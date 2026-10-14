-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2208
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:59:54.694631+00:00
-- url     : https://prove2.me/submissions/288a3fe6-0c79-40b1-bfed-ba4ffc372078

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 396942446 ≤ n < 397122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 396943696 1250 396942446 396942463
    0x2205010906140d051b12030a051c140609040201230310090209060a0e21030715051e280c09081203010b0715150611120706050621 57
    0x1800101c204107030b980801503955500c110207400b41d000f1208422884161350000e05030180c0140030700c2100900e00c0ca00750700f035800550507117021450000e03030b6a81061619040a074000140d40c8200301848a00070210f00304030000f04140d008003480c00101d010b5a020303221b0010690f0304010380402c089080b420340c4119400950f0a2550008615004513984c0207074001d6580c0d00a016000c141040e4440300c0440d0744201c1c203810b02d5001200c84c40c40340d0f00b00d024001e40783c40f4040140c009650340c044602d81548400e0000c01c1d1002210720348014400700f2850002d108034002c80031000c001040d281c62500c2ca41e078298080c4a040c10541c2c0c403200c1c1e0b81c03c1c056600080c0f0a54003985514001c517035200043d5444000040b000d02c45c1e1041000103014480b41c0d107010305000c07402070b081440f400c001d03514940c040300c00f07184550003208081d69027000400d0707101c1c001c05007040040016100040171203101c1a064002d00303400400054640000504030746aa54002c030b400e5190311601c0c1c3c1958070900200d6100d4840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 396944946 1250 396943696 396943709
    0xe03070c050f0406060203030613060302100203070b0a05060f100210061707090213030807170403030503150103290f090708010f050402071a0915010b0c0f0a0506062205010906 77
    0xb5001218403803509110305001c655098002d58074680e0b42004002c56800c8000391104410b80e10313140400962601803442d00344900e66002950b030354020b824208114440140407810003400e000400146480350f4024175155131050311110034a40d01810280d043c030384032140001849243c42c400240300d541080c501400800441e05440034140c8641e0ba1034242d01c140d40c240c2480c002d1a51080001601e104000c9c40e1640c01480c041c0000034141407404200e9001c4d50003a400904017006100882940b45d0b10718004140c2404d0401000020000c0300c000c030180e16405002480d040220900f060301c030300e10010fa0f803020003840000c491405400140c036051003130050140002c0080c0003c50381e405d05100715282613400c41d102106115200d045000e91100040100d0b04a00407030000300100381c0c0c1502e0181c06400c150007610b888000b444006450301881040c102405d510440414001c10b01c0450055000041a41c15080380402742c28030640d40d80042c12882c070781c030745424000510404540c0c004c1068490 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 396946196 1250 396944946 396944959
    0x90411061602040e010627060b0a0309060c08011809020316030623040f0f03030e3003010b0d02161208180607120e0c0d050312070c050c010f030e03070c05 68
    0x3c1450501c0c200c40447c011034110100e024011707000c03c06210300c0904c1c550070112022605649541941200e90423211341000400c4c0c40c0c51520b010030000d03019129072a005072401410301c2d032500d42c0001000300040c24916140386d072040054103544040c405052404416202c00301c66035079070b140c0b1900410714548141071840b0040e00c00a00c0e1442440c986003d150089c91180d100c184c503850360040200011011800e16a484924600121003804101c10641c001e114510315003040c3c1c0c1200108410b048080c0c0400082080103208040c000740030341d4605d1004200040e2540c1c06a130142400301c0c40580054522074808920080e10742d800f0103c21701c2044c0d00203040300c6983c4002010366850714143e03007a40103e4100003546c0581c10309a840101503014007001c48440c0580b40d07001c690312403808c0324203403007507000001e000385002c1c0f03800b080a40180080c0340240c403001040c0c48298981030320f032003520f0402c80103100411406200707821038181410040c0940e5958882450100705111039440b5080c041c16 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 396947446 1250 396946196 396946211
    0x50a060501170604060f020d090c0501030c050a020304090f1e020c07091109040b03190b0f010f08030a050d060504020c0f250303140c15010e010b09060909041106160204 74
    0x15100c020b00c504452070000400190310307240e44540c090085c01514511056083c41520101245030103402142070085103a64a079508140005060b201c40e080440c0070300508000d000c420320b0740081103404403040c00000181419844002001928407a0b0b181c0742403151041c0b00ea480030311140e0042c20525100300450703b40654070f40c1c504080c0e4071621510001c030201880200024206038101514588004065034040c0c0e54200714109092079062058035486040d000b080048850350f1017090140c500742020307441180c9004034040e030b2445550a50800c02901080c842800415a0801005000014025510f8440c0001003e545210041e1070214511a26030340c243c0001502440410300c00154201c40100d07421518183c89115408030718640c09d000401940310300120520030301c80604c6144858100f036514001e060302e25000180c0003a509200e041080400c5541d5440c11255000400d0b1460980e56803a420100403d90719034001d141c0044001032841c4c040c203416649604901d20032902041203c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 396948696 1250 396947446 396947459
    0x101d0a0f1103010e190204060e0117090303040206180307090e0d090f15110102030703020a02060705040e0708180d050a03200301030807082205130504032106080703050a060501 77
    0x29507040c86401c0340c503030341000140100040340701915441222410402d48601208035154100e0b8041c0d40000c0028600c16400160b035a40500c44030a00410190915500c0c208140d1082d100d10015000901c40c28002590f0b941000c80203000140c103003401000c0e2604e403544d43d1070780e80181c003030322500442034042c07000d502203180d010b620107000fa5401140c444400d28101210403140401328500710b01804402401c00410072000d000440c403480160760301580359510100c02034078080000e40900103004052009000314412070b0000381c2e010301c4601e4a58520703160a4151034002002d40b00f540650f002e10300ca001d900f1508240100184c0425560070040c200000310103ca4880c1c440f0510090349604200410200e12400e0207010210b0082214a02d0710302030b004515801e185101c411000149102820072452a05103507030180c0301c0c21a0f9040c460b41c03400c0d0703030010100500302d10302c96404090190840140041980408090480d031012031b02c0d03503034407410000d03500c01c2d2040702103900500748000420380c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 396949946 1250 396948696 396948701
    0xb0f0f070305072304090f0902030c01050f0703260f040b090d480201170712110405060408010e010606050f1e16080901030c051908101d0a0f 62
    0xc0711560303101c1c03107800e01000040105611500040c03c1d0144180008240302e000c504c03601099076510100000c23080140e2050500340000c82d843c09040c00000d0003d40005228041194000756142c9802e1901c18403e100600f5814880104c0d0103c0f2245281085208600040840e01031400b0381c1208000340d80320f0030f03840d5540e099180340c1e400140910142001412881401001c85105103000107485001d550400761000441d9018801e0b005901131007506658222005503620341c40713141c109006242c2004040e24081c030300b03804030030103550f1600d0508c0300e52030100c03e0b00d01402d001000319580b035a4030b0004a01801031003520304299403800740c000600340d000c1c000b218400040000c2c0c450400c100040310140142d2038005c3d03200c0c82d4600b003201141c017901d0a803081e01304611420507180c07100021000101111a40c8540030140a0100060340d1016444e40142d520f0024514182c511961050440040ca82d80c0750310010040103071003075120182c1a00c080841c40b541c40a1010400300191901d86010f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 396951196 1250 396949946 396949951
    0x30b04150e070501020d2a08130f06051803010f1104050f0607262a0d170621010c03060e0702070e0a02210c090114120f0601020a0b0f0f070305 63
    0x16030b02210b229410316008914076550141da07c00e00f1b034640d45031003d050345281044034041302d00c1d90b00055005408021350000c80d010304091f00c2c01c1917819060000191043c0300d50100c220318a44041c5000500340c0c0c09400881410107400000d000004a40c11203440c1070f0460301855100da4100710344290310b03092075000c7d105140e40040031404612080d142444c42e441452004807003580c0708000848180c1b02103117850945103856060011001c580303100d460f0a00255801e11001c21001e07020404201344604d6445800c0841160065644003181c0c034445004030f0002005031141d42042d0102003100c1d00b59000608880c0005001c10f0641d80c0c150b003c90300e40d40717136001d80e00d6200b070802c0200e60503d0280e40985611541c8810948400c4840840460081d00c05c60340c480e4040400141d150803035a01c6880c0302d4000c812903170640d007882e009551102030050014400108002e00c00c0004107240e100f089105121900101806141c0c1004400008140d0044840042050020000c40c2c80300b8030a03c00e151 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 396952446 1250 396951196 396951199
    0x1e011107050c1c24050105010c02010903020103020a02010f18030f0c260412060b0f0d0804140402040e040809030d052b15080a120203090d061104030b04150e0705 71
    0x8048455020020390390f420300d010f41d90b0b21440441003400101c105881c1048420501d510381500140c01e031841e8182d03a0140c00c03c82c1040014141a801070349c1204a04003500d6090030050703152981148106e004080c80400c9480c014100b031495205141704030025040d4a010ba03903108210b2246440540f14074030358a40083c407030300754050f001c0c0f45080d2100c182113a0a4400c0110784c50680c2ea45258480c0502c0d00c00160340d05595103416200c00d10b8000240080380390152a900090401611118814040c0d481600309a000391446500c884d51075074104d070003800d05140020128105402c05c418507070810103c05010b0b00c20b142c0a00c10990140e01942c0e04141c1a0020070f80c0740740707803010f56221050540860340c000e648030400c10712105407014101c03010305140001851f00005505040f400c03801c0511001c1c0035034104214551498075034000c69002203400c074201103501551141c43c2e40880c0b0541d40080c03c4118000180300070044107402c0d600320420f034500240b10000250a031551184458070405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 396953696 1250 396952446 396952453
    0xc031103010e04061418070e0702150c0f0a1e090308161103062e0f050d0305120a0c03150b0901110120070c1a25051e01110705 56
    0x1002640c0200c0c5207a0f500900c6003002096102042c603400e0b50142094803032540301c0c0313241c0d40403807600d95040121000a00c0c1d201c090000350300304050007030340340ca80044205292100c40c8c4000341000300e40300304807a500d11040c000c0341e5681c00c0300400204030307041c0c201c2c0446450710352418542c2081e01c60803481094903004280d144c1392080c1468034901860044000700c58034a03140000402c5070754180009880ac0c44405008503400c0681d081551070206102212100100e001d41c040c00018000c2c800b41058410955003070302202c00904095400b4080c07040c0450209a816040200314211a0007142e01800c16031000e104000c031412401c2845641c50049600d40d00050112146540c49041711000024070080005440d1480c000380040240110089440c1c0b4140090a1000c100d81600c9480c010902c20520a0b0a101c107180503845034400e428000e071401c6800c5809240c01c040e43e98185030590307440400c41c0d4040320040006448084000060030b119441c00f4007000710030401c030f011140d44a030701c20081e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 396954946 1250 396953696 396953699
    0x306020a0906020a0222150801020301060f031109040e1e0309090106020a0f021e090103080304140f060705070606080d030e01151409091203090c030c0a050d0f062d0c03110301 77
    0x8031003081078004140409a9140c058001c8582c0b11f504c50075010f42190000983e40b036040c0304c005003044850204030410546000250b1030400c03200001e0312402d44003150042035180388071701654a4048401c0b1582d45004c4820000c2d0a0290000020520124266403c0d0520b0781e840f030f070507600d41e1003141c400350598501c000c0040040c5000c800407201d80001d05030314034404500502145101c402600200e41840c6c00205210901c40c614030030f0440b90015100421000c1142007401c0d880d0078020301480c05000f804204d8008004c00c50300100040e1840302c044a141483c080c1c0020090401184010410b510340b41827402a100180c8a0b0802e40d2016205085c00140342c406000e0f0403440100070408e6409a01e6805c29000d006000a50107504210014154255004109818142c0c402c400d64071802c0c50120400c080c2e15550100c0d01c200e9004140200d022150341060170180c40c21818241080304243c4440b4003080c52070004640c4402480000c120100b01c025064049440420380e485030304405000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 396956196 1250 396954946 396954979
    0x20604030806120d030e1009020a03260307020c09010906150e040608060403050703090509070e01030b0a0305060c040e1e01150c0203121c06060f05220306020a0906020a02 75
    0x16200d400890251192088542c41c41c050790402c1240384c02c0400081d00c41c074aa039494101000110050445070904000f06039080d800070300802102d1000801800d030850300c04000e290800402c94094a5aa80040c1d4030300d000340300207481e148601403903882032102c000041200c000a208020035900081c2c0c080c0c43c03810320343c041510151486084698440d882d9907000c41c4049040c41064012440703600c44c02c0d119140c0f450081c1c0418107582115010f14108020404455881900c01984107000c1c2070003e40d109014000c103402e0310094202401e41c0c03041d8014404440400e0000b001200d011103e80e084640b10105031071015602451040c2c1070b240c80c600180044411402a0b06401c07000b400d00e150b200c090b07035000c24204206038032110010580450b001510140140109801c101c080c0c004200990400c40c1c080d0a00181468a80c00c000011030440c45420643e08032091041a40021008190366444c080d03020b544009000000520a284005074940c00001e03042031041e8010181156071003543c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 396957446 1250 396956196 396956207
    0xc0c05040e0a050726010c090e0411180a0c02060402090105120f070b030406110307020706051c05040803061c0309060f200d020606030a0c03020d02060403170901081602060403 77
    0x240e40000c02d000d941c0d407010004508100d902e0080031032181c1c15846695162041d0700f07110102400100a03418203041041e01548800080d0641c0c4400c0c2200001d03403038504000d04240380d0300308c0c901d40040700d0072143c0344e8070690b82c0c0155118440c0d08009000408002d10120303102c0d901a9030083d0030070040c0c0700600440c81c2c01b9000c200207000c0c08084a280321516080c2d24035201c0b035544064110b100000c20b02052140d58001c01016941103070740b01c2d00e10b00748864001e5035600d1510800301084008581d128920f1483e0300c1da4444124110014802c030b00302410502ea4990042d50341d43d01c66400d00c001c0c1c000b040e0f0b9011075a0f844035016290043d1301707807801c1002d440c068106100442089200a840208000e20400030218024810000c0c1101c040418001e403402c2c0c4042c10041c070941c020191600005c0c00c240c0706105036a81591146024041840803918074000d0360801401007030102c0c00c02d6115060302002c0c02c090202680e805c04140c48400219000740c203150184c5005821660000780800c0c02034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 396958696 1250 396957446 396957461
    0xc060105130b09130203070e0405060604090311100209040b120d050307050403120216080c0d0602071415150a0302060304060216150f050108010c0207051e13020702100c0c0504 77
    0x5000301c0e0101c0b1007000101c080b40111060019048000c0300a800c1d410308004410180500800d840c241c1d00302500c88550350f0340c0040c509845141c88160306d80c2014482c411a14001092904030340d04164103a42220203034101d114454042c038600440d980c40e80c0303000030355610b8201d0306001030400510012001c491a0340010207403030500ca030170000003002802620760708040b02c14641c040d0411804051585030710395120b900110050b48004059450380d5260075814050360740c42000140d480316a40791402071240c010301882d005009103880c00706602e002c1c2650f80e20850340400c094805251442c20498120110b0101a410000038000103000903015802420120007641310850713295045e50711f07030140d207140700302c001c1140b81c4070418018006040d010ba035016084081c020b114091032260001d54400b1a40308880c455003840c4c02d940401da40f038641402000308040d000b004480d05447d4104065488040101d001304400404015041c5c401c441c0d903d0199408500454420300e008200005416213 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 396959946 1250 396958696 396958729
    0x807080307110d0c05010e010917090112060806091c050a0804020616060c030e0f10050c0f16030e010f09050919091a010608040c0b03070e270c0c060105 67
    0x180920078560b850304002d03941444503c0da55240c183c100c5440d1150946855081d00d1000380c0c1004401c134006400004006ca0307072500054a00d4543e040500120b4002401e04030410301c0600d0b02c140410503942c08100300d4410300180044801e808400b00002d002114404504000100148002c40a886c4110b09898019000030705403401c2014136000111031242d288404c40d0b01945d201300198189405000d0244c03e011024044c0518180e14440e9a0b1204003826960031500e5640c000a0781030904841982c110000544e09283c80345c0c410707041e140300b00d08103800c250b01003080b20b854031185600c9810502c004000e15a608c080041c41c081c24003050f20400390042d20042d020300400d14241c1024400c03002203d00501030706202c0d03001030000841010041e084041001040d40400004ca03983c80940e000300c601d0f1b450601e81c2d13a901d03d003003110400c00c5c2612040d8030005541402441742ea800ba0704580301030401260005a80350090340940c1881400905219508000010040c80c42c00042d000760f8502c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 396961196 1250 396959946 396959957
    0x50f040e031606060b090306061207150c03030f02030106020a26070b01050a060c0b070806150304150c1b2a08030d05062209050a021509040f0204030807080307 70
    0x1000c0310803400c540096a00010030070940b801d050500801d40208401842c81e030240c5460309110002281e01e03803200401c001d0045506000d56070141d90200b02036802810684c008107600001c2c50002050255001c50a800090034100d0038558094030b80700f168102d504a80042400303400c07036910f0800c1c2d81c2510010880007200700f280f0704500c0b820700b0000e001440c031600b501100d0358104002c110ba034a040b504140c0c10021002501ca0020f40c4008400740c000c0c00d00d09040d0721568840c00001d2100502042d101540000401400b04000f00010208a5003510100610070b504c0e405008651a802d43c000d6040152070701c0210070086442c61020a1441b0411709103800b0400c41941c0310040c043c0b4039804101c0c15800020710010080c61882100c4d080b40003162000080300711031040182284031408445032245d990028442002000c1140400c0154080c2c070540d4800030100001113560441c002c0075024a050a03411882400030b442120162540004c1c034a041c1001511038944c42e07040103112405102 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 396962446 1250 396961196 396961211
    0x7050423150301060509210622080d09060c0206190f06170307020a08010614041802040c0906020f0303040819021002131a090f01050a0309080c240403050301050f04 72
    0x9003000b503010b400316031140342d95001c1c0007040c884005908a2580780b1a1040c001c0c03c0044013000c02c1090300701e800240d00b0a801c076086c410201000126080080c200c1c031b00000c0c401081069504401e6a190290004100101c4007200581c0c4403c0c040b20619803201704e19103110f00f150241d51040381e04038100c6000184090715a003250fa10025460340e6203007a5131000c1020421031901d10303060400b410303a0100a101c0d440c501842c1203450381200101620464540f08416841d0040c2d00017924045e400800038043c80d20030754130103000c4c06140c1c0100401030003100303640c2200f00c2000084038000c55014801c90314100b4140000c403522000300e24603404600940030075403c1540ba034006000f09240f0301c8440001280707400421100149a240e40c005244070510003116156544100c42c8000503080c24444c0ea1142c4844048000380705045006100310030101c1c102c00d4034440054552502c5000b1002000d062140407440c0300960001c460050018200704018010307414694031410803410050000308114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 396963696 1250 396962446 396962479
    0xe03090919051b0703050a21050105120a03050d05040f050f03030a051006050a0c0501021b01020705060615041e1703030603061b07030315090203190507050423 70
    0x5001525800384001c0c0d003009451404415104407508601d8031414619424240355510107140507030035014003406008a0b28420542c00384114902c13012189081c901200b84801640c0000d11080c0580d502030000c1c503a0445905000103101c490041d01502d03a42d0801d082c4070286000352600800c1107a680603010348400006204200340408401030340c000e5600c0b494010416821158001c26540031003a4410040050303075003000c2140c9040e84680380807540c1010320f0500c540680b08031072422014a000c030741e500c0b09030b8034194083c1103118801d00c01d541032074a95004001030540c44d106000e400c0c330820042000100c3c10010003241c8081e0309285416100e98544107042c003a0501c41581c040c90700300001f0800d55180600c960b583c09280c520850a40075062885043d19018517000203040c9966805c1404c1140c3c0004040c0c401000d050405640c0e074900701500c0150499800340110146041c04042080030340210181ca094580741c55000150041e00c0c078a4044000d9101c4001d5005241d0483d400c296 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 396964946 1250 396963696 396963709
    0x3030c28021507050f0105160804031e0207050f060f0f031026061006050d020c0a05070f05030d05090f010e06070605010311010210090c0905040201110d03050f010512100e0309 77
    0x410b4169002c01c0e11080c90341440c0b4208492041d0011460f40751904000000c1900c3c0d4008070000440d251810b00c66545160541e80d0491b40740a803010300c01d0401030001c245500041c004180c51041c2c0c2c4500618626005205090007541540705c01d1030310074030903d4410b1281002540d801240d900902694a5580f0140301d190020012400001907008441c10449070782005866004201110368524080c90070200814074015000c0354850190002042080300e070042100e5001d00d41c00001350740c042ca54405a003840303280a8803425009000b0030b2a4528200d0040080e9840b80307401800d83e6103413000700310044a044410b6810103901031014803402c800310341984101800785104004450b82010004006403414094210100740340b402d000b9480c2c00106d107034078100200c920041d00840e082d201c502c010303034514500300c644880501c1190707a0b072000700750f00d03400840c003807945800008034170307620780d001d01c0051507803510844090b038040404018001d000798001c000010008066074144200c40340040e58 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 396966196 1250 396964946 396964969
    0x1809031418040605010c020f0f0a0503070f0602010501120503090907200a020a1e1a07050303100f060f0e101e0c170702150c01021308010504030e03030c2802 69
    0x510714000307100c4241e9003401e02c1428050002400d09995000030740e80007510301c0101d9000c3c28014200c0d14601d10843d00d07034003204000380c200201900c110700e443e2000807842400e03c0c031032a0015030070b0500001c0d5459882c1d581e81c00f0290044051490408001c00f032000a103800350258040045840d00c0070320034103000e10720502c1d209111001c0c005145190040001210240e00407a6088008900c045000c0c00c898046c00211188200064030107841252011024007808102403c00d020000400c401448416400800d440d240c040600b01c0640b05c040846210203071315000c20220740301d0028682c0e5482c0006d180c002c00c3d62103140000c1c04440f5841903620790000b44200c0340218840d01880070401440000c20200c541804c0e00076424a0180c2c1c0000d1380c1b030210b182c8910491040040ea0321130707804080d0100e4034000d00640082d543c8541d1140c00d1030080c001107030305030001340f40c50080c44680c0c17502108440c2200b1100300106030384a8001c0f0810444402106a0003c0d610a21851001619060790700329 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 396967446 1250 396966196 396966217
    0xf0f0d0e010c0207060c0f050f06090322060f120e010c0e01020124030308070e040c2a0c050103021804050702150907080717030d061e0f18090314 64
    0x696080300c010450030766078600305610a641081400740082544120540d5840d41c21444113400c15845043c040e0402d0340745801100306000710780401101c080000010041015540354201c00c02198482d01a81860301d4000e2a00103011001941502c0303200d81c03181c3c1c0c25020509030005050900804c4242110f80210412010420500c0004819a028490394079070500d40404040040c00d00c5106207804941408002c0500003190003040c410b0340704035002c0d224a90050030402141104c06406064092420b00e401c40111030b002c81150913400011965a800da4420b44c802e807080d08040066011750090710005189030095504044241c0d111b010741ca006000e40c0d0040c2600c01440680303030481c0d00e0010541d41d03d075800000100020b141c00190a000c444540000450305480d4455070750840c49006511010141012004290700d0940038140e000c14210451481e0440e03030b03038902500340c44020301c1400e20305c000b0143e00040d207000c242c0118101c140b0a18040c40c480908550502041c1c003d0031401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 396968696 1250 396967446 396967451
    0x30e0909011509050603190302030d0e030325080f060312120907051905090a06030f111e090f06010903050d0c0201030b06070206030621011404050601050f13020f0f0d 73
    0x1c42000b158000e00202818080038280300034540a404241c0d1031300c0407102001c4000c0c1e2083e40c0c0c02030501c28429101d07842a600d1040c01020307400380c1b070070740e032500300741c6e4018075864425640f1100001d03003050620344000c1c280c81c1c0540c03550f940807054580002c000c0420303401d40540c041040948010200900810050081d420090b0a05c0c9412519060351900503501514680283e110007260700200c44040b00c000300c60004840c1e03101a083c00243c04550301c001c00005070001e034038082100329000d0544040d03054801c11030112800b0448034042d00d2a05103103400c0f4600101089061039000b0509910100604100c0c000c0c996a548031440c060850303032184000b901c43c0f20f00404641c1e042c047c14404071012250b0904064240e00000d000f4440502180e100c0c201801d106020303042500d2240040f96440d5000b04480813117405401e804400444003101c2d2170003050000f041d0740c81c10400200e5000c0b4007801c070400c00001541e01d02d0003903012410f0190020070034040c007800001402c00a20804011540c003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 396969946 1250 396968696 396968711
    0xc1903061509060804080d02090d03020309040506060414090402030f0a30050a0e01020a14010c11030309060f10030c030c0914060108070513050402030718080c03030a0c030e090901 79
    0x15460021100d44100c10400303418010080c082d413041d110740d0015009440c0965600a81556a000340300e0301d0107a0380c02c249203288600a040e0040040e002011066400703005a03916002004003d00c01c5008110f03080c0100401c20405040029a00b54003500c041c007102d100341c0b0300c10425464043c504004444d42881c0702d40074140300c0c1d10000001c4000140c44007100003001514030140450003604d143c6030401c924007804c040c0390b030f20070070800b4900b036004094080c601c585484441d02800d202c0300c0c43d002098000c05520451000041201c0c41a00317110042c141944800c0310001034060080d180c180407550191010001c0b0b411050b13080c004520403022007492038a85070014003a9254413008e03d1904c100c1e031040015a036000500f05603c6411881c05640d02c810b60203030403841d2109900700a411034030100400c80c0c0240c010f522642107010203000ca0031420b9880074401c0e42c0700c50441c52240c06400500104050b14062280c0342e0515100341015020810314001003942c0200445091603d40c3d11000d5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 396971196 1250 396969946 396969959
    0x904060b0111011109010f0e0409140118120f0c05150103030e030c0a180603170a03060816270906050a0c0e01050f070c0e01033c0b0c190306 62
    0x500941550000d000400e0204c800c040c0c00d004403c8158140204240700048252003010a144d00700030003042004641110304200041d009010800b0080d980790040c20303003c03003001030401c01449600203030801035000c4c0400200d814081c00d00040040c0100300400c580010410b026a404448504410228030343c07550800410b1207085401107402030300700410031103c039121084e00c4400d03a032294450b901d44450034007514004160b1903001811035440c06401c2c0e403c0c9000302d402006c2c052440d80e41401955140d48240342c0740d40c40c030206002e0700070041004201b100d0170140390070240745402d820382000b15925001202030785c0015804613203c039035540402c81841154420b86608010720f140c6000a04003507400a002c503c100340f1880145040800d012081001d203126210190a0000c840022943d40c0d180145104403852245d082c02c546140c00c0300301e2a542d107403616130480c29800242d0015849a00c805001800c0607003041c0ca9075008201c400c500c113081484400c01100c0326640010414640300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 396972446 1250 396971196 396971207
    0x109151518050a23031e01140703050f011512050a050f0c040501051614161716030f060b060301170106080f1f060519150201090201090b070f020904060b01 68
    0x42102d4880e1100d40001c0c002d01e01030255600001d044940a60103400b03008001070320300a0610201e180b84500b60000b80c030302e0318064002d030144085191084030140c60b014801da040e80c0e02194491f21100740300b8010040b60011030000e41e10200d590802c80c1d0303e070000c004010140d07142254074444281c0c0741c40c01c4c0180007110500280c3c0c02070001041c2c41c00c00f810b0030002813103417060395030140183c490130203407100780903031415101c11000aaa08841089121007480302006e600303481040140070700740300404884900410075560440101082c041e4007421b560780c1c3c2464181e4600c05881c904e5507400f032503405da01c4140086003e00252045601d490420a03042425078000e078000c070f001e40d00200c203418a00d10b40000c0c3e00090007410361005088040d000101e4004040c164091075010380a41d000c04e10759201c0050703075001d42d5490307401c56120f10707540c10050f0309903007103401c1c0203000a41c0302500b045207008000160001074440d41001d2140386240d000102468030986066800c0f65032030100b034542d981c121 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 396973696 1250 396972446 396972449
    0x31704050f04140106050d020c01181406071e17190b0105090a0504021605120a030513170307020f01060801020d0b030714060a090503060f04060c05070b0109151518 72
    0x102c0d018000e400410341801d11005044c402c42080c4031000c20340e8204c0609540544856000401c000c00860700c0128040c0c40c42d4500501c00d40d050301c2c0e004440840c2d6040801e4030752103403925460301c4d170640310040480401c60802120726010001021440200740c0080103800780510400d02a685600c5021039891040303d01c0803050f43d05003c01000081e0f074a0b215684068202c640c2107e0040c0c403803403040c0b50040c40c3c400b040802403c600440c035a2900c0c0f000e0440140c43c1d071540c1a5410003460b6245000903800039141d941c00b405015400d855602079161010045078080b5191060394406640b0b101030b607003524102c0c1c11003100c40e500407681401242151141000c0c0090450060114519215100e0300040303043e54824003d00c00061101c80c414002c1c0c8001c0b00402c8040c0c201c5080e41b800368103c40c14801d00360f504a075441e0400464075031051040040d254074942107502ca441c50b91915106000401d1058200522030445031000110300d246001340070007070b00080d110441d094145a04282103074099 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 396974946 1250 396973696 396973699
    0xd02031201090b0301060b030a0203010e060a0302030c0f0303091c02090c0a0801030620030408031b0a051b0a050a150e03190c03022a011101092a031704050f 69
    0x2800003a040d500310036819811221042d00019803680403030f0201380035020503004061180f100100b03122041e46958011412251442402151f5465280c00c00002e0581e40c030002c0c2d032543c012101c00c0c1d03692030007004100300704000804407440e2103100404290840c0e4081c0042091166000042c1c1c194241080720316440124120842e03d0404102c030050701440e4103010103450582d0303c060801284040c00c980001842e01446441c0c0c07246400d1801310211391088842040042580042140b002d0f03107a0203803050401e0a403502400e019081a603807414810401c1c8036142c0784200103a0901056052041c00300b0705014144040019070040b045409076400300d0024116648100718940020041c40100b862003076507441c200c42d010b101d9040407407400d801c40c02c00090751007140c0340491094a4080320100d0b290400e8a07030302000b500c2c40d1030440c2202c41d100005007034003e03115120a80360ba2100300c034034400141c4815803d0000e4a07902c07045a92183c101950500c4040082e09201600d032608191940100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 396976196 1250 396974946 396974953
    0x110d051c0209011b061118010e0405090303070e130212040b0f01060c06022b1e09020604120201110d0503010e010e090706030b03030913020a030b01090803030f13050a050604050d02 79
    0xb003107030000300481c20301025142c410301d011840104001407508071814400c04040180d48400e07080281070003090581043c24045200002403410f43e00b018081d05100700380d4000503505581c3d501000b91400b0703a615001541c0700e04442c0c4082e91110543c40a031400801c18405070641d45041e29100d1210200900346500c00c0c3c082c58010084164405941ca0101d64420710158585800c0032508120220701c40c1c4482020140e640c141c6001c8549610280008200111000c2e8a4000d408014103c80c00510042d401240070070042c00500d03030004030500c00707a00c18502450043c21340b140d10703800c1c12001000140040c800200402084030005c0302c031805810b000c17420b80740034240840700650320501c501c24082450b48803901c01085036414004c2d50b004c2e48024000030305841900c29500300a61041c1d60f280c01191401030410050751140090038180c1d8010801540ba40d2540110710508180080c030080842c0c450f9020040010030900180400b0341c0b14000811940c1820703d400c43c10551020f007040110360 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 396977446 1250 396976196 396976207
    0x30621030703120b120a0b07110601031e1505090d170601030c091d0108010f061a03100b071506090b0616140106031209060c020904020f01110d051c02 66
    0x100071140a158181020b4143e80b0072204001c02034000c40c4452a4055056008100b0307400c800710381c03003088038484d07005000d05030341d402000d0307518000c51004203000307902c400700600001d0301e4082e111102c002d9000e07000700210342079a40c0140c58451000d541d03466907103890a222201604100c00031560f0014100703080c141d51b415070b548103602001882241010344500310000618001c01960000e800b440440700302e00b11007940c41281b0300e603080c443d4824030341c0b03040d000540d07001140c030035002913450a0240c2d0899103083e280b1013525800c050500c01204281c003100040c5480407a004203c001c1c8280381810604100506101c200d8075142d000d00340f81404c2c16981585507485600302c421594840005281101b07060800480180040c282c055841d0300c0c140c004002e01450101441580c242d41c0e0700c0c040d4a036211142110b42e1040044002e40098008001c20010319182c5802a460300042c940f0300580300184101c6d0307250045d00220303000407500002d1018940c184120890503811001e00d001c0d840e08 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 396978696 1250 396977446 396977509
    0xb0705071202060705182d031005060d021e040614010305060301060501140a0e0d0b180304150f0302070203010c0302031f120303050601120213061704030f08091f020306 74
    0x10306c1030100f218461501d80b010864a1358803000150003107400e101c490480e001900183c1e1103280c40e4440c18501c0703803041d07004d0b0010011060196911602c0041c04014160140d503090100025031009002282c17140801c00356441d4495200c0d40b0014200c0e00e205c0007110b04000c001508460f40a483c240c000c2c0d045c080d0138401c0c0e9800c020100c2403803078803460203035a64030030082c1207c5150341900050b50141d60030440000b1300010407035040c09603d420b00c00880301c0d0310f403103000c1d9600e00c1076126220640c520704200106660003024109440e01c080d0602624280b42d80d03000030701711044040003202117903000c801c0c001c003a4445c1c000f6410300010650489000c1e81000e20a50007107040100c02020142c440300003e0013a4840d001a4422140e501c00564880014000e1410242c0780c030301039038000449186011508691401c460340c0142d4140e2140c00008521740c000b100ca00400030020080c600c14a0900007101004844d1841c0b801440b4000507102e081070700801420305c220b10080c5190801160400480 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 396979946 1250 396978696 396978707
    0x21120c03071d12060c04031e1509110316080f0f15040c0b07050a060f020a08150a0b0408100b0303121f0302100302070203010c09140105090303070b07050712020607 72
    0x28480311032410641c5140000002d954030070070300280485030013010300340f000d1089a040580152803080050004094102034013920001d50210701078045042a0f640707840e04e4001e5804100e026002d6002c1c1c0b2070300125500820b04d800b078907032218a8003043d81c8a0421004130144003000c141a00ca00c05042c3c8243d82a0200fa510403400b924104000703241c2020408001e01c2c000000d0080c0003c50f9019212840c50410584403081c9100c143c0d4003070704044011034186503a100b203902501c0743e601c58021a0b2620071b401e0107866804005030f034000d41d590381e005c078402440e40b018000400b180c00050a208406815141c2550b12410505000382d1050000c0f801100340c40200f15800104d005181c5102c0d002c018042c0030459280d407010750400040b55108c603419500d50020022a8000e5000740001015000c0c00c40b014180361040908034007135504412140d44c0314000414094100604480c24055180c035601e81840f1b050700c44101045000400300e003040180018040064070300d00142c42640b0700600003911 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 396981196 1250 396979946 396979967
    0x8060312091207050a0f080c030c0a03140a0212030717280909020f0301060f140f0f0c010e0a050d050a080114030a06141012020f060c21120c0307 64
    0x20a60032030044030000c2400704040f03001000028401e54100d5a601c2c8007101124140c0039102c01806050701e034050509000600b52030854020341182c120f0303484c6071204049603010b1030509601d806840e0320031015a84041c8643e40c110100400b95a40307400514200788611041041c0d94240f1100f8050008518a280480010413602e0303a401440e50b0010501201d0f0344115801c81c803040ea20200d40e10304e059070302e50040d6060b07a000d43c803071542240e01040181c17041e403000b49452845600c104400409144a81d001d001000502682d040c00c1074500c2001c0780c01d481200719610303c0e541c01820704106105082011401000349818017500e44691050010884ea0b0b050040307600f0380340556810045034804004580b000e80d00000100455000602c0e4000c071071405a03110340440e41d2014000c1400f882c044070b00c00c407041c0d0013000c06200315a4081440610380000c21204081c0c01032208506101c07080e010086005403644070700990303032803600710803c2102101a140d682440030500403c442d182d000300700102d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 396982446 1250 396981196 396981199
    0x5090a06111b01020f030f07030e01031806020d110c0604020102012007110d050d1e020f1b0103110a05091c0b070c1b0605030a140709062f06070806031209 68
    0x58012404100607407030701c01510740f201754a200c00100d40403c11600f5010f081104e100b952030360350034452400118140e59501e400303520301d503400c0d944000005100d64010075069a8025001c84c4040544500050641292411101581001080100710740c0d080c864048840160981016021581c01d4103261500030b007000107100c4c17545407400001a94900240380055603005045820035405201e00805819039100ea0840252b4581080c0c000c041c00403940d400040c0c514401400d4085100c61690300d01c13034038600054180750351440b00c40520b011600041c180f070099601e0351a41d40008005000032840d02451b420f40d0842a10000c0c00000e4140300f45c950809010314000701502460b0030700038000380c000c010808500c82c0d55900003400c81d030040082e500c40e442e2a001000f80c00054000c0d4030020404442c0c8200003500e584080c08454002e45003125400c0c0c84070102d0280f80300201089004456048041055500220400200c20713030009240d41d00070016030281c8504d094603246881c00d40507906c00607 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 396983696 1250 396982446 396982483
    0x80a06060f080d300207080901031a0d08031009090b1f0e06011116080f0c03011a01110c04050f0a150303050406050a0e0916300b1201050705090a0611 66
    0x203000c80d139045104086444040300c0456030b80d0f5840c81c140045038465041107022906004a14044060301d00301207980107006080e903580000320340c0d2000f0b40c0390710080501c3d40003504041d011031500054810759103003600c560311031655800c003500c8002d001340e24083c0882a2902585e818880308100c60f8156400800c20300300100e1000e04c4115803410215507100104201040d2500024003103c0041d07864518a180ca00356840000300718245400d8449200c070b10440035240c1c41c4c1e03c4050754070070f04059a1400700842501c0d8485401d0b40090300384d55080d10074400b20002c071014003840100c0381c400d08500d19044086184d600f450756030090000e00691241e04144240480d05da4440d900500c4214810310004010501c2ca1404903d0101c00b184d00d1090300c000584d600d8248000e42c0e244402000c2920007020508000840868030388001c3c0c03001d21070182d00100300402070120140309010f21800750f03450b41c950940703800f001d2040c03240c50343c442c6d4058401c11200da0040742400c2c2d804034410011010b61183e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 396984946 1250 396983696 396983747
    0x2c040504020301020d0f0f06050105030f01030209040203150a0c08060117010b0319021315020307050c0918010e01050105010f0c15090c0308070b04150501030302100c0207080a06060f080d 82
    0x2030090103141c0c100c075174060400340f0b100c045001c42c0d44106030780750303c50380200300450b00d410046405000c00c032844a01c1c0420080103001501d0aa00c10550081c070045c11a07110080e0a603800c54841c03001da40c1200169101c2c107161150507001071039031754030003003c2c6400683c0325018a80740c04144418400e260b105900000465084600c0075008032085c0d11300c401c03d560311104084424a514890301ca41500b46c0d21481112005034070200463303e00c06d400c5002001c2818441081040d112030151125035105c41500c00c50030541c1080c000c2c11040b01407c0b00005456160600141c0500110900c29041000e051007480000710f1204445a20b0390040c070000802c00711610f0100b40e40310f0540c0024006034400b0076403100b04180994002c1c8030b0751048030052410150a03800c90140e40c001c0c00018090380003843c1100a03003159901c0384031100c041d841182c1940e41c1d1240c00c2801e08140e12400e59411f5241c4106001b003c603031592403402450404018030000d030051800603d180c025131644080060313085032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 396986196 1250 396984946 396984949
    0x60412050c03070302030403020f0402030907060f0c0b01140a05031c1d0d0506010f092a020c04050712051005010905131b080103050105090703050606062107020d2c04050402 76
    0x1d45001c1d10301d00003100ea4800b92800e01a40d282c00c6803008078881ea00c030f1554901181881e000762400746591100a003c07146c24500103940c40310b4510b19001c00c02c000700088501061a08603013a008100b1000d920b00821039030000d2202d52440f5070400c6000e68401c0007000040c8565540d21301442c402c40c6400b043c03410729904219011a03004460a81c0b115a940050090150200380c141c121400140104160b9a90b2001102a6502e489021701c9082d03022003443c10207407141c4448540c07800684160342c40144800c0000d000c4820035604800003c03d079004544078040030b440382e035401414542105a04a00d0400024040107450003000c1c010070388403410300d401c1900c43d0810600100e402203980c1c500c03054400001d11600e400d11007600e0755030818000c555100c0b400304079031040e01e40000180282d5074404040c450a58000400c1e07250400a007034203120303140d44882c41c081c0900c1d0b0a40c040c0494101c40718005003444240c0b240950001e00b501180b0648503940c90040c1d80303c14080e06c020445075201d00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 396987446 1250 396986196 396986207
    0x3130c0503060406270503040b0706140c03060f12071a13090506100f080c0c030403050303010b072102030a18170a030801060e060d0b030c1c0605010b070302060412 72
    0x5200940510404040c002000380c0d03030300000d06a007504603040202600903403180d0045c075403046000c0c0141e00100001c0c815507105c1001804480c1c020400410b0045c4100c148444018084030b5000c0c0d1800f01000344815407a044030380f000650001c0b030350401100a0703460165141e00840c46200883c031000d500d07800503a00601d041d500c0300e040161150600a41d11409200500760444000b84034251a4043c4216180240425611442c1655491030241e42d0324803490129800f0091400480c0b10500c000400204104000c43c060503460f80c55540700d02d894078240710b209490707006c69502b00700d40607106600c042c0c0c00810b85030140c0c081d184c001e1003032440e0001d481548000b50040e40558840aa95440940340080c0c545001486550b03281d40341d82c0e0311310085403008040c000855124a04010030b09030201c0d00c2d0040095048002d055510074140400007031014041ca000000343c1c00105134800d01809014800c00b40140a5044e100c0d10f000c1d0a66002506c81c840180b00400005402d18412400b91080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 396988696 1250 396987446 396987449
    0x30c091719030c2102061e0a090201090f06050403060b0a030819180605030610030218040b031212010311010e010f05031f0914060a0303050729040605040b06120303130c 74
    0x45a034184c0340c4440b211080b1250844c0c8004025200d0328002c109102c04580c10311282c01600e0348105101d894590142c00680b0451409034100041d644001c2001111000c1c0c3c4402000d65442d11a96146140f9040e800c1d40e05034030005100d000c95410420104014401700ca00380115020005401c000c1d001040d6000701c8218070303031540204402404a03482e078012004500030307442191904008244103c00301c0a0784200d150b142c481003040302d88070342c050402e5088012020801400c1d502124182c0300d11060b650003000400d8a4504804010000d00000215684070480280f8206030380300d50840000c1d01814180c40d04800f040340000c00240302c80342d185006004c2c0d842402008032115915040e500c050424071724804c0802100c180410752910384000701e2400c0700c3c2c2c59100e0a04098181e02c603000b8001c0744035105002d0042054110004410800d003503880380c3d100e000002000d0a050501c030441c0340c07000742040d02548011004045202d00002a00e40c0040740d18003c1c04c010a81e494420619500c0303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 396989946 1250 396988696 396988703
    0x31e04030e030303010b120c0f2a01060605210103030e0d02040906050a1b08040b01140d060504030e030c091006050307090e07020a061a0901050910030f0803040302060f0c04090228030c091719030c 86
    0xe15001090596100303000f8015203401c6480c580440300410810f401033f84c800c0c400207000c40c42c20b1200c600320f800c0031614070b101c1900080000071540c02c251184015a003040740c0012002340e4035090404943c1e480c030f407104c0c8002001d20f4a20310340d18045c0d40c3c003164a43c1c10f004540f0742c0e15407008100700d16519070100d1a09540d002005200f18202840e010b8010154202418030078042c00a042d0083d041c1480c54510034401901e4090080f032801c0c05c10f94040e88003500040800805a0002c03588203662581180295400d034001c200c0c510550401030201c03044500c2c0c281c808114080d07103c00301d50f0399240305030540c1c00403568520b09441c2c640e03000a1203802640010010440c0984450070701452001640c070803400390f0242c0c0c00da9601d480c5034807603c031000c40310030965800900040c840c2a0303c9501a00c1c15840c0710300583c42c1c09855401d004480380f41c58110000003511100030900255204407131000a1415281c03107004190f018680c9611a40800601c00b100d04800041c2000d25205540f0b9582c103540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 396991196 1250 396989946 396989951
    0x180c03070315090e010b09060d0305030a0b120d0203030a050703020f1c0b03070618080d0215150a090213080601180e03220905070203031e04030e030303010b120c0f2a01 74
    0x40b08000c00e800ba1501b8052240300da00007c001075180d0500541c0d5128590781692018a5640c4a912190080c07008140498010fa100a0540e4030b0010421082002403010b4004517140e15050412100f50380009060b00d08050040c8030b4018030003072050948248121202450380f6900151802800900e042180c841e413500c580000000e0307954014901a00444000342c048240f1030310b03a01d4103581e649420f101040103a1004000f64030b000c1000c0d10b43c542101c0581d40300d00d045408403002070008901c0da0001c28000340e00003148400e001c040e0034042c009299000141c81258503088002442c40c0f1132120032031159440310059001054248115032140028a183c070b4040c0f103a00b121800b4030140c50083c5681d291512022841281c000820740c0e1150f90016408a0150004500c0180300c0c84040c00803414400342010510180e501440514007801040c004942c5a010300d983c1242140340141c19807182c440100006903882266130110b800300002d00103e85080b02800c0b1048000d0226907000560035403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 396992446 1250 396991196 396991211
    0x803061f0504090605091513020d020f221413021c021e041a0a020c0409052409030a052208060412031e1e0204030b0105180c0307031509 60
    0x35007000141041d074142070010003d281e01c40701400f104490540303a003245041c41280f0f2552625040159440c0369000d04c90150500d5a81500390b0141e0300007021085002a01003100d120582a80e00705010404035694100c54161500b00b043e054030b03180203009401460140c12440034221140c0480744192500d80040c2c60600617540d4480094000c41c01510b10f82c90342c811178815a25496081d5416070301500030403110008200d046407650b034003030701c6c0107000e40c0501400242c9594503031240d00710b1a40110040c1465003001503010f03501110f888841c440d040610400d000c0c030aa40003042c0c40000d1a24148181c1e9218600780031035103e480100c014000d0b9020f554082001c25010404501a0b4814816844801d816030b206800390b8041c4608038103030885001c0d00e00424080e54100d107618507811529540710907220a418820303a401900705662420225004005600b01400da020302012032000212131800c0c45210030140d4800503100d5000c02d602c130580d20030404c0980004000501d4030100030030444 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 396993696 1250 396992446 396992509
    0xf040b04061e0f0807080303011214060f0f010f140909010902130618020f0a0f031107230c0904030e060424230a0c0c03020d0309031716080306 63
    0x700c14070f0040c3d028900a04070001000c010005290301610106009981581c0c00c000c00c06000401903107094503100c1c4015224080280113205440c09810003c07154804d03071178441003410007204180e003c00e0001c840c41c40d007085001d08011203c260008100c4180700141c440741d0b640350141c0380d0b601000e51700c48004130b5110441d258690210003160901c03815103414100100d440b400324002c80700d1503000e00701c040108003942481406940904591070400207403c110700401c01920f60480c605c04c17141c1c04d604000310640003150010741d000c9000c3c0d0300b0041100c04803040218441200203440107040c080c4010003445640e455405480c081c0410043c0d0035082403d989840c1030300c111641025011034000e0300240d000050350b01c0300d0140c121998888601e070180c0300c0c5c030440300d404020005503960f444500b0040010703690f481c6100382c001d000303554081081e411410014442d0554049921a407001046440c41200c0e43c0c80b441d50105800c40445ca440ba900c00c0d010521105000c2e00355821038101d240100b852 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 396994946 1250 396993696 396993749
    0xa05160c060f18030b010510030f110403020a05060301120b0907080d050a03050f01061e030908071101080f06030604060207031716021009080412030c0614041509020f040b0406 77
    0x120455480c03c1d05201c140d142841c040c0c5650002401d941d007208014040c90074900b89444200c1103920b00044c40c128094031460072114032155002c3c441800040401c207510341180000d0140004584d024519450701444c8810403801a50080041641200140700341c08113121030b80040c005001030740c01c05a10040009d00644c000c5038200003081c94075010410b02000c60003903d0586a0704d8807406410a80d21217000c0c18940d00305603a00402da180c10809002171152400740007958464180700e030010511900141007094000d00900010f401002000004d44d000203910350499006000140c0c0d54229003002c4542e15401c001c10464044180c05209412203588910f078030310314550b402c1c1c802001c01d40c83d40100361851814081c0c40e140041c441405050481c072148480c441c8a41880c0d03c45001e80e035110030036034103e41c11100422451100704018044002203400803c0340480c0308100720491036000440d0301407107580180c0940c0e514080d00107640c403590300200243c210f601481c400510b051001005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 396996196 1250 396994946 396994967
    0x9081905031008010203061513050303040f1a0307020d080c090d0f061b050316091508070806040c1b081324051e0c011509050702010b150a05160c06 65
    0x462000d102c0025200d003041c420b60740034040040500e40c150901580451090b044400c1c0c06c041c25800c8900025143d030200010001081201d01e015076081c40c10b114840c1440e80501407a407aa2010002c2040080c0d0208004100380c41034142341103151a02640012a80141542c0d1a0040c070403410440501c0510201000418860b44040c040503005508694103000c4407174450010450a1010598185242ca0031000c1060700d403400b92044e0b6070751805071040c03640500246000c0b80c00704c804d103d00b1640c0804550390110b003d0b5410700205190b10001010400c001050688000306840d1500400c0620800c9460a11401d04e444a07943e459100750301045100760000b440c81c240d103c0091003024050700c140c802801440021500d00380c29058041d059600620901c4000c1d50780b1403004400c4411046040c020f8201c1050004142c07078a0359001c1e00715810100070502c0391210b07880041c0c080c00000106e44940a50b40b07445511424005030324060703403140d603000401d011008203010524a46c880304619 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 396997446 1250 396996196 396996211
    0xe03121012031e050f091c0b270303040b0403051c060801020c06060901030c03021e1905030c01110705221a0a1a0a030207020607050706020d0906110601090908190503 73
    0x240f44a00c550309031160301c030f25a01c9909403402401550b000d8607000e003c0803440030103e10b070340340c22092560f14114580e00848001100d60307201001c04a0600030b0300702440411030000010751850400c0d4440580c01a0000e00003001c020700080c58485804902d031542c1804084d5803800e0103901c0c0c644030494041d400041041805106074030018090b8901035000604036a004100b14041c03600315000d0001c003080041054051404042d04d50340340d501c0e64050340d0842c2e905001900401c608120425041881c0d4101c908e0402c2840d00981d5000d5001041e80d004035a03049910480f804c00009800b8200d9000c1d60412201b149407001400b034a080e4941202c070400001c480c404c401c0c2d51107015151400030b0014904034015011300c00fa500c00d500030740c02400143d0000381102e090500a942e030740e01e8518180c00500c0140c02180c0c03081401a0040d40400c060011414020850300c6a15034081e910701c414421015980e84a525840a0140c0b480c2210a1a40400050102a5200b28000d82564000d86020307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 396998696 1250 396997446 396997487
    0x71a0103121103070f03081f030809010f0c051506130905010f050105120606041a060315010807020109021e011106010b130f030203030d0f0f0603030201050603010605040e0312101203 80
    0xd48002c001c4100e44009900194a111a44036524110b5024400401c0a528100c2c07920091000c041c812100a00441c421410f00c0e40d42c0320050b0005100e030f0110140c2d5001d200c280b05d2498009030006c154a0b10222a000d190388040e6203076000607015840003d1015402032501007080c003400341c103400490040306851410702c0717582d030390301c080c081c0102e80b40c1100d88160b00403401203a210714040c3c02403400083c2c40000341c2030411001e07000540765802070720210130045c201d41c1d00b03c5155802c841469030000346030000f08008281a0041010010300301079050301401107000312085a802408504008541c0000300d500310344c1c40b00d0225070280c3c000ac107250031360391a800d030026840300141902e50990b0fa000e00518100604054000c01030500c0205034074070240c90328144a58140b0300e00c81c0c0801140a9800400d0b1410210203043c210303015608194003c0b0304042d00c2c0c4010a01c0081210b8895116007450196a50341342c0d611140720a483d040108201e0101511b10140356002090b8449a42e03641c564 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 396999946 1250 396998696 396998717
    0x30727050609090604032706080709050f0604030f060212040b072705060702010c0510060303030e010903050a0f0513140907031406010e0307030f0f051005010605030c071a010312 78
    0x208100401c00722100341c01c541c004c0d400100020302c2064442d00c0307204680920292610b6402c040c3c4440900ca420040020700064104945181d0002041e4010101034490901410001010440a1003540405040003200c00171202c10099254100c40384541e08501c0d1410b1414140742018004105440c41800103461209210302e9000d40d22010802000301404180307000e1520081c8416500000010790600c142c24080001140d014002c280c910f0422100015010f07085107000b404850307800c5030f0701d61182e1400482c40d00003a0800c045034201030080c100245060300f42e0308226214800c81040c403a031a41c1c0d0400000383d90602074003c1c1c40b01c2d501221041c031655140f000c22001ca07588100c401c5034031440c40740401e0f41940912000c990b1500b002d01980c03907107606c9803920f030100100100204c844d0181e484101040c4881800b1500380c10105110510040d490f0800081090101805d8500200b5000903544200401c8041c12501000d0490040701c0e00d680d80d04151400303078500d2141001140d0821270 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 397001196 1250 396999946 396999949
    0x61c0206030a050901201e09040603141c080f070e0405192313140a06060317030f061002070308121006090e010905061314190e0a0f05120711040b091e060307270506 72
    0x1015804c0000564581c0450393f10510304010700ca50181040d0309000b1218211105500d0b68002c06200c0c081821102078200381c0c0030380f2042110300090145511100102d005411800c0c201e044a4210105030001802e0240b00c0c20605d072043d042041404051155002040c200301152b001841200d005040200d4a007581c0301101a01c1c0c40100e4100e80c4c15584100050903600e0f00c801c035820088001e00c102c13034a2076126650360449074441890746540d0140c0c6010480740b07207248050b2001400d26860541155490301d044034a02213010300401c00000d031030750001070030f5850b0610309482c800000001403050941c4401e26551500302540e00001c080843c0112031000b2050380250310304249070030010822031441e0b13110100000b9460340112464040c80311035001040111003c0d02d03000e805001800000f280c0801088211682c1008150103960b02034204445140c5c0c0c00031840c0801c0d401d10b1a41c0299442c4400641801e00a4204003580070000340d880c1c100205030490036070701144c4503070100016200c050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 397002446 1250 397001196 397001233
    0x170c0f0d0c030305370b100206040b060604081c03020712170105040b0a1205030c0111040f0905010620010b091f1d061c0206030a050901201e0904060314 67
    0xc901400c62a4903905100340d8100c04c48002da102c117038070000040340f5040300005016069981c66080041e4401401c5c08203202000e80760541010702103400c5031030145045a2a6103c1180403a2000c901e481b080c1290340d0980660102c9080992180220080b9460303150050805070b00d04070030301c0c4800103480010a40b41810720558400450040c0640d03e03003450840d24030085414a001140c1600017130001481c1c40c103090040c240c1c1e50260003003d42d200c0313040258000b11266198080f0074130030b041c0401004041d4010b04442540110080d000c8250b4040408860141000c21501c9070024961801c001d00305106801c03001800c0305000c903540c1c0050340c48400c210b501008025008850080002089181c41c0c070b1820480c80b8510b01e8824203603c00310b5000210560402c94081c140f454407041041020b50081c807890303001e0010f14100b0302c1100d160310300c1c40d103041c096842800424100c034a07000710b4030345810045c0c40001c0710081080c0304d2140c40e460003591015602c44854054800c803c4ca5140c07024200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 397003696 1250 397002446 397002481
    0x90e0708070b0708040b070606030b09010c08010b090d0c14100503040c0b1b0a1a09162312010f1b0806130b03030c070e090703170c0f0d0c030305 64
    0x380001c00000d4203140120030303141d0040008840d030b840c0c10400091002415800b60800354040e00b00000e0170f078558248800d0485000300900f6003a450305603400e15440d003281c143c9040d2a00024016110340c07800003c030300302201c1a0304c054116416a900000c4807040c00c280384060b04016a0025090000c0c00d0081c0c802c0d0005640c0282050a80c020502c01d049450020340081900c080e140c400c1c041322a013245003042c158110544141c44c0720003c1da000c802c46802c0f0181c22005503001030042803c0c00030b00170120912806250210f4250f04803010111501c800d40c2680c08500a003c06440000600102d00a0280264010001d810441003155081040c805940c010007240c0b079800c51655038070100007080d40248001002d9907654442e6450790345003000585200c0d00100700400c0740c681403d0494411274801000800325502c03001050000440500360b46d4805142c1840050300c521005100c2420529403601999007441500001b000b62588184141212806030703d017082039460398450b14a010400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 397004946 1250 397003696 397003709
    0x1e070b0406020c150909010902071b0506030f090705120303040b0106110a0807020301061a0306090a05070e1908030a02150a02030103120e0a051f120212040f030203091009090e07 78
    0x403000710321084c10301d2941e02440801c0c9400081ca0a659540082e0803902c007a0040a0041e9003c29500204892102028a0a651510b007452590b180200050003440010031419014080d9404140300ca401000f62a016280c01009034041d03040065102c0e5680d00304507000d64100540130300000d0320900603482d45140707400c0340c806891100390644a080c06503200c00ba003282c05640e5441c00080740b074a65a10042c01d203549461440e56810b10904111044002608070741503180f410003806003098003c50032500c15a01904c0010261428005c541c424080340d6100403564040094411500c42c1e01241c116142c04c0e201c00c541d1066110640d20a003280002d01000344009100300c4460400350007090444200c06008054106442c0c844000ca61209404421200f42414200381c0e0440300307800c4064080389007411001181806580307050720441040c0a0310292041d40e03031100040c2454824800c407009010041c007031645030700011800138240f5032030f031140b107031514135080f228008102c0c00705050040701c96 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 397006196 1250 397004946 397004953
    0x50d02010c12020c15090f10020307020f010608060105130603020a0b0901080a0c02030307030e160602031c200a0903050d120c08060102100f091a0618010f120201030e1e070b040602 79
    0x110240455006807102025114003519490040410040a0703060900c88d20b0258803800c21103030182c64414400a50f10690341070003014045164000340c0f450449000b11603400c00030303c0c614000d00017448a0b4201a400440c0b40c076000c103241c0d900314002c2c600d500007030342d480601d82e80f40904070341107440c8451a500141c0042000c1040540300b50020384000000400345d5400d07150b005504500030081e175000c0d10150300701007403861074204004084045040c0c5c0540601c02d0100f480d00b6100d410030001a04052608040f45e03040c1180d10400201019503400412241c124110b4140035000c841007012600e6200c9c1000c40300708055100d444032034069007068006011140301c0101e00701c054600074001000455070f0345950700104110340b090090080042404202e141002c800b44220703480c0c1580c4070008078118100400c050300700c1e280103d04440002c002c00d0452151403004070090031484002031032500c9080300c8180c0000e80300881c10050160642110082903480240c1d1703e60740114441c20001d80c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 397007446 1250 397006196 397006213
    0xc110f120a050c010c090302010908010b0922200307171c03200304050c04090c030f111302031e1323010504150506031b1c050d02010c12020c 62
    0x603900a0500315040e07041050400c00785000e1682190b904008900001340141010030640d6001401d4001405c4980c00a00c080b09840000c641460303409484400c0310041038200c040d40f000c4500300c0c0c0e0038860340700c0e91006c0d01c0d4429001e00742c000d401c9800a64801d01a000d0b0000b14050704c0b840d11500160080060040300d50312058540e601404000d64000b0305483d039500c2100c207954804201c040c840442420390b101c0c2010309080386021100302403203004624084942c00880d030010503240440341e00000c0502c00c00000e1601c03441e40310007041c41540290191044e00040320158001d98440d102501d1010244501c200c1070500702002601c06841001041580e40d001c168100820408101d803010260750360040c0104903070854004a0b41510301a090152400010006024098001c50b04400624159254003000304c0a1103120501601c61103802c2d21910a55101070080c82c082e541100503660a0450418068043c00c080c1c80c2c80000100d13031001c08001d0300c49a02c251100c11001200524242 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 397008696 1250 397007446 397007473
    0x10903030c050a050f010c02060f01031a100905012304060605030a0c0c0210080f010609150302030613110307030c03060e0703020705030c0f1e0628021b010c110f 71
    0x541e07480c0400ea076a8010101554042a800c0111510380c22001c0d00000d60b58106410003070420002070040320186030358100400c04985107000c0c1c000a41c0315008400c0d0140c031022120502002c1c640d000017222810320000140032031003103a04400590b04110203040c043c1e401d004020484230319028281c0810710030b00c0800c408282c5c80d40700103441501414019a8510f050300003500c000e5040c000400014480d2003042541122502c240c0c1c0100360784e040140002e030600d02d192150300485140d807000c041e40800000e070241d44a800380f58995808100410500249414403c5241d05c11282e05011a0504035202e8803507110b486044100d54200e051200b0b45d403143c490440280d84504003c0c0d4181c44203200150402c0300138041c0750607001c400c3d002030045200126001003000c0c0130014480f440d401c0b50341000100722800240702040008281c00300f40405000003018000d00924448286039050002d4005940c44158045d0004103015110854007000c0800c4503550340d00011000b0402d80c100c10215000c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 397009946 1250 397008696 397008707
    0x31207030b030f030d020301030c06020d0206040609020109050d1401050c0c070b031506030c0306040c050702030d082e171207170f2709071704151e0e070501090303 72
    0x8040d0700400f070b00c20401140030458550f0b0400511441c40a50000040042001140c41900100402d0002c1c0540203001c52019403102802040681011b80300c1c80e04604581c460827110020b048001d045040c00760003800c107194640180c00f94402c0643c40c0802042407003a860082c0d030789401e1040700410000341000406281500003809800c0004174840c5141d049035a081c010b14403407070080440c01c1e100d180450411058803070000400c420701104002000150f01d010490600e03005450600c000c00ba20f6000c020701c00291001480b5800104022101e1221401800344100b150400c3c001c80300c0718030400002e1515902a50240740d503059080080f0b900251020340c0908a01005400a5052896082007044285d110303d08407201d100c040106168464010810581384e60700c10740f207424542c6450800607000440d10891911402044c000041c10819014000f1600145048040c0042c01031210b508200741c01c007111000d000e07401d08182840c68070b00014a4000ca030350507500c1a007842c0ca180c409552 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 397011196 1250 397009946 397009961
    0x6050a031b0e16031a06030f06010c170706060f05010c0b1803041202030613050c1203091e011205040312050603030c06070207060e0a0e07080c070516051203120703 72
    0x264814000291030458000d0700b521a034076100d42c500780c0004940008048a02950a40002d51100181e03004640c9800c1c0560368408020502184192035880040e20140c694500c010320181d00c4141c521201010380002d4020203129141c1840032645400841d030921580c0d0091900141c000e03990345002c00e01c00c1e01695000044a0403c1c102410320004c0d050855010360800300a401446032703d10b003103040810030f680d1f02100401e1450110320b40f42e503c1c4c6403100d10402015100d00d01055103021a200301388119541c444c001021020002131103000c4003503000d80440d465011070410100309914400b28007895114907410f949031100d000e09150350324000d040c080d1800350980701c24031661015510810103240180342c0b03a0000c01c5182d01d00a0014171030b001040e40603009241e840400c01a81e5144e50b810307508010203080079589542e40c0b80e01d40405015000d03020700f080c0b01d0490040e40c02c900c01c20110007641c82c26142d84041c40901c082d81c0c2e0383d038411441521040c241e814002410588260320442 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 397012446 1250 397011196 397011233
    0x4050f0105120a0c170403261b03071404170606010c0b01150c2406051912140616030f0501240306170313060c170d0b040204080d03050a06050a03 64
    0x2c01c8002c05d10032480c5042c030112421800b060780301031980741d800c1c0f04602c1500c41801c03c40340780710766143c001524400c0c0084816034102003100400421440760050711402803c80c02d11425507222a034400140700000c4801102e04114060a0085101075200b50303504000d107030704100c1c210026403030507980c42c50b0b040403030b00d03640c041198110381c640000d0401c100802c41d15102001409a116144c0d04807011075045500c0340e80300d03003802c0703103850700030341302c0c0700c0c2410845258050b0410b580381c060504140750000940803d02c58004c42c01045852003144c41c1550050310660307810068152102810800c8680070b020390714880889043c076885074040c88482c00d0340c1c502a4038000c100e15a48125000c88200110200302c4141c001046031005c0f0b0ba06000c58500030302c404c2c50440e0320207079a625003c2c45460180c1800d85280c800080d203c000c00c15030341010f601d401020340308541c2d880c5c2e80d022090700c41103020740c420000b070b0410000c104098501e0291005540700100840c808078038503966005a04030f03031320814 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 397013696 1250 397012446 397012457
    0x160815030309061204111c0b0a090602120405060105011b240c0201091104020f03070507050115060302040306051807170708060f04020a090c090b09220204050f0105120a0c 75
    0x24806070703c2e140003500c44050480c014121031300b800c2c0b500e0720004008481d2140a0207510080406030f094a0013924190350300700c0b400d410f0036195010b80c400a02414040075204c42d000140021103941c00b0728603603200380d015805654542c2d0302c540046984014641d0455074440441d40c480c1d001c10828000d42032840c0442c000c10030303942c1c1701048090541e20240150409030750f40386000807d001c608104505440f50031602145403240c0345958102c07500028050790204540482c040c02042400d41c00f00c0c440c0c1c44910398101c3c18694405000b0701039405404102c80c2c140c00c16010070f02c401410483e880a00000102030550103007844510031040303048200c080c145205207000002c101c082802500e0041d000d94035104054031b02401801002e0751036038400c00c2054a00150101d0f40d95004070751009451015010a540e202c52a0000340000c814011030503164805034400030f0018515401081100e40549407411845001c0e4010341d06802058a0101c0e00c500413800111084142e501188900d103260804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 397014946 1250 397013696 397013707
    0x10e1002160b0a020f1501064a1e04020906070804090b09100f15051c0f0b240706060e0a09060b0a1503090c0b0c07030b1608150303 58
    0x41c0c1d204280e072580038084210340040c0d40c008050f81841058015507904004043c0f0100c02d8100c0104070b43c0500c19a400c010101e460b25140880080c00070410b5660107056117901031104441340d000808401c00790341858840395040d00036007400e216420001c110907901c14040b68801e07003440040c0d07100700c00342540100204180c900041c5c07201f002d031014100280c000100801070350103001080c54060705004060403446e0042010802085e0110b040d00d041d40440350503400c403100213507564010305c60b00f54111440d1420000c14660598042030750402090300c10306c09040702005004840c2d41200240d021a14408400c0c04024665002040030510540300080c02c155202821007507040140e50740d0742e5003070308c5d80e801d10184466405610b885210413568041642d1400140360b801043d195014018035444680c6a014004030300d04550007070045201c1c003550380100015007601c40c0103502040303030851440380104503400c0b40054409000304c003070f46552040e501c4079803440c41d01d4502c00310240c0c0d05102c00c010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 397016196 1250 397014946 397014973
    0x20409020706140c09030a080d021207030b0306010920130306090302030703080105060f030a0b01030e012414030606190f06050306040e0a03021207050c0a080303070906030209010e1002 81
    0x341001801024001030003078103c0400c07107100c070028040364002c0c00e05214000d115540805c031700c80c0079079124810650b6654800c0000d0f000c1e00451012000d15801070040126498040e000800b4441d400c03000e540c00c82c0e03258203000b0304450041c400e40c140346421080e5890000c1c03000009024074800b10354181c9155a50760754140582c0c0503c0c80441c01070300040b404204142c1c109031010b01401c01107032001c0c00c2100d00340030007046010040ca210309a43e10b4980f10480790340243e1050010121100013480211507180150101d041c550016440303460b8140c0000680600030100004520001002360001c0d03202c800c01c00c22126200c0710740c000080303c0c942000846440e04c04041004020503104c0ca6242e20b442c07401c002c2120f45419281950350040c00e40000040d0780070a4070170700b02084660190711030b82203061052030101c0304003083d6045681810046105440000a10300c11040340d5591403086072240d8041301030303018811541d4080b0f0a1010f19283c07500c1e240da81d00180500c14130498620080300c0c072 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 397017446 1250 397016196 397016201
    0x1b06050f01031e0302031e120c221d070c02030a0b0106141312020307090c090611030705070b0f16060e0c01021209370504050a0c05030610200c0306130222020409 71
    0x7103403101030020001d602b0b02d64200f40c0603804400900c04807400181d9150203640303d0049421912a40303401c1c07000d000034074040d000c0c101c44480d00b900a01190100d44492a006112180038010304001c01e510301c41c00120310141e50202c4d0349016000c0303220022540340941c6840c84c01ca0001c000c80c2e040c010341c81e002c61540301a10400c032884009540d10440185050700103040d81d180f20030fa443c4a0340040012102007840040d00c0f508030345442c8842950780425028000e40d0f80107030340c00c1c603a00c1115a080740c001e001003a0030004000c108107003526002c098820040e41d6a040c001500705030311200744200a254034010201109449012407000301d0100650000701d0110000c002e103807403100c1403841c244218140352040541c490700e04903003004800c01b000e002071304a00009060300c4c85495080c01c464500c80c80b50540056000c842034000014800044003241c5403401030092600a12420f0002a070000d152501d82c0ba030b01e070300034089400c108942c903450f00040c268115404603c0d5020440090301e03000c2413 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 397018696 1250 397017446 397017451
    0x906010c0b090714060f0912030f04090204090b060c0a0f03030207021807090e01053304061d0402160605060301110408010e01060e070f1b06050f01031e0302031e12 72
    0x103011030504019489020301000d015990017008188050200300003640e0480d90904170403500c4910b2200b4000b030180c80c40c85a007088401c01c0702e0109000a1100c42900900251480908140050000102849110f001ea0000181c45902c45151039020541800c2c001c42c01500910b400752804035150042000c000c16003030a2407038640030380d0410101c1d50303201580e00050306543c02125001d500d0080064a00c6508450300c200000300d000080b6900400860000449405146050340715a958080606401310300207050595203d11542d031304080c6001d100321010010700401090801e01191900380041c90000d044940540da01c052504002030242c003d04000c00044001240d4120380c400d00e90b0070f580d45603201c100d10804581c107200311650000b00c030019403100da1400c07212031016211410100540780c10043d020500d40030600c0798086210700200d0507039003c0c1002000e4400e4280c041414901d0354180500140c105015590815041b42d12803418410505420380c101050001c0103026001c06 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 397019946 1250 397018696 397018711
    0xd0f1103120601020d0201051605091809010e10020f0417011508010c0917060c210108011401060c020a0b031008030f03010f080307170a111b0307140d020906010c0b 72
    0x82020030010351307410000210504060b100030300c22420402400001c20781554680d50a00a001c965040b59854168450151000c510070662076030420514060007010b110b510070740140900c840c5241421001e00849003003401c0700b0303507840c5414600000228600c1e038006c20301200e0754860103405404594800d600014261110000405e015158000f42143d285607112200509a482e0b2140d00c2c01400f245913503000c0c00000110760b40d0020b8a00426052401300d00c100b50508480001060b41d03d015030020301d075214514914a010390700d4100a4504c000d14842c000d52048803000c060245082060103160000c541d0840070310203c4c0c55030489821500a40051900c074107001c4010000c00106002d848000d10360100071b1071501409844800d404140203036003020050000410a40662044582a007501140d4064928244440845207950070100e01d51603c04d1080305030100f103130741c100b02501007a040e009141e003100840c1e0380d0903c0807914000703201e0b60500107070030190808548103101c0588078001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 397021196 1250 397019946 397019977
    0x90403120f0f15050f04090c0b091c080a020d1e030908090301060b0711060f070807021c060e06060907050403030e030a1a0a050c0304033e0d091401020d0f1103 70
    0x6103428801a000c0040c85c00d4801c5043c282c0d4517000c280d0b02d0741e90f0f0b826184c00184075659002450049224a0500340c0c00701055980002c4800c00c2c420644007501450782e840d42682c10703400410703c0894500354001248118150f00141c0b8844641c0240d1002c15424841c0903001e040100c1240000d00f15003041c0d02018088a0001e010420400c48004203800c00300c2c01c8459504200320390302d4805070f42c000d05100400f417090000308802507546107a40030704948034219140303402c04040c0c640b0307002804e1413264140d020b00c1084045140d078600240560b1103a102955101d0903d840c41d1000c48076550380400382034160041d1100b460104507803c1c00088018609400804641801c2410038103d6000804582c8503100074020302c40040c0e400300c0d20300c2c10810110a800d402c00c000c1c160000c00b0915641c2c40d0003c0d00742c1c12240002c054800300e44c04491240c50f8440c1c50000b030740e90013020014101940b640b8016008a1945401c46004201801c44a442c0c7d16240017000524247e41c0e180d5800a04440c90604 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 397022446 1250 397021196 397021199
    0x31506030317100b03100f09050c160f0b0c07060f0501180207060b030d11161206090503091f02010b010c020907030c1202040801151e0e070215150a05090403120f0f15 73
    0x1400304440010000e00744108203614119004100500900d2f06402d8940000e50280d014800b054200c800010340107190565281895843d000c456403114804071912818891113402d00c05d26842074038102d40c03440314101d010150384c9069130b00942c0401d030304503010360f038034051043d403910200000d0301854032540300e507855030740701c48542480d004e04035005400004000209014002c001507100c0700056110742e0100e803c8501e85400c030b007903008810000d9000b03039003c210844c040d00ca812110884040540003085001c03c003000444030501e00c0c1c24040c0d0043c440f8030115114500c02d41c0540354203902e5180c060803400000c4e08042c113071ba005034480003150b91a03d6060604c0311020b212800101042c4903d0200f1107060100c6100980651207407140ca0445100041d20306070092050303580e178001e00d0300b001c0700520b0404522444030139035000300360061143c4200403c160910a29050080350103071507944442d0a0085414050604a005c004451351142030040286400d4054500d810748541445041c45 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 397023696 1250 397022446 397022459
    0xc131d0702060c0a05180a080d0306051c020d0f110d0308010e0a091a0c041701021902010908030f100512010f1b1710080307030207031506030317100b0310 68
    0x142c030141c0400320b8110200848201150008100c9001407202400c8005d83c4442e8030004a101d05568071004c0c05001d003d071266855903060740114107071241103907500c1803659060705141e04142d00700402504040000030100c082120503480f080000c0c40b82121140c3c01c604070005c94088187c440c02140414120f000500c60b0f01b14116400d6407080d40c2c41c808100448407501c07003116010031329207610341c200000000b103080500650300f241c0141c112104a0701d462801001c00c18000c1d40b114114080c0507a903000441c05051042c080c00f454a80c0014010381544ca07919030700c140034000034110b64440c000c1c060000a4030b44844007105003902c074010001079008035140100341a2680310305440040b169400060303c0158200580c00c020101030a5429a15070f18070200c1c1007050100d400402c0a440081012020107500041071016a4481c25580c031000c00000347c50b10940d0305a0100070b01080e100700d036009841b05264001e0b41e01030184c01030503401660b80c4001184940c4113907848200c1032501381003800203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 397024946 1250 397023696 397023703
    0x52a0a0f0b10060f0e060d1401060e01030b03030313200301050a0207020f3001111206010210050c0d02030903070c14120708070e060303040e01060503040201110102030403080c131d0702 81
    0x1d282da070600c41406143e01000400301940419040c0c854130003c0b543d5002c508203603002d00700300c9418101004c02c65031210380c05820240008be045000a060848070300a9040110031380303016025041c184c980301c1c00103640b4265008900220302546041d1440e250074140e400b4000e10740203850800c001a6500102e0050021480042c4405070117005034600940d4189002600c01040d181260fa8403042400d1b4035000c5405008030100c0d204c1c050002159404c1d90791000c103803d9019000907000c0b0b403800c5c40e6114071441034800403264602c0481c400d0150380f04a010640003035500c03c100105580c50801349503280410f100c416000b4904120841e4036101c41805c000000c9007120011400500e8034510303041d000743e9102807600458240502e03d6000c40c0140c1c904105030780140c001c02c40d810046607151000140355400c00c4500b80c2c0010114a0100800344040c4202d901031a010341d1514002d90310402d446440f94030041031000521100e80300092031318118004130b0700e0180725844a204506010304002e15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 397026196 1250 397024946 397024949
    0x1a0f18040f0207030806042004030506010602010605031b0613051206010e0703141602030418020c120f0a0c0305090301090302010e010b03032805040b0c010c0f052a0a0f0b10 76
    0x307801d441006182c000c01e80024906502120844000c1918400d00400c11611007990300d10300c4a644010801104025010500b113050b900c0795402040b22550762403c060ba21945480100001c0901110703101e00f40c24150001c089806031520000031081d544d0b000720341034250313000a82440b600040700500100c603000a406400c0004d074501884220380c80342c40c80c110020b001d400220301c42c107071301d03a44002c05000388261001001d861041502c0720030710201d8540a50f0090201c102c0754051220f11800384205101991451042c1d203030800c1c01c04c007614105841c810315086007a01400400d024000191b0303800d000e22100b15109600104d060b0b48403451507030a6900c0c0c0048544203800901c03050715118102900004940070f20400203402020f000005e454034031840d00003182d12600080e00100c1c00b0415004481d00c5001e42d51180d0460041c0c02003219140501b640004400e000006140d10081280e0001c020061856064400100d526a950f1120b00c0002c070080b00c02103440e0b42001301200e5480f1b0038a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 397027446 1250 397026196 397026221
    0x5120a1d2806060504050f010f1a030c0309010906060f030c1409070f0c0501091419030e10030b0d06050105010914030a031b0209012601020f041a0f1804 67
    0x191407203012800ca101040c0c4510055200c0c01d85030410340500c241d680025000701005030041000e410f01018441500d00c00340a0070020481d480d10000c0c0c02a0540404948400c1c641d0b180c508549076400095040c0e84040e1014075190748030702c0072801052661203440c004014040051500c549145800d003039812031030340400d101300b00010704400c85403030f03c1000c1d0b603000e803d44c0b8021030001120142592580301c002d5020785107601e000c4001080001c40ea00071000d0310f2072101150050381850b0b0345088905d4000200500081c5ca990a0006d1428580b400d03081461007820b0110700300c6042d1010900d40c00071a9020380b25540ca44004104658014103c0000350280c504290041d400316400301e9a60384480c94000e042000004100419000c40040b5880300780c0c3c000c0120915581d036010844007401002400d001c02a11440400112003051003103070750781d469901507141040e10b0039208a4a407005401620305090f800c112111030032440c8070050a0a242401d070440c44945050280f1040b10800350262 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 397028696 1250 397027446 397027453
    0x906090b0c0a11010506030d180b131d06010f0e06070b160917030f0a03060503010e0d02011d06040206030402030a080a080103051203010e15030c0d030309022701030f0305120a1d 78
    0x6c403440d02e0104084103080345c1c50418a00c801151000c41c003000c01e00341e0240c40070701000301d0441c00b485044481042100c200c02082101c0c001502010708810754255a460301217103110509000b024060901c0c0c1c61181001010700781006090789a1110402c007c403417040c0694900d4a840040981100e0a034000e4050b1008102060002034846a564410281d02c01c94550020402e07041e000d210307030011406044c01500078019811554079266456031140d003404055401c240342282e5040c20303080e80c9441c1540c003100400c0341d0745858003403044660002d00181c3e00350007000303600c0f0085000b180040c03c0601041e5180c04a562440c01c0240c108034050301d03480a05101000100031541c001520650801092200d0356692012100000e2800c034450740903035006611000c41c2428560581d020410450003a075001000064111003815460214054900060541001232022500e25180c07003040c28800d0030890f192a80307040c81844940800c4444410590f210742c1900340e0403803000c482c080c00d0450719004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 397029946 1250 397028696 397028701
    0xa050d08010e0a050a090206121e09100908090a0e040b010909120809010914070e01090501030221010603061503060e0d0203030a0b0a0308030718060905030d030906090b0c0a110105 79
    0x74100c07000018140d045440c0e20303000424000b040940c00043c4003680100190380c0c0360700274520240d0000c401c0301d5002e40e400100e40c0d044040821612428414401c0c1006001d0603941804501e0060409071002d41d5400c00c1031000e940306072510340104010f00490440891140703083e2506241e80031050300484401810060302c0d000080e2450000035181d42d25007010200c50751800c0b000790042030f4844000e054000304190040204801044141c15a03000620244481e81c0711411142520402c2c031000350808d001c017020500108400070303407070341c000710301d40001c500c8698a48680c070640303003800c1c105034074000a2201003040003190301c10a504425030101400000701010400303922404000c064581840d22582c003551140e59101129025690103c0c581b9207a0811440040c1084184000c1c170f2130181c1d8100020480310b0103020f1306012140018000d00b90070340c0e4001c4c214090600d001081301c02c0c94a5101c24000981c0110401340309030707241042c158035000702c2c410003004040c111400c103000783d2401c0c05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 397031196 1250 397029946 397029959
    0x50a0803070b0c0f03011202011214150102070803090f130501180e0c0a0302061b0304080706020d0801120f081603020a060f090c090e03091e010801060914091005120a050d0801 77
    0x5d4a04642c8607407255042c0e0b0010b800142c40c2c400000710394400312032400b034100742c070410750300e1140340500f80c401c201071041038804005980c0c513a0940111142e60b0f00a2005803a60f1400c406200503148000d05062145201c0d00e280a054980c03c3c2c0000ca020721011005802c81403541c070502600a01500080558001240c040b5551000320700000c1e0086100082188504120080c0c5800310304281d411280d5481e80c07000340d20740311442e034005c0344018040c00c180003022a2103011040d040c4c1d001c0c0c211818a04005503111035200f10115411100b8a90030b11020398009503e00203a041c00c0e0080d00a040601f009191903000c0707034582d010b048122840c00d4000000700d50144207803015141e0800001070182c600c00758441c070b107016000c120759100e002c007416070071240c030028154001d581007a243d0a00d02c0e40c940c001a00c8001c40c90141d547c02c0320320b456203035100d4607080d80030381d80011400d24030030041600e0303c0204a0030b802a000380c0c0c2243e030020700140200a010841c200002c061071030070740f90741e5043c0f41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 397032446 1250 397031196 397031227
    0x30b0d110310050f0723130311060307091e0f141525260c0601090b150a35010b0306030604080a031b0c0b16050d0213050a0803070b0c 59
    0x401e4030b0708001120203082c800b1b01505407403150807064245429107968021910b41c1c00c441c03140c0030448011880b1155100e4a051042c1540d02900d074139224070300068246100341405160284042c9a170304260100015500c98203030b4180050035143d21752000d2000f001c4144062000703000311003107600008000c540316031007001e58001040524809500c201c0c0c90281801390030310404907102c022411844906c110100c000600403c80d41465006459507603030313610b103204100d613144071070b2035001a01d03a502082c80320050310085c0602250350404042e0511142c1011a85444800700440d0740071002404a0070306018402d000d00511415081d2840d6140c10340c0441e88605000e88018401200441e10a14180c00f03500b08482141d8010000102d8043c0320704020440c2a8540d230646880d10401c010030840d03241040c04880d42501500c64901e4400f40012120007036011800312240703110140004505d6030342d4411801c000300360110040d038503501c26080602040c100079141c803044507804c0015600c07a42c0c40a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 397033696 1250 397032446 397032451
    0x1d060424020f120a210b090901064203020c12070c09021c0c0c020f0d0221010f0e07090e070303080a09080d020a11070b0424030b0d110310050f 63
    0x800c0e0190721001c4d00e140a032140c424801c00c061840845048009800d18030351b21403a13050108950042d500d031507080400303003210003a000344520603024841c1500b19a59104040000090807607040440618007511804548e1a00e108000040d0700041c41415519003080206050f84c4065170441c90440a81d460b203030034550350720900210710740101d8000200051810460390450001200748a9800c090b50018030b4001a400200d100740201241203407135080c900302e64138031981c0c05018200c10a0712240c00b206489111224180d0035904c90900c000d64070b0a07400f541301208200f178020441282401610307030913682180305641140c2c0c4006410030100380d0001e64150480400040010703848024282502288103a20716151010700004400201591003610580702001a000b511207030707a201d065075240ca00c60340c4203880c2d54113211003034110400001020f41d20a0101410000344806c852000b01d814400924000e803503c044000152206003414811200c40001c038180411061170f000c00401c0818102 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 397034946 1250 397033696 397033723
    0x706060602160b120606160b0403140315010305040c1d0402030d02010b0a120206090603190606140a030f0e0a050303100f06050d051f0906090b0d11011d060424020f 72
    0x1132004200152034100448540d0015009407503014591410701c2010620161021800600207880c0c2030012001c032025280035103840e01250203011040c000440250201034416202400140390010700782d912a0302100e840e420b039544440c054a000d004141c02d0001d8102041c095904000a6111b9a610300742c15a0a503131945464510311480385c00400c003e401800d901c190003c0000083c071a07c04041d0342400458265800c0500086450381c404481d0300700311034480c2150410130710141c240507001e60032241c400d05007075a00048680100e0601490400b5504054a00303400c000700380144641e034002410040d110951070b01982c140344c01002001882003141d00c07a4100e030707a500450480c3c0c001580c01c2e05c44c0700340c01000c4a105034590382c4140c01070003a485605040b80c6884840180c60900442580d245e5400191202c644c104403c01500c4d40011b5150055003061028a1001182d40345000760014044051a00804464008614500d160f20800c074030251f50000101c02c90302d00340001d896051940d03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 397036196 1250 397034946 397034977
    0x26040617090a020d02130e1222030512070609120c0c271109030a030207230f0f0312070803070f0e03100f0f0207050f0601061e1409060706060602160b 66
    0x500204250007088040c407650701038007e08442092400f98003018010900040346007020402c14000020903a00d09d9200051442d0480520980b01225a00107401c0c03540c06510041107082440e91440017140c80841020081810045824180030720710b8409009014400c08420b00e000340314440d00b01c240070b05031000c48403e496800b0780000362002d4089d20440b031800790440b074140405250180d00c911b114091102c0d40c000090740b5542c546c1880101148000d4050004810012a14240452001280b5001c0c0d0035218004540305811a906c0003082960b010382c920507101d0400c41e400500000004155104001ca0300d841c021a0b40d40c0464800f81003d2103010019032018200070030700c0a020032000e103410042c404039410b0240a00420404607080c07050341a00d138244c1c1c82e081c0c151101c216900090780706000003000c2100b140e02401002d20030000c42d00045040c0f4810900142160344405000c4541c6a01d42400b003048503010070100c0460b407840c403440c02c02d65041103011020f074094000e15100001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 397037446 1250 397036196 397036219
    0x307110d0209070908011505010c140c09071707050c1009020406170102130506041a0c03040509090c100201270f062a03090f26040617090a020d02 64
    0x1a1100d249003034095001d00221440c0c81c000d08041d20b9840d403482409495403c040020004000c2d038500c2609441d0140c460200032885526401c5440301100211040d600c10541e19000c5552410011803158038542d07a03180ca120006040b086803280e01030429010312006229041002c1004981f640740403008080010304281c2900011380506210b40c024031166681c4400c4400001c41034004000148540800b0070304a0b66600c1800028800d501c0b800c10ba0150419404034030405450040003011030110071613007050344440020b601c80c4000c0c0d400802980c03050700064500d003002142e03940d01d4440d40c00200100c0d52040c04a2814420400600c0c260601c0b1441420070050303104001070034190020400c00210101c03aa0324400810b458201290740b00300182e12071400c0e1322a0142303519480c4c2c00006880003450310703030b61012440c0500344030749100c2c600840c15103030503011a0f01400c0108070766580c500a041f04200ba9440008010304851a02e4214071380c0b050140c1c6585504044055050303d0380705840 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 397038696 1250 397037446 397037449
    0x111608090d0212010209030c0f09010b2b09030210090309170f06091e0601030804030803091903030f0c0903050715050f04080a03080105031506090a180b1b0a02030711 73
    0x401459070003944942440c0d50581c40302e10540c003415800c2810340807a48000d50241c100064080c9000390554080100070040c480182c00e480079000450256845003d6030606c070780031085461800d42e211070f01654580c855804c0c03643c1004a10102d00c035601c030401001005850081130303a0350728003441800b0b01501010041d0305d01c0403c0b02c40d00071680d0701d0540e00b03141000003003541c8841c440303d401042c000004a10201a21000c12124102c1340d010802d5880c08d440c640d18440560801895000e480c0280042c040842d441300f0541c1c0c0070f041c4240e8001580c0c47e42e1031145800c40708006030903020092001020310000d800020b0503802e480c400200440b08460902040390940b04105007640c00c1c101c0418009034240000500345c86080c42521112807aa032a40b0074140e942c0180024003105d040c0040110320641899811250407210f800008606200f00401c1400803001180d000c88540780c1c058200f003c0180400d0802150021070a03295141151506000f582c80c010380300080e01203401c4402404c1c1e42d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 397039946 1250 397038696 397038709
    0xc0709050c03150907120504030e190305060907081207020424050102010b04020a020a120e0d0311010c02030a05072d060518010c1d0a1706070311160809 67
    0x24948884240a00c1c03406028625030794105444000c500d5000002c20f00c0076250a0700c10b60320071402030b614400c81211140215000e0319001d0000d5003400341011418043d91a2403100103400c00c4030b85000c81c200761652a12500d0b000005002807550f070004002485030150101e0b1003284100300f1aa83d41e20796200380001002056075514440112042c240d80e03141010700c41400c001120b0b000d07002008140c460310280405d07482001c0000d801038018401e0394001440081c1000707158285031906000010084010414a40f0050000c0d400f1842644103490003c07024018a02d003040603101540c107002000401801500540c04010049100141c81da40080d95841c200c5110080c51441e0000c0d00440f0304104004000644420854800414418221460500451790340e641141e5074a034903480300744035120500310b503500500d40c007058110001409442280b01c10101c07a40044c0640081d0070004005011155407102065071001c2c10b02446030305484074414000026042881d44d0f68400e034401c0002d06 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 397041196 1250 397039946 397039949
    0x105030901060509040317060105030c070f0501110c070801060f0b0421050109060203041101031103010b0711030609010c0906031a01030f140f010603060906030b0402211203060a1e030303020c07 85
    0x3c014601c0da08000506a110321f581d12504001c0d4440e40254484000448141c403003140c0041c4046020082070000601c42c4880d00c0700c0d54025000000d400c004081d004886901102d0080c07040d50000c00d0a05c100301c070a1040100a02c082003010505501c0c0034204051400b40c4e10842c900002071400d41091045c1c415104100180c2c0440200031002e21850808001d40084c0d6060b600b111412144541170750203480b030340108000c0402c8075401c580c60503a4482c8103a001150466000b40700c20300380c200d40c2c4c8003041024041e0090200108001c0d006c043d00401100710b41c1c1c4004101400c2c010381c4859420168044511a0b2080c0b0300403d081ca04c0440340702c05814507202d0030310120050030070010802504111036041c1d5a196030140f04080da0b0b0292101030b210f803030101420040c58980440c0051510501c0d10307040c0c01490071401d440400c1c92140c54207200107a152656030a80000401c00c180c50070701080c4015010780641c3e1994030074002d06454440c806404000d060503400200c50180d0f0303808001140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 397042446 1250 397041196 397041199
    0xd05030414060403020a03030c0e0d02090915040c050405061e011d10090503070503030f0405040b0a0f0b0403060c0804050c0d02060d0c05181c080f1905030411030708030901050309010605 82
    0x34010f04240ca0000e649010002054000034602401c01035034612442d507090000b18001c06c01c03030685c282602040503003038000d40180705a110303501c0d41c02d00c01040c540041e480745008040800e807451800c0300b0721056880c000c06079482245c501021004180440305444003181007803910800b014421a482c11403081b4525200354030103004078140c0075040e03001c2d4082c2c080d20300540945000701d5440082c940c5d280504040b213120f0600c01e010921440c10213600c84909400001c0c1074074241c0d40d85d4a082d01142d921504044203101c000902031040c8400c40c0100c0444c00580d10304000740d0324242c0c44051f1101599480284a0032041e0542401c0d503444200381c89002c8804002000303140f0302d43c0070140a80e03100d0850100510b000491412a40ca4642d82c1c60030a5803c4400c1c102196900b03540317400844c0c4c000e49040221440c20b12180c01c0300404645001c1c854275158540e40d41d241441c1c1002e07600501681c0620f0312a50241d0700034030040402000340c400c100000c4c00d01545030741714481d01d5405402181c1115 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 397043696 1250 397042446 397042453
    0x60a090509010504231002090312131409040b0126030d0c02071205030316020307080403060c110f120903071205061602010209010903031407020405040804050a0f080d05030414 77
    0x40780845066124500851003880c03914208506604080d00311a034003201c1c0705507500006100c1e0205d465a0f001090b202d40c00034196040742d0300030007006485d82c00c51400e0300b0141c04500c409022004d003e401d540381c1d82004580c0d0b0141c514240c1ea50010100d01409000a5030f407107402c01c1703034510f000d04006154804801060301d071607105c0300d0340c040010310742040c0c6140144100400001c0c041050804100810340100c0910306e195901c3c941040a65054100c0030110f00c8108054408511200064000ba41c0f0405001c03918082c1c034280201980060405a00c00b034110740d03070001801000248240126054504680d111466400041c0c1040b440e640110150300803503002804203e40030034002e1140f4200300f10b681c0c400e50608412401c038004c032944079012807036820091020038003c0310940450320604070480e207008269070224050320802c5d50201d82c2c00d84045018401480c1c4010188098105070a40544d641e02d03100803107a8034800e1403440c505001d40000810309019a2084040701c4c181b07483d048 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 397044946 1250 397043696 397043701
    0x51003020d090b0412091a03010603090318090f11090a06030f0e060c190504030308060f0d120c060b0d05071208040302120309030d0806030d080a180c03020901090908030f060a0905 79
    0x29560b44126480204002046d40001142d0115142e0150802409040b111415a030078210b05400401511030141c2c00d224003929446004640c210051015141d0342d1408110428500c9000e004e50b1581d40415040307031801c0c0220342850721880c4204044a880d880c0c003003040d038400d074101d20050241d484620103501a40013003150b41220700c030050192010041c135000a44480d00b100310f130280114000180041c00a402090180c0b030075081c2541c483d1002840896800b00f44c0d03640c1003580403613030034440108014101d48001c0c02110310804168200c02d0308c2601c850010b0303030f4626458480078003403c540c2c01c465240060901149009035005940d010b00070800521038071109036965006024001d01c28800d80401484aa100e4520603005003400780c01070003240351040c1c00b03841164006044501e02a9900302c4070500c0a40082e01500140c000e9030718420590541c014440210b50580210002e14203080d400c0c03002910440450f5480b02d2017200c1350889e600d51400080d441e5100b903001081a03800d000a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 397046196 1250 397044946 397044953
    0x20d020d061503051009050403020c0607060905060601021b0112020d0c05120a0606120b01121508100606050a0c0f060603060608150c180307030b01030609030206070207051003020d090b04 82
    0x8028280d600700d50502c500d981290718100e09031482140d4000007090121010440c2001d00d03082107070054400c1c01500e00d128180b0001c260307150481402610000d407500d20702018000f00b40609500000280302804034015101d643c7c0c0d040060080509040000c4801c40c003003500440d5040c2e071f02940000f6402e008031061510000c1c203681001c040032403108a42c00110703100c0080c0d880350508603115a1140412003180da03125100a00d9500d8541d4184031008a004411050300e115514030000c0909948001508120b000e0b1324218454003001d603a00d02d0404203201c1103420030b094844040072803070f04042104162a0290520000d904000c01c418103045010003000700b0f5400400507104d10200310354200e1000c0018030b040b03400989a060006400f0807025000e01d140303e00700318140c0700150854080a54036a107150107804268815100c155a41c0982001c05505002e40d40e0892031502c02041d000d418440000d0300280e00440c9070307050581c0002c20f4010031019030482d000485d0883c204210381d1800e400c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 397047446 1250 397046196 397046201
    0x3702190e181329010e01090e100506011701240203070b0402100207090f06091b09090e030c1b1206010b1c0f05040f020a06090e13050102190c0201090b090121020d020d 73
    0x1000c11000e0300fa40082000d15151080f900422340d118001e10f610480342e00c40b14020040a02003038100004210310003500724200c0106802070100c0d000107035685490b61301c2800d00b8400d05220f101150006c100340030204403011a041d0300960101c8201d69090b204040613850030007291b0040600300d00b8240400c0c01e0080d13581c0860210342c80c00c1010700008e03442d070266407050416202c000010500708030040c001d503a9141e00400d4448050b004591801c0c0640c03c007549048100350b8848480004210714410900305a0000900000070034014812075041c480004800d0182c2030f45050702110700d50703070f06030202416040b000c448060306c0b0082080307040c02d0400d03016050080300d082e4068461044000785861003101c200c0c080703c600c400c40081540b00c0d005143e04480c034000082c0c54564081c00320b483d0180356400100010621034684005c0c0511f18400034251804640c4440443d21051250108030b9810420303051809907106001803c01c503a20403034100070302408440659141c80070854014002a65 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 397048696 1250 397047446 397047449
    0x218090a02120a0516150e0109170328020706080a06031415070525050709140a050108190f0302010905191502033702190e18132901 58
    0x15010741c2c0d45017404010300035103144035110b41c40031410701c41d902040c1603210f805076100c00c0205142090960740c2e100c0402c20454295030004205410008402c414245401c03828000d0300d807100302c00d42110045040181d100c0710345102d07105c18044010002026201c1c16440800a95448090105c2c05030f400ea000350356031403540c10201e464031361641c0440c141500550660f14101c00740b015a07218000000c0b0230111405d0100d02c100c40310700c190307200820302200701c1c01a5401d5901324203580040e807800e40e80750410b903141a4055081c917001600c0c69840b500c8003c2c03210004540001030400c0076102c1d468124014405988060315600404420819001d0001c0700700c00407601078a80600d14900c0c2c4c0745904101e100c01e0350280c00c4841000040c0a11110b04010ba0a04448480c3d4140080769000d181c0c0c800d0307901c11042d041c1241f80c1c1480e2901e075950484002c401c5031005880da4111341010840c1d40040074000782800038440824841e40701004036604a440000002048144c1030309920364483c009220207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 397049946 1250 397048696 397048703
    0x1106030a060914091e0f030406030e0d030e031204021306060e030c090108070e04050319030f1a010c0b0a020d020d140f0f0c0f22061b0218090a02120a 66
    0x3400b841e8110000c40a81c2180940c1c0750070007030450207100344541769420021100c028480d0056900000410005102501c0141041d48002c074100c4000241e0a0820790500c0d0803400703252611100c01346641e00082641d994543d1100180700640381c6000240d00d021128102c00445405c0080100e552640800f00501c400026811901130802140420003004024050a51650320100d0100407820701460807580160240080c1e9141c5030003007424114040a10003c0c2c0c0119807140000c440d421041d105003000e00c900043d03545540004640001e041e614080c1010303040035802030104420315440d90403504a042c00701e104660354483c901702c40d00a050b20210640120024100180300c10088560f9144280b00e03010340d03174049985061200410303810156420260703400600c108094000d002980d09994010004441d0256242c1803008080c0d9a071035807121440d058400c8440010303261404105480c80300701d07600020541e03032003d03400d14040002c940a54000300b502d402c8110503501041003c4c0481c00f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 397051196 1250 397049946 397049951
    0xa090c0906110d0203030606130305060f06031c0f0c03031823030306090a1a13020c07060509010f030e0a0803130302060109140114030c09090c01091d0f041106030a0609 74
    0x2070b0034001988841591a0010260304104001007a41c42c1482c000d11040d91035608441aa540700c0c2c41d00c03490004c04551404001c0b075100700303004842c0350030000014200301002d100f4050070403c070401842361011903807040501c0803441041003054003d8001d6410780d40b0300034502800c680c080c1014018400c030301c00703242c0d20740700c1c0e10184003511000401100e10030080500a0240d5461321810500100b0450031881c1d030400344444003899596641c1c0310850120200b081c0540c98640300700343c0c141004010781c49030007400400c00044015036005101c100c3c0350b00d43e500300003805224141c14603082001141009202800020170481a000c00030700c0300c00b9140c0203508541c15030ba2a003803003808a0341d400e20a00345101400c3e00400c407041d8500e2004ca4029000340694920304030880c003281900f0002d5800c515141c00810720302e103455920030308050082c4100f811030300d035044458145200c200c401070302e4002c18030716103000107041c0700100907025086c0001170015a580c2c41e1030940300c0300504213401807212203030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 397052446 1250 397051196 397051217
    0xc0f030c031b15110f1f23040f080f1803011802010816090b0a17010807140609040209030d030501081212040b1b041d0f040209010512010b032401050105130902090a090c0906 76
    0x1e4070200d24195071111f003044900f691215201c078443e80c05110000c4031011410405403686501000140c01c40401c5080e0b01402141403000b010700b03403090501d0040341c0d09490b100c0038000d47c0e03024518075005294650240b0b080341d8003030801c4401580b26001608155800910441c1e0550311080e017209065800310500d1890b42c03149600c0da191043d9204090524200d908010311a00d4038400030921034500400044c50101700101103401c000a0140c5940405c4d40d81c0010028000c09100a850142c1c055000700c1c6001070401c0d50711900e0001070800303012a031003000012101003500d000075504200706241c803a00c17150780e101514043c10301c072030180030b0303407907203c004269600551601a8015640200503c1143e803d100c10b2050b20f007680002c410303496480b0041c49919031028800c0e40160303c5212500d0201041548000c0500d203c10303840a41040030821483c08002c11a001039400e484c00d0940c0940d880c0c404400180003c55643c0086159618003144c00b89a250002841011a085500c4445010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 397053696 1250 397052446 397052471
    0x4031b0305011b0503070e060403020904030822170901112b09180e0c18040203250e07020307060212090601050303041508040c0f030c031b15110f1f 65
    0x49910f02003008600c050000c144c940d13024101c2d007491010003420a42c101590ba400041e9031100940d02500070078030207014003070340c00144240d00422520040000c44402200d0b13881100b002c1041e9050034591001080d00d0b403d07a886110050050001c50f42100c1c0008107040040e1030088085040d92005a080d1043e0301006c2d0003034000300c086a89080c1824180800e01e030a00010700001d500501d40b0703015004040010395a031000340e040f04250072000301058601441818070341160440030002120003812403400080a00510f0002d076140d0022000558581d100300b070b843e500400000600c0240080348a241308540d40301c0740c51082020f10200c48542e641e41e400d054482c41140244d210350315604d03191507402c80c003a15440390018070690404181c2907031840c1e10304802c1456042280c11421a800400601400052094150380369171500c84055242c25602038180351160126030501c5400f07041080600d1042c0b015800e0103880005030382c2c9a9568502c00103810041e000504036440ca880705045d07e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 397054946 1250 397053696 397053731
    0x809071d0f060f0f060304030e09011203030b0a050609100323160f02100e100e0706080c0f0a11010b18180111160807050d050307080901020909010b030601030204031b030501 76
    0x9040c0c058031011440344c240d001c0c00307082d501c010420703804c0c800001590170b0f494442c409200d0082c4048030454003000c07001d00d0f008080d1a14540000d2203001040c03020b0084d44e0350501207030900b07501120b9400c0041c00b102000d6000d0400c001e0340c42c0e1000034a45003e050b03e905210050301c60034500c4000004906810420b0316400000180701005030300c4000386128040c500d500c56254443da0404842000581d201030300242c0c6c0c444080d24081d038100c5e46040142c1c03a001010507820001034a126800c000360740080702c555000303003442c180400c882c028072003041010a50200303204490140880701018810203001581ca6020340e5510459210780f0800048090113126080340e4850b4007400900d084050668107035145507842065034044010041c03000000c0c400c200d4243e584140f6103070a502c07440c001002602049000706040d500c0d0740100941c00e02540c803040e48070305541a20b04400e44a4440d240101c9c0203005940005140855484004c80759145580c51241180d100d030000340024a2007500407241b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 397056196 1250 397054946 397054969
    0x905070314040209130c03060e01050c180f15030411090105030a050a230f06090705040608060631020702030d03151401050f0a050a0908030405060405010809071d0f06 73
    0x20441c0d11580414014589421450340042d8880c3c20b019901e95151244610f1910315072048500566a08011061f000c080c00390780e5002290500f0103040c02c100c1c000c154a41400518094410034a41314010043d0b0b450348440070300754003080301441d10b07840d103464000301402141a180784295208e000014843c900021345400090f4807001500d280e506070b9807a030f178403031000d41d2818805480c411003044103c04104900354603a0f5a500003090641080360456050a0080c0c0004d802a0b0400f0018043d02100181c0e1b03d401101c2910310004d0003210768201000c40103002001891841d4500032407031000701e281c000d8103039a8002c900b0b40703054000868040d0120f54480a02007083c0c80025400c01520845032040082a10113040013450418031000000c890351050300321b040440c5c40800c18a80181e40883d010010b0103044006511302400c080001382c1502543c80707540c2c100004400090010141408a20001c0c40e140600d1032440081c00009012a00200c482184d8540318000049031450040100788 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 397057446 1250 397056196 397056221
    0x7050f070b0f03040c0e190b0303040f03030f180f08100504120c11130515030d090b130b07050105042d0809010c05060f06040f1104150210090c09050703 67
    0x2440d2402c00140d5001c540c000a00a4481c0f5403040000509a2048060148500c00070306140c1c40c0c1c1c880030f030030060454404040c00d60285c2e00c01d11003070055102507661001901d0701820410006116501d04681402c4100451681810b20310400104071000082410603030305040181c6191090340801e810440d9411600a401e07036840c1100c2c541801c0c00b0380301214a10307010380854070340f014200c000300313110f0307071103a0b08002d1800c1d03a4404004d1104001514032140311021005070541c03103580340d40107090b460a402080b912007000070310f004800c004000050010411641d0030740d00d0301c5550504074020301c0102e5099030b13003440a21820030480000c140006104440819175012000243c0343c810090300940c201a060111650000021880c200b2a55102c0c0d40c40a40c10318032490008140000c0c0c52060003e040500d0804804071400c2001c4416241a1001d17242030505586031440105d14008030240c041c0784091404502c00144211120080181c800900c0140140c0c3c0b101c0c3d404504895040c803010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 397058696 1250 397057446 397057469
    0x2e02070f03050306130203091c050304110f060403060f0606020d11070e04060e0303040b04021002030711300a0c05010813140c130f0f09420207050f07 66
    0x100e0009000b070000d16003090700505100510445c0e01200b404990090718882c00c030f40d1002c0c6000a508e21a21071074008004545816400d6050655480c1c1031045d40c10205445a10310080d510b03590b440f02c200381c1e8010354100100380035030b80e262000c030b8005107407602075130005002d500094203080340070301008000b00306440c004001903864000758404000020f0001c45505484030f00500e060f000c100059401a4003500d00c101842c100b5104100340c002c141d00c1c0c0001035400c140803a6000c90072000c85d180b101007040d02c03421905900154584101c104010081d640c0b0103229016041403207001448091442c440c20503ca4002e443d0001134941070b1085030706203a2805882615000140340c0d43d000b18804498001b1901091001800a0404020715042040440c1e54203400d074000324031409210016100440c003001700c400d10351105d916041c064030382401c0501e4045940040ea0140d21098112001644002071901803054003041c003039032007110700369564814141c80c04044c45c0003140c024125912010503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 397059946 1250 397058696 397058723
    0x9010e010b03100b07080a2318060702040c11101a0f040f060b070b011706070513030f08041d15040905010b06040e1f03120e030a052e0207 61
    0x408840703600041043c2400843d40400084040e0301c0c101402c0c82501c209540f646070320722004010900d0403c80a21003900b00a1100030302461402e0301140c0b0703070b803110403d201111000440454a54460040001e41107440c0420099105921103402c445016441054581212080102400341c5107038154041000712907080e0f11241c2e10700001644102c940c00b41011440701001030408046921070f42c0403094010740007600303a0420050b0150a409080c00612030752a40c518034642c1039407035000802032400e0003000500c010f5070f180d410034928015a80403403564100e054618000d40c0581041c0302c0c40c0c09400c030313070007105480303403280c0044510807100701c0350314112350001c80100000b401058400b0345855680306072001e400d0305c1c0e010081010b01040c1401040c5030804100d0780e1209190103c007001c0716143c980044c40094014208001001100d2510303e0300b20403a000004d00300350f010342008000e440381c180d95190141c0840c1451060140c00030898046484030b194180a80c8200030000746a44048100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 397061196 1250 397059946 397059959
    0x30906040e090a120f02010b030a0c0b0f0d050405010c08062e09030506010e060f0303030c03040f020f061b010f0c0215040c08071e06171311031203010f0509010e01 72
    0x1c0580d014034214100c9a951810791030307902c00c2d070181210500000d40902d01c060089502400b1b17049968034281c00a1000d0406600c030004080203600a1113006d00002414101035a1080c3c1618104020746404208905080c43d141d80205a11006940811280000100a890300c0c0b41c20b001510500d01c10400030324410a60302c10718540c5505403100b8440c200c40f012000c50410032a1901a224094190784142444020000d600208220341e911030b03031040082111111404090700d4003d0b43c001d40e000603c01c60f03440042c41c050f02d40c60b00150080c42c045010b00070001906249060a51404000c000d51608040302d8002d07139180c01210307005a481000d0010340d070f604600751654030030f0040361340c2c1c0c05603620b8103030b0035003009100d52001c410302d800c0407840010303408000d1407980100742c0744c10300c031401c0e001541d00c1480000e801406420304406561000051110030a14600300d030400a040c1c440001d200c07640c110890f00280608218404844008540c5042c214800c0e4140c0d100e1503171200542c0e01c3c014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 397062446 1250 397061196 397061219
    0xb090111012909090a0804120314120402040605040e032a1509010e070509180106090c051b0d020606091e01030b0a0506030a030509102a0b070203090604 67
    0x10004210340d42c880500c00e00c100c0c212074109078648901d10801d1031600003402c1003020381c00508201ca240d00141080000181040100c50485051003c20300c0311540506003618041d8040103622143c80001505410030000101035070321440c4203e508100280e2100c0034402161200241a401c95000f00200d0302d0307032082d48204840c06101a0800704203945c03100c0003242040c0c08284100e0b004a0041c0038889154800c3c09042e040040c458000e001c0d042c40c00c000550101e00250508100d0400780d1580303a2200000c1d04010040c111200f13051001c00c1711188024000c4d84150703011201308a070040b200401032004202c0b80082c55166004120b030f07499000420111030780c00341000e00744010040c002014000e42040d074078020743c000c3d1054061858015407480c02c0e0b890042c804c038800d41040000e0000250480d065680403001500c0e801c22511050109a030800c4bc0c00c149048840400601340403403100302c0b080d10050500c9803855058940340d006060b640c0b4010340384100d43c4a00140001e110402c40356 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 397063696 1250 397062446 397062467
    0x100503061515040f0501020f0a020a03030c0302031b1e0303040803040b0c040e040305070201080a0510030b09030904090813080304030804090b010306170109031b0b0a0e030f0a020a110a0b0901 84
    0x2022464000002c0c1c565190540c400d50110890014100040000e5070301845460440604200608a403000329400a08140c450380801414010949101001d00d8400c000f6a400c60b8072681341e020744040684400ba0703403401d03e190020203c400000c0108001c200110580740200d6000d04403a0039920740d83d440500480c0b0040c4880700e115000c0c0130014a144100100d207000b94069111f40342d40e14460b0000400040008003549101420a01808000f03100303030480d201107940100c1007501c10b885e441e59490071480b4a0fa61a913205060603e41c0050010740e2004041e000c400240302d4a1881d074909040740c036800340784000342c15200c050200b005100300c00e40051220010524001560382d48402c02d28112a034540320700c1610369900c0b85100101504a22050603203041c3d1042e0f015040d24980e50792180b003030002d1000d1035241d112003d2100e202000c0099804d0304201100c01130b251560542c000755540107040081c1e0324403440c2c0c102c14841d4180801010151502441080e2900f0358a100544032034442 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 397064946 1250 397063696 397063699
    0xb01120f0b0a060e0c09010f0c060b0d0b100609051003090203010b13020903010605011b060b120f0a0b0601140904020c120f040503060f15010f11060f010501081005030615 75
    0x359940300004040c034114910070105008000fa20358101108491101401054400d40b44000c00c250045070380c00c03140308010361903903140000e10030429280c06406841191012508000e003070015100308030301805a90b2254000040c030162a0707607200400c076500074051150640101504100e0621030348603030414000d1900180011603040716010100e10100a01c1c201c4001c101d07804034040c9180c0c94203006900051800b484c1c030929107107101e81042000711045000514050341c8420b00d072071a46980c480140700c40c03560015648400602c444035601c0c0d840300b5900303c80e910245d800044156000e40b03400307150b44d40a118024242140003040c04007d520014180c00c2034482d1100c246800c074000d5005043c084607800500e51114584020f0500c7e006000c0c0c80246040c40710010040c0e604123041e540301d0000740c24038004819045d0302d001038a5104019100304894000c47d010051002c204110082c100c0b882aa54501595100341010703a281d8054023840741d054001c1c4002c5054801c030169000e10b445d90 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 397066196 1250 397064946 397064963
    0x60e030c09040f21050d1416050d0608060103030215131e03031401150e0f06070b060d08070606050a0e091f061710051b07022103030a0b0f010c0b0112 66
    0x4044d00c60b499103120301101e200042c0340041c525407164114000c40e020000460114502d50600d218641406090050800200070021514400400c0242c00642c0108500010b64919584030304000b0740b42c00110713a4603810040e490000c1007034800f00030340c41e0f030690740c2000a4210003010302400f943d0a025200f1b0603810952a4000c1d81101c40540390030750f000340f0940c4038100f0340940224018101800c0d1400d031070321841d04958944041c8e19224110342d0803a91103070b884180c42d51791000090b0401c10545000c1c01d401000f1490604101c1c00d54041000e031003084036540d03201aa12701e07040c0041071080301c1603d05500700520705141c00d020300002d030100e401c0c030803c003103246034540c1c921185103001c400350044141c0c4202c4090704500b070148241c81e0041e43c803074a50404d0140e41c418084480c8141d200c000d000b003501d800450503101e6801400b00a0a5209081d2a41e904100128402918800051912449400c0b2201480d503000b2a81c04003d03980c0300d818246142e103001081580740d28190801d4800c0d14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 397067446 1250 397066196 397066223
    0xb090a090515041112220c03060b1801030809040504060b0312030109180302190201020a02090406020a08070f090603050c1608040e01091103191e06060e030c09040f 72
    0x84440c02900d2050111211005030011a80c04010599003800c0d00781044480400107520720505c52014542e0040c0c42440010354410394038120500d00300d0054010700f885106c0800841004506d400051030090103c59014018451000e07800e5222001e1200811100c000c001c80c0d142d501b4940c00c09540913014210008078544e44102090400d4400115141d01000010052141c1d005d01e10a0180107011540b09901034030480e64003950701c000300c0a03100303c8050b4034031521045a1082048802c1154090504243c60506141650294020040d12004507640c540015029445170592048683c10b0355548041e242c600701040c0c00410001d00500e40e05d000c104202d000300300c41c880744c19142502c26034405070b840340740c0041a101806e0613041010f0144c00d21012202c24299201960342001d58103c0520f20304030710901e603500030a4070717501035030b041e41d84600442d11101403a8404011546076886588030f19540c0340405072101c040412140d80034074000c1c080340100d02074521a1600710311506203481900f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 397068696 1250 397067446 397067459
    0x3040f080c0603190f0501121a070219060632090402220207080a0c03181d07210c020c12120306011116030c0608190506060f030a050601030b060309070b090a 69
    0x6ea101340c000c0340c1609000885802048004100c04860450010100e4014100100c0003912090303030700c40a443c008072900c001e030140800d40d0f218200929403c0408102c2240044d507070388424085101941810b84200151040341c03c00c0002c00c3d210313950040c030031440c00382c0d43c040c0344c0c039a107480d908006c8502e5400c1c080d6000003203021005001d0341040e034440000c00c2c1510715004100201d0076816036030201102004201c00c104105042607584840e074040f100039500d41d101201d05020b082c03c00d90340794003502c015609011030355005c210240c0a941c241c0b00c42c2101842030207110804d24221035402e40c0503041c2ca414411844001e160803100c1450600c030524001c41203070389481210314183c0c007000c800c10410800c016824030b07010300138030071410016036078070b0440040d01c103200c0c0c000c2021b140e00d80c40c2d1300010405c0c0e841c982210312446141c070140b61281800b040364401800c00b21031180c00b0074070304030b840c4c0700031302d048001c2d2442190640024120f0f181050501192600b00c8a0125005007002c200402c02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 397069946 1250 397068696 397068701
    0x20a08040e010e011a0a0f03110a1e030e0312070302071b1d04050c011805030f0f0c03010b0d0809220c0e091005060f0c03030903040f080c0603190f 65
    0x24040401181025410800400d0010f601a0300031020808104851183d9402c800709a0310310204070b0500503c40303808120b00750050044e02003000107040c1c0008605408035008051540c207a0106c507541005641c5c4440d06404503003269100013820340c0309001100b00001c0e207491036980100c06140141c140380c03041d0b59203c100300c00324404508030b0004c0c0100380074070100601421682c080404014005061603124561100c100b40c100d181006000340c0d803207107400d03025140c3c940201405000c454000106d0080c41d601c41d810054a80d4170780c06030748407110243c603050080c82c003000c078020004104001c0c643e41380c0003143d0041c1141504000039000ea12510368100d210210418a0510007084a120f08031008044611001d6090f03ca81500b60a011001c4942000001560015a40c2d603942d010062030204860045030a40680e80c800001041140c00f0040058401c81d914860f2849200340c031080d0042c0c540d13201c038072a0754200341c040c000a22400383c06100480100d85002001035081131030300c007000a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 397071196 1250 397069946 397069949
    0xa020c060412080702070302011d01090b0310060818120309010f091a101404090501090501091113020406080c031e2707080a02010806060d090f0b01090c0c030f020a0804 74
    0x1928070603084500400b075048000709500250b6032000e00502425680060f25400e210030391600d14201c2e8030b0f4584080c4c3d00400754140644181e411880e100d03e482c00c0b05000703080140c056000000c13040d8011a8000d80098000e440c441c050f08003a1440c03000d0181413098607080208843c4442d0f417500b181d890010507070b02c94424064002d12600180c008000945864036178083c0080c228000c069004112541d0700c800c03103000a010441d8082401c032660701305140500254a000307450b0f9442c3c45890310030090002500c08001006a64140e0052010320042049000350300c11200481c101200203800c1402076001540d20044012500380b64800b07109410011603000c4540115250000001614969480d00c400011552840040c03080604228509484010a01000703052003a19030100320540e80d079005407181a568210304120110007820700d2004080e6481c001d80d080c5010000100b0560018003030b22080d00e041d6111881c4c00c000315902190740760120f0b40c00c5811405055403000020340309000800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 397072446 1250 397071196 397071203
    0x90f010f090e070909050c0a0e060c07033008070e0f0a03061b090f2d03051203070305060d050a0b070203040902040b04090605040501060219060b090a0f0f0b06120a020c0604 76
    0x555107040040c07200840b1401f500028603070000344140f649856010361410301103d015130310241c03a0312040d40c405c4c1c500354064100800040b80298205001c04048044502200d19041d01119440e0b0300b41e011b48403034909440000000304900328280f99400d1603609120165405008406403da0300c3d12004211104a0449404170015a528140b0030b0b611410b02c0c0701420514804036866440d000c010207481503580302ca000c22004c5001503000d00b400d10358406004582002c16600841400c9045002d550f0046a0a00201780b900f03001c21394034205081422150365029000b440e0041c1c01c2c0e2039030186000c001b0310f400c04502c802c00011030036900c0ca001078802015104021900c650600c1004030a42d41c1c5508010b0045181000411820364001803a070721280500c00c81d441d0680c81810000c0c0542440c0c012036812158050601041884951004482c42440034080042c02e01410051041e00c1c4a0b440c5103601c21002c1c40410900b001541020f80c212100702d40051411030300003086810402c048034260b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 397073696 1250 397072446 397072457
    0x2060d05040606050a060203181906020703050d0305010b03010e0a09021309051009110108090a05030a0806011d01080c130503191412161b031511090f010f090e07 71
    0x40100a000fa040070f813400303d86500d02c480c200755000303503031380606201d65034040188441ca4080c1d44420b040c01001c9a00720003003498003900e071003010303680d1131042c8000ca48034071039500718a60181c4a442068141e910400352742c0e1079039203402d84000b590720028118601c41e9681e4601440180c0d0703101c0c4034038a0460011800710b0701d0074403410031905045130f15000419850400346007c00148200d90701040061003400d0483d016194031a80510380005820002c02134440042e44101154021003000e03c1030070260b0710100e4022008405140854045c0364180c0415021008142c142500d07030060010904d401d0450380116507650000303864100700050300182c0f101c1c91401703002404010440b844121f12801e000709102e190035140051644039002c0d10066140d0700c4042d03070b07041106200b0040b45912580c001424034a4030303810288061906516521111840c0600903c040441c401c00d03a100d1210040140402e079404900545000800c0307121502000039040020580020051807240a444a503594 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 397074946 1250 397073696 397073701
    0x216030804023f010905070504090305041223010b0f1e04050c0c1203100522020a0f0e1c15110703171803090103240909060f050402090c090a0302060d05 67
    0x2420f580b408503410b6440c66074107250606002c2100044e5080c11a107040e42d00040c411254281112640100d4100000d41c14000c0e000c0340c1071080d451143c0c120030400102c01400301003d4a0032600301d07582a189907422080000801d5914544100e201031445080e442c0b00107085080f1000804079207003101c80c00d0284002140400c0404c004105103c001c11204806500e182410500c034602e1904610505103e000e00c1d10030055204d06008841d00c4040307003060b013551141034504d00a0304001c600801540000c1030008494aa031400d4401c40100301a6603c038810088410344a103c03401c420280d0300d0281070380360109040c04002c0e4000502c9a2402a07954080c00c1c0b400ca40f002800d54000743c0480507148542c070754854102400320403203204510908002440800030310070340d112217074280304181400020700340009142c1030769004442d4280c03140508012000d003210241c4100c41045c0d0700039411407c2c41c80000c0700b0350070141c0102a40c100040803614003968030760000301c60394803182c50314611a44400a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 397076196 1250 397074946 397075039
    0x50c07030f0c06080c030a020307020a0c15110102180112090525080102090a0b0703020703020a0602070303170705161103240a0516120605061b07060201021603080402 73
    0x70010300f40f0341c5020140b50170036112090703071400301412030b04445500101092000d8000c01641103081c2c0d002e600d180034150382e0700d11304454002c0c140788440400c03504440b80e41c0300d14040c4200c5101a0b001c80e061401d0710304040045900c00760010002181d40e59030300e0052b01203102000b11846c1c846010300b09000382d0031103042801a05104e980108141da0040c0034010403555030310411300a6846101d03059454082c10308040303282c0903541d400030f5040888004040790007540428500e0580740a500ca1422286038656402c04038401151403c000038418880218941c2e148181c010a080c0200d035508071020742c3c7c400207400c210241c000744480c0c406a070307081e1010f41c001500070303a801707110748004000700d1030040581c440c25000c82d0b4007030307041011966050082040030b80c088005400090451911008203206501040c0441011036050384074014001074050b105008440c030740f000303500d0548030032003a0b640e060310750b02c0001e0400c83c0d1024002d201c4000e81c1e6040001110802030080c1500906d20f030111 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 397077446 1250 397076196 397076213
    0xa02040603230312010e04060b100302031b041203080c04350a03020d0509060f0403421e0c0e15041d060f03030316180302030a060b01050c07030f 64
    0x202c51082c40c0e0020b00a403507403d4100541d031811144a2411300682d640c651800c100240b840d003079019401000280314126460b416800b85100b042c4801030200900c1100c415444180124450380d02e00754a1a100d010001e846808030310b030007007880c682080c01e081d198190703481041100800085940341c226412031140e018902d40900c021001c0d4050722a180981d1030007901c0d800c040002c00244900024942c03041d40300d480c22559441341410500d52125100e1605405a244004030010014a00c01d5000241d4910905407030020400c450001d0240c1d1187c81d2281c041d2403201a0607000d221072081d074521654085c024003d00007c90703030b246110301c80c2001c10000c1c900ca440f010a240004148000d01c0300b0442400321800d10128031707034482e0043e40c600c000104d0098038844941d17058003000c0207110301e0918040500b12454075a0311801c0c0c108402c040c0b800304031104c520000e5419031140c0c40c61408034110394403000890301c06150407450003400044407480d00c010340d0300c1200d443e00d002a031081400241c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 397078696 1250 397077446 397077503
    0x3060d08250213020307050d27030201060e010b09030601030303150e071106010b04050a12050c06040609091112040b0a150611010501090504020604032a0902040501030f050405100903020a02040603 86
    0x103d1045003107082081004041e0b00400d5468401d1994512900d052060a14201500400c108102060410091030002e000e806540308000382071a040d030003c0b454540520aa50104c080a0010002c0e41c1c03a60301c044015007070400350000b00b005c12000224010040d4117040d4818034240d21001d65106440d11411b1401c01e050b032040000400501c001e0006130f0341c07030140c5000c646118104211b16516400c100d424001c6403110360b84e00190020300001c400303800c18401006c58016000422121015010302616441640b0344a907401501000080000d200c00d015250003401103000010300c1256072401d455654615048900403501c0060840541d20007406118003404110788180401c0c01d0690100c0c0090003207000017090311241c110029003514800d5072812604001c01e107981c140c0c0c0c3d0b45a07000d6000307500901500f40024240714100402032041c1c000c6c14080e41d448001888901600340982006010740241201103003d15104207000d80d5480c0185000740d4090005000030912a01c00e1942d054000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 397079946 1250 397078696 397078729
    0x10030c0b0a1805150a090b0d0617030304080412080d0504050f1e0a03050a020f0106180c0305040f120c0503130602072408062209021c0803060d082502 66
    0x1814824005134a074221944041d080d00d1103059103400c2c1c520f8003a035140f46580c015411140303006c84c000c0034814481e01700c80110354665a021101e031182c2c00100c0d07141d11080350041c18190041004105c051900010340300668005d0003194100304006554505688003658140c9081c1e00600789000303103103c20301c240c10392a001c2031401d545032290303112400c1d1a502180d4002d001c1c8000030440d001518001c0c8a00034240c48640000c128058480c00c2c0c6040b50321449508101c66440c1c080a004103d00030b10500303001e01d42200c1c000101071b40310b550b400c0715281499084c80030011000340a400040d002c2024001c0c617040c1e20f0602000c1410100700901e00741c00383c1e000c0c80d08440701e1050807810030460001d07507040050a1030000a02d81d6640003044007070b0400601c1c401d1020705001c246082182c240d000d01d5140d807007258a4207114911441c4021003541598015000c40e404101141451805106425180c0d00c80d00240342041e00c1c59485075202d0724560801d0f00c03505401950710f000c40c6040340c8150a813481 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 397081196 1250 397079946 397079987
    0x905010f0321020c030f100f050f061203040518041e0b07050c01110a03020307090618050405040c03020909030c010b011d090619150201061202010507020910030c0b0a 73
    0x20715110301c854241c4801d141c09600c04401c00da00040d900c28085142d40940260844885480300d449843d030f00e090011103c03003441e2400d428068200351902071b19000d841110b010b84441c0e101c010420400150b111401c036005c0c44100030010f030315102c1780342d1200e40c0d12814401440360b10b03150506030390202000230810807402c0100c6c02200026442c080c0960010424909075441c3d907c5c0c01c01c03e03401400092054031030020003086070080300d81d0640007144600360507a40d404020342c0d691400d480100e100c219103000c58003078010a008a08040c2d201c1ea42c45802184000c0c0e407256242c0202c1c50b404006d41d560120382d0800900d1440c006030901801104000a10f0316401c1400c0c8007255041d00100b2742403080c07103541c401d404100d141d6200786250120811502c04900580d940e140516a0172285402d200003550906900040c064000c245240c0380f2601a1900d91402645908002440700e00401142008883d000b011020600c844d440348050300304c9040c6982d4074441d0681c041d001c1d000c411a080391502 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 397082446 1250 397081196 397081199
    0x2121203011205070e0406090203010e0706083d030b0c03070507082b1a011107170304080f0d0e120c0108071403161e0f050a0504050d0501060905010f 66
    0x2150142181e0440304114030341940c009061420364244889036000c0c604561024040c1306c10b011441c5c0c4243c01c283d10031002003244e02106409143c8801c0203108600105204d08006000110460304145a131240258484001c600c4c0301f45401070488a13409180c4e441903105410320400c03144090301904090705550f00345c118503000340020040d2140840040c103240c4041784a900c0108038080c203082d000310207981c00d54804441524a801801900c0700d812034945c0203403007a05c1650041c110308080c80340c0c52000c0d101d0681400052810000500d40500091208110010341c010013480f42c891500c48050262181d143c215100914000551804a114101401d801c0110704000940d407012030f082800c2608055541900a8626292202409080304000810170034141140031078982003101c20385808107080180140d4150360403084d040c1501245100280c3c200300d501900291002148a2500a140070380b1500498241c080050701102c9503034503410140040100c138050580900740360510380e002c0d0f9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 397083696 1250 397082446 397082473
    0x405030607050f03151314150402070206300412120c05090405040c1215050f1303030b0303130b12070201021813090501180302011b0804020f0409050f0a0212 69
    0x42c0b201070300a42c084c0515520b0b0340155142e81c03241d280302d2400c0480800c891f40303204000b8210910200c44010104010156841e118902131094510250b0060866403c100c000001b403c2c0e140e0607074401100c80c00c16005261003070b649a8050700d220780d1040d0401c40004402e140c0103410100300c201d18904031820b00719444040c950010a40780c1940c2c0454000c07800e030301daa0410001541c8a90804412054080300700414003810a5010381d070019411402c101c1d030340c1c030361076581409502924a24920010000d949001c41c0c429040490003c000a05581c9007000700300350a0501c0c00264030201c100c0d07401140c1134403604001e0303281b180e000d40d50303000a52404001d1200528030f280c5415100e8440c1c0038040a07541540e91781d0340103002465210008101001c02c1e00e006010030040070004800541c00c04440503403200c0d4144140002443c40c0d2540003580d2155803c00c0f680d210044201034100740d0b1001c2450104808200c5481d1001110f00a0546110107005211003004600d00a54145d0f0000041030b850 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 397084946 1250 397083696 397083727
    0x10605010c030c14030c0d170124020f0d0804110111060a021804090606081b0d02060903031303110f040e0316020a0909060204231e0103020d0908040503060705 70
    0x2c1c0d051401e400c0000241c603103180449801c0c12001c0c8184000301d0780241900000401c08800411919051410340c001810059461400d014603c9104007000c00c40c42d2021010345040c91040807401502d20420700d105c0d08910700024000140c0004030254244800d00092243c0701501d01000e01c3c0880c02040c1d00c0c0c04c0c0a507900400b801d0f0301900c9030300041d06150b048902c0151501550001d1091000007024181040a019240079001c840d02030709895001901c0034006260211718003410007199a1029000c024190f00130844940d0940170800000d04413000745580f0303801842c4109806006600500107002c600b1022010150259240082c0791901e200d0010075200894030001c040c84c8055407910210b40d215240b5071040000c0b07802c0c141c1950070801c0c030750041e0003900c2e500e035030344440184080710111072801c43c00c4065400200124038501350a010f0048040d5a00060401501d03001e00c0c4549482281c80081c000d4900500100b024005446c092001680018652810720b041034000d801c41b0340d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 397086196 1250 397084946 397084967
    0x503391504030f0e12010203040303050709080706030207030c1e0309090b030303150d05060711010c030b060304060c030209150405090901020a0212070507150c1103061905090c03030406170901060501 87
    0x9002840f0711110009104035082002182d01074001141c1111041455020b500241c40c110046820720b00080d1015108901300b100300c42c03e400003041401d00c1c103481500294041502034040150100008000c21030b0a4410441700e00c3c04840c952a01d0510300f00104100c026030441c910035030a0404440b050359001094a812040703401d400e02c400c020400029072004c0141000030101e010b45810000010781040e03202c0e40c10380141d070080c829001d6011084003101c4101b241e150384200f0500c041004118990700caa05061f40d03d08005203410211400180002000c0d120403003554000541800241410f88145e50801d20440003035080c007564400294987c6c9495000b244001c80100385181407060801c0321400802c0c001803500e103501c2081c00002d10b44007188100f81c85840340c1c80301020f0302f424002900d52040310310402c1c0c50150300b640d2400d0400f40c60090003049083c4114088641a507034280001e00003424a07464145050888009030324103840010a44a100e0740341c008108040d98000b142150f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 397087446 1250 397086196 397086203
    0x504020a05180a050405041412030f0408031009020f1e03010f03020d1a010906060f09140105070303140112150506090403050304080d050115170903070602070503391504 74
    0x10b914600b69408104058a00da02156002d0309000900050121000c3d414100c0c01081d42582c11080b600554a9024881071720341080c40f21000c000500821200c034042c6070401e80402400c2c1c00543c0e10310050043c0e030046103616030b195030002200c8500f4154480d19102200c40601340d0b40c150343c03500510642ea10304601c13010340540300303405d2240e041142c07141c0c0d141d114103a0301001482c1561100700b080c0042001d801035102040b440c00c15074900c54060040701d8103c40d4116505800200c1340c0004413034580000604400385500c0d0b161001c2c10310264005e06001c0d21083c02400c200584a0502d581c103248103030410a42c0618010038030061b508c42054859000c1d4050500760fa0340d4840d40707045001c070700c91101a440c19a00e04030011604072a400442041040999030b1a14100c840c42c0d00701c071410900341c50701207456008101020005d44a038000e086114014019281840070180b43c41c044010f00b40b131980510038481c00900e96001e0079900c01000f40708400c00078a06210001c121410490002c0c0018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 397088696 1250 397087446 397087477
    0x32304020d030e130e010f0b03031207030e0f0a050102031605040303090902032d0115020c0f0f03030f28030209010c170c070b0c0c010c0b0103030c030909020a020307020301060504020a05 82
    0x43c0c800343c8401201d129002a0000200540d20815502c0f0340284040305003800c100d400d1224994040ca0004182c40000300704d4011560780e0744130b4400690081000040000c1380380540c4c1000380c4941011b1165044240c00f0740005641c0e4038080d9190004410080d20303900c00d02c4011300c002d0000c203900514080613944124001a40c0c0e423180103078042e107102051358200c000102e12080c1e0320b10000c10b0f06e1582c100c5138206102c0708040002c1c1d4069171a00b030508001d9822042501c940515440c0032215140a400c018065038030300a00c218150b000d44c0d006142d00030104a46007618002c03a5172403600080c114145d45070450500c54485c000900d02c20525030050700f40c054800803880c41a2545086501c2c589080044461103980d60030044901e030400451080b00340110b4680121390350041c00042d20300d0350321080c0e2858a81c01d656066504d1005120b0550812401400229400b002d6100420145110390000c1d6101c0030584101425980b40e80c01c800d000e58014041c40c0390568101003a5005000d008101 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 397089946 1250 397088696 397088717
    0x70903050601090f090c15020d1d0d020d0203030c0f06100b1603031119090b0406080c0307051201030b01090515010e060a17040b06090708010302010c0201080a0b030d032304020d03 79
    0xc2d140034050720000034080702d040140c0040d4400b800d000f0051740d0304041d020b070b480341c006c00f00d415515500d03034030a20555662680c843d51218501002f202000b5840180220b074000c0c001d8004c40e28540218906502980c40744c0e50810000d0b00410000b6408520314060640541c100030981d1030b54000c240e0940c0000010540c00000c04d4000d03004840364451901d41c09171540c0030940d0354a20720046e10403110104402c1540407982080e05e1045a0a0b2140c0c6d86545040da100c520f004100c3c0d51000f8540310400c0000d0048100c010039074541540298007810fa01816541131120020442e100a00078280e0120700320000e20450360805850105050216103d075280c0401044c1079442026211220765031b20383c0d40e01008100000807581c58081d400070748203411143d5030780d8400d4034424000c1c00040c2c00700c0d8440601c40015031140c04125401620740b60003089104400c00401d10300303c4500c420310042a00d40b6810360030f98814400c8204041060540c041c0d2500b840e4012841c0240b90385000350802022802 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 397091196 1250 397089946 397089971
    0x304060c030e091f060512010e040f060f0f1b0e120f1e07050114030112020a0806071d240d060f1401030c030504020906040b150d090b07090305060109 66
    0x102c1110b2950042d0400505282c000343c0b002d810b0307484000303458181d2035030030001c95240e00c20416500d00380b03921041d11001d039081048070801040010400c0303881e0a00b038044d9000103140c0e4060b41101e2080798101140c2c06040d00c240c0c20030303101c035501241c07400d45100010313020141d4050000355403003100347ca210a80c00b901d849424189210820950030607c6500d10003c6003455001141e801c50016000341ea818a484900440721003070750744403681020f4000d1005014601d0309072a5420003500c0105105190340ea01c003442801d05004680700c002248000200c041c0c041a10060450031181c1122600c008844500399003202c0c404840c500030403c2000304c0c060704602c0e00e41e0300090160a02d14080c00d5501e64070004240100300d50a1040c0c00a8102081504054080c2c011a4000e65000304010010b40e1307000c06110041401ca5066640a100700d00c1c4102070700a0203004105140303080c6400b0850401c541820104503a01811610810000300d008202140c00400c50034103451b02c4100106650600f0351 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 397092446 1250 397091196 397091207
    0xf1e0807020c120c03120430060905060406060905060612130219060306090515060918100e1005180411060f0301030302010e161e0902030a0504140f0304060c03 70
    0x444150020038400f59049000c000080745441040b003201101e5580346084c084a405010b24418024290070742d6000103085076103120348101c0c01034610f405503200d1a03d512030a0030341e50518002d540c02e400c241c0500081c0032090055401500e44000284814100b0300f0105041e48240201c241d01d40c02802c1c0825044600c87c040c40c00c0d5980c0007454884140e4040e903020f100182d00348121000300740344c15070010786d80216020b0715104001c0c3c029104108020582071181540c8114003513940004c600c218001c540c58142c010b40d016860a00c40d20a081d0f060503000c0210b800f026101e903076001d900000802050b07403032110140c01101b100c0409141501c031131808170740e00b200010b031043d80020302045007940c2e500d448010714102e900980c000d0041e0b070408201c9546031111440148090210340a05200758180d030240c8904190358400028010b40d6038882d400101d8109480318042c0b10b45810074841482002082c511191080c00090810200000c0485607244101c1c4a08030512000c000d51209060082 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 397093696 1250 397092446 397092463
    0xf06090111060115110706021c0201021b01060609050402030112030e0a030f050307021c050d11070e0907090b01020313030b04060618050a050c090d06051302030d03020a0f1e080702 79
    0x344111060b55071160350944003903880311024000101901015040da40b400103000c021106030f60054240310024110780740e074242d80101e0100c150f45d02040903481c070690702c440103111035290740f000241003414904010300c44100c66001901c190300510050203440d600000c1c504206501d420911459004c0c04082600e0700069032010b0142c9803512170110a004c0c010000303242d0644210b54541c00d80000100507001050030400151140d4070a588030078015000701000c0b041080d00d07800b2904441c0c0c2d90400038800d203000700e485100395000310800700520006030051440000c824000346081c00303003c40089600d4401844041d280c0e1014001013001d0164940c0302c4005400c2d114409002d0402c030b10000409400e0550b0b980c0701e0285401c0004c0d111106420545951010040414850f0300c0103844840240030041d0100245802440240005039420418945100407945000d600c1d0382c89150007510100140b0152400d00034008901e0000804a50780040c0010040c00c0c459941d480b2060202d1405141c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 397094946 1250 397093696 397093727
    0x90302121b07082508150907080f0f0615011b1b03060506100f0c1118130506060f061603031104080307110d02091b1303141b0f060901 59
    0x580c040811010000f040e0040005030000000d51009030010010003070701c1140c440d828003030300040c0941200710b46d151141d5404ca1400c0c000c8076400794450019a081c1110420348801c950300260740c06280f10018049158404c4008a1090350310310070303c00103401c0145480c20508800e9984170504104011008038040b172155002c180e80c08030740c49141200040c20241e454901c240c02d141d01343c2d101d1300d20030051003a09020f155258092030203a03980315003503103135510709142c0d0110355000880ca03070b0350415407410b119401485030310f8480401c0303042c05420801c024182d18010902e81100103105d03215401140d03002145031950711003c0500e414210000d1400e0a030805058000180009980300300001821405000740d6840d074404032518100500c0d034100e088025084580e41c03000a81c1c2041c0040c002d1052101691503500e82804103070580480300c02c0790021990816090420086200104040c1039103c13042c1c500501d80440e6a0005580c9190007452244240700c00922640307241d1240c102c80300104078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 397096196 1250 397094946 397094953
    0xf060603050613031803050709020c030d0e031201080a02010c0212030c0601060f0311070c030605091e0610050306071d01121401051008041101050f091e1003090302121b 74
    0x100103020030290002d43c50f050b4001192030445000f00750f500e03001c542c00c80b9803010007002124078000c0680c0c040e410614403030129000a104040d0602414040c0124541101000e140e440c02c060052121480041e00011340781d50141d141240103076081061100d219404942c842c038440800c3d4022469442450092000c900072080006590b079000000c3c445c0801654070b051042c0f0083c00b800f61800d00400c480500214815801000400e150768041d030303003242d0703d4010b440f2016018410740c3c8e207280340d0b914018856808801006070024082114401a200c110054501070030140801003034402c1005685210701100c0114841e030360300800078402d501ca020301c01072160010700036039980316030024403500780034607011944840054800c0714454850b9511002040505240200440d156006600581c2c45a6000c0102c0030440d030302c52036801005981d61107460604037083c0107200c84050030314000401d050a02940300300098001c24184400003450780499200d401e1390510b0824060b9800150a8a00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 397097446 1250 397096196 397096201
    0xc0906070807021f030f11090f0f06071b050406140f03160602010906050a1e050601260a200403020f03030d0204030305040f0b1603030902010c021914040b0a030f0606030506 76
    0x80e00400d0760003064041e1400c020042c0c5c15180380050704c0c003000c03080846130700030407040c02142740c140510b500d0340001400d03038200c0300c2c00000460b80c154080c5c4425035111201742c0b050200004054294000342209a030240f05a5203410a141e60302c4007103404240c42524000311800d0ba54800300710348000082d810810500e802d40c0c0750786c00f0b03000309038024058540e103003014002810701625014840e54002c1c2c601c8d070440c1e041c210711a00c600501c00a0b03d190304010300d005051989101d00c1d0414181c1848560060b5110304005d0207110840381222040f081c0c41020230528030788944400c0c1070750200ca0301614441000d029050000782148200044044424808035021060681c0000600180c84600c2d044011458491160045070300410848141c01101c0420080000348640c000711101071041c10010b0604210703500040d151210280136803011036480e01c00b00031000400d841c5902c0c03100b080c1c03400c002a0304858045000a003080c00f0203001500800071072420402c01c1e0348114001c41d017083c1030310300700d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 397098696 1250 397097446 397097479
    0x7060f0f090302072301050a05040e24040b09130503040b0307180e090303010620120901030c05030103170a020a050a03020a020f0102240a0609141e0c090607080702 72
    0x80071258420307401403003410380c08501000440c16900708901100000d2000c0b10f94440111601d501c55140c1d00c0400005000002d0044800400b40c2d000d03d0802d0803560780030170700503400250542c01c22141c510450a100101350140c5520301c446400002104c0032010b4440e040c10800d01e18410740d400310301c00e04800000c01039900d078401e0039591401031407090082044e40d900703200c0032410815101c2ca10207070010001084000e0081c4220b101e1140641042c3c00c118541000701801d02d03101e001000401e44000454000540e410701c40c442c20140a424928255419611074045205401116070b946810004072004200d0003004000c0c0c40a030b0043c100c449000a620f802519004140d00c100d0094411400c1500d80c0d40c004220a0741a26203055026040c41030391901c0180000b01074501000b055840030085100041400340ca0721081044980d000c0900b13145012805a05a00c0b142c0c4100d00800403c0c0525603149800315010401b08485603034982041d8146160300340301e0150300950180d80341d40800d808 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 397099946 1250 397098696 397098701
    0x50c0a0c050f2403060103090206031303020c1c08030402010203040b21060904031209080d090506091b0d060507180e041203050702070b07080d0e2505100507060f0f 72
    0x54607016544800b40e42008402d002032940a107100c0110380c00d1194106040c40c4611028652020b414540032071200056004075060758000e69041c1400918070050a080c59010040c800000300292f41e44410303107810748140030100c0180d000c01070410700d00202040c2560310810907117020307042c0b8a45950760b40d8040d419104494002e00742070090010b40200007040c5c2d00d89144028032480e01500c0e03c4248900f4035100c6402404104c070f04407080c010910422080f03007801d2040011441c4034000400755410a0418030703140100a004540b100c07a0030741c54101c65521480c0c54406017070b034040c00103e8161112142680e144984a8804600454000740000c0c808420f15100c2d000702e00556607840d54515041085054500449602340540e02015081000c5aa000000d000d07417030042c00e1301c90074158045180f200b9507484070f030014940c0d071000c1001c40118045c0000e8074860404e01c54030320a01131034140440c0800410103c1c41d002e0000225000091084503000440503482c012420012659910f021400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 397101196 1250 397099946 397099949
    0x7140304230a11060304020105040e13050d09050108060f01021203150d080a030b0a0e011202030f030307030e0d05042114010e060a271e0609030903170a09090b01050c0a0c 75
    0x1103000c4495007000c0d02d41002130440703001e01d40603507625241908082c801600081c001d0300e808503201d0031421220216200b070065480c0040e15a03540b000c601e1420703000514012014102510808001401140700d07a000100c41006403200060582c0742d6440e602c001c3c005248422031207401601900420007006171180091410b504907440400091464406000210807903001c0e0f401d01403507400040c88140040c01c2448401c1e0b1000b0101c5140d000d400184030305603002601c1d0f070310119844401000c10380c0400c0c081208030803414074151342480e203420500d944001e4a104e01803001c10b0114010414014018000020324080c400203110901035001140d03520389040f03410140982c80d0030070310140b180040012001c030034840a1300301d5200065840b031003201503180b603440403407540c1244400d0004000d030150000310f50107622444034051850400781c0303541c04c0b65030414180c0f03181081203030102078000c02503409441500000117020f030b0180c2d0041c0c81c58820712036180c081d4482c980604080020036180c800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 397102446 1250 397101196 397101203
    0x100c050a0c1802030403090b0903030403060906141e0412050708030907051011100f02070c08100b0d0f240f06051002010605010503190b0607050c0109080607140304230a 74
    0x714000000b404600490005841c0200002c410210070062108480040e118205009040d64030b401d96131783d83d1030200e44210200715441a100d0107855402c0b1201100c903584500084256072910081c0d1404d2102004010720003882302c4000030030210241e200f00195112503034400304265890030102e030460741d078400c60b110b200d1003400c211030010301c1548a86464030141d40f80200a04e20b01e901050000007030150803140d51a5907600b4480038010650b00c2034003d0041c190240501481144a10001c00b61501512049e00600388400340d80000381d05041ca6000c910b07007104000103078105c5202c41740002604910904803107070400740d440c08148040d0b40702100705c5000701d5032000305e040090026420f071566480390a0100b10188001a40c001d0a00c030000c1c4d00e50b004503000540f20401030001940780d0040101038401d940051500c4140f56003203441c40015084082c001c024a1400c600c00800e41c0520000c213003071688000c004201040300d000005100130041c1d40c8412500e066070703901c0d0340d611141d400702907 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 397103696 1250 397102446 397102469
    0x2070b250f120e030903070324050f0c090f06040f0f05150a1419030b1c0b01060507060f05040803040201021209011e050c100f0605040515100c050a0c 66
    0x200890042225400d200102d84698500c030100d55654001441918a038640c2c5000c1000662000e960074004040a10311075101c0700300f002218040840450504900d000c90640b800c000d01c009841c50710202035001d01102c141598950404000c207000c00c1c03803080307060380014001c076011413229040e0b5030510a403004141c1d07401d42666208200b00c85500503800042508004020580285200d0009144070b080c2d0060054542012660741f552402c0a000b10400040e58071108990240341c80c004075000b00841c40c07410a12100e00d61184000440103101d070000f800700000c2c1c0c80d400c21205800554000390104420456843c00e03080065040d40700b15002c90040c0651301c2c109030904051000d80e0b400d0740040c1c0d01c0400351505000c1202410b1418a503d10034890180003854113000c04210914003102d40e42008549809888003001c1500d0703031a00442e100b2403d08c001c02030b46a54883c8000551441120f0181c0701c03d1001900f901c1c51000c108000c0e025010b480c198030b0500c0001000d60301101d0705681072 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 397104946 1250 397103696 397103761
    0xa0b04060315180c09111b210903060c0a1202040311030c0a1202010f110610030314070b0a0207080f030c0a0906170402091b2b0203010e04080d02070b 66
    0x100d0142040d02c40f0003801c40380414070a0000d12103ea01541000311690f04891038110184035008191003201c0001d0758941c00054880e054040301c48c517840401d0b0141c040305041103540f000281c3c4a1100900b629a0603c02240220005100380da01c115007910000c02150b8640c0c8034105240c0e032060000686000b4403030300f0132424060400c01d4209045801444012001170020b900442e41036105001e80d030708002a10303003104c907004801e005d058040c003041c501c804443c0e455071802402c4415080c08504201d48240080310200d00d214400d95031010b180ea41c01a907038101d42c81c0c080418000c0f0000000545408010881003c2d4030030b000709440e041c9611030054a80e40e856044034900381c00c412030751411045102250060810886072900100080c04601d059050032082344020b40007105024019800c04a440c4800e00c0c482004d280e00c08166981540303503605100074100047c0002d00001c201000c001503e1201603843c0d41a640155441503ca40761401e011a55242a25024001d244082c102103039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 397106196 1250 397104946 397104971
    0x9210606010c0c03060c0c0b0f06090c0f040e0a02160305070b06060f0a1110050915090c030a031103070b04080c0d080f07050a0e090a0e06100f030b0a0b04060315 71
    0xb110309103a44000090700705402c40da111005000c00f091030790240900100410002000c03002c04034070039454a00c044405240580402403894405405045c100c40c3c10844001c1060300c000440b02601c802c41010582034507002000700c024424510780004114106012404160b804401400c0d800d0148810f800c0c240c48040c108010352140340314000c002c000802c403607a01503004204000c0414111015200380e180c9880d042429220100c2e00904039403c03e03425030301c90614845401f6000f1281100404954140002280d070342c1000c44000340600401d10001e1000402c00c0040f01c06496115030624840d080924100e00e0316000441c2000c81c0b1f015607500310400f44d20400d00f80b4490b8030030340520794079a00e8400050781ca0b60f1100f010a010884004a500083d498005040340107040000b40003504034480d902a500b84040039214041007111414100409a4075005031415242c000500b4045501d40900030801480b07401c0c3d40c0b0350002c0c1440700c00014880b022103800c00c860300c100418400703c1d0a40d00c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 397107446 1250 397106196 397106207
    0x41a0a0b0307061409040c0207060f051303030507081b060403030e0c03061f0f121407080309090a0f1a0f01020703031d0d05100225020d03030b03030921060601 70
    0x81154040e446824100040d503c6811007090780d41541c5030040c5442c24210220f400c0e18003a031f1245002d0b0f808200100901a40406019903804041c50180d04100748401404c443c4042448064108180800d02c4024441641c003110b1030780c4604030f000c1c554400e400c2401c5803200c400b110b0580c0030030b00d801c008640403c4082000b9004045c0200508620703a01c4425210501c0000c0791700071920403090b1000f00301103c2e42580003002c0d00984200d819030310710901d44200e080c8000c03e0215080c2d00070301e01c200060f4400105503001c0b04411200b040d420356130003000d000104000c0000c00f19050400000522a0480740703110000340c0c03001e480f0b4000307441601005980d1146903200050001392005442d03d0814012901580071140c0280409003001a980741e5610385542c4110807908540e002a206c014800821403440c5510100c0b1140240342070135800050005e81c2c080d1000d030505858281c64100d5685c00d001705d80c008180207010410301811441c400744c1c41400588020040d05c6010007145980d07016a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 397108696 1250 397107446 397107461
    0x20f0f0904050d0f0809060f0403020123060f10080a020a0e0d1b06050906040513020d02070b0f070206040308061e1f0e0a03020a061d04050a05040b06010f050301060e06070b041a0a 79
    0x300028031f00f603211149400d5032860010000e0701195a00d1380c01c1d00050303200950004002849111050302d9007441e1042190400044508078844c15010f00c50560484d08188015030014080d40d005882e0394260109076001c840b403080c4130307510071122155841045410700c1c090022144901c882100a0380b2908195180d00c04c6c00c990940c0f100d800e01c410003507450120800000540d2802001d8101801c0104103003d03038002400450781e11307030090100100c07214511992075118403e88001c0c009800c080c2c4010304002c1d130203081c2038020403150100101c82d40c0007600801805201910040b203c7c001d101c2440d0a00e81199401800140c00c28081d060034a02440d4010603242c0046c003031000c0601d840001c0c0c45800641d8801c0c540c142a000303000c1540d94503032041902c9040c9802c404a00c5103014900311101900050140d1305011300110207000496008060364150f4601d820301c603066032610800502d25000d207000080418004108000c1041106401b02501001500e00f041807603c1e83c1002109a9110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 397109946 1250 397108696 397108711
    0xf06060309030806030c1c03021e0307020312040f170f10020c011406060906031e0903090405070309030e120111160210081e06040b03010c03140a11030103020f0f0904050d0f08 77
    0x2074101c400028001138281f0185601c640100c1f031008081d01c1d5050b0102c0d2044500450581021881009504061007001e0208550700351042c41e00b41402c903104a003054078040c1c40c880044503403000c5040041000101e504c080340328110368070f89c84502c0020002e035100d4202c1070115400c2c4241881d28850b203803d003a000d140c0080120381401e031040c00740910340e000101a030000402202d00d0900005165075480e01600e100d0016654820451007400141d82c00940301c40101443c04d86a6008282d000704a20718490381119001243c1841c80c9041c0e014214000c03201c0112900014000e6000c0380030105841a06e20940d640580361000c2c5038203407810181143d070318220360744034080158201c807140d0b41c540e070101004000282c090302030004070b402c54240914660210b03990300300014101410000035513102c040d02031305101480300f0036400d10150106202c028080d29071142080020f50340c0c85502d50070248003038405a43c0c1c0c80c1038100550f691945090650200f41c40a8500034094400d910145c0304014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 397111196 1250 397109946 397109959
    0x211707050604020d030e0d0305040504060f050d021908120702041a010818012d050a1503030311040e0f0f0609040c1412100e0f030a081303030f06060309030806030c 72
    0x5443d0280501e90240020440c10800241903140c050340e224901124110300950354151160b041600380400c4540b250080c04101200382010407460b52590841240c65a06540d5041c080c80c01d00c03210600400e140d044404140604410382c21009441406071401e64001c9809100c07503040080444895a0715240150024130310a0010314100580046105482c400c0400001d078076101542c2004029481a40f2000c2d6407150090036814107030500481da04040224170400c100300b4020358140502d06140300040c14551985404656034550341c080e50001d0103041b031410403620307000e12045642c8608481466076003013083d0114600d810070456581c4650f0b8000304032a0340d80e05040010005041003851540d0200107005401c00700e240510481e625030341c100d440410b04403023424203542421454403c000c05a84148040c504040d8040c00081d04104040c40d4004400c3c0b081c00d08801030044000d40f660441e007070031000a1580d9059000c0307000359000344e4854407203468074000c060b15045402580c030760040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 397112446 1250 397111196 397111201
    0xc090c0301170c061917060f010f2c0307060c0206030a0504140a080c0f0c13020309030c0d05030115111e0a02090405010b0a0b030f1f2117070506 64
    0xc5803038001c0301c0b0018003a0441c1c8070381c41220005805a8041c15240480d00151007040301a10740210507030740c1480550400c1d0007103281c1a404104502e141c1c510203070421200241905401b8000c070b403194215940c5400e044070a0f195010514000d000d80b040007400b81c4104100019001d108520520345a0784c001c20a5207161a4a440c60300903100181c8161607100300d85900140042d0108024030b1018071884529840f804c4008030107003407074030064840d001c54100004084280c1c0d42c019421090081c040c0006840340c9442d00c04074594014599010002d00c1401a031140c42604280618100d46591000c1c1503400b011690440d0300001144811403243e00240002c4520041c0c02c130403801c00346a9070304991071180160002000d510003554166801c0e5980c0f1105030650401e0701c8003401409103854207500e181000b0340c01c6a80c4840040484c802c05c01011640206d003004904514010850b4899102d040c01c281d2820f0311781101481000c171400314404002d5560401c1d10800d60701c44a403c44060000343d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 397113696 1250 397112446 397112459
    0xb060901061b08210a09020a080703150903021f02040f06110c0d110d080304051b06040603051e0106030b01030b1504090216230c0d0b041b030605070c050c090c0301 72
    0x1d40003c1844448011460300300100c0d132007200c02071031250805200103d540015401800000801d5070880c010326008000c0c18808149000002055191400e00006201d862410304030b01f07040141c064510104041201d20088a9180c0c000e0426101600a0014010b90b00c1100780d5900500008414580e04200980d030140d161610103550054080c5000604241e0700c40c001500961a000d021a84800c000c401d0206000c010131143c454080b0342010b04240c3d000c450006609401203102d058101500c8000240c6003640c1d10b91031078400c00110501500550315407030050082d0210400180c0060300c0d00032070030030300d2410943d40320804050901d11480c040c142003103200650302075502c2c10b64400340903074003034000350071510304506036002d510010b0743c00c204009403981403801000b0141d20810440604001154140324a83d800035070121b56040e040c1821101d400c000c0c01d0036840504440d00e010108a1040d40141d10461003610030401c1d514012801c004100f0b09502c1030320141800c2c0018001403128 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 397114946 1250 397113696 397113713
    0x807052b080f0a092307080615010915030204081e060708040c09020f0403020a0f0f0e0606120a0902090a0b0f03030c100504020118030303060e010b090102100f15030b060901061b 78
    0x8043c01201d00e20001c1904034801c00c078001040d445c0405c42d40c4200d000700072180c002e0050641000c1002c62105148803514002070004c4243d000301380b80d489641c076020750700c0340c083d50440b40203003118001e44200b007001c040d00d0b1851508240080100d07006450004801d81e02c90441c203440b03130307034418402e458590812590b00b000790020786000707000781070802010015a0380c40c10960000c02c03010001030080e034100200c420403d40d0381e40c0305144400c3c41105010482e074404040d13420560460307542601940d95060504041d00c51064040c0d04803514134103008520903a900546e5807214192a80e09036155032100341680c91040e40c8010b2010f4201c0201c200220030240c005a0b082801450140c1505202454140c00500c2d07a5100710b0110340c0d070b40c200700071040742000d84c0b50041103032400140c1040d00d020f0002c1c0d268990040c1c5410040ea80f40c1f150041411103078015141c030342c4504441441c2079213130301d40040b500000f07895440c03240b26140e0000803468880d0495411003030582809042c560360a41d1032048 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 397116196 1250 397114946 397114961
    0x60c050a1103070f1815060903060b010905041a040507110715020c090a0b030c0a080a17130602030d0f0933050f06150a05160807052b080f0a 62
    0x7454010208001004c02e02d0b06615000313868403469210b01302c40c0924002c0d084503034001841c05020008841046105c0d0840b03c18411203401c2070001c500e02102c40012900301d4000d800123a030081c07800890044d1800190a0340403d8401580c0411054496000a4680841e40d0340d21140c0d90380b0060003440454044e1510300b43c0f150480c01150107488030000000c44901045412403c03d0f80d071030072524030360f240070080c518040d1070a071003660303a035420883c02d6a04c60700d100741c1c003800c0c074020401d0004080240000b2511186007008181311060b8441c00001d4881e4020200034040b02e051049040c0032035010710946241c1c690008081c800014100d90b129021040034411503004c00d400c441904103000c49024480c0300b14214688402c0c5c038038165042010045000200075541030342400003088c1c032504074007250f040c000c00000307841980b5907520300030410b1701c1614401045406414805424004200d00c02d160400038400310203440400b8141c1201d074603500711441c0c0f1100e054980441c190f509913902180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 397117446 1250 397116196 397116199
    0x50607080d020d020a170c04030c060e01021e03070c0e100608090102070c06080402010206180c060c0a02030109030327020307120f0f150606030b03060412020708010c0513060c050a11 80
    0x141000003d00c640d03022a0003800c0305002046000d99074083e0381e41e40080159210b0110b6075017a05190545e145c0d1201010f150050400b0307c0807007007409025030300030040c0c903c00114406206442e80c1010100c01d4503900440021524103440d0040842d40015024060b4864107044103504d400528040b401c844003000544414543c3d5400c02402e404616060751100c040c003580d032590251401c10317200080c9056402041c003c0341e070700340310b400c40c961031408900040c1351102200c1143c1c84100d25034107981400040d00009525610f042c005908258268000d001840c5040c0518107084a5007050708400d442c12510007541078002900611030145170741016429980a1519030b115031200c1e0ba5201d0304422000d405541340046800c10340603800140c020800a072038585401d10501c0f8000c0c0110359502d2010744000e2810054001036101c0600c208100d400410348a40240491110301c1c0014019500c800c02c1c1e100802c1d0440300c00b280f01405005007240c560b500100501c8100b03010784404018040b81d15526 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 397118696 1250 397117446 397117451
    0x3271b0105041a031918030806030c130e2b09050303071109101e0509090c090105090406090c06030b0a05100807030e01110403240b0d06020a03110a0c03031401050607080d 75
    0xc5c070070b41040e44259220208124500700c21580b5505010345103500c0101f00b0b9102c0e52003006800c025451301d042540d100d91030044081044191080681c0c00c00e000340d81404491000500d80a00c00124000e0034200c01c4415280c41e00390742d494600f4561240715003000076080311201c081c0389125090041c02c0300c0c1c7c4042d100080400d0725841e10103804030a0007070170804480c050204410712403031809050407a000000900108462108000801c0c14800c0503c0362510075800e060028007404500c1c1c2124050700da01c5100e0700111912054044d00030040c08907900d018400c0404041100c0c10400c412003984003503a107c03080103a580000c00c901601511507400015529400c1148600d640c1b2005403000d0f51040c80400418000020b1403c019500301c44440203242c00c0228914942d100c21601810481d00010090b82c0d0391701400342600980350b521420b41a07004001070b0881c1940e0700003551480070344031395014050312055001c01c1c80d0f9810203028541d031018040003803000158061000b0040b940c24003101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 397119946 1250 397118696 397118731
    0xe01150903060c0f080601030b1e04020c01090f0b010b070c1707051e040e0615010507140d0809251401030b1903021203071703271b0105041a03 63
    0x500c401d440c0562609070119804c0016001c1803600041461b038030990a00e0200118070b050000a480c01121000c021800741400300c1c1e085c030300d07211a01140c45001c071000089c8000745480c500780486940b043c809491710002900040ba405492034100d907601034205404202c2541000e040a09c481c141d2110500c031072007490340000740750311420321888040760180d001582c26203a231001c0c00181d45807551550b4031500403d0410460b052070100e101d51058085c600b90f80c480d5424034105904102900522030079205142d45034201c2544a00741600c01d6030f00d44251958143d9030301c210000000c04200f460600c4404400500c007104d41146550b030240014900401d9808019000c03806d04044c1c0e400d0101c40c0414104c0c20300642c10300340c20750342c0410a0180110300c0d0240c2520340407200031000f108040340c4440040410360740344c0600d034a49003105000d8100c12101c911b091200d9960243e40340c1c1000762403010100007260358007840a030f40c1101c44101a08140c0c40c003e96800b05580c0c40101072101c003400100c038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 397121196 1250 397119946 397119953
    0x9010f0203071506090e0307050703060213120b0a0e1506090714130f120f02060d062607080f0c04020a1e0306080c220f02040b161202070e01150903 65
    0x1070481d143e000070000040c003941011800c00c15910210951041903200300318002c00205c000444504594107d0b10040c0c6401d01c40825010002017540580314441c5920703000c005210031081c0c2e0301d003c0c1819420411080070b041c80125258422012145400500000003030b4090030009100c6520122624110160810800c07806103d90001641200a00c11240d0103110b90102800701c1d0016001c0008a00d03030455003603588040d4950b841a0081c00303504086101540710041340c201001801040000500100c5003010039280f042400300c04030921700c5074180025400c440421401c481d0703001d400c041c00700c043e540700512019500074881e0b0b20800140d008040c0305551803510700741520899940110398145440d9000380303000701840d4540d10070011120354a10070004a1020010345032118404540d4549030800031009024540c031003006038a000800707031520510203540c95401d902ca04820080920b084408a139268200d014410005a1100050180c208001c490070000c51852608041c099101d94 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 397122302 1106 397121196 397121213
    0x903190b0112081c020d0603081201150203070f02180108031e0a05071407180b19030209040206130b0f041d061018050a0e010611030f09010f020307 65
    0x20b8104400703071340d4066030740f030144981040042d65507904040f2944e500c44c009916500c00008008200480c440c0305003420310b0465401541800c10f10341d645048041d42802c207036840050f1150b2008020700d4102000d02034191880034686525030074070001c0148080540d0311410402c02d000c000c00726903200c42500c0c90290001c030815841c8000c4e6a003d4104a22034200e902c50306551405001e0040e01c5821108030107000751200d03814420427030160308000d0703084e01001703510450245c0440e025143c0341c80901004418954040c1400b50f5400d500b03600c0754401040350550b00300100d8101b142c04080c00320601000d944c0060741c030310740c83d224000402860800030340b642408140703504047e180001e4103500000e4070740503081d40b054941310780c10001c03c0c505c244a60b0b40000d503880e4408512100c0803058440d142499032025040c040401300543e400980c10782407600714401070004601048080 = true := by decide +kernel

theorem cover : BRFrame.Cov 396942446 397122302 := by
  have h0 := BRFrame.cov_init 396942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 396942446 ≤ n) (h2 : n < 397122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
