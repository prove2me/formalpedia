-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1499
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:16:20.740983+00:00
-- url     : https://prove2.me/submissions/b64d7280-192a-4587-a7f7-0b9d2a378ebc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 269424460 ≤ n < 269604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 269425710 1250 269424460 269424497
    0xc01080703021e07050c0f03101802040f0e1c05040b0d061509030b090a030e0603132111060402030d080903160b090f0c0f060a020106170304030213050601 68
    0x10380c80100c616005003002a80d400f4030880e00c0b00c40410507a4004001061024030406005220840704244c4102408281410100303546110300d0400070500396030b0313842c229142008044900b07030154009005003e40700c10741d02c03060010103001c500407031144a09484800604065099044601c04a494041c02d103464a120031000e0340c40390399085002070b40d840011a00d850303001c2c184c961a41903640d580d14154214a00186404000707441c0c2403041d40529115030009034481403010059600303440541c1c0300d4407032805014984400141c000c281c002503896107003442c81155503d40070fa0f030741d5a4503000c2419009e555162183c0081e50040d4068000301c010107880c0e4003405000e41c010300c20074122460300201c94603000c00c0c000310010403100d14000c2424484081020400800c442c12068060802c00c940240003030b0700c0b50180e0f0b942ea0300030b5402080c490703030345e40c000c1d0b10940040032448802030b00c42c040d01d0219500c0342e00c01d0004900c02c1c4181c48240150080b903214491080d0384c103840f2036819620303100461 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 269426960 1250 269425710 269425727
    0x108150a050310020403022809020a02160e090c0d0804090c110d0503180c0901050103110d05010f03056001050a05030c091602070e0103030f02010b0604080c01 70
    0x240d0300004003803400a15074904100503035440703800341001a00d460461040024036964040742130441c015a114001c03200180c2500340b4211a5822030040e41d4496604003682844a001c0800d03494084000d00040c90052507611140318150b040244c6d01c01003424000c000300c0030007049002d00030a80500c4144401c9003546d1040f541c0911a0802d4100c40d8219481a40380c02c119017100400101c021040c07220031401c9001403080e00c0040c10240a2a60400000c200c0c49541481002d04064485410204450300344040b144004410942800950307107441009010b050740c0e11040b500d900c54944c4180d1401304032045401d1000258a0000040e26010308080f0f010402c400741c1d5950f2a0803d04640004510304010030701c2006d1041d8010320b6615090411420b10415400140250003085c88507010303680310014150f02ca0304121185000c5074401e07104a00d00307c81500f1010442d00d10704000303c24140c101035841d2244840307038001e02c8540440c7c428040540918450110b040e442002c050340c0c90f601a0f000c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 269428210 1250 269426960 269427001
    0x1d0609061f050907092d09140f0709080307051c03060305071a0d05160f0905011403040f020a0605180a050a09020711040f0e010e010c08060607141e0610050108 70
    0x11104c89621b403043c11820385e10309040d4000d82810071500c000c10b6850084003800030030281c60104084014013150704103810000b03003400d0b2222071a500198001d4094940381001c0c104840869444424524141d81c0d07490340d180381c950701d00310211511071459100340284000d8a910502400419240c4480c0011002c2811140303140c030f000c07c1c400a800d4503414403400e031190001028a2a8220200d44003610001107a210f201c208000c0310320030300250344c200214503c00d092420801c0ea40c0d95403802d10076005c0c800880d00a61010030b40d1000034103142d01c00b003c0c08140180c6500003100c0c0c900d130002c0040544d4030b40302e002e42285040c2e2040000c45d040f9400741074000e0141944907195200c0100140c00c40740080302a4215582e1404041e4150909201e243c00700d11141c00200300802d1449400b0f0200301c8010301e114400c100014800b02001804d91480c2000350707140088814150030030120050310503c10b1500d000034401c51000810072102c0341f0580003194010b8455410ba91140c100e0818140034240c3c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 269429460 1250 269428210 269428217
    0x142809060c030b010e120d050a050c0106060302280e0906120105070809010e0619090804080a0b15010c0b04030305060f03060a020a0e0312090409061d0609061f050907 73
    0xa1008141a4003400381d2020a9590018400b441c040000d0105011395250034010503480e405034501802c00a0807100300380050600640f18083c0460884c0c441c407540d20103000f0365003000000160681c05402400703c1d045134041c1d14007900301d101e880200a800200079a80040d0384002505094204100c2070342d0070040c0a03145d130004101481c0e10500703440c000c3d01c0c4140051303058420050002000e2150052083c503070005400c10381400b071203055000340c079800518100c50340e5848201c02c015059044a0013410300d41c05443e944616805c0540c444002218103084803422002c02d0301c995803150454002843e1f000a964125480359141140204401843c071904440c03081c030011403542d010400c070345c803500f4440c0000d41c2c2e80d0004180205403020b6011002d000360b1142d501c800c4484000f90642c0c12440098a0006180781141822009401150b030800f20800007c0348001203580f010481d035215090b142c0c101c4070151105400e5000095450744125203c00b03001e00c05200c00e00d010300c05a504a00d2a16 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 269430710 1250 269429460 269429471
    0x905071218050d030b150318070803040501090b030601120e0705040e01020c0f010e030406080a0f0e0d0305100b040b0d02040e09031206090f01030305090307080706030902041428 78
    0x100041201d98100c11081e41c80034401c60141081000c0010721072540461600f4411048031101003001c44c0942c00c4818162880400050909407804024054180001086405156640b41c885440c1d9106001c0d0600154520303101142c0e60380307007038210707030092006030340b081c90419240d0503250041110365400c805034003c084000600d0303522406492850510440016690100103503070342c4c07501e220a59042d007a641010f00b612003075080403098504866590500110f241d0b10035034640010102d240e49440254980030b044061008001200d154650550301c00700b00a4445000c9010002031601c104a0f122008100a0000c2e00c1e0007005441549282140981070644440071306407011030460300715036540c2c00030400515003041d41c61540d41100082c0d44e00d950b40c0c1015000e510707001105000103014400001100301c81034030304005400042201406a507070340c640fa00c2005016042da0007080c0d1081c0d0a243d6400401c01c074040c891805642c1441d0218068440e0502c00320b036800fa1480403001c01a03840 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 269431960 1250 269430710 269430737
    0x409050a02120705011b050a0b0a090c030305030403080f01050a06030c050408030307210903020c01200f010519182402040b0304020907020d360305071a0a09090507 72
    0x81442d0780001c400c42c4040e02185052070b0004001d8002010f41c0d030130034440141190302140c004142c4141207070300f00c0b580603240c0d130b102c2401602608010200038a6490090300000505a0040145000714400c2d51141025101c01440003005582030254540c029100b1b501000224060751004542ca149400d129090660b6808014299003045030b841d0049081000000c0120440310300c05900505446002c0006083c241c0b402541c6110030340405051090452140781c0c40c2d10403120110080500c1e9003103800b2139068042032400781500f66140910300075510004007210805005220004100c44143c156415050311030505101d01ca071850003050b501c404190014800500050020301822031120f96079041c00d106001440c10010100310031500441d051110450344001000e454182c2c0940080850720515130642200c26a0005400d2031400c24a0000811101155880844001100b103560a003401201100c480c81404056000244554402c0c0b210420981c4015008069850000301002d0f04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 269433210 1250 269431960 269431969
    0x1501140a030c0f03050c030d0504060e0406090c0c02090a0603020f091f0f140d0b0a050a0209031f060509010501271205010b040c051e03090a300c030503060409050a02 73
    0x1250490740c03d0f000100414414840b0401195a04403000d0700144100d10b2220001491401180a00700c1001894401c01e09903648682000d005401c1040081000708902e0102030403c26003460101d0080f03404400140c00000c0600c90031044a4002e03040c0203200100108103c6016002000042462180b807030004408840c4c40300710b405403603503101c084013050801403061045110032031004c2c42075000108410002c4d09a80c5410b802005480740400d02e5182c10f9901d84c041d0043c1440c8503050300c40e001040640219026600382c100310303043e10401c029612001070141e42c1ea001d001c2d540c00305642c4104110310b13180e904030015400e01100600041c407511000c1d11101e084805030143c0f10743c3e442d0200c138006841d1030311891024507500d0070010b1070040319506e82c12a5183e5800ca07003121010100000f01140402d00500d1100d5500a02050701041b03182604443c00340000a11120650f1481038544114090403140c9100c94058454030b0031a66400100406844031036412140f50180700074040050301c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 269434460 1250 269433210 269433233
    0x90405041406040c061211041e0b0310030c0b040305061303030905030f07030e03010b1311070c1509080c0607230105090102030a0c090308090409030519090e091501140a03 75
    0x1c1500013004035407920700010700442e032045001c44070501d4080d50b46120742e800c208940c01c851103104807031410000030540a03121082544912451480081041813041c130042075501a00e108a601070541c5071260f0303461665026500000300250300c403101050442d00518940000548285004645803066030782d16400c0d5000040d901003040c002164080816802c2858020010700583c02000390031050310000d1249042421088581c41d03561860b02e440b000345004030f44c22160880c81c550112546c85410b5403420000c160014009074009501140d003070b2010170010b440140007400307503043c000d4584559030f04003281e443c5002845184400d0504100342801001e1040405100042c1c6031701d0101c0c03d5900703580e0f81d071700520104024000c1c1400002c01c13140a88001010940300011100094035080d20184035001c448034041c0b450803a5104400e5024012500f40e83c00415114038945414600580d281d42c0814091701c081300b40030040c8400e81103d20b101c210a100201800141c0f83c0c1da440f80c84a545 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 269435710 1250 269434460 269434463
    0xa0b1f03090201030e24190e0304140d030801090c09080109051605030c090a110c100204050a0e01150c03031d070807060f02120306012c01090e01060509040504140604 73
    0x203032076000350419982c062003480d80c58050301c0041e041941c0201d06e00380d0224107007020b07401903c900b84086481c1d50442c04040c40303140d450b017104100404452440940c0c0b5003051203801030070b500790240c050b180c0c00c00c0803a060b5150784c192511041750342030011a801070980260340d41c04103c0801c0000075003000c24041d40655600402c00f0740750300e00008200d03005d036070b201c3e0b04014013035400a003092840c0d49807213020960103102404c0010700c7c01c0150601292b0344c4107140040410384100108120f210308194000d00883d5000c07500542d0550760740c11070500701d030700034428426180d5200c0707a42c1044500401405c0101e0b84285000a08082c0e41112440718400740d07110041591f1200034203100070078042140e84c004d40118144440c8407182240c009580304110701100c544483c010000c101142d000343c1941c1366a0002550203d940c61034a070300e400c2c0751080c05260038006021580006100c0b00d501002030b05a485968409180180403002c0c0300280002a0040f80c0880724003401010f00c1206124090045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 269436960 1250 269435710 269435717
    0x1090f061406030607050a0e0307050612010602070e06010c080702032a13110714072c10030b072102040303050c25030b0604021903021b0102070b0a0b1f 67
    0x440c407420081034448004003010b01a03403104081c8503550f03402070155070314410b680c507203018014200e80c042800c15910380d100c1c640111002c154020007590460056040c0c56031642110040f9540e0502a01150001d960050214690040b6400411a03801c01080d01c10700284c11500780c0d00400805202d408000c00f00d04102e00402040c011092420700d50354010000140001d016240b03005100034458411148010300701c1c01c1480b1104494481849140003e04000a540204545161404481c1406070741100c05800003e0b00065042154852484c00d507508040d1000007517507541d401740d81032641d520007100004008070030000103c0386030005102442c440d03034a15459003803042d04945460503120b5000045101e4404014501301c0401d10343c0200e0390400e0a036409a191440810000e2058180c1e102809074140c04090003985c16800404d49100946900c55103084050412402c0340100200204601071100202c1c145036099040070b121200018108200600300c0194200140e01001c5c040e00072 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 269438210 1250 269436960 269436971
    0x12d121b020d020c030a0206090f0111010e06060f0d0c0b030919050c0a0b03040b04030c0303091e0b1006080c0903150108060a1b0c02130f09030801050306010602010b0a031401090f06 80
    0x92076044c0040114000194010040c1c500194001030050103102c000718021014141005038030b80c0b10302c02688600c0400d41c002c03c600d80031492419201c8a0868400d805400c00543c80d19031420803070310f050a45900086002915401c150301c1102981c80680303644d000e0b00ca00101c000c81208048501110284501c0c01000c080207800b05101004806502c0104209030610070070020591500800e039025925190441021010b450103500500700d00c507010b8114500341c0350040038201d0750440450600e01500300e184056031804891040b294883c0162000604081d001c0751040c1e989002501101b900201034580b0600d17400003900c0c8120090740100c00a600000a211481c0e005114444d0503a01c0e00341c00b140c1901702e028020740241542200240500b0702c2c2e150058551030b49d54003803501d490b0740780310074030911110381402800343c2000e002c3d040c481c0c010b210000500e40d00501c600904480d01030301800d449072464455413100422401c5800c0d19540703400600b000103002030740c002c900700c0c0b00d1040040c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 269439460 1250 269438210 269438233
    0xf1002030103051509030f0906120f190510030b0c0706050403080a050c0a0c030e1909060e1609051203120a1a0109050114160b010b0306012d121b02 65
    0x213025804001541055008400d20000701d01c00700c100c40804100c1030869590702d000d00007066103441061410585444c05000348414170b02d2f00f05689015010b11088028000d15508180c3c044070740584111500050b060030400009e2521a0019400144c0307a8102d800d00e00e940d00c90030140c82d011101100018000030400800c54450300c2141e4000c40c24100c41c0e401c003242c04101174801c07001e0140140603c00d1101c40b40e82c4a075508111051b10302e000c503101d28180c0c1e9442c0409409001c45000d0f401d09030a0400000d0030441d90700441d07403d001003030faa94022491074a01808950b0880610440c23080c0010054580c0c0e161152001a014110301c480000c3d41801c4400e849504c1203508400c0d5041100000c41044507a901c5030249601c2307104007114a58503420004c20b0004a81300d808000c214201c5400000b4014800d43c001d14880c40e000c5c2c07980c3e0083c10a110f85060000303d98000401c0701c2c140c22041c00700051080713001800700d03402c02d04d001400000d8141a510300c0006101da040050b84440042034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 269440710 1250 269439460 269439463
    0xa05180403110f07060e030a0501060303090602010c080c041202150a211a1002190c06030e030f04090207020609180a0c23160803070e041b0c11030f100203010305 71
    0x100060703885809031484050f11466103880390030911510b001c0010480300034429540c00d001024207283d00c0f000070001c840e40d070300c0c000e007800403c4c3c443d81380554601403501c42e4060148038403d102d0701d4060a040e00d040c3c1049003440490b0280f8409a03005010403404900d40e46240b001000070141c1c40c2c0320403003990b9110365001c842000d842d42203540d490411135895000845800183c56a101c221100c0d06035682c05402240752456400030a542c452500c401c5005101400d030681c2c0980304159428400300031000c080e42d03541d1240d690440c4a6007803c11040221340c030107a020b00360551008005500d04482c0c03600290b001e0714050350581000101e442407000100861045241c0c01c0b40340e0601c448505148844241030701d040700188129044e00207204005000c0103021489440e41c42008144c4038200340900503c036a4000008500661504404c40c0a1462032000d0401d2100595a12080c0080c195640c8401802d8001c41d60b03014441d90001003816034051154030f160108003440107031650324605246 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 269441960 1250 269440710 269440727
    0x1b0303060a09090803070f2309090702031201091e060602010c02010b0a080d11100e07060906231b030c03070c1208040308130e01091b020114060f0a05180403 69
    0x4182c10714100303030500080c04800c103507640140f140c10683c62403135103060b00351150b10071900102030111015006501d00d005d04000b9024006068400104076500c28006076600d120305404004140ba109004104103150b581001500344034034001d004040303070b1020104069030711b142c21900141c4d454514403107241d5070903c6100d07041039089401200f154904403140e034a03414210062810049420041480a0810480c03a0500b015020041001403032909009403580d1647c0074000012341d00a07400250b280c490302c0d100c0d440f0000f0440c400a0341900700c9864003158010f00782c001c001030b200c05000080d031900340040c080032132940010399520810f0389050305059180b60000708602400c2404040481c0c02c5e00c042d030341601e90152070195544250760815000c0c0311a503000202c00c80c0041d0000c40c0301c0015404c00449404880103840c23181000039002e074280c50303000c00000f02c080c15010000303c003441c242490f907010301000b60031440c0e02516280410400407013594041b91010706401400100766010240 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 269443210 1250 269441960 269441969
    0x90306051e070c061b020f0709020f090904020d02030a05030307030f111e040e0705132403021308010f0603050c0907050304030c0606080d110105010501090305030d111b0303060a 78
    0x100d0080344024494107488860140080c0d04002d20800c410040140b9544402492582d0134036440b094001c041000355204840c4648846602070fa4800180c0f40f42c06000750341c4000b5141d000700d410541c2000a010013540014070980e40301e44620803040160700c1c18000e107900b2502841c00f40d550385c5080107010f800d0368142104d05011034a8240740700c41900d00403007503410440c1e800000e103100c1510b0420a210600a68101210047c401c0f8180192150131100810020440c0390480110340c0e901d1010410b450b80380d00800340410601051307404018400e0b03006198189201105644094071009201e085a018025044138182d981000f8018004100308180c140036040310100f0b024a0689001000c3c0d000c007800c0241801007203a034880030401690001d90107004840115004061036450042055014910b440610b52a2100200d055486130800c80192604a8019450300d09a007072080010800d1048100450b4000d100005d12240e400313000700919504070006680300c0c1050030401c54102c409600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 269444460 1250 269443210 269443231
    0x1712010906140307050d020f0303030c0705010c17150103020d06060909060b031003060e0a120f0e0907230405040507050a020c0409021825090f050306090a080d0b03010c09030605 78
    0x1140140c2d43e800136a003000c2d600280e03a5005003202ea840450220000c2c80c090070741c140008802c00c102040814060302103907020744024840e01c40700700340540c0e0940d4011340e22040c184802000070660740900480b04103010042c5401032400180641c00022228540c01c908001a49104104004103242c014080548001e441c00c0d40b450410b1000b8103030582092000074992626482d1840b42c5200a00c50f040c00280c018445158142d0400c0b0020100c205100c40c2c980400d86413402404241821603520788504080d8484010760001680152000c0a00c5004050f0b140410000800c1c1c54846004440c010b035070903102d40351101d480f4040642004000c041040c0224903044042015a88010303031010802c032012101380084d280c2c001c910400c200c000d5003040c60480081c0f1380d40181640803462204481284200d600080d0f1900100b603110181a6001606a8042c090f0000170840080060208180c0c0c4417001441c0b000510100e42968180e075060000325600303110400a014040c0130b0264401c01980 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 269445710 1250 269444460 269444489
    0xc1b08070e012904051503011d0103021c150c020d0207091a0607020f0a03030509040b030a02060a03180c180506010305040314030907050d0c030314070b0105010c1712010906 76
    0x145160f0b10342071030010302032842c040d9803456107034000720008503005860090300340140d190304981e83c0c01407070784284204010700110305101ca1141e80c252011505a1b58020000506150703900b008a0005c010034206841c038030028050810b040903103100d0b820840715a83c0292441180c4040c0103414280d280d404480c003141001481840a40420859412078504440298445ea40360003c1403564180420254001c41c0700e48010041c160010040c0c00e4001d000c0354140413807a200024562103d00030f01c0f00075000442400354400c55070094002210310042072800c190741e120513880d8801074221940c02040c2425103458040050340d924061503901c14028201800380f070900d0b990051030311003150320013420407030048045079141c4c2d02802607000800f4000c1102e40032100340d00700b0b0410040c403803004a01003520038000f15410b20158050b43d40036a00414206080d0307107060019038240c4000e84080b03034080040072000e04008001c0e400b130600f6450700084c00750380b9810310600070111070b40f58005108800c05c80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 269446960 1250 269445710 269445719
    0x10219050706080c0d050f0105030f01060317072409030801231203090a0b120a05101a04270c0e0d1410020a020312151f0c1b08070e01 59
    0xc1c00c41c00c544441c50480f0f03003940c03400c113281c00900038003840802d020308000500020007c0410054180c41085080d01c1c2907000500326242207800d60300c4001d0455070b4201c2d00e00c103884042d5001d001c031603010348500300408102c2c2c05030f8541105009010140302e50740f00550018942c0c0041e4550141c401a0300d000a02021561241c0300035000e100c64074491806481c44180c00303401071065904941c8040c10030494540c5417040b00c409a00021820380482c0329940002e40c81c0e449902560b4011104000d003080058204002c52002a16122004180c007070108400106818503801c0007803003900c48040304c403041c00304202e0758081c3c070300002400c410400b40101006191f9034400c000700e100343d4040e403030707020a00755452041c1c10060850120545a44045038900101ea004001010704840006024404c6d94580326805a1601c0c00300c04182c1140301141000508080a0403030441f0b00c80701c3c18a120014450794840030300d600c6154143d0131a403482c05040105200c00c01400b13025001c4020003c40d250b050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 269448210 1250 269446960 269446963
    0x70317271801120506160509150c030f19080114040f0b03060a200406020a080a0203090a0f0f230d24050105150c0a060b040f021801021905 61
    0x2a00344001410080c4010038480d510300056041600e50559440d40c00d6940d0040050703d4030281c0c00681c1d40e070080600082500d1815009003822040507112981030455071818002840140d120355210400d04104400700c003041000580710704601d900c81c8603643c0101c0c1c02c0e462004402c0070404424130000c0341c01400300700310034002c80c0001c50341030318002000309000c2c511502600d1070840030354046c081d075014421070207402e81000e0400100c148104880c079020b400b10035030900c220310503c00181c0001c091600003c50360002000010920301c103c80c14007400c90002200f071186035014242540c510101000700e445200c0600300209a0b920140c0302188004161080e4100b003040c4251103070700344510030400c1001e090341081050800200c0c040c0610400060040241001c0c05a80d2240c1c01e00303c21404a0501c81c011034140e5070944000d8245007103d40e03103100260604035410b641c41a15118504900c00d500d1018000007100c00d01410b101c5940721001a0407d070203d0742c0d580303855880e00f40110201e0320 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 269449460 1250 269448210 269448247
    0x80609060606031504020f07230706120e030a020c03070801061202120a20090c0309030712051c06031704080601120512070b04050c030d0e060304020a0512070317 71
    0x3001d644560f40c81e83d8841d4888205012600c0d2242d020740302040d002044c0501d40090140680b00d03210f249080e0405801d180d50300c10800e6a840c9031603000000c2444054410f0103074030500c0c524001c0106500320858016420f64000c42440d0300164031180c06a00c80c0c0c0b03000c009680080090318020401702d41008000003481e01c84680203409080034241a03c0007000402214071826009503c2c13108071080301c0c0ea092066412940098411180c03000851030990301e00084178000c81400e00214940a05a568921034082c909010703000c2c8502402854111422003002c0862014000c0d40000d03250b066241031480c9241d1400402880c1805100a20081500140c00ca041d1400b44203a00c030001d003d0f1a005252040c141c00301d005126010800c0403c10440c60b80c1a405076129005031070907600c081051583c4c98075521001c0300000d4101100c0300860074071900a54100c2e001820303c0c84050b4681002c103032042c51241072282c56500900b410030600644211085500314450146464010f24000c1c01890b2074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 269450710 1250 269449460 269449471
    0x4080304060c0e031b13090b1006080f06090702010b0306070203070308090a0c061d0d1a060102010507021b030c0a0e01150c0b01051309140601080c0102032a070902030a051008060906 80
    0x10b24000082c02c59951107546810010044010f200e0350002340307001140e4000c145d454000304907540101040107401281c803070b03119031800380c51a03036960303100d80800c80d140d60060000d10030b40d5a920540c889540341440340f64410b40080e002199a5801845d0090010100074849401c81e0001280b440009800d103010408503031151420141480d0084903c144021415134090b501201210b0113030108424030400c0390014403150019010b5544444c01a800d83c1c8040b00c4000040c0c00bd4910b4000d800250f110001c03840c0c40c00350484800810003408500440c80d10340045002c101d680004000382c2d40c200f52001614521f51815030002002642c0c0c8140d540d03410b0188031300c2610600e02d03000c040340c8a035108002894121000c4d1120010316000f5588800f02801000c01c1d0b4028441d14070308550000040341c0e00c071030302c1040b03100e20b8440040c0d2444000755101002580307406142c2c000580521140040e600031400000002141e003040c0400c042301e250507501145142d0000340c1000700807840416031a0384034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 269451960 1250 269450710 269450743
    0x90406020f0409060906050a0501030218120f03030a020d0c09030305071e0503190e06041a0a051303030201060602060a0c052a070e10090902090a0f0b0904080304060c0e03 75
    0x201d410100c092510300940c3c12644680d45422400600441e59410503411580c003603441400440e01c03100110143e02c00c43c10890550080c581841f4060300b03103c030744900400c00080a03142c04c480b190443c18115441a6600801503801080b40b14401d01e01e07200b80b851510260030304117010751940d90b020341701340901c00c8013900c0d034103909415800c00d030241d846081c10154400c003600e58820b200004100880000380081000450040901d4800c1c2005000c9600391000700c41340e08030a83c0c4801e0b052406a211280401c20000244047c480305c1c010718450710091846500081142c0b0709100c8000e10b00314004100790609800c00201d0b002243c1c0082c100c0361303142c44034141104020090b40004e040829840d40841c0903201c0c80500180d4102e82c0d40d04280182c0910941c2c2040540d5403100106032400e07403c0103540030003d240410035468455018511b00c0e440c01602103501036124001900b10a0304507800c1e0b40c4c00c5800005c0104110091182c0b50b2904501e090841d4a4040240030a41d2664094003c0480 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 269453210 1250 269451960 269451967
    0xe061c0312110309031801030606020a080c01111303120e090a0b0307081e0111090a050108150916032405060a0311030703020a0906080f071b0606030813060c0209040602 74
    0x101400b50807a4800c480301e4142103599040c4041c1c036641e254001c918003104100c0789810921070358424025141200e034150700412008580351941c06556010410944c0d0941d0390f40076400843d640100900b2402030040100700c0b21529604041402d0302011400c07a04021084d205204039503240c000507a001204c801001404244201c04289404019008014607200c0c0d00041c1c0a41401c1510071203a10140b00001d04c0700d031821859004a90042022142c0c0c400a284800e03c400c0d48074100d107540c02541500000904420301f008214111000c0d2105540e19854041034803034190140103d6401001d421403103a1001503c1c4650100306000c0e0007040d00c10400085c0700c40099129802c012441c4001c580c0c00e50f502d0034080b9000e8000e50009202d01c001c40c50120300061260302480400e8442c0c070585400c00c1d19581d40d02c10403101d1301c0304e07011000c81d20000c0c074020b0f0003c220766214510146101d142d149540d180074114008100c9006d030300000030444503080080c01a2900c5030031540099004001584 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 269454460 1250 269453210 269453237
    0x12901091502150c091804020a060509031618111606050601140309010507110304030b010b0307050f072004020f090d020d1406240616020402090a0605040e061c03 71
    0x10b003007030b4030551a604440c00303062010303541301d00005207080f8004403040c4024484216000e50022400c4402940c010f403020010814a8001c40c001d20200f14014262a40050221101c0348414000d4200705a50304c6c030344154002c49902c51182c00065000d42a6a0b800d00c41e01c4a07910f86000c82c05100100010f8580380032078101c0c1d0203031003038060800020520903202d04c0c00e0b101d031500a11303040f01c241303001035050070032152140008421182681c0c1c110346a144941e00308100c0a4455101500110030007104112003180c420a440242c0716007845581501802c210349008040c1c0028011050303481544100310f5521449400e4044810074030b002c0e1011041c6240900000700042407141010f402101c80900d00c1c2400d00780419064801d46c400500009214074070a4004800c074a030110060700071034100032900100e112280c01e402014802000540b50040403804100341c0d2106a21040218070081411b010305004515159403182003510f4520300ca0220440403145030700b80107400381c140050051000f4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 269455710 1250 269454460 269454463
    0x5010821090a121104180611040306020d0209090109020a02030d0b0a0e0c0316030203220204090813051215040f150203040f02030105070e010206070f02190302012901091502 76
    0x100039140003494035001c19a1000a00044403000700104c80321922071902c001d4a03c3d1600c00c0102003408a506204000702c0366596200908c5c0715442413036036207004d01c0000002040c900003841000411407000d41c0710f184003810b01c032007a01d0681102604034010701114490030350000980d003e8000409010030031201c0007020424240040d00002c90600300c1b0001c2200103941100210b0059402c0e07100400300d1700e02490f0407800c90009984108200c8400c510540d030659006018030903447c0001d0001405103010743d501140c0f944640c5640500c0200d0704010007483c40d020071030804011580000e445500780c0142c0384280c1d2070004100900d8009460a0701050080c4d0030b440e2010501030f44c0c8110359a00f401e040100c2040e025070030482c803940c280400202c0c03041c41008600240310040c0c000b4001620351040a40340024003903298821489280075a508004003003003203600041c00707030300001021310f00360755010341840303c103d410840e48203180710151407070340c2c0004588c00315080c00c00805441100020100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 269456960 1250 269455710 269455717
    0x10e061b090f1e01080a0e030405010e040f050901050108150c04150c0606090f0b060a080c0a23040608010e0f06241b1e0312040c0302060a0306140405010821 69
    0x2982102030ba8203400d003060f03802c1c803040c060190241c03581c5507a139407007049240a940104400c1d501941050208022a50082c9003511542000030808a1a036081c1d000442c1124022120010160344072801000003800c01e1003119121850300585034000e18160100d45014841e074411341400000b0038801c02c902a00c22808a03594030341c0443c00b8088195103541c820301402c1526a4a58668640181002d040c508442191350b001c41039110b9002559030004a80266003000c040352080c40350344418084004455510003003041c1002ea05191500d0170040300500848058103c2c0040b04030300d01c184440c0c5440e240c20158040d038102c03507541a00d281040d8903075410300741000c80f01e000c0201198240100c891582c0304040c002e10801220a200364400c484030040a160310381d00c1c03498100f009408040304806443e0b551243c0620a0078101c10313980d5002c119030380e000703a0708000000da40349401d01020030f1078075545000300005ca501384010350605401c50b44a1822144202ca001c0d81c540c0e00c0a0b0141150058 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 269458210 1250 269456960 269456989
    0x11d0f0903040807090b0102010c0e030a0303050403140a03020403060c030207020a0b0304030915110111041406160b0c030f06090606160302070f090207150504031710051302040503010e061b09 84
    0xd803030013599251680300180c00a02c2180d405035003090520b0420910464041c80d80000003030007054649003544003900240703030103001501041000701403246000045001800071011964005944507e1410480215002c4c0448001014010030086001d42d07034140011094038840d10341780381d50ba2294502641c81d5040c03984002e580d90f281c0104c00310301c0b0307400c0715031003c810442e44001d200b4101c40d03d09114451080e40039a02202410749450001030800c41c2c0985540c3c1420410324820071402d8803070854951080301c08554240c000401c00000000340c02100e9048401600c8190031030516400080c0d43d40918204c6845207901c24842900740b61007000b410004211096250058a07200e00706013020f9400ba05007030f107050b40004045070031034489205182c070a5805036900c4000c440300a610382e80f030800c06042504940503455011071103030381e130100c1c103500c001c030306013005071f0340c80c90301045c142500c1141c5003154040d003044080100048004a000244c8488102d4060341e501100c400100e415088504 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 269459460 1250 269458210 269458213
    0x1a0f0313120914040606080a020d02090a03050706110a02010f030f1d0c01031d030306010e030a05070e01030b06011706010e03240403030e120f0d060512010c08011d0f09030408 77
    0xd0701c49400010703400c1035a124400710120320240d50240030640701c882c401d00c1d0001d041c3d040010301e0040c0c564080c0400c001100405131410260100064089100d07030402c1e901504000303010401150032041100d0180008400381c04101c40302d400192a50442d41420814180c8075150132241201c268003082c9003841d0f104201070105010200107607541940441d60740864078004071640204000c0070140d1224814070001d62079036562400440301c50182a24207030f050310a900381c0e0380c006801403080c0c0300640080481d1661940c950f003819130801c90042e008605020681401704c4081107991001076105030203080c0420180b25040100340f401050540180300600588003402d00346001c602d00b94090742c0a640e050010018052400e030302e80d0403941c01c1d11820f01d0104100003482605c4c90241c203206001d0302e03000800c0c42d0341e03601041c9070200030780b00d92000380d41d542086c0c1041d90b003110009002d00100c160440051708c80b14000617200c50041e02c0c42030941d003a800001c3c12100200100c9019003000e60 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 269460710 1250 269459460 269459483
    0x9221e0f0f060e03070519061b0c02010e01090b0702010818100504050c0406060906031e020f070b0f01061202030408090409030504170c090711010605150a091a0f0313 73
    0xc02000400c80740d40120380840c03d2506400d079a50001050b21070880d0450040c3c01c45103940c0c0701c0303900003114140040b9131041e1a102d00048900c2c0c001c403042010601e0b5100c5075030007a003d20006042d10383e071f0b140c4541480a540030a001c5652004243c4285550a00308a2130a031540350341e610980790350141d040e0b000e1140480350304049032190410b40c0074a00c42c030708030f541d0143c130030040105850042c020a00000d034000c6007005403610a4100940007401d42d002da05590701544110710990748552440d100d21300002030004108440c4140850780014040c01c0a4040d50510400400c21040d80a0015500340c0210200c2c092140384401c548140d84010310400071014645000341035078001e8400c4c00c06468280c180001c0420020800305200c1c0802010340050356250308043c0d40010b0b103951003098541d6295400b04d0503403601c081d0254078021100b0341c2d54440079820401041c600207a000300080884070b10b0449039001d10b900c01d440382c64118607000b40d200e55401809d95a404420070340901481e1512 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 269461960 1250 269460710 269460713
    0x60f0204090906050a111e0c0d0c050d030e19050304152c010509010309061d0610050d0c0510021212060a1e05040c0509040204030b0609221e0f 63
    0x40d07101c825564803401c0203000560305ca81c0440b04448803005141940007041010085034401c00d590140000b503080401414180b03002405441c105801c2c00072408a05416115811300c04200815134500c08c00d440d0520030700d41c00310070841e00c6503424003800c01d03244000240f01c8204030b0b0034415100030340368040c010000b81d0a0f0312802041081c44400c0140a05c0814640504822103600103491944c41070711424581041d44004400070000d0040984010b5504c000303c51341d6028100c901e00954100200504040c14460400340e02c086d81036010510642c049141d250008101a03440e0301115421243d0712403c0d4031606059040000070320f10035106d03001c00124800c02c040d402480c82e01a50068440303d04c1d0301c3c2c690590010113040540ca40e00700c00c410103030410151400c4c1d04004644d1105245c540e00788540c1c40040b4061780c0154104443c40801c4404021040c02e00b50a074590021408840805110003030b03055810f1310030000c0000d030071810700007110018903a070f041e80503420315030050301d00f02c019406 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 269463210 1250 269461960 269461979
    0x12d180617032808040209040f02030f01050601030c030c080612030c030714010f09030e130b0d0602030402040e0a0309090b150a080702100e0d1b060c090806070504030c0909060f0204 80
    0x4001000b0303240541200c03960000c3c60407a029030707802e0742901c440000b84c44540070000070b444010011980310102c2c246280c0140c5040c056510030045003c004030715420440005800d4500d40d41d03201c410103240c4429036a400b80c0c00b1214540111b02070340e01e818546d03d030784442411031040144859452100140d04410804680b030b0403101510b00b40000c11040000c180c0440548018020150006004007680c481d18a800c8c0c0746056a44030b01140020003060341c00104140c170351380074010380308183c0c0842040158246801989003c9180e10b010305505c1d0004d0780c01920982150190031042540c0d0b007400344468503003200d1140c4214001041c3c40e1a403480c0e4100503c1141b04541c1100180280480c2083d8100c440c020048900c04160180000d020b008904a440000190750302c01407190541400c004511184190a0320140903900c41500b5410210f00a240150151101c402c1120400c010000705c0c0c051100501a10b824680100d00028181807400103441d50343c6d40c004a0620010340014200701 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 269464460 1250 269463210 269463217
    0x130e0123040302120319150e0a1a1c0b1b120103110f0a09020a020a0602040b03010503070e13021203071506050a1a0403030c030909020a020303012d18061703 69
    0xb007903086948460305244545428001a54602d0f20b008900e00710282c60707036080d001006800c1140d543d8000c0180e850a80b100c5000056500d035004680d42e0f4004080c4525001b0281e41d400c0c0182c2e100800d03040300603186c4100001c1a600900340c0c880d48000300f0640140b51a04d20b9010a074201140d4441c03510b05441c0000d14020b100c105c0b1140d84000300700c420390608a4500303400316002008010050b00d0608000040d520092110782103015200990340012041d102800c09000f44c4216a40c90390306140c249480c000503500881c01080c1e04030308006002c08400c03105a80d40758181c40c043c0c0c00c0c41071030558a18600420000400c0602042882e079540c11460384608112403007203540c1e00300e503591408194490310282c404000307007030410001031021a01076400300c07950620a245c501c6140b542e400051040380c0060b00c4180042c3c00000041201d0302c08011111104034041c107481032080c0c00340c030319524681468481c0341219950402d0f009054402588070f0401081903980100c00040d1007404241c8952 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 269465710 1250 269464460 269464463
    0x2030a0906020c0f01080a060e0a020702122b0306030b0f0a231501020307080f04090605220507050d06120512070308010605070203160612060e06130e012304 69
    0x401052000031410302c0010303000036149020300b1300c5554460071001150403003002880c01c1c07116a1200d60028440d0341c1c0c080c8861040c0c01e044001600e5880310720401450341107d11046046034001b80c8102e540d04491401c000e00a01c40b52201c410803441da0006601814482c3e00191903030410504115400c400c52240d140304819111041040d21081c0040c0301e058803094034110b41681c05180058414111000c4850040205004a03400d102160382c840c15140d1000700340440400011504100d20f40c1d16011324409401c003203130080c4d48034004001c8172410a02e000304141e0502d13165004107905034012001c0302d80b070500300401403040c541c803189004c01e24181450101c60600c18620a1410620207501b03480348140e15590b03411980e441d01200326002c3d080501c0030703030b4140140300300388031042c4020001400800880d154a003200071320741000c0044900c240e0082c0745400140c070070000c0c0c9585a007000c0c02c080500c500c000400c142c48219030342c010490428841043c880300482d003150324000800c0e661246 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 269466960 1250 269465710 269465717
    0xc0714131e050108031e1e041206060902071e110406321c08160c050f010212030c070809041a09100806061215070f09060503090a06110c0a0302030a 65
    0x81c1d90f03922901e0745e00e00c185000304003043c1005040001409501000384400c91541e824075040e01c10741d000b01c81d440d612907440418a40c482581c00403c0003031030300074500140210201141010210b407906111480c9010120407503001c0c03054503c08200b16a10100b45000020b0801c1002584509007804546c000d44010701d40e004c103070070070701c850400c4016114242075005440e11404401c101140ca04040d100c1800311692881031018681001c034046424000500920720391204600d0b2000f40b103c80803401000f9411500712400036400621004c00b203981001401144da40d8403580c6050000050047d00901540a401c0141e1352114070f90440c00507041f07100031900c2103904e856a80d10041082e26a204502c0c140d08108001541171400c1c0288200f0f80c030200341510030300c603808903040035140012a07a19011681300340032030907201d42c04035440300a040181001031031424260501e40e903444854100038804c2d516055111400a4460262002c00b0707084012110842c0c1c0915000e52a50440e07070103103002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 269468210 1250 269466960 269466971
    0x51c05090f040513060b0a08010e030d05060303031e062706030105070503090a03031109040c090303020c01050f18010c050d0e01080f0103020907030e0f0708150a020c0714131e 77
    0x6280a200c1e95006501c1000c203108202c0d055039401001c0c191a06c112540801d5950000820800a0041340d0951035550083c6a4604a241c40141180c40c0a00401c3c042e41c004e104020b00d8802e2000281c4458240c108011501c0d80d0f05400541101007040081c7c02200441802001c0c03640c560800c41d02803203080b0024855070340c500d5012075140c0401c48815000364020110035022038026403048403900e00b0942d142c0d280c510400c0214042e541c000010500003541500200103040d4140300c0661130b9402440e00b207162030145180300c0542d0241d82340e4041920718210f8160000ea00540c140080c10f0392040503200c1c000c2c40034501800c41c1d0046108117020409040001d0083c941205225050344c1c4d00600700300c410340b64a4800c800a110401c0483c810340300700c4100c41900369040000e0402008903c0003465405120100c0340002240605052a05030040c0405114008041078141c25984641a0490010f02e0400050a035040d860b080488091070101c104590140003001800f078602e20050a010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 269469460 1250 269468210 269468239
    0x705011406131130061203090f0a08250918030815120a1a09070b0a0302040e01090903020d0e060d0207020a050a090b030d021501060507051c0509 64
    0x100042140d085521007001d01104040894640c08014001d12110000703062a13080c48409030038038201000100f03d010125648820714801401c0b0700d03406001555540c1c40d0401014100e5030b02e0007035410303003442801c240c0c004000300d80303524060350b004114100072104401700e60411120307240b400c2c0042d00326036010203802190a01b000d02940641500d00c1d034502c0140f0009840440e01690302600c0910090300c1c0840c6038010340c0d1504503803108110490003034081549035184c00c00075034810b031500d040049008400c00454201c00b041c0308007150300d0f11008594039000740600710300921a5801502502c1c04d2000003089084d202d601000b00c152198003203070b5a510300350b4415141940001c080b50b9101c0000c002d00340d08181c04e80c015092061024241d001d081d031722480000d40000490300058041556184180c03110300d82040700d00c035a00306038000b03040c0c0c80d511081541c1c4029814050340080c070100040250800808211100000300342040034035103010380440c01802c135407140000c070380b040340355800301e04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 269470710 1250 269469460 269469491
    0xc0f120c0902030c09040c030b131404030804030c141606020f100f0e0f21180108070c020d0309090608032a0321010f0b1614070f0803070501 62
    0x485540d084510210003525080c0c140002c1d41c0002c10b44802890f00780140c0400380c44a000d400480e101e992004200c803a000300501100c00f280110020655080540c041c00d0500001304c5c0980240d050302c3c0101c034039999410242c1e04a840100000c00d0301440c0e0b40c02004a100108692409034200040c4c00040d43ea90301c002c0b661a80c0c03200c1805a59000002d020b030225215a00402c1e0f44c0d40300c180c2c0030407190241300d41181081da21300c003d0301d819004001142c00c01c500076101c0c0a6807040400c162402d01d06054180e044240007015a107051144541c08034601030702802c007140d20558000c151000070300c040d01e0010200780e003030320840901500b07029020500310008821303210780c000c240002a0880c05c0001d800c07140c0c030820716410301c600c0c00308101c100c031030165003090a41903011903030311003880394035111903061000100ea01200060768107021540440401c905400344140e045030080a03902210728160382025426403100c241080110780008080c000072024200710340c040c500800151280c14803d8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 269471960 1250 269470710 269470739
    0x30903190509090f070e03010c050414041b0507060209040c030c0e0a1203081305060f0916050105040302061e180307050312030705031e07031407020c06030c0a050708070c0f 76
    0x2e641c4078000200080741980302141840d40008075141c181500121500881c0c00c44e2010f40b280030000d1000102030145000b1140d00c411100c1040d681000001d00829a4100060315407001c10200000040c1042c148111601034130f40b00340f4010000c026409040030302070001c0140200d22400300e880c0c3c0401d11118075125158404a49500350b42c3d2010051540d003c41d504100103244101e00c42031800c1d501c01151042202c9485079558040704141d604080000d9480d010000b46111802c840b05a410320043e603001c0305807000c683c2d06a507082c0d201c0240c6565003011164044010b200c080c0040f502d1f2808031282d030000082d02000340c007900c103403548480130315896601a50000280000c10000b1441180c855001181e01c008285424400350800805030041e42c1001d84120300080d40b2203140d0103608403c5261940c2001c4240010140610b543c0082200b44c00028078007051800049510701c00a400313441112410759000c00002c1e81c2d48402c3c030300011551154040c41d514650071080100309080c1e0801709 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 269473210 1250 269471960 269471977
    0x21140412260306210f011e09080d0c05090409110415030506010e0702070e0108161401080a0c0309081b010b01080f04082b091b0506070b040303020f0309031905 70
    0x600d10754510007440703a40c101000c0b41c8480c450404c18110341010042c0032030016a03e008001285610b146c1510350074403007006040c00402490b210a4900003903028086501107400c0400201c1c1e8440481c2c0166401d018140c40d55800c00e041688540c01c0120310212544801000c541c20000030016000c40c4485d041c19000003025907201d040188410301a0045859110b00103204a0780d1864440d0f90710131000001703a2000300740d5486070400115400e01c0714500ea020b08000001c0c0d0840e0200840024003200e400740c030594607203568200141c5038910a420206295420054450b03603001071062092042284443c0104036518207040e0f5000341d0b103d101c00380d025042d03a41e04940c080c0c8990b12800d900340c0c001d0110700b0785070002554640540200a94000104e1b902c0b0100196003125810328131403804410700c0380c94030801c160905028540d1000e059800d295007120150045540b80d2030260000c0c811b080349501c3c02c4c0c00210800c64141000001807168813084030003012100b03036000080d181c07801505507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 269474460 1250 269473210 269473283
    0x1e01090b010e0408041d0f0a020a08040308040203070b0408031b121b0a0b0106080f090609030706110405150a03060f0302090112050c04020a0e010e0a0321140412 71
    0x4100440304120b840c2c1e04076020301e040324580780e41c0300700c210740e07628140c500100f42010080400c05040c00201c20b4a900c10080e00c1c0035480d02100d1200140003040042004060065a0f07002c0341c00d5407004c0003010040c2920804095807242c84000c40342c1c0d2900301e01081c00340c1c002c00c1c491400004402040742c010740301c13002c000c4500f8034000400340550041102d580d5040c0d40308a811580c0449d441e03400c843d000300056224030a1500f0300308201c4210010081001107071341d106c0fa0074080d503540000100c5628640064000079180a094800078051050b6805140d002c20311075421003085007460700604405840303403010024507544d003014800d07082c450710000c0d42c080450f00042001d49000301700541264419000d940014401200040882e0409080d050004a11501d008015600f0880e0034070700180403140c1040301440c60f0350301c3d080048404088500024034129296200c2d0040c16840d850070003034580380342c039183c4034006800c61b00c071540c034103880e540840610361440020060081524481440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 269475710 1250 269474460 269474483
    0xf010204060912080c01020403030f110a0c17030d11340818030a0303150603020309060606090a0f0605070605070503040507090b0d020a03050d020606011701050f061603021e0109 78
    0x9a0b048499104078000742c4513000100102c03503003810b00b0320003000558403039201c1e00a4501e0703070b080c010000740a014003204c2640c0410712040100e090114072004581001815000210741c041e0b0581c00d500400c09020340c00760070042c80040310101d0202800d0b540c0e0b1140c001c0c124070000341890b24844210b00000350720110b07a074034040d0301240490000b01060030407464000e1450400d8404a880c1000114094000941d0785807505c0501c40200340b005e0040c00140b80c207608500303000d050345440d1040078108074401c010000d80c94207a42c9640d51440c006000c10001940901d0b51000702070100ea0104c02e08507091446c00c1c0c00201014011400c0c3c0c0d00882d04240242131307550800c8045401001714030412076220503801c81040c0160703034081d0103402a42c461409130802c90302511000c3c1c40d002014109a06101c5d083d0350000d51038800d02815030445100300e400294400d050400f00300769101e807000d0711042ea2140041070052580009503550000380401d0490b081070f6401041608076141ca0100915404064 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 269476960 1250 269475710 269475719
    0x504051302030c0a121104020403140601150203121306090c0e040501060509070507020d030905040f0f060b09060304260c031e0307020d051b160602100209090105210d0e030f0102040609 81
    0x743e40080841b4064401441c040c1c581e00c071000e00c000400d1400d40b0603032244005104c1100c0030540d01606210381d000450038807840b44105050300800070111070340d81c03541d450354805008050f0031440c0142d8010700300518068440f10402d0440104449c142c81560811400040300c4c101445c21901c555665664907040c90b840368200318600380f41c035030160100110042c000c1041c5d0f841e441400c10f40b441c1810000b401c0c02440001c0d00c1030301c5103680b02340d0105400b405900043e0721003c040f42e900c85e500840c62010400c05a4040c2c0d414440581203100c10180071800b00400100000100740140c2d90b134030b0b000c0350a0f0302c460307003180244011200000182c10051170340001500400c0644103070f45030b000302459040e68010b085460140c1d42d1b5a1107841d041c06000411500340c045c810b0f80306804011400758901440500842c0400c40180f01c2c5c0390140709104200780c8916206ca1410a0860701101521220780001c480140003541d060b020a10902078000400200c45052007118121800740e11001401d0785031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 269478210 1250 269476960 269476973
    0xb030f0c16081605010507050a02070e0108060622090f0209061f0f26180703020a0b030424020306010207050d021f05120901020a030e01151e0504051302030c0a12 71
    0x42040d03603220b110400030f00040d000780207007031080c41c0c981e584a8940703042050003480d01040350300c540084124030005000c02000030a915921440035622080d9144031408844280110344040342e1480317180c92200c00804c00101040700303803030340221800710154807842c04020706c088800360210f01c007e1030000380384400342c0140b91840440400e070a000c01441100c49a40d0240801640138040d400c11403404c1000403c045950800c8175190000100311203410f50b804030302c0484c254040d1a0200c1c1000c00003c2c1003020b140d50b510200c40404586410030361141c0c00d01800703504140ca843d400741c02920340109990801248840c0903d070001d1800305560b66507481449144058142c0804104042003005600c00002c1041405100003400050340c0c0c030b2003590020100d0303c88600395142c83c0d05001582d1030080040306c001c003e84801040c1090a840c04005030351000300540e10080e0450304150800900100359034118072500d0095064074801e041410400140740701500550030706000c3c8190f4280411038 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 269479460 1250 269478210 269478217
    0x51203090d030e2e020f06010308090d06060506160309050f01090905071b050c0405010f0513050604060512010603260307080705160f1101050f16150203010b030f0c1608 74
    0x50126480c1d403901184100c00c000141418288a0802080112144da0704110030210600800042c01c8030f541507548000c0640328440d0118410a5290404014005243c0c091070050030300500c219078854058400e1410b55182c1807082c1c0c0890400c2c03100050904103986807080c232304416511b41c5000c60810700100018103024041208121040c4100a0480117109403251000d006200504507640902c041105a440c160810905602c400008100c6519050f00300489030f0100ca02c0855603642d10400305004152950040341d12903094020b4860040341940b0150a0300d0040d800303031850704074403104107035002c41c607004040780800b0402c0021b400c14440e00d59280c1008691800c5031038010f03695401c00c2005a5100b041c0c03003403d00d0b00600e0f4200001e600003403900800c00c0c240300e418206070728486022030254810b6421440e854100c90020442c00704032000c0099010b0000719101e507111094288260011140519121829800301d05c0303c005200070f462500c20241410300312092a940c1d00c840300e42 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 269480710 1250 269479460 269479487
    0x30f010e0718020c07030c0905060d150518250504060506040513060e100810090c1e0314030a0906050705030f1c0e0c01030b040501080d36051203090d03 67
    0xf076003481800150350060014800460180002c495030310b0501265a08035940038050520034a0500c034804005941e21160b1042c0204540000485640c3d000d98a00300b4440795600d80d4050141406000e61851800c142c002001801c0486c09141034464040c80200c42c168010036070711000501c410002440c2c1119001d2282080e01c402007130541d51144000d6807800706454100440e049400d09000680d000c21802d1417201c40d140040c8000c10860b110f428030304045015600744d46600d00305084503e80c00701c050bc4011603001c3d82400d14601030352006a00d2b03400c000c40c16030001d500c260000850b00d02c01c000361999240c228001e54070308000710910705419070201b18490250f046180c429801c010b124410b0304070b0b04e8181d001901d04d00ca8407000041c11161151341140c451441c0000501078400001400d0306600c2080c01d04000e07c0810130b010000001c10700c10308a09100504075182c04240b0281b40389000c917001079412002c45008e00213001e45a0160071012a01b2007a07042175440400d201d80c04030700402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 269481960 1250 269480710 269480759
    0x6070f1b052112040602070b06011d06030c0f0c010614010903080f0a090b0c161d0a02030606190216060906050a12061205010519060f18060e070806030f010e07 70
    0x401c040f840c4599200e0308440640d1041c0e07010035040300703101c25880b4155200d2000d01e440e51064000140c1c00c02d100964081c1640640804030000e05480c1c0094100e0740d000001c03580e015214402e190001c0c1c0641660b0245c07074a0302e00d80700c400018a50290b60310f00c094990241005040540c6a02c1580131038003c020140d01308000c0880000754403540700c008101c1c4010761805014415074011031030510410070762000718443c0740390018403100e020080ca01a0044801c841c05030340d03a00c800001078024000e10031100d04456038201d001c001241c001038000c0801e1030208016410329500d90050395102c156214000c0445c1013001202c211a101c3c07101000d001a128000082c1c60380c6400d20b640c03556103d01c0c2c1c21200c0c1c0c1c2d500c0d028070000d0411030000f1a07010680b82824031145041030740206641285d40314150011302440000c03d4140d04a400900144c40c120000c0926403074050750040000c102a20260302a000d0b032411a4003000e01806584030590054006155035440c1c41c019100c0503050381c2c05c54039031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 269483210 1250 269481960 269481967
    0xb07110406051309051e07050603040206040302090c0703080f040f1b181d0f07060c030c021003090303050a0606091215020a03050601021203010e2706070f1b0521 71
    0x90b6101a880f001c01d0840c010b0001d096903062400a1070034080844036052090402c607211904500000e034801518402d51b800d54403a03e8520200d0460300990300000d46c080860300411501c8190309011f455202d002e6030356400c05882e0354040044000090314003a007491803055412001ca1014003c0e501d41003800b015652401c0e036134030b40701507000e02c40d400e14055042e2281e821002003098901462041060300000d8003866410466042c3c0e5281d440c4107010502c01c00c1a00b1900f4940200603888440703802030718170325102e1200030004000f8204074004a01291070000070a442607040c1c40b8030340940b205501d50007101810040100030b4100c0c7c03003400715140c03e07a150042c03801c0c13980c500150211052030b840106803802c02d2000079060003082ca403443c44800051004204100321071400e96001404d02811400b01d40c0380d43c0740d04881e03074040d80340310002d40b01380d800313109a540d84603213100014542030f540d255102d01c2c4100100c2c240308080d0006461944451403650104070300d954104c0c1c1450584401916 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 269484460 1250 269483210 269483219
    0x80f0408070201051b070906050303030f161e1205010b07050c01050f1b0a02090106080c1603110f060117070608010e060619050406030f060b0711030309130b0301060f0b07110406 78
    0x29017014550150070841040081c19514064000600811400fa6046280040403801d14200090160b03008141119040b00344074040c00180c0e2444503800001041d1030a0b021000d4249600c0c694002e210b00d142c50000100101d4802c107854220307901101900c0740008217001150983c001191030008850100103001c075150030030140440d03002e2403e02504c91190180100245203805a00140074000d06d40b040007000b19560044801087d06140300202182c2d003420b00721106800c48810100600c604050000000800110740d4100ea07108041e03000414000d12415071220700e988520030105064dc801449203882c0401056440400609407a040c05080c02c0c4a0a01d10440ca4809010880c001000d014803580750080c40391610340c100c81400018601552110300e403007600800352001040070104090b43d0707014001c0b100420700c010001a0480602e2038510014250340c5030b0b2600c258a4400006445001310341c410044078561200700b800c080094030307025101480900100d070321030341d45e180206 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 269485710 1250 269484460 269484487
    0xb070201141312120305060d0611090901080c030610181e1515020106031109041b06050405030c04050c040b1305030102030a0e01051014010f1205130b07080f040807020105 75
    0x744000820f9080440f1203040c030440c0d915026a00008141c00c1400b0400c1c15101c580541d04840da010600260001004001135200d010703620841d80e01032510000041c540307000007903596014208400356025a2612844285405014411408007000800d07202201084036880800002130f0b07070760408c3c4141c50207403244045881e00c2d07445001446030000e050040084051102170160b00b90300080100c80d00356156512080d00c1c6290f01481140941d000600b00200000c0d40340d56440c40a001416603a00e481740074280390414005c4030f00901ca144500304a40c90702d400b0b55401a18030034001842c26061800d1070302658440b03400c42c1109508a88001502e8400f4401940300e40c40000c400244e80300c60011060031358801419044106c005500e062108640720340500740d00c0b0b0424280080a2a034520080d070303002d848403070b600345824607010410040da40e060b404c030110103200d9079000c1c038169546001a00c1c818000d40d944890801d4640c0007400040c070100003000501c1c0141803140c1801074100f0000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 269486960 1250 269485710 269485747
    0xc020307030501060e0f0603032502030a140f01150e06180103030e09011413020c0c0306042102072304020d02181302040302060d0b0f030304230a0b07020114 69
    0x88030302c0e03035545004100c4441d100c4441c6070089008141110b96090800000b40e40c0e0056215250240017404840ca011286100d1840111940901a18070034942410601c040c0109011881902d00a959202c0b8240e2010f2288203540d44d0a08081171806082142906445100810064008808050280254084031865402184640d5400c40840060002d001007210181e10140c8142d000c14103149071756985c810a01c80c003440c0e0f801c0041e20740303541d01d8030740d0705d0b105165801c10b805004100c244018002e41c220960701c081030070300e40d001d110b55052208913503070301c40b922a0f194000c1c0e0060307024807526203845a1070130312503009101600f800719905c0030000320ba2081c0490a6521019405d110803420230f4090001000b400036002c6003000d14680104c0c9151146d8140c1d0150700d5592207900d0703400d40e94200c1c0070044e40400342c00c981e192500c5030240c1c0882c00d12090300c4803800e0521412a41c051401140360402d9820700d0709064241181caa00540d0503507003c01040205080c00e0150703519000780200003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 269488210 1250 269486960 269486963
    0xc0503030a020315010903030203120615070809030c090702071203051e0a12020301050d03050c011107080d05160c231603060e030f070f08040b0a05030f1807090c0c02030703 76
    0x580d02d003005902060380c004d080c0f83c0c41e814000d00c0e9404002194021082da980f0214400200c0d9540d600c1400051285403406450b05100802003880014405840040c104440003581110174009840040041052040303c001c001a40005000d100034a82041c82c2d40c1ca00c0d210b070030250700b0940ea44100d40b080c02c80b40728408031400c0c030120701a10002d074440c0984403031440c03085007145903504000105040c1143c80348041d00380400010a00d5003a80254090743c0c940f405c01800c00c0d1242d0461500c035090794083c20303003070110070f086c0001304207111011100c80110804031b455074400e0b08401d41d264140c200807040c000d4048514480003105502c42407004120078610402e1103580c490035807404900725071464034100344a82c0180030103032211609400711441c079500300404107460500c40c60001d007148a540c2002d170a07114082900c10030b854021000c0d60150032080000080b40c2c1d9005c05034090303800c840041605a500401003004000c031039034004000c1e58410b2804440c50342581d00464580006c5500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 269489460 1250 269488210 269488231
    0x160f080c0334050607050c10050108060105090906070813020f040507020c040c0e060703050c0703081204021309030c11030f120c2a060d02040306091b1406070b04030c050303 76
    0x401d01c54520044035884624400341031000010752842c3c5405a030f075000103129105004000619a001d0303d41040480348403200c841060040d0f6843d07884460300c0741c0c1c0a21400d801640c042e00841c0004401080103445405699a020110b964040e02c40c0c0035444860741c00d80e004213074903086101644542c02103030310903109070b0010b10003501c40000340401c07074a012841d101007102d1610250307426901c020446a82580501c1c0a98480070b09801d0103040410951004284035000114060300344044c40000c1d10440c000c42d20340c45107a40c122100400e540b0782001c010b000405038410400006c92400100100c502d001d0101e806039030781c00d41081e141c8103401040202140c80030a0716102d1500400250300c00100d00d440c10001d5140000c0484082401c4440c0540314510200d24220000921350640f402190000c3e82402040c00b10b050404202c91a4401d80250710208803001c03c801c4440c086110b520480502151304c0c214a680720803040e5003010300120100b04642c000e400210340200041c42c0140c1c0c5101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 269490710 1250 269489460 269489497
    0x206040609030c1509020f241b1e07060314040f0816050115060c1a040503120a0902090108010c0905130e06040b070e0904030c06020c0109080a050c01050c160f080c03 73
    0x42040d240f04428032188640c1240d85052360050030303250096506141844032545504084801191a241000f601084c138420460200c161410751070861484032121020341e58019201c8100301c00f55040700c400c0704608102c0740041400202c82c6808a40324034050304400e0b0400400905403504140350b000107880680d15102801500e9407518050070041c011402c2c400d65103040c030b03074480c0c1d0560000700d40750080144601c00203062020a000300c2d5a280da020402c0c03aa01d203401e0409900500701014264044d0780104004540d1070070510030f040c1650302d29115001054580f000b000484c080600219000c2a1038071014845a041000082d000302c1c4034581c0d01100d4600306100510350074103064107078440c0d84201e05010110350050700c1000405d07000075000d40d4445800a005001d000c860100402400b0300045041d00190f120300a4a01b00c00d030103000782708035101c20151280c1800b489280d01c0b1400303c601c0304400000c81544184a0740c5200d41c14040c244401c900e10503046030410804c8420b040b0011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 269491960 1250 269490710 269490713
    0x70c0b0a170f010608130311070b1902160506070c0902040b04150206010e0703020a02251a0f09040c141c0c11060103110a0f1d01060f0206040609030c1509 68
    0x30141e54000c540500d845615850004003c1039208081c02030042c09005040c003000b8148034101501c5451284401c8aa10a698806480c583c2d444800c000c00654043e1140f040103a1001c68000341c0c0440307080c4080c099500300710420545a00000040b03808611140380050490300c00d00213000140000480c1c103448502d0880c596407400c111000ca0021034105200500c210044036040681014562400513160621000181d03d00050035049070600c80900c061198440380c40000a010b07540e9002402d2840d00003102440c03018000d41003612070405051121100605159006079111040303403038200c003d1329003d8500041a404403189001101c143d4100400804203401012030313101c5645481c0c8414060f4000f400c1c3c464006000003884d55000700c10548160b9200d0f5021405040340d1800e001d03550380d880320040c3c0c01c29011402982a40c0138440009115030050009000300b607526006441c044e595031b035890005204408046086c0204103c90102003407120407510510b6407500710004d10742070030313 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 269493210 1250 269491960 269491997
    0x928030501110a1b02040209032b0f0c080a051b0705030d05030712050c09180108120c0303070806030709020a0305070207050a051008220506010f09090b0c070c0b0a 72
    0xd000d80b200d4852080156240c0584d029000c50703440303d64010f019207000203a10001c0c0181c803580b0304075541440741c4045506100c100a81120300710410070410100400d070b04d00107954160150310048041401002d03070078041703400e00c0001e00030204503160a42c5070101c590b08103035046c000803101e04034591112000b48114142000a82c0d1038002c0360a102c2e081d0314080303100810b4003501c5803075500810b485102003100c07903540e1015543c4101d402801260b01024062910441c81024843c510083c0b107100c4521904148017412504460300b0030001d10318554460509541094000d05000d400d84260000050703e08884d10242024142640e0040341c68142900000d20700b0f42250030281c4141d0560b03134100201d503115042c1c0040700341caa04003120345942d000004c500501c0001c101618400240500c0b60400c03c0206025050325001442001d1854890080d01c04580140000402e800d140c1004501002182c801500e500e074407807405070041c55100c1c80c1c0a911500440c0780d08000c114240e400300e040020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 269494460 1250 269493210 269493221
    0x5010b070b0c030c031501090305010507051e03012142050105011b03050f030f0420061213020307030b07030f1802010e1809100506030606030a080928030501 69
    0x40694449055041191404504d40f1015000d07148071180780d8040c5000f03901410700c3c0c80c02150000700030051071070030703002c0600542c0c01161600031f0310800380300e45c000c0d0303030b002105a0781a03460502007403903020f140c0b595041d103003080306000390362001030440c8079150205020001105021192152082c007959001c100d24140e800f04160000c071414480140101e1340c1c01107400700046040c02e01100704040909050302c1e0707407013840c4e5170007d81c59002003004200b000e2550018012071081034100c0f42100300d030f070307003a000407003880304c8140d218108200405810200c44292604200ea1800c468000c1c91590300080c50b14031161b00855070fa0b10800e0402850542510034031000c21144076041c030101301d980d0305010709040103410081c10312103200124401521103468032203140d603120500307803400d0604650999542540c0c81c0344500c50707800c00c0001042420081101070207010041c0051007810050381e510301803070300400c07901f50b080051b081286464081d03020b400303010840301040307001c0082e04500b0252b00b55103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 269495710 1250 269494460 269494471
    0xb1507051b04140c1308031306020f030a1b151a01020c0a0602060426040e0105150f0a03110903012f040303020d0c02010207090504060b1e13020d020d05010b070b 71
    0x52501141e04070404480c43d00380c0d130041107406099510301d8286910840c80000b0b0b084164503100110b103601c01c8490f0086030505403107042e008c48508094100a09a691207005206000940d100484c0e11490813503250343c00300e81c2d01c504401e0950544038a51041240c1c010b404115505803900035040b003e5805004802d90703d0419504244070604220010f0740e20a4040c01c02850180a4010032024030402680541019408001d50741e0f02c1e5900c40d000c0c00c08039020f00074144038030000c130740300010415454103c800c0700c9500d000c10307414107035900000da00516880d0b02607034200c0010821803015035400e100c0e5000820080009040a80b05510034041c840350441070652000d5003040107201207030300000d4207915068a860402c0b210185880101d0030035565901c250806070410040c00204240303600000c9040c401a81c0e00d448441c10400310824840c90007050719040050244103201a5107190000c00c142c0808000240c50525480048412100264004560002e000c11b02c5010000c84084594100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 269496960 1250 269495710 269495719
    0x50c0301050d03110115030507140618010503040309030c080d03200723011b030e010b010806130902090c03041719050307170108060702240a0b1507051b 67
    0x1507040c00e0110700703081204100a4140007a1440c1007111070704c00d4010b00c0c0c1a1115040c182c42d00b50303407460305540e260194016824104842e0081c601a41014010f9400c0d910403c01d6030f0020300005001500c0c990700c080c10030780c01c000c4140d5010010800050f0440c004000c018002d0411801520b0010f0444001c030089490507a0140c28a000260442c001e5a84103900081d040503030500d0000c01c001d02c80f15100d8001400d50a00e248469481168011031700403800948083c040540d440600d2400c07650707a00500d0340402e9402d80496160b00704180885c811070003010001410700013580005403502c0084030404c40040d000000c0004202c04003c40707030b42c4500840b600909050140d8841d004c141c204d99606c20400c032020001400c4684144051030310200c0b00c04510843d540c6459005881d0102101c040d00948100507000050b07008958201c1440140c5650302403130760b111904d2500183c510b01c24402d80c085035882c402c0f261201c1c2e050040841d076201c2c1e0024640c1d03200344a600d07000c0c2e0b01041c900c136118 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 269498210 1250 269496960 269496967
    0x4061101020702062a0f0318010c0b07110f19170f0906181306030201090f0e010b0d0b090f1015170406060f060513090501060c0312140c0904050c 64
    0x40e240e60b0191349502031070072525183e542e6610031716000e02d190424010510b1240000c809001c80c0c010000f400040203a48604454130f41c000f00564030102d40760b40003045002414005840c0712b10541e0800c0010718900103803641300311b40201d80c0b40340c01c0e01903203011a50003000c3c44020800140c200004030a60306104240e0078040c2405203808030340101b502c024007034000058000744220104074004500000102510080c00d40919104018046404103e02140000d000455007548204440d01202c420140ca00002c0cac0c2020110034180d080326410071b00e0207840c2d00d1902003d903240300049101300c006244608840c60a0221b1740c00407007650340300344050882e04036000d6803540e00400c0a0403400340c3e8024603405441703503e00f0000501d0258040c0c030301a04039200c0800e445a010780107141404a00b0302c542c10f0152120b4490003255400c0c8542c50100d0103880c48480080e0040300d0000d43e41241700c10028940745041e007410320f85001298500c505910003d40240d0524180c856103410411030001c550a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 269499460 1250 269498210 269498213
    0x3100c1b300c06021309020403050a05010b060c031b030409110a031a1e0d0210050d14060a0510030906020424030b010e011b020d120206010819030311120408040611010207 75
    0x2a00e202d4040600301d03680010b40b4040c580c5044481c40d005103203206045541d1642e07424425140c03800070404030340b25400d00c3c600501a1400b00103689004904202440c5811150301070026450302401a090050006200004a01c0f02c0c0d8070401c00e40301034841c0c0356030740c4192a00300182120300c00f0b0203101040029080142d8140c484250803001d03407086c5c0021040342d492802c0001c00c2e104500350000c0d480304c1801c055180c05603001c1d010306141100e0b10418000c1e0403d178851002450340407034540340c00c242e205104005918101480e0000d81c481c7e410002800309080d142c10003640d019170031800241f0b0040c00745560541e81080ca810000c07000c1d140c1004041e100301c00003008100201c4909042110400d5045410400052204012580205075a00260b60340c075110200101d1016a4805405401c00005800c03101040d003055644a40c003652140400b588e6041d4004c0001d0565101c88440501c054810085042070300c80c095400782401c40c5e11246405802004680141d4142d00d469005121610 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 269500710 1250 269499460 269499467
    0x702120406050325021605060712030b060705060112020a1d0a050711030d05010333020703110105070207030506090304062a12030510090b03100c1b30 66
    0x1416030307225282099507602c4644101000350880c010407401c00e1050100c000c513064000a124502038401032200c1011581c2d203013006058021180d01030000d103081450010b22500c241c2c401e403e110001007116080010f00e0700d61a00e800800d07007180010100d410400025880c12409440007415401000040380c02c0b6040e00c0507155401411100c1516110004514454000d000c00781c8101140341c12a5100c0850b00070b0040034250a100a8800c1c0f032a99041d050080d2501781d10704007a40042d8502c144007803042d03c40034002c1d405a50280e0402c641180740711030302d210038041c06002d07551a0740241802811405c11301d0902c400034000240aa104101c00c008042e0040d60f094007800603061608000241000c84140114141c0b02c010544030010b80400859509036210302d00400d401c1000488041e00d6807825030440d03408900c00d41e41580200c09581c20384000c0d80198004c1891031a02040078100c181c40d45241d1469080304450000041d00141200c48482a91071b040c0c1980000b0f14030b24800c1c10390041c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 269501960 1250 269500710 269500717
    0x1e0e0a1e0b060903100203060406050607020102071509051020010e070302190b1b0c01030b06090f0307180b040f3305030a0f050c0306040215090d05010c080708070212 73
    0x115042901d03840c00501594690090714605800601920070003820005403c4c002c3d401254018800c514100c408a11420411b05840e6600d40c180c008054003420007503481078038130b0030a000c0d600b00b1031055800b0031306444a10702c1c07810000d1070380c4600310040c00c2c50f9401c00c000c2c600b4070b0801c2210381c501040d540c410040015688120380e0141d0310f2101d00c0d010341001c20300007005c5400802407611300180405c0a80311081104e00590786502c2610140002d0f10011020754050240e004c1c1c0c00780c0248130100451030174500e0a0a41e10000b011601015504e07210708016151103808400e449648000c41101c6003803d005e0550088088241004800b0622500416041380d40703e03000210240c0005144107607001e4408500a04001030450340c0313480306d0745081200b810f803140c8100d6071030180802030b40c42d030b00300080c4e218001ca84c0101011142d01104540c46041e0b0032041030250f06c528640c0e641c102040080c4160b101c0300c52644e03034602c42c5182070003016001500241c181000c55015030074180032051110b054 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 269503210 1250 269501960 269502011
    0x90a0f0528090c1b1a0f0417031510020303061311030708040305041e0603060b0a0206070f030902040906090c08060c12041109090601060f050a050904020d061e0e0a 72
    0x1d403001c0c510b1044540459407400c08400720712044440e018020342000071005c03032260069040342076642221a108201c0180c50080c01075913042045162048010082c41e40f02d000310140e20000400080000d12003000324407401e015820001c01c2c000b15040a610b00011540741140500048003205c0d800580d900c40289000704000044002c2000c0610a800725801000c101c11705249a107402c07821030705001c00038030400c00840c0c50401c00192181d0180285c81040442e81c01804041d91100c2c025204000189120410180d81b01070381710059866108400354a8003441c0005852485031800340c20009035078020301c0c86940844100b010600c891421900b407174a07101e50301000c0d5159841c05c00e80c4503182d2900680d201d5200000c01c80401c03000a0311078100c620640e1001c83e06409401e00740c030b0768400c10b203a080016404000c5900b09003415001171600601030000010255030f0b580c440404886210503854a002095504000c040f01c07080748141c112030341050410110040038030450708020301009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 269504460 1250 269503210 269503229
    0x70c0b01150309080301090219030e0c010c02042d06050f0a090e0102160807021305130f080f041e0603140402040504030e0910080616091a090a0f0528 66
    0x29070758003680c801d401807181c150b400a8075a4495844450b0030000c1d400145088500c0301e5201e941400091080c09030030b2003407034200302074050510884011624080a1142680c00945504030a1b024219140c441800301c01c8000b1036030102c20001181106560103644414401c004044074103080c0d650300240e08040350700113200000d903000c10340c82140c064007030600d0002c4103080e51850365080c0040b00e002000060720889403604660304164826003203440c196010303140043e882c6c0c3d0302c2d00004c40d1a20020107450103101d002d0300304040c00c900208030740e0003604801c02e01101c5642807007050280d19141006000b00d41028459070303081314460400280e000b000039106586400c041400c1c14050490707607441d260090104201c61600c650031101d4000144500301e43c9100b8140040c010002810488401020319030764900d81c079150103150360f4a0480386006040c0b54038204502e150350303628000c00400400b43c5401308440c817840c241c200030703881c094880c03400700340c502d8581c540b00c501000401c0300b0251810040c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 269505710 1250 269504460 269504489
    0x9060705010917030103020f150a1103090301060803120708010602120d020d0f1508030f2a0a0308010905010602060405100507020c090103050a0b070f0801060305280c0206070c0b01 79
    0x103080740500707100a0068040304102e440280c0308038595000b58107aa00990b042c085000c501800d00c101c0340200226581d06000900c0800c01407445004403400c00c940000449040c03501d4075000a084419992100c0041da000144a4800031004482150f002099082100e00c541c03400c00c01a45580780c503c1c40312180c50000550f00e0301484203038151000c088410340308000c400c1154040c40c00a02e00c0e850391a045d0850b600c80000d401a00104035149442c481d81080c0c2131a4404441034070700510915400300707900c45003000110341d4400304251101140603913103c9810354034209000c01203902c1070304800215005507042001060703000030340e4006c1e036280950000e0641d50b0034008908080b40c1454290b801811600008103022000410802039402482d600f80d0644070400c003528407481400c4d01c0e40c003294a603001004000d000703611940d4403100c2c00004814505443c2005807960085003140da207569641c91203c1081503040065560081032420f010b00ca0f041552128010702d40144500703850a48202d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 269506960 1250 269505710 269505713
    0xc030c0f0804170d031503080d11070803040803070e0a050f010c051c050c0705040b0a0311220212150d0b060f04020f0d0b041a040506040e101d06040305090607 70
    0x2070701201d00800642c601d00c080c1010742c1803402c1d200c65080c0385040000f03007081091608445071101d02c0040340da016074107903d050940b00c9041c000d849200341c480c0882c8024400030b03000c901004000d502c034034444c1d0985139403460007a0010340540a041140360080402040c00d110545a41c114511001c409003032250381e00c0e400e85403da2800c6102c12242041e1200701c4500c500c4160404060000d92003004166000344c2e40300c81c00c5c80201d440e251030346944450311368000c00200700c0c0d42c0300744510500c025043c0000c80400403000c0c402420041c856101c040c0c1c0c0000d5008004481c101d040c1d07001a4190350200250b0044000a9003124139500301500492241020481e41e43d10b268064401c0100508299107400c40b1590a258a0b000958803500480c1410030200344c2d0b2234203100304040c450080c86170b032045c0c044200c01d0100070b14009045580055a9100000051000300039601d0000030070715004c80d00807003002c4040400c849688412140e68041024400060382040545000c0c1000761000d640380d0000f07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 269508210 1250 269506960 269506973
    0x10b090a1d0d02070303120c08040f08191706040905121810050307110606010906030513380c0403030f02101e05060607111908010501080106080d0c030c0f 68
    0x40c0411a01c10320800d003000c55040d40126030842101e000f070300c90500f580d4001e1110010358104100401c00112500001000203d40402c41203040d03004440761820000000901c1500c03501141e14000490940304442c15005907022041e40c0c02841500c0c14403d00344590340f1280d580c200a50b40c1b8002800101d26004d04d000d0b1802c1e13180c03d170700c1d00500c6600005540300b00a0a03d41c026038000000030710080007a41c0b020000200c090003002e06a45a28103030746064011401000301609000e100d018400c07116020030200d60840007049140ca9000c5491040c80014040812002002c3c80c0028036034070800c445401e001c410b0b0b8088030f4140c01c00c0c0c202400140c00490404000410f00e4410615180206001c00c0c00905098a482d030208070810540d1115010072096018a203c02008030b808062000c0d41400e200ba680c203002c10303140700c80da0580ca440b40d40060a4680917042022641e5440d4010001032404001081d1422000c1c148800b03108155100240107403c2d650001d0010200020641c0400c81d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 269509460 1250 269508210 269508251
    0x2073509060906040b0d0e06010305060a050406141e0106020d08150a05030303040804030c0f03050d03110f040905150402090a0909031b23030301080705010c02030a020d080417010b090a 81
    0x40140348550343c0c3d840c0c0c0740031425074201c4040c1e404074500e000c3c11fa011040300042e030203040c1d030f40007001401180c0d82c0645260180c840200300710f400e80d44036800c88410034042943e0328040c1a1020b070086041480d4004486440030580c007130011907000800c00403500340c11058054100c009451000d00d02d912140101c0d1900496900803a0184030000410046c08020070250007520300c0740811401d925070b00c3c0050b0441c2c10b01c40c000a07040e42c0080c1860344d101402680048040144050606d0a20406001d00b2141d40c000e54040d5200035140c1d401c00c4014000d0f8510101404012102141003400320f2002c524050700301d01503c00f50603502c40c0c407582403501a010550111004103141e846a078898a0320085800c1e40748201d0b02101800c1c0541d1009801c08410780c0e058580810041c0342c540d18101c011664000803800c02c2c0e816004911201c005602c828091509690151003860b680390329000301c5070100340c0220108202030749402d425034005e83d0344409490300100850000708441607004060101d500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 269510710 1250 269509460 269509477
    0x1150f0b220308070501051303050306040b040603021003020703020601050d080f030709030f120807030c0503070e120304091407030902010507060b01110615101e2d030207350906 78
    0x50350141c0001005502c000904e4000d1040c40207220350307140d5452200025208000c01408110144002409824140c0c054240c50710001e20103d206503594001c54003241d00161540c00094001070560300340740d0100120382c0104819954200500305a440b020740320701400185951442000001c1241c15216141c0d420203190845070140116040c6d183c00094040c82070600000306481c00000707540180248920710b0300d00680d449041c0307103a44201085030745812184055904c020014031070030fa442801c00242000d00116400000e0602c4280c2c82c62440c024000e10345420182001320000050343e1140c04e64500e542e10200118000403020f0069400340c201c00030603041c0c0c0c440e0004105076116140c071040404041500d543c458500414400c68070345500d0180c54030010a81c15002580b240715a041c442914112883d903143ca00308091500e2041450483d5200043d07000708018082c0120b062400903080484800045501c16a030915500030b80a481e0b038204480c0301081b01181c64503843c00f21050b0f02c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 269511960 1250 269510710 269510767
    0x80103020312030c0c030310050a0e0f04060c03090516050f0909070306021b0a0b01030219050a1202011b060b09011d0601030903031d070f05040519020d060f0e040501150f0b 76
    0x28500704c808c00941d10303000d1203214030a00b90002c00007110700c01000e185000360120504030406a03a191201d0010300f80d5281319404150b90780017541b02080341800340303407400100e0759165680c01d440c110400c0f91038502030b01d4a40c8201d851a061000d03844002501104807a0300c00c00140e02c1e940180c1c10340700d0401100c00c00100364010745100034100004103071018140da00c2160070002c11400421311283c000002e00405412044040c414040061100d501225040c41454800c810201b13002d00002c84909662007100d440380c03030b407001031514940f00400e84d01520711503a5281c4035146035008075043d0600641141d05040e610f808072400d141c8a508110540412110420441c1c2444c1109603901c001c68401c48120740b002e1180880c4c98039040c06804d01481515071314500414419640d98029400740d0251100710f907903032100060141041540c44010500885400d55524080c2811403d40d0120a031a481c0b401e407102040c0941c50440ba0f00405841f03004a50a44800040d603101c540d40441c664921000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 269513210 1250 269511960 269511967
    0x80703110c060405010f11041413110c0c0f012007081b03061821070204050408071b03031e050424090803190c11100206060f01080103020312030c0c03 66
    0x1d1070710001c2e030940641d106400800c030b1101d0041c200011564244034103400d08800300802c0080071403a801400a5000c001c3c108482e0005039020b0600303d92249a28150141000c648020502c200340000d02c0d0108003a18000810700c00000020229100d0721801a00da468142d514084100100b100c00301800c0104100c61064625501142c40c00c00031904c8a4800e102d180009100b24107594504140c03000700d08000c00d001007003428811001c00600100210041090040f840960340740d0294602490040c0c0b405a6030700b605080c1101c05280c82e030001084070b2503500e001c000183c0c0c40700d00c1010402d440924148032098024040f80da510640d80a46144003481100712120f02c1d500c82e401101404589030041c10319903a1000c20380340e0060007201c84002d5190091406064062590400ac03980301301c4920554400700700001d954104a840c400b40140d020340c041001c2400d04401d02030f407101c42420f00102640c5141e00003551004010411040501c0100108240d815140d069544501e5108250f0340c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 269514460 1250 269513210 269513227
    0x10905010b040c0912081c090f110603040b07030e1009120806012c01030905030703020106032a0506070501141320060a0e190e010509090609030a08070311 68
    0xe42030303001076244030318030380203103a10f0070b80c010100c031401c49404101c400389403121030f2500741146e0003000700044483ea030101103446c1d40c1080d03c502d58425201c0d07545401040c0352410080d941242ca03007040c0e8042c10040082c0800700380c01d500c10342e070b0041a5103404101c03599054586414202c8a50b030b030b011140e007491400000c004c4c011300482c44c0d49019540d0003c80c0d9850a004640b07130300c1061031842620701503000341c441c01440c25102014803c4103050104403407441b542e5640c07860f8000b0300e041c1d0043c1d66030348062041240d203074400d400305421102c548c0c1c0360040c540d4009602c01406d00c94a40720302da0000744101041020342194090700324903142e032309051418100026000c00c5110080303070700445400401016040072590310782844006401d007400c0000c585401d40f800340100074200d82c02110a0b0360030001c0740c00303002040060002004945a02d500d0301c2c00340820514050082905138020104002c1c042000000361100d440c01883c02d01d0709600c07100301c103400030103489140300950a400a089ea8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 269515710 1250 269514460 269514463
    0x1e09120c060609060102010203401209050a080d0302130b03010611060c030f0c0d061503020702030c100c02130e0d030518060f1303051605010c1e05040504021605010905 74
    0x5120702c0741564405000e42d18580124200e00c000c98401c5800b0446910303003840a40a00e00c084800c1c0360b007022a0a401071914400e28000710100c004881e01c54540e10410500750b0f01030140380c0100411360ba003246030b07410f054525171151a5034600d10100b5501044c00c21590240b6038190008015a82240340d513540c440d40010a08901034400540501c103810100304003200c51400c8038890a41310758076407400d8a40032252201e030f43c402c100c00708589864210100c3c50309648a1340e208030030200c2e1001651000e641c8107060510ba0056030080c883c10b01d9080c110700081c0c01c41d022407a000d9040380d00002441c0441c010344001c000c103003001001446031500006e1455050f03801a4041d001c3c000080c040d031401f4100c52559001c08a0344061240aa039021a2000520501c08003003c0d01c01e040c0f01d418481c428410781043e4412020036226a9101d4400c5401c80345c21680c1e0003500703c18003441c1407000b401e454005c0c0442c80f60748640b9015550000e401d0b106030000071100384032554084003e0198032040d0074006d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 269516960 1250 269515710 269515723
    0x2402071406040f140a0f0f05010806031606030e1002040b04091509060605130e1b1605011104170304060c2301020304061e1808130807080a06060e1e09120c 68
    0x14051080c0031740118000c2c40003140d04007104d40c1848500c03003c1c0e0400d0011140140041c0201c0d415118004003402e1403110748a412000c2c2030305031303800906032540303180b000e15004000a00c1400d091040200f84540304c9500202c0d02914003001001c543e01d05d070403c580b1685052075006005462070210081030540d801002018409003554410440b036071504040c0320680300903140d816060354034641300318200c60b41c0c9014080510070035001040881039607c559094500c072502284103541d0000301405000103a00e480d500c0041441e0046003014104203000d80300403801040680b44040001c800d9524900a40e0005440d41d000b400035034030b9007098504003014202140b01c07202c00080348800c0e110140301078420400e4404c541d1a215540b0005034407180e1156024031100503410841080105d107406003006000c000b044d00c030005004030700c050705010b011501d698121442503c81e1a00741304082803e486c0c000c103000d17600400c800c100c2d03c400c0e00717541c500035082001c0b00419801103450b019000c00401c18 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 269518210 1250 269516960 269516999
    0x7080106051504210c0b0c0c04050708091e0307140102030601030e030901020a0212070506040e0f0108010b09060909011e020703020f060c2502040203040b012402071406040f 76
    0x5400300d15a40307034020b4002d400759019240040c650000000c4604a24440080403203005d40f00d06400181c44150816035030703108020901259216030004641c40c241031080c0c2d0b038018450324180405040405103252a420b4072482040494855852861401002e00c1100e00c400e03404018680030360055500c480c080d4104030f84a502180c0307403007030a0900c5040441180d5a28205a001c1c2501c06031b19402c001006a01c40a00c01040c4a01400441c098689c00c0050002e007011110360700b283e2600384040c030140d440503002410030341d04018008115071502c0f1043e54007e00c00b140c4000c440d9079145000d40c010311201d641c2042483c0150901402c0c1051a4018250302c0c0c0240d0035541c1040404040c541d4a00c001d4608a00c041410042b20f4116400d115207500c60441030600b101c060009600000c099800c03e03207080e20f24004280040248644c0031000c082c0104c10041074946001c800c0f00040c0d142c40c030500c00c1c0d4a0034000252082c001c2c7d50f0325000c0790041c0400041702010162900341c5907141400366800d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 269519460 1250 269518210 269518219
    0x90a150206060a080d0f120908040e01080a020306060f010e03060c1932041d010e0108010912030e0703021305041b030c0b090a120b071d2d030708010605 67
    0x1082c2c15080800604050340c51100003444090007a040482c1e0055503007125408000c1000c4455103000d44601842030414020f90201d0380b264140922807000e0881a0700846140e407101070341030b005807004103481d41d10400454019100c01c2240006868050ba170424007036050098404002103288c2d030704090640c444009032101e04461280500380c4804800700725403008805401a10811402641c0c0f42486200c010f22283d41410f980b81825400c141c8075504000d0341581410062290040903200c040c014104c5900034854012991034909048110392a00c604041c1c8407440304803010400c104a070000c2d45d010300144031410031000d500d401040151422115410034050340340d07000a0000e0b200c0c090766000440b4019072803a0140a100680c0540c541507000311300464002040500c949014441d03d0094040040d11318045000600c441c0030754420a4140308148165601a143c048658600701e8008130307403040c41500c4509403a90005038400b4150300d0711901c1c4000c28010700c19085801203413020744 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 269520710 1250 269519460 269519473
    0x3050606060703080c0c1c020d0f14070b0a060810090c080d0909200c1b0105040b16060e0604030c0606060c0b190609020d140a020711060c0102090a1502 67
    0x2400c02070310380314255024000442c0c51010481c0020008010300410740c008080311140b9062110015800864007000d10158101c5900803034003a4100308240100981454201740602c0c407940c041c1c1c01c0d80900b02c80a0219070003d00000d0758240258400806800502c0031940b042e4985411740015042c1c00004498071010b034900001e52030310000e244401814151510300c906410b01a0000092000c009582c00304036031003801403882c005001c024660380382000c010709268210f07441034039504044d20100b030381046000c01041111045480a50714041d1409041414002c13043c104003014001601c04a0498018481407004145e088000f018186110324024440c45543d1102662070408454014018103024000504981e4200101411021041400060094031040813400b2a003207200b000c00640c0e540c601c0b03103030380ca1840700d290f070790200e0000802e62402c3c032540d45040c091070703121101ca4050700c0080303123480d007480007034041d00c60041c03002c1c003100c00417690b99140d01025008161000b0141c0104c9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 269521960 1250 269520710 269520721
    0x14060a200702010806090405101a12070e070c05010605031009050f06160f110609010f15081e030409020f0706051e0103021c060e0105060306070f020c10050c03070606030506 76
    0x410554405540584400406655000500241080007001101c841c081e904d503134644c03c00e15102e4032b00301c0e810360390030440c1c1d403800c0f20701344844030a02c0c4007000b025500001c404c00c01d14054255842d441076051038418040222031410b240500a00c1d04290f80c18011885507a070015134640c46510940d00900854404042c41c0003050344814042d58004030400445a895202c507005410406e08400507286c003030032900c0140300960134a1000e481e100c41c00c4c2d44407918200740c0703132043c010f920802c403001c1d910030f000320b281c0f160b00d560b5540c01030044040c8801441c9000e070340030f000b1b02c00d580050002902c1590703100304104404c81e9075405003004075441c80c03405001c02d800700070f00d16140c0b02064410407440010790847d0204611245136010746040081d80300481e900258050243c803041e4040d0b40d0000c250380c28440101400c28800420b00e5041111038608040d046230700003440082a4002d550441d014105c418040f10180306a144d0b441051000246541c100280f580c44001140d00840030b980554840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 269523210 1250 269521960 269522021
    0x306020c0c1c0b06010c0206040509071101050601180306050c090d030512010e0f1513020c070305060610020d0305060324060a0501030b060702090a15030b010f050a1d0414060a 77
    0x341c0003d0030b401c1da158009445540100041d103404ca000912003414265244002034500304112002c00000704804a02d620380a401d0003038a0300f00509007441000d00000329501d5010020300d200141c10b680d00c400101c4c4020b880d1000301c030401080540305218020481c01d024103540c3c80444440c01c510240c0303000180341c5030148800c80c040c131408900301030181c81e0591030320215552040320390391100b0700781c41e1035062407d1480140a098900c40141c00000d15500f0210708104000305090700034040b85983e0003980d50702080c2442604080c3c01c0005a98a509004ca8542608124130790780c04400a42e402942140c40b44019101f080c0446100307202a0311800110191020122247c1c2c00c60801c0c010400145000000c0030360000d0310000004040400d0320040761f4019040c0d00940d410681c15005011209000002801074402a602e4074156840d02403811081200a1130380d00100c85890080303001c10410302c0260100c08800402c44da0702e41481d42501c0001c090b80300c407040e91182d040d200b29150303142 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 269524460 1250 269523210 269523259
    0xb010f060801050f010e0604060903021914130b06030a29030d0507020d08030f041502030402061812071502012301060305040c030c0b030403080603060402030d180306020c0c 76
    0x907a28801d20340d1038901400140c000700301d9182e051200f40700c60300f02c0d2138540c54041e00003402c4c15a0f03004061850740c014000c9010004d9002111540a400184501d40c00440c401849000030384d0a44890403080110324000c5c03e08400944d4804000402d1100c0100c954111700c416240030401724001a00c441c3c41175603803020304e40c000c42d0150000c51141885600070005840d066002600840808865030b4070710342241d10403108a119401210300340b10500c28002150104078800030021803039400c142d00050700d240152070b158440a200514240e0b0282c686041e2a40552803410444034040c1c0c450424080c1c0000b054546801503181032021300804407100d90303240b2820340368940300c0c3c8140d0800a040740038100c0240103440c0c40c642c0b5000000003c0d85c08000e00010498500026180d0406260003420b1000241031544a98000020f01000d17030307404560883d4141d07440c00d0006200340d88071101c00305610340d9440509610710114101c9024400400c040f01ca85108990010b00540c283c140c0521406 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 269525710 1250 269524460 269524469
    0xc0b09010e0c15220e0105010203041a0f0706020c0109020913030507140106170c13060e150f04090311211b0705040f0f0506040b0d060b0d05190b010f 66
    0x14805115005942405800100c84100b5006100e141ca16a1021801000344c0400070141003a20300c2820040c200f00c4164981c09420244080d40c0b80c40e117409580c9500d940d11240100b404140025011402640701d802c40310aa94451010364070f031f14000c968107000302500c02050340145480c4000400741094801c1300050300e07a1545509003014100c0e102e01140c10b0034a00000300641d65944042801e92603a00003090303d0840b2001804250b01040512403a1089202c50115550412800740203080d50b100410f94056514244000c054108800060b030100d108007100d40c2181c9005195000c0c16803140c003941c420b04410040740e140400200d00030b600c000380c001c18600120020302882c8081080700402c4400505c01008072003600307803070b180001e040380d440302441d000e41030b82c9002030a03000429000701988800201d0701000a034400801048204132144002003440e0f5590710941c03001d5858580e128042038101c03085032900d5054403c3d00c0461025200d05503180400d1200005c3c5d21121100c0340030688 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 269526960 1250 269525710 269525713
    0x60106020616082a0a030f0603080a0507050703060f150b090907080411150904050618070e01090f080c09090d020a0f0f140d030606080402060304020913120c0b09010e 73
    0x2618841c02c12a0000030103000156108401d500350080c900000a0b001a08401c480000b90ba40c00030384c101804a40b10381080c6c01040d81041d000704007181382907082c1ca40302229401c000707030f8131442441c09605005003904014501490000d243d01903104951015031040b80d110443c0e550746481d1803480685008051850f03a0141c2e4000004804074032a440d115000b40c07140303040c0140c103a04480001c4245030f07a4500c03090081d03404113008000c3e25141c0100c40d004036069881c3c6260008503101907981c030341d0041c4010b00303100030250a041981d10a500c0203009200540c5006031840e21980305541301c01e54080b03414450040d100c00700c0c04844001c00d88044071013040c1c0040c03181a209990b071035103032841c50000b980c08000308007041000c85c070350745003100320700e440d60740980f20320200300c100541140c0e080e8202d0b4041191590030031005803074030402c5a070030030b404480e007400031360749c280442100c46e500c01401030011002c001d80c10f4141e40c21042c922001c42c842c1c0b1801009658540046088464140ba00c003140d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 269528210 1250 269526960 269526991
    0xa0b0702040b0d0f050a031e080103060b120313080d2a020609030f060f0702160b03040c05030a0b06010e0d0f0f0201050c011e0e07150f03060504060b0c0601060206 72
    0x10301c0e0507805241c060034040c003103100403005503e5000d1451910b0742c2c10780b5075420440400082641c0154000203020140a00011280104200803e9a076050100816a5588442c508001d5881c4915000080701100850790b07201040c1c0601e02c00c4468502c07030008035110780d620300b40e142d0380a803060031500b020072910a00c81450090f901c1301e01e0704c0c3ea410181e030000c0c000c2000d152103440912003070080c3d81441c00140540d09140180c02c0e0035010040208046410070040861201042401c039800ca0302581d10507500d9171240d090103c0028402d074003071a4035101e4000700b201006068000b003440344409807201c0d4001542c1d0414011b0003900200024a81321500b00c8107400602e10078080782003180180b403ca0705084e040c400440c2101c4001c00021130054010201a80e0305900340034081c00d80c00340c14050310956140a0010514a03c04c004480c284482c047c01101000d01c45d0344210000c000003032040c03140e260343d15441c80495000041425242c0586400410840d00018a05018020710540d4898 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 269529460 1250 269528210 269528213
    0x90605060d02100509130501120b0f160309050309090f09160f290f1c0b0f090a0906020a270806070c0203030c0a08031f03080304020d1b06020f07050a0b07 68
    0x241342d408080000e62185400b810000e03241018032441d4064101220005460001e9040c030030321076503000341070048410500e810042c60861001007646101c480c0d040c040760b0041e682c0381c010704501a807440503400c58851400c0000e00d00a01a5141c05502c44405a070482c0304281c0364044110714602411102111580040103010310400c4030f07103030100e00420749160861014070012241c1e03008040b000306240021034164851403d16410813915903c01100300b0043c1d02201c04180b0301104241554410b80742400042c4158006800ca500d169034042011556224002d201914a2135542c400c0652040c000d03045400f842c0d260482d020540e031002006000680c0c40460848480281402c1281c06010512030043c0e611000c000c0d69007100d1080101c1d50301d902d8213443c10300d000c00c04c80c640303049400c9410a0410100b81003004580d001034054803440c44901c02400d10140c01c1c00d44518001c1d070b1245055001440a0b07020590141c1d402c009401d6540b00359a81003080b8244016000b1a0181c1908000c210b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 269530710 1250 269529460 269529467
    0x1203010b030a0e0f03040504110c060c0306010c1a0403121a040b0105090a09090b0603070609030f0609050a0f0209010f0509060d0501090203071413020307080a090c0f0801090605060d0210 82
    0x6911241d0042c012070714503031800507a42001c0f03402600c41c2c07059001213400d110b20725040c002d4010500f840040e113800c006041c1d003039560703841703020340507044610001000c145964070944030354840329000301c202c284a000d640d002c0600707450215019800204018484030311072110740245091500495040e81030260454100300043c003c1c628180c1c1400b030108443d1000e503c07050003210080c407202d1800604000d49007032038000a240146071611030340000b0428803c1c0d64100c0c4058080d01d40000d6860195a810f00d0090700411005002401511074040c581007008049620741e8030203442940c4950560f40c1c0c82c00c143c0030700801402a6076000904100060040c10002111318000f0301590011488002c140c02090620005400116042140045039500b6080048280350040ca411200f1072541c80d2090b001800000b001d40424021500c50400b40c0a0150261030f071406807240c1b00f100440700c1d50b1510f900d0300a10071001c00703c8a060078040050340a140c1031030324400807034014049006824140c1800c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 269531960 1250 269530710 269530717
    0x9070e150d0c0206150a0b0f030c0708070506151219060609050c0409060f0b0d090c0302040f0e01050a150510090b0f07060b040b1302070309090f09141203010b 70
    0x2441501810301848402070800d010342c569401964001e00700030f00f450843c103181c1c210750b03440b181d0050280503c200030b00d5002c2c03022618030120030b031151903c07074454140301c8e00c1c284a1120041c08190003c500c1034180035010038401c0c041e031040540e0200340d005000900050100100351040550041c01d040105040c200a280090034171036100000c8107a00c40ba0540c044903130641e0102005e81006c241030080c1c060071322802c8040e003030f001350301201c0c1e51400c0c452103400d00c105602100b40c980c8a10042040241d81e42c101da01555008005000300594644400c00074001c0911075070b60f41d0b0030880802c0d04205d6911409040c4202c0c6503110300104c0c1014244a603089054501d181085411400020b8900012019043c03c03202031031816964011400c00c10145d482c8121000d00c5585040f0a0305000c0d81c4004102c00000f0110401585400003410700741d0300c0031096403001d4609400c2030000d40064106a10200340c1c40e21901881007544c00c064003650391a5004007854141120800051207a8194000074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 269533210 1250 269531960 269531989
    0x11030a0507051609050412031a100302090a060e0a090501050f1203130e16051c0b121002040314070e070e0406121209081f0203040f0f1101030b09070e 66
    0x312a05100b05034031441e28490f0316404048429924000e0208202440b4001d854006142c541441002000110030740d0302d0310b268042c544964a0102d064070700030b019405440084400600403c800e0344d030b030074014041140304120a84520740c103100209681e60640304039030590b50060021340402c0480824840700d03110340780030740c01944800d003c0341e5104c0f8140c00c0c4010190640314291300533070031b101c4007100c6c038010b190070940c00f40402440704042051005180b011300c5510344070003080c5d01c0407200104030300a2182c4c0b100d8049014602d68814403c805800900c100c1c0e2082c1100c0c00e640c144080306507182c18880c080d010410440c2c00106047c02d2080c510b018551200800004070103568502c0400300303944407a001c941030760070b441d4801c0e503003900a070020000307003c9400605050541c0c0d0042070300f40c035110391920039103a0340030001c5000d000c0c040150304030035035100d8007900c81e42242e410600c500c1c0d6942c4d105580000c0c2004074019560808842d068020b0229856500e020f100c18810000c115190544 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 269534460 1250 269533210 269533213
    0x2402040e04050102071106090f0114040b13031b0b070803040516120c090b21010b03010c050403110315130f050303160305060306060a030311010608070b041511030a050705 75
    0x4003140c24401880c0e018001c62041c000140c0d135000916010760b0741c5e19021015482003200f0300115051f501c3c2c51550400114092070030174440043c01c548210386001c1c50b003008a03030400c08602c0040701c00040203400152030150380042245102502001c04400e0203000b000f101c54000c2c0700c5000010405005150094410015145481c0103c0c0c4076040030889503014200c01420000c0c880c0521165246180281440324400d0102102500100d5216144000501200e41c2030700c0a40d40c48000a40c0040f400c80c00040c024000303140c40400c002d24503005030009072003598842d2429a0185400501c1400021040038060200d9461206409031501034400966588401c80d4800c000584240010341c0315558204043e14a1145024010100e50300145094080d17440841800540c2ea542c0a089045070303030601d00103100290035410a0f000d8101a0702c81300d03c40c80390a0010615a8400f0050416251300418142c0c1011082c03070100d468440c902180030f219002000442c0e40d5500c41e00051211300d00035070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 269535710 1250 269534460 269534467
    0x31b0309030d14060906090405120c1606050a020706021c05090d0516180b031b03070b0c0601030b0c130501030203070509060304060e0601060c031b0f0218150d2402 72
    0x20384400a50b60b102d843c0c1400340c0d801c030040016500d04101120380050040d5418000e0345002c0e900c09070b403100032125842e9050300110340c0710381c01042001102e401e07008403030300d140406907100c00140540e0041800807025014070003010038443d01c0018060300307203004403641c26210751402005030b0302e070341c41041001c1e044034260000d000420410005011840b0b0701d9055564005d1901c802c1080d1200e103001d103416102e003802500c0500b0344c1c0004512040700c1c0080800c80c0110007200c0001d00c2d10881d80e0005540550108550007001c03c0440c2e81812240a240401c0003580c030907108000512501f6203402140b442c3c02d5040c03001d5440303540a0b42e807200c01403c29620703080540c1c00049442d00210b074226030054030703180c800808000510590f401041c280c280703030040300c0c9203950207098030005102580c110038080010741c0c00e1180c0e10403038410098001d001e038100b2800411080600d0001103800300480003039202004204d003490a40131001a81103459181c00c28250400007043e1104080d03007a00558003171 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 269536960 1250 269535710 269535727
    0x1050712090801150b0d15150806010e0f0619020106082a0105070816050102040e1303200a0b060d1e0b010506130b092e0207080102031b030903 63
    0x4100a80160155480301031081d86442d060b80e0941e6001d418403038080700c0c8104100012040281515200c049040c0041415058480f0a40854a041d44486501c0880070040c0c45195001241d641c010720007aa07480000221000a00528011446030b1a800c00f030101300000e1031840d22204548011070500c00416450780c0e41000750728107118002c50406958002c0b80d0301034001c0e2a8815009050000e00f0101e0801040e070701e80c94414010069665105980b40c2c03140d0040000a5049034080c2104040d505003500305160500ea1140c544501100810040e601780034001084100603203030302d4070613001443c0500860707640c0c040701c030b9003c1d00c032a4014441c0810307540010101240c0710b4031086a0f0340c46800c0c516550034841351482060b0b0080e8010702003042200440204004140182d4180e441390550f101203c4022038444140700010000f10100e000c03541009000f28034200100780150790845140700e490704191402c0f1301c82520400101260164034030340c0038a8190141d5440401c90080d0381c1006800c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 269538210 1250 269536960 269536973
    0x80403230c15100b0708070606230103050105100f180b071b030819022505040e0613030e1306060216062c0d15050924010b030402010507 60
    0x1031195126000340c0214041e07521400c104481402c02c04405806416401d00910342d00045540b4016032245250000300340e018003c01c2c108450150f60300150800050703039660703201d10320f10f400c90503890840ea00700301c1a03040c2c1e58400e0003454103a03030f00205400d00303180181a040e500000c5280c02c500078000d0803044912f600382c000310003c0003864800d52550751031401e0f00d4042030407071050480c0342e181d00c1c07601400d2010401d501d00f503420007003a003406000710710a00042a4030b002c130342d0308808200081120410002680c0b034448034084039026182030000c440c414040326101c083c201c42072000444141c0d101c0002c0391051300510312109000c1c0000540300d2145a00f2001e46403140c103e840075a110000390910001e604125030000d052600d0604d080032168103802c0350819138040703500020040d040401c1c0069a900102454107580f21064242e1a00003008140151800b19420521130140204001c10300d8116019450b03001c1c1f404550340c6e03941c3e003408880031442e00080c00603410001c1c1405240c0020304c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 269539460 1250 269538210 269538257
    0x1e06120102120f090604030504061d040e0114061507020409080910090e011203020d03050a1508060402030601171903050d0203092d121c0507080a061505040303080403 73
    0x188400300c102c02d450710300300d0062140f40140c41c0c03901ca035011804001c04280e0207003c0d101500c1c13a078a001c0400041296401c43c00a1083c2c0c00035501c01d00c2e000540700320210552003001581200c01b031903001c40c0d589104002e0802000c20304400400d0042200f4001440c080d44099000d034816854181071410840c04112501801401d55020503504041403100300e40c00315500c0d00420040c4803803103000300d055500a48900b078207814401032544900202e20b01200d1900162646081d90306030340191503170744240650b5290f054401307a0207806518008290341040d01360f84910100000c1c020007144000c80312240da0040c0b040e40a404002080c4030301024100540010342c02107030144018494103080780b0074420000503600c060b5140924801c2d910340c10702008907039510558a0307030200c2c0361503030103206402410040319400006000d01e8001046060740d08072403181e005101c001002c000c2a91a0848000307081c0300780d10000040751060000700000703882500724642c014800d241003034104112440640b410003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 269540710 1250 269539460 269539477
    0x30c030a09090f180f21030603031805101d06030f2e060f140a030c08130201020307060b01110717011112040f0f120305010f08061e06120102 62
    0x9140d81010009140c050081e0000607040c200e00b00b0503034000500c5821300c0b81d01044000c00945600c2c00380c0d03040c002c041540c2d80c01c03508000d039401d50144540700001c0040c002ca01040380480c8070301c20b20042200710301e03001405489000c0c04040908041038420740b8005521400079908002c00c00c080e40403900c4900255002d0b42c02c2111400c2d41c0e00300000010b0916003902c2160300d070b00f6041d0041402000304903000308125101c5081ca5546a00301e1041240c08407036030030b10980c00100c00a200104075038554850901d40001e03946141594440318141c81c816647e040c000b90059009214640115101d54440102100c0504204d584001140c030241d05000007944015005880c00b44601ca10744800c1c000c260442540707d600d10703c1c1445515103110618005040989055110322298080020840c1902c80d00d680140d00040038001088008001d40424040d112400c0c000440000380303003400060b042c2c040c0e00303d410318604121840340d10a44221009040e180e001e441038042c812444c80c203100614091 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 269541960 1250 269540710 269540717
    0x2070302010b130207031d01020109060216060e0303190f090203100906060f0f090c020102070206180310050c03070c0c09090614060a03050706111c050706060f180e030c030a 76
    0x2500c28804000f8030020940740a07a10900410210001076402041d11500c10450070408004401d50300040f40140101d03100100440c0c40099402e42d6403210b00e801307881691282c0c0040c00404000444192a8081035230007850300381080709442c2111000350814101a288110001485002d0340c0000345081d1800b03040100480c0d9841c0d0a9007407025030300071078001d000b0444243d002c0300d1905541455150b200d108507583c4564403402e140410340300b90100c60030b45070024110f58907035002100c02d5000a99443d041d512038858008010312088850054512491044d04042d05580d600141540c0d40c0e0300441003107034100fa0356600420b080c600e40c8141e000c003a008900014505004000c903480d0b56002409071071180c0d8082c0701c1000041c0001800400707469151400518810855440740c0c904981034100303c48400b40e260020b03011f0b5500c90050100c0300c1c050f1a05011499494004401030b00580c0168444407003c00a160040c1d001c1d034224101c0c400d41642242d1a19020001c1542541c00c04462040003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 269543210 1250 269541960 269541971
    0xa020a0b0c0601050a06050403110f150309010b0103150915032915060301030206070606090f0f051005010228060501060e0a06090609050103050402030c10020129060304021504090207030201 83
    0x7038410411655025003000e0701c017062941c1c04c00b000603011f4000d610008060403284144c0309a1901c510a601d00381c00c1000c0c004030200b4a500b480c480294008803646c0c90315610300354209241d03611a0280d4146541c03c000d902400e00d0412650b80040d1a401c000c0141203c1580c50001c00520314455004603410000000d044610b542c05070104004c20148c201e00c8000705660760b010280e600e203411607044a0b411100180c0e0785651b40340c0034001d00000d92144446510707124124060340c2d140d4000300c039500b01885040000340d40f16100d41c061007015024003401a441011210180c4007004502c824000d150180d01c1d000015642c1c8a906481098001d807001034102407011080d03041c5280981c003d0811403d0a101c85420144010840f829520070b180c1010340b2400414150f481c14040000c6d0b444010740000c04400301c446c0e020340a442c910210301d61403240d140214035400360341300071098128801804945540c80303540810108480840c20000e031028200000600d0350715920041090034400d8001040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 269544460 1250 269543210 269543227
    0xf030a020f0a1a090f01110405010906210507020c09041101080c0c1b210a0209090a150f02040f0e090105070503090c1003110d05040b09030712110a020a0b 68
    0x4048640c0041000d5a11220040001a0f03611105190700360110540d86803e40d140516185407001d40e850318503555103018800e0301d00078548402401501c00030f0300c515074a1030340c0b003500300c40704102d4806c01d000e4560901d15910481074141c00054200381184101e0700c010103a0b00c0024480c806c00d032004c4a2449074200c10710583c2d604400500d5212101000e06800c026079140d01d0f68451001e04042002600c2d91003021640c4d6440402d4140f0550030b244004034020b020241030340d5141c10718041030b07118040c1140001d0245a001902c81c2201d1391210148424840030740740c0300c1c00f4003007880d4107a292503000c0c4000714a10141407107500007000c0031310721488141090014242140d401401c00f80420004004100e0707054000522030b011404180c0d480d5070291940ea900301d004141c4541446128600096009020362007a00114000e0703000d180070303502c0c0c0d4941d400010341d03e104100c001001100905281340e221070203010f001800d4440e520a0300d6443c00e00ba8001075091314960000005040c002c00d5154 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 269545710 1250 269544460 269544463
    0x521011d01050115110304210c0314072408060d06110703080708040f0209270a03170103050c0108040606050901120b0901050403120c0504090615080c030106050316110f030a02 77
    0x7081c903030700e03410420311a41e041c803401502da100d98000e80d510043c0a1612003002c800101c001c000c140c0d003200a15055074ac980c5007607411490a6040003d00e40701d075160125089807400d0011000c042c0c2c0070f4984070400f005420030350700040020f00199004111880080c04101c09008408686074058005651001249005450380c5400380070038041001803400c11000650740e0780c9c100d1401d50100c070401c05903560004141201d8004051141c80c0750070f5426220302c0c1c00000500d51801314881c0d03c48001281d1500c1028606a00921001e012a40500c88220281d4060b203041c0750894010340780406d47d2a00c2c0c10104814030000c1e803011441ca00b90303c00700018031807405034880e00f111000c03000b800203080075200204401014040d054240e683d4068000e00702e4052001c070b170000c1c52490000c3c080c0b19681c030114810072541110540228101d5400540c5403c8403000b01c0e41a00d4558880e64196202c00d1250707805100008995824410610380d1464541720401194094101c400001c550741ca1904038000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 269546960 1250 269545710 269545739
    0x100203010518040f0314091008090709020f0405040902030304080708070302120d17070e0406260d080417120a0911030a0206030c03060406150504080706090521011d010501 75
    0x21414541c40040c40700284044e000302030b0350754243c940b6480114001010f008079200c2c0c82d8000d40d0160088500704030003500010b1061081c80481d050721641a0748084e9501030303100f514020441554104400c3c0450319082d4072940c8864000340840f41425120880c2d64900211500104030300ea00c00c3e0810030440c40c184280c0c103030210914025043c400c030440c4000e0001c1610320034845c0010030070000154500e10800204025040013841070080d0750362580d0f126800c0f46032100c2e412003062008881808800000390401c0c0b5801d080d5510440da81d00c41d02c4003c0c1300c4d004410aa03101850400c4540e0801c4100718010780284400c801c001031038490341c41c1004000800c03201980c0280c000e40030041c05607450300c0549138400208c4800642c0e0b5500e0b000024018199500521200c940e4a0511105580d02001920035500390208541100d83c4800094400c441c20b48181075100724403085000326295240142480d414080001054000c44003042c02465140c55035028190780d520401004111ba440d03150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 269548210 1250 269546960 269546989
    0x90304091a1309151107060f0605100e0310050c0903070e0c1803100e16050102070f060f0e100e03060a022d0903030d020304030206090609030a1206081002030105 71
    0x1c00058401460115400800456000e5400c641d00d0080000f84481c00340b8031341e924003603210200100080e0041d881c00542045400b901e9262601216078000b842d640301e92420707200c001b040c06119107000f0740222180003210079010f0f0540280c3c0c0070300039081c15500600f4061024001c0359510340c03146030140751401c0000e07445118030002d00010722180020480459020745064070814040d0610312012038602480b094442d80a03902c2c299180f007130480c0104c2e1100f00c081c40151082c3d1155036032001240c0d224035600801148040c0f481c02000460b006440030210b2040d1410410b8854159500180130760106042c0384000c648850300d14001c80c0340c28044a0740c4a0082041181054081206103070303225800040d6100300c207050500c81401c1e4400d8070545036a0341d0000c0440307076550388031813074800a9001030307a0403000b44c882d54020500300400800e80c50300c2141414001c6041c14090f40301205c82e24070401c0969600783e40e800000c549400c0a0003004800174507500056640c2d40b400040c070180c0c011100c00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 269549460 1250 269548210 269548241
    0xc0b090106030803071107050a120c14030c01030507020a12090914090304031212051510030c0e0405060a08070f03031716080a0209041404060b010e0f04110403080309030409 76
    0x18000610f298050b2904442c440c50002c02100d1110982c0e803030120b003604090ba002130712102c005801620340c204c0404107840b0b0041c02c4d44103642d40203164440c01e140003103281d040d00120032481c2c040d4400d622031903006820344103c0d0a07c40103505c4001d174424001c480c540c00156410400c2c4603003402e90285034121555081c5105192820b924060780700d001d140001801108403a10300c6440c984980e06119100c00b40300760070046030030b0400281643e1040d010205006210080000e00c04602074401c41c1c1740c24005407102c103080c951403000c00c0000c100007032140b98880150f070404250b0348400c000040180c00842452380005055081c09445c40104002c0e40007002008c108100f0f041e0022035a44004101605202a03242c4980a03241e01901a51058603000352800f101040044032000459016500412040202c01c03640b000450756048407070640ca40050b01011105001d041c00e510014001c521103000074142501c03640e501c1c00301d0388151000c0c031199002140500a65a45200d000c10f0303003003e0203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 269550710 1250 269549460 269549471
    0x90308090a0c03080a2d200d0c06020d110304020301150f0b28030b010806011404050d020f040903020a140c1003051504020f04031e0b040209070201020c07060c0b0901 73
    0x10340b95081004640401042d0400c00f01c0d003034181074000c80c0100f003000300305402100c0c605024444404c165140e4508007000980500941c1740711080008072255203580d4a01a29804422003003d41e5145001b00084070010b90810104444001d1485800802070419806690700d05042c01058250b40e460800d01081ca030b40d4800400009280c850000e040742c070400c045688901c0f454083c000440c16a02a145034010002421044583e03d50b004c1340b8020826290602c0070340301c1800440b415895050a03c2d8816000c10041c0418a0200303040312000744001c00c0c00303803904490030101d016104030f400b00f02c015034054080c2804020503240403142011581c40184080101c110005e00d180c40d004c2200002d05a4600c041080758a44092942c0d00c4403024000359503e4800443c80320455000d8841030310b900c00626240005e421460180c01c041c540c01090881d001d48842d000c00c005d100c0058a4401507660070043c2c0780c061039041c4204801007106448100e905a03081c104041c10420003800000f4903403410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 269551960 1250 269550710 269550713
    0x19150e030a1101060305340f0b0706090510051b25020d05151603050105130519061d0a050f2403100c020c01110303010b0304080f0d090308090a 63
    0x7a15001c80d0340386425001556203410050040416070800341150003025090401e60501c0207003004032010842007119541042c0901d10a41d4105000d03441c0440d002c0c110820501c1d4074007004d0b01025009440c0000c0501c1c040e641d0900e8002809584407c80e5196010800c507942e10340800c084022034200c0b4186400c2000d2008024000010142441e83d4501c000050940d103400b000b841e4656032010460301e504070034503109880c1c4802110000b0603030b081900a0040300d0710030b001d014102e0300c02a00d034481024050000001030000200407505401200d2454290818940640c400400c246a03101d802c3c1c41c20071150220005000340208900c0c0c0c01c00e4203000a02840f8400ca035030000c9503c240b034811130700c3c0e09802e4280036000a2265814411084d901d1200c2c1c040c0d40c4032840e90390380b41d003c40315040403071001903601e10800c211140c1c041e00b050004002028045004541c0b2034030800f03c552401d040700348141520342100d072116040350b0307441c9502000c05030403441450f0845049001030010a005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 269553210 1250 269551960 269551963
    0x42a03150b09060310121103190803060904051203070903060513230f0f060f07020a0305040e10090212090d08010503071a09060a0216061d011b0519150e 67
    0x70400c106000c1d0f4400800030b2031741039004500702c019001c10301c50726503600c445003006500c0e00000b20341e00c0d100e130103082c2c400c3d40740c41e202c0c1c200400521f42c408440c90171590352108002403203400400c00d40380c034050011510b2105030030400542c85500345460b0701d011181141071003021541c0041c810251031040c0c200000104903034214044404075001c0f2903604804100644606006c2c0e01d10806403d4410041107140280380481c00e03510031f02404600c0161560b80071000c0743c0d41c109003031000d400700704108420300c09007200c0c003145584020380380d5030405401e9030b40700c4000c22039000c0222200c500c2d80c138005120840005214200f01c040c924a0007540c2941050f00184c0c560f1150700c18980e40c40d0960710b8a201c0551060b0a03590742ca540205500e842c0c40b60100b01a489241c016841110684d2240d03001c038005006801440740080d5040100425500c0e800054410740c0202204001c0e4030b580610741c000103403007009410203491900880e070380c0310006440e08200440520381c4d4104001d00b40706000464000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 269554460 1250 269553210 269553217
    0x18060a290102160b120a090305070b1503070303050315012c0d0f14060a090f03200d020309130212040206070c080a0506010e060103090b01060e042a03150b 68
    0x801900005901880340180d00d0302c08400c40071598009240000141d051492001e800c841c41900340c0e0003020340e1402403c004503101d06000601189041c441e00c4081039041d82c13040d50040a10058801c00548600042d150070320951003100000c0d00002000315850700c1d074600000c021030a00f401a0480f050141c1c2c40031801c0003140c0d5041518001030766199554424055010b140e030003801882c41100e00341458808690324446130b84070341c80b45101046210302035215001c0c9050300012040011000c0350b8040340e003180300143e07901c16003496000640f01590305000c08141052241c000710b80d9060701c601440f000914403a50704943d184107200c050005c4007a90b16880d8025412a501c56a90120740340c01e40301c91241c0c4c0c0000d0800d00c20341c80a8000c000000424074141c900e039409010300b40c1e4a5400441c01d90703021500051405c07200d0b200401c450342c010550b1040090b401040131441d480e440d54650440c1e181d104071070a070154007448948505401d80301d481e0741101d180c04200031a038180048003490340b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 269555710 1250 269554460 269554511
    0x10206010b0d0b27060a0e0c0913020d060306050702070b0d0c11031902100e19080c010e01051e0f070e1908100510060f0813050618060a 60
    0x18006809030b07160304603a00044084100510007203120743c8070a400d101402e03259074001480c01c03200011075070030303d03180701c140080701c83ca0507044145d607891103d1204150041d807402d81d000302e440c08005290030340ca400130700b02904002100245282c40d40c184042a41d102505150554000e09814400c240c10b1800301c07030508649440102d0010400c142c21a400c0202c121603c544e03005c08150300015200c0040049420122a4200d60300f0070a485202c108440004000310305aa1040e510494460100644281da190255844900f0044201c0c083c074251070440209401c1655100108a00100500c402194941d000882c00119103040c030000c4444485c05849a01400001007030381c0c1190b9505018401c1480000c40c9450382d840c1e40b1405a5580d290310303c140364600f030074840083c9080c04500100d0048031341d950342e000d40902d068401901c170722101402c0410680c100980b5580801c2c000c1204a010746003c20a6011001e81c8a035803505118000e804441c030f290074045030340e5900c410034106a0310315 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 269556960 1250 269555710 269555729
    0x405070c02091003140a06110906070b070c0803011d0f150d0f05010213090b011d040902040b092a0c06010b0913050a1506050f16080d0504230a0201020601 68
    0x162100101404000f10030707403000b02040c5e10040c50080120000c1045404a84501020b0091440c0144401601d0040c5145981c01142c1400014081000403c030036800090380c1c10a00301c81041902c811b0301c2076000741c020501c1e1050090328040240120450b42d513102e402ca00da100d070a42031044000b40821004a06184100000641c031800c1c40400c010650600364014000c558500841da403840d52890540324401d9140d18207241062154002c3d40f200c8070580c2c2d0004100c603c46d03404010800200030144090760001e5507030139004015101c5140d81802150354503042c1860311002d003180c01a005003a01d140b40e43c00f01c1440000b440324400503409054901000715551644100c00204420803c525201509103040c032042c0180c0c40b07c0c0da40b0002c8a040914251706a041e1500015200c0d071084442003480d0020400503650001030440300a1840d80c86071070340c5032500c40042428415034409903030a80e981c18003004442c0c3d91344d5540210010564188016000c0700c11076400103910350350140700c1c02a14 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 269558210 1250 269556960 269556979
    0x3c21011a031018060303080606030402010f080907122001300b040f0603022706040c020312010602010f1503021008072312100b0f13050d08090405060405070c02 70
    0x10300c9110025940a4056060300c40f0000d220000043c029080310700c015000325400801050250070304408586c492034045e1100030102c0403980c0c00302d480709401802040d0901914030042400c454034001044c00720701031102040700500c003018040405480c2c002c1541442903c4c030328061316001d0f0041c01b1041c41800600c0f450700035219182c5c140507050700304003264818540341d0740d210391441c2030780a40180c0e030003651070701050080c1107941c1c1d0540c140041489003440b0410001015841d20b50400120a0081d1040d0303400c00c00306101304194800b081c0c01100150b51903580a8490725003902c1180c00100c991100680304510b141c021481e6014040a4401000303005400600c4250203280e9011000c60720302110a42108180d00300c05a0b0f0300700b41540d400320b5040e080859128000c02c03c149054958090040d40342c480c0000f152500313640541241c4c004001c0e8410002250795a402c1c1807401540290740704ac3d6a9440d0b28108070480e8401414288918504000d00c0003060b0b10201d54001968195528010b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 269559460 1250 269558210 269558221
    0xc020114160209040807060606030c02030d0e03070b0702030301092906090f030f100e01090506072006010b030106121b1103090301050901020a020f010e033c21011a03 73
    0x601000e500710194000c0b02c144140410040c0510051446d00d01403a0308102c5070b500c455044060380e40c01c0055800581c0144102c03000003070039074000c0e119406001c08807490295140d60720341d04c1c40f400700d42e84030140c0c201000411176210179002d01f40c281002e22180c1508414060b0940341d216150b08a0180201c0340410407007500c0e11003004101d01c44800804954001d0049600e190341c80100140308081a4144400c808400b04140201204150b001e4041c8c040c5503a4002c0403510601100103610144079200e907030064101090001d503002c0c001c2076a400e0f903a0360500c4d001401d01c00240e503401900910b0140381020310343e030707d2056810840d110b151400801d504c0c070703810500c0c2d8000c5440c500d916501e40020712086000c154002c2c11040391503001e460250b02002c1c2c0e403600703ca5205d244044c064200700300c80c49104848120a440c094070302102c00f02c00d400341540000184600110b40c0b400d08200180c00d1401c00300e501600506040c1c403611f520345560500400390741d04e83c0c8040e1740178040070000c0017044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 269560710 1250 269559460 269559487
    0x6240d0507020c030f07060f0306080307030c0f0803090a0b01060512150402040e010b09190605040504090212010905061911160203010603050a0b100902070f020d030e2e0c020114 78
    0x4002c0303800500f2221120410740017584c6a880c14818000490741e00384900c04d446002c0d02520088801c0c6e14051030508079152010f51342061340c5001101e070101d00c1c030030000009030088051801111040c2c02000102d02030f151401d8120011f0300603605006c030038050800c80040031032150358050340c1100b01c102c00301d181c0c0c40401c01900031b81c1c002000f66a1210004645803040c5801b4118440084800d5180031a030300701503286d041c100e40115000208204030a04c003074140b0f80c01005140c0e01c00b9101c4681c2c040e94504032400c41e2003240d01140c80750800f0b41884242414421040d20880b020a0200000360014400030918402c41c100c0b00740000c2c8000340c1809640c0c080d031054000350b07000400d541410a4625002c0520081115495040610304401007071801c003d1094542036a80032080118840c615002c00906d0190f8030000c0b81007048107042002103860701110074116840b100c0c2c00124000001042c14030031380101c260b520030811900207880c0540cbe48001c252240e0310060510581e00d00b10440401c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 269561960 1250 269560710 269560723
    0x1022e09080903030a020c03010609020f070b071803030c061a0d0308090304030803010e010f06030506060f03090c03120c070512210d02070c0501170c030c0d0902040f0506240d050702 80
    0x6581c94000070170280201a00481d01b1820072070118020055281c0701d103165400c9000d20710360744e80c900b02c0c140004000503a030603001c0c80c2c010155040041a03940c601c40801101d0030b058108400080e44901e0380c104201960180c119000c40f00b480c40c0341c00300011804070304408006d110140400004402007110380a09104840c055a00004600d0707503076031905508a4043c0303080c451054806030603040000d04a20074403840e4001d003c010b000300e18120745614891800e404c050415103007406003060000e003565003009041c11001740c440c0300580b1220240d182e035007044d2150344003034064220b04140200a10300030035840b40d10094182810000c115800c030103145030088c0c841d00403402d4400903030181800800207000c07080f03030004d9851910350044d14082c15401c80c000c1d1a01030b4a00300a1002c180c1180c0100003510b0150348120001500c855641c00040644065402855000d43e1300c1042c00883d04040719030100c041c0e0076000c9040309142c0c04014814a100da219090709071503881c404920028401e2059 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 269563210 1250 269561960 269561977
    0x80421120c1b060804030912170a030b0306010807090b030c100c080706151a09032a0301110702150a080a0b0f1017060d030e1002070b12010501022e0908 67
    0xc2d410854035610f01600100c4151819004a0108640082c440e03000100c505001540003d08032201142d031610312189400002c0028241502d4102d6880a91410040c2600030901e440003040050300e001406001c07250801c00c1c05000743c2280c4004e910315120070704407040324501882e16000d40c94880c181031189005042004145c2410310501c00d00402180341801c061380e01c00e0508000002942403815100d10440101540540080d0161b5000030032800348000121030340010000000c01c8040000d00b1101c4840054241640210f071590540c2081040b8004104001c5001c510b4440500c0010740350301390007041640103030340361180040c6c1034aa1030103082c1c0021018010584070010f01001400c029100a00010f2000100700094494907092451a5106416440700c02c80407101034248200001c14040e00003d6105045c1e000802c10811002071410407403024201900b54100000281030100d49401c03426151017002910180c200c0c102081e0613a40c50110700003c0c552400d103482c805030300a5500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 269564460 1250 269563210 269563253
    0x18041107050a11010816080907080d0c12050901080406230c03090c0a050a03020613170a0c0905010303080c0307030b060a03020c0c0909060712020705030403080421120c 74
    0x85080c10070000207902100c040c4112802d02d821240d03030b030044800d844104c0700810081400502d4034a02e40c01400501d410401c6041039806075515003004601c0d00f81030721200b10001d001d030b035002c1d000e111044100031550710f000e192442c0b4210200d00001c014940141c00502102c6d80c4107207aa101c90414280c1c0385500150044095040c58900380240c0311f42c10485001110780100701401c580c5203400400042982c0c001000c1000b05030968003488601c1c0c005414240c52040c80aa0100e0f10a401d54000c080304180480244110003071403400f100414000d50240e4103031410600140002508400c200d6032160401004a480c1c0c1e68003202103001d064000e4120303400000003e142c900b0039502d90001d040e080c52103400c95440110b0b1105004005008941080702c1d5003019020581c00d41c40b8005205d280c2840c04405814034411341c031f0780c41c1035501c9588102ca1041000070104401d0300310384000c51075014401d80390440002a51101c00182410030150810002400e03a0f19040099000c200c0c80e07245c1100d803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 269565710 1250 269564460 269564467
    0x102030411120f150a050a0905030f0a0314090d020d0302040b030711031c0e010c0e10110a0c0b13050301051510030617070806010b13090b060c0105040c1a0f180411 72
    0x18810026000985c1d00b018070904050014480c0822070044402e50f40e40b05000b18606200343c231149040d0303080000360700c00b0103443d44114040e20000008190244100c18081c1c8581200e41030003a240c130515110031428503005120030092078003d202500c1e03222855003000e000d52910f2030f00b0300e030035803003660b040c400440c1340d44070070084810142c3d0110241001190007007041101d420380035280c41a0181c940c0e6480362851800402c000d00c154200c1a101c60310700d04803858160b40ba0303500c420605407034001c1d01c151075010404000b040044c0d0315501c01048250005c00c0981811400c000c1c1420f52a00305034041e58042041ca0f421501c40d91281009040c80c000b030071801c2110f8840c0c6034a4444502c501000c0f82301d50400032480d0803008046820070040c0042220708a4a0049084064081802a554402d5042c8a02d1340390354420b0003030030b120714843c0c1d15108501c0d04003001e0a02030743d000780c0403400d0340303005120003e00c000c2e00c40100c85003c0005a00c0520100b401e8001034090031403489100b02d034641c0030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 269566960 1250 269565710 269565733
    0x30307030b040f020705070b070c050a060305040b010f0308030a050c1e090a1a2203020409030203070303060e07050f09060403080c031306030203060607060e1002030717090102030411120f 82
    0x1544007080d0654100d5081c81181c4a6201110581c0545035000e4210f030000042008400040c500038900c03940f103a80c02d9000241c0d60400a42d04c01030a6100e80007180d20b03202000200710405810320f000d02041e030181c0b41301c0742c116100d13450319010041030f024580740e0340c0003c00e00c00c1c1301003003e8070035041d407205d40340019200b05480b016494200c0d41c048c60180c21603020200f1000b0000917800700c17401040780600d083c05c110340e5030000c04c8010b100010345240d500c1c08001c40540c46034001c4e08030050003900295524400d62078010126107680d4045401c68090600380080298018121800041301d00601c035203c2c400800094807901c2182d00082c01c0d40400521200c05940c048060103c1c040401400152643c1c1c5550590691000322005036202c00c08021450000d801640f151290704001c800322420340340701c044460700b280d1080e6041000701d43c0c1c0c400d0900340500300b0301d00c1e554083c0d40fa400070b41c21400d169540b04501d51600b241075216441200402d11909410040c0307040d0102d2481c00c559040c4505c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 269568210 1250 269566960 269566967
    0x712060b0406020106080601121b1a0403111f05340b07030c05070818040603110a090209090a05062d0a1202031b0a0305070b0408010b191404020c030307 67
    0x103102c0c03500594240100050b400300f000c1141412120a10030291003016540e450038168001c2c5d51544071541c0104401160328024072001c26034654100300c4441c0e40314258142404841c481c01401c6d1f2245488100d1b103060700003880609440c4c2c1c0c05074141103844801e80c1d11b0442c41c0321040316203020301440c0681c096001c10f24070080491124000d11b411011502c0d486001c130281e071004042500460000c100380300c0003824800080ca480c094001056484942c510009000c3d1880c0d075005482591001c80c0d00d81d450b01c3c00030000402080341c004118900310000b0003107886840c0c0244005012079684001801d00e84626035840603080c1103102d11542c0f503100800100698005004244c05900d4030440030400c186450000f00503c0d400a00034900a44402020b10300c141c0c80c503d4854100c13110b0f03400040020800c001c1540648404070b1b52035181c1c2d003400304441c2110f034820700c02d9218132501050122040303011070102050310340c000c1d80c0c00d07129130128010602178800c0004d082e0441c03000100300405181e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 269569460 1250 269568210 269568217
    0x10516121d1606020a0f0f08120a091b050f090402180703090501060b040b180619020615010813060b01030b1f0f080702070e04023f060f06090712060b 66
    0x1002c0704503800316511800101d9490701a05401003018246110707450205100341d1000d290f80c0d100b0044140b42410480940b0840c000589080551646030070005003007004000926182c80940381c0c5144500b480c11000943c08140c0c4000a4003e02c40743c0007084c190349840110033074048183c10710b03045500740803a00500418a1071400d6450b540b030081c2c0864108203010440e401c0b10000c510f40c605050780304240041d0014480042a80000300300f04c241d4010030012003042d40c600040e0054002840e04000e10070740d04811451240c10490040100084041d182028143c0c003034002c02c0c00034502408000580040041d2060319074004c4c0300c005c0840e1200d20708402c04020704101d50314103501d5029071200361103c000540b2420051f800001003840300703611094546500500041580c003056070304031f10705101a0400c002402000d0905094140d05d42c0e0b0f00000f054240c90044001c00316482d1402e650305038000c000d810035206011034404149820b204038a80642c2400100b810041140d46000d83c1c8103035030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 269570710 1250 269569460 269569483
    0x52406090a03211b0206030a0608120a0305010807030305040e0405070f09090201030e0d05030105100c020907080702070b0a0e090a14090f010e0109052e0f09060e010516121d 76
    0x1104124050351070703114146140290b003c071300c401c0c02c242d00150308104843c0c00003441c88080a80d51100082c2c2c0071020008500c8103607098050982d2107084c000300900755035050f0003900d0241d000840400010340d1000848088400c0e44282d85001d403079910f0180d092520941c03040c00c0707200011101044070f515690040180714405d032400c00c40040c064001c5a2204600300904020030030510041201c0d04118002001202107440c000c214180381e030b0300164005009940380c00c0000c42803010030422580400022020341600d00c0c0c11030402003000c400070f09850001002a0060500c2c0d0041071103410142c202980c0c031060084005050721b00340720842e0f500d045842d1031401c95800c050580540950600c2011040c80e041809420a0061008a4160a00c4d02e070081d8000403901107441c44c00c480188076944100801030300109040c0d60a040801c150307a0503a0000b50b483e4940814041480050b0065042c0c3c9481030500751054515082c0d260010100100540707801d11400c03c080c04503403004909004801e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 269571960 1250 269570710 269570753
    0x1906020a09081209011b0f02040e1509060603190c0312030207080a080a0f0e0c1018090501061e02060a0b0a0909050106032003030711210a02030f01052406090a03 71
    0x41b998801040005c2c204054043c1040b0255a42000503041941050802c60540002c0302c4003200b2220082c015a5400c9481c80101d403c0a0140a11403800780141341c003540965a5106440606454001c0003c0061000401d480280c990a82c0c10b02d0080e0141c401da543c02c001820f44840700c4e41c00144c40341030122203a094042c0b9150f000682003a0703030720503da481d1324060001c248007902141404009003c40014205004242c0825101c802941040740003800404402040a51604d08050400f4122082d40b880164014841e24451a0b001038072070390003818a140032847e10400f9005c1080c024094001251403420000c500040c000150041002c0307030302c00c0010300700c6c1060001e01000000881c3c110250b06410402004010070302e42099036091680c002c2c984d145100741d445041d8001360980b166900c498121014640551a00f842100380c95203440000b0b02181c54100c80f5640c80b50070b607050f890030b5848400c4032100651a00010380b4003950303001d428000d03d0707500c904005044515078698200b06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 269573210 1250 269571960 269571977
    0x60c130f09050f06010906050a1101020904020c03120c030408121003021302121038041404050f060a12140607030920220f050403031d1906020a0908120901 68
    0x84d540b0a0641d00c08540040e83c55900304003030078004581da40741d42c624105166400340526507181e99244000d261650040c1e00840c2d0310250025001c004000041003244004800d00030407000ca4094000c40f0030907650b80c48600f480d90740343c0440101c0ba2001e40c001a40140780b0360021900401140d004207035100040045408603584c4c0f0300c650b10300c0003450290151017005e8146c1001440c0030a22950303020a280010800d0989011468244c281c00a0f404480704280300c0030004620b00b460700c25940c00125052041500c0e240c0031000c900d00010500c680811080c00d44442020703c004100107120110100c001d81d00790741000c002c0140a844d02e11801e82d9581010505c26601c64600140320307140c40340260074140d2014803042c007004014500301d68041c003207031600da8154000b5803621505105610035140040c1181c5401e103044c807000000200c444065120403801380815190069812000d81e00c41c1000d80d50710b101200803a20b0405c0c2e54058a41d5202e004c2d4010580c468000142412204c02e0342c66150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 269574460 1250 269573210 269573221
    0xf0e091e010c09081c110316050604200d230f150c07032a0b130c05040209030307020d1e0b01030210030b0f012d0503060907020708060c130f09050f 65
    0x2250426880c02c1d12100c0c2c18945c0c510f2842e4024454040000303a000e098070300303104203062102e5003d0601402241c954019400704000c1081d4500318164211204070300000c00642d0401003985910050720140c10180c2d9241c100400c0401d80855540400c0c4ca80282c8074500e60300c215407940c42483e00b00700803601d043c440005514107004001d55041ea034140d965200900c1000366008a002d200c07000b14012220590380394000702d01c4544000e40651001601490301580d18144a400440c0d16040103100d18010040311189a500000340c500c040d80449071018158564500410031040c016080099614041d100d981405074441c0c4082c1282c0c000e44a000b01140c0d5114110115945010b01030780c0000b000080d0780c400d5100300309090f016801e8052084011405842801c4100420003040000038070000802103d828102a4950400001e00003003002138205005642c50340401411040400400308078980d008292001b14001011401d0101c0d28454a843d0041c0c06810204d88030304d00300020402240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 269575710 1250 269574460 269574463
    0x2040f03020901082b120c021b010e010903030509190303050c0c040605180402010903050102040b041404092307180b10080408030105011d040e01020a0908070f0e091e010c0908 77
    0x159043c0030140d1010303211108194100d00117a010150501b0041d00b014004410700d90b45c4110100803400e0780041c80e2400c05404688060300034050b401e41000100b03a110521039070468840300c03c1c2d9900d41441c07902e40c0203d00101e08002e8424071a0542202400170000c1455040b5009100c60f0051030182d0343c0c0110b40b80140010347c0d01074170646d6000800054800e120111000810f0f07001071051400d42e030802e0f62130304d82c103003641c020340c110005031080001c0c200f080300403009068021744800e5070184514045622814201c1054002084132081c0c0c00c04c503906a89814401c06018001c1c8a522448903012502c410008100031485140240880c0450041c014051514688929030118025107984c4c200801110356110f80300012a60b9100c40040000c6076890b07010b480c0181600500050322440c91182c024183c0c0355a42c080d54030b0760011441400a01c0682c4050000d940c40c0b4800361007243c40d68a12a8505000342511340303001750380c090b000d03500d030741041d001409501d070b265442c008040c1d25003560701d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 269576960 1250 269575710 269575723
    0x70801030b0c07030201020903060405061008070b1b0f060702010606080c0306031b270702011d030f07021203030421111c02010e0609010501080d1b03030e070902040f0302090108 78
    0x90005081d5100084031040c0b448010810188284000350a02c402a00842c0c603058081e241150990044010082d0540340c0b01d554100510441005000c40c1d8a08040c81c00103114804605201c0d81d0402022140ac000c100512401c205900741107950031700e00100024000c02e56400341a0005640d000403401c6400c2d0b03e0140e030300958006020340010032602c0b000c0d501061103954029044980011540117100c0158901d0507403006949148409243c046002800c41d49240f4542c5800341c824021075900d10030000544001e15450441030f5910034407800011003500307281001c0601c91000000f08001c0140f001c01c0c0142c2081441c840505009516600355400801e10b03520300035950201d4800f040f5101240c4441405820a00000810881211400341420381c211000c0000769190320040100c030303c2c02c011a48492505241007401e01c2122041c41008107038024000d0101621000b580c03c00002c1482044010602071804540e03035540e1345203814012041b403005031301c140e84140000401c0000031414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 269578210 1250 269576960 269576963
    0x60a05061921060303090302120703050622080a0e180105011b02130504051606030b060403120e030304150e09280204080d0c1103070b0a11030d090c0e07080103 70
    0x80c0980c0c0d07a0000422210b02c0105140141011000040000b0091051060401444c0207594400c0c805040d4018002d8881c0d242c00b01c00c0c1180d2200b182000496408036800e034106480907240304c2c5800180d545080200d107035400151140800207045035865402180340101c884042d50f01001c40d50b00c5410725112820248a014045800e41812080721615200d03002c000c00d01c02481c9415003603840c0180401c696084404a41e29403045801044400c1290740c0b80c0000e001038541400300300f500c440801c100303005501c0000c0007500b1609403038442c0c0c0d0107424410202080902101d07120f594840700480189581812400411015402e4003602c0c02c203407002c2449a00000e5018550f18003032070041307136a60452161006a16401d10000c2103106050013080040c400f9580d400010070070ae410041242d405a00300d00f8400d5000780c000701f01c280d1840090f9000401e4600b002d0201404000d611421031041e02c00f503130b0200789040d0700d4004000380840141d007601d45407403016115555911081d640b0b03090a000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 269579460 1250 269578210 269578237
    0x72001020c0907021b03030c0111120c0301150302071103013b07032402030406020414090f0403080711030f030f0c03070e040b1c050d08070302070317060d0f030305060a0506 76
    0x40291420004001217588003c0c09011030389007804421301c640c01c581c801e28450303864076800651400321311128817809411502c94a480b502d10351400c505200d50702841945803081c1500894810107101c0d8845141d24106009002401080000031100d0300701c0032009803c00001802d03102080e058441c0b0b01d44000c4020540000b40180d03804d584030098908400d80c0c0074100110786000140307079080c1d07500241d4001c512910300544ca0324180b5407108076003400340e1070650240a88000b044910000c242c0a41c0e00141c00d400e00d50400e40f20721808540c010f03400384007101944000070b40741d0104800c00f00114891011b98610110b0354940700c80340c088a2005079914000141ca0004020151801e0362004182400081c1101c50000f01c00740c400400d82c02d0303900261481d070040c422802905810400c400d5004141c0e11b001c5260000603900544080c17007210b0703082c0034810301c040051800d407a81c2c1c51180f0059041500034058401c1842c00501a007000c403440c0b401049a0540051241004801c0c0d0703214140400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 269580710 1250 269579460 269579473
    0x703080108160f1a0417060103020411090108070804080906220501080606041707050a18140c0403150b030a08070323030703050a06210201080c0c0a08030c072001020c090702 76
    0xa801003c0c1802c21110200184c100300c0044d1103000601508014508200600429031441c01040201c40086046e010307040380402c50400300d40e03031100145501c5012402c00000c82c4e161410700170400d006042c451a04580d0000d050b01405041c003a0a000030403428104c41012602d0b2801114048030a80e103141d04074500f0b110601414420400280704040030f0702c100d0781d14a03991030010780c8103400e56110a4016030907490100c00c1580c20300995020291401c04d001c541c0c10310611781c00c042e01c40c910000d0500c0086030346440c036082c1c10fa0409160b114006003214040e01c6103080400c229804000c003140813502c0d43c01c03d031380011014124550b411444c503588030308561314108150050040200b95900243e610200801d5041483d1201c0303150500040481044001a20014002000107040241d160505100382040458002051100d9607400141c0b04e4880e11400c0600440340241c1c030004101c142181000d090f546041c65000d25190b10990031240400c0020041c03140300d0b00c05031138000c010780155 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 269581960 1250 269580710 269580719
    0x90b090c0c0604140a170909090106080601090b12030f090a080703050d0302030403020a120201061508060a0308070f060e010507081302100806030c1e010e06040b0313080904020703080108160f 84
    0x1a1302c104007896112080e5000f00c085a640e10018040380342c0d40f1307091035601191600c103500b414510641d1211649002708481d90528003041c0d81d0340c1c0144140c0c407486032112a00d04040c0c980f03032204021000707204102d03607e92450350161102e0f5045211614000c00801900207444003000a141d0304594010010f080e210b100110110301a6200800980c00d42c070444000314000340e003002e104d100b019025400020703000e040100705c401e40466100c1140c1000800424404a41c3e26100150105e9900048a5940d00d14925092540d42c19085007d05035514000600c0c08080f01034201620900180e0f03a141c680da076543c82440024080f12a0203500a02d503207114640290064002d82c0c2c00c0000103003280e1a022000c4001861400c15407048a400109100b042c0100c0d6080001c00e80018012a44d09003080d05004041400b4000180b1803100f1050101800c400d20480c00c4c00c88035111800f030030565445682e1b003000350a1180a1080038443d220380f06a07074180004607600d020544046018100205151 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 269583210 1250 269581960 269581973
    0x50f031c0e0a08240109090209060402070620040302010201050a1a040506150a050c0d021507030b010c060f05071206140402180a06081b040e0c070516090b090c0c0604 73
    0x8414416002182c0382c0d80800d41032410040014141c40005801049003400c40741010309100690000400c00d0501800d1070040c6e4074a9081940403100b640e005850307801c14180140078044114003501c0000c20f042c0704c012101e039044000c0054074000c0e0000c0c0015180d03c0d40543c21140c0200d298080e14104620f218443d24143e04001c5d003080000f0050644014443c448043e1548a2503000c0003103140080d403050302503400d01c00c0210800c440c2c0050603e0401a45203540388800c010415820140c1d01c4080702e0301a0300130a060110309400440420088201c2002540201410307141c0e40c002c01c02c049100980c0301c105000c0c03602520703024500d4084200f00d040610001c1e4008040042166100d84240c042d0703521401d5100c0000c1500740e4596841d820065aa244195100c008040c140d41c010441840443c014608150700540c8125081d6070300c6550303040440c14007201501c0c2072011030324450300203500011600810302100c0c04507a030800f1900c2c1d0302c0e801e924600c80e80744620110381061300080c002c01c0700c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 269584460 1250 269583210 269583227
    0x1501270b030102030c0c0f030304020f101710031401050601020c100c0605091501090902030613020310110a0e06070c031101050f0d020301060e090f0606031008011104050f031c 77
    0x62810109088404400107400e90300125041d581002d4045040c03802c2000070080b8409822540c13020354a5400c158005c03d07203041082909501907034020b080ca0030030741d10131910001d5040486c1100c0d8003d01300607085181f0344190b84001e444182c0308500000107400184504d90140405030000d00a03101400700348010303624801b1100044c0040007083d10b0201d2034600072288134045500281000c8450020400d60740da1042e08100e6540d443c0251040040c0c0b00040c40b1a002002000e05205032140e520010340790000302801c1d514814284482c0103c00840d0b0005032100d000e203510703624a144001418486a8045c056002c0c25404030040c00300085004100390084c0e07400185402498100c4885000003103500050041300340941c001700401a00d5409180707a03071000421540141d281c1030031400074901d00b60203854035210b0100000800c07103d13030841307034007000529402c00244110407480c5c3d20b0300403640040c40340c3e074000c2c3c071804504c400710314010910800048505228a00740001c0b03040803981441d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 269585710 1250 269584460 269584529
    0x1030f140f1f0b19051606090606120b01060e010224250815012d0513060c02030c010c0506070c03020a0b0108031b0607020d0e0f0d03020a051501 64
    0x2e0340ea1006600b524202c807003001c0584002e107069035070303400030f0300d03551034040b2000c1c19102c2041018000003500c8600008150042900410041b43c0d0105038100403008041c1e82c3d0160080b5038040010344108000103d4060480340d5030f48804001401c1c0c0d90040e80c4806141d0b403101400c2d200502c90f6143c00020300981e9401c10f500e41007094031180027000010070200b030007507500d0208081904024807030396508603200c4008028609030740380c50503a40500b007111680580e4041d01c40b07041c150020031103100c0d4041d502283c0750b03800011402603580e00c02810714295003400364000e0083d60b0780b158007540190b0702098499801002416169501942100c90072013000302181180105201100414100e10040d40a0706aa50165a440340508010341524001c5014100183c200c2000c101c6000d0700422407469002480c1410706150f0003040000e04491040d484a40e40003541c00b01000c00e040d40061002c3c0c2007031140d001c990f6242c40c2601d450111034001d11814025005000c400b0740000464003400a912 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 269586960 1250 269585710 269585731
    0xf040207170703021b040b0d2603011202010306080309010206011203022112090a110d0809040504050f0d0801030f14030d29150301121506031101030f140f 68
    0x241a0700d10011450b4071544065005074040d040d40b44500040d55046a0b81e0441104e08108010070880030a0205e0034601c4060940c5981d500c26104132440e1b6400924094004005079030740703603154003c039205d180342032205900207440d044011505650000881d40c920350160014040742c1e00e0b050400542014540d0101d04600502c0303030340d03260214605400340c2d440003080c0c0c4080d2202017801606030500030042000b0a1035000b1140940450120070481c0000d00b82941d9403621a0b2007800c0c866032600c210104150018504002c02042c8580414941d0507104e0001c02d5492160940d50105c4084102b8040941400b101841550000d00300002a00e045883c1e5002d0700e0500e8040594102264803040c01042914181c882403984040542924242100115400c0c0806845070b800042e181c0014003034580403a0307100030454284083c1220218001c0e5800c5018031207281c581c506140300c0220070136128042400d180346014048264000d42c10030300c10071000e03408644d49000d502100400042e0104685 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 269588210 1250 269586960 269586983
    0x206090111101a18040803060a08030d0515060f030604021608071208100602030d05070306080708031c18020f040608070605070c150c12021207240203060f040207 71
    0x15041c1c103001d01c8000425500b00080d4850703441180004424040101910411961304203c8200c04032484039604940c00ca00402e4580d9100c40204001c4000c83c1c2000800c1e110100d600c1d0081c08481e0003251003400320000a403040d64160303040c007866001c1e80541188401080c00099071508056000d04070b480103090045004518944820b8115484114141d580e281c41f40d0883c00365a80020003680c01c0142c03001031400c41440d00c1d4009480340105411061600d8a500100d059548250845030207400110103540c090740d501c5840a640c3e41c0b0800c40d10703982ea03040100c4540380003418860100ca000c030900c610440801140d00f0010000e14100001341d0181c0d44440100f2440810041c0d180606229111141d68007020b0811400040d078540c080c03025861135041c02c99485911481113941d03258049000702006441c0d40341607081c4104e148060b501c06d04013042500c28094100782074822218000c080d1a807040003031250740142c0c0710803030b4411f4101c410000402e000c1d080c258001c080e40b6001c4c3e0010101d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 269589460 1250 269588210 269588237
    0x190f0b0d0b0703111305120c041d0d0e010813020d06020c070611160e070201060b0a0e19061d13090303090b0f0103170a020c150c07140a0302060901 65
    0x140000c0d240400d84007a96280d080080154043c8038041e03508012051090600d10406001041620203004d810302408a04586440395002005016080c140c020028071880482c3c4030f61803050b20503209070800070b200e05e005130203000780903005080c180c1e81c040c0e45100042c0d4031503060448440c00100c0498001e1042c4d5803030b1010500c5407010f40500311400c00507101d030318a0640000c01c1e01d03d5810640c82507402440f52214074130301443d241c404a070ba0802d0030b099195110301080c0d00410066101043c0303190b0001c1e011050950005030783c00b04070720803103d17065481c440e001c0e501000c660310300070400440c001c0903034a140602000005e12650800606000072103034400c2c0040e090360701798071084011030348528080c420000200300c40303039104003141c41c2c4c92140d40c50341d205d014003403c031402103483e440303c0024091041d074400e10100c20b03054009803024005031454185201580d1184003c1c01e194041d80d400401e01c0325034075202180c4603000900c0f5956150940c1c0801100760f201c409020b05001c0c0305491101d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 269590710 1250 269589460 269589469
    0x3060315060609100e01140c07060e15040f0f2405180d050d0e0303070f02040203070509030d110d031806150e0a0e0c06030403080a0c030b0316090e0105190f0b 70
    0x401c110003603445c203414011910000d0041d904a214500c440c440500492040d0170000529008803400c07494440309201d14480490301c1d19600c0101c00705403d000040200c0c0f82592030b0350600c00c07a603038240c5a8913404d6a901403c00840f080b5050f520b8219803071010301c5209441540a00345103440b1a08801000a110002500111800500300d8960300403c2000036a40d40040309203041000a0300918500100c940d0381002030103003040001d10559006c8040b801c054401c0098804c415000742c101c51010411210113402140c441228414130300c504111380c200c0038030074094681c5140c14000441030b521095a6008090643d000c0c4406807401941400200b0482d80d1140d00d0158848850003d0090030380c070740881c1421112080709009110030400d00c00007d81c00041c0341d274403e507200e1000401d503400c00021005030088510060b4075101e104a6140290f80c81010b00044840302441000440302d1000c8403030981d0030448108e02e19000c1d11494079444105c40c2c001d8850300c024034000042d60508200000e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 269591960 1250 269590710 269590729
    0x2060c03072603040f020312071506120203071203090b07031d06040503190f050d090603060f05090a200a0f030f050417031503010f090213060506030610050f0a0810060503060315060609 81
    0x5640050b400c4841a92403030ad1403081070042d00101c505e0882450f01a0003190303441c04148036400180742198001c400349840751405401820905c207403d030740d0f84818200240700c900c04071070a20755818500031014252509a08640c212040038000d40486100341c1103006c40341031104002d072510341c0c03034440660005206029140e072a1005450b12240309041100003421a2400d40115031004440c010070b000e80c5d540c110368a640114910740114411030b0b00e44985c0002c3e0803180722856680804038134010015085821808207003016034007000384801000040341692000c0d54050300d40e0360045031055003008800025a4444e0340e640041e8101340d03941020070300710385c0907000c3d83c0c201e16a40c0c1c07009400c514001400500d0b41211080600c0b0950610001401500c00540b440744604c64071190704d0420350040d4155090754080c4280d1684641d20410080c03e8168101c48458100b4104880443c40c503004000782c0c0d000b404c0c080c0040100d59421070605144004c050011fa0b440300080c0308042e00c996800700c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 269593210 1250 269591960 269591963
    0xb06030f010807120b0a0b0105074e05091813060c030516052506050f1b0708131809031b02030307080a0c02060c03072603040f02031207 60
    0x2412603a42c5000709440c200b00c0b544e0040700c2e03c52070102106000c250302d015019040785041030000b4036039840c040160754501c110b40c4010990410292032030041d64113145054000c1d2003a0800071030b01d43c0403003075000ca540f952055184100a92112200e4403a1182c0040c1403100c00c00380220301003060000380800c0c1004d003101c2901c41c504200745001c040000d240581600806242411300c414100680032a440e4031000701d0340c00c100000410600682600c20215104070912411400700040300380c185040034200850300310404144120100303030252480b810414034007005a58141c03d01109070740741c00d13290380802a40c9803c000d0000d00032410308040e06880403103141c201030015070403040b440c000d00940c5284a002c5130840e121952000540c03408000c4941c03460b801050255a11803500054070101543c1034080c0d00000007141080b000c0c00000002d0140e40c2c003508000030203d050500024402c120300ca9801d05000301130000c900081d602c0401440602e10007000c3e00c00c803003020b1002d9032864110010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 269594460 1250 269593210 269593231
    0x21801030314091c150c0c1a010b07060e010b04020313050c030d051b190f03020f0c01050d1d0d0903020108010e0403090e280905061e0a0b040b0603 65
    0x10810141c02c403000400c040008900c0c0c9040c0a543c03800101c91048404080a580304913040d51070800075070000e01d05e0211001501001a200c0401004050014000c030454017400305042107290503d5009181c0e04841e844000c40d464440c40da0345203806800344000b5074500399201c0c404094241c0d07950002d58890341001c8030035002294a41031480c0b0306504510a1800394111a15100d92158084125001c00c0d09030790042581c4051a64014030305001d001d0026142c40891030120300700044d0748a0306080d40e00036801c68003035000032402951140c40c60311009021620400540c03114504540080d04800d4020540701103403070300032920710b0401ea8580301c54000110030b240300744215a0428030f01c501600512500124a2030169009030550f90380d40118400c0d0300c03240e030028a480d61520007a25880c44668070340000ea0200550540140110703c800f10703118010031000504040c450210f41d88c2d403e00a245002d6941c03500310001c4010410000c2e5190066107032182e148040d10342c40300860080c0c0100300d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 269595710 1250 269594460 269594509
    0x10e030a212702030f1e060901050906060d020d0f060b10020a080d18050a12030e0309010e06130b040b0c0105070516020906061b01050a05070c050601090b01090302 72
    0x1648110011055284000603850000614036004000c80e01c0580180050b0031035840c02c4090000900e80910800c880700e070340c8240c9141c07200c0309030303000c01705859801610202d4625440300381d8441d090311000c54140006034080d42c00108140340215030350b06014000b800c10403200400b516160401c60241100341e619030345a030801c4d0147e0400b80d2142901c5a401e202402036240c99554440280c03044403100844c980e1201c14a54604400465030403803d68040304451844503246000c8504031030500d86007000c03074503100c482c040c011004030403580e89801c165a180510302c4076204114458010074042503a40c2000746003c2071200d24940180054281e54299544030100661417900b0755000405081c1008010300c410250701586a52000c000c581c1102d10034040da613401c0c0440c40f64003030011014640d10100701032104104040d8000f81c010185450b0038821a940c3c2ca078103441c3d8225140c3d0040c103542c40300d00100440b11103580205041d010500d0010310b00c0e942d9400003080881d80588118041c0c407000b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 269596960 1250 269595710 269595737
    0x170601140109030f080c0f0a1a1303051c0b0406091b020a03080408160204110304050607091203080c0910210b090403110a05060703090c091418010e030a 67
    0x1485426100c510074a04401c14605640c2c40360008030020034000e200100100d401c1810301c0050040180c0c91180d14112020048541410350300704c1c1100c030b03281d04482448408542490443d50500742015015102e091034140054100da44800c40003c2a400720f56417052062090307a2035000e04001008600d202017100507042c40844400005000100e00b558003c0920000003600071b000c0c01d500c41d40101c0b0185c3c843d1041503141c64174900c0720368001c0d0b206107004900e19007947c405010f103006038060b1044611a540d01d80050f145030949001d0102801641c20440000a220301c2000d913100c011588d0050902070036201140046424114801c046440c6201e0400700f941006000d11000e0710b0401d080c441482c025000c13032400c43c030103480070742044101000300780c51010801c40490680d90100440b0b80600d010070008000341402c040031108040149d400003400552801b07041c100d20b041c0c1c4040e01c0c450315080b404847c440c50304a4440e909540310b00041004210a2020300fa00e001540c031424900c2055 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 269598210 1250 269596960 269596979
    0x603270c0a0b0a0c120509090c04031104050f060d05070e1312030203040f06050604090f060c0e010203031006030c090e04051c030e0703060c0c020a090f05060901060f0c0606170601 79
    0x1c581025590030b03828000b00c0c0016510188040d02e403034118164542e0400712030021241c0c3d00c60542c005030045015000d010007d05a84010310482c0c0c01042c6000400043c041040140c0344151040c901d60202400072070300901d00625a0405170344038400f150255903950962503071840c3d04550b52000314040c40c0f50142401002240f03020031211a1900714a145030654681a80606601c0094903d82d90f58000a87ca6110b82c0c3c40841e40c550005180d0744034030090325120019002030351030080080c06103002d0700b00950001090741d00484001c0c400f0b413602030400000b02e004104c03100740d15040001443c00001c034560864082d5000328041c001418007052000c0312000c0300d002d8000984105490042e011602141c01328000b42941e50008010450801100c8221004160ba4038065030144480000081c00005540300071000541d41c0300c244402d40d20310040004500c424801d02022403a1103038842d500c02e2195609810703440c40344200164894854040c80007510b040064412294072480050201140707 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 269599460 1250 269598210 269598229
    0x9060209010206091c0513050301021b0c04181b1205030409060b070308070f0207050a06020f0106210b0a02070807110102072403020f07061104140301060509060603270c 74
    0x1e00001d01c22110b100002c0d910203244061a00704001c804113145900341c44150b500c1e0300408c00140259280e10220304862151201001501c00511910320141100d04050103214140d119088040096003416161f4080809440c0d1041160041c9000c012400d600b20683c0c2c43e001c1802a0b0046844a040c40a00c0c800c9500d107401c50000802d003444502c001030303442031050394030140e54034203080401e01e4480242d2901005400440c1d005c40c0008002c64025400a40c0544001c8110001e0104a9903001d800c0d20301c1c0e09640d09004407512071a80038011a41c11100c10380c0154a220005107018507985848416801000040f01c0c0000d0001072002550780c1000184050f0006900c01b12080044407a5080e0201c01640f9507001d0540125030f5400d012600400e480c4a142c00400c14824004c4184d40c11620740e000d40a0298032404005212001341414030ad001c003900c202500404140e00c4010402141d41c20007007540c02c3c00e034080e2400350701700c03211028041081442c03180144444001c803c00c010f0002d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 269600710 1250 269599460 269599471
    0xa0b010206060f040b01030b0303030132010e0121090b04140607050417030403021002030901090b040b0d0203040f17092115060a09061421060411120109060209010206 73
    0x41c409014485140e5581c00c1e0500001e50032100003030f24a48100043e009041c4c0a1f2420364140008000003c00c00480800502c402e2100c11030540c8150f015600304120500f4a00039074002007011146820365401907130210f440f140d9030714581c15410b80119444055079050601112407402d10010300c010010308901d0310300700c5580700001d03104030b240010005000e80118800ca180000103521000c0090405004450165801500010f4000d41c4040045c2d030302da018001042c006010820300140864442080c4c40a942c01c04078001e2418040e19500c10180d000503100f070b600781e03031500000000075030b034600b040e441c0900c116010350302c4820b8072041200a603880d0401c04c0b848040e20455102c840000b10345d0740d410102c4404000780645985021809070710b0781c0d03048130007591f16241c80861030005082d80240608412106000c1205d03102208144903280c0c09030104540e800314000c14000f502c5106400350fa691302615809199008615850a441540c10f040c0c800c00d5002450001c0f5503814802d003944070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 269601960 1250 269600710 269600713
    0x150807030207020f060d02090d0c150207080d120209120a0b0709211103150609100b19020c04150513110304200a151e0c0221030a080a0b0102 62
    0x402d85030045200c004150303411605c200400a62101082103560584443c40d07005010fa00c4200c15500d080900c0005078000d18034a61205540038003601e1002600e01c1c2a108003030090b0400140c55007080c2e6052144c1110001545c0c2c083c08240d036640c807101e1014078028001002409111000e04200c4d07a0f0080c007030143c0b81003002d040030510a040c0c1081804036000c1009085c000f018186041080360030030302c58003255040c010420303001002c3c0714405465000700c4007190542c2081d118403181400e0803089100c1c8800d0800140908940e20144001c440456441350069400160307410002500711050800780b900b2104c6a10000c1c009070400f10110303c44803145000401521035a64080f541c00d000050006040703101d894103c5411901c0e0011941180300c014203840c84090316903100148020031480b100c400140d02c5106480d00402d00c0b1202a5006801e4403000441c030529001e1144240300b54031817000715a0b444d145640740703450800c01029001042e560300d0203070382041c440000070340d10304039200ea045 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 269603210 1250 269601960 269601967
    0xa0206190305070306062007170d08220201031a0436050303011a0c100606080703050421021f0905160608010509060d12080610090e010506030705040b03011508070302 73
    0x18650400c030141318454140c01c2c1f21040c04c420741e0a1920340000d54225910101d440000b90703d12200014041203c031005441e80b5035103a403180e401100440154400c0005c032254a6400c40140d4045d6101450110041032091250481c0c00041400d850400c1c40c00b0440004c9542c0304410010019a031016903200000c142a502c03086881e100da617804180074204440651074420389812101000300c40314000030b0b1040e0354418001151410042047d4400d02003c078054500003580e1a100340701c1c2601c9254080603281c213000484100041203020000d042055106030744049417807410b1248141d03102303c0d12850214a124031850031904091010040310551848540d00744010f07034100510a041d194140e900c2d41050382c4040016000b0344560741d014000b621030080c11040c40d580480500c0c852001526101c0ca05000d0990443d030400c00c41c455558007003030840060285107842401113401c801e09180a0342016124500085254020b90040d4003c01c2d00c030711101a810b81002031180e202c0d00c41d0034110308 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 269604316 1106 269603210 269603219
    0x303020a0807050910030f0221070f09140108061c030305040b010f031e030302071208010f0b030112020d020a091e05090705100c02030a0206190305070306 68
    0x915070000104124012000c481e4454400340c0180c280785090030342280280f01c4090050401e5400300510040341d031503c0e807204000700850103080340030b040269028101c80603504481091040b003100402c107040b80e820f00f040904000303003040645551103000080d0a100041440610411401e044601389503059200c2d5100700d116900e05c0c8403c0e600d680b0400304800d078070320006004c1c1c902201c1c902008600a612501c00d1882400d0140c1003112941e1002d001003019400000082d0003000104159400c03148008002c004000b1820301d9541000e035020181c8a0b003420107401186001d950100310341b00c625128008007006e00c4c1c204141d4100c8c0b82d60303c808e2144038460740c3c2c0090501c80441c1c2c0c42900403406404031080200204402442200140c1e40ea4540000aa070305004070f18284025899050090048440f044c0035904042d007001400b40444074041c020302c0805103010800e10 = true := by decide +kernel

theorem cover : BRFrame.Cov 269424460 269604316 := by
  have h0 := BRFrame.cov_init 269424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 269424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 269424460 ≤ n) (h2 : n < 269604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
