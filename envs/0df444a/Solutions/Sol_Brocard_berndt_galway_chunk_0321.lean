-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0321
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:11:55.893901+00:00
-- url     : https://prove2.me/submissions/5689d048-b6ce-4617-b377-8158f1c41cbd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 57553960 ≤ n < 57733816 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 57555210 1250 57553960 57553967
    0x4031407020a0b030f160905030705040f02090604030302100605040507020c1002030409060f090b0a0e0a02091c08090405100f06030b040e0313060306050d020f011b080c071701020c0d0c03 82
    0x90f40c1007100002d2011013000074900455005d1030183c02c80c18859078415196140446181c2e0340b50144a0301600813500c20061410075421400601d40018001b508100400000c00d5040c0c010740e1040d80107a00a01001104040f24800c280c050310083d6024001340c80c0503200659980c100104031805081c030f4003500ca00540c424001c0c0c0c3d010b81403106050050030395071002d480b000c4620780a00c101061070304500e88028541034241c68101c51240400c035400341e441300c0d5050000d4028500c41c0c0e0f00004400001501e0034002100c907000588a40c4025443e00e20202c02e010898100a00c001c80c6600031100c20f014402240d656002100c000c0c1c9004100745000e01c6c0846d010f80b2a05055030000c0c80040381440f180d11004140c0c009440803690100155a6140200200c0140c0300742c0180d0070030b40ca141605107a520038840044036010380b10b12a040d082345c50741c0b030f070005501c200d030788191640098605100c16441113510f6040812004004d40c208a600c0e100181c071240c0d5240301005100c0d0100e05941010301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 57556460 1250 57555210 57555229
    0xa05030702161503050a0507080402010f0c0f0804080c040501032312070c06110d05041701140406020301150c05300301060905040c030c020c091308070c09140403140702 74
    0x240d08102c41c005507900c04480c011110b8100c01e18000c28205030000700080d90358450707144100060744c0c4e01d41c865112600151450708445003030b0340802c80240107000218840c0c81100454a01c5103400c41d65075850144c003e82004461200c035031042e070521004001040415460103541003410303262054504440440703515041261030b4101000d400818034006005a02140100300d40d51900c40c40c2c14221100111030721580b000000f003010490070712081c0850070142400c07642e45040c44d400011500d1080042c200306d07950845003101c3c2d590b0000014040c03816111103a03003144566040600900f02240c4d1238a071a40c00352a480c840c0e410441804440b940e40342c200050001c42c11000d05582c17561a5100200050210b001c0c05019900b0000c9180c10035210380b185800325403ca9010303124001c2c0100801004e46000303801040601e5041c0c1d4000701040301b2800801c1035510491059401d1881c00409006803a2403102c1d2101147c2d0400030800400d4205d410002d0a039448003c0c80e942d40e5003480024400030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 57557710 1250 57556460 57556483
    0x1106120a2f031012170f04080105090a0201140a050403060e0a150603060b06030c0307080705190509040501060309080715021b010e070806090c09061503070804060e0c01050a05030702 80
    0x80d101e144511491460045000b285000d960842064a4200a1189140505004040b124400c202d0031640490708040c04055601c81c0300a8a0a07680c2e10426003507070f000b0749102c50650868a460070856811290f91400d199007030312104c0c1002c00d140c0c800303046030040340320240046890b0942d10322212414081c086d082e640c0f10084490162040380702500502c1da5000c1103d5161801030011a28a40340f01a40d00c04c0c1c640c9a0b8481c039607a10300300201c030342450107861102130107018024414440b07003070410300701e01c0c005956450b500e4001510400c401d03102c040c0e000900740762070b1801c030f4000300d92214202c90030607404c12110505502d600400000a2103558520b0131200901d0b84444088101034000c244899070940840702d481d42c8031804291101d40c207544007003440d4041d503030580300750502903060b03540060020080301e143c100c0c102c0d050600d40d00c12500d0b0300c0081c040c0c00030001007080c607100c0c004181403c88000d240c00c483e200006000c0c3e1003540121002c1c000040001801988200400700541 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 57558960 1250 57557710 57557771
    0x19060810020d061a1306020303060904030e01090305060a0207060b0a030305071712150f040506030d0f0e030a050d0212070b04060911030a0602041508040c03020d020d0c0f031106120a 80
    0x103a40130400d034031890b0000129000628201c100000d00c146c40001668003c071402844035003117468aa405950240d0142c6100c1c2c1840000040000820400c1c00030a116000044015070354204030b15004088482010701103200d035030005030503c0070980c42800e59440d2130b03003c036405030100907004026045010b17150141c4a400c21640400c070b071181d810020000e80341c0060700d112505140c10404c100c142d03201242c0a41d0185d00050300000214841c0468201018943c00c200074141c910b800880d013441c2e2050000d55155002c450001a80c6604015041c1031908501e074284c284202036403420704c00100604064a23070781c1c403070300c1e1302c014803201d100040e03090305008084500e011101d1030003401941042c410103401524420343c5c10328403070060804034812503001c1d0341414518251781c00c000403a202051f00766044a40102c40d24000340310040014042d05070820441ca0b024a140750031000480d008148900410f81400015140e043e402d48440d00080700d020301203080aa030901e0b12400410022211805 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 57560210 1250 57558960 57558989
    0x1805061c020a030605041a0d060506060d18020f060c07030b065406090c131202030d050f0d050601021f0506130603030206040f05011d0619060810020d06 67
    0x2e5030558000742c111501920244802219994034000481002c005140c1007260302028030002411a80000c0d0b009000400050406030020390303402c22120720403105854940000000419490060303001c070040c407022911245400180f482007030721119507200007813458281e9404142c1503610b400b0b41c1c007180000780a41070100000114403071404081c4188584546916000441e180c44800024000c0501103403103481e800d40705d80003403142032070f001480d1060000b03041c09a05103114049414000400141c11205038086440c0100b60401540e11341000034408108841c403420200708040e101041940040000c0aa0f00c03071740142d040464807070020311000c5070703100310032083c0c1440d038410340c0190410382c2d94842c41c55254040030221103540c000640540d001d500054001140d88c254400a580700d00b0021640c2c6a174200e102000800607580412550450410408546981450807a00d494084c02c144003492800080c0c030b4454182d040e406542c01c2e00000d0008231b8081311303040710005241860038400c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 57561460 1250 57560210 57560227
    0x14030702030a08070e010504050f0a0902030412020c01020303040c0509060d1403040e060402090a030f0602040f060801060201050604270804030507140307090605060a030f140109050a06061805061c02 87
    0x1240d82c412903100b00820895000305804a05c18005d4456018042c2c50706171074a424402088510a511400d4641c000b40c0d01501141d00603040c0040c40c021446040e460603101c50700703540a814452641d0a241c11503009004010103e110000d410045075000e0720040419224100442c00440e00310388081c0c00031110742240e132100d901c0040100112025002d51041c0ca4a4650400c810b034071414800c075500c400e03101d009002161005140154103071040a005140541d5203015004c101d2481d880540400c0341c0380e0040014070780a0007000d0348400100c80c20019913003030381d01801c1c0d80c00095412110000e65100d2050810400c0c0d011100271b9034002023225001a03480080c456031819240c032050203030194400c0005c804003d8010f2606440c0014146801d000060204070f00805002e98080529030325000c5040710040750002e018060141c82001060350b280c180720440039a4002e03031000080040f03030003034220500d001d507141c0000e40d00c1c1102d22691310700c181d451100d06040c604801c04022031000800a1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 57562710 1250 57561460 57561463
    0xb040c2319050a110d08061e0904031d031b0a06080702030414040204170c190b04090509010204080f0609061006050a0c0311070b030f010e010302100f14030702 70
    0x180d104460105199502003000000802401990020000395104180040d41036010b10050301901c0c4091800d84e01082e4107001e12881d03c00e0001110020503886414845641052010108010822030021a6004101e000300c0c5011400500103010806c1022070042d074a00d0700707080342c90074030001012104056000c080d00f603004032000c14118412080000000340ca5401180b005205050729000341d8209403a181c24810250b5400d85003d40c080c3d0700f0000400d4111404850f042c1c441400d40003081503810b03881c10b10440c418442120f6a0074144140b04000700c01d1481d044034261164018085855250381000d6800790250350851200390050307c0510350520000602c5134420070421088410540320340a2040800307016000d80000950f00700031903015076001d10100d1501ca0b2007480c04541e00c0700e0340d42d081800e04907280c0142030f000340c0c0001072000d00d07002d1004080c05441120a404c80715495603000031840c81980f009107003884038403282d40351100c0c000c111164000613075a60080d0b5a180c11840207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 57563960 1250 57562710 57562727
    0x30904110405040e150f060d0b0403050706050405060907050a05060d09020a0305010c020303070215010e0601080601020a0b1003030e0906010c1b090203011409070e060405060c030417070810141305010b040c 90
    0x901c60580d01c00005043d007480041b500d000300b4014145903090b42c0e09840b600000100140242c00f0f001c0200403000004103a4414180300b9405040501158100903400d0b07403c03c0150741c0043e100d5140c16406100540e9a03400315030303201000c144006000d01c1c032840450030700710460b80080c00551822042000494003c0015482542c460b820b41da0002e5100001039044d180031f000354000d402c001c60000d2520350003400d459400c501e050044440c1e84003240d8821425800841d100c40701c000d0000410170030550444a0f6001c40c2c00111781c41051450400c000814a101c0c124000d415041250031201101460444003005840700490035582e940e140c5401c2280040100c00c0c0501a02c2d1080000f500144a5100c0d4480c440000380590302d00f5203003004000c4660060740001e070485c041040002203c00b41070800840305c1c40908040c010851400300c8090600500420010304036082148150550b4440780c2080c2d845240c0c01c064000441060804d5401032041908a503005454581c41820260300000391 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 57565210 1250 57563960 57563983
    0x102316020907090e040609030c02032a01020303011809080c03030403030504140316020f01050d1d06071b03031802091302120f0604080307020a0b040303020d06050402090102030904110405040e 84
    0x1040450701c030007030216140c09882c0b0820100141340c1010070002103142d04108109806031610305072580c2039400280c2005900b0a100020028903452590403c600005524441c20b090000d03505540c544a0810507a039881d06a858900340c0e150032500400082c00207690b0041c14000c100d0361246401e11703001d8024001036030b095a8000e030721125407182800000c1240c424a0049064103003e144903401d0243c5a50361501090601c14140118200c210803880f4074a13030b02c00d144400541d902c1c070601e00d10b8203000000e4031305010802c00740600301200c00c0c80c960500a85074103150001d542030b900608818801c211050095006001e001807280680c404100141c80e80d0007200d00e50110b2900e1074505681c0c2040300c030008030075000140010041a9048041c650010540c01613032031541c8180c0e20010f80354011a401c40100f980811030754400c18a40c40b4035000350a040c0c13000c40c50100704030000307956800340544862150341c42d500c1c0c002d0025483c8045e50001c020180003444024802d80180e034a07034000c0b405 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 57566460 1250 57565210 57565219
    0xd0b030a1b0e060a140112020c0d03050a0b010c120f0306090f1b0e010215040507030203010e0318030a11100905130905160e190b090c0301050f09040210231602 70
    0x2060140ca415404c0c80308035400d002406400c1d010000044d11104000c55800c1c0c60b442c0e01f4851501400401d004090b80c1c00ca150340c0000d0366140829045085407526210b180c108900d020b0080c002038011480c1c2c40c90031095050840c5542a000c1040b001f904031070b0801507800e401c0c070440c01ca030744050360131000c142003800e50200c410005020007121111343c15070005005a000c0080442c440e003111820355003060107041039402c1680c49401090940e40300001001c00e270340c0001603002c00e285a110126040780c0c0200c01a000e840040c0d11500241072010b05001d100d50410030030208141c6c02144444010f0402501410310300402c45c8620009007a400303810b4415006985403c4a1121010603402c2607d618881180723464403441c404140060340032404424496842842d8100d40d9a440c050724404c03d014001203660390b040c403090241804518a00b40d010340740d48411b110044c0c0d510165200082d00c1d6141036020444945d9604812900714070039520b1204000407948000d10f08a900c0c070800c64000d55 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 57567710 1250 57566460 57566489
    0x12020903010920010c150c0302040e040503090a0806190f0e01090c0504060b12130c030501060b030402120a0f02060a020c0a090e0d02070303090902090a09051305060106030b01050d0b030a1b 83
    0x2001517071864030041008003405422075040c03480204d907500c18020b0203900d00c0c0041c201600caa4402d0764041d000e450a0b1400e502c0480c00b82c0180c60302c001000c0180115502408030b03410701031a41c200c2e41d080c20394128195921002130008148480d03200e007001d00d00307820080c4aa03998030b0802d510003d605004080c0905d00b00f450218802001108070359009442040c0ca4001c1e82c3d484903a5608441d881c42d049031100540d91000000c41d000340100805055402410ad503a810184104440c1c01c4108210303203100d4000c14030100c0403074852200c003600340e5019940c95503190b101c0b060803801d0624810710552301040d9804040340072400c9078404568050301c00700f00d0b48141c662031410b07607a070603061000600266520209002c80c0c410350300604011000a071007110340c181c803240d1a80c2640d200b151b2801280044110050520004026240c01400c482c24200700d00c0c0302900000305984a814880741c01036032a104129100c1d1010810b070600d01c0e8000014606010081c445008000c2140c86400d10414060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 57568960 1250 57567710 57567773
    0x1a03011505040b1816031d03130f030209040311010b04140a0b030109080313110d060c02010b0a1a0702030f03070311070e070f08071119200a0303120209030109 70
    0x9092003203c542c408041840130f9076520840489480705c0c01803000c02c16440c2c4ca088070070a8044820018660300490186884d1a50030390742d84d13504400c5907c0395100b0004880c040025031100ca61803904180c0610f4101c4141130f003c406140035140c11068150458941354078081054141e002d02402030f400c00d441807041c000210101820f8074040c0c0c00150003154201301007840000e44841d20703010280300d070785044160503840d0009000c0700c2c11440c05840b007503195000905055030a100300140610100c0b240c42d11707282410041c100070b10195050581c681b03c0010800305550302080500103102c221004c41707076240603e00c1c0060041101201640c50340c4a06640030440074071040c0b00030f01c50320140c0e444500d410410340c1308a0b540900075100c4401c1c080b4424162100300d07024031000c4920b110020903606113040628081340340c04001b000944252000100c2040709660b0340000b00704580d010702c1c0000c09500c400c90342400030300c110300c0d51661540c40c0c001000101f0811901c2c1844004030613800d0b080c2c08842 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 57570210 1250 57568960 57568969
    0x201060302010905040c270f0b031f0803040b0a0212030a021e09090c071a0703051008030f0906070203070906090507080112020a05150904020c1e030403080d1a03011505040b 76
    0xf206c9000020440201d0040b402d00c028144a81100b540f04030010900f5580d00380401c0c40d21a0740e000b045100030b00004100c0d40d0141c106940304041b402282c41c442d094603090070300e03843c3d0043e40156980b9401c0060090340070b81c03081201403004400b031004c0c03e54909120b0001c000039440b0b80ca000c0d001450001642c40854428000c3d100c0b1100060000b28040ea64102c00300035550250f0000c6446000c90304800c40c101d441c501040d48200416103000605040c01c2d10500c4200c0c80079030214000303a2040211442d1400940c041d507581c418181c1d69140c440c541440040d0400440b40c0050072000d01d41240000e542d44a5040f6074081c070802e032182007043e600c81c041c411402c80070080194100400d0f0404011501741002d0122080701c0204011b401c045042d0000b9090f60702c50207401880390f10503c0e881c9000320300040f10b16141203903900110320300303481e554480c2a42c0c0101d01802600c0b5507600542e0313414085c0d1000f000c84408004008104590070f250440c0500513480c007410f4000c9191042000071400c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 57571460 1250 57570210 57570221
    0x121008060c04060509041e0c03181110030e0303040f17030411150903010c050c060609010e0703020f040302040204150201050105060c10020313020406080a03020f0a2f090106020106030201090504 85
    0x3508400c0c20300c0c2a04100f019680c551100002c150000d40d0303030603490003000203143c00f41d100c40788400c0080760205d06100010281e4848111300701500898000403030020308400c400303c0205e0820740e03840102440c600300c250010408581600614000041000304004a10101d000054031800240b03100d0020038405039621300007120000c10080c1e18880c0d8500303610b00b0900440c4244031403c0380f41d00c2e00850802003070a46001d4400c075000b04002180f07060081500b401855405502a25002ca0640c5480c0c2d54502d042c42c00740000080c0b50303001a00710000348800f01120051600640107544c0d035541c8420004e182580d90300c0d03480065190030b002140c00e180200c120384140320000000c0141c1550140701c28001d40c0f001d0803d000d0b8031300d450020360058449003c1c09008103400c0000d00300014450a01030708101c544603000426400007007224000944c2a81c090a415807045203907812600c1400100386204c0a2101c2c080c0c1c0010b2250001954136415002101500d100fa44c4000c4034503568030610050b0b07030303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 57572710 1250 57571460 57571471
    0x605090604050105070f0602040611010b0904050d080901090b16030b010903081b0c04050903030405060708091005070c020d0b150103021305010e0a0905010909062304110102011112100806 82
    0x30401042002d5071255000d821114005c0c0c034041c05118281e55094201d0780030f948031b4400b02d81c107101c190002d10000e1240c108100815201c1d0300e03807460035541300341d06e541010600c0c1c0c0c02c1c481100041044a042588240c9015902402c1c0c07500380d090403613a07440d00c22101000c040c0040d040003028085540b003070101000b166417088e41541005200031461041e9056070b000240a0320807040d0303003a443e95523806110f000d0a001c030040c50f81c0741010f003461400d280c00100030400f4441c01600b0301c03c0907500068a00180d44403040b000070030746c5035014125103840030700c44080d42c4858880b6080e0107101c105809280249519074108000840c080d00540a9016110205011901c4020200001d5000306a15485010000c0c40800a25101c3c0b00e84421a1400e070804402e580d03803800381d50104071040c4552039501549104004000c400010124002d100c0144004c08506030880740c900b107a4000d40020240b0030b0354507100c94540c1010810104554021100071425000545000907000e4002caa01d40c01130 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 57573960 1250 57572710 57572719
    0x10903020c060315090117010c0c031713050a0528020a090e010e030a020a1101030207021e0402130314060f24010e04060902091203031909080903060403090906060509 73
    0x10048000b04141074000800b5100c84001c10310301c4080c1d5940b1010400d001c0c0904011342000c9100200c003181c21108074450100a03c44495036140200b45c00c416101c80c841c4484000062a940e400e110340d04100d0500c40003046031140c11440401c01501240111405444500c024828078100c3c4101241004504000c0d4106c91142c1040c090202700307421901e40380044000203c4d06c903444151003459644009521801038020f08112001c101021000c0c00c0000824030f030560400000c1d400040401000020303000007140c0280520580e515542c0554000750040716070290302c55564102600c4070001f80201c100f043c065030303000032100b40007081c0c080d004000d1000c1e280c0010392014202100c982c0415902414020341d403244c410161303628066040900001d81016841e40c150600f8000c000c0300030b1a1081391900b042c002c2003401d449025400b420f5060070f90000c07400300041d080c4010301e03200b9859030300d07050b0240c1401c2009064222455a0450700c0e21501081200d944d010110ba9a000f500c0d000b5500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 57575210 1250 57573960 57573973
    0x60c081603150e040302070306140c0d0536010f0c0f08071404030804050907020a0203060a02160c060e01080a02070b01260d090602010f182901030f0209070201090302 73
    0xa5407090b4008000411002801003103a6200c03011071501803011641100142d100c20010f00401c10140940310003d107030b03040c0c801c11a05100d504489940164009040c01640d5032000800d002000502407209101c207125290000c401d0807104140c0c021980c3d5810400d43c03c00c07504290809c003174424500409442e903908030f440c50a4940803103882c0c0780030b0706120130082c8100c0c02c5c004240d09440140300651140141694561400003031041d00040201481300359002040f044000d0380b00460020b41c0116100001655824425484000710755840b0001c1c1500300040c1012440c10342081000e08200801d80351114140e0700c00010f08141c3c480c3d2140100080200bc00401030608502c011000d028036041601038441001d90041d8540003020901d00f0015020040800181e90284181182404403c01c03d100b0700507695440115130040c800c00401c03510443c02501c0030700380508405071030b400c7e05030000120355a580c1000b41110104003410782c8038400407000b140c1c0c464014805d004415915802800c00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 57576460 1250 57575210 57575251
    0xa050306190b0105041701020301060e030a0314031009090b040b010e190b010e06031014040e03030c0d02070b0907030c0b030601080402010f02010b19030c06020102030603060c07020307090203040807060c08 90
    0xd841d0100700d0303506101d13041c0004501000401c2e150201000580700050b129890084020801d44d6001e1500b400381c0c101c180c900f03001c02e074015101509988552a165a25101c070b0070581d18100185e40203000007460300d03095804000c2c00c8062103020324041d02c2401d2907645c803190503c00552060300c500d200a4a10310300c1004041041d00300d2035040b50b0505082d43c00c0c3c80d01d503000c11f00741d03407040360385081003036017aa8113000c400c0301c0017003a800c8000c00b69810882e80301c0c9488030320b071b581c8405040016003900110704d820460348260102c540c007651100c4000d0007402c080c04084d60705c92050104503183c03c40840041040e0003070005a91142c135050f514000305403204c0e00152000070324500d9074030455495400c803000e56142c2c1041082000c001e101001b49140c610f04088802000e45e0700310f8000c6900400c1440601d80d00081c2440d00b0200548035260b4a0945100181c0b9100c0150305c2505450300100401c424171080b04050101140266014441d02d2041d034400c031840c803c01c80e00400401d07400714a808 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 57577710 1250 57576460 57576511
    0x602160e070221070b090c01050d05130f030203121317091809030702190f15030e010609050a0b010c05030a030213050604080c1002010504080403020105031e150a050306 74
    0x40e00012180141e5210084103d0b0038848065114164000d50900181c1d401c01c000038180d250307502c0310030240680003800d8144002406403180186121803d40c9900116007088040311070500c049a101d108012801d0301440d02075142d03044008914420402400091842907030781059107130444e030013004030382c041c6a072100c514002e401041d076964108082c412500c42c4210640600f0b8007504082008649032905132040280c8041594122001500701940801146a041c10072100b51051510f01d4030080c0c4450038110010301d07902090030300079803d0003c009a0703408941c1c440c1d409031888040c144980c1203010010740b070380c60400c02d0090a6038010090261024420b074098140ba481c94421802e02d595038a0010b09140c00941286219802c03500720803013503182240d01b20b41e12180c140000d00c10707481c01b9101c00006001d05c0c40064103201e0004001521056510401d407465900c40580007101d0421055503900c00c2000688940a4024040c3c00b050034603001400a2142e00d0070010307021031014020041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 57578960 1250 57577710 57577739
    0x105090a020309190809030c01050408060103080708120f0f06010c0506010e0603160b0a0921060f020c01090b010602281511040b0909010b090108070e1207030606080106060216 77
    0x4001030b000e83c80071070200e628a644c0e00466213019080480d16142000100b60621221110041c14410204002c000c0f45402068140c1129000200c403a00c0b040581007150703180c41031031406583c020b4102e040081c02002214864000c98038540d21980c1591004019150403a2011001d031150f40040b0041100100105a0513030204020f020380f008001c540d1190220b42080c5d410401244c500400e041c101e66070b1100d030440041a1500882d001c0700210111003229500040019003415100e159036a851001a0122540200290004c02140440e414510b140c1c9000b03018040040c06405d5218007501201c00d0700854000481a003041c00080540e1118070442305003a10400c4513480e0100c0d00607040350080513000034140c6d5080c0070340d00e14007203040060501058100c11803000c014001c1d02c0c99640d111498a5200015007840ca00d4144a00000340d1050030100301481140300c0e0103030200030002680c1192045540110091120035100c04e01642c80d850028a80d01c1e42c1704503007504104401104800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 57580210 1250 57578960 57578971
    0x120f0c0c06062209060f0b06130308030619030302060403030c02071a1315081e07080604051009181104060e1303140a17130804052214070809060105090a0203 69
    0x81d011075501107591010f44e4500041651040c3ea40c1002c0e0303070b50340701c18041c2c1e10300e12000f2242c0d20b1030442d0090b03080004103110302003d42140f0011000401a85034000300b61540d040c02160300c030307031307107640c1d10b0300070340d2184c0882c1d0880000742020980d46145000144600070350300c100b411414035004040c4c58841640216001400d040018100041d11004910241220210f150b490030000c0c5041d01c1d40030341da83c1c030405480810110841c20040c0319680904056000f0604a0300402d04e915040c50b0100d503807100350003078140c0390300c0d050303101101d0392520702103481c1c5601c190006113441b0106000c01084900d18460a1220707110400010350320405e1140c0010b40e00d10038140380400c614000d02d80306083d009056000086552080c40c1d0a00c08400b00e4010b80c402c1c11180741802c4a411640e40040310300481c41002d0054040c0e400031107a492804204040351303510f4840c104004003010321520b40c8158196120f10100d0341580210b04050004184503040c0c8034007030841a15512400100c00c000d502c020074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 57581460 1250 57580210 57580249
    0x10207080a030605030618060609090a0501050108030a110109110418060903021f020c0a02100507051203040c06080103050604111f0306080706030c0e1003060b120f0c0c0606 76
    0x1000000c640501034001440e2075500000c03000e00344801d1500c0c0600107014520070103040440a0302d107080000d102c5601441c299580100d54541c1c242946c98140c041310010301b40c1d400c00001054014000000c1e11540f80903075211b018030850009114200c0e0103042d4094082c444200c80031802c0e0419802ca0070990b84500a089840400b40c1c4500080356400d04048006801c41c0e030407224050b4003003008100c520311400085207843d242501460341d0340440e590090260010385052510180a6016103d0203508842960b4902000380da1034181540304440403036091040e040c0204801f03100e96a414140c0758000b0082c035840d1141d44030082440b81e01d001d119409080748a44000c03080611040388480202600c0100b149401c01d8606400c7c5480781e00a60201494100d04840003544140454584c0805171042401e600346c280c000c90161850360800080040700081c0ea48454441000080c4542000c6c010180d450301c82c00038002c024420041d29180b581c0c024804102c191811405070010201c0c90310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 57582710 1250 57581460 57581467
    0x4030f0f080705030304030909050a0501120b06011107080a0221060106030b0402040b07030305040302060115090905040c0e27030301030305041403010f0e03070302010b0a1508220b09010b0405010e01170102 90
    0x1901c0f00e2540c0d0085508078002220f9a20030484c01c12140212500091030150501007036050442c00d10080003a00c01c060700b041d405101054959004512800400c1d0001741641e0f2a01d0301c0d1003100d80d4408032508100c3c02408500c4c1c81d015a13a0340900c110700c510380030002a0803142d180401c00c801a00120720050f80c495400c200c0004d08054645c02000071380d05c2510f002c80c552406041c06414203805901c0f4510038418222030000c42644814480280d4003182070010f01c80d200c5080104450200c0d8010444072101c0200784100c010152a01c001c4400c810301c0c2d4540316107003c40007217403680820711008021820030721050200c1c18240388200cac12044043c00018a480304417644209981c0c0029000c415504002542c1041c5542030181a002c12005d4034a20592803504110b021403410f0301500404104100011840c8007440002c814030110020400c21f61014250421040703601058a0754003180d880e0a508601d142428004d5504a450590404105071b29010382c4c0510780c1603054110005540c00c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 57583960 1250 57582710 57582713
    0x1113050109390807050c0106090506090a0506010905060706140403050c06090708120a030207050106090e0c010203040803032a0703090e01060e0d0219030b010806040b06030f060a150503030a120b040204030f0f0807 93
    0x234420301c0000c05141ca03000c582400c101c001c0c0703d91080082e0141000900b403900700132207030f6000320342d0104803141034801c00d56511440c10403400800c5083d400a403c4501c440070301080c10ba01c9000391140c240342109a410301d031142c48409036a14031a1140072a00e0300980005803c821009000d04183c00c1c03241000340c0b0b80045944c0f6182120a035400c1041d6843d41d4018088480e881088032102204c02800210701c0d1604044100d560381c00014108504c101f000b440d480010522002440a109801c1c4141a224081c1c0d00d4040e1030100e00f8021030554145840001030800c0c4101c180342200900505841544140d94003400940480e032400c00c03120042c180d00000000314400201802001c0c441c0140049003050b2414502c9120b004d05214829804042880c01c0c1c0100481c21581003071a40d43c00040d034004a05002000e6403140e13000c0d6a050001103064440103420103180c60b04004000010003c443e946010002240900d010260294002d6900072001404480c11425818000c0718000e041c100746 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 57585210 1250 57583960 57583963
    0xc21050c21060a0606090f0e060d0f02030304080d0e04060303120504051c03090506060102010207020a0b03100302120f06060a18020f070609030c0302060109050c071113050109390807050c 82
    0x580301803d540c2c1e514042041301c254440c00030b0028103001e03034030300039203070b150074001201030401500310b1b40b1505008008008000c40e40305c0c10045507a018090b0f07034445944844254688514101c000080b0b60b140f410508075203042d1103400103803641602c50041485940c20018024100140211004d128108400f0340c4400840e0600e00c200b00d081d580800c1409803860710504228010704141e05580c014008240160380b8403d0103015075480d035a4460301c9a43d03d007954081d240f1113500c0650444400500040301e0000030074502c890f04904001c0340d40d1600c41d501813000e088042e224006e0881c1c0c400000070071540c60341e0001e00c071a1900d070a4007400d00d196604e62404640b84164101c2c0405e421240700020550140300040c01028903d2040101d841e0888401616210303c01000b44110b8600c803a00c030b859a1610480c07a41e0800d0302004001035030f110f105450062000b0081c2041c080a101820314174842007002d03011050484090350040e80620314410b54201c0c03800340031002805414045203645050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 57586460 1250 57585210 57585223
    0x1b030c05011508071a04150e040f0501050306370605060309030a121b0e010201090b09010506012c120316260702010905100302040807030c21050c21 65
    0x500248400b111450300c0503143c90496603911480180041d04c3c003c50480c00720400b6202104d0b0805e0710080721b1083d0480444000e45054119070788149031540a24400c4c0711382e0f200d641680c000b9821103010b07032141e141d00c048541202050001100310740e071581e00402500220480000000207020900ea501c45001440541080301e0140103a400400d03140e000d81c4c3e100e4022481201400303401c100b800351000108083c3c400041d9842c0900040c40101601c0c0e074401d622409410b904079400d030901d4240700c0003290103400c054419a00242249091111000c8481016890400943c0707290700319404500500c45104001c48a03001c2d180024001920200083c080c01181d40c2c1c401c07845d031190300c942d40117002c44030742c0000c000c0409400e05110140050b60800e81c0395040d5142110b0400340490101021000303031040341c10181c1103004040300041084101d460003006c2d1100907044074402c59401501d2245132001c8400940980d01c807d18034222410105104405240246801002c80f01070301400e030301c1c102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 57587710 1250 57586460 57586481
    0xf01360302041e05011205030f0703051c0f06060e0609132717071a06060c0a03050c0120040b0f0702040606020c0a0b03070f0e1219030305090109031b030c0501 70
    0x20502c000180b001c3c942d91040b02c1c00341c159031140144181c2c075601e07000c0d5a8001e0018070781844500150040501d800b0740240e0340402802c0a000c05034441c60340d211000790900c0081401c0c81030030034201084060242d505005825405407409060030100805c20000c61903504d419001e5550f201c0f01e20303c8001c05248001540c101d101b00d500d14614084c50000415075114100501000d0144441c0f00040e85020603409540940201c4007101e40341c940008502d8402c004081150344603840d4070008068001d0084c01460f421340000f0403400181030301420002c02028a403014105d003c01c001d00483d207154000d0200740d2a65105203050460a60119084030b072a9001400540d00204d40c00c922450140d4408002d440f9144e81c50b4214141000042c1a1003100d1000b5802e000405001d9102625241d01981c1100300410440d1041038550452240c1c10f12203c6098000070f0500001580f05c080502510401e40d5240d0341d82507500c180c01d6034018030108180300450401c01d29284010124600b40079950307010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 57588960 1250 57587710 57587741
    0x20c0706080f09060402090f07030b10020706090f0302060a18030c0b0304050c0102010e0607030b060702100302040512070605040b03040204020d0f06050445060e07050f0136030204 79
    0x2d08182c500c08010050060440c00540d10010070480140c031402e0b14260080d100d07034100300c2d00340c0300c64074181e007c0c001c030f407107210741080142a0700b01e001e56000400718100d40194480c40c0e101901d58603043c07030030411800b02030340064082042054851087c00905016038000c0d40c5105843d80f25902c9983c00401e03540210504000032040c4014808280040600954240020001d100356002c0854440200901100c14980d4840e42900161901421030701c280d54010060140b8080a03440a80207400502071540100c1c075090b040d0400c10030004d2610300b0745405860b10f40c2054602031080800781d0004008a030019028048007043c01400e0003070032103901c00290086a240c0c24107040c0021a40d0001000320040c0c0400e895022504e0316600442c68582c009151403011403609981114846000b20000d040301e2600c500038154201c04260482075480482c1e90a900002c04c100464400c0c40e585d100d90301010002e6401a6854115160b03500c41030403841481a03041d96030380002e0201d403800c588140e550f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 57590210 1250 57588960 57588977
    0x3040602070c0501020a020d021924080906090a0b0c0c030c010f0b010e06040b0307021603050a03020606040623030f070816081f0e03071707020a060201110a030f020c0706 75
    0x2c2002400014001e09420300c0185505042a00069814020000c0c06409030b02c0c000d20389864540308174200806465604524180c20006a10741c50540b100760b4500800036801364081503081c40c010540600500880c8000e0035040420b840d0014680d00281100c503143c80100310034038403010107201602d00e41e80a50000640c1018880b0702070252000286403038100030505003512803564600c2c1c103540c240d440090303080752245e417100c00503842c124a03842006680e200f00780c000401c10400084c011040c2d84203a00b03443c00c0342c0702d000c14403081c4d550318026001c80f40c00400c1044024080c502c004060b0420080407510140d00c1d41717001e50b04101603600005c8040e0409280c0c2c900d51030220070144001e00c082d00c02021940ba14078800900c021242e80607000b0070391a035258899110080059a01030b68004040b80801e0b80044030000d0301e580703c400100d00808000d90700190050040c4103440c0071410401c402840d1011001044006140310300010400c5a800d1240441c410005c00070003000e002d00f500c03503100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 57591460 1250 57590210 57590213
    0x6070e0a0317030405070905060a0303110114090601080705010302090f0123031008010501120302030301150905060d02030f0a1a0f04020d0c0503010303020f0c0112050c122d090a02010c15020304060207 88
    0x3003006d26001109901c0c20501480f10036111080c0000c102d94051030070b66040c050340940386000d44880e41c1001c0c0d00710140c1c401e20544e45d00c003003a1329048412000403280d40a07502c3e00190240e00a64900c154004029840c00303203954020820344a0181080d00380d00340b6441000007a072529041991a043d0307100b00c01ca03041c80b040600b407080c58091b185514001001da603003036800030365070303c01405207191441e00c0e050100c7c0300c0760280314090060322000700f120303845010001c460300c005d420031200082700c4402ca901094024820388640030001d013001d0700030711415130301760180003100d10000c14040d0015803c1000d018080603620035050354888540d10701d1359079451418001d180480a2a1120560704542d42030002c0e80c0e007019442130700d000c1076100480c0b5540e40311034152881c0207640ea05422040e98408020040846901d008205900f1001d07208400b50740206400c1c1c14901280d40141690040151a02560041020003d05449030702a103060190f8100c0d28410f03a0002d82d0101d0351107801141440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 57592710 1250 57591460 57591463
    0x82d0405040c0905031c090b04090b0a140306040308060f042c03030709060e0409060c08060909070303020703110a03020a0f050108160e010c050c060f0301081c0206070e0a0317030405 80
    0x441ca21803880c0031210f050404002a844400e10404072204d80c0401d80c03545009070040c04080d00400c20804256100c0740c0d6801d0100140038048101032158440d40004a0b5041102038411604100039005001a5075196030a0700e0300300004c0c2c5129402a0b9070032041c00c3c01e94440c044c42d1403240c0441140b0007800750b001c0d4030b02001503022100d800c040e0000d1081040d01030380003116030211030440c5000762030302c2000d9001c5001800103501c050f24440c10f0241a20185800c1030607607005103000d5402c820b0960b036400c4800d031601c00c58040100160030810302040810000848005070002c0141282c41c11a905da002034032881c050342c440100418500307030411243d070b00071400c40e40c800c40101c6014030081429a00512160311260700c541407201110034441806070802500c0081c1201030a00c3c0e954062180080e08250030901c107040480c843e90454004003140414485100301c0b0369001041d890b1a250001e603041820040d00030303008213042e0f02c004040703601078580c17074045220007000c00d40d282410705005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 57593960 1250 57592710 57592721
    0x40305090d111e1003090804050406090c080a020a0e01120213120b0601050702100804060f02180307050a050f1507050d051b010626010e060406060f09090f082d040504 73
    0x18051070004003441c29140c4880c003680700c144001340350000d4000011f01d0294418065900100d8000340b5000002c160030400d940036503070080b8241c0303a031700d000e80e1000c02d8441603120780301100c2e00041d898209030b501385d40204012000e000c111740016060a502c40d03030241402c1c40560000c5417000c9200e94803c00c1c802c80c2c44003d901700da020702c3d1141c5492140d4001c00e15551440d5105002c1102d400001402e20440e98405006240c02407420740d030700c029024408000c201340d10211803007402401000212450404000c4003100c401502030614542c1180403c0003420580d60040d03100c5c0c1040181c030002407003d000c49027a9403119120f080d140e80c200d8034240003909800c61401c44681c075080d0305001c030300700c18404446000c08a40c070f0200b4600d90000c0c090301400d01b05150000610889041c40100403081d0002e01c29184d11840d1513000c203079200c00e44016210402d00140800c41540030364008104070000a110402c07040b81d41600300b40601e080d80030f4034004181807801b08180403030140258500740c001c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 57595210 1250 57593960 57593989
    0x6020706180317031617010e090f0f1606080907050d030c140304090501050906130c051204080a03051b0301060e0a05310207052a030303070305090c0405040503090405040305090d11 79
    0x1600030000c8015442450818001c200c003d07644100002e040311401c014ad006400c04800603101003101d101840c6603184041800c440b4203000b8500013080c45842403440d1441380b80c044c0c0040c00c08a28007001c0c041d880d004000d05038200b065003460703031010500742c102103c150302043d00150b0391189003d00f0301c1c0c100d40c0c060f00160b11445e00e0000b442a266102e544594025459000c0041c0c6400d044000ba9a503204803441300da5190503002c1040140070914028241c000401e440900031a91031584007840900c0481c0680110001440103011051044d0184081c8400140c02c03d04056210b100280011102055400b41c103c80ca4003c9280540c960b01c4444280304c0600c4d056007840c10954a4a840303c580303400c82d4200c42d084503500e000c1410416401d080c070003005400c0d25500d0409820040142004a42144091107141c801004506141c491280300d244c0020140d070a180e40c240030800a0107019000360704006052150869035621150094160381c403030307400104505100c0d014400402c090060 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 57596460 1250 57595210 57595217
    0x10801050a0c050703120b040c1d0607031b051203091c020607020a03210606020f0f06071407050f01110a090b030c0405060c0a0b0a060503010b0307060207061803170316 74
    0x44003040c043d00401550441649810031050601c8248041c0005049103480d0a5002c0d0401d50307d07804242c3c101034070011142203c0003094143c0c006000380051131140070b100078009165030309481e0049898000407203082e48103405403941e013501031800a082c0c0d00180d0f6100350a0300010007031345600010200300a2503085600242103149445280a502c0718803048018051082000850050101072801481c81031100001040000e4640d20000c0d03440780310b540030040c58401c8d03007140b4002420001da0680305240783e5a40e600c280c07443c04400c25151b044150122458031501100040c000d000707014100550030f0340d8140c1c41d20f603507504a004281091a0340210b203480317020014410b80703080030b07003c5034181c41c0f054400d1070356018010385c0300e8540f4a64400c0944071300e074080300b4031814507910740241044030341c114000e0042e482c0c0c000800d5110328143c8928030260307001540c2044035a00a424042ca049104101d480b6680c0d80c940f9515910618034500e032007c80e03c00401c00140f00d141c841e40d07200e507010514 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 57597710 1250 57596460 57596471
    0x3010c08060d0503090301060303020a0c08011a040b010216030b1603020301080d050708040e01121205030610080a0b03060903040e09120a0810051309050105010602150a050702070b030708010801050a 87
    0x1500a0600c6102411007030050100b11a81d20900404000f1626040c00c050000c0010382c0d071702c0c00d00945540442e48100e034030750344501c00064505414058002c1420000316200e804064a0080100030000341190741d055005100034004c40c000360b408084000c6010320183c0b01c00346482082204c000d24504c00c00c80a051062005016800f400640c2c0b83c903a1a071400c1440e41c8203590304044442d03016a0f401407000c004d0340000840ca54181c0c04c0040303115480f420303181c02801c050302070566060104688994105d0a4070b10141010b900c110717030784d1790000014040002c04001560102c0d052000495101d03149500014040010120401c001c69004100d2000b515190403951441c0e0401c0c814402648104808003002c1205900181140001082d00070046003c080d0102c0c240c00c0500364000c0c00740c505e5468480000307034050020030900e0948800c1e4030801059540e40d00300c20700802001e0000411131041ea40017207440c007035990046001d8550703604c2300b034599071400b0a0a13083d00e60041407040000c1c1000d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 57598960 1250 57597710 57597731
    0x40f05010e0607031b0c0b04050703081c0c0918050c0d060603090209100e16050405220b06040513020d06050904210f0906050a030b030d0e04050112022d060d0e0c0301 73
    0x503411ba940d010f80000302c1a2110f051851400070281c10142c50408005a408620109a4204005404404800e04c5161103600c2c00355001c440711300c00e182400010000c86444008a0f5100c9913112005100203810004001c1050040b038090b500124080707a9150b59040552400203c4c41c0e030309c019007040480c580c40c28104008250100900f02010881c15518000081400303001690003904000c1d0080140400f01600144040401030310002c0551030003196032030504207403085405503540607140c95006a050810800258070014160301120b95074100440c103551418804c0380528002c60700c1c90004807164081c1d5940c0060001c80d1000d00c4a003104800c602c81d00214003c04070360340303814401d4544604950540c041c01d0003c060551602403040042c06650300042c3c5240382c0e480640e01041941e8035689402d41032200303010065480400460130401002051040c1103010303007081d002c00c0040c03488102190345904084034164205850740d50340c0849041c2080705e00c1621801302c0007403040f403100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 57600210 1250 57598960 57598967
    0xf05030d05040b030a180c150806011d04060506040303082212080a0b1801090e0304050a05040c020a080f030109140708010608072303220b010905040f05010e0607031b 73
    0x1140719042503d5404400a0100c1500da4040c0e00d00314440800c0160044240c90b0200007030005010301202e10300d00000001c2c1285c81500744078400c3c031041e103d0681119042420090000c07040b110950b01a86424001c2001c0e20742c031001d04000d40c800e45070140300342417013924200c002c8120400340484680d20071120f00030400c42e01110104060606084800380c40b4181c2070760290447c44041c5800c540c034541d22501d08e00144442c039048400c014000c011044c0440c0c0740d030340c0f203115910405074480101e52081c040c5141603408003008400b1401205c00b01207450f540c44140e504a1080100c40b100b01200410085159016122040003030006080c018a4945000341104006018800c10810314100080c000e90003103010011004c4c52207100203482d06a0580c031a020341c011030740d05803040114500d14007030941403c40d000525501c0800076485a0a000c03011008200052003515800f2145030224041142071043c40c0d4005c030400f0280c0081d00d00700d1406026079601040d200c04182c66406010300d25640b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 57601460 1250 57600210 57600217
    0x60c0c1f020a09150e041a04020c0a11030a0b06041a09070c02090601030618110c03070c0302041b0203030403050d090213090302070f050d0213090501051e010834030b010801060f05030d05 82
    0x101b1600007811456a118480300414014080f035081403001443c19525000013074181400d900c0750702901301540400c1705150301c1d1414801d009160700003820114209203800e2b0041d400d0540c00340700486190b4001ca0004016160648044003c601d80035085003c0d41020010258040828242484103910307004841c5a40260481e103945000e50b96011200c803401130800315030b014a2084100d03a100d24507800d03c6994040c40c1d1100324825880c3c030400e00c0f130340001c42111494581140d0003450031035465032000c0d1066400b003040ca0300020364941d240f00051360b500801a844e601130703510008410060380b401034580402c0303401120400070015400c21180e661400305242c469030581f540e841c9015149948c002400d40d0b070500600380c0d420710042286200282c0d502e0010701c0c0c058030703500d41f56036a0b03040c01603110100c07000d00320311120500380742c44108264400c1d18081403094071031340c1c0101666510b40303110002003038100d51890b03510b03403504010500011520788003410088028029070860244064250721 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 57602710 1250 57601460 57601487
    0xf060118090311070b0d0e070302010203031807050604121104060b0f0a020102120f09060106180e04030512011e0b13030b0601090f0914070e03060c0c1f020a0915 71
    0x54481e020142010b12681521500098140858161580718484d10b00305802070a090380e039952400803490701c01a00004c103401160f4042c3c01031890354965145003124084d0008801c1070318402e0100015842e22a540140010110803c640801140c00d240441c0048111111075120b0b030b00703004050000e0410b000480740000e100140c40d44d0b6030080e02c1405e074068041c52007101d0404001c6010016910406860103104031480c8050b544180c1c1c9401d0282d41400c941c0024014000300ca1030288000110040d40d036030014000e0800f40d040c0301c090741201941540980050210251501500050181c4401a24054171030085a142014418207003036100c000c071484090440c042d03074030100303119034040c0d038041010f040260100313050140c42d482568090019025044050741d00200002e2803144580c908680c07143d002009854203441d0034407504042d8200540024003070242d000042485101020088241c106020000d601d40d03000e010f01a0030a49154054000c00514000034087c01d035115500003190f4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 57603960 1250 57602710 57602759
    0x6030706031a0301020310030605060612010902031b031311030307152a03090201020705060c0c120f010c081608040302070b07030c06020a05070c051c11060702040c0f020f0601 77
    0x122407122141d41c00c8800b81850b207406520000900560080144088056900a800c24041030b1502d000b402051300c00c640c81c101003e0240c00040c000b40d9043c0c3c0040d5040854507800300c409262514030801c0542c003c0d58071000b1032048248400800103405da03002c0c40b0350b004902031428108641c4490782000c01c01e21600041d541d072545000c4400e038480000385031984800000c1c0c81c0c6500d20190280c010401000d007a070162003410360004503407600100310b49051580d08040c0c03110500104c1846140948120580d5250195a010300040c880911855404003036507a0b031901541010000d2a92404d28100320108000c0b9003000c01c000300703400040240440c0d0f891717180542d0702c0d0100d040031540b0b041c00c40c41c01000b0a00001d031160940c1d0307114003d403800c1c038041c120b44880f05175614100100180b000900b8144000450f135110082112804220711100014001e1450002d481d03000904851002841070080b80c0011000288180e041004401c04c9114400034096941028900d0341131010228100510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 57605210 1250 57603960 57603971
    0xf060509060702210f01050a02180f010c06050a06050a090203060306011208071709090603011b0309020103140109020712030903020a110d0b0106110d021b240d02130e0603070603 78
    0x464030740d60343c24081c05043c48200c0340c460034134106483c2c8800c03c0e400e45034030660900b000701e0343d4081c8070b2003103401c004200b10214040f0030f58103080c41107140011008038180050103401001180e61401000d114208501c00040d41e503050004010030010240c000c180f08a00c18400c0000750b450024034a41518007500505602c17a4040c58005a00d210b021070050884081003090015040300c078001e407041120445502c0c1b01542c0d200d052500b02c840310044001c83c03054066869000c10301075401702c4071140c01032401040f00e400007800811040400e81c401c07088107900161202c14013100380c1c40200748c8501031405100550741601c009550303203810f940250400c996811009007554425a0068050f40d000e8100002c960b5182806011010764881d124454000e803040807248034404507890403083c400310080440c0280040038040002c0b02d0030000183c5075490411245107021503c00f07030964402c0e40c0000341c0d0320168041e50350082c0c10503a0200000788101070a10049641c00b08441042d98610300c1c00052 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 57606460 1250 57605210 57605213
    0x1a03040215071101030608030705100e071707080c060c03090f040f050703050906070507051c0504030807111c0209060405070306050a0303171b0a030b030a02101106010f0605090607 79
    0x1c5003140380800006000610310041107490f032461240c2071004d0f02d0401450341c1d5410304580f640b18000000300aa08000000c2c0e17290809a40701a141c10984c0080342c040e00d48a80c5c8801e0104841c100b508030540c070020080150510402081001a81c20b071040b034144076151203000d51302d0142001e0346104040840c100c400383c0e207450380f00342c0400341c0840c002e0149040504014005000030b546048590042100041249000c1c03001ca481081d405070041000c0117951744000c0203417400c1084d807010440200070001c0400c1d40034020b0080305010700f04507030400c4140d0040000c40620b0f00040085540d0719403242002d84e81e1525259480348050b01e02051a07541c0a07402c800605040d003280d5031000580364080207055101c0d0310921340c082d20105000040d12010a40142d200b54402c0402d050582040381041d418442e0300041e1040c0b20140403550112a25800036082c4075000c100000010f030302c90f0034034447e205d003007140170300401031490082501406c12400820038401d0503607113401410001402c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 57607710 1250 57606460 57606469
    0x50406120504051002030f07020f1207021c12050d20030112060b030d0c0302060f040b042a170d0e0a0b070804080708010e071403100507030e0106180f02041a030402 72
    0x700c1d1240c1c030034800c46d44c0349003c0c43e101884507000c0d10100c006208001900e21880d200260701320300e038000010002d080080d99800c01941e0b840900c60b04210074242c12425001800400c0b5203422041035450301c40d10381c082000c000303007142da801b002c811944244201c0402c3d5040800126030640c0e22071600d20b0180700c42810301da4080d110811489405100350b907145400716510485c000802c602c0f80d800e80f02d45c0d40700c104c0081e800c8601598060a032104107408100003a000e040442c0c2566041c13150000c10340c0d84000c0742c07504c001036548190343c000210400301600c00803c1c46600030401207402c0012960100b80081481c404140c022a258900000f034441d00780031000c41907034000c000c207200711843c2c207499142071070290162281340c01c1c01d4807400c1d4000c100a01c02c80c02e95800440043d0003010700701c81c03214050004d04005041c48003415901c401c8490020720a002e800060940320740010044400360340c6403021200c0c294000c407030061041c0070601254502c2e01c24460004010b0601e02e80320b889500014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 57608960 1250 57607710 57607723
    0x1020c0a08010c030623010503180d02010c0e01030510050f040f020c010603110306040b0601030f090f0b060102060703020f07120908151b030705091011100f0c05040612050405 77
    0x156006840c03800c00a08040150401110034a440e581404220b9a461b11541c2078400020381001904000011915552140c4007842c0d01a8801000e00455008040c6d0701e41011445c60b0040c005035110444620850b030885080007882170700786030130061840c081c0030050b42442e55000303552003541c51044060540d0707125007107410312000e00b0b4411940c0d4002c00b01030301d000b0304891104880c0840c01c6001071855282c08922a4481c9800860818542c0e840c840110001c01c10000a807007003540d02c0d200c241c0864030a14142c074140740300d1110088581001d070006803030640700138000c3c410540100110000841d10f84e09560400d58400c01030a480000020242c0f819038281d0440c3d956886030f000d4440703160f041d00006c0c1b80542c3e06004200006c4500740341100d02403108444001c0410f0040000448504000c00c005111840c280340c40e081080c10a10750350f051a02000c000791320301c0d0310380001d0701c1e115403280b040f0040074400e4103249180074070f0003002410560617030304540684c0c0da0780e1000400f4040148100d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 57610210 1250 57608960 57608983
    0x902010203130605090a05060f03220c17060a060f050d02060c011404110f0109120c03021e0906240c010e1e100c08130c08010207050109051c09090b0102 67
    0x40100300b54407900024103036001881c04511038071281c600080c1c941003203000c480140268504251850b40d4101001450407030680280c05540c0c5070760840b20214480d04460f0b000b805a0300306820040d40d401000604c1c080c0050941d0740d00c3c40c50900200084003141b0134120844505a9059a50100b0b03400081c0d0700740a90304682007594240000d0f00d41003410030318954443c0f4490000d403d18854844d040c04800072000601a02060030300308181302c501c808041c075144991080c490402110b84039800b140001117015040004445a560850354903d4040c2800707510440a883d42c028002c6003c00025402c40340005102c0b424000007620f1682850a421940301c170111300d03040300c4e1012440003101941e91450b030b1881a00740542c1d15404416003c501130030903408180e079500c1402d51184800d003440d100c0e121400300c4a554002c040080d0121084c00900101d0713004000010700260182010340c01c0c00c000510302803a0170320100b4102074041c0c10011100903076040c40400950901801d00513458618030340403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 57611460 1250 57610210 57610237
    0x30c0d0f020d110607033306030b04090b04020103050709030b010b0406080106050309061b0403150b030609030c0d0f09030b0a06090c0302040b040e040201051b0303010f0e041101030902010203 84
    0x484556058000094440c200510350803240041c800002c1241d00341110810a1440e400510114000c07034480d03080102c0414181e400300c2e2540c100507403024620b0420341c0c5048000401950100403043d094428910319103010744090010f02011b0b55182019080140020705250741c0b0740c040313042203104032101c4007d1a8098084112940c5440e1044100d0704a0b06c95680001c0b0101c00102d01300e480b410649002c0e00d070b1318004050548039605640708010f503000c1c110440da0003e21002000c10035281420345506800100021642c5d4090706143c28004020080c442561040000349012600002c50400c005800c2c0742550300c030500010b0844021174540d001501105104041c40880034042e0b100c0ca0417203652480800540301c4460f4280c2c168025403090150958084c0001c000012007001d04690103441490700038034002e08000c000d1a4414000c3e15019035900210060000d07404807013004028203a82007424644c0c0c900341d940c0c08400700ea5110000c0c105510348a090045900800544109942840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 57612710 1250 57611460 57611473
    0x405070c0803190b040e1b060c3f030415090803090f070602010c0c20040501060c060c020a0c180f020a0c020103050c03040b040813121a060114090d0302030c 69
    0x803100316079400780300c0c03900b0350310313032030f283d00c002e69407505100d5040d502484074090030340140c161422865034841e944240b80c20510401c03c030040094103201190b81c10000c45010704111441031501014a1100d07015500c00c51030002c0c00b40d02e1301c440314040c1e96106a10039503802140c896092840007910300710380002c101000100900038044804144081c0c01700c840340c225415203591385801c80c21b0b40c1c4040c40c5100807600e800100d1012600810700d0380e8000e401c960307510102c1d000760030200f02100e600f640030000003080941803030100043c0b40a0b00307210606030b20003040c1e044c2580c1c90381110b0070300510810801501c2c055180d541c644142e000031107800600c10045484021500b006801070706d103031000324000b9207018001564102441d041c0ca0166400400c41401c5659a560703200c0301ea8400c03400341025410200e070001d010b00ca101002401d181c452212400c01201c01314031150300d0000502082d040c4411800d070803151100000544042c0f1400b1103200c82108070f2410140d086110381c20600a1500424 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 57613960 1250 57612710 57612721
    0x3020c0d1401020706020403200a05060d0e0a0803060102070b0f0a03020c0a200307210308090703050609010207030f020102031311060d02030a0603111915110a0c05091305030403020405070c0803 85
    0x11b40c094003c4030301441c0c0c000010748041000b0700d84065205940c0d644401109020700560034898040c010a80340003030700241d1419401c001500d050004e11049801007070020030014156810700c1401c0041035070300c540c1402d00351000c002c07240038002c8210310401c0540c081a40d04140c641009074841e030603003040c01c104c0813031072810142420742c02da484414000e115070400012050102c0b20300d50342d216640e1112800102c501d0364110b8a4007000ba08510080c41003203808408110306000050060294000050342d444641c07802400f40030004891034196441402000a044c1c8140d18100c00b00707a2000e5191007601400000480381d0141d2031020400d00d00c0401086224980e0754404030940b4025042c0640300a0808100014070f500c90f6818070414140700f000704284241104010900d1610342040700c4510380d480c00480c0b500c0b000e04020f8500f81c50203a010080d03400c00d603400940240b40010024800e80040c0c45e411766034803031844020b00803943c880c005042c541c80b034907020f80c0b0316030700002c46562401c21 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 57615210 1250 57613960 57613973
    0x603140120040501020714040905070e1e040206030a0e010f0903021f020702130f060302060a030c0f0e01051e040803130602060a09110d03030b060a0c0b01050301020703020c0d14010207 81
    0x10305201c80c03070003041690604500841080e1011501d0581c003c103c100d042034001c1d028000307035803105070b01b00303407201001000200203111410141c42e11000c00708103407500b48402a5004000300400745442c00d040180070258907001c5c02c0325400000b4803408103c200c20300d024103005155448041c204280f81114050805901040c003c4840c0084d505000c0c4004101d44881c2c103d01c24060001d40c40000085160003803101e0360004000c50390040400500d1640c1c03900410060350000700c41d6400a0384d540309030014190450031a010301011031800c541d290714180300203080b61140030404078842516a00d21140381740030303104440c054000301041e203449800040c58141404a0307406041d000d4065400006c0441500744154541660000c10f4416400c092030144100c0c004d0402c002e030304064483c003000d626a10b6843c001c15001c90380c0d40e582c01042201d8244514802810317005184680d00400c25000407a50018403050103500c11501d104c00c5588030f03d452072442e0641403100a0950021aa40041c03004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 57616460 1250 57615210 57615221
    0x20a0c15080a05010b0304020d03020712080909240d0c0f08070e1b120a0f0905100b15220e04030201051006020a020a060f09030501020f0a0e060406080f060406031401 73
    0x460322a541e86440724030542c01903075800d002e02c0d054144140006409440c04861000c0c41c42c0c0240165108907807940c1c0e0050314800329000a440c52040050101800c1c144681c080c0e900807610341e02d0364900c0c1c0c05003502c10408242d201529110707964550352001070228840c910750052100c034012502590f07480e4502e6445041e98450116005140400158908403010904105c003042c020304610306084500d400301c2141c000f41c01c4e403a40303a60390090b04000781d1072071040d495043d02801c01041e0101c16500b0a90a444c0b2034585c2da40510001c0d00d914405452800540f80c0b51611003e283d48040c101203400c6c541042c465226040c02d541c181b040c04281038040d0b210034022403004030924400303610342d002079030723644441c801c000d400208080c0300b0001d4074802c3c0302c2c0c0310401c44146811a40107070340e51120b40c00e903000540c0882440c10001442d9808039040500c42c000c0b05001c0d03621904061400a0141082c640140941c05007010140001c5041e0b0312a4816005568020029001c600041c80b50500800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 57617710 1250 57616460 57616499
    0xa110d020712020105011203140a090503060405010e0610050901050904020301090f0c0302011b02010f08090f070603020904061a041a071202010518300909070507110a0506040b0901020a0c 82
    0x1443c004c00400c68110300c00080040b250149c460000c0e9201030440b40500b5403103030b9400c1c001c120141c01c0c04190b543d410300c03946000b98012800480d5012626403e1b0707040280c080e005200030030710324000f041961500280c050440d10704442d5050540d84e01d00122780501007940000703080030166030740b0718100700d0f41a8001007564000e91b00c1c802450400600305003500b0862601901190755062100f40702c904c2000e280398040b000c4000c0d21f66000b6512038a41c5460792030713040a00402d030046072001050900744a40350051902c50501d050f407105507034104659119a00070740102d5100011107040101000c41181c43d1298000c6c00d02c1d80d052050340c002030007403400303640a03c0081d9802c0400d186030800011081d0f80303800010f03005042c0c811405410101d04a0442c80100c40210034410507000c0e58035011014880c452540f240c960300c504510b8802001c0301d510480c5482600d40c5030302800140c80d8401070781e007507032901501d07a40d07201200d40040c0d20b0840e0162005002589001c00459411034865407210030f80d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 57618960 1250 57617710 57617713
    0xc1906090f1b0501020304030308060f01180b1b060127020702061c0509161202011704050c12030c06040201030b06092e080f040314040e070806011b0b0a110d02071202 73
    0x890f00d030001207889200b03901c00030b40081c41903004180c803032410341600380140405041100009080821400d10719036103a000d00070354180418101481700038072100c0c168a403d8440503282540c1060002e40400844018910403614010a00d0715404040da045580c625001020786880e22003001140c5400e03900c444104403020b0401d0041626410005003210103510502d1840c6e07400b505201100702c0305071032a6020f9040000b90501d01340c0328829095010f01580c0100050b0851394a00014850100e180000250f8503900801842c5200d10000c500540c11550900c1c02280c002d10b02d00c001040c40c01440350741076000c5103411000403c907078202c003508c24070148040c000c16500801c500595074101b0441d40324034052100c00000c1c001921510001c1d4200c42c08900542c1019241c000c0b62000400c01c403024000f250ba088203002c225030700400d03030303182d070b040e204100240701c0480f60359041e2480c80103400e1222264a501740300d030789404030400751982a2300c0301c0c50440d10f442081c00e040c1d10380904500c852025 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 57620210 1250 57618960 57619013
    0xf0e0d14160818031911060706020c070305070608100b130b1201050f0a050303120a0e0609012406051602040608010e0c0a0503060c070b040201030f0c020a0c0b0c1906090f 75
    0x3804c0204041c1c0c2814001503c1c8407440c1c515480d0310188400c3c0c0d0040a82c4008100b00d804000780092000e450006045c03002050f4071811480d11500c0c051242d0040d1090089034000c102200900d540103030180e503040107590f911005020035444030451190081180008003003407043e8517198000c2454101c400440e042c0174501c080303205100400506000e5a9051340041010034548282441d00c10b4000c1006a0009811000c0d03052440c140071007a50030038103a945880c21006040b0640080d9030150002000d40392480d0315040300546a0710401c00031180708413900b00d4100c150b6455920110041003490000c1c0b014820050707807a6228020704071030781d00c00e1141c548007150345d0600041c0345114420404d0800d290400325200d4095503200240201c0c105030300c6a4030617081c0001030041c4242003110340c009206500852034940c62180480d0801c840c030030f101340440740c0901e800140700c01502e81703540403141c480c24580c1030200207410100b4020b44064045400c20302003280b00c0480c440703081e9007004960f10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 57621460 1250 57620210 57620257
    0x20105010b030601050d050408090402040b1305031f200c0106050109122f061201031118070c061b0206011502030313080f120a0c02010f0e0d141608 65
    0x1c0ca400203442c960700040c424031a0328a10203d40d80015009406100c0c2c0604004901c40010145e038490303000540d00d0744010550262400300f00090201920081b406840150707400c48822041c03032004158901314940b2040c00306440c13003d021075044440c2500c3ca81984e2045c01c4030000d8003038480761041c0c1d80054141840040c8061440707005422841d88028044041c481c0c800e101100c1d1a044000403004074a02c030304501d12a51142c004246c03050071042c0c0b015066140d0309203844010f5510301194003401c4510340e14101000e0a1001712f0340321505041403814100682040c80041c00c40e00c0718040b11442051503070100d10b400040301412580f110902005003018810200cbc1c4a00003680c4050030b500080440030005400d090290200c03018a105090905005000031080280182e5100d5103a5136030f8080311a860354203018081031550030000904c54102e20f0280e483d6100001001c0a0401660074628002e24030942c046610445100041406e04040da0410b81c1c01544000c02c82003c0d00d8511420a8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 57622710 1250 57621460 57621479
    0x803070e030309180702030d140402010306050d02090403081b12010f05101407210903030806030a03050301090b01030209030d0905041d060403030903050d020417070f05090c300702010501 82
    0x100c0f00d2030090310071201c00030f400b845200e095201902c1c910641c0018410000141858030568003c078428180e21500c81c101400090115032050b005180901100103505026071510b00c02207400990503d800c00003961341d0031111088a1032103042d01d01c0d9040020302d4003d40c843d1402580e0584913444c40b9103141a0b59401080351500c03606084001151840302403501c018509c01c00780c0303080c1d4007030302000b24604a030121500b4540c541800700e01c00b0a402120510034150311019480c3c2c040007d800512890245450240403030005100b91620307962181d40103446a48282c0588500000180841c1c6001b0460000a08080301c180183c80c0204e2a2803d4035004c4000240380d10305103010b4030017501c0c0c02e0700c035a202113000c0c0035403120035014018100806c0400da1120b100410060907210011300600b581c1484080c01d01c4929403110307003141c8140f40180090303940d6a03542a00a454080700e1591030481710014051107800e41d510404c0101d1015203800018003600015124407840d0f402002942c1c1c0720200b59 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 57623960 1250 57622710 57622717
    0x10c020a03060e12070b0702010b0109050102071e0b0301120b1006080106200f070810061a070c0801090803091501080705060703090e04050a050607030203060105030a0903110a0803070e0303 83
    0x203944411809010004158280d02010099600105642066402c3d10b66150a540403c00449038920701000300060180d081c4100c0203d0003003441c24400c1a854680001e5881d4510700404007090300c44540002c0d00d032145032118008090201900d61690303074490343c1c90551200c45400392440900350b00080c240400100f14034060742c0e003903111100c5a07420400102c400083c0161020a00d040c520341143d2845820040466a4050100106505402d040009045c01c000f0b030713038a0080500f80b000502074140c0c41061444986c03001c142c065110340c002e0034075001c003044c3c56218580d41d51900d46204140b00744e58005510800f10b400440e001425210711041c4121424071985c00c031600050004d200c186040e9004201003402481c00b42c0a10341c807114000c800705419a07040b50141d01c00400744040107000e0100a0380710880381000c60451502030006400341c8001040c0300c6506989059070410107018002c003005081c41c0c00d080f81c06181c1c551503c199960b2040c2c581d00d001c500300c446032500c40d25002086 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 57625210 1250 57623960 57623963
    0xd0f03081509010b070503070f0507171605010c0f080403060501030308060303031e07030605180601020d05120105061e0a030501081009020105190c020d050a15020711010c0201022404020906010c 85
    0x155143e803800314281240d4025800c02c82d61800704002d50000314192501840d507950088000e80041440c0010420801e014803161030700c6600041070007000780f008554460225502820003851021003032905a0390341c004804000e040314000700d070100c28490301c1d90019068030b1003501e40b41040c0e2501001c040d6280000c96070710401d14584450036100460386120180c02200c20301b0080b1342c0c1900c480c0050310220500f55014064032400c13003042140e40e41000550004601d038101949082500c01c40035541550500909000c2e8100040701c442d1a82c00c0b04020342840340c20055a901d030000c0f200010044d1000b0b109081e081d11503008901c0504226104021009031305031159441d14109090401240415070507900c02d0240d416800390160702c8491908480c1446200070742071480c52441c001030850300c8501c010000a105100302c0c000180d00c1791001d501d224007402c0c9412140030394030040b490700d13280b03001381c002d01d03c4e180b1140030180f220102c2d81405584215441001659101c0045a034049813040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 57626460 1250 57625210 57625219
    0x20c210304120e040903030203090c060a020616120606050903010c140d0911060c03030412020607050a030e070503070803070c050411091201140c0c010507080103020a0b16020d0f030815 81
    0x7240000d0000004041501414101843e040020100103400c451344440181c0100742c0000420082c28401d10406104d0b1714115501c0d07003000d80b10403000b591040c00400d500d50014080c1005194540601100c0d40000020303441880000d8503000014041e0700900f0000d4042d41c20001004120340c01020303203000006d88451164107008086400101422a101c015560412040580d40e416103c0070024920700d0b40b82c500442d03a032304044c94500c08030041c04000308119000082031260155000007126513005a91401040328180c43c803074541407155941c05107900d48111080081c0380c150101c06051000e01034500c0c40002a90ba0060100f81c541142c1408000c40c410403140e584d9142a0004800d8000450000580b040081c01a01c0200ca8140d40e0030005a10204060201075000d0148952010742807605d40c900b0351459000c504855802e002c3c80010040210b141080c410f1784142040103560001e19217101c1e40c102c3d04001043c00000c05007580007a40303040004070540c000c50302003040480083c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 57627710 1250 57626460 57626467
    0x80d0b030c03150619050904030203041d0712020706140906090717030301090c02070806040f0b071b06050a0e0601030c0e010501090308040509151216061d1002070305030706020c21 79
    0x90811176004d240d103420803191400500045910b4542d02c428a02c114070a400456869040503540d8103034070180c4860221600310b01d41000960383c0d0080191003030044050015889000502c0d001010700b0406044902a14540c400c01c0841c03000010303401d00880400d070035119110b072607231010408601c2d90b030030310412540100010040070302d03194480d00c00c44c103881c415101844d845411003801c120042e141a501c54040306004401c4c0001001c20f160081018201003010303041040f0401140381010901030030329560340000400c02400c5802428441012030181d500668491400800c070a241e4024200d86c40c91410004c80c095001d6100003007074a404c155a141020325240070419640d000601c0c10220400c0c01011240903154041c40030701401c11034018007031502a00405ca014105d040d44101c01300240e0704100460140c8602c0d4291140f54240d40d017806080007000305910781000c650000b0704070f100021f4444288801030b4090054580e690b0107460340348046a00c01b90903803620122a0070040400c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 57628960 1250 57627710 57627721
    0x30605040f060e010e060301021e041404020405011205090c03030a03050a200301030f030e1003020711040b15031e04050307030801060203040e15010e040c0201060515030c04060f0507080d0b030c0315 87
    0x1c100f421b9000500400151400003e42c481c410341c1d52144400c110f10441c04030f4223010705070080d00c4110300100180c800b1400c25242c44000dc10110f40032800d0701c8141e680b040030440c240000e0101018800024088039a900000200140100421a501790050380f0300302c00c0052130002c075403840c2c0b904108200604e045901b55155003c40c0c414040e0118244032100000f000c69131149002c40f51583c426890040e00c4030dd003420645540d082d00919140b0403880c2007501c0740302d0b54400c40048030200c0007500540d200d40e140c8400140840498804040d00c1540744204002c01400000a01c40e01e48a0b80d103a079096680e070032059030391b400343c1c5c001e21100600000c00100410b84000d140340003424145032043c1e80e18406c1c0041402c99a00c1c0981400503511000b06008a08041c00381070a040c6e02030a17002d10b0340c6070a046400a5000b01d005a00400c94401c00e65000316114074140c0301c54a0700f2014507030f512120507040031300400340402203900a0096140c408060314010030048040c000f01d9243d159941c1c0d52 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 57630210 1250 57628960 57628979
    0x706030f0c0503040201050c070509010e09011a03060a1802030601241d04091109010b0d0b01140a1107180f060503060f0417070b160206010f0803160c080607030605040f060e01 77
    0x2c240231000a10954500240950395655014000c09080c00d0144084c100300d91400d080d28400072424107451650274030351103070fa18006061a03000020200c0022007013040c10071616041c01400000c1c0d403500c41c0030b0002c2403c06031840c984110303003140e090801400c00703801016240c1c842da02042d03020300c2c10400203480c030605254000c9468140708528004d0710312140340002e0341c407060a03040180364036130106071511059124802d0a000c0d81d402d0038102d1a0b00c888420700c06c2d45100c1c458a0000f000710384041000071800070003114025040c0104107a00c104210304026008040e107040e1411503a08100001540303040203c0c9650140030000b002e20002d941d1511001e4451044691003201d01004200410100b031013162210b020341e01807204000d00c80010f20000340781100c1138000c141303490764400382008206400400c540e980441c01000d148000b141d0305012251000c90361100d41140541c9003001001d0380d142c0c1c82041640ca00721420003804050b030b0980d500b01d032200d00400602402c110010300c502190f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 57631460 1250 57630210 57630217
    0x50d08040302062a100609110702040903090510020d0e0406030323161a0c09180c070c0305060f0f01080c0603220c081504031d010c0c080706030f0c050304020105 71
    0x44c40380038245810050004400c15522490040d904141003404103c00c031401190010820940c040c01001204440e0003c0c80c843c10800900c070ba941d400c5000205809458550020075006110640407040903102030b465446140c0e1050000c0c90040e0001d05c10301e803c1c41040c2c180c07509680e0350744241c882180d060b000450007074200340038030006002e4002901c8501c0b581d01c058501c540c100404420741c1501d2111003020151120303c03086804c1c801c103191078a800010501c80700050300040003944400100c6030040c8100c040140451421282c084203200700091424015102c040d0074080940d10f030800b070440440203008030700040d0000107a4480b00e282c030102441e0080300c4195113010345840c00000e8241c007150032500300c509071b501d114108401503050102d2015000445181b40c1f152400303980c000c01083da03079482035908004a0a0001169124520301d290320ba501000d84101346031504003443e03941d026841840c0009040c40b1506075012114060010109641e0f12071600b5a2038544c0103403440d80 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 57632710 1250 57631460 57631477
    0x50a030e012405090a0218090a061a0a080603010c1d01092102010f0201050c07121b060b040b060403020307090b22060e07020a0f1502070803090304060306050d0804030206 75
    0x40d00c4040303050810361294010b1810281d02c242e02ca502926103c14400070403402011848034510500098803d00c0003511301c60701c02d44044840500740d58600c401800205600e41201c40200b82c842c000e00464000300d8002c0031091150740b2000c4442d0344036400c2500765461032007024000f6120542019201c0040b207007001068074141443c09030b4ad40c54103082c2042d11203400c416007038074007045105001e550b00a2a4922f18821905c002d010905e003280642038140318051000b80035411f4514200a118468101032201c929941c00c070060205da17038100b04025010303440845100303605e001d41f04001845c2103421241245e038040e010b08a0189807150070390080825032141c54011050000d241d65005071120740c1d81d08401e24141c0010224108134101100c0c200081400c1e0a55100c05c030740c00041041d03228111412a8000d04600c4c0031074030310040f0710103806102c100400004000c402d018400d000070020b4030070303070342d99981c1000b600307940d0401c00c01c030541c50040c040d090601c00c00c02400541000c030b004004c6030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 57633960 1250 57632710 57632713
    0xd02011211070501020a14071a040204060803070f0501050612250f06020102031005010e06030f190207050a050f03030106050f03040c0308070f021302030c04060c0f0204050106090e16050a030e 84
    0x280128400307007940c0c4030500803640790354000b481d5006140c0090035079403c55403c84110703061000c00c1c3d80c0d060b503203002d41a0030112454980c00080465585401542c0541444416a80c03640c50720b14100303580340c102c0c2c03108565550900300003405608000740169001500100244000d0310a603c840c2400d059a400400391828484000b141001680d10b0b8900100280c2d400181c0c1d9103020b040101c0d5018881c5c200504001c1881da9036a4207603034034401d480c0c11807000c5040450076201d01c0d03081903003110a03010f40b91031580013051000601c80c003c40c01d102e55900a400762610707110609011500c17440240506000320b41c0030700030032060110940146034407031711800c1a19055901c80e140c00d081c68000d011300b242c02d0070980d440001103052925194a000d040c6580c154194140142c4012182c003890081c24200101c8014800c140040850f0460000b500a0001c000710758540c0e0008151003001e010f000207080ca00380105100b010038400204551516946803400c117000180100c0c00f42c00001c1e403040c0c15 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 57635210 1250 57633960 57633971
    0xa0c1e080304120201050109050709031119080f1002070807120c0f0c05010e010207050a050103020d02041203050714030405181e0108010b01180302100309050f060f240d020112 77
    0x28046400650066000f20420480e200410700c0082c207452058010506044c10b0402348165039801074a042d00b03590340000321300d400a0191002ca403005051269903120a02c46050000c0c60040100d1000001307114402582c9481154003801000d80c800c0740350007801c2c030400308070400201e0360101da600008407640c50444d2098540e501c401c04981008401500c442032020b0341000b140da081040c0700000d907400e0001c0c081907440d280c00600042400d20826040c5600002c0d841280c403c107030304a4014058142010281d240c25080061458000e0b003000c0300d0440386850085c203074000001c243c40c1143d078020300040e1140d103040c250f4400c08070090094041c510030030800880c0090404012406480e01e4000000c160049800041018900c1c3d1110a0040000842480540c032007001080041290b4140400c504809250a0346485009414005180034820601080416140c1c1c03a9001e101e0300c81c0c601d0514810399105112880001c82241c0e0f000f1440c1c14080015406030180d240150340a00e800507c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 57636460 1250 57635210 57635213
    0x408031302010c080a0210050f06100e010c020411070506010f031212020c010914061b0f03060a030c080c1e03030306010309060608150a0515030a1b090603030806030708030a0c1e 78
    0x2243c00c615805d00251f0420340c203010050300c2e80e1240903881071040549642c1402c010f40880c48004401c40c4113020085001f040e00c1d0581d00400714004c1040d40a0000c219507054821900c1e156088180219001c2c014580001a1a250b540b28107040c0d98100f504042042000c0200b40c0e0b050782c1004440d800720b42c00740010034441d41c0078410640301174002c0311225a091140480141072506c000e114a0000843c0c01c0010100c040800941d5814842c5158035540d81d103030140024110b240b0b6500c020314120304d211010400f0724010070303e492a0501622a4034070403124600ba130303d02d500300c0c90149401d60700a0000610540c402e4000c28071003401201d0018407180c03981c0f640ba06148907030384100501c82c0880184010701d00c107445a90307481444150f501001d0344021000a4072071440302c00c0584602284008214035202d0000d0800040c105031030204070680da6441d02410b40c503c100c400354032901401c100040e8448022040f200b00d41e01c80ea481d00059403503076a40d1140055040b400803500102c0c42218030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 57637710 1250 57636460 57636473
    0x80607020d11100e1b150909060303130305100606020102090105120a0b0916110307020d08030a1b0c030215091e030c060103080310080708030304121b21080408031302010c 75
    0x4009081c03400074015a407016050701708041c6045200c40c0c046e041c0510070070b030540764460a4484842081b02d068040d900c0d071400081c51800341c1c003010788541071201000010000d000031304000c4403003040014400d4664440041e4200e000c6d004000f400300f40100030031088400c5a9488941c8510558030026036080b1840c080fa02500049a00584600f001e0840b0007400b42c10140b0b84015680703001c002c5150580c00d0780400ca83c00e2171100300900040303020020800700801e60308401c4000004500c5000800032040008003286c19003c000d50241c011408200090510003c0e441d229900000c01803e108481c0851150800d400c1c220400180c00180100411450144030080c000c0d4021056180c89040c12003007100d00a1140d440a203413540000000c101c20305000c0262a0b0154014607050001500c030801a110200406a011314101d030010408003004214040b02044808101ca207418400c0c0401e815107000400f601c0c090111141400050031550b803500c0002e240d0303032040c540302d081c030000d5a940c0b8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 57638960 1250 57637710 57637721
    0x506041401180b03100f180902010c0515011a0307090506030601140d0506041d0601150e0319050609030f09060c01060506070605041707020d0b060103060b0406020115080607020d1110 80
    0x10020f6000100f400042454903558001a01019011500d03c62400300c0e20419400450800c9803400d4448200e0703029a03000390511080d0a0b04042651005100e070b07002e155003031500740100c4036455030340e64002c04c16030f03201030a491045d40c080c5c503500512801c01c020043d45801c01030075075040114081a40301c0203a2190f006d40000c00342d83c200441e80d82400703c00c000a5511411403065502100c01a401d40046c0c0001ca10b811140e03041090400b01d64444403c480d4944003420040d011710400b209032007241030400041d40030500a03030a8420540301c81c85170644912881c0005074000d04140301c560302600c0d0410041180380c507464000514680d40380d01091158110680136140e41e9515410803090082483c0d001c1102c0490340201c40c074000300c61b0300140d0005110f00e0042d103518800000980c0a90080e44070002030020b580009885594825000340608441640750b4000100403070001044d800000e03501e0b008030380a03009030001003524541251822401d0a0b810071912408036034240c4612540300383d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 57640210 1250 57638960 57638969
    0x1d0402040e100501020f06191103090a1506060c03110a0b0f071209020603040305070204060512030d0614030a200616060b03060f0a0c140a08061009050604140118 71
    0x1094907458142c000055199041c1d1003035065400485203102c803000f01152255100d840d960320728545002800d80c0070000c042203012050b400d03400105022030003000041c0d400e046072003103e560410a5150f00b101c5d00703a504520840700846d003a03192007800a4010f42004011900c040c088038090491902c0c1d1060b404015290710b85080d41c84014816044d501c40c3d0744040405969405005c1848030358003041c064400141b0207010000d02003100f80840d42d4640040c00201130081c99801c2003d0b0f00450355889510026110f51500d16100c400159446019918169114020007501020f80c1c0c07a01d6031019202142003580d8061110a810089030342c5041c00b40c141004030b00c3c001401e1003050310344003040302c405a08a6210354041020403084245010556921616034400842c650940400c25503038001c03841c544d007402080100b403080c0c82503404202c4900c507900c2120b01c182444501c402c10b0b40d1403c0c250103025002982044148481013030001c0309054100107140141000001300c0d41801c1041860f080b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 57641460 1250 57640210 57640229
    0x706050a0c150e0d1d060d0f05070815120303010509060604090504030e1216180f0203010905160c0b0a1805060a050403090603060807050d050102040b0f03041e030206071d040204 78
    0x9483c582110070071010b02d50103684d040282080c4140c03003c046010081c42030301342c8110310000c1d42081507100382c1c1019040b0443c0204c107000c0e40c20700a90281103103200710740b698040020202c083d96503180540c4119450500c400103075265901300418041c0312a0010101500b0450800c0f00142c208282e120340380c403d038002d507500309031170400c0c0040107807203a14039000a005502c15001010500c1b0701c4030001d000c440101e032180c03e1403408440d000c0040c0007a842c00841117480403000141c00803c2303400c418820110a4142d043c44810102d0603102c0c00c00451014080001c2000003410dc01d00d00c0c0c3c4502e031041080c42800014132156510076150010840320f803d4520717102d40a10003019008215800030704010304042c0600e40c20503003410368400c200e20030948075400751514141030290030b504540c060818290700c0c95a800e01040c0b0701e40c2c01e078030603101125240c00e20104a2411420802a50009549540038201d15251040e08075411300380f07015124804007082001d0308041d520351005000a004190 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 57642710 1250 57641460 57641471
    0xd05031209120703020d0c05010e010f061e0f0e0408070204050c07151803030f15061106070503190c090e070309021203070c1a04180605030d110706050a0c15 69
    0x41e403418010031403542e00c150705003842000000381c0c01280d007513140705503454051031103581c1d400c0107405401d00b409a00c4082d440c2090800501c1310580260040e6080004010744e84900c22803601101d84540c400c806019481b43d07001d000400e403038026250481e005650050500c0c0c25900001d003158821f5400c0c00ca0044001032003800c004518502c542104800d02040141a8045401c58400188404000c007015035030140c040a83c5400d034400c6610920020324014003e031074080c060310300180440031004034810b01000540b0b0710b105104407403040f0b50351402d1001d210030048540b4060140b40c0d0000091021111020844590140200380705180341d65011407415034500500140000d024402d5440307400c01c004250105400c0090b02084400905414448031400944c0c03d44500654014503107074001902c2030316078031030181c0000302611030440a940c25031005180640d406410800e01c503032a50485881040070764082c84c041c1c8421400c9007040ca0090a0503902ca00300c607070442c982215035580d6070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 57643960 1250 57642710 57642721
    0x305090402030720060c0904021605060906010501120507090909030203120703060906050616020108040f050609060403030b0148050a03030b150409150b0304030809010f091e020d050312 81
    0xb249000420341208010740068181b000144c1c0d034512580c0180d900071500015018145100d02043e2004503170480d040d21601c0c2040c140700798480c10284100307400656021480020078416206190250440341c8074072035014684081003010300440070040e02503010500c680c04140c0e4011007110710980d900c0d6400101c03503040445807030440d40030f80c10450207120144640780504000c001d8059502c0d4090910407403d6031140b400f060210383e043d0307000b0700b035005072000e00c10261000201d550141d0701c240c90a006a1548100440b82c0d854850b0f00080c8920141100e462294072010f03041d2002c004000ca011307220301d8001040c4031006003090341158690b204120032030515505205030340c034494040301e0320061074441c5417138400140244c4c055030b031009030740e40840036000804040c400000d100d01d00c80281c59190034100501700e00c0089648224950030000c1551000e1414450340d86003642c03005003543c074104210181034624035400401ca8100800c0707418200404c000300040c2c40d028011400c440e0451a12 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 57645210 1250 57643960 57643997
    0xe0a06030c060516060509011806020a0207061704060f0e070b04050405010902090105031821030708181203090109021c050c09010e06100c080408010902030c1005030601080403050904020307 83
    0x842d449501008003d1104c0707807180409803032001c00c0310382008001c2000c0e01c0d40c140440c010050049010000c43e42d8880250400000342c02411800f03801d84c080c1d82e40b20340d0f9880d0a0b036449094400b02c4400f100d01d140043d00013415036000944d10b0885500c0000e900001c44000f03890160a500080301d100c401080801585c50301d40160781c00b4150001003542000b40301070020b0b04500010342541201c44030f840d04110b040c1020804080d40980703040c2817910024a68100744425803083c0c034910002001c07035000075000311424030516603018043e03005101685001030000d01d00c3e040a00a8141075403140a4070002d82d07035010485224146400301c0c0311000c2c100e49020f91802c43c28420141c054140c690041044505000302c1c41d9000c003041c3c40a81c5803113038007081100d041c181c28030000c0620300d020402207141c1d2015030050605620a90880d100418101d0410005040350080040007a00400000d0160751041e821660003030320a0070680d09141402c0000f4090f40c104440f0f060010380080c02e03c1b0141c440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 57646460 1250 57645210 57645233
    0x703050d0c050714010f0c030c08030a0f0e01051b0c01150305070f0e0907050d020105130f061407020604050d02010203041205160618050103050c0c01090503070b0702060f06090406060e0a0603 84
    0x606034551030304000e13414000703040c410449010a0901c211aa2200305050041450380191580310400b250f89103407680d0924010924030f03150f4903055241c450049981d03030701407145d03500505641c2d8403150006103101c2840705c0c540c4410070000d001d54844254420030460035200501031841400980003c1d4203009845003a01c4040e880031030145a8141407010162001c10b203e01619016030302055142070a00041c1c0e80e500c01c00c80014000060140c0005130100840000b905072080b6a8500c1d9071f05c0152034141c4501c0c050384c04003a40c8904204820005071412020b0030034114810b0040c0c0703003010b03602c019400c1d800c06011029510790300001c403c02031200c0c4850810000c3c04007802d00140c09200c00c0e038400d5521300c41e8000e450505680e600407850281c04201901c0716685104020b100161482c40c20603103d4000c580100c80390007408000c41c486900200300c852144407400200e403001e9441070f0400c54014405042550095030752100442c10620003880305115081d60300c0003040c40c503d5407a0015040701c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 57647710 1250 57646460 57646469
    0xe01080c09060703050f0304150e0703021507020d0812010515032404110f07060b040b1003181a0709080f07050402030405010e0706090f0b030f01060507050703050d0c0507 75
    0x20605040080090000d0140e5100420540e5465142c0c0d416140654a034801e80900810314100482008100a40e5645c0c1054031000f850b0140318142809006c10703551581f601009500140300354000d613074800700c2d002400703070340307000070800a0b4242c490340318013003e6844203a07003c4c24842c3c104018030003400c1005110401e01800707006c0b10310b0b502c0d1a12560300c0000117400d504180480110103040c4645d00e9400200180156140b01c80d924419044156900d0b44680c804840160070841c2d4401c4520b064411841001ca02402d038081c0115800700440003001c0a0300302c02c5204c0b00b180c80c80004134941405c0040c0392540c80d84281c8036402c1c40400540076030010360058555074484662841c051170041640d0302124415640980c1307a071a0340c41c1042c05010021140509881101c50005880b070703100c514402101d45801c91100c0d4076448155414507440100c44028080c08420010024948908010f109181c090800d440311079407250303101c908040800020304009081485441c040c00713414007480d0001c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 57648960 1250 57647710 57647717
    0x515041502120a0c020d0210030c0908010b01020a03050307050f1206180405031801020c04020a0206011e1401050711090a02031e01030f080702150301060201020315040207170306060f03010909030e01 87
    0x1007407900e80d0300b07240388100c0d0f01500402420221800454480c032001400703c82e03009000090440010000a0052203200c10003c002500390720002407a000600c689280d42906a000e005040ca040d00c013941d050b03101031f2143d001c00c02c5c20810b251400c0d54080191113111590241d1900d14100361040000c0c40c001c0d00c41d4401c0504203207040c000003039400812240c2c100d0a946071460800c1e20140140d05005403d100c6036001030000402c01c10b1540d000c00c05a060310002c0012445041410443c00d814908500440e641070456408819056001e040a02810f92140309140041e581e080041070202105070b400540c0700e0b8000c01404103081c0300c10013042c0c0155183c01a0107d540c5103458101110340005805060b10343e0008040c425034484100740e20082284a4540d90303a542d42d0b40c2c00170b000b54030803200640c5080c80000039202c41e151900864068641208080e100b13204410307403504003a8409012960f001e5020000b030500714a04101650090002802c000b0720419507007000707804200401d0450f07040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 57650210 1250 57648960 57648973
    0x14030a0209010e090f370f0608190305031504021308060718090203150303071b050105070302210d0c05180a0b22091b090b040819020a0515041502 64
    0x880980b4031501303500002085031480940541c203da040384406c0d02003100070188441a51034203440054014020b0103042070000c014650f584c1c007101d511095040300e1158529100c00200c1c0120f446040a550083d0340c00c440d9601d944000c81c0040d0480c0d20001089070801062042082180414000c0b07e0340204241056039039500000303000449148540200c0035810790100210342010320b050100b0b508100090100ca54070441420401c190410050300401100c40b03001000c94194032800c00e07160015403540081c004030309402250030b141c0c3c82c41d0003100983d01092000c03d503403004601a10324040c9258495580c1e400000c503810b95a8007c03414614013400380c0d6941001440c41c110f04944a0104207080c010480f600b82d03044e903400c62203e0348080c42c0035003410025101070080d8002452503001507291600046d5071460081c8c01809140300c1c421741600000107100105010758003580c2079600c020319464240d80c4540005003000d8440482d203c00c48d10220341840320071002a0103482d842c0ca540020b125 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 57651460 1250 57650210 57650221
    0x6100b0309030d050a06030206040305030301081b01081303020a02030d0518040605060909100f03151a0a050d03030204090e010507110304150e03010902031b030705010e030a08030714030a0209010e09 87
    0x65030b00c507041101c0700f540d980380c000602403003140e4810000b035075004103034035600c40d524103100c0da40350400c0c001c3c40f089006248a8041c03400303032086115080304040e19030a00c00c0d0707100c0c0c040c1504ca8403c24010380950248060290050350301344101c402e101460b07211240c45003a01984614a1034841c80c86034041c6292401c1444190317a00810358540724000c940e10955580c0f01c45180d03010410f1684035010b0040e03800808000c00050f4480b40c88501815442042500c000c650130f03100c4402c05486a0360010742e03c22007440742d030402c208500001c03802418007628180e030703d51540c0c0807111940010b0300386940d0343c03051000c3d07107a00c844982e42103224034004504040c204160034100101012030710701071045e521400c4445440039003108251075002002d40c0c01072044a0486000200700c408460703c43d0081000c00b0450758020484c503403134000c020b0002c100f0412907a903000c0c036640c80a00488240b2405154110500065100a611030140d048016850301400c1e0009400580120406842031541350304024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 57652710 1250 57651460 57651463
    0x207030c030b0c0c0f0c04050c030f0a0b03030702060d09030f020d020606010323041b050d030c020d11030a03120507080106050d11090d060618020405060703050c010b09010806100b0309 81
    0x1560303000070758203840703444040405003e8401c0420318030780d5016040483c0b45010010488021919064905200d02c0da19000816020300c02190103c0c02d100c661804101e150600d0346c4509140c103006011039140c480c480e0002401900120010603031540c580171a4002c02d0350000804008820034002001c0d500f101c000302945982d402801c580c10190780c1c0f41e80c40f01d40401d041d00003004070060f00015010341481d080c078488104903800d42c0c107003805c0003c400040d0f42c10090700c4118180d0f05035403034400c3c0f44a25400c0181d0f414281a043c0c400070034442d174845041d0fa0502401401da0703c66101c50071468040c4204005070740c40104000144071600004108550704a401c4418518a0500009001844040700041303230050982c0148c010744408200b44c01c00075a980642c00741c40d10300307080082d940340306c00808042e84124040c268100505200900010340950040c0006201001c004600c40c3c10500120320300e2102607009420300d600c040c040c0080b40e0402c0350202c02500c2c10f00e55942c51840c1006103075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 57653960 1250 57652710 57652733
    0x3090f0d0209150a05060409020a020610050307210206031006030f0b0913060e1009110405130308090106150c0209070f2c030d0e01090e130f05010e2a01020703 70
    0x9079000c214122030305501d560b5134002e090203400014100341e100c47d1107a480304025049861440c01502c60701003c40d15152040605401300c0720010003c1420908081460b201560300b04282041c400340031103044016510b81d0040c521800b02d80d80780c0001a840c20000809440052076111403891070103060075080d49820003180d500c04c5501907000a08000d130300c1c0a00c0149905c980c612094041c1d00a2581c601201b5000481c51034020342c00c0c0c50350441c6480822007254800c2e03500000704410204403d00103409601d040340d0103400d07030000188096a486c1c40a00308550748444500052001030b0441c00c40c5050801160031044a01c4c101c81d090000700805001c0c482d1603014882c07205100b42603004503014441c2080c1008401900f65240164010405401c5003000a02e40d400715600f0f003070100d034226064070400d100d85440100c40e1080236551b1250612051b003440b095a45541364040291b81e0001041140245041030000455414001c61042c0c0c1c5414001e20041c1150004801000030a07454586c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 57655210 1250 57653960 57653971
    0x190509060c0304020d021806031e073b010603060902120604050c0409060e0709170a02010f0c08030f0a0e030702091f0807080307030207090b030307030c0804051203090f0d0209 77
    0x761682e945450000400503010302070000d62041058145104400040c0c9403e80a16802e40444000c682c407008983d14901c9200c0d8494078a80c00314004000c5442c0e462505400010608404280460002c48081441c17000c0000e00c400803003408010410070798588501402440001000c42c1006d10704581c1c8022010007038100d52240341c8860109504010080899009011074001040402c0d541c2011841000c0300f25074800208a600000042020281c88032902d04280d08000d001030f20070300e03401501c640f0110403000080084c11040340000518802c000c600a00e0f481d10030810b01c3c0742c00c40e0410140d400309286806140c1082c0018401a00e0300018640c100c954000f02000071604071420341104001640070056500c82c60070001580200032004201c0a80a0303800c0d07a030f51949651841081d1200e40d251310707405034410801c0c803001c0b074807071a6140d020a100344803581c90140d030b5000103407101040700340701c01e401c2d0000510046075151585000303031401015078444443c4a0550001129a40003c4c038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 57656460 1250 57655210 57655231
    0x10031a040606050a06090806070903030206040b04030207030b07030b0f060a0e0f030a1211010b03011a1002010e01050106110f0c010e0d05030918040b060f060406030c0c0c030b19050906 81
    0x800c08010080e008031028150103440d8828407660786000501c2251284210380300e070302072100803a141034811140c940035680c01d50018800b949903940c070000c02d850020000d40441c094030002100207006519014010100780d503010540e020304004001342c0041d041511446141c0030869178001c03541150053304c14002c00c480345895504004c010038200070844034000d00080d00c210b0b0510792150001d41d1000c1101d5144001c0106541e4903041c542203402629180e8542413680312188041e1804041d0109604010710000c40e410f40295038442c00d5a6007030300007001041120071142c1d00102c08001050403901d254000f003540410750400600903071003003c4a940a02c0054400b07100703000e0200115081d905000c0e04840c01c5113503841c02c40400d00810340d000c075181c115810100f0100c0c80c0c824420513044400620461806245c0300040c3c0052419203d030b1400c0c0180c204c000c001241481c44241e00a40c02215554500d29140d801c10306402c00c45000c8911551a2409008a0341400140036900805443c0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 57657710 1250 57656460 57656513
    0x40c030504052a100302160803041403040e1504090203060115030c1704030c02060705070f0509060d0b07050c010605060d060e0106020f07030b150405100905090d0e0405040813090606081003 83
    0x204c114060f118040308a4039001f05081071104028044005501c218003801c0441c54039030142c0303101034491081d03215801c04074400c0341c0415444241e2800c4045580c100600000702510304c7d42c041b90801034264414485402154814a50f66815000d8000080420714240d14a59080d102c0c122125102130006010421103110540442d02c07010200d4540d20b4101007101c51103580e90644c0c602d621558010a03010310419808100342d410110607000803243d001680f4a401d64030b900040311182c101c540340c8107581d03484000000d110303100c0c14002c1100c803580d88400300f485420184c0c00048041c042e4003681c119401403401e000c103140302003800d40540b40c1c0700e20903400c16129003061a00c1c21404680480c0e10500d81400c1c400d050000c842822b04841032404240b000d6030f0b800c0c0f06180c860b440c425200010503610341284c040c920301580150740c020310512400b400e00001482c0d0703200c5070040d03400038076400f5903c4005102c00c3c0d0b0410b00040e44010700c44021480c01d03003540d89021250001c00750070413488082d003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 57658960 1250 57657710 57657739
    0x30c0221040f081f09020f090402150406180602072d0f060c03090506130909050f010207050f010b09010303140904110c0d03050a0209030c060f09040c030504052a 71
    0xc04540080c01d40150081025850319006500c0322180d071480759044405080c0d1101c000303e10701961170120f4004100c0244014220140900660010000c90344a58290080785030440341c0c0c1e000c4c0c8060001036913a820612000070743d243e21003d080c0c00900642d40822410864041c244540c03150081c1100d007018440c0c0c2a02004507882c02c00c0d50070500000c60740b50390106040342e001340507485041c00f82d039580390038980d10403d01025205d00701c024020005403e0042c02000e900d5000003c08500c41da00f21780c40e10702145950360884e00405803c458540007005103c020960900504116007021074469859514654002c0c0081c86088140c1c1001c141c0410750140c2e13030782e5560200c02d00400189446513925410443d01d078aa03c501c08006000c02d1030000801d601e01400e20a880140c0800340051202032808002c10203150410780c42c0030114241040204170617141c42c010181102c4240d10301003800d00b480d2406904041001503510000f85d01144130032200d1354208000c0c10a02c0d4169403158810104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 57660210 1250 57658960 57659023
    0x10302091305010b0d030507031806080106050c031908010f06020304120308150904030906020d02060112080921010504030e0f030a0b09030409020304050606030f0d050409180210030603060b01030c02 87
    0x13001c0301d54810301030048403040c550444003d00c103491082d074464040720500c00e15401d000da6680141c3d4000340c00717600140601c901950007481880c00c00000c40e81071983d801005801c0c908400100310002d101200100040c03060440c105001e0109400030394241804d009041c1504089200c014040040c442c0c041100b00e034000010000100c00900320340326514190a0160a0380e44034481c100040c8120049204800d102050150507603035603404480c0b8801c1e40e501c4011281c2c2060000c1540196000e681c09074003002d41c0744459038402d1020000c11285800d04016000200038480b03e0f002d0604420603c03c1c5540100e80a54156809842d258158a40900b690b00d14000c94019929840c40003003400203004000400310f211740e00840c21254802c0303d0800d25030b180e01c6d03000000004524240000c1c0214010340c1c01c14403000340c0e00e401d40303c00100590005903028030480300407000300741c0d9820b060003405064026014000401e00301880203400c41c0344002c0d60703100b15803171001c003181d459050300c1c0c81c040300c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 57661460 1250 57660210 57660221
    0x812090d05060a0c0806030a0b01121110020c0102070e0c030420040c0203070c080d02031206010201090c12020a090e0a020d17030f07090509040c090207061d0106061701030209130501 80
    0x402900b2102e581c68043c81d403a004040c407076084008100c0d4440090010b01d000289030009640c0410300350403e920744503010007500080d05044844041121085440351503400811306a15503680c020426080300700700180c00d040040c1c02c080c4e070045c000e000304500c03d0b121200b280c0d000ad0f401b4086c020b03880c145442d06500020200001c0740c6c131a04107400030190039800009410700d036001c0d100303000000d0707511850f690707403003003524410800341e001403114969015207412a07542c0103030180004181c003c07041d503403044035031480d410907603242b691421242c007503007005821100501007804080001c07040070110035664401c0d6800092183c40e040c41c000c0100510507500c111140b802c0c07500742e80c8a0070041e400000004088440100160340080d00007094540100c510740960f4101c08459243c80c2060301d40d601070b41c000380702914103944812507801418143c030103c240c8120760000000b2458141000205103066840c04000800c6034800184003603503496656a410003541c401c0c14192a9040ca0070303030b0240c00d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 57662710 1250 57661460 57661463
    0x108040212010b06130509010f0302150304030207030203030d050106180302060f070512070809032401050f012d020c040902090f0403120c0c0201030e0303071409030102040305070801020403060608070812090d 91
    0x2004201111000652a1054107480301207800b0781d1030780e072190400359030f0448510000e03500c070280e0363300d0b04418400e8000464009005c5d1040d918407036107a801207451980a50304410407213940d007004104042e408126191501012243c0400152854001903002d000346200c02e00b01546c001903507000c118007001942020342011107055104c034407604048409800c05012940240180300703a080d80c804900c18840c076292100e18400c007050342400700348440c20000000c1c803410310082c040e100d494880a0b211508807511010151607801650440c000c1c1000c80d40c2c40b03d14051400c0590503001aa0b03100c0815030312680341c001c80c1c2c50355600e50404841810101e1802000a4540b50400101641c014000c0c90514000c1c1c07000d008801c100b0303215135968882200d01000254803012520880d4041000401c15080020005400c20b9100e071140c038148503444d481126241c0d0700080c104204a041d000b1007004100c80406411628580000c140d214860a00c4496014500140070300385035541120381e49803076 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 57663960 1250 57662710 57662719
    0xc05060a053105030703150f1119020111040b0d0c0201060b0a0305010f06110613030216170d0503100e04020d0b04060b01080a02090f040b040f0c020d09140108040212010b 75
    0x15501c10900612840b03001e510b0072204580a0404981401c0020304201103d511070181300b1a843c0000124000f804070407d560545519030b24000b503044403480203064800a010b104080d010400c0c44082d08543c0d64403140d0307040315002c1c0f2040184000800c1a40c80e0880d020324080b8018105444c00c80c01490385421100c0c1181c40420307210403080d4158000c80c1a90442444007000e032362074038000e48008000789004185a03219a0000320000c8410030038028107440b9004a0702e2200116805803140350850304000c202c01d0b11120800c1c4403180400150300c24a0307203403c0c1507180d0300341549405111b41c0c140c041c2e419000c0000b80898119101c1c104407420a03508280c01d07141c113041c135113000d030003a204e90075034580042d040001094085c0c52a10071140b840381c0027840042000c0400c1d0034030002d00210001c0726071041c4c0d6041010740044842c01a0908130459030302400000810140c0901000216000350f103009181406040740ca0740c008840f540c216804035034640e80807000b0000507016201e5407040c207410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 57665210 1250 57663960 57663997
    0x1216050711030f030304201e01121103010b0a09090e0303270d09090506040b0a050103091407090608060703020c072115050a06090b03150c040e01120308010504090c05060a05 76
    0x1d10847c0749240700d407824000c8299801d402800c0412883c4005402085020420398840c440c0643c0204d1800c0c103806540030f40845d058a120342210340c0341d00241c2c820b41a2800024400841d142d00c041804003030103800c03004024160082c188240d50340001004010b101141100f00501c140e080780030141603940040c12219200700d03800b0010288103580c0703e054161410040440c03480e1509000b8811a0720000d000d406080e850000114060511f48805036868a45010340f07003450503080c0305c218080d2507214408107a007441c0100242c07900c00c0003000c0c034042510502000b0040c20020030f111084030801419203e00e010540190940800f104e64010116030300003440c024001941d4106d28407415a00c2010001e20703954602920594909601711903141d0001e1004140d0350403810b02e542c0e003014205504504054a941402c05003580030303000350140344030200700b0004055000040901600c001d60302440840f4484e40c816003000e030386015086c4552004558808004c2c800c1d016680c802c1e402c100c000a8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 57666460 1250 57665210 57665213
    0xc030a0504050f1c030e06041a030405060618010b07020402090414060310090503040e100305030a0e0a0b0c100506062502030106061403071103090d03051216050711030f030304 77
    0x4654094402c040c02843c605107041c00510b803070304c52800c1c000808100500d1540c01541c0c100c0d51314403c0d05140d40d001c0701c240b00228401d00e04007100d9170ba4495085d541c036aa4100383c2803042c60070030001c0c10188184e52040c0401e040114a10381035045500c4140250384540c000e2000030040e00910360265005072138000070856461140b01c030343e40140016000e8079800e0030b68002d4030702075618050015069074401c0104101225810801603409110600010701c110b49030350b074160550344120200000581c0041c40000149017202015004103910360045203030401d105040c03500c90010540d55800182e80310f00040c5240c6600040b54041d42500f0410403020942e10603146e40d1103000071043c0d0080d032074101c01260a038016201c54044002d00314005081d0b503038031141100d1800c011403040382140070a00040754070751902100801002d1181d1905520340071f250840c100b80242c0207001402c42c071074020001000e00d8000c000c43c2c5000350400d4000742840440030200c0d1614141c9035103031a00d484000304100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 57667710 1250 57666460 57666467
    0x605060f060f09010210140f0a05090309190e01030804080708030a080703200f0a11010501061b030c060c0801060210110a030902030712050a03081303020705120c04060b090102010b1c080f0c030a 85
    0x34869801042300c041d854407912052021154111520700c2130380e100308460000c51602c103864414581c40c0d1100c50108c2501d485807500891802c0e0300031500050301107000c2c00b00e004180000b10103891004011410300d50244002486800090003900c20b040c0e948401c5c102c0807400090b0f9000810a081c4d196694030300d040d8100070603034851406000040c120381880a01140706016407412180340380c0d1229103010304005600c0b43d14080003030440a016040310f1420000341a4011100a0400d03915209515803428002a0030944c0005c40400c01b40e1910781826121000c020a0f2820400e0303d1500042c403141900c04685000b0045c1c00c85c80c1500c40300d400d00c100700a03000a0702030b5101c0c4659202c2e0000d484828644070180503d250003000350300a10014001c50138402d010180040d0031804581c020200341c3c02080442e0050b401c0110608400100b580d42d0b56024010301a010381c046d03c2c4000118100020507024800c0c0c1840101007000c009038101c80c400609007a2a06108a0419603a85922204024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 57668960 1250 57667710 57667751
    0x31909031e0306050d032007120201111f0c021501080313080303220807060513020a0614071106040e07090305010c0504080607120e0d0c0605060f060f09010210 70
    0x681c2164848226541c0c0d0b40700b03008503000c4030030150010820b07406a40d01601e20841119180c0444218050342120560040141c000180250103894024481c035000061054440000300c8519602c0104040e004a02e1100000c50300d4502c048006001c03d5000022400c0000300381d940c8000074411400405c9550020000f050303c040c44101c54014637644180240d264081200d004296101403806031030922500c00880038080d2240c0c0c01c1900e450101d40e02c0004888040d06c0030040c03801c501d125001103003001182e01c00a4401c2e4200001400e16030300c5444040d01c511907000b090b02d40d030440714050548400c4280c9001e40080001d0f244180740008c8010400c1549103c00e0382d1960070308109030400741c000e2040340c05884c0504060310050f82d690764107441203004004802c034140d46e291184071032450b003800300005850705681e510b15480020b040220030742d60f0181071207106042c140114071166517110215541b4a2080c291543c80d801b9000050307082180200f20000224203115a0400110807400d46 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 57670210 1250 57668960 57668987
    0xc1207091a06030103060209011403090618061501120204080303180d0314040201050309120327010b030d0804050705030a0f1e020603150a0503010e030304050f0303040302060c03190903 81
    0x20071601007003001c035441c003001400003250422010001400410030a400408041d4818140344440305108502c8034041d510844a405840d000380c1c050000f01000d1004000c10403040c070340141260b0800003940311518008a010034144a401401108036504940649000740b001400791794503458840000310642ca030150f071a011070700840c1c0801851600078440e01c09190104040e5a40705c6d50f4983c01540d040d030000e403689465104043e4075419840c00d02e4000d40c0f2454417040101c4a42c80702c1c403048200450040c000395a242d0501c07001c0b0b54182c600083d4074082c0700c01e51070178400ca0b442e00d0402c05d0500c12113802203034150081c0b84190b000c1c041e50100107400b0310300c00c902d1000380071103c01f00050f02c0174008bc0000e6005d81c0400129040540d00c040030303040220001d100081035a620000282101e40074080440145c00200c04c210512205020b81e181c0e060080014500c2e52a21f0340c0c0003903d42a000313101c08090080840418000c8400c482d00c0b000e8645505010402c40764a420040c0124010074107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 57671460 1250 57670210 57670229
    0xf0904050706110303040812150301050c090109081f02032203050304170307020618011401030b060405100605030604090606080f010f050105040911060a0507020a0e090607030507080a0e0c1207 84
    0x343c0724055800801c4030710540d08040031500300b12014024070b030750b07000c06840d9202c0044a43c5159566a5003132103418001d0030b0354131940e80d0b240e08440000d0701e003000540c8061500c1c0c008900d1840f040700d482015071001414001e00581d640d4403040f8066911682510b1652241c50b80b03410f400c101900a0300850080e4000c1c04041c100306441110865540b00803211480160040303030206020310040181141055170b150300101e10b881c0440d0005a103031400364820707100d09504400344070441c2442d108040d004071840c0104080103080c005d011708148000303080c0c58029a07031480600d003444450b42c030490240010005840d02c0718800115139000c0d195074810401d0052415000045501d85842030404290f88907100c1440c85003c0f008006558101295450512200b046a01c0050f915124508090034020500121a0800100052401100402500030305203040140040c0c1900f102041c1d81c0044840e8000c243d02d000014282d081c250034102c1c0d0340d00824080c01400c2d00900c082208010b88900d0007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 57672710 1250 57671460 57671477
    0x71802121302010315080c21030a181202030303040b1306020415030b030d020c0607060605040c0903030201050703050420030a021302070204111303080a0504030f06090203060a0b060f090f0904050706 87
    0x901d203035a6017158407030710303100d40d0004541001c5130800342c041001920386801c0300c161224040c9501800e55004098404c00a01801d40388044402e40714514406030540c4e1852424800d0079502080d0380c0c1c0700140c0044d1401d000f900000342c042d040c8100d07180c04151300950030f544039a619002d121081c201c40d01040c01207418917183c41c41901b07000407202c0d40741e0300b95801480c20340710950600c225544584400c0c1c81c843d8031100d002c40c1e036840f0342c0a034401066140e9180c0310350b5072940c18024210b440107003212041500300010300001c5100d10032692041a400540c1a111803030380b03000a854400b00450003500149401c200f04c0309403e01394040c2142c40d0090390140410380c400b0001c40307103a10800802c0d804281101a051010a14440150544440740e0030700e1464143c49441d00014818058801c940d426100d0605404604040c0820303500031081c11428880441c0c0307400010094014030128a04d00c140105813110700341d44500d0200c0c41d103070700504124028140380c14095221a42d90107108040307817000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 57673960 1250 57672710 57672731
    0x1e01110106064a041803020c0d0812040302070503100b10050904020706110301080c03010b090a050702150a15120218130b0a0506030d02030304050a0f020d0203011b0305180718021213020103 83
    0x19450014481c3d056001e891401030100270050000118802900d4401c0180b006040c955024168140501d0190700201400f81c5000d042514280a081c546c00300d09041010001e41511250000c40ca643c00909025490f01c0414001c500280a4518094080c030308004400e811403210b58000c60580740480300340d49400c0343c544141803d848100c80350300c0d00400500000f4041c4c04e2103903ca1500550644107a800410b050751b4000561501561034540181c3c3d141c841d094421541c0b00880010601c01102c07c1d05c0034495000070380d0481d0306210450000c481d501c00110390041c070356440e136406030b8001c11614442c01e2082c942c000800044502c11300030310411500503000b50000095a201c3d07948000146042c03001c0b03070b90702d010700c0007500c0c03041340c20220100c1d10000503542800746060540880a00d41c40c0006450401002e491000e44880e00051542c6200e85440101280d48410f50328150b5030b90311f0f0149803e000c0c40092040b402c0c2a001c0c0c0c068a014007402c109020120a8214000d903001d02c08010907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 57675210 1250 57673960 57673991
    0x705070602032517010323100c030605040902030c0910080304060e030d0203161212020a0302030603010501170703060b0f060f070606050603010b25021e01110106064a04 74
    0xb2070f0741ca040d1607442c04c001040010f83e900302d41d0440c8585507200c06615000040c1b40c03841c7c01c11000701f00d00020384810409080030b5061084030010f050885043c403001d00d141d00070a484001541c41d0a000301c1d141c2c030008281a223080c1401e0001d041c04400c41c0d40e03582d6110002000c0d40c06142d43c1d94072078010244608206071000080e81e5120580f20910f80c001242551514984039510b042d05081c41190b00a4a008046034070141c07001540944001da80e92900d0802c0600b19001600301000640807404a00029000092300c20280ca90102e000a00f107508040040e8201d090400710a038082d100003402005040d5800240c031420384100414440540c030391040041c1c81c04240101480c8510234441010b8804017048109036100802502d10002030310364001c5101c1c1c00302c10448003940000c805400d42103581c00511400c40b01c1449000300255030800c0c00052913010581086c02400340c04002d0701c2100b10100c060707104110111849035580351070070007043c96a81d0300350b401d2522491030880c0800004c00c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 57676460 1250 57675210 57675227
    0x1050c03130f1217090325060e030f0405040b010f050f180603250302161101271a07050a061d010c02010501090c030b01080604230406020304050d0207030f020907050706020325 77
    0x95111513181041071021a0101c00580000182c41c500d0719186409c9402c10305000801464030310524259032907040206000948070210039842c100f0840e1000c2e03200203507210701038501044010440603034a400b00354035084010600c1e4400380d4400400814071400101006c141c46c0400c0d036000e14000d07000402d0078150100d029509807900d40b131100d001034034000381c030018040d201e124050401c2c00300d400c007560024121030313188148a945544804018490b0a1800d865086400a8114414540100340d5145a22513000c2c1d40010304050325116040d00f207240380c0f400303e1b14400340d4400800695000050081c040e0800380300755000b05180003001030541d0300ca4000d42c826800306840d03440e21f40e124182800001e00652506454102103611006000c80103a09c8281c05036008080158030303800c1c2030410b541080045407a64066600c40481040082c150013051440c254044450516658410b00191a584a44980100b501c0e100204020b5508e80d021040d04014441020041c40a21040070a0750110b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 57677710 1250 57676460 57676477
    0x31e07050405090c0c0a060b010e0618120102070f0503030f070f051801110a06060f0e010509071b0204020301060315050103051e06031207050607030e01050c03130f12170903 76
    0x1101000706100500304200700580000c000b060b402d151000381500385051154100d822180c80d81c40b108241407941c1e005100c894040801c4440914160b5403264114410042400090040c14164000807800c04c083d4160b4441fa604403d000900c003c140ca08240c07240c1c4200d4401e01d450b810f20340410826031140c009100e4080c010380704c0e03074500300d8405920021071402c20385181c1080302c51501ea2207460b0051240e0304d032040c803130800031681900b46004002c07104030540210041031042d00042186a88690300707240c225882d410008100d140000700410000101c0714043e40203400003000160050385540200190110482c001100948540044003605d5094804003440d5080300541c0c410907007440034040e00f10380018216600d0b640c0c404202105070f001541c055520b03805c2441000384598050003600d103134201c0078000700014909007503540101d000144c441b42c0d40382c426031400801c02060070002d28082d030304855218824160441c000b001003c1d9402081d030800d64010104001d402c000040c0c52110 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 57678960 1250 57677710 57677717
    0x1f090207120e031c05130504180f03050403021e03060612100b030327101103040603022b02041403070510050703120527160504050a091403031e07 64
    0x70880c802140c4042c00c110300542c0c1402910441344003c041c07041c501030451140d0310307416210061401014118422980a90701450a0008030101d500ca00100c82c02e80760f03400088464130069034142228540241d0b000250001010044480040e041e074401b11106001281101c150317946800c01d0064298481908140c0e07503010032881e581503685600101c410300300150172a030400c4400341461b5500080740000d0348070415080600c40316420039071441d24484a4500340300c1195042070319480d0f40d80c0b24a100c0c00040544c08190207185214045944540c07400d00c81107000a5818014000004d5029210f82c2c1a25204084000080c1c10b01240b0441102c400402c3e0911070b502c0c009003030b682940f041c1c504030f0410a6031000c0d400034621511485000d508400c40c003002268030b01000880556810032100010f610a640a00040d40030030620070565000b0f40e0302240300c2d10303004d440601034440501700900341c2c055a0b40d00404218000003840c440c12030304881c02d02000340041d41024243c410389044000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 57680210 1250 57678960 57678983
    0xe1c02010b0d111302030408070201020f03040806010e060402040519050310060302060418140f01030b1b0307030c030b0409052505010f0302092710080d05090d02030f01051f090207 79
    0x40303140c0031400f88540d10050205291010303c1a0b03100c049900c100d400b1140810080360070425035074104400c20301c1c2c1102e24011440c01e0b0032f050750716075554030500ca5004042d201d03400150268595806441c02403102800b01400d0004402000c09800501d0094500078854400c40c4c1581120a0007418100e94000d03140c6440d290402d1a11000484039408102080e51034119220f1075500381d401c0f15204800110703030060f8a5045103400c55448001078840440c0840d181d02c12150110490101d0350890085c4c100001c9032500c900043c1d0250503c030306160390240c9858160f90902c04041902e02084058510340d0310401429824210448014010b09000510901241081e40d01950061015040040c40d41d219505401d1508258450034000c0180a414400511039032907680560200a020740902274908003030004801461406003c100d103104051602c80320055480030b114500e00154410020300481c5030003816101c064441500c81c20101c08020b1000030310b040c25101b0345800c541e2002d400082c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 57681460 1250 57680210 57680213
    0x60203040b060a050f010c0c03141c020307030909150503010608150a06030b07080a021c06080105090a0201080601200615010f0206060a05060309010b09010305160e090c010503190e1c02010b0d 84
    0xf25001008001c885c60380d0262408004030740c6140e00034a80105020041a07000003280717000300c401c12f001e100c1c0d078195401030140b140041d03000403401007500c044440008800c000c1c030180c25244d03440c0b94011a0954604440842c0c0a00c000c91004e202d009400e00a600c60b0f10351011600803034440d44000b40c03041ca000008500560720515410b500300300640b81c00340c201008051424440007802c007200382c03090755540e003c105402d000e00034594881c628070090310a48019400103010140e00410560401003009660041c05200c3e4000400c3c410000c0100d400b45c0c0f8002c850990089489140140490701203501682c5640c80018000e1080b403000c0d140f00486403401017030024940001d0421140c0395280c1040b1000c0d615450901030007107002d00c0041801da40440c2c0082030400d0550042004100d4180410441190004074102d0918081ca045640c0ea55004004040c010040c1c10350410f40d800c2a11182c0111f10004103104141d40c6c0303411004602c903808405900b05c0e804c00b000b4941120140d0317202c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 57682710 1250 57681460 57681467
    0xc03060c02070314010b0f010c05070e070c0602070c0f0b040b1204020a0302180a0e0a020108160201140403050403030201060b090d02010f050c011404140705090a09031803060203040b060a050f01 85
    0xa096041c012914a0754032582d0784100c0070300300e240c4404960341d03e02c110700840c90040e40c003841094082c00c100e103500000e0340302e440e11307024113015014000b40248007142c40c0c18070598081e4201c0350084c0f03045403076011500c0d00e1100c2d200310344a070301d04114203903001080f00391964046404842c04041d5581ca021159a01c2c0640d1a030300078000d03680210080740c00009a01c881750085101c04c0b403600d2001c00391402021a40072036410010083c070a501500b40f03100181d8001c401c035900034564600c008140d92682d41d089024201c5506c0325012120220140420076420001400c1940e21940081c08026158032f119641c034010510301d40d0307024201c05c3e000f40155001d100c81584240d0745207480c0d0b00d4500c0084265007034410002d08104800090010482807120111481c00c19003240c0300603001c254035010000c1d810610241c0100301c0c0c0e83d55050150f0030036000381482c00344101d1000c58001e0303413603490506030020b4008031819076054801e0000113400d40b9102d42c0040c15600000c0035003480442080045 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 57683960 1250 57682710 57682721
    0xe2d010531031202010f0e010605030c19030c0303080f0708060f1909061503140603060f090102040815150109060206131106180a0e040809040c030207140609010b030a0c0306 76
    0x405040041e6004008107402c80002a03940b0794079000070980008000b000c10450300c1c4020210a00c1c0d1410805100da81d50100e581103900000700c6810050042c21001000c0d10091a80020001e02c1c21030000001c040d001848240319080c070701c03000429907590200907102d441d41140e40640c403c0c1c1107a600142440c02c0500d8807501800c000da803d4405895460440c12a03800e600100124049070440301d840c0c95150080d540d40884190041c81c0c5402c00070b020903074402c400b43c103034440524004009002e481095041d240182081070846004400303005039501d00c40000c3d607211031900c0b1443e1400081303500074080729048440c40e40c009d0203140c0d20b6460041800440000c11150010b900304072000d5a42c0f10405000038030440c003a0015031315144000c01c918a04907500c40c03400b0340707000000c00000c9a22442650b682c40d0003594082003410700c1c000110b000b441810f000a24049880d201d00c8860800002c40e144900c00c0b881c02000307240180b00400d96034141c2c0384001007110b4107480d001e000142381604203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 57685210 1250 57683960 57684037
    0x216030c121b08010e0c0613170a0c03060b040e0a05100509100603050c0907080106050702060f0f0313061a130e120309010c09060f0c060c0e2d0105 65
    0x501104182140c2d00000a41e200c4541613445041c1800700b003200384407400400c0b9044a01a18000c0e441e020b9424101c2c2d45c2c410444d40440d50001301781c0340b4405000c2c1c2c003c4c9503031141c6400192526882c0800c0145622254039018614142568042c2c400020342c03000c190f0f4000d0028810a5401e24164014000003041b9600f1409591800000c14000340205405540f0031006032110309041024403d94100041203003040012250040190743d03001411603091640540d29195699000380c056001d521500c1200b0300321031b40000421802031660680d84102e64070804041c40411981400c07060086041d510003a800600c8040e0381c91038a03031aa000d9803944d03034114203890483da03440d80e668038950000c50301c5a40694440d40cbd40c0b243c0f95400320304000900b10b1420442804100d0540042c407000d160003008040342e5444c1605514140210414081c841000303290030b1401c0b082c506100c2040808403a005c2e030402044052034001c4d030040081d00c44104207039400b4100c84071006007034400d43d114920b0b13 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 57686460 1250 57685210 57685223
    0x3020a06151a04080c040204061b03200307060605030102090a06120b03010e15010501021c0c0c0e01090b09090a0f0b040f05030f030f13080414120a05010b010216030c12 74
    0xc0300a2048005690414480b400c20348030342c0f070060030783e050002007222a0b01c250710400003409904c0d0001c090010304545055124200b508034581602c200d80400e0040a05244000d265001082c0000040140920038507051010300d07520300616080c1c0c01002d00c01d07940120304520500626109481030495040102804100e05002902003800c60307011010b21507044d088481840025140e01d00e00d140100020b200514410a1140d110090078a1410400d000c00150b41c032007205100000c0c81d040003802e41807180069950756100c00380010300c0380360259801442c031100001c44c0f444000c240d6000b000d42000c90000c0c0c4900d5542d8112031410020070850b005a185039010010802c10006000c2c2e1280401c081903803404d00745851041200018403540c51543d8440400c00095040801c0e101210801044e00358900710b0350340041d0042d0b2505e41880c8161160601c0041404415005010390306000e03020782d886101a000707020321500b1540005003000761024401c04c091150302004a000300e00421 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 57687710 1250 57686460 57686501
    0x305031b01150e04170306060f0c0a0b0c0a0201060f050603010302010f090902030a0b0f030f0c0402131706160c050312040303090b0f0a0501060f080a05070e1210050604020703020a06 80
    0x9020305950351541d04241c0c06041410300300020000350700981044801401c40179819031904400251051080c0d14089035044004a8a031811807002c010300d144580c1c0c080c2c07c1500a15024544441b15003005400b14010360074210005420240c003190b460694601502d21440c5030300f0f5400644055641617500010446000800100d60501e44065409000c1202c0c010491450182c1000960307040980417500c287c20010b440074021000091301c0034195015100541c89594004000c00001119480317008201c0f24401031589610f8003080c880c0c80b521840b01c0d1071011000e089400c40780b290001c2c40c02802ca034010000307114540300380e40d02560300910926010520304900d54460615403016030b50a4142c007454414801e013840180211805400145441c004400011034010000c0341d0240440d202c0564a82c04104032900c24003104152849c090300007022068484111651511594101e80d41c03249401c000c1160f03403500f4003c8903400c1b509680201440006510780200514460011004010204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 57688960 1250 57687710 57687731
    0x1403040c0e0106110c1008040609060b060403061508060106080c0309120403080a0212030c041202060c0613030f08061e040f15060e180c210a0b030c01090305031b01 72
    0x1070424034007030582980d42c5500800410b0449180210402110f0310404d0380d140480c034900d83c010b00842c3d0250b007240d004201440c0c2c9080490040c042c0071511508010005004410300c080c43d00583c4107014801c80c41054540d80300801a1101028040c0074001915240469003104030078000d103410080700c00c1550100030b040205509694480d500c1191031000201e0000d181c243c05008071450248044007070745c614a802080d0f9a4140302c2c0f80524100c903c100704000d000d64407042c050314690050001110f5840c01d1080b8500107001e101ca00880c001401c8081d01100140310b00345450240e4030141c26120050780348040b5100c08000034a01a070440e40d201e01c4024044030390b00400000714020f5400701c0c030107400d008006003007030303a1804414000d040200c1c0c15417140281c0c01050b0750000b8003d200588038800800408000744440300130051100800007880300c8251194400e40044004804441c004504a001960f5000341480060490342080c41280814007001d0381c1009d01c140b81d0000080c1c0840308 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 57690210 1250 57688960 57688979
    0x60c03071b0c050118210602040906090905060a0b030a06051305120301081209101803210818070611190515091c0525030f02100b011403040c 62
    0x34440d094580031189002007000d940c001e901590040200154a500302d03003007204040c412006c01450128185948080b00d0a100c219410796001d00451502485400d0317462031000302030003074071109aa50740a40400325110392a1441445101c482c0a4090030f003001c41074072801e000741001001c02010787c0d0071561010002d04140081811007900705240b907182d504200c0000d140c02102000c81c040040d0800151090b541e40c1ca18000c1190010700d80203010603a207000d42c0490848030b0340001c04943c0344858524481840082c281200d140b00d6a0389102541c50fa1900139a4150f40b107020b500f503400c400e0f02482000d218019082201c032050084031041100d1110391030745944020010385103504010360f99048900c234403241c241c1008070200103001d0141195450020355020180020520000042407241c807411010340c19a2419100d180078059031035801c0c007a00c4401c00d45d29031030040c0124100c082a00707100340f1410840c088185e42d0100d000701c056403201b01c0f81d0300141c0113441640e030085000804607407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 57691460 1250 57690210 57690257
    0xa0c0306230403030c180b0403080a110601060905030d0801050f13111803061815091603030203070203060718050409020411040312020c0d030e01030203070e03010c0504030209010803030108060c0307 87
    0x109030390003d44082005c000600142020714501d1101114100c100680d0b0314040aa8003560780000717101c0c0d42c80d0315003c41940c800401c80c0d0140c0b598004c0c00300008009402c640c900c1c1c2107920540c15180c11503045442103909031401d0040d0740d40030088004012150506c041103607004441d00da800643c8240b03c0d00a450180c02c03413405082600510241c0e90b40c1800c080c40640d0300040b4003d0f820341d0a040058081d0780703403070444c195030103000031550000c1c0e00130400304403000d0a4001d001809100c4d645a05009460340c0c404042680603108220110300e2552140c1250380a0701100b0110410850500381000081e1207400c105a0b4880d440c0c03c400300241c038483c001000294400c0d041c500d004001000040d0500001e00c49040c810805014642c0209820070311b41d008580d400d190040e44e80c0e80d2610140d86800c0c0c00d001d510f030150318094066810a401c80000e05c1524021540c03010b0980c0d844c54482e641384024001d00003036411200c085070300c0c004408003a58001e646030030110440100250071140000c1d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 57692710 1250 57691460 57691463
    0x5010905100207060b0604080a02061e0a050a0f09031e060b06040906031415072a0c050310090c05010503070504080d030501170606031b06040b040f06030b030a0c03062304 75
    0xb58005115420448140715481d08113100350f03102400e02d4a8400c240e03454031280003002c0d006510003d90141c91710a4001240a150b01e601549a1a40004c0e540142a134100c05400b901107030081c40d508880354000d0040d48101ea90040341084501e0580f1840a5480540001250101d0315074881c1c01040d40d03404045d202502914900040036440d50403c001251401101003c040d00019152403501508030718440d0301942d141001c0700b00d000510350200b00d00d520449211032001015900360100106025400c00700c6a0480c100c0e21425118040582181e1060a0090100d00d40354400c10295020f5009140d100b6881c1c2040387c10296101a40c03414604683c0350711000030b540701c0041c04100601540441c00e43c5245006121a10b0403d01080e520001d01c41c1c814480c08054451450641d140c0c3c0458029044400c505615075541d1034080f900d4a01ea4022400428246a4602d8550400142c032000d62500f001a032041e4074a10b495040041600100c05a00d500c4540072142e030030600580307018042c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 57693960 1250 57692710 57692743
    0xc100302181c031b0816080705010504050109030f020c090a0e0703140303040c060e09060906030c040c020606030606041b030b01020a02060a020a0309050402030108371a07050909070c05010905 84
    0xd0a03140c024081c8101345240380610546144181c04540c1134826a640c00504d81d180398596101420058800d002e4500010055030800c030400081000641200a02d94440d45440000e0218042c1c160388419010007900c0d001141240043d02c2d1490702d403c60303001c01c0800416181c8154803a01d8503135a0140c400301d0681c0c03036800001404104001500814000c1080d0b182c1f03110181046400105244c1c4094062441101c01d04041800c1c0e5a09103c1d905000c100200104024543c0c0c4030081d49410048900610a02600300001c070780d1309240c05503440b00306003543c0703448000110860680041202042c058114402c1c14103e6005881c3d103801442510340315001003a00d21060304c1d0050484185420981c0a07074010320040110010004054141d04951140e42c65a0a05903c0c1d2010066520640f021035074000502d10b001c0c080c507007a9155095800900d0b800b06a5580c2d83d0039142c1d880385850043d0009000800a08024400e054002e407141c0705a0020503030311410349603145404c54201031201e49 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 57695210 1250 57693960 57694009
    0x50603091609021305190e090106180902030705010c080403050a0b060906010c051f09050706090501080c1303080a020f0706261b090a0b04090b120c10030218 69
    0x42016441c40002860001415403602c454400b00c048580c2c014803619010701001c90103546424020310071203000d002d07904080302051500d529020f01802040c402c400c4141d401051415001d1010301a0501c01d40d0050020180306250900444a00c41040d0080e56006401e20011001860600c43d00e000d0b10700031801050749082c41400c100c41540c02819190500500811500000f6004035111021014941e0010b40c10182000d85002400d00c010000300a4052a140860025081000309040e1107080e69006041e944560300c4050324841e80e149510610f8070320404000160340c85c0c0051002c40410304c1601c8420344035034611407400f03031141c2086000c07138450f001486520300882d000c84400d00300c2c045800300ca414100b6034a0784646059520880400c00018440241c0d101c290484c0002c00044100640d502c0da550a0f00000f41180c54040344a101181061000c51070000349440c1140c00043c1b48025000001109070001e500000d2403c030948940c44010b41d69036190502e114404c4040c0c1d00403080d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 57696460 1250 57695210 57695233
    0x11090a030b040812040c0518040b0c0307020a020a1508130809040209040f0903030c0f0525080903030d02030406050a09020609100201060f03031707020105010602100c090317070b0907140904060605060309 89
    0x10f03001108c584810180e030300000f00400320300846916500043c00c1503000c0d5890315001c004a04003040ca8a010303400c581c00380000290050140e4100d9003000d05999012020780300d4020211443c0e480310f5029290100602c041c0d140351915a0042034400070091001401c844c0011803001030302c2c0c03c80d000380c02199a43c9002c0c00c010360004003103095070042d840c01614048100070f0303100c07400030200c0301034114210030103212042105100c112410030b41c000b03003100d0b00c1e503c01d2908040a540b04072811100340f82410b0101b1038071406802110f030301f9a401040300d400d0000c80018002c12040d40c03804201159260b100004014903c850100061401b940ea074100c0785021028103015560050a68011a0304d042c004104541d404101c50303551696000f008600041720b00400c4802c00c08540018080007205144a040c2002d01c40040184510404094001d50b8074280711340d440c0d00440c0714101012202e581d81d0603861414820781075105114000010b0002d8450f408111150000c81d00c66500f54807242c05000f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 57697710 1250 57696460 57696469
    0x120608030c070603050921040b031602070503070b09040c1701080a110a030f02010c05010f021216020111030a0f02120705091309020a1511060c090411090a030b040812040c05 76
    0x9001c1c1c00796080500860400c01c4100c7d0340d0b00c480404040403072a031355a400c03981e81c1091048400404620300f0003500c0703080803202401c07001c14816801000d445407520005003401c000c40d452041b11440020203091513412014440036010b4403041100304a522030002442d20726200550b0b0281074030320001c1c605e11006283c40e41400c400caa040c0c41c400c51801c4002c10005524003047d610b05039080ca0804a911240d25205024191404418050a001203414681846294011403203a0811200504000100c10b03041c2d081740c244600b000c000c18000c00000d40182d03000c0d00290000102084010320f44a10220a4030482d4020b5034281c0010381c0001f1b81c03810328a0f008a5010440d43e003580c0c02c0081456030380c0024181041881a6150002074903031418240d4000d610b03c2007540e40400607143c1900e40181c405042c0e92208a0051160f80b50407a07078455614070105849522001410382986141141c545a161180040044034002000c2001d00c501d1135480c4001030250307200c0c81c12407411a08010400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 57698960 1250 57697710 57697723
    0x3030209010e1203030a021c0c0206060f010f091403100e030909061f0e010c0204150806070f020a0609081905040f1401020604030f03110408030c0c0303090109090c120608030c 77
    0x500c0f8060900111012180c0401125048040958010f0f904c00c0131000e0720485001c5480700c40d141510f40f80d10318404a0b000318950b4407800301190300b80e0540c020a00190b8000800060301c000003501c0746814401b1607000d40c2d807152420801400c075000103244604090a5941201030a105500082020156402d1200009401c00c1c02115881c1c0380000800a4000412004203c0c80800c03403032031102c0b080c07640035001104419801400601c08a1511031071260658558416480e07584a01c50000d009144a0111074031200718580c081c00701c010441e103483c8041c0c1313212001036902400811042907108a507001c8070780c4081c1e06440e95511503207002050424841c16900100c2501e6140c0c084030740c00da0b804500141e115034141002c0d0010b00c0c8420080303009251540058505d480d00040110704840004041c125a13403048086800012070304041c107031a40030b101c1005021607039401c81440301140541020510350741c4c80c81c12250b13440f40004c1010079110300760700800c0340707800004404500c2c40c000d1200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 57700210 1250 57698960 57698987
    0x20a02100b12030708070f08070b06181302152a0c0a06050406050d0f0501121b050312030a020909040f03020c0d03050405040905010e0f0303010501180608010902160f0303020901 78
    0x280c40b0020038000c2c5030f91a80300340c5800130f080181c00903008042110069041d1000f41d00030190343c1d1204602d20700144903060551b0300e144121b291002c408110740d00160300030f2082183e15540042980f090b4203020184d10f0400e0001720b8154113004c000c0c086100c00c00e84d40030740f0f00a40141d0780321500f00c0d18040c1c10811608aaa40182c054400600842c1d8010080324212451403900075076500209840c04000c0100b1540e0403030039030405c0000075440000100003418030340a403190009607881c08031000c0e0b14464900c00c00d03801d60001c08544d4442d0b642c000207158041040a009031030125210001840703003e0849040742d080003045803040505504100e0801000c0c2c00742c038010b80203d03c0380ca020b00240a1b5104d82c500c02c5844141c25002c1201c00e4104c0c680c44080d800c00c4502c3d00700e03800320407a103030f400900802e40000c00500e4000060384460a20700c00b1a072a80e20b840c0026401e20007400042c0d0f112600328155540c01c850305400117090114480031042c000d580c0103071102c5490000601801c1d40c2d00c00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 57701460 1250 57700210 57700219
    0x120801120c120812041101090e1009050907080604050715030e0606040e01060503012f03040b04021003111207031107020303040e04051f0c090b07080702041a04020a02100b 75
    0x2810002590108141e030664088110071aa07180c12450702003028411440c000c09220f540d20180820090786c1b042c4031001000c242c0366040c40c2c0780c84844a01171418201c45400d05401da106040201c10041d03440242c00884910590b001c064a5003003141c80c0031001e44044410750b100316010000000481103101000c8a6441c00703200f0380c2d061030901581c1c2c00001c4d0409205d42c0d9241d0000c0d000f1002540550000e0901500901ca403014134010070300c561058012109041188000250700f0100003002c580c4100d52200418034540c41e15000d2114414038407408005056035200801d0042402001401008014400c0b203130451426207001015a0f1188581c5000b803042401007400580c1d01000361800d54502400102c01c1e9512030401c80c5c0751401c80e0903d640f00301c04181344070030580708503081500c0070106070b10f071503d042e659016501d031a845903180160181806121480041c5000d0300013074030000100c000729402038070107400181241c3c003003920140580d100c0e0042c40c680818601540585200864 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 57702710 1250 57701460 57701489
    0x5030f030406051e181c0201050121030c0308040c0e130c140d0605091c090303080105030d0e0607030e09070e03120702010c0803180a0602041d09030a0509010c050a120801 75
    0x7085095418005000f20740100c4240f2214175110784200658864035000d00001403070140071103000390080800f0301803a00c401ca042e0b9402d81d0101d0411820740a4103525a8030384a440c0c143d509c0880d02c001c000f500444a1016500c03000444440b00691140240390910307220002910360f107400510442541e00c00091072064805090780c43d80d9074007012003c560014004070765650381c01040d0f82000d061942000b5000141c401040b81e45034071210341403d99100c0c0e140c05615036250b2080640c0c0d405c480c50760000281245c1c110481c0c604201d000b40070b540388a800e01d41000c4958400080d0310300c4c0300b100c0001c0021307840401869189020803440c00d0801d0f0340b0840368600103203600000c00007860f00d003014252110000129941c03114415600c19a800600c0a0b1801da07007061400f240654018443c5201c840e846140c25a802c8015039041c6010700c5c03402004500e0170802000903241500704000990501c281c1d001120003142d014403515070807500c01c554030b407568168498042c1420b030040c1c001488a45004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 57703960 1250 57702710 57702751
    0x50904140405030415050403020a24020105100605090d02030a03112103070e03070b0a080403030e061014180a020a030c020f0c011d100305060301050a140c0f040305030f03040605 78
    0xf10468040c0c0d4807940b080b0f65003000303905083d9020b21a650000f504030001c43c40008005001141e01c0c1620a81c0f030501c1842400401812400d823002540d02807502c5982c16020400140a40010400d42002410442c802000c036000a0f08043e2805000d50100e0400300e030104480e801400b00300103010009010041190320380b19896202d00004101205100c2649000e030059a403c002110042c00130214941e07448901c0e050040079600c00750750071404203040c1001150b0040307001c5a1944100501040065000d01e0300a01c004000c064410268010441011104452a1000c8000d1081c00c440d8405640c0d0888580000d085070407a1001408541242001c0c40b05442c010070304080e000c40c2442d103002c540029202c90b13107072034a00d2411325a00030030303c01c0720440642c0c058100d01e100d614103e008200a6849050480507920702c808443c011a00150000700700440082c054031b9282101541d1504080d140c4e50394518550024401000704907000c0208020000d480c0036143e030015100c1c0b181c00305031aa9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 57705210 1250 57703960 57703963
    0x1a130c05040506070c0e0a0c08070f05030f22050a0c08011112070314070e010e030f1e010207020d050703120507020604061b050607090e060a06051204030306030206030403050904140405 81
    0x10350040b68418580000c02500b8003108059200c064030002c0c401e5121818158140710007000f401001ca004207118000040f0118003c1e02c071107200e18460388845255503110103505054110052a101301035100e2040013010f103071108105500d040c85007009150888441c200742c040160507500100c1268100300f07842a81e410210142c0303200d50800c2050400c0d41d1a00101038000c3c11002a150035001d920300d0800c4500c0d58068840d944052081c2c90b0350701b49252441c2456101d4040b50821141e070f500544600c1d0703180f402c6100e503c000f1400742000600302040c6070300082c8a0104000c0a07155031b0b20401c41072041c01020300401ca44070505080c03080c90f04901c2d40c00b203111805144501800e0244103111803407221842a29005a00d600806a960a181c00200a4500d5071140558201030317150800007070090134107412041c00d56440d612951700303200c804107030310a0a2100038011800c01d9183e40d40000144c0740c04028500880c1709403505034070f5400c98000d00046944050340e02c0700000d055020b020102c1d20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 57706460 1250 57705210 57705217
    0xe010204121e06110909101a07050a0c0303020106080f06010302010e0d06020d06090507020f012a090306050408030f0702011b0e06120903030103120513060806131a130c05 75
    0x1480081c42c01206a610410940801c2c03503040070384102e042c2a516410300c01c0f0040242030700c001c100c0714100ba50300c1d40744140702c100140f4000e40342c0743d501d45554070b4451500c68010300102449942159101105a5603070070520005500440160391904030a000924040c000d0400620041d0004c0c0741e150714540000b410310140004060181d445049101c046c8060394045640701c1419050520940e030b500c81c40c501c010038049803030714014014000401c4440e40180a58881c101621040030807001e00c040c01503445610b12104c41050010a4000000156282c013502d48141d020340c000a850745016044949030950082004045900d0828404045a2a08020705079220181b510b545011020000310388070744181800c040300301100008108105000100450507684a40c8801044115203a01074510f400b92100e5062600304200e407d01c0300d140310b4823000340e100c0e200070500801c507034414041c4001c41d803001d080390403010300450042601c5d0a00d44071031b107041c03d0780c070318100801540464014510700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 57707710 1250 57706460 57706463
    0x5190b06100905190806040c03020108070203040506030f0603010e060412080609060303030a0e010b06040e0103060c05090d0f020f130506090c0a0e09042102030a0314010303080f07022b030e01020412 87
    0x344d44c1e41080694403440301401504403c4100d0324182080e05244a5042c0b00303100890003e41c0c800001408184080241c030304544025001500307503150400e40340014600140101d41640d0b80380d075106d000040400045006a0007501051001040c0c80b00042c24064000e0603a03002d80c01640500c401c40d00c4c00000c42b54484e21450b800111120083c5401c2e02500031448140c3e0b11a134042404242ca00302075000d58100d030701c6a0780400c881c078203c40090300e641c00780a242c0d580c810f48034000c81d00469180380fa903075a00b070b100518142107480d240b00000c1801400d45100100240d6038010000542407000d015908070820100d003a0418141c0300d8028420241e264900f4060b00030345011034100700c1c2913104010f884209202c040c6e4610f48090000395aa0407040300200040d0500e0b00300d07401640520361040c166509030340c0d00501c5540700d102103820f05e00c0280c1200b04510178039040c6089043e0650744569038030046c4082441500c0591001070a99080d03802d000d006901c10003041048521220b10f800340c0e203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 57708960 1250 57707710 57707719
    0x504061404091109090312090c0105040611010908030a0504020f030105090601051504030206030a0c18030804090216050f030d0b040b0f010806031005010906030303111303080903070305190b06100905 87
    0x16881490b1011454103804012500200c1389014000c0c5100040081c24908001643c42c1145035141411143d850940d400302034003240c2c0800090089501c910001d40d0340040e50300000c5807014060343d859940d03a01c00c507003400070a0b5440b4240300461401e94111441003208070020320442c10aa41e07841d44800042c13140714400e504458a44d190881302e10300366401190020100c035200e26101b200213003e0b1907000440c000050000c0044810b80441000f2501034a400c1000039080c541080d003001c0007580190243c0d0200d8154414423400140104103100301030040c80042d58079841503048690603511560100761080307041c21003482140e100e040d0990b10000003440d01d420130340c4450b4080b0307050050707640034981e64500700400401c070707220076810a20440e40301c0d82d0f00300b003041507410302c850140c0502a280d6900c04104041000410148005403000c401c0040503180419a60780c0c07501d10f00740d40085c49a052185032665642885440d5208580c441c9081d1003030301454201d410000c140d41240e02a10744203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 57710210 1250 57708960 57708971
    0x50606070314160506090604020301060509010e0103031206050303180103060b0715090201050c0a0b0402270a0f02040506180f03010207020306010b0d1d0a0b0a0605100c060b04140f010504061404 85
    0x400e421900824161303042402e0783c85500b040840300707840307031002c441c141d019601b020000141e90520300e04090480c1c0b03d00c24141d07007d9007075070740813910680100c2128a4050312000b001c205070703800348001c3c0208090798000100210003c4000b41c192000c0c0d600a0315000b005006e030601003481c14180c1103000c0c000000026040b800c0d840140c907540540010039a081c841c410100d410820700c817411a004c0c1d80200d888100031502160100700d440c10300140c0700c465002c1e802c0401c0002c03180c0e8104001403202140b0160420761610046005600710340306080c4040403041c002000307030621038801d101452040c0c00039403900030903401103640c1c2d0320107200d654005900094988160b80032507000d004400394488001030219040d0a60b80d603582c00e100c00a42e040910140400ca82c21075521482d0121030018101282040a02d10305980b44005101c090310304030384644088034103540d40c1c0311b001c403031000c81407241207142044507461f8007407036058000301e010303e14100f4148000020820300000101c0202e501159 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 57711460 1250 57710210 57710227
    0x140303040f08030c010506030a0f030e0109031202010b0429010f03060b0d06090c031b11010219080108070b0c06040b0a0b030703031d0102071526040c09050606070314 73
    0x1540c42241d10041c9890030a8402140745038000c4001c0c04804c94120003804540c0741c000406444620540000300070780c2c464441c07900001c1c000d986503407080388141090f80ea650795a40781c000c40c500c41c103118600140d6544a04401c54542032080481a800c040f40440007d0001e482c180303210b501381030055042c861011010360010703101e60422400f4002200302e20352074020b034221100107000c00e0702070320010508110b828900c19201e4800c1002d401c4484000d6841c1070080300c01542c42c1e13201c0c8a04102c1c0c3d5502000b811140402c0400d03010314404550f500c83c150b0798034044019007805030540000040341c004002c07448180d01d0018031240c100e904031813658056212104260000c001c12044141c060058201c00414550407151921010000320800204940782400490700c4070218040d07400114810002d90220500c9510000000307406c2e840c0400050300009551310800704112401c903006401510140f0200400d03009003074104a040d900c8504201d0700e5a0044d044900b100100f80e8006030119840701c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 57712710 1250 57711460 57711463
    0x18010815091c05130e04050a03050f1b0d140f0a18080d0215010f050102370c06090b0f1c02040b07140601060503090307260c0a121103041403 62
    0x10282d0141e8405905602042c05014045810a8143c0c0100c000300710000196200021101c0344285d40c42409040f0b1010643d03000c0c0c4407908000f07420101000c041c0010030302040d01003008404541283c3c001c10409050713210080c40d025600d0080b05140d6818041c2d1034014511030152640e0f0003850030100c210361088865242d280009500000184c81203160084410790089030308080310700340701035003081a078860001d98180030039880303807a006038013140203d07006c4040d10801260301150a283d8985036a0b5207000f020300d8801d411380c1603441c0c030200f00d0304104848d0059400c5000f800c40aa00745c0c1014442564502940aa00c08039103444540d40c20a00c482c1c0741c19812603014013440031645844a03800d0a10408030450142e42c16494171883e000402d1440c020070517644542c40c5c100c002d52510300c01d9640c0080641b5100e440e100c2c00c4d041003914602e2011500e000c0d244500915009204603452801c1000341c003070083c1c03158800e01c030312a60280d00514002c01114251104448030592440058001c20b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 57713960 1250 57712710 57712723
    0x41116020114030a0f0501080c0d08180603010803031806010515090406030507090204030302010f151a090310020c101407051804020406050a020d05120604110c010507020c1801081509 80
    0x2050940c1c03000007001424030040c5c0c0070042c840403801c0c3c20045680c0700c0882540e5a0400c002d403a0303000513046012000903041d40010300020f2102e01d01c42850328241404504590001c1c0c01045850300044100f25101542840414200d1145001040e0315454580804c1d00c001485d0301107102e907100015840d2040c0c031182c120200840e404000c440320669101070034002034116020450065007040c1c03800030741844901600c095083c103046881c10303151904950351090b030816006c52540450500401c620f6903414031a000644810007070240e030311280060401c1c104445490844030152a20380030100c0c0a200d42421a8010b81e20706116580b0144a1003800400141d400c8107580a4000a400b04d40f081c1d01002910072070780c103034003210502e400030700c002c1e2000d005203641c0590003021000050403601c1d29400103407807030000c803050320b1802c1a5240d1040c20b40d00700f2540030340940e00142141a02d4108041104200d1000720031841a550404021030b4981d00b060703103180d8926604102141e02c1140c2031109 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 57715210 1250 57713960 57713987
    0x903020c031005011503020309060705130b0c010507140a020c0906030114041b06080903091e042a030e060a150b0313050d0809030a110c130506030c0411160201 70
    0x3101c400034200002c201c00b80c00240074458654054000441000e8024000e030380c0948900c0380601003e96401c201201d880c0c0141014001380860311100143c0262440b008051500c60708001080b580b44c4200082c1c11503008628110140c84204070041c01c25034041249030140b04211401900c40d100c0300c000a0141003240001c8218402d22000d1204022005a58400c40f907000c0e42c118000560703442050f074134502e0031210320806400800120a141c07030060ba4001d4881994400b103401a80c2c0c0758081000c035101d14501e0300302c152041c03c140301d001c98691819258a60545014003001016801d0203480c1c8201030039054400c0e4545803508111203d016120015203100d2601903120300e000440c0c10f110740104213080e26079004086802006910400708184550b007071134010f501e4581ca26070101c500342c042c0c007241c052a0040140c1c402081c0d946d0402c1040e07440f080f26000c1114204541014105251040034520580c94807140c000740701490020390740031214a61000c1c01c404010300060740d001d2481d030030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 57716460 1250 57715210 57715213
    0xa0b1f0602010605090702010e06040809010c0b010902031905010506070f0501020910021005010801060e0105061b012904090f150207051509010c0e01020717010605041104080d050301050d02040903020c03 89
    0x14045003440d4150b0001c0b08456040345d0458440e100d58009a023210154805603c0720f030070050000d0701241140c00100115003061400050104141c0c0380c01c1a080c0080c0c20000b82c0c03940000038031074410f00060b00d18149032060141040103515180025145100d01c02e0002d00501804c2c1c6214140502036040e914003132400340100a4003640040025145c0b41c50100d41800b070381c9400000304108505105200c143c82c2040d843c5040c0d6401c11080203240d13003010091200a144141c185201401c0a000d00406194030090301900c9402c00d40c5484012044503400e58000c03850442c00d4000710745a8500d03840c0f0250811400000002c0050032680684540c400c00f41c844d00c01c41c240c9403a4016110074840c85415103000030001100e1070182100c03500b10904800d030059005107001d0086100f50070400c269440410f0001403520303503c20114058035034501c00d4002c42c130004201081032110510128490003041c0c03030154519814040000c0030480b030140040c0c0940d540702d1407081054002c00000000035030040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 57717710 1250 57716460 57716521
    0x80102030103030e01110109080403020402090613031b060509030c060c0a050a0f020901120b07030b0d0c0b03010806090703120c150f0b1c0309050405040516060f090501050c0a0b 78
    0x78060113240b81d603600703240044c0c0c0b14006054584418810452030a910900c240d18151640c1c00b040b010750030010341142e120008204035604014207400d490011403040c400200c07049598001680c41072800c0c2e05c90401d129040054043c20f1380e0214011001c80340c21103555450315840700c0d00c9803410070b040c43c0080c0305110349641c1806212005c1c0040524a20071104441d00717a8a40e0b0201d0213002c12040c000708542821000300d15018025081024401b01c060315402d40d0740e07001e840b44024080311360321100c5001c50001c014451508281b0049074009003040041032440c0c03030340e55411b002c000010201c0041080b00a10307001000300c0c1400c00e00046110303090900000480404502c000c0841c00a00381c8645c000c2c038016035088007844c1d01850380701c1e00354865140d06403410003408003903c030042084400e40030f0300002c0740c074541c50110030801a20840d40c070818400403000b4040c11075078213900828140402807100c4c0000040005400c2c0c41103070303c1881310965460350021490b10012100707c2c0b03005441e070403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 57718960 1250 57717710 57717713
    0x130f080a05031012030806013906060e040506160201020f0d1b0e0d0b1009020a09060305070203040e070e030f030c0a030e0a21080f04030c0302030d36080102030103 72
    0x100280d4003e12010707240001c055641d550000c404000841c008004c2207004000516660280f00380704010f0b03603001c800403002d2a110700070f04280101041500d803c4076207000c485050001078407400c1c0107020058017102c0641069151141d440d00001d001200d50540d031000c0d058002c2c800c1d0103903041440e13440c10640c1c44840150070100600801a81c0b907030700000d13029420702c40b1407040d100c1c1a4004805044030b00284071688402030b80c184001c0207500110618800040e0041c801d2000f401c54014a0340c1d90601c1170300b4041c004059501c040c02050071940240020301c440c0c005448081e40110940c14007406800e03007035001c42c1c10075055000c000d40d14000480c0c84070800030003081406c03140784aa03071a03584043c000d030200510f44040340522014030401e07038880c01501c0d5840000211180c002e16a080c2846200c3c4401030300380c2c1c8181c0040701c1188084070304004508080003003123801c400c0f9080c02414408480d840c079000c40c003030b0300c5030f400060203a440e0320303002440310039600c8003a01050b0001d55a0350385a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 57720210 1250 57718960 57718967
    0x60603170a030e1f020901020106030f06050402030f0601030305031303020c0a030602041401081302010e03120d06051509010e1908030712090605180f040b0d1202010f020c06130f080a 80
    0x1c41220010a042100f10346040300046142c08444480000341c24034060310032480c5009411462055040d50758410010000c40c2c024070403400b0603441100086018a00783c8107140c00c1001010f021640c1c0d5100714018030020b900300080d00e070b02421101045900c44840c0c11700703d03d880c1d1349032070003a000030b1009404070900401d50000c10645082d0a1340a404c190018011104404c045400b0b2100a503070f0b00e07981006600c108004c510b40e40d0300404840c0c010003501440031b410b80c0501042010a692140100030301d040c0a510402e404d012018100d040c00d041400107040190111401361198088880a010f400003480d03aa1014001d504100ca4942880b03162400301d03a03c2c0c002083c0040780e1010070006d003c4d41f082c011942c7d15100ca44041c880080c4040030700680340d481d103411551054581604c0005911400d1100900701d0141c031400c0011340300c0c1200a401c40d40350f500785004650040080319180103000a0a580212886160020004160030703c1e0000c44100f100041400d5070018401f65402d50 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 57721460 1250 57720210 57720217
    0x40b120a030906020a08030c0a030b090c0702010201050109050103081903020f0c010510050303090307032015070c0f05060a1d030d0f0f0201050f0109020313050d0320030c0f030406060317 82
    0x300b0388902400680340c40301a1380d5085060002800c141040001560300300380f0501805e4601d8950902103400c400c850009070100b03000f198900d84240c40442d029065680c240580341c01001760b0042000103505544903507110748141ca80010203000b1120704202041c0c440e030f04950088982000c03040d10b8142404295018040c00d85103402c1e03040c0100e0000c00c0c145004003c546644400400030510785d49940d5a0340c810355000c00311440c400c103c4654540300c1c1d0300d1700082d42580b24901741a10782d0729502490420087d0009030456050411224030038403043c2c55030341c22200d1042490a007109806c02001020107046200010f4640500031804105401500510b120000710056210441e005010800c105d088910442d508a400308204004110829243c0d0096806c00100d20040750800d03143d4540500c1d1800854405000a54a041c800d100c2d040c811950440c94171000c03021451070810186c01082e40c02911a070744002c03000000810100006640158002c66000002ca030310407150b4440740e0203039003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 57722710 1250 57721460 57721463
    0xb160c02040c140f07110402090105250219090c080411040216020414040b090a052d07061805030a0203030a0f0504080a0804060e06030f0c0306220905010c180b09040b120a 75
    0x380c955541b40d440349403900030f6541e2120107945403810091004650340b2404401038400c220b4115038200c40c005030b00c481010350605041143d89419603850036501d0011100d4450023402013111030002e200000c0c0b0340140c001c514090031600561202c051007205081020f0124000394040e242807440394240c020b20705518480d0b40202c1140601d80c1d03a01000c55141c95140c1002055904500310711035405005802d104009900780e01881030410640202d9441d0032006e820920106820f10824901000042e0162029150a4000c0c00c1071040e1540800e40e00c1c0100e841480522000030041125180f01300c0503103008061500c00c44507940102e0074013050a90142c010800068400101b0302802d09008044901a000c82466011243e603581580350701900050401a0b201d0f401b44940c402003211030025485621180d000042d00c20124070788175003128080c0341140c05010103c018121020780c100f107844221241380c60456030300e2001d900001c000704403021426034840c40c404a031503011100043c521011300d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 57723960 1250 57722710 57722723
    0x6030c030b100b03010b031012110a050607030507121b0f110f030309010f030f060602010501140111190221010b0a09060b1b01091406040b160c02040c140f07 69
    0x2d480c0c0b12420600030486029070070002100f00010082d40b00c0000045070b20460f1003113913020140d201e09140b6880110300c501a41c59401c00e94510465240a12114008120031a2164642034007640c010708240030301100980f14001200d0300614050040408c034056000050360014445038a04e0012203a4440031030075180300a0100c2d90f91040e060124074440c50040080c01181480484001114814070b8078504801f00354031248900b07140703261400f41d000035081e903030000b05556050441d6035200c000707200704040c1086461880c0031500303000440c80d2440e26105510f60304100704a800800e480380c01070000f01e920004070018051078800c0641c070400042004580922455941341c5500301a51414050000c0303003241048513074122612201101071141c4ca0f000081000e403600c2d213075901e01901140629015801a4041004000380c12080395440914000000c1215809040c010a6288800802401103995508003c0c0c11030158404212076000000c0259540308c000707d002016801c900e40c1101c20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 57725210 1250 57723960 57723983
    0x2090f0307080a050f0303010609090b0102070b18031504030507020d110607060c120e07181401030807031407050c0d03231305060708030406110d0c020a0b010602061605031906030c03 80
    0x1e0005c04070407a8104c2c2c100355956100d05040003c03600c020301e00f201d8410706611a000c00003030b4002d16800070b06618406110082c0b10340b00550241418003030707030b480e190104040d0901000002a0440144c90a941c1c050f01d80c00c20318285480e00d8804104406669503201c000410b00300c0c00c01c9030903000852800103036a81c400c5410a5010007070169107510342d0a626a0700f01c80424008032400b104110300c401410ac0e0b000c5010345900c038110708420f0081e0400e81d41d100e07000400409141e007101e08111003650040c03e40e442c0408076166540c841d620050743e00c5c410150000e0740d40501d841940084540103100c108410000d901c1400291154860003200c400d207080004001890318100c0c007950031040d04069101c0c40c45c2d980d85c0c1c900c0018450355400d00c6080105000080381c00c9924850300002c40300c650018907010140741459241020160700a20840d80040f0421802210282c5180f02410182c00c01d2500e0f030b140c9071000c8903000843c0398040c0306246041c00010038422010305403c02c503070185280901 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 57726460 1250 57725210 57725233
    0x1407060b010314060d0b190f0506040b0a030c060503040809061306090f14060c070810020307030605040507021b0f1203031801020405030d140405040207060207150b1302090f0307080a05 81
    0x160f503030440341a0b5100c1044603100c0c0100b04030110341c81c0d100d21000e481c14a2034000740038010489409a01c000c0e151075544040110714200380c8201d031113032042100c6040030245142d0b511b20708064180290010480c0100115003084010001da03105040001d240c00d44801450449894154242c031075000010344120b00090345800304c42100b0161002c44050300c108225400c2030087c642c0c040d038980300042c403480c100000d00000502c0041d00c402e0185001503564100080005c0543d40035400880c40b03180350005102800c1e40000e41c1d0040141150b401c1c044c100e00c1034000031207080200810a811020044080c0d55186001c07009500c02d011000045892100d92001d5900301d00a41c0200d80c0c144d40003101c0c0c1d10926000e0300c260b440c50562504074618094440700418160b8200003000c0315501c0c1c0104004003003240500d01c480c3e01000d0011f040001c00700040c00201408507000c164154203500203140c080c0c0751100e10000410032800340480f41d02c2c0b6074468a00c0c1d030307406262000761064080c038884080d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 57727710 1250 57726460 57726491
    0x51501050a02031e0403060c080a150b031f0f0b04081e07030b090319050910020f0606040b040603020607030215130f081c0515030d14030f06011407060b0103 69
    0x40864010b58020f500700348011440c040416007039550124401418800000003d2140c0130318490051144d81d43c10542c20b05541c518162a806140d04030002441c007400e00900c011306040c0c9074030508002c40c090001d03040d284c012a02c0300d0789030000301c1c580a4083c1301280da10010b00080c001c58408504071900700208010342014441946021080d6400c840010008200d0140c1d490307802c900c4000a030f903c1d154031498038002c0a98144da11001203213003ca80701c1e6003131804844128580d071160000d00140c00c11592010348406000340740382c0c425a48c031481100710b52110351085c00034550290490341c1e10f501c1c0f410086d59801040c400a4142d016650016403c0e030000307903004040300d500860a100e1640b15035203480d02600200c155134500005081d03140e107a0701003401240d0186c0c0300040c0c0c40390200da55109041c10f003440030700e0210900544100350020000300720116075105040c00342078821510f5000040351100e10009443c605a00081046828003080c7e51003a0b0115009032010400b0795044081034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 57728960 1250 57727710 57727717
    0xf06050306062d210901051009050a09050a05060a050115080c160209180f0102090a03060b0303090603011409070e010c030f021903030204140301021e090402070606030605150105 78
    0x260481c2c4103101400040b01c88280c041c224001c03071807461128403a40300d4148002d4100140041c2490f084074001321340d030302d55101d0881d00004144001d001503d0050250008200d16200b400d80e000ea44d0000940f5140c2144d000d024240d80c000140d802000765400c0c06541e98400341d4110b80c81c80d2806000141d50f10090889405c00181602c405081e07540707411161f901900f003481d044c1c12455a10700104016610200964802e060a5000309080d1260442540c40d007098013040e040568410000d0380300d81da44a07980c003802c0341d40c070075000300314400b440c000309040d80034008445400040c0070001040c0c030010f076080b12206a9050b6000450781c2c1c0d0701201102d41100c80311b081408146646d40f0070020074032500404841c3c80550040f40c1c41380d6898805642035941082c0c2c182c000035804503081c400300107000581d00147d0002c80084d42000003c1000d144107401d080010802003000064105007602e80d901550750f02604121f040190580d01c0c101740020b0013049940c00034096810030701a40c03560040e002d5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 57730210 1250 57728960 57728971
    0xd02031002040b04150e1e0a03020a031a0f07020705150c15091b1008041103031809010806040317071101051003020108130305041205030415031d060103031d0609040c02070f060503 79
    0x31400304420400c81c0c484045c87d02604076001200c1c401d0100250300e50880c03101c02184510b612030750340d003841c1c00101d10340580500185582d0f44030100340010f85500007046004e4800c1110355070300d02c100c0c414941950b4400c0c3c1e400e50000307026242d0010680340c2604c0441c0d208a4094081c1c641603c0200165000ca90186040036407141080381d848101c103109481036680248642d141407241901000041d285030064000080b20742070f80005190755040c80d4400c1401031107a0300c02080a070500e42d0300a0140b40318164081c05900b0400b00107401903100c0c403014101c0e440c22038006c208034144010800004000da00041c1e010800043c04601e50b04c01d40b41c1615501901940c510b81041d00702200341e10158101441074425100601c00400c2441140904805002c0c03281c40015151900c00794294070b41e071504800c49840d030402c0b401040441d800000408800707007040341d40c400e0a04100c000a1090080c41c1105806c2031409410a46107900020003500f41c4032000700c4181e9541c0c3e1138000b01c40d02d2104464 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 57731460 1250 57730210 57730219
    0x100504150903050316051b011a090906010605090303070b010602060601031a01080103020105090a0306051003050c120303070f030603140d1e02100b0103060b0c0106090f14060d02031002040b04150e 86
    0x40c000380b4802e00c07111070a40c15460901e2501c9a10f50400141400c5090f0810180c0d5658200a40040127039034080d903445d405980c08000342c038208000d00e40741c01052040600388100041d001106a40070300031038803081e03401646541c245d44c546030020754a900032240e00d8042440c000e00000c00004030f054210158205940b01145d03682168011501900104005900280d4164010002034040d02603d03210b1003040d40c020001d0b91850a040b498581d903000340130301644e6004548070300042c000c0100d030351102d07589c20121003000540d0070490080203103600180c808207050130311182d140000314131210341c1203540d40c890b8500e0b0f4a80411b0a004a182c050500161b4042584e4242c0740172903422140c0482c5050500155007603648442c0c1d02c00382c0c03220301c01a4441e55940c0c0148540704040c400e858031142100010890760410400c07450107141c0141c0000c0c0f09140c02802e100441d5020171081c601721810f8003040d91500c0d40c0d005100d8081c0c01c18001c0c65104100c00b00400c1c2403a10500e16a44400d00090 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 57732710 1250 57731460 57731467
    0x90801180b18010e030d0b04060b03010b16050c09010b0c0d0905030706030f060b041502010e0109021c0c03081614030f0714160b0301031e050c060901030b0310050415090305 76
    0xa182c040305400c691a41c0605540711428880062001d00140c00301303510302c1d440400c480300880200b2084803800e400c644011001030005014000c0c1d0101529407aa110702c900041001d11410320a20f0803c414150310f0307000d0700d40c100124800d91003001900841d42081d0071a207625092900943c1c81c40030798041da540540c00484104010f5100e9001000710034424400060b2440c1c54201b6121160301a81181d050707403488000e80c1c9203070740c0d09200e0414100481402000071405031750011720703040c40010801003050f036402405010f100051070244d0042d039101c60480c0e6282c00c0000104030b0089110000c1d50545040e40010900000100071148284842220035140c692035580d1911411680c1c4000b0700c440c8150b6099502c0e000340d8403498409401c80102b07242e06c0b0b624518126805201d440d0341c1d681e190503011920b100160000404014100b81101c40316255282d20740101d00400080e15034a5261103800f50b40000c01d6100e80c40b4a0281d8001c40c1c0306100341460080240503100d070306100800096082 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 57733816 1106 57732710 57732721
    0xe06010f0503120c06010501051c060e0604060801110304020d030c0b01120c0501020a020a0902300708010b0a0f0804020607051015050a05060403020d1a07090801180b 73
    0x40f540a03d0118503000d05516a00103202e014140040410010b940d0200d0160070f0744172104d504006c00615982d00030748807c0200545000c0d00807841e210000c81d040c0c5042c046d10066180c0180b00515540341c0390b0038803110f081d00e41c1090301003022408003400003906544034203000304010440581c110001d4204000c80c906681d120b2410355100000b0100140c85403510901290f40410005031188440850604d2920307140d5030020018004034011494070281030030480c0942d5243d80d07410f03110381e01c44100421a118110003000410341c0000d120900920030050181c2c03281c4098092414203e0742d07074540c0e00c0c02c0c202800c45440d80344c560400050f044000c0c0c81c580000c1004854100c01203181101140092003140030290240b01d00c20004410b100041540e06900c22100245982d1890061070052460384a4002c2e1030040d4202000484400c842d007232840740c41c07070300038402c080b40341c855 = true := by decide +kernel

theorem cover : BRFrame.Cov 57553960 57733816 := by
  have h0 := BRFrame.cov_init 57553960
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 57553960 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 57553960 ≤ n) (h2 : n < 57733816) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
