-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0184
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:19:04.271369+00:00
-- url     : https://prove2.me/submissions/8baf4068-2672-4513-b305-8a04315d2612

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 32913674 ≤ n < 33093530 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 32914924 1250 32913674 32913697
    0x20a17010b120403140c0d0906050c0d1103040f031b050315040206030c040306140a050618040f0503071a0a0b040219080604060b0c150105040b0333070c0204050903 72
    0x1802c81080100e2212074000b0b0301c11810070200843d100f01c010303080d2001e0401300e41048058107400a10210241c00020382d40d011038203000b024010781680c0c6201085492110145040180101d4281c1e02e4090a500c900d400800e1101e40c00c01000c411701c02e0300c000c02044048415400c2010a03100c1c0105541c401440c42c01c03200c0031103108002001400e1100c05940c215140016840c107294aa03079850301940d240e00e8080100b0319401c000c0112400d00c9000b0300b07801c840e080c0c401031014504803800c020601d00051003e445d401c4940c400c801000010401c58100d1504619444d44d290640568111040000d0f9030008549080114100702840c061080302c0f020f40c00311920b03004500141c034060310329200003811164495503aa40002d02600c40c0c8000700804107084014104a84511402046805040c2c000c64000c51400c07000e410140c40c0010751174040507913161481c803400304c1103500d02e0706a1244001a20f1945041052100064100c0c880b4101240308030303010f00c150707541c1c006d080d650317409050610344 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 32916174 1250 32914924 32914927
    0x9030109050109061104180c021009080a0210020c070504020f12010e0906091c0f090f0815090d02070b07060f1a040f0b0609060a020309030304030c180513021e030a06020a17010b 78
    0x4a460983d0b000f030407400d11900683e00f00d4007a00343c0c6001150080032f401c1e9800030000440c0900320380c0c14080380c22104040da1045041ca03400031221682d072000c9000d03c60103603600003003038010340b440c0d00203503030601410046150166840b10f038040201c0b00c003610004030300d00c1040040390194102143d901c0c0c98440018003602c80f1004a10215030b20340d080c0b1449400c0c45011000459281c0c2c24050b480b02030490080145801010b034aa000407038a0300a105071002e03085003000c80f00c11940400c60308210748580c06110348a6400d810264024a88100d000003a01d1415079120144024883c807015000f004980401000e80035844800c2582d1128a4003944a00200441c0841e032070044090007201c0c1c1f0701e1048a062410540129107554000e4106880034440a00100039411141c111a0b1040b146080107024074148041d020145070454103000744101c03684510410707412554001c210160307600500325180e032810742c20032100940c40307000804c00144468003c081c1d2100703090700700b5040ba180045001d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 32917424 1250 32916174 32916209
    0x6030a0303050711060702030a0905060c0a060203060a080610150806011e03060b040b03060f0a031109180a06050702010c0e010210020a020312011e050a03020105180609030109050109061104 83
    0x1c03802428000d0407a0240700040b00700c2c48070340c2000c01c4a64420003854004551702c00e5070420152101c3c0c41d503840548121410850104104404140c141c0c480303901204c0941c40c0e8540388005000015260403d070918131030141000a9850103800040840343c1a919180c4e031200501d10440b00004121401c0740401c00030120300070740700c0403034407001003001d0f492a0004080703480311380d03034299548203511a18100c0c4010061181a2500701540e140401084842802c0c85186a0712050b1500300203409510406d200f00000d50703564090854054066924400d41d2440d03039551800760020b00f030540e034890046d0700c1d002281080e14040d12002e960f5182c16001008801701c803101203006175122056541c1140010310610b002d40c194081c01d81d028140b12000c060034282d110070340401c01d8200303600003031113100b800c1c80030405030740c10408495400031500b001d020030f005014080780061003425005a010342c03030210b00d08140401135110f0b420b03035489980140301c0c0c46240c59103a0014000c501514401c8060075005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 32918674 1250 32917424 32917427
    0x803070c1b030506090d0216180603080a120b030c0303090409050a0b040507060807050a08070f0908101d0705060a1d0303040e04051509030d0b0103090b0405070f0e06030a03 76
    0x30284914032442050000103000420354000e601140e0084401d076110100b4400009000c0c407415510070800c0c030050040f440700c00610007042401d44916001c461070400c1c41d02c405c04d240d0304044040d40c2c00914007a074801c0c0c61403000b0903d40c2c100440003d29460060300d60114a000f06004c005400004e000390300740701401302000020916079004450900c00c04081c1000101051003562091707000d80007130500c035850070802411564000f0700711020050104010303a0456001149690480c040780f402404050003407500356030003030342500725092a02c1500b05c80382c00d404a540244c0940b8100000580e10303124080100c0d99150358a01440303031300c00360030700c9107c84680c811031041501c00c07216600000042105000319055901c140c0000780c6500203030b4100003e200c1c003003240650034810011904d1251402034461500ea000d030510030749179580c03140016003a5a200f42c21111409800c00c5095080b400c25180a40d0385040070701c10700c0841c082180000845800d4000d00350311800004c0d000e0800a0350301d580 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 32919924 1250 32918674 32918687
    0x105030705090f100309050f0105010f03170715051503030702100507050312010e070305090d080103150f02040b0a020c010206070903060908042606010b090102030d05070311070803100b030103080307 87
    0x9456800002803003050310f090f610000046803000d0261070001d001011800c01500b0425603101820381c5038140f030010091440400c1110701243e0300014483c07070b402c20030070313642e00c0358862401d001d01500086c030300c2180c040020b6403105009403604501844064900f04c1496260700552a0181d40108801d844004a90140c00186100b61007002130300e151040e81d56540c1e940402c2a00881003078205103081181d510340507c01d003a0824142c4000744444909050020300200050100a10001c505443c45588070820b8101a079a000c00c02419503c40782c48900941040d006003804500500c5001d042611950010407664000d2000e41c0d12015628195243c40d0042e04c51894102c83c404c00800000400203011810301d100b1103064003800400300c0001d1491840c000043c1c10410010504001d1448961703000800c0fa0081d414940740400e00d6030b07401c0300a800405500e60382500703e000000f00c2c00b040210300790003903220b10581c1a40d007060719101ea40311000f6000c00d000007840180d04002150b5010b00800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 32921174 1250 32919924 32919937
    0x1712030112020a0b07060c08010b070503090f0109080a0521130306020702030313090b040609020c19020a03050a0309030501060f060504092d06060908060402030c10050c0102030c09010305150105030705 88
    0x424010039540d644988081c1c0754032aa9061b684039560300f03144200281c0c840180760041c44844030103070130841244c031082c0d1284503044840b40300d03511040190f0410790045a0705801489901d040c0c80102019041131900e84071152a46000c4000041d00620740a10040a991722041951120608541984c0e0b50800950000707030300b66814441440440c140c1460f050504020304180607001c41c90012000a00c0191061030308456012401800384403c10400003c11003030a07043d5042c3c042c4e8800305400499040c1c409500058814000c22403c5824540c0100040084071310a0000b008099a03d14107200360782098005d66000070002c1004001c00710540d045051031400e0354103a07580c0c80100212491484030f2039200d08481c0750712010100186508201c40c035004007200c0c0e01502c031520705640000d490748510100d20713205040d1030040095151048007601c0044a0720002155a0f040c100076422641d0008101e06000070300380800110071101284901c99a500107031141c504645807450203444071340014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 32922424 1250 32921174 32921179
    0xc04140c0c1204060f1101060819020a0902030a1407032a050c010e010608010b040203060a0902030903160506060f03031603110c030106120308011d010501050a141201171203011202 79
    0x90300d036455554100302c0203100904407070320751122000c90030b00042e0001000445a005503490881c040003074690109505440c40640d49030b14000c3d01c030502c00210a113182d504500b560520100401c507403503440f903001500928107450b03001e442c2c2d940c1c81e800b14250350505401c510504d5049800401048000b959850000d1050510900f4610711000d45030848141d00b5141140d603440398000c01240c9030a2040c0003080106640a40c5945401e00105803031551621070702c810560300000241100d6018000d45607000f034100000c56030040b10781000c5981300016503440384240107940704ae0b180d03454000b003102c2c90646a0390045004605644050711980d0340c1e4050701000b40250262655650340a11070b4501911350380904846520080c1801005020140c0092501303549600400201450180c0382e2811070300701b464090366511030598201c483c0070301c000e1003001c26080429120003c1c5e0320b40546e40d040e00d040106030440503c500e00e410b0f546041c3d251510444003410401401210071101c01c44000ca40003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 32923674 1250 32922424 32922433
    0x30b040b03010e0c0a0801110f090303090d03080406060f031101030c09051008090c0306010f0b1804020301090b030c01030b21030705060c12010807050109050103180b09010b030c04140c0c 82
    0x1100401e080d9010000d1403c07050b00704440082c140c0c03400c81d80c45805008048002c000c0c03c40a01c0c2480994407440004601402d00820707584959602007045806a0801a201e4649004070340350282400038161003c844503801e1900110b0555000c480d1401160b420544800e0720380d0140c8015001066002d40c9034081200340f10010910341c4030318403d03500c94092641e40d100180b42c184841400c03e201007c3c0f041c0309401c08801040050401c00140064800504005948400001a8011a000c200b00b4140c0003800400001440c081d1a4010041e240c070690564640340f071540011012640003144413944030188000c80c4c60070003c4c5d101d075506807000c20400c80f890808187c992524000040b1921484c01500180c1c1c1c200141c0403000e080d00402c0510028240241090000b0340144100c2c001e43d4105a96a120f04402aa0314030b200341589410034180a19800d0ad241818040d20440c800203019124022202165081030710a14a0789005504511000c1e101c0a10795081c9030b000807003481103480b8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 32924924 1250 32923674 32923691
    0xf0301140910050105030a080913020d090c05030c04151211090c07030f090b0f0306010c0f0311010605120a030302070515010608010509010e04051b04020d0e01050708010807080706030b04 82
    0x10040e1445010703441ca400180350003100340300040141d50301608241e0003500300601040c00580000e0039580000c0040311070450442c0e004900e00000c0c011602c0906505080400300c0c2e09014038500007030103490054003582d42080d0014148025222400b103288006480010104000300403000da03050b21520038400c1981201c075140020303000c40300a40c1e010003041c030002084410180c0004030788032008421309104207203603c2d00030388540d10300404020f405c1d1617100200082c0c2c01e0f8030540890316070b5680030420407202d00340740c103004180b03100b5500300b602550b103480b5000c14203162155114083ea84c0380c100400305000241c8d4100d01039003240780222940d00c00c800d04083c841c0042c2100c94081c2070969541d070060362401c410400c1070841a8821022441940d00b4440800d101140c5410b8201d8081007503505009140d012034003d100f14000a544a8549181d8049030344042d00701034040d680f60341d903001d401d90321031201c0ca85600350761142201c1a03000c000304011150003500234104070300300140002005403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 32926174 1250 32924924 32924951
    0x2030f030f0f0106090303080c0901030902030607080f13050a11030c0a0905040b060f0108040f030509061308120a0f120213080319050c150603010e250501050a0c020f0301 75
    0x20030a940480250300818100000c90b1051880d1038010501c03444c0005600e03140d610050301c00d06001e4400400303144002215550780e4060f030001c240d083e038003408455071454142d0b0300602150050319585c810b00c0c01500440c10200501224006068200018000e50000e40d920340d2108280078240c99094083c0002080b03180d600c991911004080d005400301d802d142c1450030000b068002403a5034810280030b06405503e0b6840783d00c095015070b0080980b00046d404d42801d0344c0034084d0103035055000d180002c110501d603040c0030424040310081e01c100c03003d0004a100d4240c480c0162406600011200d41d1044515031264812401d4a040600010300d4000515070076070708042c20741c10450311036200254003021001c0821035a1202500e9241450a002e04109955140c0070700e944d22503c24850740c000302ea81365138294094981c4449c00700445155004913074104030b044d01040f10310040d0400c03c00c0d0001d110b500500031508445c11555811145c00c01c5030b401c10988080508800340c2645d0b81e50084544035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 32927424 1250 32926174 32926177
    0x1005030703050a060b01021612060e010e0102041d0f070810050301020a090302011b050d0c050c0a03030e01080f04050d0804060902120606041104030b0a02030603030d050c0715051504020a02030f 85
    0x1540200080c0c0300800d111300346002914002001203046601540310080c104600c01c4030300c01034910349640c01ca941039450802c0e6001d0210341070b02003c070707500c0d03c0401692170744154000c1003200e56283d19210071346484080d00347c4a4400711100c03200d002105002070700c0a480741c04000d0b4421040b6200c9604243c860002c20f0880c1c010b001650081005000140207641c1c1002d86581642d070200d01480143d0a10340e9074507140d5800d040da00c024804841c4451080200901035454001030180698218655a050082c500c848104003036000c589014081030740c00040f4181c0511568200b0014038403000d203c40208d8a4400041c41516000d54910420005941c0c0564150b102e941d1840141100c0c10700c038017004221481ca041c0aa4800410007040001644180080764094800900140c5a941c0c8002103400c51061203083c01d010f510344000c015044000201909010f40a102450103100c1140000e0781194015150702600340000c0c203260105240c950001c00b6122800d106a82c1030000b55070054165 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 32928674 1250 32927424 32927429
    0xd060203132a0503010b010903080c0304030b0c0703080f0405030a210c0e0f19031b0e040609030206060105030f1321020f0f0c060d02070215030a0f060501021204050103020310050307 80
    0x655040705001014604000b0009020344000c80003044200300b60030028200103894840203114500114000c440b0b44000d2042d9001180c0005480070170740703090381c0380c1a020362005038200c1c046815800440c004024041690344241e9015006520323001301d050b400d84003640c8060942420207084441d81c2c0c40800c4a0050040d006455200ca44016080c1c9081141d00d80030901e0103802a0100142c0b0b91240c090312024008494201c0d01c030080700c544c28103580c81c00f1580780d000364503900d820740c00f403200300001039004030040d0707000f82d0136030b000303a101d075001103d1520080c0d9030759844071341e0720021035545c06403008100741d541d2007080382414015840f65450320149020400c9400f681141009900d0710106010031404d4002e04005130202c10504800107103540140362210b444158041001c00864850003209080b0444400c51540c031f902e0320308641c0000d0122003c0090000d0b05086c4009650750000400d850a0b00c00c030352001d414103041070300441c000c1d04010900541d4920741030b400212920b003400f22002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 32929924 1250 32928674 32928713
    0x15020102030603060f06060d0e070510090e0a0b090105010e01020a0204051006110a0305030c0307021002030103120e040605060306060d0b040504080702012007050103020a050706050709140301020403020d06020313 93
    0x1c0300d203084000c1606088005000c00d640d04481c9040214694038030085a140c1c060344103001400701c183c04080c034507114064120541003800900c2020314103400001550845101c210008001e50382d080880060b546c00c45001900324051000600c181c0d0f02404c00e509d9442d1040c411607501d455190002410f07500b081c5ca0701030301c40c1c240c5441070001d00d40c801d2403a6a620748000c01400710311025a402001ca202c001d00c1c1c0e1461070305c084040cc05d1a4801c0c00064042d6500c844159182d503180e050460441c3c0700c64074110041811800c5640e600d04290041c01c0889100070102c43c02c60303881000b444480d6000000d05d07908180d860600b10301a80c2d0340d20459014a0080ea10152501d80610015000d00044500c2c2294035410701728035104840f0000e40c1c081039603400c2c40d01584840051030259510300490200130205400c00c400c0146240d0b01c42c4800382180d079500c8140c0e540520f4602814201e2140e0300000c1d40010b0a07100345408946140c00550700860341c1c00010650034000c1c0c035480d140c2c481c120a03c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 32931174 1250 32929924 32929927
    0xe03160602090f06070206180a08060c0d06060c050604030e010c0f150e0a110112020423010e0604030b010e060d050601080c01120b09040311070906081507050403080301180615020102 80
    0x280b42420b80b208158141e05503044d52a0880329000180079019144003089190180b02011006c0c0c1c5515218000030803a560882c0d60a0809402c584c10680200c401c50b030086207000000103241703100d6100e6070340c45500000548035989580d101103c0c2944c3d140446418040800b1802c00000c1010718210440740c0544d201c136170380030500c0e9030002c103640518111a10582c030a1207000b02140030040e513a04110400d08110840350040011500a406154000c1209020b1501d09016044030f449007c403c400c800d9030b407803d0050381ca808102d4180628003019100203007540040c081070002c0745129822820081c42c80300f15480c01d590f11440d00f1000d03040141103810a02900445580041254160384002c15040c0441100500828152000140040c080001d40e85241803240001c4c45881c010b402504401d01c05280c48440c0784d66519144002c5125202c060300000e01254418000d803010360344c1c0506441c0c50760340307001c0c10b1824006982c015990010303607600700002e02074044054181107801e00d40015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 32932424 1250 32931174 32931187
    0xe0103050c040219050c0a08041202010806040507021b03010b03061e090c0108060103180b0c04050306010806010f0303110102040b0403150c020106081c031806090507060509010c02040e03160602 85
    0x182011010124035000b07078014883e11542d0000c0c500e0100c0d03042202e1078020b4480d81d03800d06003860070081c20381c050100c01c0001000300e58110b02808035840c0710300170f80f5400c030b05407151002e010440c2d8046820382c006801049040d20a0315250310f10340322941008001081551218000074100304041e10511501003900c0039100010340c00d51040c40e8404038040145c2004600100007a2a918000b0007580c10184d450f81554241041c5860004209400c090501c551786806400140d40303600c20300a1511a10a03078000284c6c0d50000600035050351400d00080c12040c4c0b442c0d0302520000701250403c81e4031754003444007091401070300f40603200440c002c0e40ca00400c2c40c0c0000303c1404030361000d0868001c6905090003400481000944003405003040303d0314241c02c0071214004c83c0100340c4444404019902c170002c2d00306204c100d410003c915805001038542030f80d0f0f0303800d050341c49100700c01c3e41a01107001daa12120151906e030380307c00030140d4a903090301d2402825045407801c1100039103044407141d6010412 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 32933674 1250 32932424 32932433
    0xe0a20090a0b0112180c08071706090a0b04020307030803070503040c05040c090506030910050405030a02010606081323030a0f0306061704080d0e0a03120b090402100f0203130e0103 79
    0x5800c034070412002c00c1910301d0200020811603450381c100705031a8890105c0c0b207006202104080000c0d4010ba060307240140c45180984d10390361144a0500c7c1003034003603904071000c10007180c2c150284900314000e2150441d607030344181e19542d00801c00d036414000d1403000004240c0200c011886141969a5940d99203050310f854000d098007500036900407460485044503041c0c0103a054025900112038140d04d07540c03400c0341d5600d0001021100d2180b1800c040170b11003003040020103040040c01039002440050385a1004807004403040754010707910410b400000c400700e10560040c040c0c00c1549002034440ca400b02c2d19181ca954041c08010340010000e070700c1070724283c1c0d151182002504807454103051748611902d03403103001c03035000d48040e0000400294808010f03040d6842b54007080441010345000f1815414060315110304503158280300d500701031104c0c00f585403807284540305a40c02065080d200c2806001125109103640c20f0b0400e5100411a42c5074840006040d8030092100c00455a21581540350 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 32934924 1250 32933674 32933689
    0x120907030213020705030a03090203101103040204060b07080f030406150e070206010f120818040c1808010c05070b0a061703070501060902250510090c080105090a1101030e0a20 77
    0xb1114000d1041c08070303800003240401110880c0c280341c41c0210307140856000123070900b0343e10b001000381c0c00d00d000c0e42c10428a0041c800303144540d0084508010143d40d50402039544e10072110020f05a807820000c228032455040042d503000382c000d0354000b03500854400004050351b45034020500342d400c03c80030884420303410401c0e54003409240c001f018070300380703400921100d0b05c602140042c00c0c50f4000c100c1c1c0350f480f181441344a4400c040240180a644c4241402070644c031600713081180144004407000c102c819050107039800b002800d641e22494886140c039101008500505042700c4140c50f86000100d407441465002098140350004c0c5035982c41c04d02d030041c00c4442c40e0f1f00c6020824011301044907440c00703081c040c09800440e2102d41405070920310f8880d0403c42c2445c94858510f10308820351081c459400e4403001034401d22802004181c4540900380c3d52415428001071445124181d401119480b80c0c214074484503e0303000311204441c0c40c1c0d40d100e0000b4414268055482c0c1a6200d9004074a803002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 32936174 1250 32934924 32934949
    0x60c0306120106030201090b0d11040b041d0910110706050115030c080108030301030303020c070e09030706060909020f1005070605040b151f18050d0c08060601170118021209070302 79
    0x100810500d07142d13174006802e0303809511030399000410116810310002080d0f0014007411b22208881c0d40e072a62220400d100c0c940103401510810a0001031308d005170500c070084603016480c1c3c04010291903c3e00305103100a0f202c0080b214900c401c05107c0100000c16500505002c0c0c880b601d1401110302488a009007250060b420160030891440e0040000100202c201c03810340360149000740c1e688040c240e031a0b24181850344000340b5501a1001c000c04c102e40031007d04041446400d00703025040d600c1e05e031a0162940802e01a51164191020500710700d032035001c1301480c507075a00b042d505044c2541c40701ca0480380d0407070341501c5081e4070340100702c020305210808161048045601000e81170804d07000414581907602c0c00001e128415a504904606041c11100200380081c4011104101498400d0380c4880601c120001440382d24045001503000c3e03a240030380b4400300516900180c1c030304090080c0c60542c240c03080c03102a600700a021401d00343c501d0359922880803c0002e00080b4690300c1172240c03a00060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 32937424 1250 32936174 32936209
    0x3031a0604050a031401020910050901140a080613061e051008090a0308091204060c0605010e0106120b040f24140108041112060a0c090b040605031314060c0306 70
    0x7003005025a036180305550058940010010800d08a8031001500900c1040304c9141c0c06501039182420b043c0d8054002e08540208ac0d80b000390407c284500c4020b94010901040d02081c8407100003100c0f82402401c1c100000903846011030003070b0b038510301c02148001b502001d24035207002e00d10902c014140b5103d0304011640602c5d2030300703041c40c000070fa21b515281c800a0003010407041c10086915540d0800c40f403402e8070707094070120340c0c0d4940e200e5000c4d101c0c40741000700300c1b207050030100001045486a80483e041f070b4410f8a44181c1106c1c03c01c1c0c0740009003248100a94090343d00c410948460b17a41e0b11803440542502019024412030b10800f121000c5441c0e40142c8046204c1801800e49980c0007000c150465408202c40c10008a10700004586008040f208242031090300c08001e07990207070ba007010368103043c107884440360740383c0700c2400d040c0521903401070802003074080012400100e02804407011040c003a031068000b80601d80e45413400c1c40d600ba5030503100368001000b40540c5241c41c0d150015040c680 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 32938674 1250 32937424 32937427
    0x31a0102060103030c05070803120708070804050601060f0212040f05011106010b070803071b030f030606080108150c07050109050303040c09020702150a020111070606031a0103110d0206090d03031a06 87
    0x1510000703503545014040102003214924032402000000c01203100940409400c0c0c0380c4650100400f20040303001210240009091000031a5102c2d019400c5a801107030400094031940e800d100040e2800b20000704200c1c2140310780190b4036046010100134001602402d4400d135141c5280a000400c410106080c50409412007401001044102422100820750042059890340d840000a80d00c40c207031100113007080c60070b070212881010b511003030100e61400d40f40c50030403505840d09012114003500b40104409075020b076144155424000e00c07042d52000400c10340300d00d0320340656a09400d440180c1da0031201a4030110a0004201c440040c3c680900f0440004506208058000612403540300744075900c0445c0000e0380000b40392007900007a0034040d04401440d510340007803820300300509091000350b49140d403021169041083c2020b03458103ca4009032029158480c0c80200040c4031912042241c1c000300c2001104010344440000c0d03c0035134043d0b100060000030b08541d01d41c41c03c05260140e48104070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 32939924 1250 32938674 32938721
    0x50708070e04230f0103050d0903050309120f030f0a03060501030903050d0b06040f0b0714030304150b061902010c0e040c020718020c0a12030c080f0103020d0f080c07050103 76
    0x2030001c1d480084a90840d004503200c85641c840800380d0107000d008100f0000740408100c620504a08518100d9210760b0803118204c140c14000c13030700130116000c010660b400401c400d040d585010b888030001004031209503171007040303c4896145164000c070f580c40700180d00860112402c6030903119001c02410203007810310100c8040ea400401a1243c0784104903990740d1a0240f00c2d00b0380f20202510007421185043c5881e0035140c200d45c21950700842012510250103080c10707881540c020064130701555014002e40120040c1ca140d035405400e9a8000540003c414001c0803080385c0060100c0c3e003132500b143c0000071104010705004100382c000700c18080c05541016410003103941d000580c80704541c010030300303442c018030f001c44481d01910603c5241e02052162080320400c0c082200180c540c0c00c40c030350718100401803005000f9101c445044403411000040c0800400150a000065814607803082c600d0714008219960b0f8000260010f404804482c0d11104080c0440e513094802c0341840da1428021702105c11 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 32941174 1250 32939924 32939927
    0x303060e010e0106081503011805060a0b011b0602070818010806010c150c050408030408070e07030506090601080403020f071403070605030c030a0209060706060602010209040f02090a1412070308030402030105070807 94
    0x2c18400c520400c9984800038500340024210f05600c0729001b0b00034440d454108e01803d407002101d0300140e5050040d0000b01d03054414a110f0309119400685801040440822000740e441d4483d9005032903290b003c00101e400100300800030301304908801c0c0c00181c0c852034507000512521005002a06000d6000a101e01081041560141d030550b00c1001003403003410401c0c00c0354103001c1d035405100980301c0440c0229421801190743c80550301c075664100700541c0c50000032400e5500c29244690020204408140035522a41c002da038000d0081c011100300168070780c0d00501c0c0101f158482c0c4484e880d40040384420b4a000e1041e0720003044181b030880e0450804601c0e0700701a1202420f50030009074001040c0c4450348030b010580c1d07280c540021082003001d5070f545001e4082d51140a15910403481c4c0450403a0100562081d1050b02c0f40242845146500703054410000b014001c45650384554445522100e0380b0301044114055803040d4100d036224107042c41030500355040a8111010710080c01d04005109 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 32942424 1250 32941174 32941199
    0x110103090203060613140c070605060306010b160206070f06140109020705061501090302190f050109060509040c09080102070606050f06070506071209121805030313050d02130e06040303060e01 84
    0x3c681140c031003011750081480b52000309041c0d038414080b0803203082007141d2185040042c200d5240100c1d13003030107640c1e034442c20581c44000900814010703100030b000c001000b100c030424002020f84082d09051420885860b1501018070f140002c860103625035200b464034038210110300d030041401a03c01d6040c801135980e030030b80304c580c010314240c904031141101d400c550384600111401580c0150065034105d0600d403040c11440981e02620031000650b500c001040e52050700c43c0e1045801c00d544207414441c81e4000c0101418400d42d051041246610010802c00020f1008051680c410180050707014542403c0c040f29031022009035125136014420200403a0700446e1483d031169091030800b0759881c428455100802080802404000340301210004c90781d00405500c20690321496141c0085a4900030590f0b02d00c21440408140c440c44e140801c0242440444100d295100800303029900e111101824100c030042c9119101030307800700003030006141c1c0502c500d00c05841c05070b600101c80e604201c07c85c00c0a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 32943674 1250 32942424 32942431
    0xc0f090302062104080310050105130e13020406090c02070504020711091b0a080103050f070b0a0c06020705060a02070c0801020301030b070c03180609090608070e040f14160311010309020306 83
    0x948400511030088420b002c00d0152480d03200c00c982c012034105803c00c180c00341c000719015560b90320780301f5020525600072130a850003103c084e0241d6008600b819000411700d040901400300400c041c41d130100041c0e44501075040505400a0005413a1082c503500914004d4a40c0c0f1040c0110b10400021020440070003000382d46200c01e0718100c00c180c450649880740b00041c03804103a509180841d4240210780c3c8245100c0c102d1340602d040b51130a020202c1040c1c4c850900303200d0a0764520040101e01041070142001401d00c501070403005040020680b0380c20300f401d500b11070f0b100256a00042800810280e03a1550025082c40d5000314150360641d602e04038400c0000e00328100b480b402c01003000406126590280c45001540308480f0425074422000d8610300140c010026650300b00b000c003180c40c04c800a109412205800d403a002d10382c0f00c0c1e4440c44190420303544213503141290350341d0040d00210304100129007484d544084000051443c100090340380c041d0300896040504009520340035070382c0060643d40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 32944924 1250 32943674 32943679
    0x20d021510060c05070306020c1c050a020601030b0907170601150906020a020112090f0303050402090702031e03100b03010f0617010621020d0e031c051312170a0b03010c0f090302 78
    0x3220a960400038079040051b440201140e000054506013810b01103424680019215100004446000804c0d1000c0c0503c1c220840141d00c03100041001c6994130010f1604842070005452980c2d803900d40c900030803e401720310521aa0321841c01000031074103110302e0f00c1884103546804003d01b4240b5100a440710f200c0007010303041211110785250345442d40d42c45041000d60122410342ea9168900e0f010380548000c40e4180d03c03a006882c0043d00081c008011200c4148580d18005100c843c5448004071942003c0d1840075150301d42003000c58041c143c00300941c060580c6c1503039040e000b4500440244001c40c85142c2100d00b5000100410510740c0102c0342e403000d070084409807214000c0b240c024100a008400d000320b515400d2103400e00540401000900c110501c8100c80c03840f00010b06180d90a6072400e031040e20500d10803128103c08181032782c02c461014061481c0c4025104280c254648001200703545080e0003a41e56440101c1070715091092000c0c194050500407103002c4003000c06401134406110103030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 32946174 1250 32944924 32944937
    0x20c01050d27060c0807090b0405130902040905070e0901061a0c0c0307060f0e0d0b0103021203210702060f0c0a050a050f040f0302030f0c0904030f020f0d020d02151006 74
    0x642c0544040c21040e000036080d225102c044026091050140c8980d00f168400304032008017040e8454441c030f650a0540b141103101e1881e051402c02800100b0120700000d0340e04540c0c440c41080142e90741d014020080703000d40b0083c030209007003407221480660081d052800c03d038035000007000032b4440039580c0c000c824840f03540340f03441e07001078183c06d82032052030444164140601e44010a82c5500800c4a00710f2984641d50565001410350034052030701c40301540906008500c4004000500d0301c00c1c4080e1000e04034505407400c107174210b0043d003c1d08400d4980c8002c400318600c100b00b0600d90420050783d110641c03801c2000340e0700300b801180c0400d01c122840c0382c080110000e1045105400381048450034005e40032526500c50380c0e0500b04807000c1840c0003c0b440b900588141210440d00020f0310840614000e1241c126516540d4007540c60400307400444d0203602418442c00554202130101041ea50b0107034000d04000b00714050b000b81805010390402c0392480000082c030078034030245540e038010303240c0340d05008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 32947424 1250 32946174 32946191
    0x108070c110d061b09030b1f1502010209090702010212040b06060f0301090218030a030509011209050f0c0f0a0308070609030e0603040c05040506150306040f201207020c01050d 77
    0x2040c0000048403020707000345254000204119080d403204910349041090185031450700181211001d0241c400940840142c4010074951204215141c00140d00d0308c0404010965509a2100c00a0026029800350354003041042c00d40c141903043d80d80c0003201e031008500e0310a20001c1601400005403010700380d90800c2c0001170658131a070084891050b10b440100d0b440750380d02d0040d41c0195010490820003922204403030801400c00040c1c41009640c0351300c80b01e041a008000450300c20031005402e10a803901c412409010440501c031a04000c8980000343c08040c20306800d0014151004000c10b020b68600c0e10104080b405150541da903103070344404040340d03120090604480c0c105801e81c0c1258015800800c2c013040040d402c6c00c110460303500783c03024080f5540380e03400c03c40b4103a0b100040c64039034041000091014640740e4040020071015880001d4101a004686100e500b0200180d07426804000303800300002164071691076000400d0304c0107007840004903000134450b018081c0c0d0301524a40740c80e1503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 32948674 1250 32947424 32947433
    0x51509060a0507020111041e0506040e0a110409060e04030e0303040602070b13030203070605072603010b0702181e1303020309062104030305011503090503160203010204031a040c090b0108070c 84
    0x2c15200c841b010000d0340c0343c0782c071410720142a01d80c909045078441c50b4a400069a403c141c0191400c50303958401c1001c1503514441340c140a81003541c05a085204200400b2640c0d4805208002c090106101010900d03c0d10345805001c0c04480791209202c0c0d03105000400c8010383c00a00c0c241618055800340751901b034140f007001c50001c0d139504025814000c5030300c04580e0079449800362003414083c10807000a84a1140907000b400601403c0040e40401080140040e0046000030300341c41b1302c00b078400f841d148800911a1031020090700c8600c110701e00241c0540e03860036994441c1d07030880101c0302c0e454005a401e58020b9603a03c20001c455000c0c0c00089000c0b82c122903007141d40c1501d02d000c014007104c00d240030301d40140142000d008071012900e4a034258482035100344144100035500000561804412642d0100066184c480403070f4199020000400056040c90800840210b1025407003002d00381440d00c1c040305185a0002d481706880d02c10140c1d100e0381d01c58600c58006402e410810210310803800c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 32949924 1250 32948674 32948681
    0x105070309080708060f0c091f200601090b0406080601030615030804080a030306080d0801060522080a03031407050301030204050414010c08010305071a0f0d02130e0103051509060a05070201 83
    0x82c000e01d0007441c0e4005402403000c591030f03124042041c1440d5450345c03240d600c3c2c00507010b61002e4940040d0600a411900c49030340891000384040350810344048807042014444801007015800c2440d00104010400c2c00d50f43d0203002031881c003c840600c6490f0038461100d6407000c0521018290549951000c0021b0301f4020b14800611b41100a142e501c60711040c41c60f40e00c043c2c01c00201d00003032620400041d5814003040c242c81c424515681c404c1580d1801500302d0300c41d000741012400190170f441111072382c41d04582c81c0c2c00052103a04003030f18400b1154100a03040f115a404515482c8059074100007003503600c4022281503d504072400501910790b81412007000c41400d0081541e0b40c82c02032840351481e0001804d030304030783c8202c04075a1200d0b00c0303504906050340c000740180212074040c0480b82c5e0f006090000303490000d012100041c2054045c40068880303400542c040f0345411150f40043c8284002408410001703400612440060f0515040d00b07075448400606103640b42c1d6581012414180c400e41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 32951174 1250 32949924 32949929
    0xf0604050a030308040209010b0a1205060301020c07080c090a0c021c031b03021305040c02122203030810050102061618030204020f04050f0d020105030f0c070209011d0618060105070309 81
    0x1040d00c0c48468032494041d04003c1c01344c600740c7c8500411000016001008401c07201054190340e20701c8141c0f00007407800300103002e0142c035095165409002401180c641044000c1c020b0504600a00701c48980780c083c03006001001d40000301751307420f000747c503880039400042c500203842c1c804001803403581e40000102d004200308100b00b4402030102035045002c96044c1c0150649800381c03038285442580e07860800044401d4180540003507040030704001741003101c1c00c0c054101016903800b20709003803102116240c01d075006500124041400103007444698400f4240342c0703010781000e0004000d1410042000038005098a0340302c010003500c82e1400d09081d0101803200021640908250340b2000d5400081c62150441d000d07081c02910803481480c1c49142420100391a1601030712003a00e19207942101d403904031002002c221540c0810052280144c0700c0d5900703035000b8030b0070841c1c0e8050914201c2150b142c100e00640018450403042903006003150911020396000b5809007042965299580780c1584e02d80d0256 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 32952424 1250 32951174 32951179
    0x18020c0102030708070f0206190e030c01112104030c0602070305090301060f051206100506071e030302030103170c15131703060109050a0e0705030a091e02010905010c08090f060405 79
    0xb006200c0403d070840700c220301035451610ba05c5c001c0c080d84c040c22a03030f415084502e03072400310b000400c00a00040c168012058464030b801030f64604074071025518290769170368035010050304000401010520229041e090702c846607403550809428143c8000f0030a00210380c01411171680010790030101406401150368401c3c000d002400300c581c0c0e8680c903080500c00352040c9801040140b41c00281d600010035100d12820392032414007401d6003460103000094000c1c007001c4900304070340000d0880070481c003032000c4d184034803a030f030056031301c0d03046182585000000055002240c0010300000131001c5001c28036800e4140a090740c13803907595802c101401c54107a40d001c082c10003200c0b54031300000103400c08021407081c0002c1e21804041030751002070103600b1809204290600b0602c0c4041152148182c0041d600f206120b0800308a8409546400749480800d0340f080c41d0400061000304c0c21035030010b0814004140900340f09140603102e446800861050b80d1080340302d101c503041d00300513036031310f200981d0003401c0003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 32953674 1250 32952424 32952427
    0x3060f04090c0504050a020a0507080a0207030206030a090c0605160204050405070b07050604110108090703030507060b04020f090405060f030a0308090a050303010f090608030a2c040f0f050a0203060a18020c0102 92
    0x150804203500350b054056180514203000020301c0c1540b4600886056409a90350741d850200303142c940f481182c224000748421401850340010140e40c0c2e4102650080c943d0400008600c0018606513501c0070300c0f6800501800b0080c00300c071151542c032003070414141d50140e80118255a0301d203001420803480c0e07003084510040200d1103000740500040c0701031140d0311070460354414074058401134881e004d0071955100c043d801a941400040c3c4120041e140891050340049011600300c400607042e40c2008240c0a1421404140409507280c103000c3c6c580c00c90420341b03003900000c281001007602c0c3d0103202c0c0054240040a8080341000c101000444138450b080000d40780c880d612541107000104161150000305070410402058504006c0f0850700340310801d448005207008400002a080c03a2031006203190601c800000070341540395030080303032801914294001802e000c80e22070042212805450070075494418420409552a0b6020510964240e08032110181c61005e402d64082d114071108170669500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 32954924 1250 32953674 32953691
    0x90703120c030801050409020307052101050103081207030b130e070e0405030a081b0301060e12010e010e0106090e1209060d0207050106060f030c02070e070c0605150f0604030809040203060f04 84
    0xc1c800550340520703100c2e641d408810390740e0344100000c0d2007000c68080d52640000c0003c00c150319040740f0039008a240c0c0301013140c0d1800c0941161742128026841a184400c0020b041d203681c80701d05030860380c00320550604001d03050b206401716507200001040c0b1760110380e403085060540c00c2d00700030b01002424244c00c04081803410f8502241c0741e030403404031500840d1580c40402c00082004d406080c81c20001040d55041d81e1030940d0803204141249211500124110190074055000380218101109540c001003140b503103540c1c03d1421a402039020107142480d10740040c44404010070384a0000305d00c00b82c46925050031350b0000c1c10070320406040380380303c0f880040c0180400806401140807155640c45000034100c86032800c3e810f4503104a001001608898000e000c00c64004000d1034001146140200d02c1c4449556038004852059a1418001d034492030002c099107080b00c040701d22801c0035a559410107103942c1d1694500c1c068100050311541d00030000903041c0e15203d0740b00c0305001008106204811 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 32956174 1250 32954924 32954927
    0x70e011211130503030415120b0306090a120509011b0314040e01030227070c030e0307030b090715020607050901170a0207050609070f05090604090b070203030114030a0b070809070312 80
    0x5000d01d04581004031031800c0043c02d13143c04811b41d011a007070403440c20b4060520410856649100c0890801115501c0c41110f81c00d03202006418850301c0302c0b80c0141100407950400114075012282d1030f03402c10004001b008081e0764030800c4e5a14000300050007040c10965031405803030b204298601c03201c0541c008540080e610000858140c101d038001d4401581070040c0100195000110202d00303096041c6c0c3d0380216901070320410459416500914144c0211a07400300080e003060042c0c0e00903100b17010b170341d014001904000d01020380242115000040c0745040200b0203510795070000d2421090160110310b040059000d0381604814020100c2e2000940c03400c180c40741d000b50072044064a040c4502c2d07000800c00c3e00c5c00075680382501d030000205d2005a1516041000c3d42200030005608542c58075003110000c0c034280711590240741c0c03980155480c2d4ac100912164181943c00c5110310950001c150307030000c0303035151502c60f41000e05072620088650b22581d0312480c05100d544010b0880107080e102246c100d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 32957424 1250 32956174 32956177
    0x20309030d0c021515010c150603080d02070303060b2802071a04061211030109090204020706021207080f0103150209032b030b030c180402010207081c091706070e011211 74
    0xc0210002482c0705d48440070000d004e481d4940712540810421030743c81c00440e41700d908024980c0798003a0041079880c0c580c3d581d000c1a400256003403c2c2c0d542c01007244000c00d0340500402002c2c0009072409401d0150b11a24018200c003441103440305a5800b41054441c14400d00c0640d0107000e9101202d100c130303032450781c03201c401da40144076080019007006520703912036085000f0346100200410303140d4203690801c18440000d1182010880e407060707081040c41d0004090780003510003100c01100c10b1095140151004d04841c80c01459507401f03c140b1700051001445030328514042c451200401a00c4034913200100c1d14003005440070380c031003d40030038000048400b00c1c80082c942e64000d07170342841402c101030185540c0b5a80821042c3d8000011560101649030440036207a11600510464a1480c2c1d5205c000f0b092000111100020842100c0681d61880d0451106001000000b01c00845141d542c8900e40d11140e000d88800c041020a001c0006141c0c46510703440081840410104281c1c00e0382ca017042001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 32958674 1250 32957424 32957443
    0x4052e06030b01030c020a06020a0c0f05010501050a1a1806040306020c010621020102100906021207030501060315030b0609040302010e0f100e01050601050706050606040b0a020a0614061003020309030d0c02 90
    0xc1d0034441c0305540c0f9446406410101c0309642c00401c000c00319540d5440294001d24002010400303403840c0301001c0f644034051128001e00510000030154180020301108107a1a0807070480ca8108801001e492020381d8201c441c2d02c00f5502d0703490500541d0b280081c03101d1085a0014161600100f0300d00380c03003d0113612910440d8443c1c1c20a41440c0302c50340010b000300001c0c001c080c1c00b581040e60b02c424045003540007511490f00c201d6005190040211440c106050240c4c0d83d500000e40c1c5100510a00346c16209403015244034400540f040c41c0b569941c0501c07104000d00341402051240041810103000f50010081084020259506001403001d007a81d1460301c2d500410044e41013414500b4201c3c41880713007601400042e51b840d484d00d40e8a032a5440505406007982c0d030408030411000a90700b405034082c141c2520b066000c0d03e803654903820180c09841c02d0700c00c42c0d4500604401444801e07903c0c400b5214034100c00c1d040150326580c40303089040c1907024019000010301d04049030280220b902244d404034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 32959924 1250 32958674 32958677
    0x60b0103291008060105070303020d0e01150305010c050f041401030f020301140102070b0c070e04030c020901090203041a01050609100e03070303050901110f060103020f03030c070306020c010f1a04052e06 89
    0x40709a8002e03801c446107001954140c3c0450020081d8201091190700140800c8640c4040491003a1030905600c0c00c444040f0f401000c1c0d81800801030040040c02e006d940b03406002072410609006d007800e00340c031061050780f0411f14101c80c40314900b08030342d000342c0200800c0c40204200b19200d41e540c00c1000358016086c41c2090040c06580008500c0240b01c1041e1081c010641c4014041181444501c01c19143e02800503404e00078480a581c1c016500e41c102d0394040d1030980f40c00342c0c80c1e0074586070040f0412041040c1e03061200d2101c2c0148001d46030202a200389050480720128400c00030344060f40c0c83c03200115065054098007802105158201e03009058245080ea188820314011035403407615007025082030300d880d410880c010009858003031100002094000d00f1789150282c008400c40c5443c5c1954000c8480c00c4d0003260fa07810021082c0314000340188400800d014a8110071081441296100038041c8210380c1da901184946c8842d0010103010303e801e840d001c0c404030178000c08190b6841644541c90 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 32961174 1250 32959924 32959939
    0x30a1d03031503030f031f0e090d03050a14042a0305030403030e0306040c1202040f0e0105090c0a03021804290f0a0b06070609080903070b0414060901050304060b010329 74
    0xa800e003400002c8600380903000e005c0500359107688510010859407007007003a81542901102190103c0c08020709801041000014458402089000b030103691004181408051038400d01c80c41605e915844554887e50102480014a5581d040c0c3c1501802c0d00c901034010741e80c925404410000c0000c01403080e03a000b61151100024010100356482c0002c850090000c000c0b03030820800407d1101240002c00d20042020403402094800c4ca03003102d00900444031141e4650051000c001c1c028086140007550a0340c00041e007508540214820f80044030700728081700d0300000081c051051041c55801038000c2050400c04601c41c002e4a2504060140c2e10318885104e03000c08a16a5500c5100d86c01004e01c0c060011410404545c0b6107200800c564102034030011002c2001e098075980501404000d010040913030350301e50b401c082e1404e008000842d000790140c0003c1240240680e000010343e079009512480104011648034012806058035054005581c0e1400c003290f000c4448169201403181e60540302f06 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 32962424 1250 32961174 32961211
    0x20d0b04020301030c0314030909130b07030c050901050d092a120f02010f03140c070507090506010903080c010603150605030f0703031b0c051305090f0601060e06030a1d0303 76
    0xc2203100a01c401410340002100400018044900c3c10361948510000c1c3e90521200c0342c04603c00c21422100d541040c071817482c0300e0041007034602d8200e42203652450300b001000c0c0c000401500070f210707039805541400740200c0c41815412542d00076242890740808491040c40c2c101001c0c4540d008071503803c1000660041020803041d8032041c1c0350060356049248815003450540066520a94800c0441d003010b84614a024178081007250650054407403072010b0b80d84403602d05007981000d0050300091390250901d4188103103680c1c410003140a4a07000503c040e59020551310543c0104243d41c0020b2103040c40062007a02c1c07940d2030340074008981003075041e1050b00019100080c2c885c101d6000c004c021842c00c443c1d00040782c1d020380381070404510420f1440c0d023050701c90000560400000a11400b00c0e91a0410000e1184041c00740c4540160303d80010089541041030103080c8660100905001c0c180100004a060401c2d0300911408a520689107a00381c042100d01c984030f50040783c0000c080b044880d0174 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 32963674 1250 32962424 32962429
    0x9090702010b06030c07020612040b0702010b030f060106050906120a0f060e04020d030e04020c06090307050c0d0506060d1a190608030a080f06010309080a030501051906020604030807090f09020d0b 86
    0x20100b80181c018802459540d0705008071001e500000e00a90b0000750600400c41034000c451480d500444c01911034400310700d01490003d0940c1c0d0000242c6010744c110b20f00d4a82552400034a0300d065413080e0910703584480d10100070841600805460041d9074050f034080c0001040a0b9016400b0f10340134446c00d01c08540c0700e070107090b14400c00ba100250401c4e0010a00070202e4031030501c0a2003404000c00c0507107000f040510041c5420000d4071300411980000450070308201003000780c5000c0c4481a140038100501c16250942c603090001e081c1c6009042e103550b20300800280054403003103189070681290702c40c1845d03110361511010840c241c0c11820701c0d004d000f152000700003082d03401d00310311a513464106a4440c0d45170605540d01401040c107141d00c818141d400603940e00c02801a151a82e540050345600d04810000a0003022507800c078041c00c10308d014040c10790f0220f8542c0d401a0542800700a0f51600d02003103e80200750380c012252041301c40c03000b15099605800a000811902038140300ba04020001c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 32964924 1250 32963674 32963681
    0x510020403030e0d020a1a0912150a0e01060320010807020303090d1209240f1b0f1106010906060201050609010f0302010c0c0b1207030f0b0a1a0408010606050909070201 74
    0x40036001c50f403200b03070010302464807542c0c0340941407014240e00c4a843d42e0f140030341000c5002d001980c8011902282c600440c0c00c10090114802c85130360010074410100c5510200b80d040c025003284091a1244002280395200f50440300046511420007400b82098050f1540049001c030344441c006031145022484052000090b03038000ea141c4405040340c00d003240341c00d07101c500300041c446026940351300204000c02c04604000c1560801c0b04c0440150303407842038240003195046281645c0d41e134540f030300010207030b403203048548030f01c6841e4281360300c03e9003101380d041d540170411143d0006503206200010a011207280c11080403504650024130650b240c5000308070301e03403209003d100c1600085800802c095032241d03601a2150740a40c1c240c5050750b8072040c1b0b4100c6944150103444130102e803142030014842d45032064205400c540340c810010f20302090001100e5029074420f0049a0402140302010640720700300310740013440100001c11441c3c0d40c0e000080c3c00d40e08008003444c4580038003000074011500600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 32966174 1250 32964924 32964929
    0x9030c01020109201813150509030a0804020d0209180c01140703140d0504031707020105060a0e0a060806040b04050613030503040b180d03050a06170304030b0a09051905100204 77
    0x51382440090800c0c0402000d08103030024055120400e64000c01d0341c08441030b03c43d4010a01000c82d491085a541070060501c60a510003241280c0f801040118007034010082d154501c000d4a00b90f04c09461341e000083d4005014007001e9400110300040c0124454800183c44000c3d0030074060701e0080304044015102c026007104000c0c5448401c001c800d000a200d0113001030802d00e010350050605403034440c00c1c1c081300c034119404c8010074080e82c03428080e40c0004e1f81555010741144001c3c0801e250075000304c0d480c2c1035140b00d24181040a40c000c40c5003140340b40c00c4100904008011a209843d250411049090042d602910140200300200364514400c1884030f15440d0561111372440e00c4d80d90307519605480041c400d0118030740c00944d4840f56441441400f001d4491a913010841e0b09200c52510121450b030b0f440310101001790b450848031040c000c03040e01d04607508080045800d80d2040080c2d0f0140004010003861801084600c18207490801312100d003d60040302200c940071243c2e45101c0c05c910560 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 32967424 1250 32966174 32966183
    0x31306091a040e0402030f0a11130507120b040b03030d0501050a0e1605030a0b10050a0201060501020105060a030605040206090a08030d0b03030a0e040c0c05030c0304050301110f040308030403030e0d0509030c01020109 95
    0x411080c480400f4801640790058800317400c4179210a40000544d040004029045504045108400003d40751040c040310450025446c10005070901c0d07000a0091035000d1460505c00340c80e04500105690381b42d021000e1044003070156030b5102aa28910f50050600740186813040140400102d4501c00802c02148250120814141405441d420594490300024011900580c40e14880002c2c0c0e162010305030a104141c0d1111610f4201003640642500c03804e0b008a411a890101001000e54a03242c8603070440344c10103000a240d8484e800825500d1048600c1c140c0c20481d00d04c4001105440000140070f02c50f0012403c00040c005c407800c040d180c0c4941490400000e0342c43c4007290461030a43e10903422220b280c240311800c039a80380d07103103402c40c0c01c0044109180c0d00003103010041420203000b0b0f40000065040154603080914211148078001c43c00040c0903140080005000c05000e83e002c048410003e8046800040442200038404c0e4001460503010b802640c82081540d40140203080545901 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 32968674 1250 32967424 32967427
    0x130b03030708070606090603030503071209150c0302130605040614040e0a05090a0203250e090607050f040b0c0a030f08060906100c0218010e01080303010e0a0b040e031306091a 77
    0x1588602d48980c0081d8420b503041c542d100c60000f070b825101d01ca0100214400e40720745891749084903019250301c90b00007002c2e000f24207002c031401c001000d8100d260710b1342c20502c0e4001074803c4c8828085000340030b4541004091400d444010034801c0c3c11030023803c1107500390b40d29010401420190002c0a0140740308001001c0c5202000c500301d02e20300d8204136401940d04048034050951030700000e14140d20130242880150310000072000400042c61080050300799400d07011410700309a90719036900c0344001e01000400c040030440d2000c0000400882d4018a034060302d003601e6400740c0700242e0b114400132800b2000325000690581405001310117440c810400188030b904c00344c0e500410300c45840100100c0008002d0034119250050341d0354140134030801158222000c4070b40c14054030071800cad01c040e00056895441400104200b9502980c500c0d0321035000100450644003580c003281c09004800074030001c1d0b020110380350a031038540e002054102d0b040d1b03943c0c50213200c1d5141283c01903180c1c204804030000b00d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 32969924 1250 32968674 32968687
    0x130f0b0306010c060f0c0c060b0d050c040b0a0807030c08010b1002031c020409020706020d0c11060114030a08280f0203040605090d12050c0c100f0806030703060218130b0303 76
    0xb5034032180002d401604c0c049100342c2c204104504030b910041d000c10200d002c10380300400f0310549120b0180c6545044e1b8140249a049403240c03585c904a902c21248965100c280d200515115651501e00034040340084425140d22494548001d156902a04400b503107000614046e6191485400d19103044640103145807004102c0c1d00150070800810b05e5008030f4003040002950f4041d8030080503000e028040060701c403003040043c103003030310341d0004100200802000c01d801880c0000c240d090460741014802401c2c6407404d40403a081840022001d0325855010507540040c410076a669035210010803030300050103040500913038208012140c4840140d0040c84203201543c0550b000b03084040005190070840c91711513864846071400440108006240419402160f03d0200024006840c003190046181b000d01200241444600d844880820180c4400714120351000d000b004040d540100055558a178007050712031140019074030182c020704103003241706910b600351b1040500c1080000c010394608403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 32971174 1250 32969924 32969927
    0xe0105010c030e030d0306080c04060e010b071e081207170a0b04020c0304120b071d0d03030207050d0305090d03061d0402030304090204060206010906080606091602010b09010308130f0b030601 84
    0x14140040b0184014a441c0421a503000c0191124141d020b54010805d282450140347c05c0069842034503014030708105050011324070f07a0755080d06503154400c0b09074480402c0d04000c058106041140d8100300da50442c1001844070010080449018420000c110703500c1d4890120781080c09003000031210582035011440041c4280c002c8401110000c0c000b40c14050600400c5046600c26403069200c9100c100c41003040122140ca1294000c4460505440d108010480c15245c2c00354011518845c0c1c01e5540602c0802d406541685c0b0346541050403160114101c01d00a4000c120550b081d450612910700c6812042d8882e00401094402008840300c001d0b02c401840400c1d035070050001ca916010074400400c1034422440035000409481d8002c2c51594980480401200c40300e0300300b0301080c0c000b04200035690312641f21080c0c002800a13110b800c0d0340c1d50440120700404078a094180c5c0404108000400e1010030070182c40c4aa00140301b06071400c0d940d40307240c0d2480c102c3d407150500700c802c2800080c03100d6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 32972424 1250 32971174 32971187
    0xd32040201080a0b0d020a0b0d050702060106020706080714030f070e030c030703060c36060309110d110a0b030f0a0219080702030403141e07051309020607120c03020105100e010501 79
    0x4200141511780c030b2002540c00200c000e10140c000030b0408201040c4245810614010b50b40c01c9401400074041c5035041160007510703110940242010310070704801064034184603c0f0543e010400c034087c1c0b66101d0034070038100780301c249040e5413180000d043c07120b5103246468045140002c002d401401008c1140c41c43d6a01800f4010891007442803040e0410285040c501d040090800034522100c1580f4160000ca810003c1e081d85400080425140c02c0c0340038006174004c02031039021181140d25400040091410035690040c040712280c0085400c00005007558664000d540900e4108491445550fa05407400d8224040c0f00044002e03005000f0344428500e00034124281c11520606c123403460706441c0d0700c07000d20b8848148490300c0c896101681c50051200080c0c0d0007071240309100c000e08100e03450000002c524151404442c55666504c10a1100b1995500201c82c0102c0d44401d8038000381030a0b000140c403440c0081400d81c099400e020001c1c1d03800c51403c0d4030000351070300000ea8403400d900700001190715 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 32973674 1250 32972424 32972441
    0x160204050a0e030c06010602120703050f180604080f0105010506030f0105060f09030613020f0910050103020c01200418060503030307030209180c0c0d0e03030910050d32040201080a 79
    0x440d82d25416560200d000340010700110303540c0001081c0c19403403e030009180c1640340c0300c80c90041c0003d00002c030019510104803041080003021458940d1400f076240f01091240c14490351703120304000b42c0098080c2000ca405801204820020046030b1f0380d031018803505102c103c0d4401404403010005001034a440c5000c1e00030810030030280c40c00c140750800801d140400a403041011810031050703140031854810300356010090180c48850b0a4180900382800c50715003800359074185900410480410300003503220114248418040d1034010249171b8002090b0785c801d002e4806030942942c072004655015001c1c1303a00310342d4054001d41c40c55640c050300310003e400065505600c1250003108060260641d815140070301040561155205180e034102440c2c181e00c0400c06050010307420b1442500d81d000700c15101e04a0f4295401c000b084245101180c0f180300d2080c07400705075454a0344501d4000c2034840c0700d82c1203900d00406c1a0450050740d50360001110101c3c0c00070b0019100100041000e03c10350003c00c01d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 32974924 1250 32973674 32973691
    0xb0712030e0a0606080a0629041e05041a0603030c0c0913080703020c13200702040e03030f0105010f0305060d0f0507051c02040f050103051203070e06040b1306020316020405 76
    0x950b12143d502c2205071481d03940300206941c40b88880d442801014868031000003483c400850380641c03a404648948144000942e109a594040080c40381c120f841e01c000311144401400c10581c50f140c5805c030300c0e10856140b5100c001c8030990000c1e03210b00f000021640c034000ea1800410000012408204013000e008007407545603241000b0f1300000525202c0600f061520940142c0741400050062013403043d04040410b44190402d4a0f00304105035100c044062003203c0e060741030340c54a0b940086005800b00d2015558240b00002c00c00403001200b00ca01e80c1038401c02d9a074882246185d0784114155903064511550024210381d0020008140d0701d08800603520900c00d6070080c80e034550010b402201f103030b0b902d401c0c1d82180c0284141146003520402070007600d00b0328200800d50564840594600c40400f85c0d1801d014004040350046000d03461801d0705080040c25150758580310203042da225007040d1f56140500b0701880d070201d102c60020042e50302110402203100c1d0901c2107a02000081c0c00080c00c10704 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 32976174 1250 32974924 32974933
    0x301140324060a050d050c0f09010f0b09060c03030115020609010c050412030c05060c0904050c120c0a030207050712030f0e1c0f02100507020307090501050904080306010e09040b07090b0712030e 85
    0x5900d1702e4002841d98441d014030068001c44280300c084c00000300070401000d2242054500500001c00400701c040151040207005503102e004030130200b841c40c400e4912902141c44007100014a44c6102070309808200c4440e425903086441c0c03044001c0c02e030f640f17002c0c42c1c0300032604c02c3c0824405c5090200c0b0040d0054024504400060095100c0c01d04111003620003041c4000005030401090a01c1d0003496002841558030301c0c60b24003000048640590041d145030402a40003603401002803203901501c4580d500541038a41d015540c1c0d241140181c107112044006ca00900625034500780190785202000001030729405800110340701001d80180c200d1000c80da8003c40f03201890158490120b0701c0460310485d1565980c46040780109440c00c1c1e0f140c0c0c0413110385800c0000600160300c500c0d900a4005606c03000541e1070b5111600142c400703c1f81003125503081600c1804200902801d100058024030b01500c0300b00900351200c2c2030380054440c0200152000c0c0c5a200401215403180e0302c81d0800800010948 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 32977424 1250 32976174 32976179
    0x70312021009081e0403020913080c10050a0e01020306010e01050306121204140d0c030605101203020d080603070803090d0501020f0c0d0201051003150b0102010f0c050301140324060a 80
    0x81d021030b0818403050396a60804a15201003d41544030544007030640a49682411b186030300152030840f00501c200c5030311f26445040c2c010800e80206403412521100c003961174586048920758010401200c12514550802102c0e012451042c4202c034017440040c0c0d2030311070700024034005440c0c1d41d001801c0b0f90f4000c0f1140c014a00f41345000e009200c024403e55091665032450110412010a4000c001c03621860012100302c00182a10318400c1c22664001404603003640c0d40f0005a0291a4645c044040840000007010400d035021540f2000c20305641c4031191680c84100a05a0325134150143d0b01d03a0381e00802c0001d400d443d003011f007640e019100701c1c00589800840742da0070000741c002d005a4641c66210a110340d20581d0203001d00ca50004150b005504c0f15031458440d49030f041c1e1081c02c5d640c2820fa5500c0e103642d040e4402e410508200c0000401400310341c3c2c1421004296030700900c03410036484124096a8501d20700070072005000b0100e458810301401c000d007059002d8160283c4140d500000c0703c03500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 32978674 1250 32977424 32977453
    0x705090604081605040e100f1b0f080108060903040e0408090315160215040305070213020301060e1302040e0f07030603020a09060801140402151804051005030f030c07031202 76
    0x1480a840b800c80504140038a00d14084002e007220b800c4a48100d05210003000500d500003008560003200c000049241c0c000c500e112002845801c135020680883d03103407503114081d00701844035120744465980301c01aa0303031074000a4642c0402d40e4280819081008200588008580d0158205004110007071038079002e100001d10b442e5500e18020350a000c1d850821001c107074079042d454401c503681c1c000303446085a240c4104500840c010f000400348100031030054150740303480c1e49a2a403118001c400f15501e5031550f002914003510580c285100d00d41c042c2c0e65400c842518000d540855a00c1200701903c0d4840a1590054a000920341020544d4480002000da03581c4e82c10341d0300a01c4200000940182083c01c0c590075108000d0b8100ca6010752082440f00603258030030a4440701801c026007035100c0711241640d441c51010704511aa20500704010300c0401400c1401100485030b0460071900000e000418680e101e000e10307600300b43d040d000004d08102081040c4410001d0200602c151921107048405 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 32979924 1250 32978674 32978677
    0x10060504051918060503100c020c010804030c050d0509040612020306040f02030a060207150606030e0c010807030e01060b0d06120b0a180206070309150e0307170a12020a0501050c0f070b07050906 85
    0x840e51901c4100420203403d040c030044480e03140c4000123006e28402828080e55840d0f05103c03590410000764001414180301c1d060b00603038103034804181d03580015040c02c0108540c0003100200e02c10b510380301d00019a440d240c100351020641c040d0180903c3d0f074540e202e6074a03102b14541d0503609401045001d8000840078030061101522460242c0c0c00f40d402545180202ca601da0000810300d4900210038006c0e100026481d07180b0902481d00e0785459441500840180c80c0d2060302c0300456091200114a5034080d05c09004155040703075041011603a05d140c2d0f902901088040645200a02c3c0c010a840b200c0e140c010001c044a50940ca440c45403d0f50301080065000c440250000b03001d0143c107000842c80c1c0d001064904109103800c0801e03000d1100002d4695926119065000801400c0841d26000030f000302542d0b076400240d00e0840d81180c0f00c01175280c003150002220607500e030900190070542c505050383d0180705000c000c0d50804a8944e601d40320404058000030520000388003900c4603503100740 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 32981174 1250 32979924 32979959
    0x19020705120301090b06040501020a0605060a210b0c03070c03050c01180b0402040e370812010609050102011803080603070f12020102010e0303070f0c08120f01050306100605040519 79
    0x103002e550750325000240084944001c01c543c40395404220400c007983e40010320050050300030b040021140c803002e00180050006500002054086400908240c505c07489040c10250203040c140f9080c1c0d0f034243c1d20301e00c2c910048034400040341340d510402010070300c502c0142c2a543c0e2080d0000500c3c003e0500400c5050559a00844494030301744108011420a07014403c00d1000d00320082000038240e2081c0281c4803405000740c1d10690003c156464582a02010070985a8012070081c0d6035295014561002207030034000d05002c0b4280c14000901c1d940f05200f081245222410600c0c6c0c1e4812903030f02215440d1028081ea5030511034001c01190301041d540a41000b00700b4140421041070041c800a802d55451501e40744c0550401c1c001c100140c0d80140d40c203400c445451400c801100f85500e000c0700c660050290440030910500c0c10000c2c21100000c1946c16a00101c0841e41c0c2c50f81d44804504102c040c034010356000980a10080006080000e814203452251a0b80c10a00680710140b90200f0003802 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 32982424 1250 32981174 32981203
    0xb010b07110301091101050702030c090901020306010810060f0507051c03020a0306090911090601120f02070606080a0c030303020c0a02030a0507060f080f040f030302120f01260619020705 82
    0x22258104108101e045006200c2500240283c13555616803400307454504d041c1605200303002801c2c0301159414131003001c40c0c1b00c00a00440c0c070b0342030440c5d0300f5000313400807107805002c500c080002c19952449032681c40110750096491040d090a14281100c1a401c8403004480502c21016004001040c4211003e04109540d40068a42440e101300400b503a81c0d03688458100c1e8904803181000c90794140c072940e50342c50181c03000c0c0c4858403030100480d44042c00d0b0b200c0041692a0001e0148002129001010018000c11081c0445c1d074650740b281e521020b5081004200c901050f80400009000790040c00d20126103406540030f004c0550042401d00d2060701c012610b51b00300d4441448101e0300803802101c16003c9103042c95091404241c0c070701c0041009040980480358207203140c41098425012554052100e40c030396540f600306601d4072503064200303000d041035040717a202c01d480d82c59851000e82400d182030b400041c1000d481c3e160b408814281030407400180b5540030803080011600400c264450280300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 32983674 1250 32982424 32982427
    0xb0f070b040317180a08090a1a03040b0105010306061d031603030221040501051206060424020f0f0304030b040213020417010e120910030f0c0906030f0501030c1707030b010b 76
    0x4040300c031000c08070020200b075920440d605007420001c100040b9480300c540d00c446c0b01e82d40c0f0074100380010b43c001c140303a002000d0044052000b07008424a40003641c012482074125030041d0348c036800154150b8030ba074042c080024070300c80c1e29070b842c24039404440c0c0e250100103001d4a218000d0070307105019100e05600182d001d40c2c0001c50009a2900c0049071038582d580c0710024a00381030800000070300c20700c111564039162844081c04070701d0f655185021a00103180c0009480c645900da910740c8098041d0407083c4d4009400341940314646124007007407138804000d80001035850306d82580d03666000084090020307030300606851502d40c6c00d014148004e101511030201e1070060709903071084081c2500d40e2041400255003280108a2800c0343c58000c0d200003190032248c003210411440e0040b402404000408042e180c140f0300c07030742a007503000b130400d9083e01c110ba90300780444480c011030b60066890a00c00200345d031070003900c1040000c500020881c00300401001b44c070340c401c0e5a07894010605400303030425007000da070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 32984924 1250 32983674 32983697
    0xa0507031b29010e09061f0801020a090e102607080a0302070806010b0c060103030509031903030606030b0406030206040b071407030615150f18050405010b0702010e06070503040b0f070b0403 83
    0x101c401e0b01c00d0041c1559810b9426903e4408a101d4032101c0182124600b14410ba05807005400c40d6601d080150806000031510f600806000034808151407181c480322003283c40200e011108090041026140d00485081d441c1d0860b0310290140b1103070b10b102162a009035000800c400b401406100070090180d0b00a052030350600e0040c41c284807043c1d111101c403603401c000600d150900818880c0c1102c0c2c240c103109445441520209017010070200c50640d0429151801c2070030147c042d840602a10344a650400140b0b14a0085c8001c4a180380406988403100380020411892400d00800440348600512030890345040402481c1c0506034200322070242d294850040c4040b80c13003070100000c00c00303146100f0204040003c050408081301d0300744810400d025441a01100c03049099100601000e801000302d980e65910840c000d4000c200100d00281140702c03103014603d810720a640708650080007030351a0034a464282240e0f03500c240300f030220100d4140047c03004526081d4020b84158002e480d000c030802c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 32986174 1250 32984924 32984993
    0xb1227010f06080f0609150a0b06070c06020705010903050c0d0606170102030a050f0402060702040b060903070e011502150106031821030506030601080a080d020705010509071701020a0507031b 84
    0x4c01000100d54950080e0204041400000780031117401e62150300f0545103495144000b0064522114800d030800400550202000446285502201d102c0d81c280c2c0d080d241c5450045640070071504c4080e2140e03000003807029071072510702000000d981c45031b600019150b682c1c4034503551443c07044a000c2c915960102c100454040c00d070082540c49001144403880c6440c1640c0000c20714003a00744007a0082c0d94480344c9201076102c0c082100ca10403002000c481000342d0719001100030900c24084c07a42c19804443c1c1803501140002042c1c00c0040c1c01d084103a2841e0300b4510202c00900102c007400207920b00e072100300d6021940e01e0343c07007104200c0540150500100403880c06015100054100b501a03840710700100401c0c07a0108048a00c075a00000070b07581e400d1240031920180c0100340014029500e0700c028050181e00000750030f411074042643d4107c901c03e201981908130b00a20034200007203a000c000d8000024483e0700c5d00301c00c6070781d0300903d200c944240ea12040c0950003005c034a80d01903040212080c5145 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 32987424 1250 32986174 32986183
    0x111031204050f1b210a06050901020c010605060703092112030204050108060d0209070309060209060412150203010803030f1e010b040f0b04030809010c050703050f03030708010b1227010f0608 84
    0xd4188058203013501c06400410310000700100c120004655803822150740003420301910010710b41160301406281401600603000398018142040150b191500004d65824008240c030b0401c0c0c0c264035034040d45440d100da00c2c6d40014448400088104c101c606110000e00c4440580f44400582d90300140c441d400c2c01c0000d030001002070091032180c07258090700b80041c0c3d14003204562004440c98040344640da1460210080d010b144a0194030007008940400c44820354070844020340d010740b41d01e030030005074203501c0e00480c4420b0003500f5080c0c20410000354066010b500c043d07088a0300003a0314045648450b014615603070207811400003650001820850404544010805000100c3c24546003910b1560303090740354803401c005c1c0c03818810303525444410302100703020010040d9040015a1060841510f1840d202d81c0103e58200200d0401000460400002c00584078520404100c0e140c1d0354980c00200c03c40700c80714800c0010b80242400304115224000e0142420314480d021000c111107041c0300fa51400d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 32988674 1250 32987424 32987443
    0xd0305070813080a03060308070b06040b010f0e0f12030706050a0605030705010207090b12060408070302120903060711160906030c14130213050a03030e120f0a020111031204050f 78
    0x1048403400c14440d81844841d4a1110203a010480710f591300c0700120140d014107896403016100090125284051182031450603104103000c480402482210360019681004200c01d141e00280e40c1c0780703080f0f0050800507140c0741c0e04070340103002c907010440801c40e0618503404100101c4242c1c9d00d038000c8c84036092407400f941c0040d140460150990a0508000070341c0c82c82e4500c07030710000e90740707500044809441b040301650451007150300f07480c60303403500c2c0c281000140c0c050305e001c42c01885003030400e00b2010074000a850a0b07240086c042c140d552a289422100303690b1030454a0035601441604902c01c80400070b16100070f1622140c045000b03442c0d401d00046000c0e090380407400c0e41e207161500d00f03070580e03c03400c4000800d01801001038494003c04d62020106078190800c9030803590805c0b0200c245a0800c0c0c0c200d04260045603031f40101040541c40d9a1501c42c1803400303803207940c0204191001980664074420b44a003004e011a07062a07541e0201c940b5441c020b0f201551150042d814040c808802401003100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 32989924 1250 32988674 32988677
    0x2150c0309070b0712093609050a0507080d0302040b04060815040204080d0e03030403080f0a030908030a05150d050c0d081306050309070902090a0314010e060408180906030604120908030c0d030507 86
    0x92060450f000c0114003401c050341c8046010300e90208070010000c503030041c23540f82e401000700d0310328194500e0700035aa10000d00441e03040d0312804420110f214800d000b00e9043c0c8414819050501e0710700350302501c580b20301500884429030407400321f030b031a1303152440548002c00ca6030b0020011444040f00207854003246005403402a00304000610218035000d00b19103003010400b00071a0340e00300c1481c0440092507030500091860400000f07011852135190070072030141800d840742040b03507040101049904440d00703600a1242d044400c40803118588041c40070310003405181490715003c0c0c090000030742001030342c000c100032480210611041c0ea0040040784050600000c0451900c802200041c5034408548030040c440d1b5183c0ca29001300308001e400c5188814104011030f40a4203140c5010030070703500400c44c800f00c1e1100071a0b000403540391040925000f48806000742ca030701c0c1c0716a150202c61410146007141407042c900e10010304d46008100929000d06000c0c0034050b80d40ca034010040030340300e0240040c0c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 32991174 1250 32989924 32989949
    0x40b010203120106110a0605010305010501180b012106091104090b0a03030207180f050702060711071802030903040503031602100305090c01230a030608010c02150c0309070b071209 79
    0x100304100b0020b18151486800c044441c0000e408078186801000300f002002d05080c10000170070040c054010505903102d002120701108402c00304081204c81300c40c440b0780015907488140f02d2040d80425075000b685800f20000c100c1135120b160705001e441410810b10f03524000020b0410070b203502441408860b180c11101f00c07003401e2443d18001c0d03544405000b05550111980400002d03215142d011b0190125508403e100e103250080c0060345440b000c882450104140c4100748035007520102e0840c0c180d5100c0f80d030b8004502c2080300344038000c1d00018048c03444c41c8020480840d6942d01007014254500e402d0313910202c2e581892051141c80c0710001c41400605082c6010310940e64400305820300480c1e004e181003900c180c4072070a001c075075038107e48228540040010340d140d20b555068102c0c109076074181c1c00074020a44510412a0b4802401c080d40c00c80140a0001c52804000640210381000315202103840316030711040203401d141c4c01080b0071507131581e02c440c1e071900040e04951036800a002030389901 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 32992424 1250 32991174 32991187
    0xc0402070b06030d0c241b0e100206240a0b04030c090b090402010903121806050405040524011d0301140105030d1e030e0109080c010507090b040f0b030705070f05010209040b010203 79
    0x401449030004041424841b10102d003d1300d5143d9408101320302400a0340f18682000c8401c054030340b100c10083e4500030b0115200c1c0d0303114580000350035400381c0a9403c02c080b000c06101c292040c5506540d038603d80c001d1900c600002c1003468003001d0006940100b503042c40c900d2420084008075400b82410038010b100540801000d83e800144110803203405c001c1070f00c6403c2860208485120020b44101d4069002500116810b540503020300b051b5032095600b0416034580c850a15100c07a21000302ca140d0241d140d00c0f2080c0d95202d0101c444013034070300081e020100c0780d1590000342502e141c101075500001e0500c0041102e4541002102c03045070241c10032609121089000c10303500200c0d0b400329002c0c15110600800d0303202c1d09600c40e01880f40c00a840315102e035049011240a0a429502840001c10f0100c005c107021035000110303801ca03600300c01c0c0c80003110b01d802e41125090304000c100340107005080c080c034000300350361140950416204200040c0d681590b50204021692001d0200d4110361050145 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 32993674 1250 32992424 32992433
    0x10e01060c0f081b060f0910050906040f02060f04060309030f0503040b0106030203130501020f0706060509150123070f021c0305030a0e0a080a09060206220b06030c0402070b06030d0c 80
    0x2c200e0200d400c61071841d80c1d2001007404102c2035080a285030f1080c0b08050800400f01e2021080c1c03400760360400d068861200e09002c0101c166001560785c90f01c1d42c0c0190000c5000110b022582d00441c03403000d09400e0401c0e803400c0c45c00807250069400a004240c80e41000404c0660003651039640c1409418841c0c2181090b0b00c07050003120050150009042e800004665104030a071400080136070b014009540e264240500c1030f4540e000303284100d90030350900c88003250615240e420703180714450700360703050007a08020801165694070500300414090041003200d440003580d1401840e04a005100c3e01c10306050030310606c00c100c02c0060990703800d039902d03a8040000035401800c0b01d07000141081c000c11900c8122803a107007405452000285980e40004681011540102c0d128003192131503001d50386241c0d105144108406211001c060714040c1e40395611001640422003280c100c08041d08a03914848400045400ca910580301550b0800000040001d81d10341005480c2c400510382c0b81c141c48030314a0f5070741c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 32994924 1250 32993674 32993693
    0x130f0504021809090708010c0201021b010603120e0d0611030402130501080a0206210106090905060402090607080c01062105070f3204020706090b13050615010207050d03020303010e01060c 82
    0xc00c1c0c0304400803400f09031301103000c0040001601504008100c54440e2410190003036200701007001108403502090740d0402418401c0e4012690005121614602c8480088403036824621801e580220307840c403c14040f642da80300d0b0301c2151005109035075590405004001b00054270032038020106040400601036581e0128204c000c0d6a030580c0c44c2a1030302002030701787c91480e00c83c0c02e00003032480301c5c4000058600d81c4000360b6811140204130801568450078140000ea105e00728405400900800c5400700141280b4010701800d031500000044041d110220707a00c00d5094208404903460a1100010a101050100360000c201c207400e940081c43c54690044043d070264684584401004200c0c1f00310741680800e00100442d004000310356991040ca05000200294a0182e800f60714110008041c100030682c2c0d500c480740c0150080c00160784003041c0e40500700d4a10201d60442c01249000030306a00c4500410030503a2190b000703075481e9814a509800a4501644180c3c10041400705001c003190f440130 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 32996174 1250 32994924 32994967
    0x803190f0c02210409020c01090314030402090106050705010b090106030b030f0606131512030f0311130302040209040f02160201080601020d090e0c0c0d030905010c0509090109020304020411130f050402 88
    0x10a114001c4150b010b00c030213030241d0f0b448000c095000003a0401c00720302c198445c1030783c1f612a440b00101012480d10790f02060100301c07002900a81010014000140510003038030645c1d100300c0020800a1081d13000c61102030007a0300c044082a00c0700c0c1c0b4003c0703a14040c442080300901000c002c4c040d91070102d0000c0c104c849502c16a804c050358a02030701c5e09400041c61303482c019000e180b505d60703181704042c5802014051443c501200007881c044408101d9401c0c0400c5172204800a92000002ca041d502004000c0d8007200308964003aa07504098140065203001411040004a8003200c58621900015000000c01010241103420140f003e219964128850718240c520400f486202940d403a40380e40f200348a140300e00702e9244220f0b9042d80c00198103400c00c0342c0461080e0000c0c44084505036090350640a08542c01d036000c080c0a00500c050303607065004d50ba00c00d0004101080120050306001c9a0ba4000c01c43c030012102000418400f00c00e80d1008a002040150780c21444c10300942e039241002c25941 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 32997424 1250 32996174 32996203
    0x90305070206180a03030f020105100602031803190b09010b030607020a06090f0215030a0b0a081207170304050303180a031b02150c010b01030e01060302010f0f0c0803190f0c02 77
    0x1240c1208406404140d00840c914040c0240d04070035140e05000e8130307071030701002407d00541c200030000e0301c0e84134441001012140650002c50a044100d6a41342115040d402900e0309032040b41c600c400c1c10304080c100300c1400d60044800c0315139400d001c20b60500303448604860500981c080340c140007500794002644145c42e81c120744005101d2805207447c1e143c1e0b02d00d01c003029510560104640041c8040c0c40010360142e1900303041000001d0054042c030901502511485c00385c5e0304070303130880c0a580300c6000040c00b6291144d88604411500301000107001d400a64042d9503507480401004018002100f5400f10011114010941c0c200b5a90b401030605800c100a8004244516103003030454031082303001900740f4500b00c08551290fa21a240310b008000f4032208a0000c4e060440c8081000018490703041680e80607998500011000e58055a14102091071101000300c6610b0744408919040c020f5800303603d8045c4182c0c00100c000510360207484c1c82028030192986800c80350344206d81c00041415006801c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 32998674 1250 32997424 32997427
    0x7050a260d092c0f0c070f0b0a0f0c1b080405030d030c020709061a07020d12050d0b0f03060c1c0c02030904051e06090702030c030d06050a150509060d0207060e06010e0604090305070206 81
    0x80c0d040170034141c052518000c01d22001541008100045860368078450350041201b003220b00840a42041070381d180d07018078004240d980d09204401200e000760480ea0300c2c0102d0f140392030a07a4600100e490320607452011b030000307030340c81d40e5020b107140d8148070800c01004003e00c240b0120307081c544114414044055020b03401540007450208644549116001c9250840d07900c822038108610094580d0f8012800380a035070f0b00c0c1c2001085503183c460814403191401031300a012559402032802199449010980e603010545c40b446900b007200c030300407a03da01c021640038540b44c03205070003844140e61024120560b00803040b10100c1c101a50000740342d51100045841d5031881c1c44261050f410342c414040c5408960000203040980281642c0102c802c440b41901c0c45c0082c1e540d20907a601844001022001c00100e0030444115030b85000c0004d80660141c41e10300600d40042c03a62a0301c11a60380c00759400c10b5800a50040001c038040c02142075010105031014428251541d400512900c14560b000744203000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 32999924 1250 32998674 32998681
    0x9120a03141003050c0d03020a02190312020307030207090506030a120306090f020408060717011509051011010c02010b010f0305040807020a121407050a260d092c0f 72
    0x1003074200300d5588064400c020040e0401100400020900f8041a10b0501c10340f552090305050543c1d078920075980503400342603410025800c2090000031746003801c10001e4140404404a96500300344018032209400550b074440740351901a0400f03000e640285c003014901004c0109a44000c551940c42d25400b180c14010501c511506074000d11480d00a42c4100f8940340e40c0a91003100d985c021700944032142c2c00c8034002e6076942001c55403914901c0c0c0d058a20006440104411000c00042610415140c10300900454035800440d042c0000d440c81107000031500314000a46820030b11400d00900031602c02400300c5040c3c0000641040c45030461031301007507070794000a07090000c00130982c1c42280d801010300c200c85030b0f600205540305290030780507602d14000e00d08900880c0d4000522408a270790181038040790b03519001094214004032003021040c0704940b02c030161040410701c1a2107103692541c89802840d410911058103801e24903007148841d206902028203000d40d042821176014000700440501ca68 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 33001174 1250 32999924 32999927
    0xe04150803030c04030507050f06091207030503030411010f0905010f050c010e150601090f030f02090408190206190501030b0112050a0501060605030609090c011d0303040806040c0e010b0309120a 85
    0x401903100404600010050142d50761051004004a9010300c08548003c1c0e10380d42004002c801c4041c4c00756000078200003012990418042940720b414000098a42c419030340d841c1d4900b5680300316001c075580100b000d0b90091961704005d0810305c81206107000e41c0034a08060020700451040c1040c00103005006c642c0000404094010a4240243e1010340d0044420040c02841981c2c0a89019000c00d04201c00842e0502d5000888000c1340e401a44a280054030f0f07400b440114080a4070540e80c4000401c261404400464420300558500740d0050005140450101c0c010340d00f15034031000c00d01e042800410128110291143c1511800480724003c0180c51a10a00d07011001000410315400d0640c0080d00030b030000051880b0790301c1540c001049a580d185499140d4100c68095170110344004e0f61040b402e2081c005191060b840a000ca82c034182d140c0304614685002110200d0305a88101d01c14001d1286808540b401004480e440754154242003060f907032503038020603030054484c0f0089600850b10703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 33002424 1250 33001174 33001211
    0x30c120c0a0306060f0e0411090406020d05090a03020c04140f1f03050303090c060705030a0e062511100c1b0e090607021b15030910020406080412020c010e04 69
    0x520090001c60442c1c0e59140182c054a4035200349084900c1c03800001455400500c1c0c031138401d0361311001868030b41c90340c2000c20040c0600a041600c030f1035400d01240d14002135030f00c140c0b4020300715140145002d43c55031034000d28015004055502550074128462685490340c401c2035084400c074000707091541d40b14102d001ca4020250170710458a10400320010900001000450250400d04141d4001c1c40c1d0440078040b00340301e48000100150710412003030501c20310400d03003003416240046c12640781030000541c03601c040f003040b1000740c004a0300e0b1410b6000c11941003503500038940144e5440b0400c0c1c0024401401c03000d0f0020000d005224000100d28410750081d02c110b002d8050030f908641107050542c041a582e4204891400141c494210740940c41c60007000080c0039010000c08641001c1440d04034107100c0c1c1c00240a405151044c801003811810040c000b501c00740180741c0c0c540c4190724050070101d8241142801d841c042d07400c0004622580d980c403140242c00b4890a55020a02e04491055000131 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 33003674 1250 33002424 33002443
    0x2007060f1104090501060c020d03030f0902040204080706091418040302010e0a060519050f070309080913090b010f080307030804080702031c141c0c0c08070609060608010902030c12 79
    0xd4945000140500c10031009401682c154060410a981e00c411059520715107203070001e076001184070700380400a03100ea04000701c80c85202002080550f015400700d0140c3c0c00c640c1090419412985090100a0344020b0003401014014202114880101d0105608009e5035032403c2c0380d14000b00000e002d141c000d40003410b04440403801c841603c402814190300803d0151150381c03611140081c41d11000005004840c0101528400703101107843da404154001c00041800f02c454540503c500e81c015611101d0340b031910140d101700410602494501b080c060307101600301e520301c11020317041030004e41800400d44128a5242c00c14410700c0c0ca4a0800e44414054048020b505204545003201852402941034003110200e4036800000c1e940039000c0d0803280140000d81000200707204100450920541100e41d0120341424180c0442c44c01e0703103508440d82d000510513151191107800041c02c0000a11030080104880703802044007400b540e0000780c81e18114640144180700030000b8100041051142104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 33004924 1250 33003674 33003701
    0x1020a0b040803010302090115090e07020f031b01050c0708030109200a020708012f0a0c08040e07090e04020d060b0a05030708010509010608060403080a020705010204090207031d0301200706 83
    0xd880c1c24a800d008660090000303d0003060785200000c2c000d00d150784074507003013080e9440701c4e03441c1c0d0305007030940c4013403c030007000d820031442160054402c21800340004d119111000d43d80c2811050840002c0d803e4840180c03500703050b40010450710b03000c900050143c0c0d055900c40f20f00444c1d21540c0d180344400507030842c030041041c0040061401601c40e000030b078440449050078000d00c07442600c001d9481450b0321003110034200c040c0306440e201103098200010000340009040104005000d5200c00c0358039001a0840c4800d411083c2c00d11a0880d00081d0072001021508403134103a62402d503021407405c500740312009140c40c1d06c41349601301e00d54034480300101801014048030303007aa980f421124082c0105641e4001c030395281c0480401c3c420790110b089441141c0580780e1101503201c1041c2c41c402944200c50980f6195401d001c0811071503060700003059801c2c003940d0394441e40c0118441c044d4010103039161035442680b4229201d01606156010722442000d110035064680c0c00504043c4003605840e4a07005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 33006174 1250 33004924 33004943
    0xe10090b030106030206042c15060903010f18030216030c0e06011101050c040e0c070f03051305190602010c0f08061005070506040b040b0f04020607060b0438030102040506120601020a 80
    0xd00400010902e00071000c1e140e45401004044403401c588c0c0501036804006402d90004070a199052010080c80d5084c0c000c0c000180c0e140381d01c03d81004841407400c3c04c0d1442d1940c1d403444014541e040084003800d201c1039400c20041440d580d42c4c424001141c2c420f0180c2c14a4003000540740fa80508a49405680e450b402485a4501081c2c80e1030a5805401150448000c060100c2d80b05030114081e5540ca0b64000800c18407a95140c6056425401c000d08001c41007e03101c102280796220f2980407041c41c0c2070070b10540c1070070781040b0001e800d50300101509001c0202c5c0840882c3c07007650100406030025010744031500845102041140d00e07105040c000b401034400c180a004c200f107101c80e03401d88514000d50204040740c80d80c6040850081d801e69001e5802a42030100c40c01103682d951082e558644010400207107a585001011050340107010001d200b0749904405050844100383d941c0c03201c1d50210021441c0038208000189540929201c2c80508200d000c0090580c0e4001c000c00301c10a80c01c0703280ca0307 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 33007424 1250 33006174 33006179
    0x8090d0c0906090b060906030606041206090b060405070801060f050f03090a260703030f09050607020c040b0307030c030f03030e0a08070c0504050c0d09050102041203030b04060e10090b03010603020604 88
    0x440100341c414458020b19142002811003018415100714590003004149005114420040150809480740d0381c40141000b0004084100d02303e42603501c1d101e02d2001c1151800c1d4100405451001030403a4012400c001c03c110b52640d0101e4454152081d81c03e000120140301c000c200c1d41c50040c0d8140e80b03256040003082c00590340300001c40b03201b4144100c805221181d4000100d401050862135107880c00401070050100190182d0080c3e00c1c82c3d44c0c502000101c00c9141e4950b00d2402800391003202c090380050400160314102801002e0741c482094006044080c0f0b156039189a2400a100280440e0300d640700788001c151081d00f01000c0520080c040394050103850074080d00310390218100716a2140c141200050303608040c0aa18403480001800300c0c20a0b06000c072007006004412001c642d1558204800700700d20360180803c1d0101c42c000e6500068440746081804100d814031303040b00458200038030070001d0b5483ca603003010007500c0b1540c4000c6841c3d04001c000c24050700460708000d41c00750010601 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 33008674 1250 33007424 33007433
    0xf05011803090f0602070305060a0e0102210708060a06020a021c061401081b060313030c080406090e13020904080a021504030c1509030e04180213020c0d03052208090d 73
    0x3000c0a0351a1010783c210025540c82060b80e0394041e41c400141160412000a1b48090140e801400740039200e000140c035109d0844840c00303030603880d1001442010b940509100400c1c2d4007800c0b4641c4603c05491080c40c2c1420200040e694002e0b09000920420001100c101166140c1795090300c8980e2203807081c48107400e200c541000b200d00034003401c030306403182c4c0c0540c4071444c4030f031a106031090704003600051546e260b580200b1245602c10340c00707405108100722800d00041c03a640041000786281d503648001142007801c0d608030b01c500903018124440c018070070320300940c0d99155140c3d00300c0ea222040c180c2e502c0055009034108031548207200c4408051004100034150015074000015200711295501d02d84409006401c82c3e01203c0c0180c0001e01d000309040160601e988449141e0740c00342002103941c105d42c1d0000705540c0360b2508640f101500802c4032201050200081284060141000d00c624035000e01042031868221004040184000500100740a0a20110752507044080c00070b44150806080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 33009924 1250 33008674 33008687
    0x51306030b0a020a0e090603150a0605030106060507020a14030f03030a0b1c1104110d0603050d08010e070e06090103060b0c010903020c0303040f090506120a03080901110c06040f05011803 82
    0x594400128100003441002c0c0c61084070b9400d1290f88601c1500d00b030000c140120700200070030094142c0b01c1c0d85a281411822010003510070314050f0408101c082c20f101c20b0500396840340e400007040c400144120b200590b100121402980c40c18030340701c0c990f6100d840000740341c015045140fa61314000041401020442600854402a015290108038a02c035a00010114051042c0900700e00c480690390610303440c00d6080a059019160b6143d0304151440d238105044440c10344c402c481da17520010641103003e0f00501007600410300740f0704480052411510181811000440c5136100e10800200391403560302a902c9080075100062100d41c0324012201c8035030003040800020360251140c1d0180400c0c2e49000800c0750180c540e003d00c4000d01510300072030b107000f030030000c2c1085034421050f080c0c81480c52010040044940d001e5529500507003031040403e4210b48440400762400e02d000c03c0f91100b000400a5060341040e80900550b055990608106004010a070452940840325103210414180c0c4000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 33011174 1250 33009924 33009929
    0x3050a020a0e0103030e0909030c120903060106020c010507060207020402070807080706150b0a030b030c032a01050a05090d11120a03122a0c0605010b04171203160504051306 76
    0x3210740c4205500d40d001841d490070244401000103440900312007081c00c1c49030086400481c9482100d04060700b0349480340c2030504894081913245c0b0046048140f0b894200595401001c4a0001d0300c012052280000c200740304048000d130180c2e4000443e0800c54585a0442e01d1a540000005403140401d1801c0519a400041c041d40c02605140b602020001c4000140003241d5109032002c1c641107011030180c01501c50312216550500500c10400141c0c1c0b0705010585411085580b40c004440c032414074401d8000445801904120342841103490071038019044078850282101ea80c00c0d64552440d1034058880c00d202c3c1d8031f0300440b10810319248050000340000c0d06038441e40390071101410401d80c031412105601003484071003649035002d28a0b8405a0000c105444d0030745000b4841913400d4a606064036800c0e40306002001000500300026500700c0d00707503100e14180401820700030049082032403c80c0006085821100151080f80312540d0003507003150002c11019162513075500c030b9001100018042c51 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 33012424 1250 33011174 33011179
    0x50718050106110615040e070902030c0c07090c050406050f16050c120606090a0903020f01050403080a110309060a1508070e07020106060528030b041a1009030305120a0b0a03050a02 79
    0x36500e0303a610540100b4020704c220400c85c0302c2d4014490782400c11019100700b140c03151590003010004038007074565000440c03007000500d14060341d80344071804043c9041140d500a4110b540b8260a114416902ca001c40c2d0803030b0628035200e5224400c110181a0078800c0281c000006101851007508105005c5405c00c1c2c2c00b070040b65041711408011190741d0f03c5100031500158084440c00000304088401c0e03000103000da0085c4102d68102c3d0300c000510342101c1c01550207402041c080f01c104801d008540c00350000952500c00683d040d41000e403c180d641d9807002e4200c107140d80c1c503040f10000310541020120000e04000d41101c0d6016921139031108001d10a64801005508128021038a14051004ca03505400c91503001c80c110030903800d01a40959041e0001410191102c2d010a4160390301d0042015965100c21039051140b19034040142c5d42c060b001c4030100780b0075800e0007080403d40100654084160300910000b050303481b40d0056004000400b8003941c42400d010010051080005500c10941d06c00d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 33013674 1250 33012424 33012437
    0x90509010f051f0216060305220f0b0402031603080711010f09030303020c01021e03060f030607020a14120304080d0b04060b03070e040e0f0a02011407110d050718050106 74
    0x315440314400d4595400ba5a40180d5100d2901d043c01449034000007403024603105690750705401441085c09145550b00070701c0061340740c40500940000d803d0403181603a0b9000d03608a8000481e0303840041240e41c0c4031001e81203006540018080d51401d01088040b48640070010051a881b481c0a00441e000080192809080c1807400940e039406032012900208482d110076407054a90b590840c003039444000c603452195000d010a809641c0300707802c003580c020340f0030003415200d19040341800000e615519100c0e1180c0c3c00541070122042c0c011400785c0101d80c21810f1900000c10030304070645460085000c0f58848000002003000380003000016125005025005004d118100d00800084d150540a209501c02040020410807802480c1c51001903901420104828022805540c00c200d0381c003000000913000244c2800441d039114515000703880c050000541803291907112418503d03a03000340103014106403400c000074000c040023050002d00d01054800b200140309014840584070038891040441e01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 33014924 1250 33013674 33013679
    0x402210a050103030e060315030d03060501030e0d050d1d0a030207030c060c080a050c0a0c031209090905060a09080f0a03061502240a0207020402030f0402091f0608060f1009050901 79
    0x640d401114101d0750596900c05070f2610400803c0719641c400707440040b80018440c00c100007600d0a00c60b231701c0503598070348000890074036110014095800c0c400c00001c0b6074000c00700e03100e0300603080fa00340c605045040c4030000d90700e200c2081541129101c00d0004010740704510307403903040590020b2110203503403062210311900c950300c82045e10014034041000341020000c0c03184580d014840e00141c0146c0076140112050303c8030b0341c0c071425080d11040d001596400d031980d558085c01a007056034a00105000102081002c036552582e40d00c400003c1c1c40b80e520b203a2111907820601200030256041150800d0b030081c0e44001010000e8010021b501ca490607007014010300c030b408c02e4004125000311181d0300c43e08403881400f010300741a681d0390013460302c1c84155003402000c0140e100c900c040c3d4861282c40308901b00d5800d1034010030402d600c1c0280001c1000103400c452075a03844111040b07204686c0b0380c0c28100059124080052180c2600030b400740e8000c1130303404070040440c0d40001178000700d42050741c480d4010b0340c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 33016174 1250 33014924 33014941
    0xc0207030308040f0309030b072003070809040f0b0916090b07020603060906011101090534030b04020112090b061905010906050708040815070207080a020a0b1305040221 74
    0x8198800600440c41d40030005010640480e4002807551007803805a508a89a80c1c450000719816204107001a0700c0c107010390001c511030b80e240145650494005d6082c0a41a41c84407214440c0c281c41c2406691214452200c03280c09400c00c041c1040000c00d10728080c07500102015010b0380c4000c0441c0020500d040005401c508030b41240d4100e41c000c3c0815143d0354071507082c0840400041d08603810403502d0f8280c1d00c4c49c00428420104d910344900050310150045040c03140c003200301c05604001c1c2c1c5106403901a41081014060002c80707074400604440d5030b44900042e10010940c00c81800c0d1141001c0c07648003048161070200e4442c3c001150347c1e0000c0c6044102c04038a00400e4022640480c0c81c082d018041540514090b0120f10300c00c0e50424074103601d07a40e0843c242201e0891509081603607900b4080c0154040c403441002c1d10092004020303c010b00e80008505030b0103842001c48501002072212101c0890f0640103001c0c04c0050411b660703e41035052100748000c581903421005003030100110350082c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 33017424 1250 33016174 33016183
    0x31b0f0607030612060e100c0c030e06030f01030b090106050604030f050d030b09010501030b0f0613030b0a020a0203040b03071704050705011706032805011406090c0306090403030b010c020a0b04090c02 88
    0x40366000b0031940c440007940d9608006040408511081d1f03c6025640100714406004d6001e428080b0f5481c024807103080c0c13401400460106143ca4410340c0244100050000e0b1000101c8c1100d0b00000c004445454071b00c0c0f001c0c01041980c001e5908003400141c0031007400a40550113560034450f504458884204500480c110f4922790003071584007046100400856209402c0704070a13000c0181150008503c10f070008801c0c1d44620401c90341ca010111003001400785c4014401e034002e942039415480c0691940c0004d44038851405032401c00c03680800840d4103948241001c2daa19640d03180022411f0410307041c0ac0f81d83e00d03200d21480d40003a03019900b982040460420540c01084040d004021107850704001d1403da640c0c06811110310f0a0780e40300306001c1003003405105818083c2ca10401f141d1304101c014440305d04001060b07030321a64020018840310b81c807a062040da0050301403800140c1a10104012a81100c030b4540182d0301494542d4007050b0340340c42d07500500450301e0f00c24003004004030005069898 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 33018674 1250 33017424 33017429
    0x3060307050108092e05060108100504090807050a061d0c03120d0219050a020d09081509030409021305040615140c0c040e010504050c01030e0705040e031b0f06070306 73
    0x40d0080c610410955000d8184103070425020015138107500b40d0f403544549405500e1042e40300c0c140c214910801408558419180c12030420f10303003804c070b610300195618076024461284d41d006551f54441d05040c07002c49029950ba0940c4035054501502003400c001024018201d841c48c0c401c1c49000600e4090000000d0800e441c4200ad8054001701414104c0e40310507410038060a400c0b26001c000803c100f00d803074202051402081e899441c0c940205181c000c1ca4540295451024071a08190030300c0025000640602e0102c00c0d03030203503038043d5035807101c0d182035000f42d501500f80c2500210701c81190b454100810007e85506480422807541e5401c1c02552013595520b0030000318954000030f040c400e1a402c02410301d4889041250074030783c407601c003050444000c80c8040c0d0690f55103406000070407405200c42603800c842480c2c180442c0e07401000090300c9407440d1007018410381d52030900101c2e030300d4103100303569035402c2e00e0740200b00030010f0b10701e071648030200381c20031400c2d900482d000118201d0203807290209 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 33019924 1250 33018674 33018679
    0x92e02060c09280909030f02010b0402070b06061b240f010e010509040c0e040c0e100602030405040b0a0905010602030703020d030c0e01120902030601030813060c02090a0b1f17010b0306 81
    0x6855035503d0030214150b0340c007408020b83c0f02091000b140440d102e00458a9040c400c3ea102000c0805100000f421181c0c011646407050b40104000c1000c21030ba41449600312004071074003540d4041410001e41111000c86601c0154003c0c640c0c541f6a0b203074804c07131000d100000780740401d0480c1d85481103003450101c2402001e03c42203181006100b54100386288a5105210301c0101505580728246046032003000c0750102c40000d280031082c03110103401603080c0d421170310807840360125038103005020352640506c1c007602d8011652228068100c0ea00c0e034562800600d200c1d070041200d035840300d400940b03960107600c0c00e5000d48500748c410030b10f48e88a4450b151180d04a0740c2d4540c1048013800044826206000b4500005601d41001e0009aa0305100441c02144124071982d6108031303c1d46a540342d07405580c0402c060082110710500941c6500400ca0350050610f08002180010b84002448003051510a4044014150615503185d900b00040c0800c0d11100d0b94007034400da81c0c1d00c03040c440d2440101c401c80d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 33021174 1250 33019924 33019939
    0x3090607030b010516060b0f1c02040506010c02090903071109010f03120c0812010302010e03032b1b0509010201060509011409040303020d0c030f05010b070f08092e02060c09 76
    0x54605110390b1180480107014900a07260100d00802e00007015103a90782681c25594030020710406107000c1000b074042650a0700c12418402c0200c43d0399800d902c192030042c1c0510749400026142d0381c07040040382e41842e8000c1500e1003909000c04010b40c0c03600441401c43e102d40400b6011940d034546072644070304840048030305036000c900356501c7d5444401002172040078040301000c401b00056040d80940400710105541407010f40c958000104420400c0c4101c0b406600108407544c0c5c0103c0f40001c040c50326004060701080410641c40801c01003232044500302e12030601d8004540d15551100007041c0804090380240080303501c407000c0108019083c459142e103007800340e031040a6810008503403907000c0e0080c2001400c06610b030301c04406070751201101c140002c0d622803e510b4181624480d490140042c40000c3d402c11030290703108512414070130000b5181072000320709450a81c0e50040e80b01c5060000200d00c45c103288071070074170900c1942c601d9203440c058011400003a014051a406030f412040c801000407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 33022424 1250 33021174 33021181
    0xf06050d0821070807021213060c0c0b0f030f102106060e1503010608070803160602090a030c09050901050c0a180e01120b07030504020a05040209010309060609050901060b030906 78
    0x620059000403225403031401040301e1011107500d0302c038070140301da18140c407000c0082c03410440007030070601d03c51058048590188900101c28900000c10410344005050400c440411400d2510500c0b00325400005403490010348044c100b5001c1018501580c695044002141c031540c0f0714840340c2c1058010a64208035104205440b00090074030307012107a0040100190840c1c0342d0b0031415071007030304071032052a4070b1001103821403d080034030807a00100004400b92481c14100380c240b640342d200e002c00f102c2c5854405010402400f600c1d504447c3c2000b0003c0038240925030324a010142c404a904c10160182e2a102c005054010180610b500c01c0700c11400722450950308400036900100294000c1821403202040030841c00004250b0902070140d41141402d10314203850b2440c1d018900030f10300c6c070405040500748801078480c0c46490040d12001c48025131030b42c0381840101c0052008500c0986158104280082c050340b0660080707001d00c0a00c4001c1c0400740d203880301c4842c688429900721025070b1002000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 33023674 1250 33022424 33022433
    0x30c111c03020313050a0309170a0f03110f100603111f03050c070b01091a03070605030601030203040816111306030803040215040806071d0109030506070e12030406030f0f06050d 78
    0x215030200d01350020810304100790b140ca900d80070080404601082910f90180300140300801040c0c07504504100921070055035507214001c0c1c0440580c01020301202c03141c1101103071004e0080c8282d000c0c0041c100c4e0342030b442c800418401703010b80d07210903514040c101c003558019003495014005400182030f01d0f49504d544818040b0002e240c0200703101ca0b00c48003408042d0001d4010305001e40200b4030000040303052105c1d2080d112101404814403031003580100c100300141a0041e00b900d07404403090900580f43ea95a0034000e40c9845401c008085481600340400b0403c0803000b0307500e511080540e00850041d4040381e103102102c041d800080d100f02e4080c00010010302d4a2018801c510300000f210340c2c2050303524030409140020554100f40400c4580e060304000402014802a1082007485c110310001c0ca1500c8107612214090302c1c4008001e20001411110740760b400d040100561010201c0e503032169610320090041c42001210703c001801c1000d01c00700c7c448240a0001500c1c0d004041d10380e0540282d96 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 33024924 1250 33023674 33023677
    0x6060a0608071d01090b0a02030715151404021b060405010e060108030405130e030a0504080607030507140a020f190302060901050615130306060b030109050a090804050d03050c0d030c111c0302 84
    0x420f50400c0015180803604d00401405003000c54619001151121003514103549415081200701d080c90b4940451a15100b00030030b0244110342d1124034044c070780c0c005000454041e220b980003400c00080c0251400130100000115284128080c1000300010451410b60584864081c450036480b5841400103000a142c0b28920241c124146540044d14070402001d25080d50071142c07500c000309001086c1008404c006221466010701349280c20446841c204c4c0c0d0107010401c050010301c8840c1c40120711a0082c50007007000001c1c07000e0032012114414954001e06c420300c80d1180044006000d4a80410440e4105019860041800502d0300c0d013141d082840021154011141c07031002c10341c1d038100000100c0d28038410103001c0c10081d050b0a54a40c103158050b000d07503074058a40c2219924041c4041d0109403d8026541510301c00c640c04000400d039820111002d009001c444161402010310008c8080d8155010044101145d200c015840c450500036944550b000082e09041c02c1e14402c10240c030720720990 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 33026174 1250 33024924 33024977
    0x1080616020a060509010e0d03060612020d0b090c031006020601030507050603100b04060309120e0a0b03100e09010e1203010806070f0309051905010b0d050307020d06091406060a060807 81
    0x104070341e14402140c07101d0f42500e009a80c0c0c0941659500c0001c3c000c0c3c0000c0c030400320b0008560a042c01140d00c0c0c01001448940400410908254080750003d8a01c1080c0c0000811000c000c1103c91070b41044043c05107254000e8590030b801c1100710744c000400c980003180c40b50403a500071020b0300c025840d110911030140c2c401451203440043c4103c01090161002d008ac0010b000240d40c00254808546000d140350307815031002d40c0600a4070790b040c101e01d40d40c900c040b07000d580112000c10744a49601704040344c010500e40181e4812400305080000c894015880602550200003c6a4816000300c0380e080f0700e40300070300544850780c10100001d88030b5409000a0440980103150014420328141c03646800d11001030b44110300d005081000c402800720034001c0305038070360084801d4001e0203003e076501a5603120b1403000901900c8001658018003403158410b619898001006c002a0b00c90f6048294031000c0413149640704102c07055000c00c80d1840380300890721906540e1150002c0408240002d0207051002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 33027424 1250 33026174 33026177
    0x6020a090806010e0103020301060f0e1303050c100203100b07031403040f020d030201200a022104031e0308090606060702010c051002040f060806040b0a030b101208071a01080616 78
    0x304400a811a020040d45000f4400d410440f6104e50641c41003500791420340d80304180c0020146403d1002020415040b034000c1500b074400001540545410340c0c45020316201104a405403101c1015a0406070f002541300305190452703c1019a102c0702140124003071000042c0009641c45030303003203103006008000c64116000b04140424210943d00240304820030410440050b511003150300001d0250000a4041c05000b244160400c00141d100079664181d050216220659012152041e8070002c412034015503002070340152455004100c02040c103c035010110b00240704003001640846000c40e0386402100020032044c80c005082d0011a10044540700540360f40c05040c40040a82e060ba1000380001d000000c0360026103464100040c100003001005c030381c01581440719401480d580d5040718401d8991201c4000000d445002c0d072141e81d000c15801082209104540640901040c41c018242c0d103481800d0540082108202241c500c42082c89038107070650200d00818074035000c5902c0b903d50514075 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 33028674 1250 33027424 33027437
    0x10f0c0503180a052b030605060f0d06080313060906180e060f03060403030e010c0207030503071209080304060203130b1c0b010e1c02090906040c060503070504090903030506120109020105040306020a 87
    0x2070385549080204600749440c0940c80070044a4095032240d4545008041c11b05040165030b140c840890035501c0341e40440c800c1e01c8800201c0d8008210941c0c0210050400c4608503a118031340c89685c94880b00d91401498003050030008006043c510508021440c0d441d480e40da0f000491520820600c420300280c60b5560103c110041e01010f03440400c501807166000b544d000c21200480352146007112503401207003086400291050001c108000202e640c0c0990146640015089004c01162070b041d56801c4400030f4000000d00080c03072540000908007584140701440c0c3c0555a031262a01c3c148110507060350f0040305408030002400e1540e026980250060401c03520074611400015461180d00040c0c12a1031910001e0700198242401b850307501562500007000b86080a84665804104034800c4204005000000441c21445101500e006010005040c03103611854a4082c010b041e04030741030350088401a040103c29403050154255454040c0c44680c80e045c1141c89450281d4000d43c221420f01c0780 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 33029924 1250 33028674 33028693
    0x1501120203210a0e0a0b13210302031b1603030503011401032309010213031406070302090109031118010305010203091c09030605060402090d140d020c090c1c050c04050102010f0c050318 81
    0x441d031000b40740340d002948004000c0d07030402d400c0c1d002840b012002d0305608c000341407407100001c0c2c000044994910791011454014000000d04900d419042004016654002080001007680080c042d6050b00d850011214410701c00c20300440444900010081c03036004104a41a55503402d59116a00301421000141c6403810301d002d040c0316903115500850b910004022920080841807100039000000341c9403d524000c0040700082004406001c060171801c0e5078042d140a59490103020206202182611405580c3d00e0a100b4001e4000302c40b01041406840100c00c00c00700c40c010041401c42c1c2ca520f85144150640e110030004007402066241c0095080241000075071310300706070950b400e225036110411842c10030102402d00d5192141e61040d5408854921b4450b80c0703401c80b407680210503100c1a91079814102d040e00449202001e040240c62030003050040303525008005109640c07003a00280488900109032008603144c3c4503601d00000d0050010400303541954081406200308401291141ca0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 33031174 1250 33029924 33029939
    0x21003020a030e0712020a0839090708060907090305071802070c0b130902070b010e07030b10030b010f050f0306120a0c06090905091b01030e1501120203210a0e0a 71
    0x7085d00f2505c000480e031a09001146046900d0201a01c0c01c3c00140c4210560b0480e00810343c91102d569812845d400028400000e564030342011708828014080051400c00300c401901c118001e6410700d0040c5e0880d0300080019002da5801c00469602c8002072800070f1a291400e151044500d84070b0380d460f40c00f040302c207021030500340111f03001d000c0240b13120380d070f0f5250514080b0b828103c80d880038401354010720241000c1000325808604503250002401c0e0b191303480100480080842c8850380754000006605031404a90640c00041c03240c80a0320b80701c5102041c6203040c0c0c0da5000c2c1171440c03c8203641c10000906c031410282144840100000201c03070602c5000d60b60200803000940040c0009110500c04200d003801c1806040d8011111002802d0b017130400c04480e074802c1941ca0b407401e050644038420700b200040b080010202903614000c034000700e0358443d01039041e00079040030309901ca481510300200e0090150560b8420750001850130501e072a143c05001c0e918000d0f5041d0700d5900c045050400122034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 33032424 1250 33031174 33031183
    0x606060c070b210709060212130e0a0b0f060906070f02010905060d020315040b0102030304030c02010e0303070807060f0b0307030b040303020f040603020a090e01060c030503040f0f150506010309021003020a030e 92
    0x380120034494200d100f44681c1c01c01d00c2000f40360b1420010744903010132041d6000320b18440c400e580113820b66981d040c0070821303280c0800e00c0e034000440320070703c1c40420403002220782c442d000703a1208480c5030041c540034400300442d500440007829400201000220001040721aa6441880c4103040c5200070799942d80c00030390700e6042840e03018806500001005000090414801b0076204103c0301040305050000c0000d65a000c0204000c041c044588041e1055a0041600c0300007044000c0803240d490085203014641030b08a84d404485180c18042e246203402c0882c0140c2448540140003070841914549a440c00200090804e42c03c1c19420420101c408088000410190200e618050b980310031001e4010420700455006406218a000052000a45c0f004500c4041501461718540781c4e03c2c0c500b015000c000200000522217440d400242e001c00ca030702d64014900c1818584204010745e6004015030035900703006402544040000245840740d4002ea01412182c2d100b454001103814500442c02d152 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 33033674 1250 33032424 33032437
    0x30204090f05120403031d22090b0612120f090301140121170c0705060a1808070806061c0b18010609110f0703050d05040b040204060e04050606060c070b 67
    0x85641100c1000500c40c040124003603c040e0011481e15261964800402074000150038802c0003034500483c0b0602d5039808a1100d100908c03004844040506103d100d0040c0441c0310200c07a101e19001c0014410b00c0d040c640713991404080c10190048a6112848615a900050300c01d8207008040c071590240d034800744142d5804903410450304070709504080c0700c010303800100c4156003148101d01c1e042c4000144403c03c44004001d412079030030348880008540364105a815081150050b00210318141c001d580700b41d51240c0b00c40100c8480044503290b2240303507195403944c0282e4815520040114407181801c900142c1500e11a028460f04030340c807035603440c012450a0703645640c1d8034a03071156403005034800e100350f40c014403289504000340489808020039a001d03800c00071681050100b00380003858056800c0300d0307255401c0c4d4130030851441d0900d0b02814003501541c0c01d038080c0f0300e003203000709813a08445a460f0040c0d41120050a43e81d4401041042c035074401703c01200d0a00510400150031007425010303108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 33034924 1250 33033674 33033683
    0x110313030309290106080f060a06030b0307091104090501050a080304031104140a0504120504050a0e0c0f030a0608150c0d09080f210a05040b0403030207111f0210050720010603020409 80
    0x480703514020f0006e080d0180139080f90000722800b82840a00d039240ba500c1021a5400d0402289110344100041e0400c00168011201903080505010240e0401c40052003502c8001c4800c015a903200c20511403000003071700501200d544200801d1000c03605c130382c031140c0340e110000b080800c031031006401440051402f80d1350581e180b51240c080c0020400c4c003c3c090b000010261401600b00343c0742c280000c4514003140b144000c0c83c8040360100300310741000030441e0800c0c2d40301c08015603203081c081a4440140854030801445001d50654030f00001c000598030f41c0520500c2040c58101504140518010811403808541036442003100c0b016500d0884060300707036881d4103045040c1860105000c80f02005004011043c880d00e00410000020340c429a819041501860010707210100c0f03140000c1c154102000ca10781c000000c402c0d0310f0034014000800d0b40004410f0b420345045d201d0892a8806881040c0c80c010041800446d00010010082040364540e0a1100000c070f8031030303600e40108048913001d601c20b64 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 33036174 1250 33034924 33035003
    0x130603080a0905060306131e0207121209030806280b0d060b0c060705070f0204060f0312020d020303011202010e090f2208090f0f090a0f110313030309 66
    0x41c0558210041c4001804250b030b10300d20754078007100050038a60ba1400801e881643d920700e100b4003150101d070624003000f540c1c8400c540c0c800460410000e04e007407071461100010013a6024610340d0045002d401c0300264940c46000035500c030102000b450200b6440385150031002c40301a000c1082d104501000101303914040a640c58803812042e409540031b6401c0b10014440800002120400000f0720a0340300c001890700a4642100d07203481100c40b2160140039500c1414407101003454401a0040d20850388201030102107044131410580c0c4a0701e40031101000341e00b01744010494203a1010301c90a40701d02c14500b401880c150640001d40400083e60b420780042041802c104142a4203242040800341502540e4025441c5540c1c65666100304100f65004403000b0f5504816034a46403019065000020007805140c070704000c01000501182101c80d00f81424501356038000003d0504482c041c0e01094042c0c04260300070740b010380203840514070071500c00b43d400100800240c500b803070030304028810040d0350 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 33037424 1250 33036174 33036187
    0x70609090c09050303070b040206120103050d031803080601050d020f0c01020703090e0c1c06030203010207030305040210030903090e0405070e07020c0a06080705031302030f0a050303060909030c1b13060308 90
    0x80129190303008a0002e01c81420414055640c002054034041a480706106e00c00d81e8852022410134000c05181902584500c4004820820049a0307464140c030340f90303003c21091080b00c0107285440f5516030003401150710040071a4103540b2820043c003121110080262401c403060406031a40d910081c6502c01d06d0f58040b441804055015910000504818480010b103003000302020150340f05081c201c01700e9031184c0c1556007058089401190007960000d00840d1240034900303010f0003510007242c080b0720804801744400394141c007030b1203007510903038042c0d0320507080328108510140c607000060f00a40302803040341c100142c3c8100f04c1c4d5030280729110035400340084640800511040c1080c80e04204140414401042012a0301c43d068942c000c44540700794880941078004a4104006040d0300f500740c4c02660300340801d010313000004500629050700d50601655030080340725168024888114003a8002d07084400425a200060f5026240c0013010204003150403050103040301c4240c0e004684131040460803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 33038674 1250 33037424 33037439
    0x30203060604020309031204051204060c03080f070e090a061a0c0709180f0c08030301090911090702151b03040606030b090106061b03121107020a15050702040518070609 74
    0xe441c0c00c90000e48041d81141090304801e901e9001703d04042016654450014080c840200001040d810380300800682c1c441d1a0200148403d600420590106074140040b0310a0f000d40441d10340f1600f10359803000e00c4492035004104048901814490003e42c80d5070010807240c0013002c43e14021088480e6036a910f00030410f40d503003000d5080d400010b08503d01401301e50070f0070074a0900d01c030700c2e5400464007400a82030b103003034200f014072a0080303440ea20020001061001e0305610441060b4081c84042c00880418000c00104034030803540c0000503001009801040ec1c403420b249a0001104009050100c514450b0300791240c008450940716a502c8010401c140803840c03600d641c012130380c2c01c02400b02500300800030308a42c104645500c1d100c404440c441c0189841041130940e4200c01b41e50600860b0020f842402c215001010168480c110202c00019402828183c0741d488010540303606050465a03000c000013403c004080d0041d560386810701d000010300a000c000f014102544880007007600308040e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 33039924 1250 33038674 33038683
    0x3070e0102060c04050901050d140f0601050a0b0304020f150f0c030703110a03020a14070f1410050703091809050609100606090e1602030f161205192a0309030203 71
    0x8070b440c2c43c0704010500103134a4894129040d02c0007070f941d40300502c4207450f000780290b5501e02e04035421b00561041c00c00f00140410814100d400031a1601616500e4440620f6244010b4400039401213401c681c0390080d08090231307108003c401030f104590401050a80c0a01c0300e5210000c640015000041c50f40d04040c1c20500b47d1002e140c02c0401005a0195a50f0217562402c0110005d0912003240c1c1405110920810005c0080d215408442e400c040d0b441d43d0361045d010040c031501d0712851001c070803410b070b4a22450503a40201e0f01540c40d455200c0c81d10742c26850030101700700034070b20f41a11106003101140303080100c0c034000c02c8038000424410541d00c4640c42103640c07542000c402c02c440c02c40d080003052500444c1a4114400f00c0d2402d0f0a880303114400c3e403641c404c803c60390700c0f1600041408051100b1510070841c809005401006855000b001c045846115000c1e0b2095907001400c2c0d0f4102151090340d40c0442c40318000c020040200100784000354400903c0001c83c000744240c00c05204504041c40b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 33041174 1250 33039924 33039931
    0x209030f010f05010b0421150e030d1a03030301030602070501091a060906010905100e03010e0703030c05070f03080d05060f040e030409140708071107330c0b0705180603070e010206 79
    0x4080b24241030038028060507c80e00c8a101c00404a0481200c034140031340440034441483d0b6080040101c90340d282090f41e1250002c401c12901c01d4070b006a041e40c5681c03510140328031000010051843e5a0956a80400075080000c044c0d80310340d42c6040f0100024508150001c161240880e0701c800c5180130800c0080c000d800500c8a81080004581040705450318425080c0318401803c024865150500c0800d0051030b9801d8180c80301e200d091000000d05030801d1100030182e0080c401e40754020345079291540140c07210302c00102503c60421a420300801035602c200c0d0030400003007850150081c0300b070001d000c0c0d0300281405440341c0c0001400b0402d494442c81103d03800c03104c2d4402d540322481c100d40080d200a40c02080035050003840e01c0c04104101c0d0038403000002c0c241101651107143c14800c0348441c1c2400d2031001d0104207494070410201d840c0107507003503c0c44a50001502c8100d6458800884043e044024160980e1b04450082c5107560364000256200e00000c0d41c079402c4c10b0010340b000900c2e205014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 33042424 1250 33041174 33041189
    0x7021003090203060c07050c0303040b07030801060e150703030b0a0f06020c041e0b010215070504060801080a052508030f030a0606080907060e150a0f1112160302010209030f010f0501 80
    0x19240c1c1c40140c0b800b14904d83d01507180c0c00059260702031030826504210030a0f6070b1541c9070000103008950601c17500054034155010342d03a8400711382c2c1c0340c400c1925a09040c56109a002c4181303c5101443c000e0180108040e611905d130100b03890301910081341e50229103401c0b400704031006441c01d102c2e00b541004131005041c01120140455103040001c00c031284110084044400e8036040e545899074000c0020000082c01000c9444051910480c02841e0b03810a008035400203003a200001000c640004010001a03004409040d048802c80c0242e14035502403000c001042022010000305414240007800307021040c0e0340c0d030301d60768900404c02004890703107500a002440008001d001554000103180400d0b1007036410716248010890001a140769160501e4a120400014244480701e0348080014001c0d000307a12282407a0301059141900c1c2d141100081c108039405000c45049a01c8502d400000c06000c0e00006180c2880600460708040c0c1c0415001031980d101e462071280faa0540c41003d0044c10706 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 33043674 1250 33042424 33042431
    0x40f0e10110f04140a0e010e09010c090602100906180b040c05010f02030409021305090103050c09010501020105130f02060405030a0c170102090f0f0a0905090717011817120a0207021003 81
    0x414403007102e409903003d0303410f00f41c00744100e00403180c82e14014100940340b1141001450360f50351502406280b8211a903144550800d41c400c0d503400d00440c3c122090300e00640140010f03800308a040c0c1c0003466544000c1c2d941c0ca480ea103c451508440200c1129851701904100805140909150800358003d92040e4100310141e9410114a0380c04416074054a22080d0096940c1c88500e01c40011655a42c00141c5d110300800000001c00000180c0341a811005407007481d1260f903030304016400c03540225054425604150540c800107500c1c000083c4046d40300030318080c201529031000c039182a049100845800c040340d0b005000010303002800e0349408550100035860070041d0000300d1507600380c080303640e40216582c1800f0602603680281880140075414010042460000049907503841d4601c501c0c244015450302401c0d0801040c041c070f00c425072141c0d01c1a14400001d65a0240e19904405110035004081c40009608420001110b000307080f0070602684401081c0104101c50240d5a82003007890725 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 33044924 1250 33043674 33043687
    0x30908070e0115031e021207210c090305010504050304030b090304030503120c1606020d0b010302040311210102070f030801050d051b0102030f07080301030b010e13060209040f0e1011 80
    0x400e010128151184042070704090074003583d090300034080403401444403081002c1d185044180b298060309401ca007000030402241c40c2e0030b0013030340d48070700e082d200d6207900100d03000c510002e03240d80c4c101050303010040c58a000c00ea5030700d0f115142140c0003920211025000003d0800a0001c07107201c40b0340100e109400f45107403900e0b55036015030300c7c80381d0700e40d0f1031042c001d541c00200a64410025030b00300e81912040e424071981c3d280340c15002584201d1f40750319030510f00403c030000f9511a100381c800350b0364485a09602510101c080260240b00300450040d00302d4254060f0800403804e001502040303100700c40c5824541e00c60314018150b100c05802950040381e80d1030048001c030303800181c01043e032501403040c0311500716246d0040b8214480c1c03d0010514100000e190000c02c5201802141240c0c022080504241d80300e0b0480340100405586900c5070140512040d804985140d008244901c0001c0c40000c000c021f680d0310000b46c60143c08400c1301608504010b41c04480d4900803010b481042c1103841303182c0352 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 33046174 1250 33044924 33044939
    0xc060c0303040b06040902060307030606020601060306030f0b040f02120c01030501090c0503070e010519020c030708030703050711010315060f080609130803061203030c0309010b0a0f0e1504020406020a03090807 92
    0x10040c400f401c0c1c60041404a50240c440d944400410354000d0140e9a03640351090002e4040c0140303224000c0144182e03c00010400d00c41c0c071415003940c0d0722440d040e200c90865107a1004c0c014010744161143c1d81c0c0707901c03800016501c040307140c045004160081c014500c60301c1700150403aa8140e01100d1450b0074a90010074a039401421294400801d05018104001c1140122058002c094140f1080e4442203c1081d00a8001802c00d0b407540080302218010358980028a0b180d000e544401404210103020b07040008100404d8854020010314001640802e8102c0b002102d000c141e10260128240302098201300f944014101c2d4044000d54001905081c04140031110000400300a45400c501001140b85555410a180d4449142000f1240c80c4d06081c030080e03109500a40d8129055071074214001d600d420300c44115002c4079090450301c5031940c42e0001c0c000580200030701e9160780b00410807050030302d40c0d00c520252000d0111540103102c20b504a04e009015070f100c54103c0c20040d40000010054071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 33047424 1250 33046174 33046177
    0x2d0906070210030609020c2d0d1d0d0308040506060d0206040506071713150c0302030901080901090506150a0b031302042c1f0e0703080a051c0203090c060c03 69
    0x45606940418880b030300c50204800411080d00181c0280d8000141107200c000001000c07500460a4000203810514183d0003248c20100550310032480d801030303000ca02016015100e0256404218003180c16013810000c001845805000001c40101e04104280030038060104541130f4803030307016941c00103d4641030300096420300443c4540ca100f01000034100003000043c1020a101000088001d52622410904010140c40314050500e6000851001c00c0c949480b510340c45640329007540217185001da5031001111001802010030074550340390b095480000d6804c00c1110b1103a102d200c1e40112003030150040001d8011240c0c08400c034000180b0622980003040e00301200100d40c121000924050604040d042040041159003895000359120803103c0a0200f038501c1003000001c03204181e290f1040e50c10080b2440c4016162541c5c2c000001800044c0b40400186900384080c01c260341003000120481c40d20018010003184aa6000300912003141c0d0100805407200c08100c401c20b00307080f0014000d5650303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 33048674 1250 33047424 33047437
    0x5030d05070f091710021303020103050c07030905040504140a1a1311040b0f090703050405060a0e0a030e150a0e19080607050d1508010c0806010e010903060f02040801022d0906 77
    0x2211400036030700410303408001c110b00328a01740d0001e64507014551a00581440c0d1484240c8c0403d0408000480e02400d10044840300c590586803c0d01044c1010280002020010710485202c000c100212342d089408000c0002258400c1c20410110182c207025240703240300280c110701d07840700380b07558020004024031b0492900b0b503401e43d40000c081e0030a82c006601844c0a0102503001102002441025603064101c01d100301d005d0011500280c645142080488048903085c5c0c425401189148001034841d926680318000001c0007100c43e010002150103040e408940c600010401e00c0f2240390160070800007a00d55164040c4004200b180b40407000c0c0e444a01c003c0807802045000201d1131a589074550059814141040d441c1800c140c440c00580d0003001d60070000c0c0042140000003e03c10b40c41344400040c4200183c2d1203c801620716500c1e100a4903024028010098090002042800003403000d010b0310b10021014a100004210000812490a002c484c040c54030402c400031064030b462048501 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 33049924 1250 33048674 33048689
    0x503030d0b03030409020a050a03060605190804020409060203090106080c0312041503020f0415120522030201060e0916081506120f01060306050108070603020309120c120705030d05070f09 82
    0x4410340341c04002421403065401864490380702050b400710981d440f0010301a84180380d00c0800070f0340c0e22850191494007540f845c4050309021244408207242c4265290f0760494806007010038190010342c0d40b041680c004507074102c90303030b0b41d40c6c2800c001c80ca06c204103c0e10082800d40290180820162500c11988140d004000018207003440795506d60384070f5030440f6541e4100d01c2120380c44544404403c039140a501d9403c1000a0003918507030f00311202ea100d4603000e00103090380183c05001504a0851a1407900c4050f41595a6864000b4407861991400e61117401d506c005004110000c520344075000c00290404456644070040310f0750415080c080c0d260f08000100c0d580700080c10401086850034004a91421403942010300c00410848650446416107042900b0342d100c19440b40e00850032408102c0700740c040c40d030000205100c04003a4000421000c00f00b807007030314540d001c03e00030010164403c0d542114180e200051407907880c01c0c284103ea802c03004c0383c40e002e007225030304000c002c1000301c40380503021 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 33051174 1250 33049924 33049931
    0x804060c051c020606090105040b010905010f120e0f0f07030f02011209060c0c02040b010c0201050304170705060103030503041e1a070509030708030403050606040203010b07121214040201030e06010503030d 90
    0x6000080009094822062030051040c40d0b80d0724000751607810942c0c820b801030807040004981490940604800c800040e5141112070b49080011100d240554902d8424440c4007500484415402e01600c48140e110800401c03c250321804900e19101a1640c0d080ba641c0056206000090306482c00100c843d40918000c002c2c05000141200203054456000f8040752500c0e10075a40d203500103086a02c40d41c000c03541008000640b40c01590000c0c0c86002c0240015801c000040008503850310103000c1090300040301d03041003d240d071100d103064801c0e00b080c0e0118a02004001c01c0100034155442c072012014120a0750000541e1400f40620002c0344910341005680001803080e80300d101990000c58008040310500c55072607251603101c0d849400103890138040c4c400000c9807420030703008481c12201c905005d030b840c5c00c3e100d8987c5518000d0b40b4120300c0810401000820034590341d802034003040103800001c081207003064800541112915562071170241c218000411032981d0200a4507003031000e000010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 33052424 1250 33051174 33051197
    0x14060a051b0327010b030601081606140c0d120f020a0813020325030b1b04060c111003022805030c07061401090501180b0d1403070b0a1a0d080406 64
    0x7181400510035241040c1080140d40300307103203441504601c940c5e400035410344007146d8a0380d031120b450303000840c090741c032400740d6440400a940c4142003075052074a8049a840c2808440184142890b079079044100000c0c21102080306100c1d00740c41a1040284030721811850074145050280803540024025078a0000e05207482d01951070500408400340b049420410b280c1142900e45040b200c41c41c001611801c828a000441d58402d20016031000280120307420304051800703800b240c1c42c21283d04100c90344076030700b1034007a000d8507070607807544209545840150301d9070256459214802d00001142d0000010010104079058000c02160f0308a1100f810342a92480241480d00203040c1074003801c8501c003000d00000841e65010b0307101c903040c0d809140303000710300c404104010341c142c40e407041e12940e005050740415800074500c02c92014850b03000c0d2060364280f580c41c5d210084070080444040080c0d50302d1b00c206001c11030382e40c42d451071040390464500622103034a4441c1c5c00140124040e041c24800c0e1450213 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 33053674 1250 33052424 33052441
    0x16030c020d06141902090a0b09060403240c020105100e10080f06041b0e0a05041401020a0f02010f0c1d1c0501090501110307120c0302040f0314060a051b03 68
    0x44200785801c81400d01c0051a0702c030141421070800c9a21007051084610540700c1c005450080360300b2010000c100c0e1807400d0411902140e2940400d040360b501c94410080000050300c0c0c0041031003031098101800078210900200f51040d540040c81503c216494a001c20008901042c2d903d420f9606c08900c501140d520400c0841d02d011031a00f00401034410b001e002c2230880000600703140704074400c4801c106140145003440840c0041401100c165860810006110409582c406944030f4094050039141410b0075451908982c00408044001415030042103031103502400b50001d061a0050200803403d18014000c0186003280c4d4509244190004199041d50710b500b203500001010900c90325000384c0605d0898024201e49404a54650030a000b036284a04201e0a680c81512130380c0350184190540f9240d075008240042450052581c240404155036891741403e4028510a8501d0680d064085100ba4588007006003138008050170a002c0000880c002c1e1b00d01c000201910701c0c1180c490702c400300c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 33054924 1250 33053674 33053689
    0x2403060b070b01050a05030a030207060507020a0302120f01360609020901061806050901050306010807090e07030e01050901020f19050d020d0207030e0d020105160302070506040f060807020316030c02 87
    0x1082a0840c04640308051001412265040300d80844d10036480d255214180350701e480c280000980035030040801004140d003e00018014548000c0c10b0322043c035142c2c5d00103190040d0320361108100351f10095040380c08010901c5240c003480b005000c81c4115444124555040d0520810580e084040480524042004a401c02e4007260b41c02041ea000a41e142c0d400206070030807480c0c001034880e100d1600003030130070700030812105140d4041c0c0d40c1600e55a1080c0040d108240098103400401c44444130000e13a90b92442c14441c0240c98994001c9901551400c0442c00d440e4090000f04a60744100440401000f202003120401c07640300f0301c01c1040302003030401602d075806a01c2c0da032064140001052005950a50f00404034280700e51251200c0781000740505c02d8481c408030000340499801c000d4070110303d14529401182030303c6031040b1150f01e915400842c1840c1c0095202c44101808080c2c144403168001503242da010303046100850505c924440c0a0f09110801c0502800307200c4514941015915441d6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 33056174 1250 33054924 33054929
    0xc0b07050f010f0504020112020301030c090b1f03020a020f0601080a060e120a030605011d01090302090a060803130f06020610060302161a01050120100b030a020901030f05060c04240306 81
    0x3008101d50f5000d6030034200680412a0120b001698510106124403401d2081d28180c80d000440c141415003044943e800408440024079845070361100304000b4000b40350241c0c82d003000f441d03402584494a0110103403030445005502d1006400050043c86070319000245a031200e034103e070340840c0050b520803045007080b070450751230700116400148042200390181c1001040742c1c400ea0302d6015108200200440d1100928101c1d40005d800e01800c00c00740c9040760b80ca039080748003001c0001d8000d0381c410600c3d14581c810307983c4d103c520095100030813500c482088910014100c600140680d46881120b1040a11081c007030349090540c00314000c0d090314200328407a610a58465480b45004001c4e10307500e40207007024840c3c2030000c0c0c010100c12588261401008680054190040c03884029050081c406010031000b00c541600c00d034039029025035142000c09000b540282c805010074101d5007051400c110004003002e90141040004011031070304044c0001c4544036013108400d40100080c0106d000c3d12459 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 33057424 1250 33056174 33056203
    0x9030e04020a03140403090312051606090311031c200304120201090215071b050307171018050105010506090a140102070b0307121a010c0b070306082406010c0c0b0705 73
    0x203508002c00c151f00014440103132801a020010244a1035008440a210300ba051911a0400801c00e000060349500601925842400d201103400c201182d2035103103800120820741d1b072032610004540c104042c1d00c101d00306100526030b662504111030307505d0582844007510040c010007200b40b9034003681f0b10070350020582c0342d40245184181c4000390b610b0849a040714409407840200c00b0407007603902549041040407180082c01814600d0300e00300c1c9801d981e89010410389103d011710b00450701c51808030710912801060248002c60281d801d030400380c0c21144160000c3e40503030010000d030320069036207a040804892a14940c10b005030324441c0100d0801c1c0c143d40c003441403000c0c00710074001d03143e4000c200c01207008040d030820048010410781c50a02c02c104014860b01041c0c2c08004e02020806540c40d00d9070092007820045003044da103c0d401490007010103440c51004062442600c0003511498150307400c40402d1a00c22450304240c1c803840b80c11102c5110304c844081000540104104042c000e00c411400003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 33058674 1250 33057424 33057461
    0x40b0d0207050105060a03050c010f020f0708030417150609090118030905030d08010e0106080c0705070902040e0f06030c01050307030b040603050a0b1b12071704110f0409030e04020a03 81
    0x15080000294101c220200d9440d42480001801c505000f90000f04894100740200f560040060045d12058202a1a0380071801001c1c400120000100802801009000000d540c0c132450810f0341600d244070010274400c01c1d006070305185d0070a620b0718242c42d000001140c49101d10340324031800f90300420160581c2c81104926034003040a26400c6006001129000d80640b00c2d1040022005c60b8100c00034012071003800c400c6801800007a11a4010903400101e214601e45401030a489061511000c1d503c0308404540005040c40b460007018400c94200503503621440e100d0500740006a03e442904c251241009404400104024400c0d041020902c0016100304206070b260308249803901454a01078400001c074001040400c07850550950080c034418034010f081080c4a40081c8500c0c3c0d000e8045802c000c4c0c003903184c00c0d22424842c44580142e1140c912014601c0000d0148104c88405a24041c03065181c50030000200f50814501e00550004840050b59102001015401054a240102a034000c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 33059924 1250 33058674 33058687
    0x9030a060504050c0d1e11060f0307090e0402010c030c02010e040e0105090d110601060f0e04050f09010b041b1206030618050f0a1703040c080d05091801050f0d08040b 73
    0x20141d02640c0a180a2019141c0403c00340c020311400000c2090020800c0800c0340000c0d00d41e82d03120f000c0b010214461b88803004401d00d0000014501e8004202c6200c01441c0042480703841e54001c11480000d210801c2185070b64903150b000a400715082c54006070601030301c3c0101c001160300c607a062555040c8018010012a5550a00c0900900e021102d0f031100d0300c61003110f192028003541e04d140055241324001c0040780e0070a482190304600685900040c4201c0c15240d20080c2ea55001c2c0302d200c0e143d619810309040c0740100e4031a081d980c400f900d0354001d6260201c021802a064482076540200f6070903c44052081e42c4402d01c001e2240740d001038105803801080c681e6108a0140c03114107140a14100e81d4040c180c080301035180c9995600082140c0d207038031203403912401d011000d1035010703019103140d41c0076540c0c0b21010350a00c0300181800f000540000707140070041ca042c4803420090341450030700002a41c10840815110088c1081462007969103041a00c2007240700b4044030041c2a182d03c041d40c0f01c68 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 33061174 1250 33059924 33059933
    0x1308070b0417060c03190207020306040f1a0606180d0203010f02091305010e0105040c020f0105010602160902030c03011a0705030a05120901050f0a02090103020405040504120908031204030e0609030a 87
    0x1086405605240c0180790b5a00b030022a001508501030740030195182d140d91104890621400c00b001c0f20703003138825000d000d4240580c0c0c00b486011710640c0200260004000f85142c0305d00c01c03a501c21810408082d401041c816036032240016a06130a03000e801c01d1000c0500180054044a9a100000e6140d800c04041d2251038091390041c0002c400140c8845070f00401320208841560b4003400b5540d001141d84004000601c2d044d00302c0c100344507903401602ca950300b400d00b0346400e69900760080700140c2c0c010300722620791485400da520000c05c916401182981084022440b0070f10041c4142040030a11000414000c10600e04440c540c950100490340e036030300911000740c01900f098050390480c10f100d10020b80c1030401801140d00c180d030f18980060340f07582c805e00600d000b500721070122810154213200115068503203100c1d950050b4018070100d1003680851100170450049038000d5840c076001031011000c4001805010b0b50000d40c9402c1402c003030300011000c26000c1c0a0649002c1e81842204030310000c0c171 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 33062424 1250 33061174 33061177
    0x1413021801032f0d0b010206041a0c0702060d050118021305090705040f0e06011e0203030403080a060f1206110403050d0804020102031905030a0c030b03030702010e0a0302030f060a0b0103050606030c1308070b 91
    0x62032013607401e002004101d001680c45a004640c0035001030584890210300922100c0c1056101085601a0707042812640100f0090b400107078580004c15510b00042c0300b60180f000308460f045a800340e0070340ca403120308042000494014400c070b50140e48004085105d0038040c6090720080c0401d071f0003c1ca042d5030703a0340c104840c0880c1030702c440340458001c2900d4122601032081c16450350310030360001c501e551a6a40d085425007402440c421030595604d0307000c90882e80e10751046005043d849280c50101c100380c05c000d403c0340c103240110382080404020400000f90041a00d0300000c42c3da082c0f44d15941c1c0c60f03000503801e521442d480c5440f040680c40341d00700c989800c40302a50194064800c204a0007a03140404c0d403c8450000c04141d060f801800303140300543c4228900e00f100c90001e04001503c40e903a6010914040f084102a01c050b0488401c200c00b0354014821114030510910b000d00a03170501c0b40200710244805450f608142100188aa504c502003905280081242d0021150301990360030f49100c0d40e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 33063674 1250 33062424 33062437
    0x20d090812060303090108150109080d030603022803030507111804030e0d0302120d02040510020105220209010b0d0902090103080406090f0f0501050705161413021801032f 75
    0x80d03540389000306002c1d06001050318030783c3d1030685070b01006446081a0003d005141040c050412150b00b0010a80000500030300d40c0c2c0900c181c5000c6242420340c810007481d543c040c005084c2c05030b00228650900d035900c491b100101c3c2d401d810019a03c0140d4280301c01c68100300e45800350082000c0c54507556002c030b9020518402c0c0d02954817003040b03c100a00308010129a614083c0040c0e0004001015031540300e8001d00c0d041ca8a05001850302c1c0d03982c0049103500f0f1041c024000540d56850821044d0808040000322410580350a080021140d5000030300890060103943c4513030360080b842c4000032250750702094106400402110041da5a45003840c034503030240c0280000501800740c001100d05c00c0c0e000c990199101c00e072840f0082401c01004466035008442d0640c2c0314030985011303400c040701c0303150b05201400c1002510250313414202d05000300a0328280b84504010720404c2001526011070b80200340b180400d207408113404a03502030b000d405412641e0b40760b0010072420400301200b5880d40041c00e1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 33064924 1250 33063674 33063697
    0x207050a060b01110a06150503010e030903070f060206070c06020d05090703030315050f06030402030a0c1e0b0307120b030c030d080a061530051305060105030102031315020d0908 78
    0x4104481c0044801c0b80d68101001c94a0b1701c006031240008109401501070130aa0a1108817030981d46c0000900303643c0582120915600001000741c02410107200e144040d04014030aa0540b40c904203000703568180091141c030070840c2880e229030411142c0d404540e403514003103000780518182140c402d9242c000c244011008207182140c030b8198014841610700c100da0700200100c001c5606c54040c015142e00c01030040360305000d61640480043d03103c1e5010000341c21000e0f41d0848405c1001c4000c0014500c036001221000c1040c8100903503258011140d041d40d80142a01040c541c412101003031500d000404a6035060254241c5440b81d80d03404100f2501c1a90741d91002d218207070707850128006243c1000141c800040c03104950224261380ca4100c0b02e692903600c0104e90100c50004034100c115641607400e43e80003808000e014040c0401081968090001240218a18202229000041c0c0395801c40107011031044240e0814138522541955054811040c040c409580c0c10701c0c050115600500c20f840 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 33066174 1250 33064924 33064931
    0x7120e0a05090c09010c050a0506090601030b1b031302180106050a120c0e060a021005270c030705120c06030711061305031c18050f01060803030402030a11130207050a06 74
    0x1d864941038104500803500e40403020702c1e00220340011038400a44510907105445010074100004500b000494452011500640070b03a504601e0b195101410151030442981354094061088040c8503080f030750402301c000c5001170525002d102040e21000850004540b240d04e441c00020b00d150400014240070b40301c0d5440c42100051540d0040445600211039400641f42c03150008250509400800340441c20f801100c4e511203c0542d40e0042d60310898908891324141c004034411030710a255501a100c00d6000a0f0000c0342c02c44001c030780d40360b189101c2c80b441030480f124400300e07254050010b8406014041d00311a40d0b450f00b07440160100740c1d50b40c00800c061003150001429620480407646403160b10101841c83e00301030350600d407052942c1080b4510000c0d52050f0044080854040e4007604910031000740040881c0d00c505031382140c1140c1d00068103504100704100043c0d4001c21a2200664040400d03a030f14001d01001c25098158010314514080c40054540d060040002d82090058031400051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 33067424 1250 33066174 33066179
    0x50a0f0207031703040c030c0906050f0102010c0807050313051b0a06170402010c020a0b0a0c02010905040902010207030b0414030403080d0501050d030c170913050a060f1d0a0207120e0a 81
    0x881e55200240300140400d980d00140e060014140c07801103030028001d955649584c2e40340c1d15008040c3c0001c0c0d01548100c0d617145010840f80c10002c2d450340700760000340000c0080e14078415001c0e0600d20010210340410400000107804818074100304940c02c0d03040300403288220114160b45826201800c06035114000101c03000030f42c070f84100c080e10f00c480c0e40050b6401042e00c2d01d500560341d80d0318642d402c84c0c0c4043c1402c0c011445c0684440a0706202c20941d98020300341010740005020001d243d00410700850801d6810800340c0d030000742d604112544001c8001050f503071810503000303604800024107040d020018001090019981c00703000d07180000c41080240ba40d86e04208203c00311000e20041c003181406100c0800702d01042201e0a200790441140f42c030b00301d0342000145400382c8141004c1540ba0b950340078002401114841c540c094071f0246100d86115003801c508002002503101400240b4240c1da001500600107901900c488a43c01a040015403901c0700c03000d01841c0e01c1d988628000c02e00d13113000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 33068674 1250 33067424 33067427
    0x105060a0f030302030a180e040f030e0301020c0304030f0c030c0b0a14040e01091503060c110105090d020604080a020c09040c0303110a02061603050f0309070e090c060a0e011e050a0f 80
    0x1d40c030440364560000c600c0c002c5151400e40d80c2031320011079041100148030000600310899802540b10703d02c6920700d14100449854081c8c410301d02c0e80d200c0f501980c414011002000000400c480541e034100c2c0308522400130b6860030040300b10f003d820040214034800d800040c12460900940513101c500d84a400e2102102169600d01c1c0c011840740d001c100900c0d2004114401a40d41700702c0b400070f01700170000d148a4032a201c0d802034400402d040300000741030140501844600381301303082c1c201c9075600180c184980e40303000081d903d1030050000703041300400080607030000d4001c00c50075410a002601c0748810b49401d04082419014505c070960100328034000949054001050b5620300300e900410241c101190010014000044204100e0600c0b41c10042d0014950140d07001d94422003020005000103801c1111200100c40003804010b029404000c0b10f800c182d40d070a0954401e001940f800e4403441480130300480c1d242d90149100080d05280d04002035840d90300070014910300956407030350110701074412130 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 33069924 1250 33068674 33068699
    0x1721090d170403020102070c0605030601020d0302040b0708090310090501021b0c1311091201091e0f0b07351012060c02031e04091a06070b060102010e0f0105060a 71
    0x300c0100292006040a010107115441140c015003c0c1c07000608001060741c40b694200425000b50001c1000030003005069a810003128590b042186400d5007020300c0e10351441d00f14080c400d0f004010328008642024161010481500359681d01c0506214420341e07400d04074009d500084c0740e00c410002501d042c000070040024900c4060718060315020095100760074800c001c10074210090382c4544100000005542c480c042056031302030901c000601d000a03440c0c1080384402c4a480c111030200d0800c0f00e0743c00706403606481c40e10f0319048500c0c14403e6a42020803034000541c5203104074203040450781e1148200105124013020411510b83c0303030a50300c803440008000d45c0c540c890f016400700110041d1f00090304641110f401c80c4800c0c0120b038107241c0c0c4c00c00010b010a030403c0c1c1810a618000c1410420101356003d0a4107600014040d011a840d1600c0400c1c1d180c4120113014140201c1c003000b24500364030035804030381100c02050030b440510400116050182078155030052159400c500701003618030b40c410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 33071174 1250 33069924 33069943
    0x9050a05030c2b0305030f010f29070206030c070b0108120a05071a01080a0c05040506060403060c140301090b09010503010c02030412030e0a0303050903011a1309172109 74
    0x900800359601200700f042a05140024003030905914508481c0c403580300c0c3c2d220118014401c0d01c8682d2649016404130380c541d041680701c080340e500301110801c411081154610295080044940c1c84911040311038007482c440c021000750440c0b03000080041c080c82c1100030b00446803190704400800d0340d90b28000d41d940c4092400c03203c0c013000c08001e00d03ea454000c100802095200d40d094680001d8007445103d2510401da216103001d41111092400b008103820307080f0041c1404032010001d90508c3d40c0803607114041c074080140000d9130b40d500114020700031400e0400e500c80103a41181d607580c5442210001d4402e505040d0b01520398800040307550b24040c0681c806441c1c00d540258102441c200c0000c080c680c00d44816000e01c40104010900e544440a050001e503009440b4035590b82c075007070706040c00c45001c00c0da4182c400c022104492003e40e580103204202c81a00040070030501c03100d007800d901c56020f80c0f804800140340018035081040c51000207690302c11149a90743d40540c1c5001d00d550b2500860f2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 33072424 1250 33071174 33071179
    0xb03150a0f0b090d0602040806091005011d1e01031101020706030902090a051902030403051803030913020d02160b070305010b070f0803071403090c120703050705040e032809050a05 79
    0x1000a004160050018001400c0001e114a01c404c0b101e031500c404030b81c801d400c5200303da0492030800005100c02c000304071001259110411456160000b1000c8101003028181e1f24240410046403140180003404d0324007142580c00c0809559503440c050400d0030443d00c405015024928000a400340244110800541c002c0c0c041200c0f07944540e041d200410004111400401e11888018030003510351001c1c6118030b1107902c4080d81c801050349003003c9044440c05282c440d80c810044480c1035243c01d2844407149107030030030268a072030480701060082e004200100c902e81c118240d0b490248006000718074000c001d2a01d041203241d072200c8540409110341c0c50042c20190400a101001800d280011a4020090f18100840c40c100f510300d040d40c0c0d80107803040b01d0a644000380807200ea00d44039507400c024946a000800045140d0f9550540b95991440344912499450008800400003802107030046031f2041030a028045440022450311501134203054002000e00da0301140f90f007040c02d100700680c1c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 33073674 1250 33072424 33072449
    0x907061e02030c0a030507020405060609010e040509010608030a02060103060b03030705030a0c08070b0a0203040302010c0e0a03060905030702040c1806020c09010b031008031603021506010c030c0f0c0b03150a 91
    0x3a000c6000c082208051100441c44200550001a0010b00800400f20b21035a2082e80e01c580320b004000640e1806028a07114640822071414aa070b0407400400e5140382c1560080b1f9650394500304c20b4014119588101c909000000f51040643d0340400c4031740c140ca00c5080b04002d40c1044c1e50500d9601d00441340001d10540c41000000c0b950341c0903540200e00c25104020581c50800e00d681c039160000d04c03d40341280e8464000c428041007540a00030010000c090785000c1c00200c03c0c03000003503480c4226200107400341343d0750801e5400740142441110b21154000d84244076042508400404402101351441a5035504402c08a025480417440b0644040700520254485c0d0800310368201075440901b560f448121a5100010b030090140040c240c141100b501501200300305040107820820090301085201c0b482c501008550b03a0080ba01e0007005425140c031101c00c40f01880c013099034040d0048054041c00311098002240d03c1c8203c0254400c8200e20070807064004500309000d01c03950f4500031002006403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 33074924 1250 33073674 33073697
    0x50a0609050c0a180f030311010608030406050a0f030c20010e0105090708070602070807061b05011a010e150f03040807050604050d0906050309071401020102091c020f030d050706020307090905100806090706 90
    0x8620072307148280540c1c800018443d40d494940e1392650340b09512520104501281b1403082d66005128030384008440d0030140142c881c003040c02400044d80d103108600104002903400f004110952014204080040080140e07081a40030309507110034034480d105640c4a020340200d801403001c14403404584051005003c141e090032402d5641010035a030000104400c6148140070401c00d02a00c820710401c05202c1c4044807a86000401080c000a41c1502484c880e6000c400b42400c0c0c0c0040300c0c10a058950007a44a4903186050051752089100c06070407407255405000901c0400328400280a50b40c2e211011400e0f690007003903441e4001240d10000a400007007081064003801c580c92a4285c805100042c41c10315040d00151507505100810104842c601d4810411810100c02c0e460584030308500030480d03d283c42e40010150300c60480c00800c01500131011401e8240034103800d0010746003040c010b01c502c0c80d01076590915502d580c032070540740e8425840030801c1e994010410380141e45507903440c0c0c01c0921 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 33076174 1250 33074924 33074927
    0xa0f08030a090222050a09050a0b04020607020d06020901080f04050309010f120e01150501030207021e0105041206090303140136050c030106030b01091404050a0609050c0a180f0303 79
    0x300010039841c111600e5611500044e901c0786461018441e0050410115040703032146802215401018800501d00e89011080132a000141500e0a1580442042d820f0798440c80403d0385401070aa00075000005440d0f40c400700002a0054160b00200faa1352400c203903a01409903003496000c1e180034080790410010494954070070409141c0301c6811b418a06d0300503251803c186d08640b0780d001d16440c141d41d525100e2600501102011005010910b4103600b400d12507000680301403408441d141340c500040c044180e040c0d00a400390f0b8009c207851609000e0085090030402c01404401c8803c0b40040d1501052042003e402603205058804034000c8245001d034a010014a201c1600f02100b01d400d00c8841001d981c200d01d002e6188030b03190b5502d806489524212014003518810503445052004031041881040c120b0011768140b60021107003c2001d0b220010400001e0109800c621002d070709000030020f03200030010013070031001c1050b43c845650744c01621603524a400140584941da103582601080400d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 33077424 1250 33076174 33076177
    0x2070312020d110d0605010318051218040207030504080c09010e011404020c010606030b0a0603060b09010f0c02041b0e0402040305060103060e030d0903020c0901090b01021c050c1510080a0f08 84
    0x18404003400110b0310040b249000d000e40041400100d04d0341c0ba25014800c0756858010305200010100c0c0040b143c00700d9545158480c5400c200e451005140803030600ca45c80916100c10410404c007500855440e00c1600300108240d025000e540b076240300e0340525140318102150143d04031640113003100382a908217622107000074081480f0a601c0354091202e140d1080c1c0a20032000100140e44001400d2984101070291520007070780300b00d060501e8103000300900206034080751040c01091074210b04044940001b6a080400310340085d400c02e15003004460381d0150015134082510007502c0319410103a035082080213a1086000081c01c80c1c01c000010400a00581c2200030020381480a41303040903501c101321401c030b0703101001c141c0c0168424400300f0700701d06114003c0c9000d400c1501050140d0f0324050b001030b54810840203081140c0f109010f080401c1480344064440003c0d060096070780d0243c116411708122402035503a4040c0843c0800000341903440024481001c0340c2c04030bc12400c0340a191200400b9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 33078674 1250 33077424 33077437
    0x140603040f060e07091104032303030604180b100e01080102070203190f02060a02030a030b062502220b1f080a092907020607180b03041104060b18040207031202 70
    0x10f403188010119131440b89006102840200c1b00240b82c40d50b00d903080820028195103c58090b2069800d5048801e66000c070403294482010b0300c1c01b0450f00b282e0000c90284008100000c4c124040c040c040c41303038034078040fa030743c2045441c10081d9440d40c0c0d80318110303030f0708030701ca003000003981a44114041030601841c6420111241d000d030026004040198000c42c5c1e56a002482800040e0400910310403030b913805100e8590f10100940e80d460802500b540c01040c449086040d1010308078031284190119559007802045d070031108545034140900992106024081d41c4003a03610410f426a0500c81c200b45100d10b51101041560320340e800c81d2244001a002007a0b80d0384143e07513245402d410548400a003514040d0701404403001c0503c5d6141c007400c000d05040c4003074402d404011001058150300406008040203035807034840125a60344803440e00044802c0012245070300141401130002d64440f00340050001c80d14803800e01c060304014a82084101e00c0390b400001c0129101001a08150341130354041c29a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 33079924 1250 33078674 33078701
    0x303040305070f06080f040807110f060a020a2108060105030414030406050d050a090503040512070306060b07050d030e1f140c09030c010e09060111120a0207140603040f06 75
    0x581600c03078680e00e00380380701c81d040148150300000c000c00013258054101640701031030b204d02c1c07820b40c1401c1d69610001d10070041c0140080c0020f41050007075640d01281c1d0141c4001c01007040341c0d01c0b1250030002c0e4690392810000c0d90848028002c140c2c11a01803011401060700325680c003074131961520300541e00c64001400566061a604125004140301040100007411540e10f4072a110101402d16100f1f4a4000f000e2540d502d05004243d00003071800000c0c2c80544030215000d162681c0042c1b2030b50700d445040d0f44040d000b5420701d000020511903140042c00414002c3d02a18200f044a039810b40998940900c0c07400503074094481400c0020007040802e50030001002c01003480543d08a840c4840482615030306c0031050001800300360380c0740400100d17114003c01e081c038043d2400c8500004940c500e000700100d0500c40c0b000524035039403a085c011449400c00c480349154032240400e000035528699170080c1c6441c400b581482c2d604900d0f201c1c2c1924170071a03002c003110f401484292340d0721002c0c062503110f54a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 33081174 1250 33079924 33079927
    0x20a090e030d02040902030115020a0c0b030601030e010204150f050a0f050d1409010e0c0d020603010b030408190503160c05190305130305010e010c0e0a140a18020702030105070504060c110303 84
    0x100d42d441daa000410061040d810f003da00c030f50401e46860200b8408000c41d5081d9032084070404009002031407090220307841c0744101900c03070703407050010f801400b6240c01d030801d10351000401059400e41e40c0030030480401266904c41891520503002c0d01d003446407071000c13008150381030700c841d5140e44610f00411140c4210a13020031400070042104035845019102c00036181d4403003440c1c4030825010080461024011070f51500d60110701c1d000300f011071106008200c0d0303100c4000b0004040c42404422600c1000412110b6000c040746003100600301c0e001514403a05034180c100c50810300d24811090603402035000400f0340440c40c9045849000b91613420341c22014001e060016240f001c0c01d01c14101e0085004100102e0040300b910442800c440c0062045d00070f1007200c4403156125152a540c410582d45000e480c10740a01214001035442142c41e803090480c0c0c400001d034041040c4060700a085501c3c03080d4000c2c85191900c0307a0039184c9001e01c0c050a07000030440e8042c0b20110720f039180035040d080d1010301520f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 33082424 1250 33081174 33081187
    0x3190503091804021921061103040507030314030c0d090c0504060602030c06180307021905060318010b040e0303060105130e0907080f0c0a0311010201021615110304020a090e03 77
    0xa0742e1140c0701030303000042910080420065080648140d841244000b400c0c40e2464140303002d445460380e0f50b04039240b0024600700d03c40204043c50344150400c1c1540c0d01196164a041d00e441c640d0381d043d9000c101c000600c130400211300d807000032040d207021700b40103107005040001110385640200007101d030540343d1800074040042c040c1c41c0c40c800e50010740b07030650103160341e03a2074080503602d014400307404100c00744070324082200813410100a607561168125400110b106051412011280c800e8000c1d40d800030000080c02030111620302060712490715000240003052400c01000304072241e6402d4501c094108000040d0b0030f40c40b901c0200034501c2040e0107202c01586904030004c405a045403121482c1d4003c010038804010200318625030104443d0091079501c40c00004641075071040c2c0310040c2048240700040c0103580c000e4069810340070b03440e0b0402d001c0408a013003080c6011112089031040c1032400c0c20322170300709862000301c03842240c003d827620801078034000c00c1c80d0040c044ea01412030b0600041c00311 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 33083674 1250 33082424 33082429
    0x3020f13030507080f0a0f0308070915080103020a12020901030209060a0305070308030402030606101728140709062c0907030b011d010c0b060f040c0507050106090b0319050309 77
    0x36005140160700038420b01c0d0070b00089070314201e603001044440e90f201e0888100000e40080c115925140c1c5468000099140c800080e40d83d62890380102c2020101d0310004c0d01c0040d44018881d040b24001c40790f183c0d00030340c0c9050506c011508840080e4001ea0342000510260030a101c00315003041c005400302500917902d856490406810f5001220008400014081940390800116811031012554410080009440a0a02c02045101460f0204d0036000034110044050114240101d42105400202000d950000003088a08540300c03803100c444020400343c0340310712991810b50b407050f12517003880c1469400c100e0303001048042200c10b40385001c1d042c0c1416201e803c600350007406182c0b00030900140c40b100140a0792050a00080b2200645500218903a408405004042c0d080350061074192101c0d804242054100c1103040d0b0850b0030004030608459000000b8604280210004c0002a84402d01002a2100410750645c16400080c50084804011400080b52846402180e01e0850100301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 33084924 1250 33083674 33083707
    0x3090807030302060604060b0c03030a1802040c081b0c030f09040608010c050c0105060102061306050405010b060f1804020301060e12030403230c10091401180f050312070206070303020f 81
    0x400c0b001038020000740b14150031710b8040c0c40042d0882035a41401d003030000400c950740303000007050f249955407210242c2e00da078550f4145511020b50080c1092100821060002d010100c054403e0031a42045510b10f18224280d00c06545035001d480c4061450301104488540b05030704100c45407680b042da0b50000081c140000d200e20b949104c00303902d0390360712040d9981c005800c4400c0241103078150340144080000c8804803049400d41c00d944072600080b20f890301c0c24142d00410b01c611040d07400000005c4c01c040d1000c2c151b070181100c0c0312074801400384c0349451018402030380020310620340450700d08010030070b0a250400070a0b40c1801c6e00c504903030a041e43d03515588610305d40300d0810b40140c00c0c81d448014801d807051001310070301c840c241c583d4111400d00401c01072190045211b040305e5a510448400341d1603114050505c001d401c1121503038041510f0f03649113803880d0a544202071280c802c15102450350380c0c0a1054072645500100401d0600300140c40075406540600c8105c0300d001c0d0100720070000c05140c0380 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 33086174 1250 33084924 33084929
    0xf010f08131a0f07020d05030103020f0402070f0203060f090709061401050a231803032b0204080312010807151d010507080705010902090a140c0705030f04080f070b0a0807030903090807 81
    0x243d404242001d1302c001c1c2c2040401350650040143c10001440580c0b500c0001040101c030a0718016541c68003400c20b58580c880c94079000394580245402d0050f002403881c045801130b0085010781d0051540c440c030b900c045401500c252026400c44401e5425030358050805040c1007030650504c1789100c40031464410b803039802c0000c0700040480111345420400b04100c1c0c0c28031030050640045103810441c0502001c0040700c559881640c20064800b859158280d03010707200104482d00c1240d803035034400b480f40c0424007000d010714402481003200018003d6018403500d10220102c0d02c0344045040d6000640d800b4481e4421400d040c13100070060f400008402000038104d007400f81000080700d1000b071040001054001c1c150b41c00305400c00e280c0400222022141c10781010703202c620300ea981c1c045883e20074118011850300001000005c50f00044884c0c0100d5800d6942d03c10a06544125840741005021405401803010000b0104400644000c0c003992000f5101c0d402801c0101006039203820039450000d864 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 33087424 1250 33086174 33086191
    0x40e060c0a050714070801050a02040e061210060902120603120d020a020a0c120b070207180b03070e04050a05060105010f05070201080402030a0210030c03150602062d0708060f010f08131a 82
    0x5d441c1085081d00a05c1400c0c2c00c1810320106628091920010549001b4060402403090790240c504000c10b5034100411a200168103206000d11903507444090000c2d04001409050b00445a0005449140c00b091115254850f03549181c04d00203480540c0300250000d0310382e00b0951203039281300c0d4082190a111180241a64090003000d0241840e141d5407841c40901000255880035200340702e000c21200c440701500d00450710004100c1d041e0780000c1d02d800341342d03404030050240702d01c140824008040b6501d40340a002d00116200d1ba66500300448030381440e14509000640207101d9100198403581306d19400600041c02c540c581a03150300091040c09100e240390000c00d0b581d142100034960180940b0b403d5944900c00c02c04500e00d003042c040d441d18001401e00300030107100d01e0400386512103000c0c2c5d41c20b40112841c590043d031800c03440c05041c100741900c120340b15031043d81d048201584a00c034104403031181d030350b00d40800d9151188841e80c84c1c07424500840d00c0c0314406098002c1c030350814400512500d402c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 33088674 1250 33087424 33087433
    0x6020d090201020c0906090c0d02041509051503060a05040b0d050d08070905060c120a09080102040b0909060910061b02090901090309050603040b060f01090503030a09030c05040e060c0a050714 84
    0x4520000e45400641130b8070314001d41d0711104114440d511441900d0b4080714003510a80d68420540480000b407185402c201b4042c004c20300c1440403550720000c0e06050310000d80e1452004004001c0541c0540000c0b00c507a0307031016440b10180712034241600704060940c0701414100181c3c45590f2000d050a01c68940500003480001c1080300040d4880e401400410007034038164607220346070384c2c001d483c0c9039040d4126203024400961200b0349441040a040140740c182c001311344a507101c04582038194400e80b03071144124540000310340300385440740c1014041d0164100c000903072450403d084d10389c46909002d500100c00ca458109001d40c491180c4071344100c801390000501a003003481e010380240506e03042180a5901442080f000618544030a50040d8007100d880e840d1140f00c10048a1441d503d4201d660140000302c0d400c111580c000d1510800e8034461040e40300e2098940d4103000c2120359800b03948095520520108200604402c0180f2400c01c01e031130040e10300000c2d0b0703c48040c80e010714030304400c00c0e03400f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 33089924 1250 33088674 33088691
    0x302060d140f060406060c02090406020901140c060a0b0411090d030201020405040204082404050d08190204150305090d0f030b0402090301050106051e0a08041101090305060907090e061e090a06020d 86
    0x138148a40009424a0300380b00000e82c00603004109000001840180b0705580003960000d107a01499143c29104030f6650085d5031f03602c40c4010300341c0700d03441950950912412305d10040300034942030083c012003030720030a07025060901c0d03070302000318140c003000c81075013555030810002c01e02e512039000901c050f0a4004c01000300d402581100c1d64044a41049240d1100e5288184030008002084003600c000407468440c8c069140d041d010019244d582440040140c400030300000c0003185101210f43c0c1400f2910f04004659481c88003d440300203a0f8114000515410340f824200e40c060381c0001150301c0d0180005040004e0309005c64210b500c2030300708101094021a504642000882c121604507604500c03e0307082001d000000340180750090401040101c803114161026440390580304011500101161000d050880000751207203003d0058517030160400c0e040b04d085000c0019018015818800c9a1a6680c41105112035500300500505ea442c021130108002155050000d84101da9291400044606 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 33091174 1250 33089924 33089929
    0x60d02040e0109060f0e070504050409031d010918020f070204091b0b0412170705010c180f1d04030c0f03031a04150501030c020c120606030f1203010302060d140f06 72
    0x24164090f441050500e0000e2000134140b00e0f50720221802e4525000964031005400c1d01c0314011600300310b42051601d60a80145540000148000c03c00300c0d11074108200180700444011005024050f101a217200c4143c080103220b82c000d003171440c2103000301d40c00d20f40035900050541f00c00a030f0685500f0901c5143c0c140010791201c941c0010a003240343c091030075142002800005a588002814682d01c40c69400c208030941c0c0c0c12107100c1d580c050000c0109404481c00540b0080c4442907941c9a811001804200395144030f201000ba20000001d241d4904042030000c0004000200100d0070071041c403503440005402d40100c5019540b180d240440c10010b00c0080d1105500a600c18070300c190305001c5c044244407a440a40000d41d0380a10340818032281c002d006174075100044d00311365048116070860001d40540426141c2c0215011000d407090000d0400f800c46d07440009102004104804200400040c9003000040c0506a0311030408904070346001d00c0314181c0704040761241000040001000200d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 33092424 1250 33091174 33091199
    0xb040c0602010c09080703060b04061e080c06160b04030212070303140a0b060d0504030908192003070b0904060e010e07023702040b0a0b0a17040206030a1a060d0204 72
    0x91032480c0c500c401c0385c40c1c61a480e68078082440082c00b400d65560b00c00344a43c9554000c4070261944501d8080701c440701036000002d9518911031401240925212200030b0f140c50421200c0002c014011034103441055250b924111070080c00071429840740c4a600845011003c0280c003040307000b9140040c4060246440060b8410001c0989003018070706580b03101c01d5070300c1e05c0a664030a080c65000003060303901c619055841a002d07400c43c44a030310034076040c00114079903c0c5881c0c28851103000e00344e0841c1034446482c00c2482c0401c01e0580d1541001e0310510010300c0f118040c103107002d4020000301340130340c3c0c2d03036207110b502a801c2e0080b424000d591000c0002c0d817601004289a581c501a800e900030044520420f00701c507403094076282124507001101c0c010343d40c658100307225000004100082259481d40c0408144d841044840c01280030040c03c0c80e452540e14007104d1107960090049807841e1342c0c40c9400d00080c8841020564000341c00802c0034507503121807010f0200242c007003a0040c1c0d00c80c03c00c607244108 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 33093530 1106 33092424 33092441
    0x6030c09150506040305031c0207020901030308061008010e0112060b06030c0a080c07080304020904080d140601030608010501050a030f050f0610030b06101d010207030b040c060201 79
    0x203503640c41034812001c02210880c440b541d41d010f01c21140901d2101a003590001d2010030040d030400700111135014240c0340c0041c0790514540c001107580750280c00980020380342d80300b00041410802c0221070051011300380500950325001c41044800d005026101c440e50110404000300f1040c2d800209101d800140724030340740d240c9200ca100094000748414000643d140000c90b10020f202c0b0103c5510396002035905185580f180c0038407840f110040c000704c0b013541f000c1003d0303000240c01d846020307500c0105043d9810181400d00c0010113a45250b04885100c1c3d24013001009a1ba8031810351000f2286c0c01b0400e000c10b00c0c10307810680c0c14031007040d2440000b400f5031b1041028070304c41410300d032058900c100302d00340c0140c07514024040303900e00c50420080801c0040000c0c0303c8910b101e404c0f40020300014070488503110340f43e0340d5150104105580484100072181424000300c5d80a0044801 = true := by decide +kernel

theorem cover : BRFrame.Cov 32913674 33093530 := by
  have h0 := BRFrame.cov_init 32913674
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32913674 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 32913674 ≤ n) (h2 : n < 33093530) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
