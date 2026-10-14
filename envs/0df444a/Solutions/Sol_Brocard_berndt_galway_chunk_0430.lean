-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0430
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:46:16.422923+00:00
-- url     : https://prove2.me/submissions/1e28b5d9-6d9b-4fbd-a0f4-5f005deef93c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 77158275 ≤ n < 77338131 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 77159525 1250 77158275 77158313
    0x604030318060507050306040e0105010518090a1205030901060609032a03020a06030b130504050703080c010605040f0f15060801050f0d0506040305030702060912041a16030201050105030106060921 86
    0x4404c0c0340c9001c000d00030b0b80090f100140624030781150b580c402c02051180906880c7d0042282100600001c41d0588001004100e003140d8001c040700440019071307008400c1440c40150301c403244c42c0d183c190310305402c454465010030300b04071315100d040002c00c16407500c400413240d007010100030001c420a0040c02800495200941082d12590700040d0607a1540c400388036140c0c2120741c907074241c010340c00500540b02c060720081c1103500044030810024038000010110400d01c40e0012510302d95803000241203508080110103001d44410400302c030040c0e288900d000b580500c0e0014011542402d030b0052801c0c0301400b07214055a051410402c2960314601a603003103550010131104e051038285402070081d00241c641d08094400d01c00420201c06000c15100180a00044401d0600386001c40088402024018418040c9010000030300b84449200c2c20b400503d001c4e07000440c055140a06240c21924554440b9080000c1108140540b154400b10500c105182400e44000c01e4180e0600b00380e280640c103940c80b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 77160775 1250 77159525 77159531
    0x1815031510210c090b040302090a051305060702060a06060315030602090109120614101503020306040e030a0c0b0705070c0e07050909011e050405040203150702120706050a0509030903060403031806 86
    0x214800c1e0090b0000c014548041d50390351080355841c0780305c00460140e400001d61248424001644480d81540304a030702100d030640d00c07101d00800d0b444590620100741c0340c05c0010b803c01e004003d84182e1a010302c8000341000c0c5000c100c0c0b1102502550740c0c403d018007000304140e40004800496a12a40c9244c0150419a000000184061400b2001499a040407a04420140340001d61224603510142c04541001200c1203880d0360300e00d4201c009500041401c1d41c815a5040c1604000c17a081028003103120b4180c8030107058801c6820300041c1d05000610190800400300100d0001404000e510401c458a00c10403a1494840b04405e072800c2c042c0042d003d4100d0820700000441c3c90492500c01801c1081242820000340c07500144003c0d1041100c01940560014400500202d040582c0c00e03440f0445205859141c0245c0784000c20031781c06600c0c2900c144d500c035014840840428841d05030040c1c0e03410f00441c07610301c52002290702c07034000401c041d040c103590303004000000e00c0e01400302a15640c441010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 77162025 1250 77160775 77160827
    0x61306020703050c01030b030703060f060306060602030a03060f080a1511030c070311070b030408030615031503010e03040324020c0d05180103110d0b01030f021815031510 75
    0x9545203682d110656092003803c0c6410040e501034424030041c0500580541000d40c01c58039200080d2040d41e10f08011030307036a030400001040e80751052401500180c0d010303564030440044014243c90745030b0018181c0c01c00e01c403001c10440303400240302450b1951024403411030b041c04c60800360080108101c4900074190000070011602c118400a10000c0e1003a00c1d0244102c00440d007403035a0f074440c3e0090740c0300454200040f80c08542c15002456000100a00083c5504001501c810f00ca4109840000e188a40d9102c60880b92400307000701649103010300b0095007003078070790b4454151000080203500803410046540c10301c48296a01291580c000d0741c0c00f1200d00030301c05480200694840c1c921008040c00200c03030450950301c01d00403501400794407485181040c0103514140000c061504c4260705144c0d40b501084140030041c00a0910184030f1800c1e01040c100e0f04003403000f194240303800051a400300b00100300c640504150340024aa8041d90b40c1d24207204500d0040c0c602d81d010125007000d20400b030081c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 77163275 1250 77162025 77162027
    0x80f15150d060b09011403070806133c020f09010509010207030507060207060e03011b030c020709060f0311030a030207030609020f04050f060301061d04061808030c03040219031e02061306 82
    0xd00c1c200b030b13080e83c0b1424200388844c0c0c030100320700055518800088001c0d010a20514048850400c41001c0903000600304c0e0a45040c5038014041030600c03803104d200002c0c90507003010100b0b01140c8282d070595040d403a0045003000710001e84503000c0601e040c0a070203c2c002d04240d1007080114065079008045400c41d68403100083c0d038500c0503119640c005030a49805d90000e05060040300355094a40c5c07904654a1742550040c1c02401038100ca0700118817500900080c0340e4001d002c1c210040010407408240f0f18194144800030300002c91155000c2d5009030044030000ea170000300a0201ca810030303000a0300300707500c9c40054507180c0e0501010358000d0616081c8480c1c0d000703200116000b0306080300200040e0780e030f45c09055004889000210240c401c1c43c0002070115010342c0014100955415680e2500000383d034581806420684100019460110801046052186202c8403c8034000d280e003101d14a16980c818000207084000f000b00720b0818060021501d424094030405040400c014500c1c80d00c42ca4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 77164525 1250 77163275 77163277
    0xc07050a090504062a030c0201150b070c05060412060b030118050d0207080601080304350a060b0a05062a0f0a02010909021801080907030b010e07080f15150d060b 71
    0x50a60303045150040d030716404182140c5030302414400350640c5c00280342c400820f4005044803039515066540701e207001d480d0343c00e4581c49135000d0244080c0701034840906042040115031a0b803c07842c0160000c10091151a0011364090101c40d40400041540301e0b94070007183c098503961007407440c440003a02040c0704008021911800b0f030780040e42122a040d0b912403140b540c9650030b1280d010030703070003c01051000341d00d011405000640c0c0c48010304414400c00c080c8044502c0c80509406081c0c101d000900b00304810b6006202c01030300f044810543d86170400001401e144108180481021441c1d2400c1068041c070304c03404501001c2c05419241001c0c1005940f41e1207a4200004034000381c1e0422000c580d5440c00e1003583c0d4107038003030010b00c00141c2808005517030009014182903a14400d001d000030004060584071400b070000c03030150389a5801d240318060080000540f0b180800303440310040041d10300003140000740c1c40408617200e002c21519802c001d4020320a40350000c0300e1a0510602144480b0090 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 77165775 1250 77164525 77164531
    0xd0e070b030906070201060e060609040b090703060e101505090d0f06023402010c050f030f0d05060f0d0209130204050406020301170307111504080f0703020a081f020c07050a0905 78
    0x202c243d44066440b05030807400ca40c801c1c024100016460b80200d00203042c172001904203000c01410002c1d06000510014050000c00c8541b000001d44462040c410300c0881300380c10f50800100d2842d001d4003400d160042e0300e0640038001c04070401002051035940e580e2072a004100c140d802c8001c202c403141a0342007010181d400015041c0b481009071000c041c20007a403c40c4c48168500152080080f0310039540110743c0c0354504003082c1c1d402e03c5003a8280744601c0c81440140603c4400e90101c0e82d807102d4200007482503c0f0000c0080380b03d25111180199540c4844043c039242e99412101c1c50440c1e510820102c410030890100a50081e1410b17080004010480e4000e505031000540c40c0342506000b40d0600756248204000100b00000b50b8820301442d0504181031028840401c2e04a0709207a01ca862041c50012850122015603104100400c00d44c240b0f940f802c8041d00c00407000d0403607041140c007650004001d40f0081038182e540000c41a00310f9000303010480c081c04e8002c081e02d80d107036a07039171805014040075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 77167025 1250 77165775 77165791
    0x1014180a06020d0903120302041d150604030b0406200c0102041406090a0b0702131b0908011b08060307030b070503040b0c0403020d02060304210504060908030f0702060d0e070b03 78
    0x200350125015000003a910150640c0382e803007500d041d056964140c0c15144442d4a43e082c140c00b44404185650400c5d1900d40e0140c084c00845d01d0ba25007900c14204070345a5141c9a030055600f08000d0000c15510098554855000b03030020401d010100e0204000c40700b030400c80e00c40c4802c04260201c5080040d00108210350560310000c00007480641042054454501025403091034103800700050711071640a003070711500040000417070852841405080d00c0301c9009002072441c1c408413810069411107511006403581d20000c0080128000400746031040c40001507090003d08000160785581c10000d10014690000c40e545043c20911f074050115001950b080310300410b0100007030702c0c41001a00b60f41c12260000c240301c440702015020300202d948044c2083e1000380d028050390700002e5000d84c0c0c1c02c2407440d066890b59a2a441d0200040c004034407508407810300e81040101c0c0425190440a50700c070f5540444100c0e50790300e54420b6100040c01c60704682900d0380180c0d0400510b508840303002d18400c20701 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 77168275 1250 77167025 77167039
    0x602070303110309010e15090604030c0302091302030705010c0807150501060f05090603040f060e12040602010b03061303110304080d02070f06020c030607050d061d10050907050306101418 82
    0x2d80eaa655107a0054114003800244414400a0245803818031550f41c40840e40d181c0340f912558401159041e8020341045c1e60842c03e0920810460800008071944050500410341e500c40c00d6500090b1142400c1c82030302d0420015100040178072003c0300c1261400c40c0c2c40301400000391403060921010b44024030610f0045500e803141500054051000c40300d08445c004d00c55403640d81c480c1e6a220205505440503128156924003003030980904010032004200b9900809840d40c0c9482e03402825211000c4a050080d0403440c1842000d082c3c030090b0300301150f03242c1009074000d000042058558040c651200505100c0c4288030440d50b034010841000b80c1d9220340c07052028641710301060f66500252803100b83c060384a240000c00941c410001740c101c04000ea0380210f2020342e0740c01940c5c00004d6072044a02407407000403e101e41c4804114440006000942d1200300c0c1340b50508000e40701d4003008185600a4050200d19200315124800d08009407540803900c80d1a0321000c40d4480002d002c0e21041401244 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 77169525 1250 77168275 77168297
    0x20909040c15051201060807090b0d050118060807030204020702060f041202091602060a09020a0f08031201090507091403010b0901080c030706050f041206090606060c110405010e07030e07030506010602070303 91
    0x4030800c00c8403004200c2c48004113041e442e10800b2108020300078010410088200c402051404804000b003410760b44900021480e07506100341201c0040ca90641121254a810f40c04c200c80350002c986e0108613a0111001070300d80c1100e001280082c441e801c00b10070000b030002804941c030700d03095000240f01d038000e80c1d00d005280e0307448003c065604600140e50300940d0004000900611180c2c1004c59042e01c00742040c500c141d42c0b1080c0b0544a5400d806ca0203880c1c0010580c21041c042040009004051468050120b418034030300281c00c40a481c0250704a440a201c0d081010742c81c2500040700201e00504010605e41e901c0c1c10300f0341c507907840154271846401010000101a441042a13500405040303500c60b103042c1c43c001d04000f1402c610101191002d40b03502401d008aa424460b02004096035146c031038400340580381024035100c00c00c24080c410361505006100c40320b59109060761110301c0f8140001e81c410041c044031710f44000b80d44028030510a0f000042050303640460310200302d910035290000800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 77170775 1250 77169525 77169527
    0x200c01061d01060f0203030f0105040b01180609080c100c020114090603181b0906062d0c07120c060305130f050d020d0c170a180308120705120f0a020909040c15 70
    0xc4000d032548c518400c190300051000e40303050341c4403222200d01410560240003c441041603500041c0d4460400f0450207602040780700360910009080000031200002103101d030071006401802c9202003c1e0401c080b00450b20400001402180e4030703180001c0146440c5d00e06032031082001c40a0141c4a1001d000d1a061000882c8240c6010003c3c010010710890907681c1318401e1007044e4004800401c504240f294032030010418041507013020b2100103c0669880a42c0f0422514040040c1d10482e484000600740c1d81c080b641010070081a0703001885c020905440328200c8040f0040c0e40704001d04034282c041e81900130030900141c00c1d15020300e15000d40b040001c1035103007900c0414408030301609003441c0b00c0294400781c2c0da05004003001e0700315060005010456240f000308009444e00102c0d6400c0c03001541d01640c3d22144c0740540e014081d8078003603103062800d54200389000006040240b01c0e0ba4000082801a4190380696110040191034080c19151604081911038018807a0160045100b00c4400f021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 77172025 1250 77170775 77170777
    0xf020310090f020f04030c15020607050f03040c0314010501030615050307050402070606030c06020304030615080307020f01020c060703030b1008090a080c0a0f03051309200c01061d01060f0203 84
    0x44802003290592545480c01010141c400a6980c000e241d40c20041d10011404c560003802c061400b50340c1c004252414040e035010410000a050425940148108844980c0c010125010040e02c03c2c0c145481c0d4840c4e2806400d2560203420040c8180c070840c61200420a055015a04032402041c05024009100c1042580c445d094082c0741d8060f00590424005414140c0050500c140302e00030015000b41d580d10f905908030120341108005800005017041800090b015600d08460110145070500d40782c1100541e4a1140540003802182e5a2000f00540d8bc028032420f000321602805843ea66402468020020000703422264410310041003403002c40c038800c82c101441381300050010701c0241181c0d03d959449800070401814103100b20721440c0c0004510f18034480500344a5256079440d0309110322042001142c1360811000d1600d02000103000e41c1410f01d03120b0840c01d009110b96511a01046500e02618541d000030b000d17100c00180c51592070000d444254101c80f8942e0326036002c5c1c3c481e400e040380c803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 77173275 1250 77172025 77172031
    0x1107271506020703020d1703010f080d0e0a0e07121d0f0a02060306010c05010b0402040b09090612061b04080703080901080903070c14040b0d03050306010215012d1e06030f0203 77
    0x60f44100700500050610075601380d240b500070f061a2080481c60600c04d00180c2c02600001c0c9540c07860300d030810101c0d03410172911b4421207850074503201004602c804515540c100f4841d01640b130000c6000f0800107400340c15000030703102e1180d9051252090200b11010b5a05c00032640d006948140011480e03a4003003c1120180950300401c0035241d038440100450750080c0c0820181c41c155600c0021440c141d403540300900c02010505281b50b203600d2048200601d40000518082c000ca1030b01c04d06016200300880c503c1e038030500750f1000030341544042c03039144d07481d005580100c40395100310400801489040c001030080440240d882c1c3c070095568400d41e03520781c001d00709c000381140303c00f49003881041506c00109407032000182c00082c1d50182c030300c002410032a109c0820380100300c0000038004156814041190142406561180c07a94505040408845020800c01c001d81c802485480707410442c0b41c0c00c0f10014a03a000041c14000da2040c044030104540c0e1081070702103450401e0b1800354500c24001d5a00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 77174525 1250 77173275 77173277
    0x1060f0b040b0f0304050304080607090603061d010501030f091709030105100803070303020a1e0905040506010c05060c0a0e060403150b04090f030305060103060b0d0b100c121107271506 81
    0x1040c0f14041c10150b19541000d4004c5030640400d001c04a082c850400c40d461040000f540c1c1c00d40518075080000d4100c13540740e042040000c180400481881d5561000d650450701b0a18001804a9602000100400d00b40c07000901c00f2004211501380f4510b00c501230a1034000c1140200701d80c0c0c07a8490842c0b003c3e40c03d842051300329001032180b500072030301a9001d44541c21f144e0400c042c003c9009071881d149050021907002c045003541d07506120a0602e807103907952180c406c2c20401c140d10700f540c803890341d2107038010855a0003010001d10355003690702c1410014120f500c044c00143d101c544900c3e004500b10203218230003a240c2c1c034000030401170b8a8980220381c409900802d0b1100080e41649003140a03202c000d1120b03042c1500d84034001031001c000401045a103c0d051400035901d1030314800c00c0020101540120b003007003440c214070710118022040114022040303003080d1760010804000e242c1441020303480624804080007030b607488062010491b941d001518030040000c0c031003100040b5411099401420 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 77175775 1250 77174525 77174527
    0xb0315010e040f080a0503090c03010b060913090507080a15060e060112060b0c0d17071e030e010f020301030b13200a03020621070801030206120c12010801060f0b040b 73
    0x80a8010300340c84a8000c0d0003203c4200a1101d0381e241c40070b1a905c10060200000c000204015400200307001c2d00030102800c600034400980c1307800c00140180140c00201303100f43c003000150305040005901541660b98400103076406a50b5543c80c00f44c03038842d041c1e01030b6a194000140034100044a01c41c400a440340c940c0040300d01c0d00e410004444010018102c03202d8aa034501001c6000d040c02006426074462410050041409036280249007903001c2e001d9414503400c407014002c00d0341d0410f40c81000309940190864228489800407000380c11809559105135103440e02d05074445000317400850580340100301464150300c0b02440d07450b54811110002e410341611204071480c00d083d500c884540110000c0081ea055a22078000070950380c010490101d0341c00e851054604880c030041001c591214850514900d2503246401040b210712a003410b10610f401781c2c3c0c002a1300f804140e001d40328800c405a50714034056840d440124002d011a019064100649000020f11281c48500f00d40544121200da9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 77177025 1250 77175775 77175779
    0xb09180d030903110a0b01090f1a0402070c0b07060f0b01020f15060307170303090c150909040c0306021303050709020703090918050a050c01030f0c08040b07120c02100b031501 77
    0x4400070b041d194801c03020003480b0b014501003c3c108220701c8000c54004c0150410306e5261a50350011510301e440f0540750700741000c0b10f49100308584064110400c4050300d0250380c44041e4038191004d0b4800740c100d861880b07130124021081c420b0550020041283e4280c1c00c03c201a907803001640d49260803500b80b010b40c4c0c41a90052409103154500c02d400c62070140c119222241c580c3c440071103c0c100c1000c0403500782c0c004000c02040680400c408005090280c8444c406004599070211381c41c40381158542c001c01240020800700100b00030408011078110f01c0854070b0b21008185000d92903968030090ba0613228050300465521214801c64a440d036050700ca0740707040c0345000e010401400000b90040d01041007421560003040e014003088124511401c0603180340c00b54580051308a4a8424072003184614080d50703100b03407540181440340c20580002d1032440c16501e2650444110300001000c682d00c60508004d590b040d60000b0380f00e04038813042030041c0030f0008070100b456684c0b84804030411ba454949401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 77178275 1250 77177025 77177027
    0xd0815010e0a080a08121501080c0309070b04060c0c0501030b010c0209060301020d110a020114070f0e03120f07050606090402100c080f1603120c0504180608070602010b09180d 77
    0x2400035841c405002241ca0b1603454074070508001c01c0c0b4400707580c00f50001032a03510302e01c00810b00592110807280d00300c40e09480c1000003081248010040d1040d01c800002003507200c00204040001000b0302d800869035507460340b2004040d61803441048801c1110880c0102da190300a010701495888180c1d202150b01000d038080001801000c2c1145405550800c103003101900b00380201a900401451741c1c0b40c1d180903c05009003150003450842400a1000342440100d50f23200140107541d440768039041c4403981480c000a400c0c5444184d54508140000a1a0720445007400c007600d0b07520b004d0011b035021039a1707820900c031101c001200d00951150040e689003031418000c1e8103d8403994000c0407254240265001040466807100c00340800082000100004040d4031200c0d0b008040070f04038051243d400c1c4e1031000f51440c0514000c400c4107021000302d01c08002e0703441c1e0001b4000e02c00f800403203001c20381e2080040c0c024424511528000d2040340c001801422105140c60600c2c9a948010001c042c48450 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 77179525 1250 77178275 77178287
    0x20106030506160825050a0e03191b08030f0304031803030801090605012604050a0b1e01081b09130507090b01110f03030112060f0e010e0d020d08010311010306080d020105010303020d081501 83
    0x800c07c030034420303800036500b42074404108510080d00c0d005030b14040e4046c80e040601500c818608041080100c0c040c09000b81500881507891441d080b886054403911079280980f8034110303100705030f10300340760b0f041c000001d256000c904541223608a400400c002502e420045071404402421400d031b070044500b4010100004010940c1d1007801003090300c01c03883e0380343e4074841c1120b420341c0c0030b80300007001e238036000e06012502e0b000038010b0440e50020603044800070008405c0d004003203026441050303180c00244400c0110503080700f1482e8088169802d450301c4e00030b80740040c0b8003103a483d40000c41c00031242007600e00c0000d1b85030101e400e4030021802e40e071070140e4a07004d030b0008400c2103820704d07140d500e015000600360003401000042d40f000410452500c0410368030b00700382c44449134215800b4012400300340c0d420441c1c017070540b50400c0300710244100110040e805028a54403015070351141110300b0700501d1707040d07100c141a40e10076803d6480c0340c1d41582003180c0044042d649074100340d41d0080b0400c2c0c1c2d503028075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 77180775 1250 77179525 77179537
    0x510050d02060f041a0702090a1e150512030d0c02060403080f0c0904060b0a0f030b060d050919120f03090c0e0415020a0201021c0207050303070f02010603050616082505 74
    0x1220300d41ca0591a80e400000b05a0800010317003003580081400c4c0118034008102543c132601742082002503122501300c51200000d90308491b1100f542d540c4503560ba14100c240320300003401002c0c04011302003e00c600c038555690700c10001c49800a14291500240d1131012908074051364240d03443d50010749601034000c1d140c0c04060400c44030345804003c12403e584403801040010503005400035110700000c58043d2040d00c2c0e00da4400304040c81d00345455200d170341e52001d80311808200c03000001c4030f54482008900d4001c944a000d4010740c80200c2e030104200d0480380901c84021035990b182e4030046414010303010380b06100c40080101c40d541c202400003040140440303502502402103104060042f5603040200d9000e400324000503500090450f204030524245d41281d11502d5408614004268a490f900c0e4000540800c040041c4610901c882d01d2003504000003031500001903410bd0305000d0342055080d8050079142010400c1c0500141d4141d621a020041000c080e190321014504c8482c41211950700c05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 77182025 1250 77180775 77180797
    0x1c27050c0a0305060613091e060e010e1e0705040911010f050a1b081201030b01050102120c03071205120c0702010809160b09060f0f0304020a080604240b06120601030510050d0206 78
    0x140c0929021800000195a20344070150310300a0543d03450900c49d050365949940507006038105100002c0e4401e000918000c1c0034044c4207030700000000050058180000c0d42c3c44150701906040c00701007803058041414030a590241c03170303200101d0081c040a07680e9005000c45000401c6e40003039000341200e851f40078808007604c117007403003407400300c100980c0700228900781c105072060034000300103003d43d580410107541c440d0326000c03089090444504402d50f4030b11513039400810190080d10a000c0c090300413030aa4071804c0761406454501d28000c808905942c204101c182d00244400c000b055094901045a1507031603109898142014103107084510700e607010703108541d0000c5003001910240f980c46409803c0348110741030f1aa5580c1024010403008803950380100b40c007034000c40184800500035040100d0070b8a00107194a00d08002c0d690b00d0b40040005000c1c80e504071100051a940d03180c1d4800009103e010b09072010046601c5403d40c1901a1989004140d00302e1040781041001d880e040010b06078104072 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 77183275 1250 77182025 77182031
    0x13020919020304120323190603050f010e010506012c0105090406090e1e491403090c06030a0e1603170306061c27050c0a0305060613 58
    0x141012000c1203a00444040d03400540307200010038036035030502556900b1400c0c040003040040d11418450400d40c1c0191a2841440100865002c140c600707403c00710040d600001919110742144985901030103007202d107984c4651030640043c03540d45c002c0000d00903440000a4a504040a820402030000c0020b0f2141d418000c0603c03d4607000d50706e034007600300075140d21200841c1a8170215030756032501c901505440180694598803828015000035110200540e803240078440c039209502c1e0000784641c0f1071060603200c3c01c0c202010220440e10080c0a0103140d170f80c0d200b040710340300c044d10260203002c1907403c12310540110000754050300c1c0400c00b540d001102c044002868415a4011f140b404070640700c02c12904c1d6940c042002445480d01000350f4819041c10010714519125001441c2c5101c0c4501205811120940c030346034804056001c2d528030020880300b0b9001502180c0e0705030b601140c0000c2240d40d84103070420f100440c100a0f0781c0300102c0798050300a0006449801c00c03c655085030355040c50400d07030303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 77184525 1250 77183275 77183311
    0x1020d09140f0405160201140705030402091005151b0706050405060f040f0303030b120304050102070501120906060801020315010504051008090a080a0305070e030c0907050a11030d02040e0f130209 86
    0x38076849983e004204810b041c6080205c1000087d094aa41c1c0ca28421000400350801c5074080c2c01204903640325904442e0030755180d440420355480141203800180d04441140308142c5031110110040c2400142d00501080c0f014151041e00c1d5142c4445c02220001389080c8410062820060003824058070003880340c03418142c03a628008000c0c0c407158019000691112900c078403e051201c80084000b01c100003a501d00b5041c180081c0d130f03400c1903209142c10001c40704600b50290900e81e00181070303140e01250a1101a541d0088036020350400d645845c0d40a081c0d20100b1910340c02001124200d440280001800040141060750202d00c014004040d0f40102d50720750000070344e8003004200090b0551400542420001c2c03006105041e0301c0c040074080d40c88200c03142517540e140c1084aa008001e85000383c1e40c2c0042003000c03601c646514085500300d01c008104404403c0494001e0000d0398022142e20720319039a03041c0540350380e85041d9554006081c0c03040084015040c03141d0401d62008a0340c600403c084 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 77185775 1250 77184525 77184529
    0x220c0b0f0408010f20070b0403080c0903010c08041e05120702010c050304081f0204050303160302010204150e04050a020f031f030c06030b030f01060614031e0115030b01020d09140f 79
    0x1924131aa441d002c0356444520b060b0034000000480120740048201c1401c0001035951100007200241c03020f8244044140043c060203c0300045407100c6c4000f4000780b002c624103440140050b0800e46003101e01076a82c800c41a800102d031003140c01166000002040d504004100070380c619400000305174100030f003ca050f00007080f4100018401082c0318801030a10584004000d414044d01080b42c0020780c1c010441000a9030300001500d01403141e20b2180386403900c052409900a21607a80500701d41c0c6a0071114075502500415039840014007540cbc00d0141f9034580000c441284581c00450002080601c00b0501400340404441c041440801164051981301d842e858259115030f4400750000e030f02c40400038203d080a0008800104502c00244041402c154000d0b12000012003000d81c0303090084001100c040a644441c0f024420200240100d96150b65201980305600407111010074200b504818195100092203403081d5001d42d00c00d0314260800d00c502c0c44510804100319481000901240c89603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 77187025 1250 77185775 77185781
    0x6012604021f0503010801050606040f2d0f090f0516110a0b0c03160e03120d02070b010602030901020f070503060a0507020c030607121a180711030304050303220c0b0f040801 76
    0x28070a50f0311025169031408804c030b406d5410084c8481d014000900c000c11014a5408911041d2818250340d0060040b030000515071904014804089510b111680020b05100343c155080a40b8070009091060680034503401d410307500c0c1511312020340d42c00011501c04a41c401c0804101d06070b2607609840c401074442d10741580100301544d41e0081e80784001309000c641041280101400046420f00e403211703001d1700f80000d440e10b03621480e0301204080003400d10f0581965038101d4400381d5012403d0006542c403418000d45d41c1d00483d00e450b0240c0701d05420311008110000f101b000f2248020001e02e05a92001c1c03844000d080c0140807641548100d1007440142e5605020303952003080030303030394141c00750f209541d80360181c40410803006044252001c1540540d00c0e8010310704c0400f04002113581c4035844d03200048076401703141f1401e1481c038000803007030108001000c0001c601501002e085d920416002014084d103541c2101801442e890007035200300030040e41100908011100082e0007810941c0d990a25070075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 77188275 1250 77187025 77187079
    0x31203040b0105102618070305010204030309080a0b070e0409021e01180e01030618150609050c030606090103051b040801050f07020c03030d0b0607080c010c080601260402 75
    0x1d10091000602483c00d100f1040900702035039191407207005848060318059034003250f01c1c880c44040444002030507008200e29000c1e50301140c1048800183c2e40c0e0810ba4000c0d00240000c6001855907940082c2c58180022550315a07908100e1164040e2981c034011f49100c040015402d42240e01d808040340542c0c2d4000c0c00c85592500d609000034140341400004055000c040c001003a490f445c02c0090041d0310300100038034152a845000081e412903801c0034402c00303814080000700b412001c4880c0c4c411103411b6402a03c22558410814425503c1d418a0140603000c22101542c1086045c8070101c484d622980113142c10480d0324203001c0380039186061040403580150030080160791110f040c0044405008201a4402c2c8148090031001e420710707000940324452016207090440d1112040c40c0d00c1d554920403030703e80560084405030345072503112440d4007811107240e900340428030800000c0e0780f55002c1c00a01ba4100441a40001411141220490413800192090340c200c00d44000085d401030100c441200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 77189525 1250 77188275 77188283
    0x61006020d03090c051f0f0f0f050c1c020a0309050f092703160c080a08040b0d1b0306030201020628020d021b0a020a0b0c030307081503070b0309070e0c0702010e03120304 75
    0x450b5412080b0b0140c19418032290700400c101c03410071440e0080390302a40d1a40c14102c2171803c0c1d650380c921041d03030600e0080c810b08080c5e101c1c40110443c06d002a0001003400c800780c40b430b40710506465600c10410540900c035141d80f64110002c040041d13040b4442109040380004498522402c100541f201c0714615040402000d908200144445081c80240030710000107020600c01441100e1050359100340c240a1391144018066020031030650041050300980002c011129030300110901910b4001e02400151000f030340503001d0540422004c260349001c40f007052107a06100c94800c2480d26207140258403030348010344d400c1d9080c040310280000785500c403918080c40400816454200e80100582680a54087c2c5519607041202126000e00402545d6105000d03013015101075440c8500c00300107804000240b503060160341404958528000041c41c0204c0300744d0111450a515501500020b41c4207880301d0102031018005500150300c40c02204044142c06400d0390200090390407007400c03640080e50211 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 77190775 1250 77189525 77189569
    0x309011d1b19090504020307030f030215011d01140f150c070605040602060f0402011b0506070207050109050604050d020402040b0c030a020c10120522080408061006020d03090c05 78
    0x800c11101100301240189000c82d9108000058120007207140b40442c4101841191600006820744d5000e100050040d50000b01c9074030340c00d20500e00203480c0c0405013001082c10036001d001041d0f1460700903429035410302004001046034280b01d0041c1c03e01d038240e8005a400710a484009020781c540708085200d80303d28403501078481c204d800d440c50402c402d98110000b0040144010440140c1c00682c15400288003200303584a80c649000413241c0700c0d0300300c0907841400d50720401c000030018009180d510a0701143d003500d80c50f0b0307241c0d4011250003400b8856031f58455002d120a200610342000000c0009100410040c54107507503007981d00c2c003500484d0b14500c59400104120204a4051044118100d422144040c0c2c60b0071190000d00064080002c448420f40e03103100060384500e01001e00301d01240b035203100c80c9480c1018600303001c031075010b40101481e40c01060040345140c8001c0c06650241c9160750082e0480102203a012001000c0301c61007078985010111002501d616001503840418400310021 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 77192025 1250 77190775 77190793
    0x2210d0306090b040b0105070f0813031109060f031002030c1e0c01110403081209010b19050a0f06050a0f02070f06030207020301140c0306010c11061303050706020102071203020309011d 81
    0xb000841e0031900415028078200000180b00360f902a088548042c1e00c408115040c80c15414070900078043c40719141015200c0b83c01c0403045c000c0c0361200040030700c012175a0000644d14030080c03052407501d4a84180d0998031400c0c030684845e00c1600034580c0800b2600d1a2800c1c810f204004000c6004040041c9201000029800d20414800c0c00b6540c2c0c0320032500806c51401e85036907204035171803098031b00d10600490ba14010034041031003034106510002008203a05000940c400e5464a2944039200c0c07540b207074010031000594550030034030705c0782112400d488032030904400500603a415400c0c107210030214040e200e07001c5019190881d00202500e03c42d40c0058031520b181c414142161181c241404400208404201c007440e1404c5c01c60340c0c4941d082c43d0512031292140392440750f8030200001191f02400100d806100b100030044800c04590290b021075407a551760341c0003a4201d00c03e0f04d0000d40120b003020003401901d4000d030000d43c0c2109805d1700001e400d03859074050652143e030340a20604241c00503810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 77193275 1250 77192025 77192039
    0x130b12010807060c02010c0201030b0d060203100503061b0a1e020303100909050c10030204050405090105070201060b0708030601141207170106020114010306090f050a2108040302060402210d0306 85
    0x1645024000100041c8042402c2c40400b0b400c2d200c621400904200e81d030300c1c0e80d90869201380c001d4603030507401418480200c8000d24105001c2d410456084052070000390707000915280c0050554010707118035000503020403400c0c0c0300026540c0411040030511550b040c0d814040e40204017031250550059000c1c40e100d0400148440700d00d1610391010200c4c9081c01c40b40d00110381c000c585031703001c564100c0e9451089114580190041c0c042c07640000e501905c0d00003009050101034222034405c009a50081240030f4072058940c00fa401203138030140114100740b000900d40c0d4054000f1598083d5031058150400e644190300f000e0354007040316040c000a40341c0b00103242e501c9141d00311502424070f500007480302e880d045100700030240d81444060505600d50803508107200240d150005420740000580314400300904013903d000c50f200ca009401c0c1007810000c0c44440748500307140341c001c540c0340d0702800c09a1600e03005c1004d41f00b141006008180c03801e09003030030310601c10400c17400b801c1c0321910041002032520300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 77194525 1250 77193275 77193307
    0x607023f0d030c0903020907030507020106090204080c12210705010f0e010906060b030c0a030b04150602061006090e040206090111071418070e060318060103080405120106030201081308130b 83
    0xc0c105040c000031388070603c01644c804d00c0060384006540f500040a99030520124050200c80e4801e800d194070004c1c010982201c04682070b01040030030340d228080c0301c540d08030040e41c9801c0205c950000d0150182403003100c5155000400e10381d4003130000419101c0c0040442401c8170725800340c1992a1b950760070184208401c40c09044010321000010710309500e030203015000b0714811601c0d050101a507590001c602c030f59139540322110001d004424500e485403180c48c0650380302b105031064201420500c10000d1518441ca184a0030344100c81d2901946488035404d010054104001d02814400c000390b403807204080c00c00000c030081603000d06c0c20703c086132070f1014080c40b440a40071400c03404040004000d030098012040c031480d02010340d0110f030340b0ba0790706000c044400551706e81c00c06103018001c0000140f050300350240c0107840d42198210300180030244103500300d910901c002400701e04483c00044954084d5462800000d016800c0380c1d01c0c10700c140b014150002c1d429004690b111308046220003c000c0d0b054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 77195775 1250 77194525 77194541
    0x3020906030c010f030f060e01060c03080c0715050c220906080c1c0201020a080307120e01090f020f040207060216110a080c2215060e0607023f0d03 65
    0xa800b0700a1200314000007441001e041c0c0380360040c03540b035480315003c12100b42c4c040b00081c000e0f1202c03441696140d0200610b081d41808003540000c41c040007040f91500703402c08403562658032580000440d45011a00c070040c0000410803080703610144480c50501c1d401010244014000400310b60406007404894021103105400c00b480175800742c1000b0350a42c5070b41950032040c60009603c0b030304066803072004074580704850f00e000301050408000e01080c1c07604601c40310740040c1103030307414080b445c41045142e003220340b103000241104802d45c000c100942447e064040006e000608007626240c81601c82c04141e91081003610080b001c0590ba600c14020401180c80b800311045901a014918101081d540c1d880000819407040c0d42800490035903c03440e00c085580304848450070310032401e1440e0b180820510b10300c28100403a140101501c107615113082128500c039030041900c02c0d880c0c40d9091840c5071300300302048003c2000e088990300803285070003040c10171452100002001055002103000b01628244 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 77197025 1250 77195775 77195779
    0x102010e0109021c06090807030507031b230c030a2409051216020418050c0102010c12091502130609050406141201091212110301050a120f020a0f03020906 68
    0x4504004016a221120341e1350340b00201d8148400302d8031a04201c002003a041c0e8005003100c400040544c01c0541020140852500985642d20820507102e446040b002d0200801007082d035a055014480701d0744010315683e04401c150440d013458042e600480e01e030420b686c40a80d10341070301c0301c07850500082003003511039000107064090100e19219075a01c0da403440000040403481d00041603182c41da5040201000840d60014414820a0081503440604106142060343e04c0e00885840e40302550050003501c0800421f5503880e010740301005a44030050500d0f500482d030049041d00020340250850015040c034a2400c05007442d0745c0d00d807083c042c01481c0035038010390045042010400000f202034141d085441016900c4a41d0080300e2201680186408880240604100c5640e400c0e816800f120100c040503001c5010040301e040402020f075039001c00d205160380300c1400710007401410b51003c03141003090b02c900b65645101d5817642c0081c0c0d640800d500505031140498404005515100b00d1441e040398007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 77198275 1250 77197025 77197031
    0x1e02100e01111611130b010206160f14040e1e13030806090606091002010b0f0a03020a0506070206040b0307030b04060902070b220209010305030304020102060603060906160e060313020102010e01 85
    0x340340c00400d06010f600c1841504080e1018100f00b4445441c04010880a004204001c14910440020010302c00d00c00e0306401441001c0c0010101c1c00d0303402031805807800548034071801400341802162000c111541c1da610b140700c14040003031400b1041c1441e81c043c9043c104075402e81007298000500445005285aaa2000e18201c82020a4010144940ac000e05480e070f10071070340e80c0070302080d564410014020b402007803504144008a0341035010a1504c20111141c0110307036804000c002e040d031140d0001035803000e4150010021490000e0080510300d1003d85024101b664400445020390000c6aa41c0c011036140e4604e0002460035200720320280c0717440035045041141c992109104c01c00014000e80e0810380003042001d107028100000a10142e009054040c15030f1603190443e200d41060310124050b20aa00200b40c40f0301e004500144a2605180149090b41e00c480089540d00c91015501041c8040042c021500c0d4950100441c458019046e2041250309244002400c450340c9040042850745 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 77199525 1250 77198275 77198291
    0x30702040b0603100e13120801030303051803030c0705011b0e010e0d08160203010b0301021309110304050a060b1305011403061b040302040e0118030c050d0507030c030f1e02100e01 79
    0x80c012490140c910000d43c0304504d030341e40680e070002c6d01c0c46544041c0c54510031186059440317038440007580c1600c1c130a550601c11515040310200300c0c0150388080f4481134000384002404001c00001138a0746a0080c0c00210301100c0f1082d600d1103e140b101e140d50001908110860703000d5822100802d9034240c265505010383e107894898101a01400e0218071500701c0d8803007824107640d025001b031495004010000c556614000980d00d00c005030b80d109005d011410261458102046101960302c125044406444c080026903214401040d0216402d41c1c4440058180340b80741070540324240c060203000390440b4040c41c026040520340100100348001410030480d100c4220b050b140e05840449605480c08602c10703a0041240c1d025022410b0344007100304190149005243c0d100f114041c2503800b4100380c90043c550b440003280c9503c04c450300078010442d0f2015030800030b0b00c1003100c0c0c511150a880e004d85000240340e0081d240b50241d044020041e8002171200516038400c1c850300010070f0503d0700800c5000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 77200775 1250 77199525 77199541
    0x4080301030b06010c0203100f0e01151a0c0613050c041a010c020310020c070513060e0105010c140105010603150504140402010c150908040e01120b0f070203040e09030702040b0603 79
    0x12005000061002141001150750307039020751041e0504070350090a44400c44603d00c0c0d5100201000500102002d042009024a0640608c1641124050101038501403400c105114400e0039081c0c0e000340c006c1d5002c20201c010100148812030040424031812000e0b03501c582030203442c0164241d1811b00c120703e009200c198001c2c040740181041c0800f0f0810142d281100d00019043c101142a848002400041c0d09003504001013800019550110380040c2d010001c401c802086884501505031041e00d40750060000d503001d03035240146a4454500071a0401021500609540307003a40310758082a250f5689012003841a140c900150106a50402420000b44155907203d5805040603041c00715030494441400245183c0d0001100000002c0c80752414138500641a0340c07081c4540d917081d20303980002090000d044100c00d4001500000542107644440045600c04900580740c1025032004102c00036000d801039180324856000c0101443d2500660b0041c08251030201956502c215010802c001d252 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 77202025 1250 77200775 77200777
    0xa122d030c3e0303070f0b071b15020d29040501090905060103060b040e1605010206010e0624040f090603050606060f0a0c05150f070f0305060d030e130204120302060f0408 75
    0x10504140500720b030803940000b00e401c5128030080500b0311442c0354001000c0c003011304130307103401801660382c0c1c18904401009581c0ea45548444001c16a65400307058100c8041c850700601981d5070650400035904074004100d400010051045a030308425031621400c0a203010320483e07005006154041c026002d1360380d903c544400301400b0041c5403540d035006d0120b04c1c0d16103602c4030103802094411900c00c5034440d0000500160b039882307010300500c6450008982030307270b03c848224001c05000d0140d60510b0741e0503210688000d80d0300c0d1640720985041c40005012485120400018562030f600000d945003503061240c2040801040d02c0d00514007040402c6503016034108484c8130109600e402c1020140030701d0118123240401a50146090451084c441c0c2544203e5015015000c0761700d60100315044000140c058420445440d98001f42c4c0107461808a4080c01e1982d0800400902c100700303442445001504a0300b060700003140051a6071415000c250301049400e030000c0d03070701c0002a03e03454196200081c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 77203275 1250 77202025 77202113
    0x11e11090103051308070c030b10060912030c0b07030902030f0c032a030d0f020d0206070917030d0203010306060e1012020f04090501090503180a122d030c 68
    0x10140c0c1c600000324500d00c0400902d604d10350100c07100703a071402142460034403020540025104140341c44042440001d084d0164021544c1ba0b4031202440d604d0480081000100380800ba0306026042c110000050b15900350780c3c3c8200c0c0240c500103061609801498a08a10020b01052a502a1580b6402a82c0004003d41e19401c0010b000500720b4a992410744004d18030b40001d0307014800c644911342c0b1690088040001828640d01302c6418844a04040742d546500ba0f5104020400e031900902c202101c074450854540120000c607403810f501d01108400b2a80309178015280b0a031390754030a000d501c0040c1700098010701e1003aa0b2107049400c21001026035040203800903c07808182c00c80d0310550300c03260081801d044c1c00000030018844181041074603503200b1902e00c101203041e88030816a40c9000e5842c003007682c4070084a4200501c40780d90380f0410340e404140b451000829003180c01d070100440074410340054400d0340e450742d030f840389d61070700300031441710701c1d01d160203400380e10401400c05a0360300c0362030b40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 77204525 1250 77203275 77203277
    0xb092503080412030c050109030806010e030a031e050c0f03040321051c1410080c062b0b09090706030b0108011202130b130504140105040807030c02130c02011e110901 73
    0x200031180b805175880120f42c3c1d0024125404d02d00a02c0c10705810848013485601d00303803180d8114034004c40425894501c2c5800c01404209108000d0100c01041500a80051b4450400030f103400308a095884c54400f03da0f9a0800951000800340200039010f4002c0f070650180120400000011103c0603045000300b4014070030424009081f130510030110b41203100c40c440f070ba00904032a82802690010101404e005808461280b6400c21350305040c800103c0b40c030700348960f01688810701c41440340c0010000d940c0f002005540c036120100c00a580b500c134042d0140511b0380050101d580381a201a00740d07440303410080d0502043e24010070440010a9965030280d5040b0740d56010407440e003d114009026400c0601c1c0c01a111307100c083d00480070f940c49140940c0c01171352010391861033040d4090907201d04481c010003000040c031001000034001c100030581284014601d810b0490b05004030000c0701c803003201210040c3e440d80301202d003100d144018bc610034450800e05220916090445010f5881541c2c0785038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 77205775 1250 77204525 77204549
    0xb130611040603020a0306061d010c020307150f081b0703080405150106051210030c05060c0106122108042006091003050f010e01050307050904050a0b0925030804 71
    0x50104202a480240300c5040c0150894a070394903900024000e4001d4004a00880d185c81c2c1c001c640c107801070b005441401485c0d03410081c041c0604004403070709840d4800032038040c801d02401140c0024504420300d540741c4070703980c3e44000c2d1a034440018480e120127800c0c0310806040c0340e60542c400034680100d608464040c11b000442d81c455251003403901981d120101c2c001810a000400e131130794084000e000090001e086060a9120082c5c00c0c502c2c2c41d91840300420460444100700590304152001c1c0104c40100c40002540791f5903418038a0b100e050140c0d0489003004650184050f40c480c80b110301c80540528503000d0464038007540c4400500e001d5a0340f2205030400881c802440e0780d9901c0c02c44058403406050145030040c1804003401408080d0340d078040c800707200310003c02c41c0407040300b845049881c003d0052440614000c14419240c002800681340307402103d280d407010500315601140520316602c001c2148003188070540100c00b03102044841b504600c00c0041006c540f48400340c0d8241d8010714404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 77207025 1250 77205775 77205811
    0x7090f030b07110f0d02070f0f180b1309030903060c020303060d060e0a1b08010501051c0201030513061b1d030a0209060307050d030f1421060103150e0a0f06030b 71
    0xf140f0f401e00d102030b900e000d4402d00c001c54100f503501140e40012548615405400c07551500c00004c204c042e64000c49607450701c41c0140c25420300007038014011100300135103421501c40500092105130742070010242d02198100b0030420820840d4844e0802c1a506403010318214240100000da01e400c2d91040505240d4880826a0219100b400004026a80701001008017410380c91700155001a502c6203406951a0a00005550402c000908800e0f44007035060a40801c80d5401034000b04405043c0b100d416804409105c0040c1d0140b080c0074844003c000c035581d2810b90000d0003802076140c201d01c7c40040291014040070303a14001481c40c450b40d411602066140d41c3c207800700380341100f10b92005907c210108404403c1c5900040c21241492850303840c1050070041820110443c459800c03220007003200040b0b009650090112041e80211052601240c0504040c141c0a141e000b20b130800c9428502e03410610a106120384160304000e044840207000032840c50f22040d5100740c008040e01c0c400ca90340415 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 77208275 1250 77207025 77207057
    0x100e12010609060e09150103050a030c06060e130203070503011a09060d0206120406060e040201050a0302220602030c010b090c0a0f020f03030f160309050303060409020d060501060807090f030b07 85
    0x16018140c60340c0d08211455484c420803034691030070350340e20070325005030002c0c0c02c2400410006c1d0341c181d07500130b40240285003031a901200c2090288205441c41981c51801082107141d95110318000c805c1540b8410110310540105414a05280c1c0f06c3c40c0310303a14108600d02807031045c201810050100b100d05210580e2004c0114020301013121000703601540004c2c1600c8130446203900c0794055400b45104014854030307806c514412540968020780420030074440b51b550790303220b50010318801c05040c0490b0003101a0911096007030505030002400341c0c10110380b10614100900c0b46102429044031007113260304124004003c280304205019081015050004440f540208000520310b580801180d80e40c0c50001850084090281c8201d507400e50806901c510541c400d0180c0740605070440091071a584483d0100002007886c4a0304980001842c1c01000100309a442402d0003403042d9254081640b508102c000e200d0030040c0c02040340c03404980e000380040b038003019406078402440d0806a0840b000952 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 77209525 1250 77208275 77208281
    0xc01110703030207050601080a0f060c021609050702010f02040b090d1e08030402040f02070c050f0d0204050a020408060106020f100203071106040606080609010c1d0d050f01050411100e1201 83
    0x204840010600103001820160316900910126000c0d90650380940d0b2180441511115074007009080129140b8504000c24483c2e400510884201d00440c0e8107a13412240860244615038021403100781d07110200050746e502130180c141d041c5450340c0b00b185407908044000c8264000d40842500030311710412010200090801c0d082420b020040880440d10200c1c50103d5869100310b40c00c81c01107051074540b010f890340038025200129400540a80142e042c5424000c0152040750115803108041c0500070160b10b2320312070741d409078505071809a43c550500482600e041d8041c1d22040031540030030310007203610401044030f2003404180b54015a0741e444035142201c24a960200c0d078281030042009001c00c00c509540540101c0d9201d005446c8030f655003014244c01c803480e2501810206505204000d0001010a040840b549004000340145515503c407207140842154060703886a544105000c14080100e428113015a000c44404000d0400100010413100d07030341140c5409041c20310510a4145000c2d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 77210775 1250 77209525 77209541
    0xb030c150c0c03060108010903030f060501080604090804050d0302010504110603060904060b220c0e040501050307060c06180302070608060402070809060702040908031003021305090705100e03070321080702120c01 93
    0x101241c4d01c0396102d040c00c43c02000490400c501080c03400890794000c2a0302e0154004540c416103074010190303650b1060001914010204803000d610400000c2407a61342c14600094250107640009030f5840c003864292423100c100b00031188140828400c1220030342e5403c00d16584190701000108500303c542010807280350000d01b01c20100818243c4c1b65640c01ca8039072202c0801e0941d95100901042d40c0014841111070070701070300341c03d50000b85007403191301c1c05807100f00340941c41000005903c05a5000301203242801020840058010362010400d441e4040c11043d0041e800f1281146800c0c0c465540701214868a507160b03020b03070004207102040d9900c9600400c2c0302030304184400d60340c0c604650320a01c2a003890208900c00c03101c1c41c8075820008440d120310b0f403041c03801ea0001c6c205541070404001c08001000940802c01c020400941006d880c2031008400951007011549003200b0140d01c01d0500c1c0054991940401660408102807241c0c0003419007050143c01451a40e26040101d21502404000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 77212025 1250 77210775 77210779
    0xf011a1b100e011805071703212a03010e090f0715090605070203060105042004091d0c010e060a090f0b07020f062b091401050a0b030c150c0c 62
    0x440c00c1d075415003095402c03a24000c0325240082011107805070000c0700084450001070003540c8103130b42c20300442803908091a4040301c2882100d0400b00100070861310100d20762a01074082c03d25001b40519001545564032010f03418040558402c407420b1400a101d000500c103404d08150884081081e9180502c01841007001190549500c0d40d29803025814080000c042c1c140040c000000000c0c006200d882680c00741540280500607030791800041102a02c00e2804600422080744c0c071030010700e41200003c100800c00c0712804181030001142d10300d03080c0100c4901c0d0321036801030080e00240f81c0c0e020424020007030003101c2ca103488441102c011100030901c0d0708199400c201426001c41e02c0802c40c0040d01060344211140500c0c0000c4006002c403c0c007400e00303600110181d0810001006165144d540c0183e0b441c0003001a1250417515a8a10750781ea0322841e40c40350350740d401806210b00041c014110b001d10181d001f4400111311001041c680c11200c40404541300000c6108404000140a003411140d40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 77213275 1250 77212025 77212033
    0x9010e030a12080c040501020601031103010b030312060103060b030408070b041b030c08100e06070e0f13090611040501020d030509010605091e070207050904060b01030e031605060f011a1b 82
    0x81c0d490b15948400302e103602e980100f24002c000800850100003202c040d40c4040c2d01400c001c1e4610380e0360016201c2c00941e0b00c0c0e819500c556100c9101d8400704040e05940c001c414a00c601800c2c03040c00903007200c42c0764011000d02ca00807c00c20012070548801c44d00e046612840a8800303584508000c210f10b0b80c503400340c000504100740300005011600c412002510501010344030318404002c640c40480c1c4101c0000082500441c001480c0386000c0c1d08800007158010b04480c1031111060000307031009010520010995668000e0001880302a100762243c44200c4003e181c03810342010000703540c5002c0030340b007841055107610024402c11401e4003c08010000940700c180c45040002c4c82175890424541ca000390385000d040020085440094540c0443d0b90107040d4a03001d8840340c907050007805108201606042d103580c9044ca80010800062084210402010a0019803460310303c5c1881d0000c1e1000325000d8005006000642041200080345400c40c91016911102e9040c0561402c58a10f112891401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 77214525 1250 77213275 77213293
    0x304030c08090d060216030e030d0e01180801050703020d0c02010608070909030e060703050a021b0d020906010c050607051e0c0304210f030206060f030a0302070501121e0603050706051e09010e03 85
    0x4901c03406c0d0b02d9051198a5402062000105042d65050f0b40f07807089002405444d0ba84440303500410320041c445480501c0e020b481600e803244d45003910019503900c80082da0004100304040d04a10030f541942080f44000d000b0640313070211040c0d451045019104444d65150210702c1054025090504501d0300600060b4803130005041c054210781100caa55030140c0034041200b66001c20a044903028104010484c0ca00c0349042d40030701207002c0c40100100d05000c28500c0d01130200d5801c020321340c400e02ca00c1d42e52950b2070840b0700902e85413241110307900b00e518405010041c0c000c070010040d070b426602c2d0307014820306030800b8070b6030b0906000c031440020308403289000316a824143c0c045421072098001f501c400f88414410740c181070783c4261240d0080c005800004090280d0341c41070f00705040c1e00c2c15181020680000c42c1c0480e541c40c0510f46c0a21844681e140c0c41001040400d004000040001d404c00500b001410f90b150501600556101241c21200099810081c0c0c020b20000d820071030040d0482d00054 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 77215775 1250 77214525 77214547
    0x60e03070e09280c060c0b04081e0d05060312070803060904030509060a080609130305090909011b0c060606051611041e0905010b03010509030909090703050d0917030304030c08090d0602 81
    0x350300341a5003a030304c083c00102c1c03418080d00194150700d500407603440007583c60741c40d090119008407000381ca0a000030421451946800006007101101203c00001c09082845c10103241141c0c1c2d03000c0b141850000d00401b40072403000002da907442642a54207404980d12441c0031101440340e09030380c0c0d40c42180410400c11843d400030340395100d4541501c0c000507076190814100e04001d4a000010300141e001c001584e01402d048101c0f03504000c84000208045804200180000c6a408146000210034101400c10300c0405c0c0614030040c1018100b0038900b51840015000d1079003258000351040c1e11892100c80a0348803171303001580e00401d0ba64a41d074010700b6284204040d140081083d90250b00b0604200c2d540d140600c1400c0c0600c0100004514101d407500a10140580007410040140149000000440c1007880070704e4200d44160ba82052607070402c020342c5500718a03221401131961060080000298101c104c500030315401034040c03612686001d00082040030b509a0003800d0741e001190410b240 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 77217025 1250 77215775 77215843
    0x1050c0414010518040207151e11030105011b030210060b04080c03010605130b0a0302130e0622030c110409030306081203100909080409020c03070606060e03070e09 72
    0x2030780000c034440d0703111942030004480c9800342211442d40c00e440501400030300c1c42c2c21382c0100442e511840b10684604100391351403040701e0142e502101914511403059603a01d09921800309070031201454a815541000d00003405841d007103032041103981440340c0c040203141c02081158840e605912080c800d80c0d80341e444800050300184030310401031141a03174401a0b858103004010079a400034106228101c2940780364006011b5102e5640d8204520703207004400b58940d045803001409054401040108442910703030b00d050401842203095801d61043c101c451000400d0501003d074040c80d141c80040400e051109010a4a1029660081ca0118103200f0182c01d41c1026085480207003e6517103140203c01c05961b01c0c44203d4800009035071001061101d80502d51041f51180d000e02032081c03d00d51103d001c84101c4e8085103046580742e101198074010005107005410140c0b015140800001d02420082640c1d0300003030044410020840300042c2c0e44a40400500c1d00040c4622240c00341d14086211094032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 77218275 1250 77217025 77217029
    0x140c0909190c09060908150a0c09080f0a17040609060c030521040b150105070210030b031b040605010c05061611100212090d17060118030b0a0f05241201050c04 70
    0x101d51031080c00180c581c00810180b8007035041840c0404982c0c0ca4680040c0180282e9001102b0b0114007140429200d5080202c2c890f04141200244401c0070325003070184e4007542c041001d1560040800041c0001c1d0352282031001222003074104406050f855190649460181d04020031045c0c088030780480441e017244c0c6059004034001c103800407c41d143c1c40483c0f10301c000301c054010701189042140000509122011a4130425640780008906019000090400e042400a81d200902403440e80303056142504c21000280b030242400a0803501c01c0c4d0310181ca03044010400804d0000700c403501003c06000e244c203541d000c04884d0179188480b15918800303000750004591000360310002d03000907100240008410030308035801e03100d400111380034030040b505071500108401d040100f4510b9041c03541fa0740c400d40c5e00145100ba0540c64251a041503501c04555071420f1524505080a003030020032420a500512040c0c000d29401104241003800301c0c84448190781040001d62a00f010480019030303800113001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 77219525 1250 77218275 77218277
    0x2030601080702010b210f0f07080f0604020d030305040606030215180904050a080c030f0703030608010507090303051c110703080619030503191206030303020a03140c0909190c0906 79
    0x41c641c0c840c1c2104900302d500b400c00c0c45400201c02194000e586c00c0c200344e0b60f8045032524081758845071100002c50b0402c20201641c4407680e001103000d005d0018140581d10b440c4072842c009000c50314040e000130340d07520004040503080c10759800114041c07081230b421003c080c0d80c0281c090b051100501c0482e078015403042207100d0181d03500e401c4107580752502022181c065500700c0002c280c0307501c1c1c1d51260190b42e0303c2114030301001e1100300a20152000b000d800381164030301a0b2400104249484075490940740010030035020044004014000681c01905607011503022a0a081c0d1101d2034480c0d8100600e490100c1c6e0716420000308125040540c040c1c0180c1c0325200c103880307180c020203408444941040f051f002c0103120317800c00d000689020b9091005841c20300700310310f8000004180c3c0002c050480d9040e40040e4002900003814100c05034041c01441d0305d04000004102c140c0c6014410030b40c072406141c01d0700d84280e90704408241030f0319404281c2d00c02c28540b020104035050401101502c26506449214 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 77220775 1250 77219525 77219537
    0x303270e04290a11070f110607050a0b010303030609020a1d01110a080702040c050301060e0904020427030905031b060c071e09061203120e030c01060b090f06040b04060815060c0102030601 82
    0x44e6210407400345c0c0d2445502061200420900b1f5803140e540303199010846411020a001071401700c2c0c010040078910741e000718100d0700c095040d414000c080e61184e80286101500410803420141d610550010b81400c1142c4280920071045004236846014040078040a01c5480b034a6028400b00c10f0043c65424401c03241001490680203058a03240401d114007000b02d88828403034801030826642c1c6c41d234000d100800c00201620101c036410000394101c101031400001c142c0802c400c00d03402514843c05080100e00819004079042884d400200c031707141c1018050030f80480d4400007020104175030005030040b41501030b000107400482015004161085a0103a801c1040004064608071200c00380c50383c05917180f0380c0782c02c10b241080002d0455480b1681c1c1a01c400c0103501114034007031080d000a8001c8109540c2c1d50f9003080e0402c030341102150003c82c40b50038100000c11409001904440403640507040c401e03503e46e2600310000c04508900c10f540d800010000700340c0400c103410b41c02544106002d888034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 77222025 1250 77220775 77220791
    0x2152a09040c090509010605030a18030f02010f180f050304090912080f2707030203060a0207030e030601050108010303181206050a05180c1e0a0f0303270e04290a 71
    0x220f514800c01d10460b070304080084e0062002602c0341c8000e41c1d02c407410200c040380d2010681c901c5401c0c410040c005400003001c50201c002c4180d82030181c1090fa200495040c400380600c1d2200041d00c0c00c844100500048500b80c20314104441070056400509a003a010040c406140c20442c0342101c0c1487c2c244c0002d022080060140701c84501785038055040800f000501d0442d5482c0b0000d000803400c1030001e00c2c89044c10000059804000d0940720302c2c9503440240e2603586c035150260003880c0c0c008000c0e1090b00110010300060740e10240103030450303825242030b5001260070400c000143c180f42c0c002586006403241071106020058001038000c2480340b000b0450b5a031401000c4040300340380303400e03070f011600301a206d040d142c035000c1031b000c4881d215600740c0d01d11600000001483c44410344d000120607016640104241034014103540710f071203030030010b4608040c1c01160888082d0040d00402030084d188401040074010590800550f11030900749400c40c845c60081d035881010021206042024104000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 77223275 1250 77222025 77222027
    0xf0c0204050c032a0708070204020d0614040e011404030e010c0b01030501060f05010e011707021006030507050306070f020307031808030a020114010803040501050f0901030b060415030c030c02152a09040c 89
    0x4136000d001c010150f501c0c01e0844980e40d210813584082401e0f684160240085034a540240c414140103169100b00c2003024400401400191501c0b96014a01079240c54074043c0003005400800754001d03410300c5c086480344c0991b4010785540c00814000f0b404080c288001008210301580041c0c01d032800d520660010230344c2c9400444005501f0518280014101c2c695000d50034039120039950440600c0c010703100f440342008400c0c1c1c211181603000366000c1e4010002044281414010550021120729210b40859400d07070340030756680310307100000f42007014040044410124002075403014103010343c00e6a541d5004494001d02801d040041d441c0100c5540c0c00020b0410307800030450f0125070041c0c403410f0801c2d06480302d1680076000390460505164541e00e42400b15034a0800804c0a0108958100b0314600c1581c401011115444400310a25152124400005800003800e4407040c001e80d030b03086019a22407802031704000722020954130000040103108442244179000d017034510000e80302004102c941d07000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 77224525 1250 77223275 77223331
    0x402040e0a210210061d0403020319020a0b0a15030b060406030206030a020304030809030c070b0d0209030d1805010912020409030e030706021b0a03030503010b0309010b0a0f03061415010f0c0204050c03 88
    0x80381c0c3d019804d11412a104040030200c01b241d12500a0065a041c4030003d802243c031406052807179001a04240019030412821403035164000c106284104a0700100d40d1140f00800316600024100700e0010340011100e079a10b80242000d15800341045413a41400003102019401c103a0702200410104000100340d024000141c0d0310f00d2200b84020a1018544a800c40643d4002030800145c55020004e0724019201005200c00b20318480c0d8506144801c907841400307010f80c080e0495030401154a004102030380000400864840d0116000100c00d03000786826503065018000194050061940000c4c000c1d40108070004c044120308540e6440d03117902d20070040c0031201400000c02242c024070060000d034008001556002e4800c400009140304c590f00080d0b00b511442d8031022030070307103912401e00400c42030303012f0030051001d21305030020385040c06448000c8030401c42454904124140d0303902055248030f0040b0807441c0d80c014000308413600f410304101e1850350040313400c140030b41030040d00450941e071101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 77225775 1250 77224525 77224529
    0x8030402040b1503150f190f06110c04020a02211903090519021503040b010906120201121104171b01110d080a020c1603060e0f060402040e0a21021006 66
    0x707443d24615039504120000c50199010300c40d8100c1c100c84285034180e150100130b1414140003600169a50b460841c3d040060222038014104100d10700b456055085400240752480c0d0230111030158035131100d040c0c101d18181404402c010500c40c01085215428078905c014a002d1004d0448821a0600e01c4010b5094036100e003001000b40e031281b60a007000f00b1110246403d0309e48000c0c1102c00d40c1d040030b000039082c0d80040d50242c172052112801008050440d208040c001c0506e9550fa80c1c4c100c00070380010308501c030300c01111215a0340307441c0104e100c07505540c2100d015003441c2c4045200f40014000c120340d100100c0c3d02100040c0a42c802004440d0b00070403404030710f03009000061001c42d10b941d03404c0310400c00c05042c025400350240b00720010604107111080b141d42203a0b2041400f180746060032025038805c01d190700f240f500005c5c4d04c2808000042422603210f501910042442c00b07410220320b00d0711131400f001a220300d00154034070030904161142c040031007800350b08850282014540d2041120268 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 77227025 1250 77225775 77225809
    0xe01180f02060f04080d09150e03030d150f0e040b0604020f03160507060603030f02060f01150503060609120703062301090b01020a020915040f060e060d0f0c0308030402040b 76
    0x164200c0040c50440000d241c9203e00070304040c00c180e6582036a514016a0308400804184a03120601841c65816204003164107149440c0d0b028881c11804251203105402018400031740b82e03c0400540b2424101200003820400c9415451960714100301760240000d440456009480a011961501e05402503952520b04001103030f08c0c54507240400b0b8403d90070200b02c03006114051101d90041030540c86200d0045000e52104504158400d40013414141d00074210190070411000500c101d20600740340e640b0301440c0d4104213030b50362a003034001a00341c00760200860b4029601c0e44644114540850b0207400c07244610010700120030384042d000c1c0e09a6000c26030410800c01a03004010f010300c140c02040c00050180103441c152a600d4000c107000c03c204945042e40001d403040c442d491070606100744182c0f07001d400420003442e400c050b080c125026018000a1040c0c40381010402808100f0464094260344903e042c80800d9680c5005101030f00119001da2007240390405410040c104140c0e17000c0c4121031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 77228275 1250 77227025 77227043
    0x2f090c0a08090303041a0a0609020d0605101404120203070f09140a09020607020d0812042103020304050a170c060f0709050904051e010b03010509010f1503030f0c031b03030e0118 78
    0x101b8441082441d0000301004402900c5040010700401c480c40240300000c01d02a002c1b0340c460a1005000e800c9281c142c004c1e003041007208003c404004070b801030ba42a0b402e42ca08a1021b10400d0000928141c0b654002c000803444901c00001c014185a00500090205038006d159690b01c0300c28520841d44a07502c060741110f4100085001441c1c60700b50038403a5842000042e0405440c400500403600003214104c9402000b004440e4a0400e44900c0080002c410701d420752461501e84d940c00d4590815000081100c00c10351108061005030100b074801c82c0102c4411503a0f0307460b180c070018281d40c01c150f0385000032940450300404c0a09101c0f01e060300c1550400e0082031942000054006117640000c15003525560300d1a0040d0a079a0a01403903004440f0040082212700d6080b14034000c4a40e180d0000d805108000e400300700003600038010302e2002110b400c0c102c10b16450b508007036811007030f40c44100c14071041c00a48d8204040d059845942018802c4c07000b000000040401003407032591608010b00b035025 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 77229525 1250 77228275 77228303
    0xd2408060c090a0b0d050f010506130909030c05060a05100e0f070c03020309040903090306060905040203100504060209090103050a030f050a1d0406050a2904032f090c0a0809030304 79
    0xa0000420b20441d0190200c0791103659040e0007100d40d04088402a50a0b8071641030043d00010b245070540504821100c0a10302200207224046034006441214103060702c40c05500c06060286540030340441d00701d0705071102480c1c2040d40c1c40040004444c0c6c3c0388150b01480c004940e2400380a8030b0381c820b01d100795a9003040d48984030107031071980800c4000c400710b21003040b070000c458945004201206210b81c59451820341103103051800da64031341d000041020716103010800503035030004124982c02c89016000a0307d0b01d503403c01d503019108071425980c02c00f003100000020400d0014501c40d07964060340c1da03203202c1c041d000c100722020300c603030040740c40000c4200f1061011400c210b40e640c20400c0c4010000694150307100040340c0380c0c60660f84001089200f440305140a8201380f500600300f0b022000c0d007180381c181141e0320401070590032403150a032050f51104110103c101e0120001460f03000a008030100e103007041c0303000c040d6402859a40c000036840c00104405c6580002541c8c02168080e030040c00c400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 77230775 1250 77229525 77229541
    0xe01050c070b0615130810090503030106080709030f0803071701140126010801020304020109061e050c100518100509060a050c0412210509150d090203030d240806 71
    0x1000500a264011310038845030040c892044001d2034107041400108401d03038506030300c240c200740c000070113103851070300b8840c017140010310100441303041d940c01d410550304644508908660b01d408980000740022202c0320003034240082e50700554440c03400c40e40e450401410036040c21404110a10a6040e0341c044003011507015070281140f0b141501c1443d804900418644481c1264600d003a8050301841c2d50010601056580c031a49a0020300701c1c9040400148602c070280c004031181c1040400100200498404903e0b0014000480c403890041020b0100c0e081034010099002c01074050b0350414850221860860741640c0a01c9203d0700340c0c4001340480b65618a10070000d020001e22000402000300008500c841601c0580e544a0303000b0b480c8120429400f00401260088540014041c800d0900008096a580143c0d8800c0c010403100c003541c541d0960b50484001e4030190500a46c14080425014589000b80e40b0251400803015201d5039030144c11180c1d003030f0403840c600a00b01d4030380003440001c00c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 77232025 1250 77230775 77230793
    0x1107240c11011110090c05030706020a05070608060414040c0501030b040c051e04031a0403030f0b0919020903011112070c02030a030503040c0e1602010c0504080705240f030a0e01050c07 81
    0x503d6015601c203140b40c0141c04080b60a400d404a03503026a085041c0214101000918007800c1a80028000b2040c903440b4150b40f041c103440f80100f00400600000c50070740b240d0b00311500c1c4075250048001281010300d03081450002600600e40002e00e0004410a0780c9010301480d4604115074654038030306000110001c0300c0b40c03007001c0c1c440700c0c500302004008000741c64107040c01e900c844010300420381d07800c00e45002070a1307851440500760b83c6070510f444a081643e03219150740c1c100c41382c550941e424100d50341660000c2d014402c0f0180e855480c20a101d11040000d00040860303003d18981c0d05120ba8071403c0c25190102c0582e4040e4045e40851041c0000034094001150041d0103000b11114455680142518206003216180c5003100520420071099030240a03214a01d13220307040803410982040616642c070f9190b4452248200e00ea40380007003040f2071035202034166603400100c9a03642d040f58801100b031984191856843d99251255840c82d4050621609000d00c0e075203040703546040310304e0300d07a0804 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 77233275 1250 77232025 77232047
    0x103301706150301080303010618031707021206180f030a05041a0403060219020d02061501030c03060f08030a02100902060904020705030903010509010b0109050306010e0a0c1107240c1101 82
    0x3000e40141c950880303060b14000356000b40003890046640e503040c030301c006282d90a0480402080e40040005100050700c41603441404148440c0e82600c911503400000d6540020307501c405282d00588080c002016910401281030451040c1200d03000f0140b0b00280c7d0b80e0f0b1117061382c880000342c020700c0b0500c0f11180040183c4002008100d01500b4280c894454500700da120704141c200003c0515984d44500b03070180007410380c0d038407680041e141900e070050100b014414201c450300d040603a110003042415019500100240c004480d5070b031029a150308441b5030320350040e120b48015128022004400c074149000349031249502a102908180c0e000d001e00001e50404e46089440303001c00e1080244a803402d10030706201e5a5424008550b442c484400075011007000e03080103020303401400c01400361001d00965a46c0100206000090315a4400822110ba110035070001100f40521100015000c0070100c00079094003000054070402c010410040d500f900d14180c00811598410103800388039030140c509041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 77234525 1250 77233275 77233279
    0x31c0b03030706020a171513020310091508011508030a050a0c0501050f01031106070206160501060b070f120e131e02040e01080f15010e090304050402030103301706 72
    0x1003000901c0e9205401da07005002c48800085c954504c600c00d4a03080100541c102622400024421b07031810023199101240c2c8564007001c0741c0000214011900046200b8018018840c040180d40301d29003904110a0b01c0740b0130b0018940c28030202c08076016410500f181110000f4000f1840d00c0d038248807c1c1d8064114042c40002e22848184140101d6001c0c000c161017403041c02800c11003503040d460031986243c41041d499004503801d00040b401a1605012240800440034000c080c0607002d241c507502401083c0c0021440c45400718207802000004001951814444d9400c5412070ba04200c0841da00317192011401d89c0200d01c0c1c01107008581003580030a414240403030b40040c81c030164500d05016613200348e2220f050401d100c0010819000d05101c618141491503018094440624880020742c40381802248041c0900b4800310b42e0014040080b580203240c003920640d00d03503079039003088441c2455404013800c1418050f81907038034104c50880060b42010590b1203d002103802c4202820768070390300800c7d9235 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 77235775 1250 77234525 77234527
    0xc0c0f020315010603020a030e0309030304180603021c05060702060f01050d0606171605030106060507200d20010c0507180b040609020903120301030206040b031e010602011a03031c0b0303 82
    0x5040d042d00380c030708603019241545001d6a9007000100050843d5255415a251a081401070b13200a076008011601201e59540c030a928148007a50300350001c20251303000070740c840c02c2e40c2c00100103201000704094030540100e05944d01c0b83e0754024241d03100d010460742003031b0706038810006101a24003490862410382c052440002d000c1c1d2100100c070069950410703d04d050b0b60000000b4aa107202200e42d01c00a4042500244121031400a024046010700302c0700804035003401c00ca034601c207400880c482c1c00c1c08000a080c0f141d401e890742441c0a4207030401c0007456480503014075041181d40250006140075134020010708910749412a04061241d42c0d941080c04207869409070409607a40d4021030016241c200001681c540030002014a08804128036000103c814801000503a5601040d0f0781101d0307103003102503a0381e55100492084080c200d00d080c40b0804403000046481a4150b100c03107446808410346400d1901c00100301550780c0076502a40e480d482c1400c1c401e0150315110b4100c02ca080c6005812030b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 77237025 1250 77235775 77235793
    0x4150203090a030c09060b090d030e0d0605040c15030902010806010e040b0a03050303070216181a090901051b180409030e060a080f01120302060403180b0f040e07030c0c0f0203 77
    0x152240700d150f00590b0640700c19581404015103c0c46110024515216010700d00a03004006c50020440000043e040c450401700c80c1c4071507103d107882104425846001044685040e1800844c2d06007180903100c80307000440da8522000b070280c03086040306a01611801025598000116088015000003942090b02e0f0105000d0751340354250004082c504c01e50107151030349041000240b509440800d0501c004008007c20025080801041141c9000210011940e50b1003a00114070040400d820940c000310240d080110400043d03212743d00403007003078100224a482d000e41400c80b60151090000701c1e0b0340c01411031513080c5029400a00c0440c801e04040512021160016107141c10030b111100100d507050080010043c04600160301402580400c1d804684698130001d503030300c600510080500044940078070041000c00c080000928443c8045551035407440801d2000b5003003403090f00900f030000c00100700c580e4024007481d0401401d503907030000c0c211143c6d160020580c100280584e01805080c4034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 77238275 1250 77237025 77237029
    0x203070f050c0d060203041101020d090b0304060b0d15060b0f04090e0f15010f27020a0903020a080106050f0405040b0403081306140f0601030c080c09061315120605060415020309 78
    0x203640900f9004800060316440c040c1045850101d02071090750440d0844010b25204541000300f160135500040391280e22a0b803145000c10040c07100784512640706980b04010820440e1400d4a003c001800318001c0c008070b6540d041d49405401000000c0000340c13014803041c080410641d01c2001900100e03404c482070048900d20041c28485100d4507402101c052900510900e848140080000d01c04284040003281c000104070b02030b04070b55502c14080b6500020170180f181e10680000c0f004d160001c02d000040741d82d03074080c0c030f000740114480c0c940602c103081505c0c031032880c0c0380c800e2a12130354100c6241c01c040c0d543c55a045810700170081185d41c02600d047d1035203022883c030303100320600c408900040889908008003400703124840201414105800c1400c40d070701d080c1d07001000c00d40252202c003496807948440e42c0025551300982c030304030400c0701302d50500190400d4850041c0c1d103444059100d880b1070b05241900c403016540782d8020305810050400040100c001c0a0251342803020462041d40d082038032500c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 77239525 1250 77238275 77238289
    0xf051605070f12020a0611060402210d030218090c1803070b0f030a0e160e1306050405011b020706050a14090d031d060c07050f04111b0106150203070f050c 68
    0x2c2801070180f68801182820903118000e0309540c1007205e50400050003c42e602d0a00800090003110b18451104c3d401d6087d0003044081c01c2c0c40c006444c0140c004c031000500a401200c034500301d0054184000320b0508000301e2060154040881062800e00d40200d5100f0036010310194907050b1045020018900120788003a122038024100c04940d6814020703d0340e800d545039480c507803551341c2101c204459004070800d1840103c840d02c440c0c0c12401d60301c01100e0f00701c103694401c02a1807141040108030400c0b0701940107140005c10034800c040916401d400403a5030340c049000d01c0020030401c004441c000c07800384000c4444007850f04040381c0382400e15030208580207001d007012400f18030403400d981c00351000c1e800100c0c25910140c1c2e02609101006010540c0c0d40d04a2007281d016803100251292107498580050310203440380d411583e0795151804503d15050b200207640007140d468600c0c0441d51003101440400d080d421580218100305150320340030b10054002d1b508440c030307105140c420000368688034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 77240775 1250 77239525 77239529
    0x7170702030705162102040e0a0c0503010c09080601060305060303070f03020d02070618030b090a05010204030308090607030507050315041d010f0e010203060616050a1e02100f051605070f 82
    0x3501035525a116860000d14100440d218107500402000742801307620348903d07440071884408034154400c1728007400414010001400c02005500540d40218140003812410b05c044541c00c2d0000c010340c0c20f072074004072048819070040000b079401c4100100304992181c0c1107180c000ca4002c054030300d00042a5541d00f001c00022400b14090b03040000c200d00080e4040c07102d0f4001386000d06124020410766070300085043c0c0e050100402d245440d402251808004000480e000c0d58000c0003196210307103a0030040c0200e6021148050a48165000212224443c2c01264010a4203858003421610b0f00d440c078007441071442036050381180c0d8075404203070800f41c403400c641403600ea080300004542d031007140c5034030580b1600341a070215a801003040c400c15895020445150000c40581a05004d0041c0f030038a05044006170040c2140d092250a01c2c6584101000090800e2003110403401401d0f004d00180d800341031181400e4081002440048501119440d201c1c8580340324030709131016039855009142e510305640d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 77242025 1250 77240775 77240777
    0x10f02120a03060617040201050a0c150203010f080d02030705060109180501140603100213060c020a09020a030b040b120628060b09150c030901030f1404030c020406060c030e09071707 80
    0x1143e042100c1c94018901c109211001107005402d45002e40000e42284100d89060007042000700d5048180b100303800d10755906035540e0f44155501e580d94003110841a12900a41c940c1d8040c810343c4408c568000400c55680700d90000103898a1381ca88618980241604000074089020072484000060428803d101d0b0690440000016078141a4241460800030021801c075403481003280700c0701c02200108240455241d440c0c1084c4a0382180302203504100b03141d000b550000c2c00410b40c09141c5030560005500c01105079030401c1262080e40400c103000603074605118607900494007040611300306040c0700d0040f02d441560390200c1100b0301c098804645040d03005549840d00440c1d04901392908109803103044103403440c82410001c45155040d1240301e5540700c3d5062540c0c07403203d401d12800d643c03c507485100341249200b809140034200a00070800c505c07000c034422480c1c407402240040c059580c407842207406594900e01100d002c0184003075108050704003028010118042c100e08496a440144202d00ae = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 77243275 1250 77242025 77242031
    0x40801020c06010e0106090506031623070219030b0402100302090315090708120406030c02010902130506010e04050c0702060f04030b01120b070905130f0b130b1201020901020606010f02120a03 84
    0x2400164561034213040e04030208001c40c4200400c42940e40c803083c3d9400001d035406100c8a1705010b02d00b62007d1824000035124a4204a41400c1c1ca02244000d070a4060003079420b180c0e5800b160900d19410000c50100801ca011210041005402c1c080d101c0c400d0003800d41001444c281d06100042e141c4082841061011130f0f0f03560401507203500a11180002b0040c40004210740c005032100a4050b014a0040500301581c404903d01d1041c402d400255515802801c00c1c903003c028095071102a0401311940c5002c034610f20030044050030148201440f4518403c4070307038142610b5500304100d541c001c8001703070740c00030042c0408030104051620741d600811409040c694002503601d0800c20304030b00100b106050005e40130080026071100b004502400d8541240007407130b2000e040052004150040d81c60ba0031030f8a2440841802c2695030207840c1c1e07a83c08032000c03180380e03d0540e00742d801c0c2d00c00c5007541d600680098010a4103940076070b165540d00f84031030054680307043c160300861b58680c12000d007040000761 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 77244525 1250 77243275 77243279
    0x4020d0b0907180e03121012080912070510030f0204031205071a01030302060c07080d05270105090706260a0c0806010f0c150b03060c04050414100b0a05040801020c0601 74
    0x2542d01d291240703e951100e0103206046665011944900901d00c1781c0703605800b0311000584aa448407441d03005400030401c3c5070104e16141c05c0202081e0020070341c2038051a002081e1545070394001035603108845000700768542d0f09082d104110003610400c02c0b1100c40ea0340900002c40000d0220000c80c1141400d075840c980c0311f030007900380f500324001d05d4620019400701010060000c80c6c0c2c0840c243d80c1c89079846400036a01c540318541300c00709110390100c50140901d0a401e200c250105440d4070382d1001000c1a0040e1440401c94a90f03089441c00c0d14095596801401c00f006030b42d00480c201030740808007140348861403488401c40d402d10607086036a000001c0d614030764003101d40c0e002003107503802101c2072130051098003114602801520380c03205c01070031006403003401141100345504100c06a540c00b406680640c100715902100503045400307000c0c4101e0500120a2840514419040c03151b14030600003d20149852448011035000000381400c0000801010074071180c01d00042a1603540e040060500c3d41c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 77245775 1250 77244525 77244539
    0x8101712071101030c140f1605100b0109050301150e0403050c03030408040e0f01050306070e0625060516080a02070512040e060a05010201021c1a10020d021b100804020d0b0907 77
    0x917505802d131006122503d52015400751092055511141145140716915404001042e6140c04401402000c2d4070441c601048a40043c4c0c214a40d0100300303884003101c0e151a00c04041c01d844280c184840c44d500050130400444204641c071981250080c03c042c0d251101c90401c4905540c41181c040c0c458001c002001c00282d103640c01020b80c040c4003007030400b400354101030000c0d4a65a010f04500204416032003c4c200c02c0d641d10b000c80303490240c2c01030341144540032208111155820680c065828a2030800018003075401c0c40030042034100b05541d042d9555135881d0101c0002e410402003a24107201e1b000b1030103202108400240040d01e40710000c1059440d0000c104518030700e064022030304590061140c105076484440d0b080034040190307640450400220310040e03807444a54a145507018007a80e503451006a00406e0302180d240c6654292614402503007008107980d11010b641c983c108411003a00443d10380b2814106420900c000e01c0a40ca107807175900e900c070010300103480c80302d5a0740280c48204000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 77247025 1250 77245775 77245781
    0x12090601081c080708100e13020306060604060215070c0501052509060f11030d1d0f0601030206030f040501020c060a0f0b04110702060306010c0f0302010b0405070810171207110103 79
    0xc002c2510320814411031041c0c0c001c00b00c4801510840600030410045035150b201c0300444409000480c14103503152500d0a149400c0b00c2c8401020790103805494041030360b41c00e00d0000c40c0c040e41c4a41d00100940307040c641141c0b103800030003407540c03003003011448582000038000c1c02014005e0f43d4480303541c10101e5451001500c508e4100c40c60341c1c00c0c0100300d9410407a00e50400c445509001c07550070b00d00c0b41c0740950380c41c00e81184200d62840c03101c03038640782840c00780020803800441c4080080c411103894845400e1106d81e034070420301020354401000e00010b03c502e8080b80005030702a10900001d41405a0320507010315104041e105801610340342d0280d10391302501c5104200311900100d8060145120304200100d03248189500a40183d82c00000603255900400420382507a41c45a80b81d1000544e40c20300900034000c1c0340e100b6100700d08010104c3d081603c1400c40900559400014000d5140b44c990311003240402124580c00d54001c1101c42c9881100c400c1c050140d0341d014100100241060b50001021 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 77248275 1250 77247025 77247043
    0xc08040b0a0c09050105030c1b06250212090d12020c120c010e0f04110403030905090c250c05060a030e06090a0c061b0b010902120610020a060504081209060108 70
    0x2064036002a4800b040d0340f0600410813100207080607503480d2614800c4035800d00c50406011090a4020078141d50701d01e00050303440c411203080003e4240303a15654240c074100d07003410300200010390003100c11040305160b1000801e041d04005106100181d007a07924503203505650514100507070072806a800c1a8145038495840e40300c003210103001100105c1c0700103844611410007460068081c00241c110985840d03100004180c1c0d0111700300d44942d035929009182e40713400d01946003d4481d54000c100d281a40005455030215070151150300031082d203121240102540c80140d0700e10b144500001150307107440300140058900e0b42d8010440b0b01500d0741d864a402009000e940709075110b440034501003400001c00c00c00307541b400d14100c0c64050044144420781581c0c00340151004050000000398001103500400700626949a0120241c0c0c41c08101b2400c88401540703000503810041203640042c1740e650185034030500c180007880c24484c03182c0b910f440d60f09045a0740b01084d4404001032040c42810020400c3c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 77249525 1250 77248275 77248291
    0x50a060906171c230f1308010b01080601051209070504020a1814060f130b13060806010206040b0a09060e060a020a090b0423010e130507141201120311010c08040b 71
    0x1e080021a0740140050f56050307036064210300c542d0404910140100803a5001c00741e416005c4d8403030203255034940758400d0502c500071407580b03030415511081d4094410544500416140c09081c020300c005071200d480310080841203280101100403c1c581e8551000c0d04d00c18500340c0c1e410401005000300e190701a1f0b01a04050006100e02085554540e40c901c2250010789000152075241cad03c0e076840c243d6800c0b100341c010f003254000100306030b500d51920b6500c90084840320740d1211320b2915a540166110765050710058028901c8800044201080d40c1141c070006102d00c40000c0e260745031401c0c10b401c1850580b480130315640c0000b4034000503640800544082c00303003001c0142c5098581180007100e0489501d51071031005808881150316805080c0e00c40d800d80002d0f151034520800ea6017000010039044900801148000340c20305401c809000a403600c411442107400120307400c0001100381c4101514049081107441402c064080c5028011a124044107445100440c02c1503c2c08004500300140742032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 77250775 1250 77249525 77249563
    0xc0a0e22050304030210200a120e09010b0a090f031b050108070503040209060a0506121b040506041223010207050606060702130c0504120b0a050a0e10050a06090617 72
    0x3102141010044400700c90b4103e64903039140585142c140c805503600303014000180185100c4100328500030400c085074034801c550b000d80600b03040006480c8000230b1044243c00100b0390f80148003041c0020010b018542180c10450a20750362400d4003520b01c070540c0c01c115a12000c090070650011340d0070040f240580350908016116141840d801000c5010041002e031042800a01103400f07070710382d48a048040c00024295595070503450035132008050083c1d514142c0a088038103020350f806050303370035101542d03001081180f516181075091a0840c40c3c01c0c00a60b10034905064040c08043e14100c44000c480c5044005602c80506082080c00c28000900303590180300e081182d0401640c60b0b0b8407400c4035019032140005e00c9802070f0021a038074051394100744a44c02c0d120342d1142c240244120b0780c1d445421b444109020070fa66844110094600c203030b4000096030711100305107086075081c0d08103940c00040030400213002a034502c9030100f541d0a9078400f4595804c40c1e004000c00e4241440001100c1c00c5c0a44c0d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 77252025 1250 77250775 77250841
    0x20f160b030a0203130c08010c08070306080d030515060319060501020102090a0905090106080d030b0306060d080a0503090c0604060302090906040b030c1203070b04050106060f18060c050c0a0e 84
    0x10000c80c40000e2016500c1c0c1e5000001031955a1a25002500386801040709001d039a16141414020f0a140070480b000c00e1503a40007c80704c910a0240005588203140900301c0c1c150007031000d43c05098081e003040c00003070325601c1b544000d4441c00081c503c51805201c100b0100d10f4400c00c15006c583e500d400040c11640100049440c54458501303807000c82e85040f4000a0a82c3c41811060040c8010b4100c01001c0c080c904d91207c80325410380003120400c00480c1950304070b8541c50201302d101141118000e203500f409000c400026401840555403200703c844c1900c02c3c81030300703500044182d030180c0c12400103c0d501003840d950301c0c181000d8599010105640c10000f008142001031794030319136218128030030f17505400c00320b640c401c06200790b500880e071000c46100e00781480e01c2c0c25406030280d802400c001070000d902401036284078940e0345c4070010000704241405810301001b00e4140c1c004050a0741c2500c52040c00c88172589400380400000c0403201040c0c0c3d0a82003800e200c0018611101c170000320000c4640715 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 77253275 1250 77252025 77252039
    0x9070f080f1006110a120e040608030301150e1908060f09060417031f090507080f0c0d050705040b1b0106050a03110f0f030d0f0e040203041a04170406020f16 69
    0x81050f00e5590400300090fa010b0381800d850100c6002005298030941290b021104d40c0101c01440c008404940c10b01c151915083c0c1a80c0c1d9010034801c40000d0703807090140f8000b0b41d0050791b2100203918040c020b00010b202d107021001c0d10700c5103070744492a03075403002e020080455900c011150700820742501500490410f5112840841c00780100392442000000100e940b021a25945060110034030210040f0706650f485208001c0600329051002705080000103110700c00d41c000c0e403503c117541c0c05034541d082c1220000010000c100080214050000410010410240b0030000e00848001d030708030003001091702c02c200e500352061607108074001e0710304040a2000850358401b005c40020292a480c030400031000004803c40300c80e45c0000d8150041c40001030300103a100001c1c0c3c85190080d211078410905017010b010881c80100c40280c03000300c810707028030000c01d880ea014541190140c6030080c00d8003201c0d4483c1c050790f03000d5401600564010b5105c4130003c142403005008000035514108915450050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 77254525 1250 77253275 77253301
    0xa0b01030b07200a03200d1d03030324010507021201020c0106060e03031213080c100b0904080307080718080703020f0625151b0305060307080c0d0201030b09070f080f 73
    0x20709000c41040e00c1d00b0750a00c0349411303218440d206000c440841f52851005041105600300b4000303400792401c410601410000100d80c042d168184070401c42c8130000c40c0e212001c0050809040c10880100091000769490f04038180350038503034100040c5d03120904490030742164410390100e402d201c80c511911190355404001d44a0484034520310b20082d0781c403a001e1001c0940d1010004007031101c0802e502030130302000119825211140030041280350402c408004102c0000c0714018540b41c1c0800019003040d109a601681001c07407800c0403080300141c0c0304c0344400d030b0081e40c10191150f841603204005620f00340b1300300180c0c0b003000c0d01d2182c038103102e400e10039003071032500007801060b1a130000601c400c106030b03007581300d83e200071201003085042c003225500084015040e4116001a00b041c000c55054034010643e1412511108001e0041080e010180f040403628a20140e0505a6490080d14113032a5410158482c00c03481c0c1c0c452810300350f22603015041d04406881c1100120083c010020b0714a00d0032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 77255775 1250 77254525 77254543
    0xc05040524120c0a1215020f04030201050a05070f081801080c07061808030c0307030c11100c0c06090b0403110712020906040608010c020729070204020c0a0b01030b0720 74
    0x1d81c6655900c9070b049407451900000400c02600f241003881c000030406240c42038040c40c14425035100c00810607012807241070f40034891407c0501003080008200540c0603a00a0042002c581809400c0c54070503118110060020141602c002c880000d82402981c10070340c19101003e000d0802d110b05041c000c4000c4442d00ae40da200402c101c3e55240c1c1414280101e41461034000e901c0740302c4507664a403450301020345400594000020a05081c1e60010040c0140100c0380410f115000800c800d101c03040d900d0015108210154080c0014048400d0100341d2500810408600908d0a1100c3d030606180040c540c00b00e040d0444650b40004200b40034044a40b0880e070b0031aa0105c4452102d503c4207000100102065448200c696190204080c4900d0f0003268102c102c440e4640c102c1c40c2c1d00340c021400880e800c0341c0d00c07207400c4000c2e0801c64500103160a6000d007070f01c0340c42321007200c0122009989481141c0f000781c2042e17400c0c0f0020f804004a00c1d51060064004004d215000e564001d2a000e440342d80c0e00c81d00f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 77257025 1250 77255775 77255779
    0xc0302070506250204110c011b050702060a0305070e0303040609030b0f0118050402040b280522090503041d2401050a050a031b05070c0e06150f090901030c05040524 72
    0x2103038070150b41d281e03040fa0310180480c0e82855901d02c05014001c8c002e00040a4003c0080760400ca41003045008109a07060b65802819041c604110b0b59012401004003c050005100440e20031803002d0b1002c00250024004648510078100d0460410580c012030081c107050249100d40010320010034009413a24070100d540c58042195100d81c40042d000c0e0801c41d5465400504504031450b210725000405540843d90140d06154103440710180010000002d0000103100303980c22101c01e81d800d555000a40c6070b80280280d9023010b80356140361a8501d440c4540e1210520b03800c0500098800c00100942d81d0001003000500b85004440040c207030380038440410040c00400701350050b2490107900641c04031125003808054522415030090981c0d046034506580038040000c0c0443d1001c001200a40245d10091498411111882d854601c6600c0290b12540d000e0381441070303008079280d00485078043d612601100ca02282044280002c40c0e400030110384c00416504e030000000b1462100b5608403e100f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 77258275 1250 77257025 77257087
    0x5030c09070207051302030105210d110a02040903020d08070504030209010506090105071a09010e01060f050925051c0218011103040b0f03040c0602060f0a0c1e0c0302070506 76
    0x41e452003682020710582c8400d42100c2010683e80d01800c4ca13034000c6050710421108a0700b0b44449181d03403005c200e0300f07202c9419140c4c00442c0180d0894000d1480403c64040c0d20222501c41e000c0d40c0c041410b441180d00101d000d42d0201c0840482190084007655100f43d0524055003020714540000c1c0c034004061140500885000400c4801640300c0e02c202d80e1456040400400f000c408030307400489145040750749600302e510b003c4040c4540d410601032101202d0520348940070550516003003040c0340304050510010501a4403503064044501003122202e84031b95190f0549401041d02d0702c00c514103110040159041c810000c0c200700301058515082154020300c2d00084208100c01d4544ca14800d03038121a02d2400c000ca03000015440d0940250f00c1307a8442c81c108910980c0d02e605c103981e204404d40c0d40b440c01c55040d00005035540040c2c4d00135200480f41d031234040000c8031000b82083c11981a400224005100319014a080c1a0104070140080100380c030024900003955540d80009403080690f0644049 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 77259525 1250 77258275 77258281
    0x40e03120c030a02070212070513140105060a1e0c030e04110a0806062b0b06070818060d1a10020304050d060b0402040915080d03050402010807030504030c0b090a051605030c09 77
    0x3c1c141d030503101c00c180c0c0070741a48044c2240700503041d41c2d81d07090310420b0b2050b040d60506200455003802801ca9844d41100240704a9003000c082181a4004881c000c080200003100703043d400c041080d401d01d1501d85a26180c04051280c10006e00010703004240302e01650408280305103010006044a41101c0c45241c20103064403044001041442545402c650303001500d00c00881480b004911815642c5048800708180c20032042404894000e052001c2d00303c080030b2000481210403d105501100402080c051911420080f040104c80c410144422889c0346404043c0c45410002c40074500700407680001e40c03c1c00d2815002a0014010560007480661188215080c540b20394055034054040120203200e9410b0b01e000107100880d06100b483c001d0710801040100150080c0324660141c1e03010307912420151f8800c03009401405000e842102001001410f00000c2541281101e001740c0d0210054440902036041103890141541c0303d503008042c5107103080165a4000650000748101510900079680d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 77260775 1250 77259525 77259541
    0x1051003020d0f0203030f0c0714220e03030c0c0c030c03060c0a02070f060216090b010801120f020a060f020c120304050909030408060408091002030a09090f1d03040302040e03120c03 80
    0x40f400e40c41c000e42511001c1072207500c00490f8806804038600d100221a5000d6582014030076404042c0704039504204c501d401c1030001d4006050520b10641e41c0e16012524440c81d0a50520f140e00440c0c480d200e10b02c02281c15034100505100c00c6103c0c040860040c42015000400242c8801010741500e0101000282e03406c035040c002d000743e000816001840c1c0d1031803992008080e40720006103c5218540700164000702c2c01082601c9108000c11043c1d4603440c5580c2042c400490302048510282d404102c40c14002e0011b0703403110040c80142829582d01841c498480c94080d1038400e40041a0740704800d240020a40c100002099400700c810481c1c0241807600c0d1500f059040d0312075034012085c03501a10040105115040004065103101524210a814010041280c90f801280607000014018813402c01c00500c440d000300074001650000020f00f0200c4910200c8142d904508250703403a007000c0741c20400c0d4600f034410803a6903800b100146240c00b201c0a00041001001000300d48031400101c00700b130a074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 77262025 1250 77260775 77260793
    0x5090706110a060203040624060f030b04110a0f09120302030708131a1c0c0c1704050a0306050901060503280507030b0c0706050c090d0f06020904060f0609050301051003020d 76
    0xc1d40103a421507481c1401c0c180300000d0440014147c2055980814510040c02c107915023004995141d40d940e41d500c502c0b100d04170007030100d108103e5401070711080d401240d030413500c0041034800140e4507050440c0b06000000303010070355143e000151041c400700c034400120b6008801c03941e40d540e100e9211a541c42000c1d01c0d84448458035040f8909510441c0b88402ca50003404000780060034101380426104600c1c0d80c50002995603008030758000410714038200740092400b000802c0c190003070130402824240c4410110b20080d00540c02540d00c01e850b030040c0401d44200703114000107048150060725043c0c0d1180030350500c9070201a03200381c0c1c0b64410455402440410712507100955030008003c0c400e030824080d901c0341c64003c024141d60461610001c00c2040c0c24140880e000c1143c040c0501ca100e0141d901c4894a030b02c00a41e040e01e030302d074007009038002c40d43c1c0e141300b8040601030402046424905202e0000c20940003908054000d81c5010107000d07406080410348001c807031381103030341c415254100d10709581a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 77263275 1250 77262025 77262043
    0x5090f060d020f0a02060406050f0121020103110d0606140f04121401090b09060709030c0521070603060312030504030503190b09090601060e061e2a01021c0509070611 73
    0x6140d00421303400c0038540c5c04038003280142c0c0182c80500c120b840d000702ea8542e002c0c0a1141800e40000380e400709403030240b11034840610f28014140010081090a0405a168020a2170140c642d540310401c0c03049680003240341c0c19400700d480e0b0b810708160032070000d80205d2245001c4d201d01407100942d140704200c0014802c9254403500710003809501c1141c0b410344c94544043d51451344070b0050703000064030544030710600001c680d040303c013041e50340c0d15140078050001c140441034040300b5030602c602e03085d120007005020020066503800003080b43c81e5003400040081900040e104150402080c0004070303030f11034240d0350040c140c40d0280d400050781601140040205100c410340040407001000070001c004180745040391680d44a842d4114460020084c15208000301e110001c0004051480328100b070901074000320115100c040341c1c0720545401d0910030140078034014400da4001641110342d0000401019228203954000e0200e41000c2d1541ca85409807806004200300c0001140c41c032012040040010f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 77264525 1250 77263275 77263297
    0x3110d020c010902120c01021e010b090f160206010b1903140a0518010b031002130803030c070302011a100806010516060603120c02010c03080702160605090102010b0105090f060d02 79
    0x140d290180d01e0218040e120542e8140e105008168000d02c4007400403c42e02c0348050143e000d0100c46540c454500b5004082480f13554041d075a6101c0d000700e94071448005809503a41c0c4030100c4107840d026000f4004000601c6000c421900302500410404c2c1c0c4000c280c501c007980860340c480d03481018200c120000d02c605040a10100d0030f0300c0900c6604211513005c24002d04131241002c080b110f03290f0905082e40c864040d406d80641c0200c00090490395142d020b00380d45805c0241d80d03101903607526003191641d08140c0b4844070704640003c0d5042010340902c202602400600700c0482107040000026250355484c14500341480350600001d42c0e240e01c200200c480480c007510818502001c0c5080140040c0301c9030004590940c0c03180c9994074000c2c051424070030032a41c140d642000c642402c2d0f03400c5402000181c01d01c01075100c4e1a0086240910095070b010240c803155940300d48449414000a00755020b0a18050500c10204001d18558035020202c40c04594181d404c5a038980003402000020312494000003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 77265775 1250 77264525 77264527
    0x307140313020a230f151b010c03090b0a0c030b0a0b0417030f0f13050d08250b0109020a14070b0910150e1302030610060909090b0703110d02 62
    0x2078160100320941200900a0300c0c822603441d00c859486840f400b1a810740d03001151000f00d1083c1c03514180c00e481c42000c2010302141c800b0a40c000500c5041d410200c0070340c00b0a400381c4604081000c09119601381207445107414403820340305031102080250043c0484080580314503c2d52800350098008107850b0030003038142200c15644006020485d08680030b0b0700302c00307055030648103402c160020541da0000c150381902460a003194041c0c909035801000003010f00325180400040507500c81c081c96403070600a032405903a4440707018546080c4000a445e10040039407028009011641181d505810344401d000010303641d00d0650400c1d108006003181404505c200090004100f004400044c2d0090988404884070403030a200148103031485410841d4025400d810100204100d1860756034010055022014003090700350003107420104c0c00c503203c0905114003081000704607401034840300180080e803800c01000e40c6e0303952200d500910161405042540b650000d010209490741100c102034a50b02c411 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 77267025 1250 77265775 77265781
    0x93304150f06020f2107031106041a071b02010e0f09100806100311040908040302120703120f0507060e0f0f07080d050f030a050a06050d080c0d0504031703071403 71
    0x74034160038003070040700c0040c010040b041142e5800002d40150400025000c1c85c3c840002d020b190803a0740004000350100401035800070301e4081e051014501581c0183c50541601d14100813018007580040c180004103d0000d000101a1403003032500c65105030f09181011110711098001030010315501502503110b0320410034444804001c1c0c00300812280f105040d28241d039036912031241f11554510000d04007400b0381101c86003038681940061100b5220780070850810340c07690013048a80d080d81e075400743e1a6004210900038482c0300b041c603c101242c103280c651071813218490020000c5c01040c00c0100840c2c0c03140c44015060005020740d07090640d07044125001c40040d0344a0594a440700c0c402c0c00032500a2041c01154903100301d00b15050403e00c901c1a074a180c03220308802004001c001d00130950f00d503a60300042035a40c1c2e900d000c405198002c120035500ea0780c1c0e02410a0800005180c0c103028000208010000640e40a41148881d000c0440d001d031245d484000c152841c0500307003090012401c00100b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 77268275 1250 77267025 77267039
    0x912011508030705070909020603070c080d020c010b0f0306130212010b04022809030308010e06040f1b03050a090f14010e0303040c030308100e0c07080c030c010b09330415 75
    0x150104034003034405c0790a001d0b601c541100c00c503512288040e4022000300001000c103409070f03407020f90301481100c1d4240741a49840300c2001300d03003042505e0300b10740e5194288084030303141460300346070f614008901410107814041c000d00400b41909200034012050b40d000b0b800c1402e0b082d071019a42d1039010b8030941d81c40c440e13807074903003540c044030fa060854026485070342e00d404074407a00d020411359034551a81c02190342400070305091810020b15042e030140d02d40e034a4500c0d0743c45034010403102004107911803030b07251030103480501a20310003800c00840b84c1c41c226a000200d492501e100300a150401442c01442d505041c1860251500314403102c1c041c40b000043c0b100300554980c81c80201c034000c0d9600d04650302c130003c111a41d55018800c2c00517413880d04001c500604e440200030300000384145105442c241c10340b030f5000c1c02c542007009801d580365541c440304e00040c1080552141e02c074004448142090003000d04424841420300e4044c11030340341780110385400d500c1c7c6030b2100081644030803c019146d656a21 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 77269525 1250 77268275 77268277
    0x2070303021306020304050906040e0a0c090507021e0a0308040302070b0f031506070201020a12020f010501030614010602120a0503130807050c15040302030c0d1a0a06060e1203091201150803 83
    0x884120b0004a040c00003e0b1180f0100640d01554030040070101103441d41400c02010741015075944106009002440380019120301c00d040041c89038200205062902041c080d003007040d2400701da0614440c00c03071440380604001c142080030980c503080905443c1c81d10704089240408540180d14840e4002070762414041e4030f100698400e080c900c03081c2051114000a1060070b01801400a000d0b074001401040000c9480b000340d03110500c03510482302021000c96002d1b0075a5020307803060707070400d66406842c100c41e81d00035060350146c060307070004000041030780d03035132031078903c60b82085604011001c80858180c0d03451140c54000c1640294015864003064180b040d210440a04214402c0e03000c03189500000e2005410b480440781c004010b403e08a40130418448400c9440004884090750860240c2c000c1e0344020080d0b0046200c950700080140c1030080141c400118614501e100d007a00000c040e0201c8000000c8a0300340310306482c0740c481044030f0200c07280074000f41c940454180403151408200c03008000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 77270775 1250 77269525 77269537
    0x21020130b03040c1526070e04020a1706010c02030d0809030d110d05010608010f0303080901020c010c08040314030f0c070201090312023306010804030908070e1e060a140d060207030302 81
    0x181c0705c428403a00c1d000c207440d80e041070135044910198480c50b04161900c0c460800380c3c07000079411310742824a810000501240d00140c03c0f4408a50340c2002055043d52514500354854021b00301000c14030100d4001036600c01c1011000d0041154200c006424510140b06840c64400341e040b041c005200c4800b24040b01e81c004146103c1c6003880c0500006400d031146500d81e0480d00c0c1c01e00c41c4e80b03d4a065880803642c2940042044419640810075411002000d1090090b42d251554400925040500c0d0003000311454641d0607084610038006c2c0302100200d43c0e001604880c030703034618035955612031005035a00c5945903c01b400003e90414112011038001c14101a041c64901071040d6591030441c000700151542c40c05407020100e0b000000f61070303500a10495030005d0190800688007580d800d582031070031045400c120301855083d030910090a4400003181c07880c0b0400d01c03502505d4580a000314000c1c03400e030710a00c000c0d0030034802c2a1803a916083e621825aa82040c0e0541d0394003402d08004d00a0b500103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 77272025 1250 77270775 77270789
    0x30303061404050c0405040207050c060c0a021008090d0e13110d0c03091511040e130308060102030304050c0f012006040201020f19080d0b0904030e01021020130b03040c 74
    0xc0701c0400245894800c403440b8a060081940c2003d04040522000f50089203085030240f2510f41701d01040d698132009405410000e01c003e003410400c0d4414822090405050b04040c044003106000706c1d040d001c2103501c43ca0302640391100410364000c0c0054041c5200c0c1c10107040e62031a120301a01e03040e00f042d00504601ea1903010071f0200c4481034100310115001c10030060b140410122881c1d11842d010f40010705800a0410940d0410352150210107003083d040e251400b0480700c20000b10708258000e0801903000209001450941c40c15031916601d50184862061091024200014141c0e0048008580d10003000c0000210b096a4203040f40d40c0e0f032801c0c2c43c281e0243c03080041c0c00c050800300061520f45590204840b6080841d03668500456800000c102c555403601c3d0043c64109071103002140f1b114601039501d105465140f4000a42040c9a180c0b44030032490410601141e030741076158050740f500c1e030000e0681c0e5030b41450305100000c51940350051244601e00005110610104041000981d441 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 77273275 1250 77272025 77272049
    0xf0605030c0d020603041b0510021b180601030c050f07060605031e03040e150402030405060a05010f080a02060306040603020a030507080607020d091511060c120f0103030c0b0a060e0103030306 84
    0x9440d0800c1040300500e07800131352065041000400040c1262200311001c40c43c00e5011190640324800a110009140714801c0141e028026488640041c0c00610501d80002e07500407407804800030b02070703085a1000b00410305160701c0e40c42000141d4820b60131902800b1542034015110a40c0c0c0c64140c014202c6803103510700c648035001d14082c252550f811314801e1000f008000b5807400f0300c0d028003852048002084d0315410781050300142e0301900d80e40025031080c2e209038041c29070340c07402445040c101d40040c0c01c8103a00040e0540d061240340000245262a985c04403201d0761295150000a00a0030702078000030740140c0503100010030041e000034182c00b620701a80c00c5e50304039034881c10100c0e5201c81d41c00d110b000084a696003040a103402c2203454000503000c0c50301000980c149114685000e02c1a00c29016008c40017946441d020300340d00c02d09800c008031b417100180f55455614010401e03240241c01901d0364809002041c2141c400d80d00c00e40082101d110707400c02e41d683d40c0c1800b5000b428648610159206 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 77274525 1250 77273275 77273293
    0x90201080a0b0303120408190f020607110304181104032103051006082706070201060f03020901060e0d0c18060509060d06050a0b0a0b0901020f0303010e0402040207020109090f060503 80
    0x206402802c1060303a0250041d400e00c9078140d071007415a82c1c042e0096071b030444100010101c0b5880106c44100c1180a61552503ca443c1500001c1c42c01300010283c1d0208103070790249031444030020080340c080320002c800084020707945400305402400711110081d16100001000010003492a82c01c040700e296142e0710030178045510b50240c0994078100d40e00010b2500c42d070024009207001e0294960000c0070010500a43c0c2190b0454880348a41441c1c6900c0590100301080202d5509000741809400d0032500c0350a410715540c0840c0000406005600a0020a8a001002da140c1d40d10049006402c488414000350781c440e680003071120f6151204580d01d003040c00c04030703a50400c00760041c00350102a00004072490a0307100c02d4001c00d40a132903c000b40d80c49094081039995501049005006051f4406039144403001c000781c6400d4600c842e00409420a000400205d403103401d810364416015180075076955220310040381c80700196009941d0045c940603171480f0440c1d007584103a065031026800c40f4a844 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 77275775 1250 77274525 77274541
    0x803160209060108090a0f0f0209070c1203060602100c020f150601080606160605060301020436050108030d020a02010207020402030a02030907061b02190512150109020f0a030209030a1509020108 85
    0x100100c0c0c0e5050703607074481051b42000800c080705115040307000380312003160440c80b40d0005600343e0040c1daa4400107488000a0418400041e04858040c00b6034202081590303d0214040d4881801c1c48080d00b01550352413000d26018001d00070643c00c501140142c401d18182d01da01803001100941712140040c2403000003566901f420021113a007103014508850b02c0c1e200b41d640d503901401e8000c0c075054055400f400001020300d421420700ca101c15001b2010000107810321f011450a01c0150300780407400d81840c0042100280200481344401030b00500540c1d940d91041c010b90191180800083d00688000108600036003142e01460161029001340c410749641c034082103441080951360b1110212041143c80010301d44041c03003e0025101314040000c10b80da03840021444e1000c0d50782e5050541140f0100481424512242405415562001c50800d240620300351840d020f02e241d00e4003850b0b0300049211203135908116426a6a0784100c940d403140c030004410b04054420020101d0200304480d02198a031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 77277025 1250 77275775 77275787
    0xc0203030f010914160909110a021203070c0201050706090b0703050601030e0f06150319080903210904050415050a0e010b010302030105060717070f050c010807020307020901060e0a08031602090601 86
    0x42220241224030f26222001711101c101c0da415030034802e01c0000403000403a0180350058000c52072021400c50b841b1741c20319401a05041c042016803000310801c204004880303802c400c003403080b290203207071460300c0782d005107072050092013001d50142002b2000d808005031240d00da00880d10a10081c0d90510141c02c0d030900310b035074131400c84003c4450354005800284603038412655820500782d00030200c0d000990f08015a000030150903005544194002446c1d010500b070400c140484949080800c0b103403081041c014803c54003881c00803e1203542c954012909010340540139404144003100104218102454a00c00a02c055656140c0795400d200002940d98040d1080e28125440500500d18000305a6640d059a00c1c02c1102d003000e080c818450940400d14200760101c1291181c0c00400041c003001300054500b10300100304034119801007103003000503141e00794083d044402d181400c0322215400c10006028003440d4000e100d0307912020409a42c082203000032191014000c1c0d400030f984d80c42781c0c0011911 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 77278275 1250 77277025 77277041
    0x10603141c030b0d02060d060504060b0a0c0609030c0515010e07030e0a02040b012a0209010504060815040c051201020d05060303090a1404020f190801080c01120905030d0c0203030f0109 81
    0x20444a0140380114203009402c50304007440f00501c0007a141045500081141d00300040315900d2607521002403103282803921980010341044680d50742401d810340e40003495001c441500618050300c540080d000c15000b802d8182d0714070740c00003c3d5020b480768130300203440c1080300748201d1145100140c04501c10300e0181c450050030508030030103044022443c2c1c0911015190072403805041000410002c001c1540031009110025882040c0c8204800039004021141e01b040c0c220511982c80c1440400c281000050b45200800944400003042d40e5981024a03041086a124a81142155600c41c03114141907008150450300d103001006140c50300405d041c0e5900504010a800c1b028542003400308180d0b200100001a0004202602d40300807001a02d40070307049003110003491802c4e071800480d0181c102c00f4281c090300d00c850007450030109010008150608100d12000004d030350300c00c00c0b024004144203d4184021103102844026144c14000351749a004991891304036011100200701c4009074020110 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 77279525 1250 77278275 77278303
    0x10501020d0c17030112060609060b040315090215070c1212050c030d1a121b10021002030f01050a0f1203050a0522061709030d050601020f0f01060314 66
    0x800710780380030603a108042c048081c0c82009030031218403460011400258041d04510006030303403082640c500310040d14201d4000c1c1d50000d0400c0300c1402011b00d0380c82580d08481c0c11002104011301d60600d0000140801a0065000b224041d60340c20500c3c6440000d080c0c1e00e2044411b8984642c1d100181075003000c1d0001c00405040d01e04c4403486d0711621400140c84800002d2060720f160040004090040707400300351021000b0100d0b020b00807041c1c030303203800382c446892026806800f8000e44402203100f900808084070303200328446210040c8403803003045407000e055180d141c11907490a2008036003400c40e40c244100c40c86000b40c4d07400856003903007008003403080300c101e000c400041c42107a0780e00342c3e0f60f60450702c039513401c003c1d0512840e10700254508403680e40d007610340600d8440340d007401402400500101c28032103015416405000c000c51002089958803449007000059503258100101d082046c080d941003800d03c150440302c078400d1010744c40300040301c1c03042c0b83d0550140046c0b0300e03540e203403800009200c07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 77280775 1250 77279525 77279533
    0x14040203150f060c070609030b070503090d0f050408011d01050603030a020c0105181c050c010e0a03140703080708031e06060a0c080d09050102180a03021e0105070803040b070305070801050102 84
    0x760682000c102003800c1c070100900c154248100c1d40c0800c2e280444a5100343e00040d50003904005214243c1c0d00160012000c0ca8024a10302c1d0502e0207543d204081380040702000320000c0c80c0010300f48548180c90240c014000240121091742c2da8103030b81226680f045000a511384008035016140020444100151a1b0050852010200010764083d000034803059000b6084003010303102960740c50040b9008254511201c0d44130701c0ca900700180303000e10b2040c119041c842c01e8000074240e584c40c0c010042c01c40303610a10f0090080422441e56040032000c1d440249aa14041060b00070440c400c0041d510488500e480d0505001d800d1500c0c0507200b4003611001d401020802c01c46400320310a241e030364495401003560900c0c100200c205642100c0040100351140d0358082601152100012103c0d01c0d800c008544050740c0c00e0940c0c00203403004c054004050400c9019040c0910315074014416942c0c62070701700e034166071280752504105040c8502242e8800000786480b0009001314061044941030b2081a4028 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 77282025 1250 77280775 77280811
    0x2506020102191d1305070306060813080c070e040f060f0203130605070207150f02060c090109180b030109030503190e3003090a02120d08070c080c07030b0114040203 72
    0xc0d90450110448203c0340d003054042036003da00c0748074210301100300e184c0c1c000886103480700300113007240c545030440400c00021205002071410b912595101307181c0c1001446a0310142e005c0c2041c50002c4983c032442a030303010b1901700300602107440c0c1c51011460081c8030a2200b44010000d290407407100f10f68290010042c0c00000b0003041050f44070300e07441485401221142e51b250102c0d02620340d01c8030300103400251018041354036180c0c10b0200b640c21404000c48241440c2107a0000380103e030090103503400640d4010260f104850803900450607000024000301b0460141c0c0c01c00a0007940301302c8000384041070780e03060520101e080384940c0d8200420711018202c0700c5004120391720100d142c1c0462070b016083c505c00c2c01c1d64031114000114060b01481c03009100d4000c0c244180101d0b11018049200139400414058070a240c002d13090991018a07445c0011580f0200d00d002202c41c00b40144405180c407403070b00c010081210071001c5a042e615002c1c60901c404c2c140004000c26480201c0c0c032400f00b0300c404002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 77283275 1250 77282025 77282027
    0x70e010803031803070203011508011a1507020a0e0a050a0c051305280801050406110703021522050d080903090d0611070b040f0b06010906021c050408250602010219 72
    0x4120150391401524500081500000c2c213403005501c0c03180786271030f11420400002400b40720302500c0718102c061003021664000c0001e230720f03000101d24200c0540b400142d103d0440d6101c0841c43c0103001015140d06190a02c0080000113200866042054918046015100724000c0007a642681c42c40b04503d0b09603400d00d03003480b00310131020200d4a001d001c520120089841004a0b040c00b8007041000041e01d8a000c1c140304060300c0030006007004400d420401d58001c00d601184004000d02007881165058850303061020102d171400c01030700c1680146580041c1003000200309101c48044075629200c00d900e5000c203060301c910505500d594000340710740c3c1400014002e50070030803442017441c00b05820503c0d1621100d400d1076046030200d0318840038205280070001001d0900750002028a4840303605414188041d503940c4040b0303c842150703060380b28051324051041c41210090091303a4155460622031311740303180c01800001c000c00c0341c280b00b03600040ac02d0b520510079100300007002e0740308580030742c5031800c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 77284525 1250 77283275 77283301
    0x8061c151a062115090c25030c02040b030303011d0c040302030d0207030b0c04030209061c120201060302090a151802280e030a0206031605040515070203070e01080303 73
    0x744400094034071964240c0c1e0340d5100240952402c180e10b0300ea1001280198094800760080c0001d528110100040c146901c800100c1c1d0352040c1c1d00e1070000d80e983ca02c81078556540d4200481000520007100000c401c2640c8140b0b40700307840d0310a50f02400401545010580c6030b000034024280040c031280300b094025504174107060741040d40500c8492400c0c0d1a500800d081c80038a420f01001340c0c0c030494003001040210fa121542c44900c0249140c00c0500b1640010b5807d5009000c40d0311075403040550400c20304c0c100172541902c0d5030010720013000704080036000e40640b00074401a031040d094100001c6ca62602c03402180748501d9040d007140029402c1180400540c81f03507850380040d0701d5080c454a00c41d45800070000300c0d10b0b2080e2608400d0040e0b10440240101d03585440c0f0b5000750001c442c0780e0010303121a004c0d241c101d011007440d918401118a4100c815000e0707544016403020254143c40030104620000b040654025000c0d03450701e41c0c4400481400030020301c1411230b103600400001c0e41d030b0345001c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 77285775 1250 77284525 77284541
    0x309040c0c05070b120702010504020d060b0402090d11030106120203100c05162f010f030225060501030302011103070207120804091d0c0103090309030609060e030a08061c15 76
    0x209045601d15030035202c0600d0b003550364025181c3e4800000e40b03081c0c194806245590300005507c024495803509601042d404414440018821380e116140f950403a9959019070300500005468007201a43c2070810481502d002c1007614000c0d441d00e00d020481070000760703d62082c550013900801c00c0040104400b4000c20321030710410308200061109601d180c54070307520155200d008441d5a41e020308450039910301c1e0a03680c1d100b07400c8000e01c010700954598000e121800c1c24001c0c1d003001615a103001c000580d0070340e00781030380c0110008010005801c12450780c0c402416203020794002c02c01c00034009504407862200f070710740002591104c40100300810b40180506d81652041c1c0d5101c0c14541ea9107400019a00c001c003088014204170300310682d1b04030b000c1001c1c0200590034a0144041b2016841c060b150700407078000a080e05440303042c41824812150810784800c46000708595070345910349001000e145054826510030102d8083c0c140460300c0561030707201407d03004a016240b4170034650780840109409 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 77287025 1250 77285775 77285777
    0x30c0a020712050303010509010b0304030f0e030f0d0909140420040f0f05040308060102010c0e151e0304110d030918151806090203090c010f03141905060f01020309040c 74
    0x9090301290308102e14456903805403003400110f03125410034080040a50050308000c82151040c002c00020a500020850309001c1500303280d0801107149000c40e0078100407002d805042c0c82546190300e00706a0040038401158404a0f0402912036803070512422a441900d0181902164207191030901c11800302e202c207229002040082c0d100c1c00c10140301c01b9100005c401c09041681c840411060541014a6682c0204240f0003007001c20385020002e04800d8040403501d0140240803819101c0d540b52100316401c1c900104051416240100b0500d01660b1044808550013424220340f04854188451120034855150300e4522240e4108900640d10085c0350300001d1001c0d8444280c02c030b0780a0403031420300162a00008403d420048032a1070001d55070f06601c000d442510400810503250b0000c545880b51040074030b400380c0304e0484060110050107000007013924100a20302480044070380c4c403100081d4401804400d00141d6115020050340391403014403e805a0420031452000b45440d511403586200c0d1317 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 77288275 1250 77287025 77287033
    0x9030d05030c0d0f0b030f0d120b190905071101090f02010804020d170904150806040f141605041a0a030b0c040b07050a06270b0a110a0903030f14030c0a02 68
    0x144103c01429526000d4000080558546a900c900e04090064032086000035006041030700e6104001060403d90040d1041c44e50740e13680500c00d00e680d42e1510b01d03001c0d83c51030300781e02e460320b0f2500302050080c0030a540310004030f900038070040c2c04142d040c0120588560001e001103411009074005440019000b48120780c0120701c9050480040d107181c0c1115442042c40712200e03101d03840001070004440b00000402041030000000b08004003002624030f6000e58807190140c0354080901d020345200030b504031982c84500445480c440914542c5003088100d52048038103010304e42608050795090401011016002001010203002007036003006010b4001050203005450140e0754210981550880c4d0b408407030642004000900f4044a8041d0300b0081c0d00e6203448a42440500c16140c4610740011002030407200000300007611042151b00445840407410405551501c41c5d05000b00203200500085001c40c003000164221b01e0f1103424030314400000d58400300d2540d2540480c5c0742054002400300c07011485 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 77289525 1250 77288275 77288287
    0x5030606030706020a060c121407030506240c0a0506010623190f05041502011e050f0a09030203090d03020a0210080603031804020702190906081203040f050703051603060e0309030d05030c 82
    0x9894810427501180408100c8014240303000000e040d04c102403c00d40c403660914510050042007040d4100c0f0040480107815a12001103403468100300d00710030b01904a000e004000a610364100c4440449800f02c0050010340c5c40300c1044603141801141e501210342d01030406035034100b500580701c8890014250804900342035462150b20007407a401909140180d4480c400c2070348400d04426014903621b4405024486454001d20412171118014003102e0081d85400441050500071310480311000c101910341400b0a486042c00b0307507114001c103003c074018901002c1144100e03106992040c001c0200a02440c90704110080d00300c401101c400314194410341c00c00c100300050b0b0b120050416a06112546a2461031812340e5010450310f9135400594a0741111042401d00e21a80045a52040d400701000411294034245107183c940039800040403031140c10030b1894614212081c00045a204100a000c403071400e8980c17035100e00a104c86079800d580820b10110a0074011400f9550100740940c0c5141042 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 77290775 1250 77289525 77289557
    0x3020108060d0c0b090306090a050a02011b020301050a091b0e16030e0304060206090d05070804050d0f0203060c0d1a03031624061410081803071a0105030606030706020a060c 76
    0x40c3c40c40e4010040d4141c0000c05280c0c2d0308050220591003c08080908800b20668a5246e01c0c2e0900c01c0c1e000703040059220707000c001c50515400c0c60034041d401400810080c9004190f0100402902c50196080c041c030301205035002800300c6401c0c0596240303486c924040d8035040140054400111200802e040e1281c4d03610000340700410180005002e10b44c000e10480c241704000d10b041040c00c82c0004100201040b0000124148100311000c51f0300c02d6590341e0f00035540b400c0c010880c0c58507040095050041d0b01c2440780c080c40314405481c00d4010100b0411901c827003800004003a003100c44240d90103402c01e101c01080b0b0b000740f0402c0b2000da8000c0501500d0310710b542804078801014188103a040b10360754034082c071a40d0109144070851040c00e5581540e00740545401038104007000b000184040200000500d200c40c05005582119600844042c80b1100303889602012000c00d0107800c2c081c1c0304640024030145800111903007190386e5074001d081200d0241d20f480000d811610300060238055200c045c81c0c1c1507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 77292025 1250 77290775 77290793
    0x2040213030309061d0906060405060d060608010b070201020a02040b0301140103120305010902030f1f05030304060503040506070201270318080619061d0a060b031009050c1303020108060d 82
    0x4005944900c06428194940903045111640102c410800c40841e00e0448800445c1050b000403011265018160356510000b0018480c9801861700450041040441d050081d089201664003d03140c8040756a218030040300c0d03c0c0110840640103902123203c035805414603900018115002500203d5412504165100d0090782039104a504086108000c100b00c0d50500c07405014080b015410340c41e40c1044101040c0700349010b40b85420b000b410020320040b15178680d03961402414094283c03502c075582c1e01005400c91700100c5060700c07103029010000d0410741c4107214100525811034170a000c50341d031103036010702d482130804021424000880700c64081c00b00a9285d0400402c0340340010009860544150bc02e0391440c1d1241040540c1003460600a40384800b6083d0030010b13101c03030450010b94810700d4403c041d0005501c50702c03e4000c00001e02030141c44400d02d4100b07482c04c3c22400c2c00b20782c58051412036a44100d0641183d003242c02d040c18801903201d40c64071030700140c00a044400f00c2245448010079 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 77293275 1250 77292025 77292037
    0xd0f02030c07030f02151503150916090203010b0703180e190e062802120705070507080a02060306130f0e010c021213140303130e040611070c06030209010507020402 72
    0x85200441c81408241c0d01c040041300071019440544142c0250308151411180054030043d01e112500000d0305242e02c080065041d012803800046003503051030400b2507102c0c011761a481c50212080c0b1000b1984050034002c0b40c1c1240c400d40c05451030400309403001c542d0b07040900713240e8a20840c4d400c1d0002d880101184491b000d050503074040350f40c000d0715906140450304400c0101d801a00420108251603c3d080c1049403200e417111034448440c00c825030014000d2151542c0480188402003c0c04160b9a00c60090110386109104440c01c19465082c02c941d030761a500c0d4000e41c003172020000184641440c2c40b0980d8488298400455403400000c0c0c3c070000d44504070300200b4681e540700741380301c0c0c0d4541c10441e00e1018004a00014948980c90940c1801a0524043d4880c581c42a04003c0c6080e1001c0080f00e003035812810340c00c58121745400f4481d00b50340e400e42e400d60f0628180560000c0c01450202161140c0341d2040103121410301d0280141d0203074100b09102c0741405070902104001da1154001041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 77294525 1250 77293275 77293291
    0x60c030b0108090c09010303080910050c07121107030609060b0d110a060306050102030316021c080702010c030501061d1318021503060a0e04021507080315030319050d0f0203 76
    0x5400800c0c4000100700050003465800e4036808900140c00380e80702c0e8168581940d40615102e1155a10140518504100407040d004150f02d040d04100303400c095140500701840c030558580a4021920b80b00700c511343c6000c43c2503109600807090400019003e070b0301c0040607a1250b9400314801c15800e00140d40744185110507a29911000d0b660020791a00c01008009000c042c182001001e0a0400003552404014500b49600b1101c1f03015410990003040300c3d154403040414245080445080700402d81c6005840c035030050760030480c000c0c4901e4000e0150038103035141da59407440c01c0c8a0000386415285000600a600015001c100317030340c078242500a900100070210004507191005205103d000c818904000103034010600a00810780c2d50100d11400715043d41c00b08140f1034882d40001012202213031010342682d0030003d06070040084910280d88100e080031909082e02c0103100c01d15840780310384001004840751b0154400c1c0c3d07440c040c01c045d02069224820001359401152080d0f0100d038002d840d401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 77295775 1250 77294525 77294531
    0x30c060309020310020c0318120118060e07350d0e0109080c091303020f010c0806011e0519020a080c0a05070f0e010e0702031303140f030301081018060c03 68
    0x5020b5003010040c44006000400003117140c107403543c0601d9124000d906000811070038206052034103583d0310741d1038203200c03010070000c208480d26541041a09000c0c1c0d041290f240d07041250300803040307a002c41c1c0c400c1210400c1c000134401d0348804d44d8080c41040900d403210000b585601181e690071204204410000030580c495619894800001408141e030030b500c40b00e1182e00c100000e15450311200c0c1c400703401c0440740b2150108000b462801364246141d4020f0003010b50300e81022800c1c0b00e40d003c00b5060290b202070b2142c0c00070044d403c10240c2c00c1303441d061840e80400c40030000f1440300042030050001d81c003001d10655200801c5540c4554055003c103a44e5081580003c10640c244a424003440340184240044110420300c1c00740e04c2c0c0c90b43c0c40c0500c80e1a04000ba070500080c0242d0003030048845d209404074504101f0354a0b8038040181400700b041d0a507441c1f08812601c01040e8001084905a038218401440d207107120005c070b00d000e007075008000c80305601ca0703c000c0c900107076481c020a201c1511a071404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 77297025 1250 77295775 77295791
    0x30801061206140d080d0213030b01080105060306060112091a070311040305100f021c090c15091401020c10020606010e060712120e030c010b0f0307050901061107030c0603 75
    0x70040035600c081c69016034a00941007000c21410f10030100489400d03180d68846a099003803090450081602514010780001110021400810400700550b480b41c02c1840460b62511000ca08981c0c0840796a07406610450103c0e8442d8001c1c0c0c125202402045400305840855035100045409112404514030113084180300303485415024141c12911803048142c241461915196942c6496900301c00ea00ba81e11501c1002c054143c0e0100c40d801804000c07044404504011510300501300501d0940321100440b0000c642d1060703504400e0070251181d0744518080381083e107040740104c000790398503040d440340742c0090189480340d4081c80c0781c2d8501078024240c1860031200140191280c912150f00c2148108150780010702c060701d03420035a410ba8601503015600c409044001883d036000d0f920740c244404501840d48036015007000e500100184c3d0000f2001c440c2006150760f408550068550100701003006111a0b031080b180c451500044034101e49120380d60752110304560b6043e800c2400060344514034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 77298275 1250 77297025 77297027
    0x1404060c08090a0f1b170f030405010c060b030a050f030703020c01090e04030f11010e0c0310060503060112080706020414010f020601240e0a0e0417030135010903080106 74
    0x2038980914140c0c1041d40e0507190080c0c100d070300c070880580010903454000a55034180000d082e4640160040d0746044185aa201d10072130003040e0104481480340e208a01d055035000e01e01005450032502d040e124401c131a012503540c01d01a107910301e49103401d4812001c030070300410420408a2071281c0d90350003459544025060084c00c104c140b5910f5418030101410400c680c4100300d61590b48280c140c03070040390001000d003007161300740301da500d8025140d800c0c50000d283d078500228039001d40b501c044084070041c00364822998203071101303481010303895000000104844280d90501c0c9280a214250043ca011019076a00307040340c106d5044000c541244c4511005c81d5604074442d59031495080c0010b100701d41c0740441c0349c1e140c2c60199944554a511002c4e011440c2401440c02250714032000303042c40c5030340d41c8601400d100c05504403400d840c0c0e070500c2d45a83d0885030a05045a05075410411058629040754001221119400304110040035149550201c0e1200a1084200c00e500c640d40301c203115490200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 77299525 1250 77298275 77298281
    0xf01110c040204062105090a12180806100e04050d051303080301140a08010923030412050c01031d070608060609060d0b1329030f0f010605040f1806090206040801140406 74
    0x2171141304a10b01401c1c010503440001e242c0f0f030080e500a01410f001078900070100c82e0030701d07000010407140b0ba481c5000b150900002c40c2d4030384504c0b2a603151079441991450042103a0a06460240c120b8018440311028940304500500a10382d00e40e441403000c0d9542c0c0d4a101c0f42c0e9000341d0100b441d8580700c0100280e24500203603503c0041428100034080f29055442c3c00d00c40b0407515050400106000c95000d03a17008061080e1001442a03401c00360503113a581c140181c0b11303800c690b403044c0040c0c50b0118074061028074506188580000c200103140c007070304208007900c1c81140a80a1503002c40244010902e0340d64820041c044900c09280210360310540005100400c0c81c1820101941400d140c0408812114200d092394294404200c030040010001c000c2070500820141c540e000340600c40c0783c000c42580c150090700071034406907000c01c4550a47d00c1081c0454588181819404800c100008045000f513040312102c21700040c5228a0290b803071a000e421101c400c2c8011070100c132804104010f2240c00c1c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 77300775 1250 77299525 77299577
    0x70501051506030604092604080d02070b0301090f02090411090103050c0c03090409082107090b03040c0b070309090203070309030809010c091e03050d0507050f010b0f01110c04020406 80
    0x3003040044a050701c002041d6010044c061401036903180e85000a00c04108a42c4d0440070701d400983c886418150144038141d400390160342c805224080d2110b44051000520300101da12140346642940d0a00f05103401802c0d4040a5400d580c0e0244668841c0380c0d40d5114000c000d00425900c180e45010702d00015040d244001c003482101c440034000b01a0820011003120200e010880b070000d01c1c15694900000280281c0106100b407101c0300c1e403201039810540714074500841341501d40710001907076201524154402110000d0220400e2a0108104d9000b030010b40000d5110b07042403000282c0b40c4010314220b800c00c4a80400198a40b043c040038190840c03201d5801803190f070000d0140940c1c00c80013500c2010180f081c420000304655a103c030135140c0369140710246500100f55aa010991240100190016a001d072202e0041c0651055248014403919500240140800c04950303030150055481d5200b8940000b82c42c0100400d0400b81ea40b90310050001d41825144c07401e0405042101d044211120 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 77302025 1250 77300775 77300791
    0x10e030d091a10090c021005040602030106080a05040201050703030902061605030915041d06010c061a1008070f080910050c03010f05191e15020c12010b0d02060703090f06020307050105 81
    0x502407116540d21150400305442c009030020030f0110a044081b861f11450248140e00949008240300801c842c540046040b210b0a9031030105684444070914111103050750000c2c00720b00200444000a40260402600341c0d000922281c20400c54289d01c003d80f9002d00c40c104d03180d8100040c5100103190145482004140034450141014103024403003015100c14021a110f038081d160015000360300c1852404549a44503100b130044024180640c8843c0b880300100a20415800400004145c0b10381144e86c030a40d002e50710180c5084407403030161160480134092071201e008000301000844018001c180c040d28808064580d29890000062842e4060380c11880c461300400000103c0221a0507010041e9840301541501802d042100c4000d01c0740c0590041440e00308003e08a00c16540100c0c4640c2880700649001c245a4000b8541500b02c0710200c1071035512402d400446c0c005810b003c4041e1182e03034402d08185881d9a20f0348070800d050320040c0d01500050b8800035104042107800e01550b5001002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 77303275 1250 77302025 77302073
    0x60e130203030f0d1d1605011b14030f1b06090a030f11010603060f02030609011a070b06030106080609101103100603090302150a0204080111070201051605010e030d09 73
    0x2640002e882c1d02c603844a940d400b01000c1a0591002095030014801403100702143c0c4d50300021086154590346410241200744d4006400050194040c1c990610700e100c03d80d880d07002c0d07241e4980d0781d0741d01003820500c50010361000303001204110888a004003088030710b0210f011112440d80e0042450500010111103054100050341c02c002398211152800c140c8460a02d80d48100b00035040c240102066840030300200e080030700b400708010b42c541c0218001d04069983c3c400c10b13038032103441c8031801d4100605071806080400c4500080303855500d0480c2c0002c4010004100a90740d8010f0302d00d40a021b5078000071540010b418072076611b10500c43d0241c01c0d01c1e0b4003a120300b585002150b0b80b8a0032000d119040030301d5168002c070001c05100340074417010869040e00303014403801c154042c00001c1d000350007103201d903600c0e0480c0aa44016150f090710f6010f41d0594885285c5078004071080a8142040c8080701c1640d268030101e501d10703030180003400f0072403940d40000403400800e04001040a001812000342e03545 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 77304525 1250 77303275 77303311
    0x80d0207030209090a0614070305070e06030c09010c060f020307170618090307170c0c0607020d080708070503070f0605060103050601080105150f0d020406090506040f0302130e03030406060e 83
    0x1801003200d6003120340481c1c8401881d610001118208481004000c014501c0c2401d050728000305498140d000c2d000ba40c0c3c04000c5943c07109004e9a13044040c607500c5500600500000303c0c1201c1c200d00822a50b0410300d003007600c0000c6640e4800a959080750315484898000c0b0420010b0340d80300154040340c01c00054010414144207002c0b40d40038503d800200c800040c80c0d80000c1e403421042045411003a4061040841c814104901510a411900601e8154010110f00303071342c64034141e41039542c207a40043c0a1907e000003542c642c080365202c140100e89030f0074240518404a04144044c01410f405014865203203101c1346080c00449200034915814140f6007030a1202c3d60b64000308042c1980d0040e02d0902071a901000b64040740d00030302503000081c0c1c5001411001901c1242c0203882105c05584612180544800810220b40614010400c0500550b00c00b0009490000890350400328030b1117000a211201c425400c2c2958030031903041e07640c0d580ba1941001150032144200c0e5011300a9008500200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 77305775 1250 77304525 77304527
    0x1151a030c0403030309080c1606020f0a110d02030a12030c030f0603030e0f0301200405040507020705010503280c0809060a05060102100207020f0a030510050a02070f060903030f02031f080d 83
    0x1002e20f00000e800c0558914502c1c0401c80703014110b82c07c4c0f0f07023040c08a8110003881d04059803444554003d420050080c0e2140303000802000846d5201d0560062981006140070001e2006a20503850160383c5445507041040101c0c98a07841c0072140c11f81540c001c1034a129003007010f001d0714034606502010b1881c148041001c241d002e000a4104c02c0110345054503010b4507400603000d8644031031301c081004d040810b6404104200c000405c2180d00c01d84081c08075a4a05806a80301d000e0361003614081102000059420303074000e02c0040441140d00c0740100003c421030503c2040354201d5000314089800901440b07852031003080696440a081c68040c00141b4121000030b440b080b140e00803014207070300418a40d0440d543c490420200074409811010144d50304d080c415941e969115404124526110111f040351941d030085458142d04010f24020303181d5142d0781d1130020700094500750201030750360402038400481800214012855481d10744004c041820394441d01035a030b5441171006601140a402e519 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 77307025 1250 77305775 77305777
    0x1a2401081501170c0406030e03030f0f0405030408060c07050c0a050102031b0c0607050616030902090403210516020705010503040c030807030207150302030403090e071e030e01151a030c 81
    0x508010007600410301400165000d60b2000300580107846540d0412507402c1d4260060401ca030000c1c0c2c0c0c140b100c200036401164592009607a00703e5540318800c0015040390810b6890754015104c2e01c100d070300c5c041c0d5909034142000c03410343d62141d4903803001442c0010311404200255243e001100c40c51015858280080d40d21b100c0c0815068a1490f400c58444244d8014011101009401b40079140da03442d1515201d1384038402207801d1541e400d81030035502007407071083c0314001e06141d0142c0701c3c400d40e4a40c3d440903581c01090b044003241003204400e001c0c542145902410740141a2640000c00c80e00a0040103403c01925801a40c1082010300400c00070507903003500c0400701d03900412150703546c8090f418100d0801800d900542600612001c402d00ca1960640c0294840c2c0e0080c5e07a6954480e440d0042d014a6140039500d45000510310b40304035036012440083d1046035595420300007140b404460250b400e440d2031049447d0b120710365281c100b001408004a4200c855060070350341e0324610f0919a4620b00e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 77308275 1250 77307025 77307031
    0x40806061f0f1b020405010306150e07080403080411030a1b060509090105060f090306010611010b09040b16021e0318030c10030e070302120d0e0f030705010c050a1a240108 75
    0x300800307030f41000341206000d0307561400c0070f401400600c0b040da12802d0503005081001d200921419004d000005c0040c2c0113080c05004400564440c26079490b151412601214003400030b0760505030000b0442d0302e542e010060780ca04148034210500d02c01d0054960022a001207500035405d21504001402c1f440d5a20715401c1c1c1941c0c0212a51034075181c0c000840a00c078090020b2960701485400000f00301d00d504910440c1c0201181c80080c81101285014041555815580141142405070120b62207000390781d03003a000050648100c5911454601c0c0544a4003100d18040601d5000000c4900300303501f410440512601c01136000305060004100414081100092036508150351340f45803160080090200d81c0c021034008200075102004010855122500b201e01900400c68100c807402150030441030311907402d4401005014002e10b400015150300400380c0080f55140601c200c0e00b000205030102c843c15100e003502081165160942c0c101c00c114440c1004890652604103011001e607a110402ea54 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 77309525 1250 77308275 77308277
    0xf0b030405030c16081207020d020d1506140102011b09030b04080409060605090103050a090b010506090a1a0c07060509030d0e010c05070b19030603150b011103040806061f0f 76
    0x956030366141812400c50150b914001c06030301030049450034030300341c84001c070b420303074181d1029600a81c01912130f01c2a10b00c9540300007904010306d180440c0251400c0460110564016603401e10134504501911046440c90740007100c0301000d19601c071203076590901c180b0100202440000d85609001400030300045050320000309852800c2c000070702000302480585000340403003102401074544500014100790403441b4040d0000e4600300c0002c244609a0203001b46554205007050704a9090100740041e40c1d02c0700d034031241c000702050400242076403140c50b02011070141c0200c1e951990450b003101424541e807944130008110040c0035603010742d5030201d91440b500559082210080c4084801170f18009006103000c0c1ca10b0084030f40000d01c00c50702c20010511060007006202d161410540c0503002c89010b4040a08051000c600d14418002550300c01108110141400c00d134801c4194107003880c0d0741c419042005560016824452141041c000208040c83c22040140804500505c008e02e80304003269428 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 77310775 1250 77309525 77309527
    0x20d02010908060108100c020c210c1e0f0111030f0d0902060307020109030f05130b0a1704051605010509060703031e1103010503100c021b0103020f0304050f060f010f0b 74
    0x41168020740c0424024203040081e41d8180d03940b07051840d11070340640740c80e40039903080001c0a1407583c130200d03401042c0d000c0100074820f0110407d40c0810044424850300e003580c803c808075140c2aa030b03400f1610030242c4101012106c00c000e080c00380944a04006200c5060140407100d90307000c454080150b80308605580512505c501d01c0100000107031040d0740700a90401e40000901081540c190840d841d41400380e12130340418022804100c0701441002003940114940503418070250b04410020140c01c0c107146402d550178542e00c40740e0b00325100180d404480e281d0101c044c50807500c00c20240b00c00281002d007080c0d81000c0c6250b000c01c400c1e11420100400b05981c400c08a0064058811100c3c103211040004004007065541041416803085c082e0034070a101c2d43c55a003440721218056034a00041c1540a031000003543d8100c0c0d120149007008041c1859000c0c051403020b0601c07040910b02c11402031000b4510000281c05590030312002904012002003c0d100500c07000e03105900b0042203070050b40c001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 77312025 1250 77310775 77310799
    0xc060b0301020f0d09050c12030f0717131d010b04180e010e0d090807061e140f04141504230a06170703060e0a0f0b0d050d11030c0a02 59
    0x6030083c810000c80d5400c080011a0402e40380c1100d0b0b01ca050700ba445101200d400f02114020010f00100700121505194800c10040c15621b4000313020b000350a1040744490189103c3d601914515001100c900c0700014000d2010400c00001c80d204500d0502400031300310107541070500e00310b001e2240e800741200d06000c20003629540e200395401500d02010090080021260004041e500c4140504d44640012401840130402d50b0b40403034400103c0301943c072407106c0c00c502201d203200f05a01c5d0341d1451003801043d1000d140b03400c0e08480100340451245000701e507250304124804112031204034100e4052003c20308000342076910801150103503015050f2810005901041800140b00c0304147c05030840f0b4081c0b00000c1c0f1542140405078210505004440c0591b24400210304980140c41210030704886880440d11040c00e41d445402a100704800204105c024440410040b02d600c00c01103600c1e500c0904020407043c0e03c05401204800d0060145161150001c0c005550308484000030f4402d40c440680 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 77313275 1250 77312025 77312029
    0x30207050c030a030e0a170615150f0703090b090d020103020f1c0f05010b0a09050f010c021e0102010c0c0302060a0b041d0307120c05061f0f0e0411040605010c060b 72
    0x440c1990071001011607126500e00e00c0c1c0100916201c1e1030a1340101100c04000c1882081c0d183c00d00440307542000202400c3d6512007030b003161001c91150541d001800d8401e00e1320750441c114010510700c000088010703995006440c00412000d2103030300803501c0d103a082c41840361958035801c100003826024a405603c50a01006c1c0000c0c5106981c90000c0f242c6a14920031500d07491394200755404c0303d40301c00c100b2050380d0b9525004424400c0002d080c002481610040c405450216525202c40780107141008401030303a98003007400c0b200800d0b4402c503080b20743c40301c2404560342406647d001e103081e8501b0b01c00c040380e03a03500a5940e80018103100003d541301c851900298441d640010307100c03194a0007594083d064075038040d8803035001080c01c1e5075500348580c202250500802e00c5860032944040103080540d201c2c03510500a549003400c01e00b4040c4120030010340006d808003070001400d43d0b80c1c44041340703040c030b0703c1c003824203501c030514040c01141800c5040245070381011003051441d410120214968807a080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 77314525 1250 77313275 77313283
    0x30603032012040f05040b0906090109090f080a020a170903031b0c040c0504060f03061404020d09050d020106050906040507080c0d1b080109050615040b0f0415050a020709020c0a0303020705 83
    0xc000e00c402c81d4040b40024400352090010710888400361010800041c80000380511080c1c101e41c055040400ca000400000d40158041d91080740545050b0300c0c410300c1a5100030300d030303800700254800603070114060744280041280c5000114030b007800741c5454a289500420386034015084454185c01080c051036404a00038010940281c1d4010020020200a424060483d420900400f8001882d07482d48090b020700a1250360241c0315418807444010414a04000c0694082d4030810f4246403102c05c9400060020040d8425001e6243c0000c1500ea040100340280038000a110701e204030306002c280400c05400c002d0710f03900000e80b07400155403055101c0300d180190a02021601060500f034802c2854640d200f117225050314180e480034092600e940c402c0010300d0910452a1034034140800c820070107040220005c04005a10902c3c40741001d80c0c40c40c00a0140750ac0d85011404030300001411140a0740c1403200901400b01c031b010450a001c46800e919a032007000340002010305500150800038800204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 77315775 1250 77314525 77314543
    0x221425020c2106010303050c0609070b09100203090a030819030902280b0301150f020c03070e13051903020606090417070c0308030a0f0e0a050631030c050c010306030320 74
    0xb012070b101075031360f81b40003007040c0d1040003064203d004c1c05002c24218140807441400300c9000018907800c0908640030464902912611481584810006960240c6542c0718080007107014280e40e43d11014486040e140201c012100d00303041515028101c801692085980100301c2c0071155600401039100b1004c24010900780c1002405104c00310001032810560348681d090301003c1d503510000981254000c1e42d07200e28284429906070011181441040045100c066100f840054940283d00a42d100d6505011041d802040c40340900a200f000b40340c1c0410500d504443c081c1c0b10380041e0700e401e40b100b1040c511070902c1c7c1103595200050001c144581c5501040141d5005503c041c0d03281008007444000b80308004015108a00340714807003e5680000c83e00507034040c0c001000d055580c0d6041002e02c02061806d01ca111020124200c130407052600d040241c280d148070340c1718098601403a0034080c0c5001c80042c0c107181010300304030050000a600460746030000108900c0e05244000e00c2c044c150500c1448 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 77317025 1250 77315775 77315839
    0x90c0c02060f0a0306050607020d1104180302060906071b030806010509090717160504060c020307082a03010603080d02130e090a0b0a05060609221425020c 68
    0x440c4000b400e201e00e030028000b80c691920200055a0707103001b07101c1e60b40508a406984040f4800c65000819403c40c0590b50702c2000034070009006000030108600302040140590040e03001308100f20900d40200819504405541031051001050034412090440707203c100404006030710b00482e9080e40568260b40207040d0080019a803407502c00c0c1d00500c18031a04030581b405410700e101003040040302151000300c01c1d800341d480516140c00c014066800300841a03080ba054421080c00041d00030007400b404404c0c484807410200030320211f80c0c044481c0c80003126410f1180c0d01d02941000081d515804484030700d90f100070003580390f0b84c007040e140c0540109903000c1542280208100700c03200401040840c1100d2003120040059103560400904460007110100c0e0458410001218180b1b0b042d2100d01d4049007511328040310444a21300346003039a0000c0c0d6028540b441103030901c17580144280360004084448001400c0380c1c40090002591010411b041500400c00d1580c8050101007a8980c030342c0daa03000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 77318275 1250 77317025 77317027
    0xd1101090206041a090d12020105060d0305190207170706140406300c0504090f091109060303071e03030b120a06050c04030203030f0d05061824031b0901060216090c0c0206 75
    0x1042c14487c041c51441e0001c4001035280200040451403d10408000c154250391044e0401d1040f1070203800b08080c004200082d40300b0f144000641c0092042c240c490311415101030321081d49050005800320700c005400996420050206105040d0320115082000059031100d006880c100b01c807034000400b000c06040b100c10f0400d4416881580c1210051080701d03406481041402c0500200b48100c0d060060001e0407150151807000711480d19000f4903420140040c00d4903c1c08215640740910240300740e003031030800380383e0101281c103158061040070b2030b80400ba2000c002c2010040e11041e200d02260382d005150319521008035140582c080d00361005151302a04032969880240e0706508107400c030b90304a402180c180000540d0900300401811200d4049100442c855141d183c49852000c01100c04c0e409184a400342c4c1c1d0055036010040100c040c1102050b010031942c40c1010711034851710580200040d50320500300c41102d0704501c0006800c50f8100c0000080f2000c1104c4219986465400043d42c0910 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 77319525 1250 77318275 77318299
    0x303040b280603020a0b070807062409060312081e040602040914040b01050d0209040303020a05070b07080a060603061505090406050d0813080705010e090a1407020d1101090206041a09 80
    0x10982e448241941c1c0200d5035a503059a546030305010a1054950041001d5020701c58840000c44641251401011851104802c010034503400c1461751f1942e403100782c000352109010000d101003603591100207941458240e8051420300454085011040f104034840d20311000050240807450741610050501c0100c24090482054040c028102c010360341074580861110000400e4500102c4800b12140c2c043e080030059951510140c00035048413113408240003040120f24001654010001e1180d403403920340203890b0400c240d11001f102c81c2034200340c00341490144280010881441c4400b030f14942842d0103a62a02c0050100780030702507690003150406400180361080080c4000070b00510b61048400810042d951110140c0d140c01d14807400c0c1c0071440300b800d0001c15040c0246000d40c0107109000c04107000c6840c1403549030368682120008016040704136080c2041d50b2102c021031558520000074003000403e600068201c0c8507038400c22001200401d4202e00c890014001e0319030000004080d090490 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 77320775 1250 77319525 77319601
    0x30e0f060c071404181214120f0a0507091203120204090209010f0c031416050f010203060a12020a050919020703030c0806040203040c030602090a0302120d080c0a020303040b 76
    0x45140141e15043c5043d4008104508151150005101201d0b0202008124030b842e4510303500910802c0004010b50801c81050103100340300109981925090000c2c40f51500c94801c0840c51809400c00d500d941c18241401001580658410180c50030305c15480400003a520b82694400c00b1010300c0060300c4d001240021b0064001d902420304620700307032110b440051140c60200c501004400d00180400e00051604060107170103401f0304400305000b284280d00e80640d403501443c1c8a011032240c00035079000401c0000700e0804078400e500410065814500b02a80c0f9400204001e119001c0e140c001c1004900080b401e0340206020410608450421595052a418000c2c090800f101c181d1005c90076010104a85042520899100301d4000d00c0c43c0030f0325030a5540e0702000e548201e40160340a504008040090390381d0324040e0704207404250081803216100b8034003a0506000401c2e05211402c14056068055000320403a50700c26440718564486a981050640034400d0407030700141c1c46498219800041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 77322025 1250 77320775 77320783
    0xe06010e07020705010203040f09150905160909020418111201080706090f0e15060c0106090204080601050a0e0703150b07080a11030f0d18060e0304030b09060c07030e0f060c 76
    0x45840c2c0e420f6400f410744440c0103a035031b81301c2d80c42000303402c141340481041840c070664003a80442c801e5581e00240540d40d80c19607000d4030425941140301c865070820018220b82c1105101006015560003582410f181110302d903550303140c10650106087d1141040000090510304942c08142101811800c5584443c44285d41e20b01a00822000c034a401601207154a007a5510a0480e800b4058201060ba6200f0048003900c912490041e040042801440341034036085c041c05000d48014500140c60b54a801845450000c041c2d00003400395510311018031172010504440c503403020007402c0105002c503c40b442c10703403100345582c48040c0d85038011a5200802440d14018007a040750f55507040310840f000803466889100303000201081c0602040850000003080c0c10001a400d003507501e40b0741d070703c001d9151003040e5042400c45a405400000f0144200030201031110f820482d800020111442c042c82000f000b4445c800000d01030120034442e140556850a0701c0c5001008041d0065031250400343c08507941e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 77323275 1250 77322025 77322031
    0x21516030c0b0f04020a06110717030c0c040902030606011b080403080c0c010206090c010f02010e01050903040e01060504050a0b030c0d0c0306092301030308090a1a04032a150e06010e 80
    0xb404a42d0208405980881d02c8501458008000302800f1b840c0100076500301089071a441034500030400c00007452943c0707039000310501c2410b402556543d45d140704c0341810801d2004100d4892450a21400c02580b0300141242d4008420b0070106540c401005c0d000e0001b04600320028058000090003204000c1c05030040d0040c4440c08040310f100309a00001643c0f501c904803003100d0141c0c80820b101c0d80961080d40841141040c0f4000061031038003000070203080d600110396030f15107640700003010483c941000a01c41d0052200b40361032400c103030410b000900c10b0300e40c901c940c590702d500100118005200f608226180b890800344100003204044c000940030740242e100b40800340c0e240012440483c0c00d0346000340d124640649180e0740c40c0e030070766030240c8008901070f100505620908a440001074000340500030200142103603126503103000d11b030041c890045c04c0184c01350381614100115000d400b103504103500943c0010029003c02040707007200001d085410820f4860b101d1440002074035403081c5a01340c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 77324525 1250 77323275 77323283
    0x203040e010b0a020615121c0908120315010302041503090203010e12090402030916091410030210031e06030c1418070c0305130305060604050105120703021516030c 72
    0xc0c5a03690036841c01c0500a1140c0e62001d82c109400148240e10801080d45004030000c000c408003142c102200c0b85041202c090f122405401e460841c00c4194110070060b0042800348002e2040c0401003000068a0002510440f5400c245524091141e8000d0301a180074041d103400400140f10061801009070500c2e48003a402546420803c001c00500450105001103070740d0741862901c03114200b070200079800203020b400c5900504003403550651042803000002c0a00f0744000c00c10031140c41c604a041c0d0000303030480302010345c0501d0420041e203444d8100b03426101e80d4100007500c103001000e1191415a03c00329100454500324022041000c030faa0600305460a000c800149c401d000d600f845080010320011080324100c3e0300004401a20401c203401c1642e100e490014144454420f46040141032900b00311601d8000c0400c11a881c1490311400740140011160324445044c00c90795591548024000640650190140800c504000100300d800600490101e140c4255290034002d14040201e18129 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 77325775 1250 77324525 77324549
    0x9030d060501080c040b0304022b11040c30021c0501051e09040f020603040b04060510030c06030c020307080408010501180b060a0c03030b0306090105060112090503030105090613020703020304 84
    0x72031654030600000d80f094015040c010728180c1060303c403003a5904000c200326401151505181114800881501460070f04484a04070654080c0341c00000000090415030113689040c41a40382150b1000000d078041c020401040810f014002c140007140c2d00c14001c02101500000340c20800d91954411a01035035001c0c40104400d980b100304011242407482141f0300b84030b036203140000d0300e850301a0525070024422008072007825255404501e06800880c4c00b965820140340802c018130a080c01150307409501c0e0381c04144003500f50796a45856044601078041010342d200d02d440c9a190080003210340c4180c1203081e031601c0702e40d1511054080d003001d00400350b442c60201c3c00d05012542a000381c114000b001442c09040c154011802c6030350501a040503001c240e04c4d01c3c0c807141240c0b420701101b80900d019038004505460310a0024000854100c100c0c58614a07160002012030000710607281522021a81c13159540c407840d00081c8034860307429072908840c2c80041c0d00010160004014030440c0c0b2004060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 77327025 1250 77325775 77325779
    0x2106060a0e0c07060213090c1706100c1401110c0102030a0e0d02030711060d02340305040314030403020306070801092007020d0c0801140105030124060e03010906020309030d06 77
    0x84815910680d14505030ba00c2c10b01200c800a803254002e002d034400c0786204c400e1003a6982074814151212034002d000882c401140c1d0820708140c025005e58804400d032425400400305c0d40b0001c15001e94400060403140000310b4400c1038940a4214074005080c001d03407642c84214805003076000b58029600c014040c0d140545e803903039619001c6500d002c1e500454002c0c60500304140c1704c0402d0b0b40803000c1030681c00b01042040403400f0080c0c0c8050300030046403440c20000d05030051008c078014520481c0b031229440c4540c15410000f94400b04032810b503a032108400601c207101c940034500d50300554000943c580a00c408011403240c2c1310410038100c030085003050140c0b0b4001600c500b40052030365601c10b03866504100240141c14011913080405102d10003a0b82d20301c0d561644282101d001c0b0a400d003c0c0005280108501e250074091100300080071080198030101041540c40c0000301032045a041c00030b007451b040e10a40e8298010400c80d904200155580e00c0c00c0c0e0842da440e5800f032414008003518040300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 77328275 1250 77327025 77327039
    0x1060503070b0a0c060f0e010c030c0201020f1e040308030f070206070e0d0602091306270501080a12020f16031a09060a270302010b0a090908030403030207022106060a 73
    0x703040300302c0300880e10300d07480c042d51810304540411025400b940c11640360748406220f500c0c0c1e84140380342910400c00000745440380a030010140d550440e440030031a8014800f500814500307000315000688031381000a09081d90980e02800740c06140e002500102c4044204034640c1c0e0315800103842000d0b01e509403032590342d840744140c601a0b45102e41507005800c00481400140706c60717005100495000f01100d1001e12040c51a506980058005125002d640020080d0f5240c21048140b1030390714008040c8410340c1080c2c040c0360b0320000d081d006091142011300c207078406030013400450048130200d0183c030301085c0303d60402080c022a500c02220155072020a51144404c407c0141e805802100003414060316914501000b0f0015102082003110290881009000c0e410b5940000030f4070135000420000000700030030040c52117a0740040d0b0103a06142c104c0001914400c2202e42c817540c141030040e1540028008501c2c102020041007200100c20304140c880080e000449070310440342107845424036521004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 77329525 1250 77328275 77328283
    0xc191a0108070b0708090d050708010e0c041e0209010512040629091b040503031b0601050a03030f050d0f05040f1101050c060c0d090b011701110405061c02092101060503 74
    0x46040f56800c0d0501c101000103003004010b2501050007009544040640d40f03500d404c200503544054111784d51101c0002c5d4000e4180488004c1000858003000a0708400e02068031100070482d03901035203603002508096581c00344c1d09580c030103205010340702424a403600d00800188800e00550003810300c0c030f04a100c2e02054081071300c2c0e0f1460010b8040d4035580c40d07a8816020540040d811919814014800403410751010000b4052204070003460b9281400782a41e05410080c060f005280a55042007091001c00d812501800ca0400b0030326000d6540c1c0c0000310310100402264000041c101d00381000c0c80180112400003c41040c06551614120b200c4103006681a11030700c0c1107c05190800c5001a541051a20240242080c03a0802203840540c0741c0e40c0601140090300030078880d0f100b01d1108525120700b4400c005460700388070b82407880e0a003010f000608074001c0307c1000b0311501d000b00144100d901982c05494200c3d00107010700d075903000020400e120500740f209200c9002d43ca010800996454001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 77330775 1250 77329525 77329529
    0x60906030f02090901020c0f071508071706030304030c030609050c1e040209030a0b1614120105060309150c071a0c0a08130512030405060a0c12020c191a010807 70
    0x3041c00810403640d9801d01081400007020711416541c00d228030801c05c0703030901444441f4040d20700a40006800c2080210103003ca10700796504100d007410801003820b40260b02201c2d0640c440020509680e0f641d0002491403040e6000101403100e021320000c1000220340010300c0c0d544c4030314103852400d4004010320a000100f02088181e00f022441c0505903824182d005182204018058030703110480c94503094481c00f0240c4074042080e00071810b000c84240c2c040145041c1580011000c0e140c140010f40c0502c0a40e41806001c4c45604000003080c101d09003007000144203182c103007202500e072070140c0c04140305402c42201500c580f0b008002942c04d001140d000b0600c14484900c6550074240506c1c400c0301c0004004003000c064400e1050701401140d0100100d6400c900d5040500f030ba00d140624000b0304048000d85001d034401e081c80903246040d0703007000040d4010344030420b00580b42c61045007628a0520010f02c0e1002440c80f01c401c45c1d0a000104841031414010b402c80200719903a100100c507940c004c98 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 77332025 1250 77330775 77330783
    0x2061609060c0302070b0708030f09060c0301030303180506090717010204120605130f05010f11031003150908030a0b01020d09030c05150909150406080a020d080a021905010c0306090603 81
    0xc0080c49040d02a2410000300ba000744100d81c11241c0b2920311a515903c40f050035195100c021080001e0000c0d01200c0380d9100c86090064102c5e030903c0031010340a03000600004081c55202c460304200560035505911229402a00720381070b80c04c00c0d41000d0780352a00742c05030348884141175290418200307050084500700c500b25003c550b51801d554a80c000100030107004480024880900d141c085241c4e000c01c91921400f50303000251882448820703c0850308818107103003140c60305008000001000b056a181140d0b00a104441d1449020074080002e200031400105071003000303c2400030760300c4154040e1400b01001c0c4c0071290280e000e8901941c48a10602c0014511405a60306120a082c0198921000e81880c1002400d007400400015041c1c42c00300c400842c1c000c1c825400903003503d054090100103103650400f03061012002c1d00442d658050002018196040004201e50342610801101040318024005072004100c40c1c540300d400b81015060040010382011004600240c7c503106400890f41c4c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 77333275 1250 77332025 77332037
    0x10c021023070308010312020a050313081b060703080702160909020a0506030c030a15090e010c030b0906030706081807080d1106070e010c0201270504050c180607062307020616 77
    0x1b03182c0e60080070800d8150400214040d9411020010360304001800410710806006207019041c844864940141c0c00e0602001802050035035000e51607400440d01d00513014a0008000c0da50301c0c0c0c05a260507100040280c101b0210b00c00064100b000384d02192015200300c03503030043c0ea0f6490701042a80d01050b90001c0036440c00304003040101c60594007d02403c240c0000e84400c03d41c0d2455000111040d0091700751040e5142c2260b008103680c14464011252811503d4044a0426001185d507a40e02800340302c00380003d02e004943d80e10a018400c5040b14025401c590041c6c3d21215216142c28504490001045083c0d0b80c2030803001c80814254031039501075072070004101072180110344002d1801802d034144a0040070726229640f070514007071071402c403400c4299003040c80c05080c001107520003466410103000078841c050810110301c010065406040710400c0d20342005007091001090b1008003002c42907004103003590803012034842e0074480d40064007501c04c02d5070340c000019428011103210000142c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 77334525 1250 77333275 77333279
    0x80f0309010e120c04050a06090509070612021303020402040b30040b1f06050405190b07080306210c0109090e060402060307090f0b1206010c0803011202010c02102307030801 76
    0xf00719112414031148801199012a0030101040454400742c130003000441e02d800341400000321a0041c41e40010303a03840142248c030702d4000f005106075020a801c4d407405800144040460b00203400b00b001458000307004540d41e941d1920060810380c080036041c0190546403e40000e0b6a05181c000c60250501d5003000b403103903485680700c4180100043c13130301014000b00d05200b500c01c107005903100013622841e1a442e030748500344000c20200040e81d4201d08844035007084144514202a400d4603855a4850f5015480391141e000080841c202000080b400340b00400d860081c0501c00500d14041910a80728003000f5929000e20301d080e00c05030001d04035654441c002050050034410003e69110b50103140040c0e0b0b00f40c84001c0141003840320340c414060fa1f000413030400c840e00c3c41803070702e190400700034201010341c60083e40c0c4081d60b40c001449002c86140c0400038a20640e40140394104280b5030060076180100001d8401400d07042c2500c3c1902c001c16070f059010101d08403541d08540d912a0103860f4100e4a80c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 77335775 1250 77334525 77334529
    0x80a0507020414130b01090e03040e0c070b100306050606030628050a030302150a020306030d03020d1407080405010b0915060306030a0b19051605040e0601090e010b04080f0309010e 79
    0xa0301094049800c03d6403071414010045a000e0780a01507031003d180da800e07604003070518a90001e0180c2000d03031680d1038603c0b00e100b00400001101c00319280c1d20380120781640e90501d024110b010341da40241029140b0810403880203a18001c40302940d1090b0410031031520b6174001d000356030000322020f60b0030040b00080481d1048a1210600b1078070715242d208900903440c0c40c0410001c5246600032030141e4400e0b101c98901e094241c02c0158000b030001d60450031450306200003580c51079440c1c0030506040d40091806213440c03480d044005888402d401c4403006082c2100000c010325001c1b1410b90b025464164911001d1421450a0f4011001400b8a4841404100c204042a0b00240101d90b2511403601030b140041c120f01c500d6803144100040510800503103504410a07148000c0070603d000151a040d040b0980d040400e403000e035101c2e4202e5922a40e150401a01c41c65001d03004040c6d110030340400015141508002001503408030070a40f00486011074015a0300e00811007100d021403c5903141034454 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 77337025 1250 77335775 77335777
    0x10c0305090a080304080c040f0207050a120201150b030108150702030a18050d120f0f020601090908160507060f0905090a0e0a1403030a0507020307210c0c08010203060f0a03080a05 79
    0x1e980018110800140c1c0c5a84461030f5074090351220301160400210700e80985058880d070303114055008002e40c5080600c0e034440c0e4a0b011296402410700300e044148031109072003507000d40304010040000391001621058411190340091203484021305c104220306c80c500b4a00300000e40280006e40085040c4544200c0035100c440c080d0944c002c8180b502d84002420380d549116984d40c060007521914000c00c107501d4014a88000540d401c2c060010b03581e007010682d40e00140072811a01c1c41c847c00214400035103400b290520858021100410a4900c0001481300c00300307681d02100d40d140c9480d1105880c122056824803504d110f1103500c401040d001602ca094182c1041c5200c0e40d0034819a072502c6082c1d641c0e004040f0a40d02021503d9001008100301459a0b120303a50704801079000031401c100c0180c1e95250074680d1b4020640f200300010b043d91702d00c24000c0c103180180381e5000b43c035040855100e08026000f90001c6806a12900c03404105c0c08e064281440004240d98210a20b02c1c54800140020380e9a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 77338131 1106 77337025 77337037
    0x4060905030619050402041415011e0c0f03020c06070602130501050301030f03030b190810050709030f0803090a1401050f01050105130603150905011706090a02010c0305 74
    0x242d030343c010114000e02407206101046640d2140b002c1805000b440c90402840107e030021320852032803015980e04103060030390302c41da04050307011074900300b0003001f40742940030400b50350800c404103c1018144c01001e000303004031040d20344a80085800c0b540040c10a5411940c007044d4000e444804440110040400f4030f031460465041d03407541a05202410001030501daa5012200082c0d11040c622418010712801440303110350b91510035544804404664840040c50180002d10306801000f012043d250024161841e41859955a00380340e070003e000c405482c8a4280c2d54400902e82100030b021103842e020010407107003488441d55400b540103030001e030705101c000c0c00300107001c1201800890071500c4030b103404039826900202c108010402500200e803024201000840c00140980000340f0442c0f408045889958031580304030345590726030f0002030026011a04500c046441500a002 = true := by decide +kernel

theorem cover : BRFrame.Cov 77158275 77338131 := by
  have h0 := BRFrame.cov_init 77158275
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77158275 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 77158275 ≤ n) (h2 : n < 77338131) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
