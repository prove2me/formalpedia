-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0583
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:34:48.087799+00:00
-- url     : https://prove2.me/submissions/019fa633-b5de-487b-99de-daa993512aeb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 104676258 ≤ n < 104856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 104677508 1250 104676258 104676269
    0x9060c150e0c0a090507030b031902010507052b0e0603061e03100207080304060506061c050c040803130f0b12041707150603051501060f030510050a0e01030209090a030522 75
    0x41c05140044c0c125003d0380701900c150500c1d2820705c82d2150040130141ca03014803000c001000c0c11460701c43e41c0554414406840c80c031384070700d04407920b031519003010b074507810017003180d20018000307031110300c0300e4260b00041007003801c1c4041e24460b04500b0300800040300c40401c0313a084105e082184031425000d503010171200400c4862000110760f1128681085c00e160350041760b00351002810800820f4190500000f16110072040074a2900d80744c0310703610b01c003028001c06400c0e00000c031024403003c11000340620007040d02100407805201e82d10f150000e0a070701180d0b294000302c0316040911610380011005824294820707401014038184542e0070f0201c0c46140101c44001e0004001400a58005043c660045042c0e03400742c01110700300d48034410030003031745902402204005860400100380c1280207400c40c98000d04100c0c61008003070b80f140003180c8002c0390b6500842c8480b4008004200358117005144942002d450000f4203680c80386524050320a100b055840c4980d84030403502898424144e4200102410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 104678758 1250 104677508 104677519
    0x515040f150308120606040b0703030c09031401150f081002092103070515070e09090705060f09130209060702060a050d09060c021b010815030111030f01030309060c150e0c 75
    0x80d241e091008081e0130900590400f81030f0309011400c01d140607810b4a044036201c500940c680203599a044000d80041e004a0017881440c0001200145040c0000440d00b5181030000030f85828240201d0000d074680c1d400b980801025440500c20040042289007441c0d400410140c1d450394510003144012140401e91401c001c00350f18240c504d03420100041c002c1c940503808881c07510f50a00d0035585400f0082d43d0000c04103806441103446c50501034103c580c40315040b815241203651350300c0407a4040e4450056070240c100002120741e032910740090000840064440b045040400c900e0100d015841a100b0191007000003007010030f0300d5440b03035040714110910010207110615441c58136501400a507060071015002c1c1300001c0720407020704080c080202ca01691004541e441c0c1003401c04120301c00d0120309416549829260241441000045025010040383e2007450361550800400101454101d4403c01c04800b000101080c00344a16614640210b0400103805006020342898500300842d1141c104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 104680008 1250 104678758 104678801
    0x504030314010602011503060b030114040606062601170f10020904051f050f0301020c0a0b0f09060702060c0d0e060403020c0a08010902010801120311070b030412030515040f 76
    0x55141d00314503604486003682510990300c810080e030a076500ca0342501500341c0b418808101156568000080c120005070001880b6402010381030441802150f0a4804a1302c0380405c00c103a943c003444c40035a0811038003101c2c4000043c210542d102c14818410361200c094441861684014181728100c84800d12a040b14890710441094030041d400807505a4451441d04001036980c0780c2209520349443c071a8559440a6820b000c00c203c0410307854038a50340c00d51340c01d11461000034000c003c1680328034025a4803185c04e20780096107112109008220300082c0c0c002d0713402d00c0f945c0e0b80c00040700c907000303007400d902030340c91300403031544030008002c0541c007084248140b80500040c0750700482e1100071680c064956662064035000303c142650084039000780010000d20042014440d00d441035040709100b4038002418900200b007162401080e40c0019000680c00010f200401c408030030101d50510b59800c09001034070341494824441d0009404890045496000e02c1944690603844030380c10b400240340c0340458 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 104681258 1250 104680008 104680013
    0x181104020c150a060b0c0a030e1c02090403091a030406060603020703050403061a040903030c0207230405060f0301110307080a06050a0b03061f12140907030314040807030b07020c01030b01050d0911040504 89
    0x121083e01e07c083c0c01141e100d8441341010b05044181c103546803915080c0d030b003001001d5070070b110f0904c2000f4401d0301017004c00000810f001151500010320303981341e109916105d0815013800004c82e10203500c08000d140c03042103e4800203030010286c0301102c2d080b07000018020b00c1e048288410540000c0029449407515804104168059002007aa15456800c41e00d40c5602c03081c88542007440e4042106152544903015085403600da0086030740000054031100c030702d45104021a003075610303030b00f8011402c4402001300000a5480070400358013000d03035082400410718050100e2004016405154210480080011110740b41c02c140c81052101000c0c0b2032001007400900140f0342c8520300000060b09041c07080883e000341e4280a8507000340d2405025203816442c5540990781c590b221252000140803d11001882002c18050700c0000d50142c1703440c0702c1628101c0002400c002100701a507040c0751030244c040c2207d0768048160b450b29520001c0c001041a100c2c00c0203088010071000380c42c1e20506285c1000704 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 104682508 1250 104681258 104681263
    0x11190b0c0a0306090f020d15050619140a0c0b0a02030408070b1e010905160201060f09021c14070311031003060e0c0909070602060c0309060424181104020c150a060b0c 73
    0x7a24050301d0f8200001c6040035207800c8d44050f00d03c901c80d403007242400007402c44e03484581c904407a4a11030914402c1881901c211041c0c9030420000301000c600c80b1028081071000d860310040d800701d4565030444c0b840c6843d80d103810b031501034080043d14424000700021540a403410302100301d15001d02c01ca61940da9595035150251000312481d03d52040743c00036a158040c014014035080d0750485c80c51004035424a25003000940281540c140303001c0345012001182403070742c440e0701101140c1c462031078010300d0710070750203425288a092030000c648000c00401c8040541c90902c41c0c1a640d210501240400203500301d06e140404498445510440000600c11301d0000000c0c135404a030401d40a9403c907650f614007004250004450042d144d402003000540001c6a16130b8a0100e207110f100940d80d0101c4004400003101d400080058400d00c00e100d80406116203512040f16021044500790700d070402011903107458100a01020180e400b007074010400e0402c0c0740e08240050504650703255101c009a0141c240e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 104683758 1250 104682508 104682517
    0xb130909060c0e010302090117040807020a0308090f011407060f06170303060f0d0308040f051e011a10050706090f0605070203030f0f06060307081b040611190b0c0a0306090f02 77
    0x10210303c00c515081e001d54040d000b6030f100b01070161686859407444800420301e1550003072040318407c1e030400c10702c801aa01c0c0d2850b40040c0d400b4040d00c1d52101d5102051025080c0308000e0b29043c40703d0300c21050302e518042003c480b811030b80100b01062960b140303110030020b0003042c0c2080035507400ca18207040d0b01040001c05540b0811045030400300601000f0b05100c203002c10240c018000482040c00140410892500184581d214030f0841e0340381000404240352003881418160110b9444c2d141075220b035164520090000082100d00103008446144080c15903c00d5080080580b901c511012040c02100d1041d4100e8503000b0506000529100c41c0c0252254421140d4112603c103503408910074180d00d14025100e89405000c3c9495510b40c1803042e254900004c21810140312031000280030545940041e1004000f1600c03000849414021181d040c085c000200b0051344422803403c40105980e50001c0740c1017003c1c0c031800d5030341e104041c804078050080f03034001c00d03600c0f41050b81d000e000c4102da034003e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 104685008 1250 104683758 104683781
    0x11d030706050a060503060c0c0a0f0c0e1e15030313030c180903050d050415060303050406020f032502120a0305070b011d0a0507091d0a05090f03040b13090906 70
    0x4029030f6682d803443e201100c41c1313405265055848030000483c212900e40083c05d0b04000d82d02200c0d145d05c1c1694401c2c0101380c00e00f404503880c000c2c90740200032209074260810740000b04440300128132910401421107074003000f0415904031300c040141e4081520280211400c0d08400101050f8598036401c081e11410218413038801140d440100d299880c400f51300c00c2c0650b0540c03598400c0c0c85c01600300c1e00350018290141041e904119110a5030002180d54424540294442c1e111140c4403842c00401a06101200c4c1c0c1c841020f81003049400e5071210186004c007940c0007a0080b44100441d0350000c032b081d92a80348648000b51150507500418550003101070500a4070551340002280c2e01c0d03101403170018040d12001c1e02e20050b508085840e045040d008513500005d54035003400301c10f07130b00c03121030303081540240482d0103d42d140401d12110300140e010b19a405184840144114141c103400142e50348203500c03c084c141e040c003288500b1805c405502e110700504002609118502c00d0741800b100a284200e0070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 104686258 1250 104685008 104685011
    0x11190e160f0504180b0603040605061905031f02120f0402040b0d03080714160b0a060f030203070909030203090406060f1707091e0902130602010b01090f0303050c011d030706 76
    0x401210500c5003030a01c4040c074042d991a41814504404c0c4c00301c03442403409146040784c90360800c0390b041d141c00d400f03544900d0240c140803815050103000c0c058102402c26000c02c5441d001501804240c4000401d000360030b501e9202005001158030540740207000744248994070090342018080c00e032205522143c09039001300c0e0204114244201082514034400c0e10081c0030589140000e4001030050204141c044000c0d20107510f086401a00f003041c2114955049840e00d01501c1800701081440c030900004e09021008400300314115000070b40e4405071132040c2c4c120103885c2c89044042501c24415240c400c8000381c130501030a0340304d96024019540c26040304c40080c0d021021500941604000140501510f8841c80c201900b08100e02029095030200103022505003c0d0001c0c2c0411584010241c2e402c2c240f08506405040810003401e59407101200d82c10030140c00340500020903918282822a64036040481e91400c905908a01401d11008040d040c1c09034090301c01c1c0c2568004c8000c11080d8441d020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 104687508 1250 104686258 104686291
    0x501020105040b010b130e0703060e09160e040515180609010c0504090c02010905060703020319050103081603170c03100509010807050d0503040f0b040f060e010c11190e 74
    0x4908941c001c44000c0e044000d00c3c0010800c001c0d0140040c1142250b242c2603000480e110003110790303442025100c41c00040e50b111401c201d400c404102c81600018044041c043c400901040f44140e25501d02481c1d061003030f1000030804122081064441001000308070f0203c0b403078107103483d00103442c40301606c4440c0d01070400010030524040c465500b1401c0c0720745840c1e04103410701484d0b4004018998806007507640e50001100803c1007000b20a1207000e43d81d1b405642c0b89418100080300c01120b8110850701424040184001800e0109480303041200604400402c1080d05044803400c0307000d10341c1c840a50f94001400b034092070302d00c0218402c80d006e40e400c440581d0f443e800d00081d1076003407142c1400e6030030200091100c4d06c1d01c4c12081443c0c0303018104a84c2401e440c2c400c446400c510303603030110f64032810025042054000b641d030014010000d900f41907225810740700000e4035503103500c0d00c014009451135400010702c3ea1903a9030b5298a080d04480010031a07207400c00c245146100351030790252501440c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 104688758 1250 104687508 104687519
    0xc03021e030405060f090709050a0902030c030f190c0509090c03240c0705010b1e0112020306010c020d140109060902040e030406020a1104180b0703060b040b040605030627040507 78
    0xa00312400340f030f07100d00240416501c2c0c80d001c00c014900644840c0c200e004901c400a03a0031104c2c00390a005452180d00010041407034070400d458500c8001c0554000e07084a2061004042c003c941f0074082c0340c081544080324400c2d0301c2e0004031802e041c0c002d0381e8414020003c0c40443e00c00055004002e6005030103c0312150102c6401540d400b02c80140c0e51492050707038000401c0a00c055003d4412248284004165000d400c0d0024190500784044140403a0030351210202d15a80543d801c02c0c0036282450451079414220002000b00001100180c000c00d15080101c0801c01a0f0071080300401d00d4900070070480d010344ca0040c0c0a0241c56500341c0c416802c02d5a609524500801150304841040c2c00525200315140d850b034070251011403100e070380699640f0950542080e03015892249621603980343c0850300d4998400740441c0c50f0f941050342c0c000d0341131105001088194048506403a214145240c4995030100019100071401490286000d444144400c3c112290203c103401a40b098040e40c02c060744a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 104690008 1250 104688758 104688817
    0x409050a0609051303210612050607080615091201061e0b030105280503120a17071b06330b0a021b1306060906090602010204080309090c07060c0302 65
    0xb6226610a0b240302198000001d0061001c241c43c045620070046c003039a01900800100d405a40c841d101d10303d40048050100401031040d5a07001c500c07800c001000e4181040800c002821901c1c03441201c00d40000c3c0324016a6460f0080b1050070300c079a0080c0515600c0300d00c6045030000801c2403295070784040401055085092090b2416148058014400101490881c0400080070f69408968120f2000040f41684003400b03110020302040c07550f5030382c81c1242e03000141412a0281c2284c4200303100000d222840c4d600c5080d10f0320000150304400000b078000d040090060114440c0c40e581c03222007024041000708480d0304c4c0d0181d403108002e0b003000ac1b5610404410144160280702c401600000805e0700098100f248520b6100000391031541c0c0150004080412a5440d0300a400402c0446104112141e88200c0c030b400980f446200960400f882c0c0f54010b03903240662000b080c401e25942d0b00040040c50b2603826205207039000301c0d050022216041d000b600960250340d170716000e0304c1e00713400082008199 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 104691258 1250 104690008 104690011
    0x50c070906062a11061303080901080a14040308070203090d0c1a1206190b030a0e07060c0203030d0c0507080f1206010e060306010804020415081b09070f08060102030f0409050a060905 80
    0xc1d90300451128190b03584e00a0000925902d42d104005100c40d40e1210865900d0704095482941515903400002c0005040c60742c004100c02441818000d130101114030307582d07210790046d900d82403a0000361211507081e81140100145690041120071855051000920221085074204600001ca120071414414401e00c9040c1c5070040071842200450201d0805440c0b0400c3c1007081d240944c0c1450321500d4610b040d0b0f20580d05407100c2910380814001d00c200c180170500c010046800c0210800c00c150f80460b840340180a00e050040d940c518085910724020401c4a81c002d51020000d6500c050140541c50550800c1c00440f8054401c0c2e1f000503210f50240c0058802202c0082c038039130666960703d004540c42d1500901c126001a1036483d40f10104c2c4001340b0700e8001c0c0901c000a00140310801e076056004021090303026100340f101d0340600c245140c0003032100f15401e01900e000c40066952200513441d601c034130303180790008a1001500041c68038081d800603010300c041e2901400041da541410b141907610 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 104692508 1250 104691258 104691317
    0xb1006020613030c06021c0e0c0d0f17030103050706030f051306050a11210a090308011a0f0301090203010503010c0c120c03121d1203070c02010c03050c07090606 71
    0x240410900c000301c01c1d16205161103440c284414050550b117050a9070480401b030700d50507040100c00040300025010f140140e5115070003c0442c401404001603208818000c0506081e8024800138180320810702e04c0301000c044803036100d0380c9581d80e10303045503070300070601c207090000345031203007160341841c0c14012140164400d9a2000a10015844901c0100340180094200c070b6541d04800107071400c00030240c5440080c9800324506405041103120040d40010806c3d040c02e4a81501070001981100a03c0d06480070071840e0413640e00a507503802072138130030800701d141d800c1804800081d094040350001c41c1a20410342c003d02520781401d1055444041c802402031030f15030616000d42c034161207000c00c08102e50080c5403400d001d03c90914070038125104002c0c0c07115045503c000c000c241410800c40c9140450818030620300d545800300b0003c1400d5004030b002810040d081e542d080615200b2402e0717580b4100300009981c50303d56512080c4005011a205940118910015061041c00ea04400100a15 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 104693758 1250 104692508 104692513
    0xc070f12150923030d060801020d180b0408030907090207060209041a010c060c0309020d080309071205030a0f0c0803160e0406140405040203190c050a0e0103020d02040e0f1501030b100602 82
    0xb5034260264864501c0d443c0841c80912052007000d503400514060b681c0106441000141d449102011500969206615100d441c0b00e0b51071000340006c1ea1189619807260700300c486181c494644d0506d0741d041034042d5101c600c2e407500110340f0f40144911940200301000e41200c040015404403c1800d01210540240074042500401c5110200c1e0302038101017007481180c580012004002d6000994a0390105004d42c0d007808040204078000c1000c01c18180070b0182d5105014400c9a107542d155034900c42c046415082040b801450b00c038890103502000321240e88803500c0fa44034a080618030f0400a0600d9101c000102c03003d80d84807003130030700e4883c200640c1c0c00d038681f50400306e0060080c0000317804090030803a014402c40303204c22503240b08041340325441c1e80b00300440c500303c500d468200310803d4800e0700704400c41170400c001000141d0f40c03500000c200e1581134801180c20140c0c0700715141003d07d5655401d19074000c01d029109590789440c1454180d038400d09501d5a41d840708010084680c405000d58000769 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 104695008 1250 104693758 104693783
    0x22170a020d031119061812050a02010216050309030d08101e080f030309010b10050a12060504050106030605090a0204030b0105090a060b0d0614100203040b0c070f121509 74
    0x1801c0c5200c06203842402410940a4001c69902c3c02c2e143c050b80f00f000c00c50000785018803104101d200d004010200e0703c44030303118403c020300f40c507000441d10503101c200050020004050303030524001e4054a210307000083d100c00d40019641805912940700c0d142507031003401911101041319000c1c40603240944a030045901c100e07401c0070f01c0304c004110695541ca08551f00c021001501c0002003299100301e01c0120041e41d12810082c07207090949046089113407090140301c003681c4450394800180c0d81e41039194075001c118402e4440f02d00c0b005111507048150000d041000111300c0d4ad401d80c028004442c1b099901900c40d070342c0c008000b0220700403800010302e1190503074010422881c19a1801350007904c240e030001101c50780c50000040e164019010301a5840d2120410800b200c0a0b980e4842100829510034000c400a941c00039100c2c4030b24041c0c83d2641001040ca401e24450801c0318101406011034082c651648540003083e40400c014400c41d05880c4030907641c2e680062a000d03981d50140d0088224490 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 104696258 1250 104695008 104695013
    0x120b090111180102070503030c1e03121501050903011a01170c03040b090f0a050a030f050a020d110c090f040c1a07020d2906150406090302060f040b22170a 68
    0x121000c0c4400e442c114400e03280003046d1a034003400205801c690b00380040c544407480c4070700302002c810f070544d418805800600c0301c51440074038129030a034080d4103c16400110084000142c0d00e40c0104903015405628205080541030301043d118a2068803d0300d8100b040a000100000035403021100c0703852500040c804200040d594191840c0c0106060701542d580c001d824900d5031908403000416900c41d130120784603c00340347c0c0140b101c031182d100318a4510720300300c203218020350b0329020b001d044130030060302007138030b03a000803040c00001d901d200001d00c041c8860404048000c0440c000303a60a8810702c08022001540b00d0b98440e800d45d607040d502c0d181c0c40c100001c0c2e400b0410403203030308030b015030f455010300100800048022080b18801300c00f140c0b8102c41410311134140708800e509142030441e0b050040000340b0005800a00b43c50440340e0445005580780d59402061034a402a43d00100400001041846100020021800000d81c800c68003100c0c10ba03603219014081c0380284106030b00b44c0c0040c01500003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 104697508 1250 104696258 104696287
    0x4090902060714060a0b060c060601080709050409141b030d12180b0405010c020606010e06131511010e010204180f0605060a170a050106081f0b04120b090111 69
    0x126030005040c07505009654484185a0494550050440c0c000d5010400165068407500c40382d03032801c3c0c2e045800d00c994020020703500d40c4c01914540c10311505c1000956018814a85c0100ce4440a0000c3c4800320281c80c16407c04c40051088490b039004100130b032050704001414075038007404020014a00e041c2c1100d4161114080a240051101d8840c00e03030031b021585d09c0f006120500c1c4140300100d0146480e080c45821a20000301c40c0c0c085411240600519a174801500e02c0d64050031150b05503210304858402e200f10a141d400464408003012000113501e17000300c91558020012030081c00070b04080d174081d07401c074460b501540b4001101000350020004455000403807080e5115000146103850310006041074000d10b10f40b400141c9004885200320000a14980e0841c03007000d42800594140403014041a1000300001500046a41c0c201181d46000030504020102c10400d95510364440d402404801d411103000d0701e036074000d040403ea181d0030520070100e160b0f000405160608860409018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 104698758 1250 104697508 104697521
    0xa05060a05191b030f0206070e030d0e010309050d08071107031502030403020307020d0c0914100608130b091c1803031b082701020714090604180515011a0409 69
    0x400c6030f0782d0b040882e00e451807086100300d0b0b8040c0c1c46041e54001c0e401002440d285c0700400f11010040700030341050164800003145e03020310003141041e100715505400100d000344001440601035100344900c1c109c000c2d030405181401410907a40d80103200303040d10511a40c440d50361000510b80044c618903a9085c00e401d50245800600c01e106980c5010807076000503c0200d04080c003507651040501d4104100704892003801291119461070701000d03c0c108035540c46d4030000d4401c083c107002e816000101d500e445002a022481d50141d1018072078241140019502c3c94107648200c842d01e4803240e90b40285018042070000044000c80f136504140c150f94044440303600355100b0b54440640b01080400040c00900035000382250090b28141e0081c11f2a00514800302c950003070703810b64200d00018400100418560034003a6003d880c0f0000d1500c400c0c010a00410703205420400c6000820102c000f00000401c8940094120011441d0180d803607400072100004041000034040700c0070403013004410281e41024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 104700008 1250 104698758 104698807
    0x30c0204110f1201050a1202030c062a03070b0709053d0c020a050103020301050a03080903030d06090c021c0f030e0c030307051507081323011107020a05060a05 70
    0x240c2080108400c5450326040f88400c1d950030002840144102e05001801320000d2400d151848420380058001c01e440d40451001d036800b0fa140018810318091030742d10010b0402c41151000740c1c0b8410443c00300383e16030b007010078112490b0b00014041180f0324420301c804015104c00030019404003220124901e8414031044d4004615004400c40440c0710304141c00c4204032405948680b41c6030505841048520340440d084581414418401400183c6500742030400b07995220002c90380e940b0480000906d1030007012100300342a410510085000461a0095106101542c0032500440ca42030341140c40101c51500110010b0341c000001c6070740a01c2504010010321502c000e9446101e80c01c00440c2c15030380084000d66003075002036090480040c0000d11198040f0301d603d010f800038281220607030f01c00716040701d01030000320342d8813149000050000300d0880c540250b4002003100900500400c000c90b00801d03402d078400c01000c02c0c001024241601200c02c0301005581e803901d080304442031f107100d400d4002e204 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 104701258 1250 104700008 104700041
    0xa020901030e010f0b01090509040503030105090c0c0601121e170706020d060303020705010909050105010212090f030d0e03190b0c210901020d0f0b01020d03021c091202010b0102030304030c0204 85
    0xb02141d820b028403038403201d4184c0c00d90124a40d185a0300140411800e40c1c8001c4c005c0d00d54134104001b00d0004401d990544004951b012240c0d224a1801001402188601d84150040600001c2c0320f4400c8412103620501c6040001c03040061010b405000e032440b2240038201061083c140c1d54101d010000501c2c1d03540c03190304018102003d54045504444150700300b2005a40260010303c40707036801a00e400000c02c0100d1040c440c0d5810f00b030000703469030071301d10002d85d9612010482040c19039400c00302c0015140060200e5001d1040300c00000c0c8626011a2040d00038061a0801d1482020311880c1485039900412541380986070a1040c1d019a4801403204e004a07001146120001c0d402034415400382c4104000540c448240300d281c130040b0345801c0c00c145070007890250348840a9801198005d000e40d0f55040040e10f41070175000d00d0002c00b0782564400c0d1407500e019410800c011011103418500310913640200048041c2c1d02c01039950340300948003d0042900184e6050041c60a81c001a1400308450f03076 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 104702508 1250 104701258 104701271
    0x60a08060a0204060e1c0807020402042103030c021b06030a020912010b0a14010f1d030d090905060a12110a050909010507140307090b090301090f050303011e0e0a02090103 75
    0x40508103a0240c070780108450300007504010050303000d20079440d8104210303001c4030425a0f505c40b00b5038401340303508003e04181000c01e01109669860781a6801030a00c81400800414003104040c0940d04581c8120701203480c007100a140030303200040c010030411242c041010700184100811001d40c1000b8422400c0325000c0040200503196140c64200c001c2d8003100115103181a40b00b005520076281c3c000352402c021041d01e4540c00c1c2c4c1d104e42069030345041c5083c409941e001210307a030586884203034400364140c403c4205411042d940f01d80c0000c2100d04c401010006501e0f240100302d806802849003200510b0301d880003002085c15000100c402c1200206205580c03070741c81001c01c0680701d045800525507590342c020820b140e9080b40a00001c2030340c0551080c070f1031500368800b40c1804514068003100e6071000ca01126652001d501a0814640240034a1921038031840c160350381e64003d000b6401c0c8070040f003840e0300d000d03000302649000b070b21804c80f12041580d64104540c2c0007900103640d002d04241c1c4990 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 104703758 1250 104702508 104702519
    0x6140304080c01090b040c050414060103090f1e0308011e0303110106030210050304110a0806071107080a050a03020d02010605030705010e1909060504060501020f030304060905150901060e07030b090f060a 89
    0x210306212540300d0b4445008a00c1e0500303001d0b13841f00030b95009502890400c070361001c4800814a43e40d907c880c0034240055507000c1400c1c48184085030b100006c00a600f41c0c0381e40402e0708000210607040511a0b0f4075000706030b803a000318142482400341001c00340c095004040c0000f0340241c0086506510300750000400300c3e902d0b00095101d2181c1c511501c046a0008144403e1114074034800d030219200b40e80340c003441450079041d6135072440010084d1080100c44000400302c00030503c201c1004080c3c081c11100700c5d60b01800c0c29034940d4003005044015120b200e2207409200d0060180303804856009000c0c0c0503a910700001943c0442a000b80c1903840300c2c09032499082032040403041c0000d040f000400043c0780b81410184022690a504002d0665200c2075040e000d400001080340e900079441100498007460700d142035440d251138006c0c64504440f05004010403034205602041c1162403c00b5441525114041c040e0129030070088030740e400c2480312001505088104540c290001e00141400f0103050303a64 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 104705008 1250 104703758 104703761
    0x4020d080a080105040e0307050c0613030c03080a090503060709090504061116020301050606090d0f050a05030a0203030f15100e01020c06040b07150b0306130204020d0207030305100801050106140304080c01 90
    0x801c80840414000c1e001405181041d200e00200c25134820300444c500803c80c0c40d4151b40308508020341c3d20405c00024034001500d5140d0802005551007900b2004107501c3e8178111945130400e280d104002000c100d40003c0b20f29001034030078001c0b0041e4903000e000c14240074050014001c01803007501c0c40d0b5110250044480900d00c002c0204040c85200c1ca4240c0e107061042500790381010f00914800ca0090142e0000c0b03a8481103880c04c03450707025a01402400309448c001307060107079041c405460341c0000b1030900f9202d90040010751250380c0400d0460400e03610403894080c0812655120341e044503a10b00f01c6900755004051400d03003d0340500403554040d89200c00200c1c0baa025800010010324045011000c200d9009100313102e040d200c40c1d082c000c9201c1200460343e1400002d08181c4d4500c14095880f00307644865040f540200d17a01202035594054a003800f4028107000e64419200320b080b003000044110040c032070641078521039175903408448015850200107420142050760910f030100940c80084409 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 104706258 1250 104705008 104705017
    0x501170a020910020a03030f11040612060504150315020f191403010602010c0e060702030c010813020a2c0402010503150a0b0d1e020f03060915040504140c010e0d030804020d08 77
    0xc0c4c0d4001e004920035031030000c0a8410f01300d02d110300ea5081440d003842d204200000d0781c00ba83c00d1450800c50844441e041207002c1d00305607000c2034101e841c1c8840c2d9040c2c0000d001c0321000b5640681c2102d5080c01696000c03000300e21544078684801d50702070001072400510440f150724010b100381b40a0440214018540041e6031007a0b100e000540e5441c42ca580c141d6030000352116a00300102c40f0242849410303008240c4981c40324400c1c90402c022980000c0000040d110004500ca40282584141ca51075826000d00d0190480360300321280800c40c50341c0e042c14000c0011510a0382d0680d01c65041d5203403040480d04c80c201000728070760310546204022540a4900024103007200c03201e41d0208000c8010748440141c1240e070b220441c052401049002007804140049a03000102a5942e404917030750900e10340403224111000f503a0050400c4140024400c080e400c50405079844000d13034503014540c80054900e401420b079620b40000e10b05000b0307000720380202d0246074000e00203880c564500c0a15035810910f0b901 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 104707508 1250 104706258 104706289
    0x6060203031609031703100803161703060f06091809010204050108090a0f031b29011205071802070503030a06030c05120318060c01060609090509070501170a0209 71
    0x400320420095003045034400c0070b000c0c0142000f900c030a080d62106003108403c1c40545c0e920341c40c0000031484001507030b001440203109000550782c40301c8202100304c1d041c1c4280c0c1c00a54036441c4140302088111b8a0108581c01750074014220b1030b03800110070500031990840b04c40b040d405003000d414008100602044584640400000182d51345e0800001500c000300c050700c800c2e00f6901160301174000030350b01058140740b5a054246000301866644172611103c144030300080c00281c14423013942415000803400700034404c007072407034010b1680c9481c181800c460214501810640c0190720805c11801251151050800b030b100c005880d003101912003501d154030a039012880c183e0351f50420410f0045003000c80c1c01400c8200c40c034544565030040f800350749005020b1764903841c3c18174070340c0c0034415610784003140c0039000564000e0000554031301e005007401c00b2910505a03014100f00c0020742109002c039000080c2e80050f1a02c140c19000028031159409000b00512020f9074200a02340032036480c80980c00d4000c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 104708758 1250 104707508 104707513
    0xd0c09080a03110d021f0e190b0411060906040603020906120408030403111203010302011d090907051e06031303121a040e010501050109050d050a06051305070803090307090504080904060602 83
    0xc50f41d02083d49440300340e4021504540080300c0501b40c05907031040124a04080c11000700b2410b0514804034103118500f2403e403440d40414407008201700000d80d0302c0d4400c9010704800c1c25001e0241040c005244543e0b00c50b82d41c0312404000500801c0d000340d002e0300703114401602d25820306100c0c4000300e0b00001c00351026114044c000c400c01003019030084440002d020220080c0204075180f18045255000c103003c000c1c18440c0d0380521601d815044081c0d808800c0000301031880c9810b28a404c0c03521074807540105802a100707403200e8940c00c6092442001c00b138030301900c440c1c91903840382c0c180c1203501e42c424821010003a880145140c054024000c42041d450411141131b5800420ba0400003103440b00404003000ba410000104420307030300b241000c41140c03015aa019882421460700314204030b0001401070405240509120000c0204c0d00344500c4c051140c0200c0d40f07002e44400e00e00d0341d80d005211600d030745680562420301c003541e42c9070807080d04103102c4d440040c100584200003030155001c079000800180e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 104710008 1250 104708758 104708777
    0x24030304031b080c13020309011b0f030b030303040b071803120f030c18060503270c010e0a0f06030207020d1202010504060b040603080f030c0c0a1415010b0d0c09080a03 74
    0xb00a0001c07020003403003c0e40c0100002d0500c1000314000345600055030700b18590102c00100c140c0c1c801e41089420544a0341c40d4019055000800340841498001600009107448aa00101d06000089900503600104950155a2071050845a44070850700b80303100400480d800100080030140415014445c9845000e03050000500007000c480f1039121701810000f48840b01c04101d20007010b00c10a0310300d00e141c00c654907500e00108030324104210030300c01e14840341e0750b2550000d400d010921403020030302680d40104030303e9100c0400482207000d010713120341c2144014003008928000d034004c0062920140c903c026080c80c0341c40d41811040e10740760b4200980d4540040208010342845201e0003814122801c01c100ba0940c3c03658681405290540c114400e00040464000c3c4201c100f0740740c0e9549d074802114020504c80c9841603a07031000c11081c14503071140240039a01e003500814880c0c1601e41050a590170486480c0024014200b00b0040c0010b000150001042c8844140008010b8a000b0b4079121541c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 104711258 1250 104710008 104710043
    0x604050102180402311a090f0108100905041b0b1c02160303020706020c1c0e04090f02101103040f0f05040c020c090c12040b040b06030a08032403030403 67
    0xa400c0b4480320140326600c1000600f0203d140048030000140f207010902e8016400b941c13402c0d1807501351742c12040d05a003c3c00c198500680d8400002d21490000f45d40f001075043c61800107543c5074400781c0d020290482e14980034070601d221580010f41c080e00130044142405050070f24154a1021034000e05040b46001542800081c180744008100e5400510110718003c012072121040007000310b4000c08058001904601740328403074064400080922003603c90158401254100f6924078200042c00318600400120603841d0600c1411202c0384c0020350410443c176144e00304000401c0005005060140a0340040c40203301000900f01400d50095118011410030080c070008603c20342c0550301c568280b44c2d01d2403070f85a012500c04113001c010b40d9950030540300d00481c0e840c180a0240103071402e01c2802c0802050282000c6042c1c0258082c400300ca10f00c0e20b078103003459203403424800040d041041c1040490029250b803810121144c0502007510702d96507110000030300710f40c0315600649a20900c901c41c03920 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 104712508 1250 104711258 104711287
    0x1020606010c0507060509060910090602150108030406030f0f05072133090f0b132c03040306050f010801110421020d020301090b0901180b0411040b030604050102 71
    0x8011200b400c0c05002401c0b40d50f18180d4400703140c000c0008100300821085032070385400c0e0644138410401400c1601e034842901009181c0c0c1342e00e01c5900010b109035500140c01440510311281a203101d0005545003506044056010704000c0002e010f03115598869411405902e00c9054010318150b07580700c103c0e05948480044d01d0710079616011b512031404164a05020243e1a6800c1e003214101e0401105404101902643e48441d03009101050500c5030410b04203449500800c0750780b804032900000b0401407030403078080360b0101e0302c0e400d6221180e403151607000b106c010320350740440e2041c81224505526980c0d20f406032441078803965a050b031444d00502c40c808083c05000c1d0303001f1882c038007a0304192400310215001100500810704544a2030300540554698808001000c1e40180c001e000110f4607161a40703004100700d030103035003551804011150644018030301440d0141c10115009d12a140c944840c1c59925180710740c0e83c1c0c07241c1c1c2d9061010958800380247c0e44214003400c00180c58000c0ea06c0f0800c2c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 104713758 1250 104712508 104712511
    0x10090e070806180309090403050f04061205180307060f020408030a0905030f01020a0801030f02030a080313050c0a0503070501030509150405030304050706080f0c0a032406090e071e02030720010206 86
    0x541444200f151141554002060ba0400b880c2200c1c020355030b85650034140c1d500d01c9080b04500600400150110352070f0b82006080e40d200b021f0420400c0030b81d940c0d000c0c9017107142e404151020260401c1028101040068000c03d14000181074014030b4207683d003000901e03541c4a01d000d4000f152500800304580d00e820310004013014040002036207030003e007a1004140da00e05000041c1920305540841082d503c041042c60035995010038440d90b00c1c20004042c143e0b5800740300342203402e8400d823483da0b6801d040c807141c21030171101c003d001020580d092000543c0581801003d00e5054030408900d5107a00d210010080d02407070041016541d2800c003818402c0c2040041c0c0c004d03005000c0c26509110a40d020840103d81c0451000d030400d44400c1103c1c000c501421000740c02c80c1c00250070103580d000c0300f0b10240c08181269069100c41e034055a481c1c3c0004003910040b5180d40201d00c0d8401c4d0005c071040302c1903000c0340301d0441d481580e290200982d100d0b81807200e0b503520700e0620782c0091203000f040c0d601000b84a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 104715008 1250 104713758 104713771
    0x30d140f090604032102040e04020f0a140d0602090d0309050a0806100527190c030b1c1e0b06090603010912180f0b0c2104050910090e070806 62
    0x241010300d8039400040d9280c801510003030402c00104088141004801782e011001d4280304401e554850fa1b5100480a000041e90309900c644580300c034420045c078000101c00129150701d0201030411095000b00003500072804415280d0a070200158102c0da03640049000c1c3c214440c2e2110641d070350510f018022042140d41040e161607104200f844000d1281100e0b403403c5031030480b01e10300e03140403001c0c01c0e20a425080f00e100c1e442c104650144840f078184500c1034074007403003858410844007402e50403c40540302d90000303507030b000030b0030781c18046c0c9081000811600c2140901c1100d808184c20b1066010038078103844c82a0340d1800c480342481140c2c9003c0f00f180b074100c01d04400034409000191036000450b1000040ca1042c1302030140c01041012082e10000000c11a00f15600e0b2096511034600500790f00036054200c0340e000d86030b00e902150100410903403c50001c0d0503094102400c0c542403292054018041450049080400040c00b5005008a003090000c10020b06006858031744140d26201c406000c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 104716258 1250 104715008 104715031
    0xc0c150e03070e0a091e0302010504030e0303131406040e0106020109150b010206070c020a05040f0213090603031205220f0b15010509040209040207050102071424040303020318030d14 80
    0x100302100b44031503074035003144000000003170495140c54607003030061003034502c01e01d65080704804105150301980701a1046000e625520040d00d52002015120301c90702c070011182c1200e02105005080c6024002d0344000c402400b070510b0981c4621204240d000b00b64410030040c0e444000e80c100f000007040d8441240d0404103010320007012403000107500c88000828410400840b4070814065603a040b07080001000094800c00c2400700d1200940080c2d8400321a01c0c1c9002098031000810002d14854001220707015034070034200081d02c0501c0409008007411003404103c0410401c0c47c0c0102c150001c42060748594556003009101d403510800c6484001d004404101429043e04e8003641c0100490300c4004040b0f030b0050b034804409001130002c0c018031001500a41c0301158040400c1400c080e2155000d01030412204480500140361482011200b2241598100c0002140c00203010350065500305054484008416907940096495a080b512510741e03515201c8400606104d110059150001980102c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 104717508 1250 104716258 104716273
    0x6041e051e240a0509040b0a050a060804050c0301050c0415030605210a0f0f02031209031002090f10030522050703030809030d0515100216060806010c0c150e03 70
    0x107418410724681d0306035500810003000c11401c00049200040b4415000c601c80c56150b8030700440041c81c0781c0140502a00451600d42a06030324541183c08004450005000408945c10501c04032809940500112014440e003026150303140d80a00409211f01040345041b602c5514001c6540910450030351070006162508d80207009503240e5540240c0c0d034001810a006002a402855a03d00301d129140079280352100b0b0b00311000c016a200b10a51558000c5080360a68410180903521502c03401540e25415441095141c490f0b40e402d4000d03194000d4014880c41242078440c02142000003181c6004001a950340e08006c0244c1599046129100310041d40c400c8480107a52810f03507950b0f00b400041d05009100b40021555602082107a00f14600513400f48854100b01a5004a0100c0d0401d100c1c03083c0c0d00160300c03851003440003030303010030310030781c4103080c01449107000d6096503002c00241c801c0781000f42e02d4090314080b03103640143c0c0f0000c000e0680031209a415886005258100221200f4400d41007504c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 104718758 1250 104717508 104717539
    0x9061002060403050f0705060c04080106060503130b040c15020105060a0f030b040602070c050a1e050402120609040302010f020a120b0105030c0f1305130c081503030d0e010b06041e05 80
    0x180c15030303202da41403c0ca55034640c103140026449000d1010020014414030f42040315041d070b000b0207401101d10a80c024442503459600c103441c280001c40340c03003212040d03081c0160045000c40804541082c000c0c141c6060254446d20b581c0205080c0c24414000750703450303109010390b5060500c599001044036092501c51142103588407080581c020708040c083c0360b000308114090081003101c20000b0003000b4610360707105a4030303c042030210b0201e921826089100e00d00011707140c1064001c8039010810034848a01c2a074600702000b0001c0d5026005408642d615070800c040c407681071008003014406521118080c0410310f1805060b56859500c00c2d04010080c414032030080d6001054500b04821517905c5a124038284c200049802192342c001680030b00c0d4021411400e19240c2c0c03000038500c100d0369607880180d582c00817010107550034001d0107400d036104100955031807549501c12210307202c018001043c3e80101c000042d24580050b001100c6404441e50755880c51100320400200030724040e1030520b4480030300c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 104720008 1250 104718758 104718763
    0x31406120a2d0c03030212120705070309180902041d030306060703300f3602040908040e0703090803010905061c05071e140114070602030403030b09061002 68
    0x10880107000c00c1c0c1d055100e80c0841d0075098060001a1201091146040035051001e1500b02c3c0344402d4002d40500040030210342c0040d82120840d42c40d58684004984401500b101c0940c400601a4200004000c011400c0d40c1d0884c9441064807035003502040b074503043d004200032a04101040e02840031000b0000038151408001c0c0ea9000d802103da0303540f60b08403401c0c01d4410140d9030042103420f01d0700e40340b101c0030360514401903214150850b41c100220850f01d5224001c03130b8110000d4240c801100303c8a40018600c0380145005640c103144156401c510550120341580d641079421100e950000c6000c0c0003a8a00c0281e580d48000e4504e818440000303661030f07041d0244010300444202a40b9603000a01c0ca85a0300d800d140a80524004200803d505081c80b94803815903002d6003001c2c00102c240214032110b0034154105030742d41000c0c854151082040150385603551030659161402042c062680850110300c0918400c0e03020b6103001c00c105406104220a00c84020001c80c0305d00e041260304841180e00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 104721258 1250 104720008 104720023
    0x603010e0a021608030703151706041b080109080a020d051303060b040204050d0c14060a1d0f0607110102070608040506040b04022b05060c28030b060a03140612 70
    0x4441c401651030a05451a40004600e60405007070114000140252a9810b61284800344007440031029090780307507034503007807071220341d0702d880c540c9910482c00f10300032030340c05a5101c045080c05e1801000c0544d4030019242518004a425141d6141c0481d01007102d68040c0a00107421200d803524a142076203030800c80070010300d00d000152040e40c3d504410300c8251140e50440700030340700007002080c4240803441c0040e02194240114801c45810740341c00380c0c0c182441420340304250340944a080f034464503000ca1052035149401c8055002c080d038552910386031140b000030104180031b01601c10450f81c0c1580064079100c1260300c074204100ea42001c0001040b0702207986030700320380d0258196031552598000607500c4130007034408041244407060080541c030110035060000c2c40c8103030241c800c16621100d941c003417402280480e0005030b41d00d4581c005025203c1005484603000c034280000d5000c5001e011074040d030403a00740ac4c80401d507101484030400411a014603440f8604480c0d01c1071591002039055151080f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 104722508 1250 104721258 104721271
    0x161d040f02042009180705070f020409020a0e011d1b130f08010b0f0d02060712090305070906180b01020d260c0a0807050a1b0311070e150603010e 64
    0x24a80c05110441d902e0f9004103210040002d01d0300382d5031512005a003165841510028400c40f103003a0300125041c820031840c0e00c21451a143c0c0c40c1825280c3d160500301c01c4501e44c2c1207078003682d140964070050785d503130640b140030b0000900c2414407581801e500030b07844c605100b50f28005061580800031500e906803814118000c02c240b5040d101c5810740b400c1000039405402c088030302c8203605404501c9000540c82044202411242000058090010300011000010000c0d40014080000034046841d4000c082c07042c0f0700714901400c10690b02d4642d9420705580f80c020804032500c0301010020111001c40403981a094034a08005003240000081d41d500000004401031104901002c459584103a042005020690614481c00c1c07400c1994110664801e00c40031012503d00400300f51a20300c1201510303004100e5031151880c4400010409000380140b4504500b0055102c424516000051082100400400d01000000e00f051410f000542d6242040c203406100d09000400c948824400047d0708082d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 104723758 1250 104722508 104722523
    0x11802010c06020c010906020a090506091509060705010c12060e07120c020309060f0309120c0c06160f11010e12031b1c050304060b040903170c1b161d04 67
    0x201441c2c40c0300680200340c5603c400d07500e061a80e00c00d0007800e40040c2203232400359448000c41ca440e0700030400c044c0150340c20a03821008200e5000c5458514400408003034500620740c2e0704212640d07481d40d0039a008200e6001c00510703d02140c00d10300d012405601d0180c5100e06035640300b458001e0000b0580c000401a8000181e19070491610707042c000d00844407450030140c003190383c60400401c5088550310584004085218040b442d00390380001505882403010058003400c1c0040c5000e0410100350840f0810801031249034050307100081900d800700081134410b103c0034401604800014010003010112140510030201c1ca0201180021040307640c503800c0c80620100040801140e64608a0038000c40c00c107004030800c0a41d006034000001e940300710302c0b8003030901000b0802000e00040e1501d8010050200d40c1202c1c500c0c11407120410010b502400e00c401071420440c3c1103032000804040001c2d1707200e198001c40c2010180031441c0d0014030141082111000b14000447c0c40c044800600400241025 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 104725008 1250 104723758 104723777
    0x20604020f0a0f0e190204081009030e12010507020c06090d06090c08030f0301180209150304020112060609061d0102062e090506041a09060415030f060207021201180201 74
    0xd54803489480082d20031852000f602e1911241c0031035850005035a06400f9400e02d024107030356500345000311010380e44508094120107800180c64005041150310440c00d002c202d10140c1c0c1507880700880402420600000401c09040c01c0202071305005503c421340c0d01a040c2081101081e0303c0390039040719015803010000910352040e003401d052603505030308070700307102d002c00541400c07811078403409141640c1406010b612141044140f9404078450202c0aa40098403080c6071010b4101d580e02440d40f150040c107200c41d40e401501001c000300c9040707420000200f40c000109220150788500300904012170000442c0b40a04498001b035a6010024120100444442c402128032580035002000d0f601d0a1a00301318031944805422014010480c0c82902503407070003da44482c1c2030038440340001d900020b030505e161601c45906020103013a8002600d0541c1d90300860000004010301480c4910034000c20005840300784a10410241c00c154aa940440c2d80c18040007809802d42c45042c504401c0d42420100001c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 104726258 1250 104725008 104725039
    0x30e0609040609150302270114121204090606110a0209071b03170f0411100207030c0803070c230d0311010c020d030c0f02120d0b0d0c180b0102060402 66
    0x1412207900507001240c00e044c4610440c40c980a4101e040d40d2007201c0c60a010030310b00145d24603032072507102580e1481000000401c041a02d0f103940ca007a40e880640440b500401100c0603601d84070700106425148000050100326070042031203088094401491f10400c82c68408a1542e904c150003040030b4030490070000421400b078001c0c2282080010782c484c20520301d130524100a844400284c0703111540034140300020300701006007403e240c481c0da0301242c0c120070b10305c1034030500c11440c214141141c154407814001102149e80d58103580020f0050000942d62450b01d031528010302c50980e0300103c01100d21102002c650030010b80030b020071080568124522803250300b030441700c15200c10714030f4205510b840107513254507a0100d0301e600446091344003400986260301085a2640c5005400030060b0030802900744d07940d240100a00040c04038100124a84040351300040208840340d401700c074518043c1c881041400030200c070382400c04415401c208412600c42c00003039110500140000d00c43c03c3c035104800744 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 104727508 1250 104726258 104726261
    0x714040b030a090f0605040501140610140912030306030c030a0302060c1c0e03070515100302010e0301150f060905060f0f0c0f0708010b04050906010803070312020409050a091e030e060904 82
    0x901d242c100032211003131000d50820000a200660301640c180d42041f196494035001000340d20300070350010b810794043d200d542d1800c882c107058400400c0c1c003012042100d0b030210b613601c440141032650048040d40c1d50382482c00030075181280072042345000f5001410042e01117500031817032aa10101c5c5180280c2e48044501031003800401f05411848604d25003220048607090010242030301503c10009c58014080c40040355503640700071030b5580d41d090580d017803d10065102e5082c40100580190001c2558801844800103c2d1000d400c200000c0a005d0001c01482c1d9005c02e146006060950b003030781c40e0003a254500000d0f445484d01c65610840700040180c100384c1c040203006001010741c0d082e20105030301d54480c00d02900c0d01e00c0703070144036904100c08282c407144040303005812036140400441c07401e00103960680e0103400307104003000e000341d0038400000c01000601400c2d00c103140c480000502c00c1481e1070460030080828010411034694103c030000007035003003244c13000100d03000c03104651210300d864005030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 104728758 1250 104727508 104727521
    0x9030c0d0302120a110a03211e0b0303070c09141006020706051b010c0503011d06060a0c03020304080a031707050c0a0213021e0705150f0f060103060e09070602060714040b030a 77
    0x505030f1090044100c281079101804c031070b0301e510030242e01c08c0320220101060240c6218502c0d003d12070b00380c0b6482080c070351100d82c44234824201c06800d60b4181a50b984540304a064a40d1140344003945030180d906220300520b15140d44112904d0130100c02c50300340714000b9507415503401008180440018503c481600c00e00d9034003090b0505400070311011030b202d9001000d540007031103003800801440210f120011413003040c180c403503040605403605001c801041102c001a1102066042d80410840400d41c40f40500c00d5800890180d15010b6600e401565000040700000300382104120b024050001e0a600214540c0656501211040880340310742000400a1040c020604001c40c0d1100360041310000600c09456400e002c0ca09507104420000034604070040c00b02c40111801c0310010006680ba50581140c2c0e400c200c040c034000a000b0b03101d800403d004c0c0c5090391007a0743c55002040030420305a0410072154001030030b10b01b40083d084040d044900d00c1c0501e024104804070040001000720700d0560003207 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 104730008 1250 104728758 104728787
    0x2a030403020118151106070504081f0612050604050d031407080405030d1401090c0807080103080705070509010303050c01060f081207140624010318020d0c150509030c0d0302120a 78
    0x790100544da01d0058800c072000c504105003401034600140e41a801403080c2c50489681d84003503c483c04500883d401003072022031020081c0c6030b0342c1e50041014003c2e031030700d2203100e4031034070084c8a94106403c3c02071a211840040200301800e00d0603040304200003500c032641010560803c0045904c0300d1030024154042c0d084040c540b64903103251280c04d094034651060480d848050208185040560119035444040b1303030361310114032080010030010b040c55000f4144240144240c900035900c91000034082c42c2e0a070f100b80c0002e03002141003c4a1442845a0f400a200e0300d40d001d0070b05881c0c0410700d921440d00241151000101150803c10700100b100604507046040c010b65030365140060707151401c580e40040d00e00c00c01c06042c0a05085500034407070012196414044010324500640c01c201d00c10010f140700300ea001b00c025030300140d402c2c100000204491550303100c0544403000a0281071418000c0c4406500c21441641c100b00403c2c0c0108216040c041040181a600e400202060b80d0302c0b2240f0590 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 104731258 1250 104730008 104730029
    0x31608091c030b120604050622020d0c06030e010c0f030c0339090602070b180d0809030c04050610080612030a0807030c020615270406022a030403020118 67
    0x70441d03490350642c803011928100b00c44030824080d0701903240342d84031002c84e40140580e000c00e0126100c4101015058040c450b0309109001c80c45090740440c414a00709002250701c0d1004450510069401d07000301c802c00100100208410000128020262580740c2c1a000178503a8a94071020741900c2a086032a4807a400003040c4012a40b500706214030011500240e80325684484c1001d58140c42441d5080442d800c5038014642c041c140f16401e2880c2c1d2104911054900c2c9109400c4900d0f181c50580711403260254800a03154041c06090500313107040d0700c10381807080d0f00d4030040000c140ea8001101c01d01856034036041d0099a60030011805400c1c0440c013400d83e0f840089808141580e101403c248918207030f640501000180d2507099030b03605400c0c0c460074550300b0780c2040c203509424040c48214056032000440c413a05010401b81082400d003d50302512901e40000700d080c1e400719485039140c10007001044400041d9099000c847d12400385010007810400c1e103ca014080c40f100600c03070b4001c0d1000100c3c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 104732508 1250 104731258 104731303
    0xf02060d0f05010311030d08040b0c130321120e0a110f03060108030307091211130213091508070b030a050a0609050a14010611070b1b0111070c090203160809 69
    0x925403120350421035817030b10030301ca8600e050b442c0612030035800b03005a81c442090015500c800702c4043c815040b4981c4c03c1d2128418200c0000458280341d10440380c582e80300d0a002e039542940b02c008105d4400d0b401c42c8a44d1a050140b0700200100024600354400d4112000c600358030344900c00510001e0386046004e5051041c100041742c0600080020b50040c00d4540f03d0981381a40d0720884490020343d580e01030010440c107203750019007014181c01250540f2080d00501c0c00d0b080000415048480340c01c001242651600b031081008004030b00c000c0a09101c03c020009517191202d44006803000400600d030098445010811801c00c681100010f403042c004144040d00e06440c02800418409078014420720b02d070b8000103032060003440400040040040a442210b00b058492100b43d8841000405080c600c0c41d1198885c01080c41100e41300075900340d120340d403180d0508180a6541c1c00b03801540f9041d1040080c0b004106240d440d00c807500c0e004d814100c0c01559112051410304070801d0311041440c40c04171 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 104733758 1250 104732508 104732513
    0x120e030c0a0510150302010804020105090f091303030e070b070215070b0a0911120d0c0c0518010f0b090609010f030f05010f0510140702120a0f05030307110a0f02060d0f050103 77
    0x282e4411040d0041d4080200b0020070740007200c0134a042c071001e030200e0588008035000d54884c800a010f482c0f006081208010115008a01501c8040b070b000706003c00941d881c0010540d2600400ea0f00305410801421460b0a0149140e0f09118031000244580031300351892046400d84402e561301d580d04039149082c1403a0000421000c0e00404100b00c45050501e154443e0707928001d1240e03003e19007403500401034507125a10075107031048809002d49024450820010b4240d4030103184c80a8100b0b401c48a111551604e10860144000c40d080302c0c0110809110280d0f041d1038034010350300c0001092038410a40d0702c1c080015001420128070080d91103041500200e0041c20b00c0503131204440d000e5a1090702281c50031812030380d000345c11401800f0b1a40030842c06c00035240019400748881c3c80d00041c0c6c2e480080315070b40c81c456a400d21104496a4101000b004502074001c04201d5030400c64030013070309918050b070f0344901e03548642c080300a00c1040d001c10504000101c41c3e2200c00880800c44c3c0800c0a940c4a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 104735008 1250 104733758 104733763
    0x6050405010e01021606110f06040501090606050d1203020307030b0d03090302090105010918020c010209030f01060602060609010305060a05070509060703090e010b120103080c0c1c0c050102010c120e030c0a05 91
    0x1402214080b484038008000c4951001601d500480710440341d480c141c50a0502c101e82a0641008504c042d20440e516581c502005120950245200d0000091207003164a420b2084e507007550b2001c0d105662210780d1a02043c40c0c0005010340c68003514005035250b642d20802d400030542406015040242000c1000c101900004008140c0e4001c07203042030f00d070380d0f5035004445007401805030303100c403c06002004942e060780741c0113403c100c4142000036041505030404203242400d401202c005580d1540410080c03103405000a6400c03404c1a0b0740c01d00c4540c115140e655031520042c182201d20703507503a000102e6042c030640030340d0a901001404103a884c002c07420001d02c401d2040c00b0301e00c812b151002c000030300901c405081300d800c4020405035141e40e03880c40d1540c05094000800140c4180640140c681e02c543c1e41c88001181074010104a076801c50380c0341800c421010f1036070031403415685400f03410b25050340c010b000a0206000d485002c0340325088036640c103003103002d40356548100f0700c6440c0c0c5075020441302 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 104736258 1250 104735008 104735017
    0xa0e190b1b031e0d06090c0801031106091c030309020a12030206151c08040e040f0303050a0b060301090c0905040f05090d02011107060f0e060403081602030918130503040605 76
    0x10403016000088038403101c203807248140400780b030500090396001040700d1146030152000403107413600010346a6840a1000c00d030b800d0000820300203100100180200160203000c01d40c102c40a403a00c504011010002c5021400242d1001110200ca143c0240400d0b20a07000311a070240c0c043d010040380c03541c9010252150852480440140c000e0340009107032410100229001402e0080c52410110108071aa110390880d0140585924008200120f8820f14202225004510400001c0807046860500070100c0304048d000308641c6040c540160029175509003580e0541d443c4060019005240d21019160030138079034001a006414100100351241095200500c54942c410540b4962030320000101d00300c60094a9640035070800380002000b24286621102d040c0392034950000d11442d0040c40586004000c072412000254114108510811132346440000c0b1107060004508100c0003000203102c410000c0311303800300e42e040c0800044030010381100d4014a1504041034a07034894584400a01c180d02 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 104737508 1250 104736258 104736277
    0x6070212010c11060408030a1112012909090604050a09020d050c01020616080c132d0f05090103020f010201090210030b1011060601080405010e0102130918080a0e190b 73
    0x480550311660f0b0700340801c2c039900c5540d10034183c52440d07440c12512801000450100043c0d0701090003043c50048004014034083c0013a1505a180064603402c4007000361202803903604084014008929240c49200c40340c2e0f0016070032103020031a0354420a07503000a003001d0802030341c0f000440030903609001c0c0106804030080c0087e82500d0260381ea00c0008000c07114170111a074006900c50000503444041c083c080e24800032010307245c804643c2e42d0150b00340200ca0300d030710a140590481120301e403d07680161101f8001c206a400c040021031501000032014981440064013405046210820582c0700394030400c003442d801042081c0ca80080c440c001d0080078401140b50040c00c4121080c0d0040e801400c00300c00c0301c00c0040c01442c59507030f0100115050349001e0005c440b03540d00c035892580000804c0c0050032039141c0301c0d140801014078000d40c031400e0703522281001201600a049139008070ba8040c0480d0016082d504003200500c0805021505030782c144090241e555001c0c1a0105450f2aa400107144000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 104738758 1250 104737508 104737517
    0xd0b010e34031b02030a0e04050603070308031b0c060403030c020109080706180b0106030c020610060504030231020702040c09080717030f0315011106010509010e0606070212010c 78
    0xd850644110714101c4501c55206612078010041d0524400d044001c0d0007001d1a28002c600401001c40308180032040d04101c3e805a013003c00d00413030040d4020b009581e0000115820f000e42e00b00b002c0826101d620341d0201a006440000000c1c141c4202c0320059059551b50301078040d074034084c06c0401a2109400c5c0c504030b000904200458205920500810150541000b00c06c2d140110b5039440f18024080340c10880d0b11107224031520fa000c16103d4004070b00034030317854401041c0080e55070b80c000d00f0060002d28403600c0d4001d070301c0c05000c15503002c419901a60340c1030b120402070b44545500304803000080d00e60400071104240c607104140c429034000c0c1c40024402e450034051030f42c401e04151050b000900485515502c036035004c00c898541c00d8031842e01e41c039452041e00c0c500000350005000c3c070751040340c000e0180103940c041e401680d680081d40003030414140001c1c0104e9410702d00020320003c0c3c18031030000c0740a40070020540f6070f03984d44e04841400d58000c0402004621004a140c060003483c21a100880c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 104740008 1250 104738758 104738761
    0x6080108010515090a0e0a03021c09080303150d242307080a090c080c01080c0712030203040303060b0d05060a0503010c0507020d0f0506010b04031205090d020f0f0d0b010e 75
    0x203441401400d02606a070616001d00300302c030f1010300c0400d0300010240e003001e90f1150651071402c1024031041900d0b0f0301030b601500300d040c000074202c4a1402c00703400060400004207002c210b0304401000b5260020b03a00d5440c980e0303160309100040c0002e4000600904042001e004a150341e074201c2e001045000c04000e02070000d09541910342c1031903510100c0100100c1c020b000011031640c1303e040c00b10780c01301c42400b00052888240d2109400c071250380e0808802640102c1505940e982c118880e603a0104050034080d1074403140f541d4002d24855941030400500d50088042802c0501071340048019242e000d0f02161905c28801908029000a0701e00d50f0048202090103d001d0406000c0d00302c610565849441c41d000d003581c2884000c0944907010380c3e50040f408420800114240321190080a08100c4a030300d443c1103061480000441d1034050080c09000c111450880d02e0742a80360f17a00300d0701103d0808043d1a00300206080105080409034449a500742071800c1203031800183d41a24002454034500c2d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 104741258 1250 104740008 104740019
    0x510051b0a0507030f02071e090b060a050712020709091208060406080c06090a0f080601150c0b011e03060204150e030d0503010b130e0415050a0c0f050a18080304060801 74
    0x588580c00d00c0700000740d030401c84100800d010350041c0902c03000c41d104545580d95610300c1d1078051b0115040d941c401d221000c10400c4101e00078050071890801c1211424a810004400545280b14032800188070440c915005041c0320b0013400303c5d20040c40b40c000240702442440c034000d50560301c00c0c00214085441000403c0d21810640704140903070354910010403021981d02c0800c070b15a0042c91005600038449403000c5203158014a804000f4802c4a00500c09941010854188841081450010049503000c103401058151100604444800c02640c504110b1f4400c100c16001c10750300003414560001800042c003241005031001600c00d00d0782c2d01071880f0170380700400d903e41c010414060700080d81403006002180c0f203080200404041c072808040785540e95114035840020849043e21030340c5500f403c1c20b151282c0342c010720354016001c15080104155051002e440c10898a1081d0108640492900107041c080c01d1101380905540d4980d04015a03148012990303603025010710400030f0200c000004030f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 104742508 1250 104741258 104741311
    0xa09030215090303011707090c0e10030902030a020402030a090b0411011101050f01060e010903200a0801020901091404020405030601030c0501020d050a050702063405010501060912060207050a051005 87
    0x216000000b43d8556442c0c00ca06020160000c44580b00c54064003000141c024024400c9001c880410b45075088202e40500130032524070070340502c5400341410078038018010f0f5030102d03100c240140d0488005850b5102c88413624003c15440100400241a05051000784840d00c3c08500440000360385880c000d54070304621500365402603900400e040b04a00041c0101401085400d2028206150490341580e4a032640d00c25031503208101d00c004c840700c1e01088041d06100310080041c01c80880254586920100002d02900c0031344121707c1903001c48103640c8507c1d0b44070380480e0000d11008040300e00320b5840c0d060240c0030b41d01611585015101c0c012078101e0741406038003a18140c0382142c071083d040401d103800340300352507024100364018190800034400d40aa40c20240b540b20080f24031555403401034500d411800c562068002409002c4440300c20000403400a80c204540342d4400320158035043c80b454140d02d801841400101140150410600728035000c1d0310161241f0317083c03441d034021000480a00003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 104743758 1250 104742508 104742511
    0x106060f02030403063308010507050702032a03101b03090215030a020706020406051b030405060a03020706110703021b010c02061207020c060d0903090b120103121103030a09030215 79
    0x1681083c8800c102103000b99101c1d0103400e941c17500c1c2c903144506103950924015020300186e9005407020300c0070b0081490134450141d020340e00c0e041c07151910100381c001aa40790170881b107400151540520110000c2561110340b45000405400c48048043d01c0d44401c024159404582071004071421194248178480c0c0548001c03030b60054440c0d5411644000303d40740a500040261542036000c000c02d50008000c1c0c4000c00003410b0b2a41c9482d16041505118044060700000c0c0ba041da500c00d00061089540388412610140b80e58140141d80d44290300d8460b02400308031004074241c42c1d01080e46424150045680484070320f545c103c2c40034005a4100542e0138102c1d142008e900100140070f003001c1d028540041076005803040c01158070100c0000001070b0300d6440702c05554800780e12a40c40c1c008140d00041903101030040000000e040c0341c2245205d5241081c14400908841081e00e02c40c48042c0c01111110786c0f40c0c1501c0250fa60740e107000f040c2d071000b070420310800300d005115130401e0841c014440740f10070307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 104745008 1250 104743758 104743787
    0x3031303031d0d02010503041a042307060927090303020a12050907030206030421090510020c10030b0d0b0708060a080a020f01030c0216090501080d021c0f0e0909010e010606 76
    0x8a1410803c0d070011a035a0b0001082140d140e0002d4007145450080e101100d48a280f003004d8000e100032403100442c124001c0300c8c07038800e420f6100340b20902000b13810040309019034000549003140c440e241c00009607201c00700b03802801258900b07a043d0003410383c507800070300c2d038203140340c45500b07031001d49410400403103608a0b43c00d40b0036000020b00340700518103035008580150040703072100c090b0350110941c01c0c00c0e441c450000354049081c01004104c541428500140c0342d1202d4006071450910880100748011010302c0380300101039039444071403010f9450201c003081144d00070202c59043e1a1841000e0001035098800c644a0751400b280003400240002e000305142d503003e08199441207600f00154060400d00f0108800d40c059540185801006800220018170a000000c035103549450b0115003410210300d400341c00c41d0800c0b80040c4140030700100c3c0c4207406410b482d2a01d111403c001c021110600041038041d405400942802200304c4150400c007000d883e0f00000300213a81d0f540303105690324049141d18 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 104746258 1250 104745008 104745019
    0x8060a0b010f020a03140f0a09090509070e01050d0305070b0c040305070506090d02120c0402071a070f09180626060705090d0602181810050603060a0314010b03031303031d 75
    0x1c2d20030403001c940b1011b50105141030035504003c401654001031400c10000390900780400010710b071402201d4100d010390300504a03190030404054170502c1d05000305030051001c00c00300d00401d4411000c03662655003200f9803038038504000400850a603c54030055805206041e40418241760580480d0341c0d0081c01080d13826200041d60900000c030014601400850082412400c1261918001801034502c1503106d50074404203c0350324091040c001e0214030411880e20b5940710350582003444901510841880d6081181f040c100900240519811220050300030009420481d40c01180b041c46440442040d00c8499854001c102c490380540c003284e0790701070821000750011910681c001c224440703c0d0846900c048901d007020132140709407603083c8c01c4030b110302c3c3d01007040204603030b10444c010380403c460300703481c604042c0000b41a60080e8000901030700076908072082208825403040c10880b2001d019a0303151000f44051000000540c48280c2c0407458400805010006035060340c007280b10700a26 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 104747508 1250 104746258 104746273
    0x22080606031f0903090f14151204020105030c0d060312020f0105071d0f030d1806030608101d060403021606030905151f03050706030f14180c06030108060a0b010f02 72
    0x1d50b0042c20103c1c2c81034042c0213419402281c041c0760300802d01e01911243c0c202d0756032105541c060112000d450a4050140c801c140402d1902c02c2c42c0239021500660240782058590300c0701c9845207814410680802c00c5185003440c00410821510740c0c221820384281c00f604e44185e01c0c541201d0913108220759410005400a0034214a244c04000b5103905240213003002e0342c3c0d11021004245429440d102d50380201e00001d281e10350100034680f400003d001c40f490705021151501c100b29039601c04c2c44032440146900c540f4060703461405100500300d890b4084040342c44606082c20f0103504c880000f80c1441d404001d90720301042480c064024044180d034000000d040c04102c07100a13852500c0301a2640d210b803541e44400c10a4010b44441c4100603601850140119510301140030b0200d03200c200c60036110034200b203e2061080d6400ca000e40c0e10440c0700c8a201c032840340602d03c1324208194000700a5100700044004160004c0000f030007441800380c42010410410290010340316101502101700050780a2007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 104748758 1250 104747508 104747563
    0x10e09090708010204230a061b060b06120901051b070807170c011e050f0a0c0509180a0e0f03042102040207030e0a09020f0a03050c2208060603 63
    0x1680580c051003000686041a460b9106542640d1050f48035440c1e40a2581030300507210ba5a40c0302030003140c0c046070600c140301d140c0b9074081c1120702d511101c0901308070ba0000000520066401021804d20f00619147e640c250407100b940c164001610380c0e044940c070b40310010381c03407512080007290425140001142020030503a0358020542c005071f01121664002c02d0f810440c065442c0160641c2a0b1040000c9201011044102c070309008032403406001908010521031404d03c4041040e0300700c8546c000115940c40c0c020320550b400e100c0c0c0700030705801c4a4040c07074035a13a003e000305c00d0b507000c0c2006071024042080b103c80c2d201c1d5a0400142c015001d80c1041000b0854020750a4400c007000c80710000c0c010803c441500003400700d0700300c5403007a008641c0d1034400c210f032442d000081360b01502d40800c0031400c0c07044820b5600b102c2d00882c44800145540c40001c9590700d50f442e02500c90140110341001c0700720042e0b072050701d0b0880d06d510481e90140705080c042047d620b4080346103440742c0840c0344800c075510f0551 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 104750008 1250 104748758 104748769
    0x7060c1104060e130b090607090b0d0b0303130305060603030702030d1d030a03090303080601020601150302090406030c030f03020708061303081302030a0303150b0903060403261611060402010e 84
    0x1501158420b66070500040e07115440d61080d03100722480c03081c0b40384d20804d81c00c01160750940249a020140c1100c410407050ba40c1006600007130304c1d65039107140d80351030000050500415906480319414400480c000c00d000d03580301e400c0003e40c2d114030151980d0b9250f51090540d00d0181c002e0096043d045200c0703030500030340304644210a1688211600300c4206440c00403a0601090080039000680403c1040c01416006400e840d0010428401002c89d58074141c11034042010051198007015000540f00e1003640e40d40c0c00960186810401e018210b541e280341907450f00943c600708801500515000250241004c502184134016120158000004c103030317021606400c00618102c804000740710346002584007001050f80d56846520005600c41100c6440c68001240e41e01c00d00000c00100b148030441d490120341141c21507850304045200c40e41d5043d503242d0341094800003070166001c020800141e05032101200c0301e902607546441d0804264409865202c0d034007103c3c0640492102190341c1820f0502 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 104751258 1250 104750008 104750033
    0x15030b010215041e0b0a0b0a0806100e090304090501080a1b030c0e190203100906080705010203190905060a0201091505060306190b03011d0c0907080c03040602040b030f100807060c 79
    0x400490f40c130078400341da6140388418055481661195407811000c2c01801d11442c1b103005840d0410080c0391600e004600444010f0711070080004014445010500f1201c1c00c00c213444c041c20425805000c0c560715100c02c2581d9580c114015100044004d420520074400581e508061741e820151407500700e4104120210b4500300a130450f5a840c9126a10001501d4070344091402100c10340f007100c02d034901c0d003a440c006039030703c03a040010243c1140c6c1c0c0800c16aa00001152500004020407070161000032100741d845081c5a40030769000f0300009070603805a0340c10350090041071301c01c204407100d015281d0b290034101c817403c072445a0558464004a0308003913002a140c00c000400c0d41d400b04100d40c0d044082402d440d16404440c26180807054003804030780083c40b83c01ca0340760301502c9100091a14a40007001da1001620340440008004049414000b140d0101c4029010b11180999241404645808005011a40d0740c40081004a020807a100045019011500103940d40c00d07140c400d540310826284030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 104752508 1250 104751258 104751293
    0xe090703020708070b04031d100203161103060709081207020a0b07051e0f060a0507081b0403060923070303092106050103050304030209090309180405150115030b01021504 75
    0x804d2202d900010b640e02116442a4881e50f0b030307042c82c1a0860003042214003100e607068072030740030b00b1201480c06034000140d81040448288042c080d000752304151017902c14221036507405009080c20400f2164104800c0022500d21804803035081d40070800700889402001c174020341c840d20240007002018004406003020314042e000b83d440199082810080b81940d81c0880c00e15500b0504030400501005d200b1554003505540f0144194170704800003e01c0e45000610740c1460f4519900c01100035408034058401655003c0340410000f803450816220359500308040749000203640c00c0c0760700f0702d54000c64614106c0f036143e211050740e0f6081140c0c0c20004002d200302e54442092200480c0003080c03183c0071f4503008500400165035100c0c2140140102100c0c000c04549203a40104400d503016101c000f000d107492000607480c0d04241c0c44602c0c01f58100341030f542400c2c603020b0981e4008108802c01e1901c00c1080d5486890801132034070303030900598849401c613464040a4084200103400b003503568840c80e00000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 104753758 1250 104752508 104752523
    0x801060501140a0516031d01090b1b0f06042609031c02030c100905160f030605060f10030510061701090f02070803070507060518061902160308090105070e0907030207 73
    0x2601e96a400e100176030084420707000144503840507410101c84403160304240b802843c16840e81420640c02107030030300c207041050000403006d00d80c2c29000300c01807081154207102042654510b00b01030034540f0b500c104c0d07002c002d40c1d03c01d1000d550008181820045890001010780640500d26041c101c0d251100764450258042d400308101c1000c81380740c21710071004410f090001c0001c0c526014101a440c0251007083d040c501c6001800a1000e80303000c2040b80d00702c0341d0240000c076456550502050035000c00221540c1c1000c4226403208984e40c040d0041751103000a651000c00003503072600221400c44805003404500d14a00b001889940002d402c42c20110130410f00161a0402c0f550781c41020f40e03c11140d020004e01c010401008001090169580080740e400c00c056074120a060038a03100c01020f440242e08520184c40c030001e0f1055901030b01c80104080c044031028002da8100604410b5084440d8001540b801000a103414060b0080038284c10004e000d480ca180c0d50204203070001d5012030400d84550 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 104755008 1250 104753758 104753767
    0x30501050315062202130b0702010c060f0f0e012f070f050a0c06080a0b04060b03010b030a0b03060705090102010e0f0d1809050705090102010c030606141b06070c0c0801060501140a05 80
    0x40c00c0044031110400e20740c0d138006035181e000c0b02d0704c40504403041d048a0f8003414100040800b607a488882c1c0900035400400001d034030042d480904005010300303502003051a05180c0c041e00441c90641c8940c4a8070702705001b120480030103c0440e054107036070340f902c00c7c2190001c2c4411808540c100aa2600c481e21039400c840c840d040b56181c8032240e803a698032460014801404120780065540038403112810180e40a1285e182801e41201e41400705005915483c0780110010300941c04d10f0b007200d064046c0260030341d90241409400141194007a920705405503007005001d907035921000846004200e000d0000c2d01180c41001c00031030b041d0020342207054103070000c4400407442c82c0ca5840b455001d81c9264031a40d688020401c00682920300440444d828146800003c1104070307040007102224441b102412595801c0755010b40340c405602c640114014418102001405500400344628490084c1040143d0750346d5644160300380c904900030a070018070078006603070408618201074840c100850034010b051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 104756258 1250 104755008 104755039
    0x801090c110a140f0d0807112103011409060a090207021503101502030c10020d150f050103050c04030c0902030403120e0d0908030a0503130218070e090703050105031506 74
    0x40c0484648242d6071400c00c8a003204045038104900381c820200704010300b2482d18802070103800c14070000d02c0601440a003164234850f413441400304018003410481c0d5550001d4440c0c40e000c910f030b0030034060490802c22428094a480c45c000c003803184036040c0104071180c540d05000107107019401202080341c0044c00183c0200049040754061807280514404041031289000b007030080c0111441c0c100000d5420400c0000c1d11030201048004211728031640140c0c1c1d4905c5040114020a02c8945070348000020300d001098150030380f8000002c807a001d9a06000e580c5440101305918411403100401402018908010078003158003d5580300c1d0107800e0a903600e104115030003044c0c540f4069808101e03003010300f04968080e04103c140d030203040428019030906401c0100030b0140e200203054000c1010a6400000c115a210442c0b00f400704074040d40181c140c1881d64029041c004040c08051040e104c1000044901d40300c0e01c41c0b1070486800034014001944654820207100c940940a03907004641400855403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 104757508 1250 104756258 104756263
    0x80f090d0206030903030709050105070519050c0a03030801050f010201020909070c02041e05040210050310031506150908010608060709030615032901081501030210030b13020702030c030601060801090c11 89
    0x1213216840c02455580c034102d0401800406035400c4103051050a1108a000c90030020b00742180043e036405804510119080035491b085241c2000c0da070091240034040109940805950b040311010385800c0034015a280069007070b4080c14840a400c1211400006c4001d0302c6015940100d80c0050000038007000e0442411050361850950503644944800c20301045003072020000350000c4d01440c045065040484090b80e031107510303220140003000c4074440107524401d1548550f00400070f56040002441801c2406469100319106400c0301d5403a042d80014007800c0401e0180c0309504a40e02e056a960565462800810b04c410303151001110b800c0000c030028442d40071007641c850b6076003411110300120403c40c92001740d05800004994002c0000214086004440e06040d40c0d411a00f01c11580c90000f030841c000c04501850301c1e801440d021810aa400496004064482c000e40c1915503210284090641d544801e21403040015840310040240304101d40c0015400c4846150501e01a40105486403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 104758758 1250 104757508 104757511
    0x2071a04050604231504030807090b0904020724060e130c060311070c06050913140411130c0c0605010b0a020a080a0507050102040f08190f0305160206030f04030318080f090d020603 79
    0xa528824001403005054124048c07a5004000b49040d030060f90802c1e0f0031461a01032010304500403034005c00c5400801c4980202d4192840d912859001e0f0228801c0643e00649a544252400b002c0204017082c1001c00020860540315040100001c4242c41c0c00030480050260a01003094002c061209500140c00d041c00b400c01410b4903900e2940b554a44000c00c1070300500300855403415450322100301c2001d01007002580e0b010350440402842c106041010494880c02c5001070703040e40d46842c0d010290580c02c90030025016002c1c5104202d00e0fa2103060340b6450384a0292038030003681c04010841c000030f83e510300070080c076901d0749131040c20802e6541c0c456003a80c100b40c01c454518048600700b03110804c02086640c1c8210ba40540c016000d240c40d80310384007801c00f034007000f070b0030040300180c052000c581204030030109540c054452035403440d103203400d10111141a9000c40000781040c0340d00c480c0800d803042d60754102e07401c42c154a00d4280d2002c000580c0c0d0b03200410b04c0e40c005001001d1100503949a07400756 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 104760008 1250 104758758 104758783
    0x90c02010e070801020c211c06091103070c02090a06081501140102010c0f030b0301020909010305030a02010516200c030105010b070b01120305030c090d080a0302071a0405060423 78
    0x208044000074101070030302c9031030340150b0000d0b0320510001c50000c0001a11a0718110071030310a203004078501c00300c40308901c55007880c0801d1840c00000d82550008951001003221443d081c20864209200440030003848180d440c5d0f070000d0825082c00002d85040352015402000a003400584c0580d04c2c0da0442c2440d0074840c0c0011b00700c0e0050010085007141510321031308440244000c0050401c8000064840b0603440e42c8002003690700c0c00280745a071025412190080e10003003041030250703940d240940e580d61250b2000401542044042812104030308407240483e080c1c0d403039015100c1480051140c0c4c45482481140c0d032417051a000e0115034400b071103500d000c5c1400d608201c0d030341d0016051900e80f100d410b90000740031621403080d80010035400800d40350000c071500c1d0080e50390349402c800a94000382240002d00032020008034083d015070141c0c001d2054034072441401c84044280b0612410301d2038116000b0303100e42c00000001d4000b840c40f6034241180511021203041c2d8107110b03c1030f603103000701e040e408 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 104761258 1250 104760008 104760011
    0x315151115161101112b050a09031b030503011e0e1003050d020c0f10020a0606090b1002012703090f120c12020102102706020322080702010f09090c0201 67
    0x2d985080d03078000038201d007030503c400090240e40420b90001050b44103250144680203045150b5494441c8125810484900700f281c0030700590030310712564001031500742e0007140030800038805901e400d40c00900c0c140350660581c031040c1c02c5070303c1e25601080000c140e0b200400810042e00c0d021881c621a130070400d0142d1a58403c014509085242c500e242c4011101c856041d94003150070000f140e950703044040d0300701d08160381a01225808000070f078600002c40900502007030800b140841d10403660390129003901001c40300680f0710140c0c0c076026800c039000d041b24450300b01120000c0d5100f18038074281003102c1d20b2003450210348071690740c004180618000d80006d070681010000180602441500d51005071502601440d90801d4550010390b0390451407008060071512108941c042c42900d412001c0c41010340095060f002d2080e243c500c1c0250310480780e01114074180c8017101500202d103c02208001e603c09900d0749801619001503d122400014143c00c00141c09800b0525510710300440c485031241c0d800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 104762508 1250 104761258 104761291
    0x3050d0608030c010c0e090f061005071203051504140408071a0708070207170a030807050c1002070507090603080f031003060f090620040e1008010606020d0315151115 73
    0xc00611106c1e4040d4494030484081c072a84c89501c003425504038000b25140b18820072060f1050310a401440320190150210840c91441c49400d0780000341704150a001200001c2c0b4010300b04400c40e0640f080850b100b03011000041c0000c1d0101c8002c0100901601c0160206196030488944402c0304842c0c04000030071480511400d01d404001e001301034400c03c02e100401e14881c0c0d07001c643e030f0f03001403802504210304100410803060242007100e20000324441a0750041501200000280d030081000b01c030188107042002410710300340e02c104800d80e54000315003072074106140031003d100e401c09482c0504050083c04c3c004005140c074401c0c614000584c41001c01c240e055424644100c0300d03510100541030f0451400ba0100d80308a208503010380d81c0d1483c41074004d448204062038003101c580c02604071980f0b4018041145500016240010034031650184007465466a10901401180c0300f102102c0d11000a035102103806501111414042c1a085400e8080030f40c40e040701c284016036151101624030714 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 104763758 1250 104762508 104762531
    0x60e0619020a03080c0910030203040606030212031c0e06010614040f03060b0f030a0201080c070c03020310140c0f070b0402031911030c01020f0606100c050706080106091401080403050d0608030c01 86
    0xc005540051744000103400c180810000c1000194010400010541e00100080030011558002d00155401914040b0f0009541511680c3c0e580003041c01c0d10600122441450300000a00490405020f8000600340c0c82e4a4500c0c1074444210380c420050b0240018000866800565450354001350701424000c0381c0030f5040ca084c800403c0784200032501035080100c14002607604140d9a40e00b0078484220280d80d0400e03410f0150018000d0380009506000e030030b182549400d1a0b4112036190a880540051a0f4030b030070030802e41d0340c442c0314480c035101720080c8001c50101c1c2e460030000d90302c03e0020301561040e9201d0300c901d40c030300b40080c00111418501070344e90203400d050030821400c0e15282070004103500c4040301403071981c0c0e800050941d03104042e1401561055031041445803002a07108040b41d8085840b1940a085000240252400100d1107203001800104c0d102540517002c20603160611036842d903460490b01580050f0b9180f40c000e0305c8180000d9075540400c010011600d540c40000764450044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 104765008 1250 104763758 104763767
    0x150201051b090906010e0a0b1809060a030b13030e130e010b0105090a05100512160807050306210c0a1419030b1503100c02011a0415060e0619020a03 65
    0x1040c00d0480c5a000e1000724243d4480104640e002182420001020f070844400121000e4a0760440c111180c4045049402580c00d4100c1441403030302100d42c5180c99a4100900c035000c50b6610010f0602004030020520281d1003111444289029241c182d19010307100002c50b5044001400f0800440d0b6605001c001d81b11082c403078090041c1c800d20708549030203450000181e0f88061030003098803600900c1a50201d40340a0700c1250310790b04491400507000d150903410406054804403050000c61520000251102c0c80b490489200d000024010015030129400204190301c1f03050031150b403445100001d840c0c0d80e403222142c4005041407a01c5019443d2413400384030702070702914404084070400d8241800010103524005602104001341b0448022690303000038a00014a250002800c0c07610400d40c2c0c175a41d040d0032481415803154000c44a000f02d40050008490b905039042c50754000c814030a01455220701c9150701a20001041d175414004e145440f02140909034444234003581c0304400c01010036400c0f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 104766258 1250 104765008 104765041
    0xd050a0323102301110330060301020f07080c070f090905010b09010b120901020d02070c0e1503060105010e15040b0a0f020a030203040302011214100503010f0614060702030715020105 80
    0xe988510f00c043c25400840d00e14003a10064040c1072082c0181101c00700d100802c26074806040c003401440351801c80ca40d42e4024189400080000b101d520400180c06080500031180c81e5140c030500b16290000c16241d03040c494212000c2c40c0c0c43c9000c0e0702030000c1e101208120003800340100101c001003d4126190003404c407a80682402c0c007031080703480104100481081a6201503002184003a210b54071038810303078024450300300c800c0c2d5824808914501408050740c008010f440b80c3d180d03000c4a80d25168160106808004800c5915601084c01032005510604a0340040d550140049424050320082e032046e61700180c009003007040c070124200780035580c8454483c6050a8500107048150b40c80d84009440b84524000170707050010800320700e55031424990000c440019880035440842c00c0154000010050620945200b0360034500310307040d284450300c1541d040350111849103c01040540501c50544c022460a0b44e050103603030000908800315401030194030f00c1c0307680001000c0ca40b0307c40d82d1042c00310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 104767508 1250 104766258 104766269
    0x30c091128021908030a090c120302010b13140604020c010f111801090b0703030203130206070309062015060612070e090f042406050a0806150904050d050a032310 71
    0x200860500f01060180003100d801000e1003c01261100050506450403c0e2982c444540d02d0f01e200114010300d68107600c4805802005c880046099001c0c104480c01c1d0780c0740500350201c0c070142401240c8985416030081003800c40788070020070000a6844104120341c860050f60740801c0300002c44001d4002c210a850703042c230809081001505081444034400741c0a62200101807550000100d8021007110b40070142c01d0354020f1000d55038080c145002081d1007441c0c0b01c3c1c03401040040d013104034621400850704854810f070900a2818001204002c21005806841c2540040c8208510107905038413200151140b60241c598411080c4800c05110002c1802007643c41c05200240034030000070b507800307046451080c0491400410000c2c4d43c02c020001d04899101c40d030f005005403400a410800814200d1080b8441c0c20b24400d03400d120410702c8045075088600501b13035006801240340e02d03030088015048006113490001403205010b80d0611100c0e24072104240d05040c0d0303508003d04d00c0c4481c2c03002c9000d0306 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 104768758 1250 104767508 104767543
    0x120405010b06040810020306040908041e060509030a1b030204051305060a0510090c0908011b020c030f070510121a030c010f1e12110712020106030c09112802 69
    0x24540b40800b078030346171004050240d098000010504580e5030f40c2010000c250082c02a50f50380b50385801c18008805015072410f49103e042c000043d045000b00e007525007040010303000c1c011066150340c50340201081011480507a40303203149c0200150301e45124507441106201c141010300f004504001d4508074008129111302400c1c0740400400d59562101c24045646412011940c4641d488003962a03014580090540e5840c1c0301c11311002414100080c2c246040c69020345242c580f48009043d142d0150b003500542540c802e41c010017541c2080395000a48941515280d05030280c907841e450141e41b4842c44c00c044000003181030301014a014094138041150900f003c2000c0c0b8004480a4468517040c0b5042c6a8800c40182c6980064003400a154981200c0701c020802c06001884000068000810642d80100b402c00140d0109005101d040242d030f421642e070310002c0e45001303e540041d10791a14047e0f8040f0042c06072445950044540e91082640300501c4801c1c45900031000340340102040140e103650 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 104770008 1250 104768758 104768767
    0x504090f060602250b0901030e01050a02041707120b0702030d1407030b0414150d0506010f170d08061e040207050601051e01080402090a1404050a02090106080610030c020111120405010b06 82
    0x11582007030a07408550000145c1520b59200c2c00060b001031200728200e407015401c0000300812100540e0040c0142d8030380080d51121480c0c0009940c3d0784944a0240c0754624040c805420049000703030060a902007018412241344c650803003281419140701c4003990920100724414802840d802d402019101c1f00155010081c51030b21100c2c510b03080d480a0061052403c0522581300551642442042d00c145c102c402c907511943d668032041014140c0b0f115000c160003900038101c074021004208c0240c0b01c0e0b5269640903854450904008000d001c1d030b8601a0524505101000181c86a0000c1c200540c010350182244d50725003002d100d0051900c051000c40300042040750710907a80c010003100d41094040d190812956900440b5500500344040344016008030b1204000400c078000624048003407094480d007090b82d0341c82e602510a00d03025110207912046081840e550ba030b00ca83c0c0302c004240704503c000f0560040d28060f0402d5076015818000709400144104014003500340900300303104005403030040c0752 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 104771258 1250 104770008 104770063
    0x92704031d060a0c0501060b0f04033806030c090a0e01050a060b120c071407061d01090b0a030912090303090b0702090601120608010c0c060b0d0302030d09030504090f060602 76
    0x502c103040e143c9041c80180244001845400d510000c0079010b501d000c8e0383c0d00c0010615070f205a800c2031004640000140081e500302180d00c0510301c401100440f4100301ca91402c0c0030251090b000101700a800d84619040c1c0001039171100a854020318048034006005a43d241549095660040c429680c80d8200402005051401400c070303440400321001c40040c0341c0b188018226184510140913144604410906008410210307496049403079603221001400c42098509805049484480780403469449040040103402d030001c01c0328003d645000148010140d03200c401158001d0318440026041040070700c100758000b032801018195486035a81450745650001d003003000028403081c100301001560b060001d0550300101c001c0c19801c4c0c000d114440d400d01c0002c0403240c40100640780c140c28005002080c4c109080a43c0325642c041c0e002c0c0d813900640703c003103002500756120100c041000c20480050307107141d1489100782c0e1040040d000714901e403074808000e1601403031015545c01c0e082042002d508 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 104772508 1250 104771258 104771269
    0x190804151707110102070609060203060310151a09090a0c020f280c08010203041a060405040203072705090c01141206010c030c061a120703030e06092704031d 69
    0x510842a00d40031190b0714003d0700306806801a50740060a20342400d00b4007003000501e40155101e06801d1302100c0415115071a1a000c0d01c07030584207060000e04c80d0006001840c00c1101d00185070704a60505d84c505407943d404119200c10440b1407500e2030340d5400b0807441050b810302194592000210040c02c88640004401d10100601000e0642120f4100103281c104a070310008d09000b002a003000b15101e01d814100394140c22840745a400c50344a17070100044182c900351040601403500a40104a02410482ca0800e044000058019011280c3c00e2041010045008841c424040e500c0609010400c1c00000740600d0703081e50300750940d100c092000f1482c041c4a00c0795903600c00c100b481c120141c6001c5003029191103c1564000d440d20f401e00803801d24882e01003070800114102070792500718034910109001e407035030440d000080c0007480000520740030380303010000340584410007010404003090003160480c00b2244071111201c08040c680030003007130640040404403030700900c04800325102d00c040b00180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 104773758 1250 104772508 104772511
    0xa05091c150b1818070315150e040303050402040b060f12090c1e0d060e030901020c030105010b090906031c020604060b0406050d1b15110c03070308070b091908041517 73
    0x4880d041c00d80003d818075030b40e00042035080113090548503244d88a00b000341700c400d840c08141c044182007021100d50308046a4011040f1044048054684e13107480c1c0e03045014003c00360040c2c1e800f035200c0c200b82100ea40d40c41c00405c42491036200455590600a00c560f1644600030010f4942c0c0c3c00c0802102c80b15121698880a1800c8100d00c0c114441150340000380302c1520703407a01400d03071171a00740011009400000181900ca00980894240c4503508080609940013405101804d4106004600443c1001040d01d41c10201c0203040d180d10781c040c0c045684480920902140041c4d2212082c00f050058030311407400901811b40d420b2250030704113004108180c4210798003d04024203020081c0c06034aa601c40302c1c01901383e00c901e00c25080501c00700241740c100c01d07000d000c0c1c541c0142d13a9200518900082c0c94011294030a40890804105490b145408200140712090078046c01400c01441c090200071101c41c3e51103103818035103950034059800124080800c0305401c1c00301549003003007054000180b09 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 104775008 1250 104773758 104773789
    0x304080307050f070501060f0302010e09010f050f030a05060a02030f01080a0b04031101290a09020c1e07030503131401030b0d0803130212010603141c050a05091c150b 73
    0x82c1c0d52050810308880e000d104200d4064025460b0450224590740b00504c1c00f011039000340d89042c040300e00b1400300700c40d1010a11900d500103243c504104040c0c100021b400344c0d0910028103031381c0c803e05641c0703602d420300c0f03021200380208541c00001c105440d4803029034030b400b404000e0020078007181556100307280c464001e4005020b110940181382d881503c00d421a010200ca40d407207000d00950303281d54014081518010301c074030424208070040303612001d520070f40e515a030a1030300801c0c0c503a10200000254500b014801c180c0c0d03010304c42c404404a84100001e2030002c0c07400b214005040e26100841d101085074001c514109810400c80e09103507a0350740e80301c4000c181c1080324503030380e600c504035401c10807806408001e40000e41c102404801220650150b02202d026540d244241407a00203c07a480d99a41e00f210b181d60084021154001d42c070440180070007110906040d032804c515900002d40420f880407503800b014506550350b90070001014400c81e1031220001c002d000000e40440040c454443d07a4108 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 104776258 1250 104775008 104775017
    0xb010e10031a180f010501180b0f061b030a080103050106050907080406050c0c07030501050a0606021203190f0509160f05010e040504060204090905061b210907081606140304080307 79
    0xc180103c05500007000001c0c040300490303c0401d4009809800fa00007480b03903048603001c102c035a0302078072030310302885804000041003100c800b00c0e00010015581c008403201a402c0304140c066803507840d02080100401503454540d50750a600d1490000d003529025040280185c00349000c1c00030306504210782070b8010b41d00081c017049039070700d8a0344c010b0f890091207072846180c89241d40000c02c1c0034041d4040c1f8001c20032203106010207a1260401e07a40e4040a900200035024204006640031000c4040c00b5048403404001140c0510120304407015544240c4102c00d041c3c104000e601d4013a440041c18900912403a03030300044087c5001c0019100080a42c0014090340d10340b07000804020040d81110702804d001941003000302c881c0e00f84503a9581049529a141100150415074030020403815511610341d42c0401c050b44000000c4042003410000d01141268882d0500c0454070840521020118019002d100e02410703241c850300910703103904001c143d0100f0380b0400a10000c03c00301d83c01c0701c0e40300003907041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 104777508 1250 104776258 104776261
    0x216090c0c050709091109071403150a1401030c0806031e101503022706060c01230907060809070302040b010504030609050303060405070e01080403180504090b010e10031a 75
    0x20640303200341d078484001d001d0f02504601046505003903224881160041c01d11054849424007402000301050b2040e00c08149040e0035500c94500000c000c40e40001c51090780d0030304131802d0020640315a01c580051031070300d0480d01a0140c959049c814098030110703501e00503525040c0400483d8035080d48100f402c4044402c0d100b0100c4c2d0b204200001e100b8503501e1030003041808181408000480402c1c04128400ea11402c0300f0262060108084286915041d011a034562668400c103c0f81e80d000004000c0a5500c400c00c41c103143c041007590100050b00b00c032003504107103402e0040f1820104140c001001b03000c03044090180c0490300160a00981e541540d000507400b118a0059426004030340c402000d0b242880400410044040050b50191341e0642e41130041d511000025100300a0420105000451210018001c071344140920f0740c200b010b420b01c66503816107030f00204094610203081a40c02c0160f04004020304410070280e0350348039048642206881d0b0079035641d9500390841c4c9200d040441444070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 104778758 1250 104777508 104777531
    0x60b09060901050108090a050f060109150308120a0902061903061d01030213020c060108011506030605010c1b090f020909060a080322170f0d030203100e1815010312021609 75
    0x804e101f42190800c0c115078020003010400790b038031a801d002e101840e038286501c0070700c5200d0500300c0806403684401420705040c1c042c0c11800741c07914002cbc2142d003003e458021010268032164014040080d40c42c40000039180c0f0b01402909903045e039406601c18562900f225150204015103090541c0d9048442c00b100c3e448500b0b007080030f40240007020b0450b0080d03000004801e00d055000c816902540e000824502c1da0710308055080301e00030301c03510707010426800f0b2400000c0e51400080400c07900060030003501c13684036843d0400305c402c2c00030402d00090f40003420285601c1cac05050941d102500720b900d51a11070030300c00c000c0e859001e4420100c0000301c0408007900082e040d400a14084d2142c83d000c80c3c80b0314a04159580d90784031402c2d11000300c0c026100d2000c3c0003403090084a100309070303034419800020304e840c04042018200804c18800d503882203440034604076040c00a1003019112424021040d410b5050080144807010101000d40d841201c0030f0345205c3e2001500c0085038081c3d440003a0302c10f01c21 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 104780008 1250 104778758 104778763
    0x302011805120607020708030901080a020a0c122601030302030f0307020a050a0606140103060803040b090102030403020d0602130605090f010e01170f07020c040e06061513030f060b0906090105010809 87
    0x741c01440c1d12000000304010300050014a161060307041d6404c494605a8851550381c4a108404981e4001030f030000005501d100340f42c004001d20070300c520704072074160040d448030441210200700d00c90026101e80304410098030b0b0804081d00084011040107003035459a500079681e48221081641007001c04000100418001d00ca030380380703641d0800183c0300001c2c49407604200500d8a40542c80100d4000308103030301e05504ca442014180c078480d000071882d003030800c2e40035040360300f020010300c1c110700c0104000310058840244000349140719502c05600ca008480d4100705000c0d4640052040160501c42414140d41d00030000c01c13505d0003801d010706400b100070b0040f581e0690b0040da4100080d0841c041c0182c120120003a64890001c46e030a50300381c91092410401501c550385800907070707544a080402c400d03181c40309440101c01010410ac5262400c401108a8180c509500a070f40340415040020180020f034001d16940e42c804441034006841c01c039002908c064018050390381045080800104050001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 104781258 1250 104780008 104780057
    0x5091308041d04060e190311010e030f04150c08040b0a110607020c03060106090614030702190605012c16030b13060312050f030a0207020f0907030c0806060c0304030201 74
    0x10007415010703801c1007190b04030600c81614121451072600008211085000c180051210300003040084100c0e4540c80c21900c0e560a0728202d0b40555031130601c074a030400d0810003000c600e00301040c056107440c54400200d0b400d2400b2071128052001224035480042c0c540c004580a0358802e6001a45480b400c0304100c441d0602440c01c2920f40c402d0a0512100e6500060b17101481242103045401d180c1c3ca40004444401c82403103008082040703001100d103810301010165500c00c14900c1120b419010180c405904182040c00a5888076903d07401480b007802c42450140d07007544100d034010903003a407101903079241040c02848403040031114082290f0007446500a107217480c100408550b640d02d1006890b0000300040d12040703c800c00c0d109031541d070142c080c1054580569480c451903045990b40510304000c0e5110f00c004a91041c41155445047d40d80d0501d52070080f03c082e54009510149080c0103401c240c009080e0520500e003e0100c14a00f407400000c6800f038a030b081c41c22201d03524501c9101451484c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 104782508 1250 104781258 104781269
    0x30f06090c06110111180d21050406020d090311100210020319050a0e19050307020301020409060905090f07061b050105042d020a0e0408070b0a0c180509130804 70
    0xa50180000302070f5800090004201c020400802c41e404040c10f600c4140d100340001420140d105940640c4245000d0414088803802202e808107030448603560509121226400a0041480441c042c0560365041085140301000c0d81890050a230940d11020302407103603404031070701c0b544815a41c218900c1c0b00f849140940c030054802552030f81460140d040c1e81e5600424600b045502d000001040c1018a005a40e010520f0401501101000c1c01d0322107511881d8a1003910f19200800404c80161401d10052000740407000c000110b07142085981c1040d1074002d406111281c1c45002400c070130441c0440c59008503000c0d818107010380d01c00c10316500c4050003000000741c000d5203008100800d10041021845128441559001584003400c01e14a150000b904000c2d411070310b45030092111030460400e880d0007901585425081070840e585d04440c032101196640c100580350140c1d40080e60700222070464001c03103a21200b42e11800e01002c20105540140003ca01c2c100d000c19120a10044404a401811 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 104783758 1250 104782508 104782523
    0xa1e020a05220503010c022103280c030612020109060f02070807092f090402031803070f170408060a1104170102040f0e04030503400605090d09030f0609 67
    0x100301c6500d4100b00781e003910603203001c0e50074100c0c40b1551a201080c11001c1415042100c1c02c03005d1561000b140c1c0f604000d0458a0303500301d00f8100c80b650003807000361080c4040c421f1804900b050304101c0c02401d41d21241d00c00d440d558420960100182c1e00040740c0c0081d140240b81c29007000322001d104034075204203540190940d018101c1d0210f81003c6c640c010700c102102080c500b440c1400c034168102c001c44809090020720315021312101d0131620f040d07002103801c2640300c1c848000100c95a02d5940c15540440400c80d518440d080c004010401040048088441c002c200d00c0c3c00c2030b01d00400b090325442c0061400e201e82d81d45120b64440c910803401910040d0840d40510101c10400c07082c0b0600070340c060700031421110303d24800012002d40c01a0b100d84655030655807503003961200108820b94091030b0a900313080d4070001c08007600c1075000030703070b00c103d01044000000101585410900300b15280501844c90301c0d00b10300c3c0c031001100c0e04000320f4021a03600442c024044052420180014866048001c2c04003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 104785008 1250 104783758 104783797
    0x4020f042c0d1107090203040f0c08160608070c06110705071e090204030f0303090201030b03011107021503040317090f030d020c1603020f0d05031306050a080a1e020a05 74
    0x429407a500010107641c08112007090b910b00c2c1d4161008040303c10340c040107038044542403040c240c40d50007541d003042c0b0070000a41c0340c03841c0d5070740e4104183e5179400c403005980c058039008241081e50880b61005028600b452501e508095030010030030389041901600d801d490340c41c40340f6408804411214416002820703603916503100c864264160095034020030202c2404c0c3d4021950000364400c8400f1a40c0c041070502350f00900d03079010342c0540356190081e8103056988040ca04503890078040d500004d510701e0300c0c03640d0398600c0344100220000c0703403049607102d010140200f00010360480d01e42d5102030548201d1070381c0703030b51100c004070310342303012100c022006000120780c02080d4102c82c1c002d030945240d4402034481d58503100e0003540c002c249601c8042e5114409058000e9035080003140c40c5c604e2409941901c3c40c00c507852003104840741e2a548580e0000d2400034010042c0b5034014011908610070040508c800b41d814104c04007050070315804515039030f80c00500010041d0060044401e0401e5090384a00d04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 104786258 1250 104785008 104785061
    0x5090109020108180319120f02030601031404050c0d15020705060609010b0720060d020301030b0105120a080301030809040204170a20010516030201180c050a0608010e04020f04 77
    0x180040a604034040f07412503000c140c40b40e8040705070700000003000c0300940c20581c80e0310801d699164140846010f00c01000c01200440e02d140c0201c8650405010b000743c7d4a0030250001030071125202150f12120b0350312010301000900109154403070702c004452040d5440c00c682812100c1458507e010420580300143c100104507001c1074861041604940c0e0703281c0c603a6103c00420300762054a40003003000c40075510f0f40000900b01003a420013050f0260446040c5501400190100c0e4002c1e0400da5000401390010441340c50000190b00c0000500c3d0068000c0020564443c081400107000050910b107001c61401c00946030f07541a81e0050007501007144101c0356000e0120340760343c440c00341944c00c4001e48540b03108141d10104115581c01d4107070345032450044400041d0480c2d004412040301155290a1001790603809810217007011340c00385000c030303941901d00410050010304581c0164240712090004000c0c00703240c1466241d0164050b240700c00000c0d40305001900400384c103800b84219007140310307441d000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 104787508 1250 104786258 104786261
    0x9080906040e01030302010606050a080a0903021606020c030111070b0c0313020a0e04050606030c15030a1b090816030206030a05060d02100309020f04140103140f07060e04050a11031315050901 84
    0x41324069002040002e49134042101d0034400c03038a00c80f0104114802140241206a02880c159030107841941c80c0c03911496101524501e0030390212005a012822024091400384105001c118241000c075180c50703016698003424480081601d9003102c008000501c4d40d0300d020340950b002c0c90f80103189590071030311168080c505031010303203081d1114410800003070b0746410b0014a60005010040201d07043d05c0100300f03040d40c00e61004180401d00d507210704040140d41c082c02c9460b0f41e01c200d161948100c1506000ca80d600e40b554880081d0f145010726041040940c540804603034002203105408a501d07952100810b14110b0410402900812040002d00d80c103541a03002c1d24540384215012500c854505081005691030016a580c009c03a05000400c001510142e20320501030444040c0c81074944411161814141c89511650201e000c030316112030380707240c6072160b2a8090300e00b080801184010f004083d05500004082e1450340c5803040c0100144014000d001126022007171040c801c0d403819205650 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 104788758 1250 104787508 104787511
    0xc05040801050718050f0105070204021315081605031e0103120914060d0c0207030b07080403030e0f0c01030c030209040f0209040506030d120c2604031202180409080906040e 76
    0xc103903500e05800718850a104444100c1c2504080403c04903072410181008520444c1c4900c0c1d9040c401c04010a40043c0c950740040e00122aa00030807586040c50000140340502e1f009141c0d600304003400042040402e001e5108920007400e6203012030b142c0d5030300c0c903400c43d021950340b080c2103000b1003030000001048440320103c620443e20741d03251035003103540705901003181402610282d4040820f00c241c8859424076400b00c1980300051048030101580c03a1a00001c0b10f100351451000200d0b4241040241609030040031130036403d03c4014281011607040c0c00d17403110074900d110f07810035445801c8c900119100380c069411880d8020004c01154860199003002913110502c5c0900481c103200014032585008034607484001016100d40141822216a103070060850381c081d00240502c00d51020040f81c403000c011450200c4079411000e8a040608014207400241c1482208641c010080e031031000c0030b00000301c440c0e484155808901c9104a03d8008881d00401543c641c000c80042000600042445800c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 104790008 1250 104788758 104788769
    0x609050c21060112020a0302120f06070807271d01050f091b0c150702100e1902210f1605010504060503060d0c05090c0c190f03120f0c0504 61
    0xa00c00032610108108a01606150740d40140c101c030340100004182481c05038222803006242d04481c0c0e44a40c0064141c7d03400401c00750896200308010080040d0410180d60031042d2410141040d1422200007000d141d16540c6801d00e03c2c0c0880d504405145000d0001c00192111042c40d05226011440c0f03000c455000348502803082004070b03004d80a60401c0f020b51401100076001048107140100b030700d481941e01640c90301d2403d106800d2480d0049140241c418010442c50317024000c4260081c40c034000b5100b260901004035040b241078203000c440b519108400e01c03a0b040d030b10301c0ca140c0f51180a40c428444a0110716105004009a07900507a0380400c1005c610700c11010313a00e0000d9195001101c25010364054040480c20401c003084091400000e41da07880c40c40758184a0546440388045014284282d440500341400844c0410741ca06043c409894441c4521003d018684955100c41641c03828030340003d0280582032501c0d48a00350030b50489507070105146400c3c80381c00324070b000041c4035600031b2065 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 104791258 1250 104790008 104790019
    0x1207060f08010509161b0c0324061503090807050601060e10030c080105040b0301020702130506210a0b13140303040b06030c1806012a02041404050303150d0609050c 72
    0x10502e407400d280030500400744001e0718584130a11711000d840031215800985201100c9820002c00540796010308005984a200c0103a20310b4040134501c42c964a040d0203200d6607a007401014000e903440701c002034220f1302e90782c503000c40d10856504141da4240f180c071100ad0400d004e5000042a9150403640200400d01e0550b040c105031100c071107007102180c450001c03820005e0828001002039140640051460a000400040c40d184142d0300291001032505920028140c8690407c0300c02e1404010035019003032544210760842d4624003d9a80701c007140344005004108640c08070310195840d0a0391002c03ea0f11200c40200e10350041c4410341d403a00100c8040307030f4a0400781c00080690a0108550f450600041c045042d600a909881c03004460000d00050403c2044a00d04200c2c0601e82c1c10310001c40c03144000018201e41e035005200c1600d0040c01740707105090b0fa600c1440005400007003140c0c0d201482c4031010391100c903c90002150b05003040400741c6035504003652034043c04400711b1034102000040f00d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 104792508 1250 104791258 104791261
    0x503070b041703162405180c030106080a0f1b08010207060506041803030f0b030a15060b13030b10090c030b010216150518040905030a020c010e0a0909021207060f08 72
    0x1c07203d42e284500c088a0070f1030150841c840c800105951030030094865a8500034820740b0400d5108811640100d68181d07412041035400e00031100180920026000107170000d118040c1014140c50362150b10070001821007170703c004000240840c0c1180c0d4044820340081301c540007542d17940c6241c082c0d00300c12410b0360b07040d141002241c600c1c50140305180d105c080c003406003010031401e52402d50081140840310304030152111200d41c0507580034000d0068643c4280c03130340c801010004007540203c885941154041000802011280d14186001d1a040b030741e00240c01e140580d6001884504000640d00070401c2d14100302e5a458615019004450000c40a90031a0001840f840900200781c81c0c520448000400781020344600c148218024000042d61101d1900058501c0e404503003203481780300013907495806c04180c400c00380f85d0500002072134000034a043d1060000b020001280c01d035139446980d4201d55aa5541000c40d100d40c26210080d041c00000d8610031a03480d070016226056641c9401c000510302d20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 104793758 1250 104792508 104792549
    0x120516030b190204050a0605090f03010516120507051603030e010c03020304060c02060f0a021e0403030f020f1f090302100e03030a18050a02040507050d0e0304050907050a0e06090a0503070b04 84
    0x300b5182121001010551240c0c51f2440940365036000400031500202882e0030a45a0f481c2402241d00510000c1c02140d00d000d101c0c60018001c240c02c4c4000481c4d58102400e1006842d03003d01070b544148141708070050300684a1606400803c0040b110b04440d5092401d880220b940560103103100d42d000300028400000f1849040303858800c200d031464030700d04076200447c4060780164041c088903c1380714150316002c0010700344c0015640240e8411030000d00c00d09a03006034244c0c10300c0f6800d4840c9405004102e65200c6c00b14140544146120180701c2c156144602c2d400d051003001480b121106070482081780000713090175a13072280c0c42243d84040842c00c0c40102c452000035a000381413400c1e040070240441440680c00c001c080c0c4005003699080150600c0001c0c0c0444507440349190182000e8004d581d00d03840c20007800210f410003800c0005010090013600c40c80768024028140401d421142142e9551181c0c0000360b00342d126030000343d014400e8000100342e28a69000400079201402c1c808060501c019 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 104795008 1250 104793758 104793761
    0xe01060f05030a050d030e190807140610030f1104020a09031101050412060e28030e060301031a060a0f06020c0a090e030703050306270402010e0a0609120516030b19 72
    0xc00001c0985e401907248101442c403e82c014507050107142c0c25600410b5034881d0100d041e89078200150303001d410028002c0700f08004034880e40401c00da01c0300989040d28005090002e00c04a900c000340101054180310000c11940c210245402e40c070090045413600800200109480580e0000701c42910b0b02c2058580c80c1d60040c0c040c0e9045600c419101c0c40f80b00f1f0550350301405000a41280d03002e03071090305074184400605c1100b1801c80c83c18103800000c01c50550800078850000c48070002d0040f0700420051011030480d4035008041051189030803466202c441c045090781c2e082e5840702412004005020520660200f4051440c0004581c0340d0041521000c080d8201c0c0c0c01058001e442c0d82c010010500040d000c1c0010310f50041e0700602d0101c0f43e2152100800d07030798800000740b00011400d541003100f15a002051100800d505484840c440c0e0708010380503104c2505402410011485014040d040040c05c001010742d25191b0070100048680e64030309104810b40075102240c220f82401c02c45034600406 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 104796258 1250 104795008 104795023
    0xc050c09011d010905090a060e07081905011103070c030c020a0e07030204091d0304030f0303090b0c0405030f06060105040603110c070306050f0a0c020c1302090406170c03031801080601020708010e01060f0503 91
    0xc00030f041000141d41d6118003c000c1c80d0000851808ac425000074242c805000c60601460000ca581581c4402c43c44e0a5003181d41406603140300a10070b1007803040496001c00c0c511942941418280300384c440038000103002c4484c41e1f10003034004050300c042200d090fa05802500403220408005d0000f81480f4480c10380c5a03d180903046036a030b000f0b000401c00300300101d0b080078001d8001d050008480c0d0b0144c0b05c10342e4900701184c0b003800204000500700b00606007001315a0100003100082d10b064242100001c0852085101e04020580c03190301c0e00d100309183e0401c858032688107104941120f59645401e4014010840746c0080404900b400240f903510103001e144082e8032994050070746e99803080200f20207149500a1801965030911003203486032510f1003180082c1494680d40f85101d92400308d1189804500d0720303401d0094200380003240c2805543d03400c5400c03201c2d00b4204410a95074480040349842c0b102e62003801c441d824500c0300d5020700e0040d403005040d900c1c45a820000e594459040c584d59101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 104797508 1250 104796258 104796271
    0x80411040c09090213030b0601052b062d06110a032001021c05010b04050d0210141612030606080f040602190815030703030c030c050c09011d010905 65
    0x4000010544515155000031502a010300b04142030549030701c11102283c10889440c00c8940101c1d40034000c1c820303140c018950002d401d00e00146090892040d0840240d00300364529920f90440700700e0119102d0ba47c02281c080d10056400d44801c0d000c007030840c803070034003070100c420681650b080300400c25a101d51031070850030384080000c00581c1c2c1169011121810000740c803074806031030800720b05607901c0700b8001000305481c61130543d5000f201d400c0d1000d00b11403040c0e1244032407003820403003048561504122030040c1501112403954940300c2900943e0604c446101090b114039000801c85a42c051100c0d0002006000d80c0c50742c5640700ca19802541141d1017402900e0208800c640011103e03d10125001d80c014441c00002d030505000b5a41c80341c802441c0568403002c21450402c0002c08004668149103002080740180710041c40c50f14003601018820030084d08010f51800307488140201000400d85c040310260a07103400f5a0b6814000e02d01070400901442410340c0e41c00004ac100c881350080c58000c44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 104798758 1250 104797508 104797523
    0x40e030301060c1202121c2a0302071b0807030501050a05060a031407050a0602030909160813030c0c0303030f0e010c14070606180e071a1b0a0b04061a010804 69
    0xa00c0707449041c00004d4a0b40000110310503c013020407010894000303001c00300c84448500d1613a00c210300d075074826160308001d04503c403c43c07024001455000081d00c401d1002490a0050b920710803820500c0449102c0340c00030a0003190040c0010350807800003600000c0700e020310003c01982e1100d99542e410780344117483c2254007070b18102c01440421400110000d4240d01001212241540c88001c19032154596001d400540c10115140040d8145900026807102003003200c41c0004480301e4019061071401b40c100c440400420b1020300406010340c06240d0ba864020400e040040d560b8580280601082481c0002c22170034101a0000d0700014043c0c550b0090407500d40c403040121100007101c144d0045102074428a03100c107800141d0b640d01d21080b10a1101c109400309103006040c14907460221503500c01d100c2c2c480c9503240c14030000e0000055801100a00300b5000c524440c504985141000c0e900c405480c904504041c0000c2201c6ca070700031340122050301c188462400c43c1d4801506c0d4064200c5000e41002c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 104800008 1250 104798758 104798777
    0x70302010e040f0b040e0d0f0c08030406021b190312020306090a0515120a0c0b070c060302070c05101d04180b060103090c0608100b0f090d0c0504110702040e03030106 73
    0x20b10b031580201407400c2c10700c140081e40c84c10350000036091b101100004501500026007841c44143d00c000001c01c450f031203081c5181100c03c20307961b200a03444018006800b9550214452240703c031070310320b00c0448005041c100c50010301801ca42c14664130015400710b0126200c4442c2521840e05402500c1c4200c0000308200302c80c0d40c80c0c091010103888020902c800b56261007185d022255141c0d64040d11181c2c00347d0007058402480c2ca0b04090500003500f000c480361781c085c415000012007481401080d128145805070300c0c0c1d09585040382c040209600903680c05841d0500781c4c0b007030952114465001c41302e14028404d0071483e0348140012121030000e11408a5009002d460104945190352a005001807400091044180d110760585075229040300e4005a2008140425100d1a074100d80107404201442480e003940189003800c6031042001e40ca000c4c212910305034080c801b0b10041140200030240c000d112030016203c007113000d64084002280b25600d0b048144000368070000039a8141d91458641c8240c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 104801258 1250 104800008 104800037
    0x60e10080c010e0103020d02040902041706060603011e03020d05061006030c09030605040206040b1b060f060a14030a05030a12060e0405073b0919080a03020c1006080304030201090807030201 83
    0x3c1c4000c1c1c04050502d138007088000c69001580c4001e00c010720401d000141c0701d90502c50040e0880c034000c4644101035000070140580399031040c080341d0442d0101400708401010840000004400d540d02c041d61000001100d9018000c02150301c901c50032002071034011047d00e9850a40c100d500c40540f113000140001000d20019010341d10054205d40000c2400b41080c3d9165000d4500d5804001483c0a05442c0c0c013540d01210410840d05402c504001d070069503a14003400800c81c0c2d80110b100340003910f0160b94540840741c4007401510039158120043c0ea0790349110401c060514060312125603da01c2c42c1c06400900c2c00031078101180982c0c5d1080c050403000d450002660310751103440003140554a0120b0316000318000400303c44c0752401550030110001c0c0340500740e8908082c02500c5094816007a20300600010742c9000841e10b04007101c0c140141c0301d445401080d841c0c8540716214011076440c1140c08100c03040c0010103401164400d13070352008000c3e160302403142c40d480f0b03610000b40402c0051460180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 104802508 1250 104801258 104801267
    0x801060e15190c02130b1305090307060207080d06150207080708060c0309030f0403060b090a02130e19060f03060e0d0e010e0d050607030f0e010903021e0a080304030201060e10080c01 80
    0x1000307071540781108030083c2c1900003400c010400380c052141d403541d40048904c03509111181d0340f1a40c0c2d40a42c00c204914240540a440340710b41003008056950002c0c6650030441c0406c2600c0740584984800c2004644070303070103d0301c02100485814007600c079400000810103070018480c3d0a4032044005400c047d00e481c0040c488542001d08a441d860000f885803801d0f0320100ca01500c003c6002d00f401244580c1c8890600c4040080a003c04102d98010400e2484aa01e42d0200c0700849a9144142c911a0750b9207640d81e85417014020450080c9080440004481e0941c04001081d01e018a00c10000e40b030351104000e40d2824140b42440109807960300c041c21541c0100c000c3c071101c00c2d0203030200041c40c100355070b42d6081c0782e41143c0e0940071030b549805040e1001102d1207005041142c14008000da0820354034040d5a0f45002201c4d900c2c0200c0c142d15600c1c008400b0321030407100561010784c49450341040e140182c0078141c01c0c00341e000b4625081001841c41007203084801c0c00c0f42c0492010380308000e500001140d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 104803758 1250 104802508 104802547
    0x906010f090c021c0e0306040302060604060b07051c120e100509030c06070f050d0e0105090120120c07020d0b041b031a040c0806010602010c080903040506040e04031e0801060e15 78
    0x34008140c0005ca46a00c0a11004c3c0c841c6100b1b90240900303250440403c0700f01d8540b904000c4a0305818461603000820015502c061000b03103c4460071444400d06003210b860009511904034181001441c8404d42c20018500843c0b0300b10007824000d45c0d8400103200d549010703902080351558020700208414038007031744074002011000d1510614003451032446000340c4011b00414000c580d0366008001071100284501541c445a201c4400e04400e80200046020302030600500407944c00d15000c540f02030020000c54503c141e01600e011301064850801064003c0b00b240d0035205560b442811144011000c24140203996100081d03040c4c6446081c60300a00060041c0216141c03c0f0300c0c00007040e40c8008100c11360003080d2680c0003180601e2007820050807800301400e0805c6550017408240400c0d50f8078403ea9041c0e0b40c3e100a8200306907941d040894243e00d44086954030311100040c0c80c10303500e52180ca00da0580f03016460384051a4100000c2c0421940e00c1c084030311444000380188a802c00c80d909948 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 104805008 1250 104803758 104803813
    0x42904180b04090b01050f19060e01030e06100e220602070503070609110a1d01030314070b070509041112040b1b0d020d05010503030a091202040f02030906010f090c02 73
    0x3032440140000700e0211980d10f00103490080c241c03130042203e4a801c08619100c500700b0740304401d640803030b90340c480103c4041340161014000034800e00c0070141d11a0380402d900e00720460440f8482d080144401c00008154041c1083c002c448800098425401d01c1d1441c807421151920510040c0c101e88500000303410586040301c0d40d0000f00540d80109195000d03842945014090010280c0d5140c41000143c1050b9800711003210390301ca400e0403515910440140c11650541170560180a84c41d4020b0a00c3c800d4003401010710b00200144180960b0100c090003459605032010401c0341a00200d0f03034a00c0c06001e5600f00c1009580d0005400503015005c02034219410070740d195017000320040940d800350021141000d643c3ea020074035000044d0300d070199a00514080e0b0282d0726080000c440200324820a0244031000115610310310219140c59114070758000301a0000c5440381032120300603031211b4080c400c1803200e8820910100d24102c8521903201805507640080a45600c0500050307206140350040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 104806258 1250 104805008 104805011
    0x110103020405100e010206150d0f1b1401020c1516051f2921150a0b0f0406050a03060b0402040504020f0c06130305070b15040e010204290418 62
    0x51551241110281040f50329150540080b941c203000a00c2c00d14001e182100e0044121141035403600e505100340c070030640090000c0515446801e100c0340030101c00ca604036500c850324900150740310483d4084410020240d0176903002c0b050360002c10030005065038200c400c00d081000040c0f1107861030b860760391071580305009a40032030315400c54102c0944c0d000c005510000da114103107010303035040d032100b4000817101c01c3c00c5a944c0d8100c3da8010600006088c10100b507050301ca4004038803407400400182d10f024a11b241e21211915107100c0d241d001d408031001c024050a65841c0488042ca018013031401078030006000d8814992440d00d8071000f80151040640d08035600f04808169600c1e20b00081002c0541c07100d4441e41da110042d03003a403402c64020400005001d01c002e0110000c1d07440f10172203068603002491803115440e4041d0b60302e490b9000341007542e441817401c400802d40c81c2045d0050022106594035080c1403810020143d42c0d2000c1a0000f49240b81c810402030109000c0322459544000c0c05800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 104807508 1250 104806258 104806267
    0x6080a051003060e0106140406030803061002030c06070c030314070e0d020d0501230a050610030b040e0715090501140406080717090105040b090a020307091d03071b0602120711010302 80
    0x3181c800310350000040303c040340d44445003071000380403d100258000e91f0944003040742500e59140c082282c00094040380c42248109881e00c1107610070019100300c0300000003507406600b00b03130f48017070300510003994100c001c02c1c01c00c0c1c1019031214000c00d41d28803942c1d0545882921800860801c002608100d200320b034002030b000c032600c01040c001d00c02d8040c0c240d20800780c0315052055039070304202048000d052100c1a410003080164030740303411340aa407007444107040210b020f0040b0780002f009030a65000c0c401007442100c0d000581251303e801101c402e04055154625aa511100111281800c00000a0056400304000c126046c410302001d50b1145983c50104d8400301082e42c406062802660341d410569164020301c4240810145000d0f00901b4031401040c60345010340c0402d882e075100c0d00c5081049583d80c0d02280454101c4420404491180016650b80b15120301c2d00100300d1100d0300902109264000020668600004c0c1040c412407600c00341e039040c1103050369140715603401d500c0b4490416800b0700 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 104808758 1250 104807508 104807513
    0xc140c030714030a0318171602060a030c0801170601030209100e07030204060f0e0d0b04020a05030a030302040e0c0403032c060703050c0105150607110d05030703080414060106080a051003 82
    0x12102a40b41d01480103140e4494140c0b80040030746030f140d50307001c20090f1040a0030b0006800007540c48052050050b10130f481d907086440c80c0085a240350f1000c0e400441c001850442c1540c190f100310100901e5440301c0080340d803038903501d4141d00c03140c4502e94803541c003201c014030244c54824006540521030301250403801d500c620819140300c10540703d0101003600402c040c404180c0000294441d51010301c5d2103101140c041c0001a5130000f203101c060041382c3c88401180c199201c40e5900d101802d000781c00c80745007800034680203000b5030151081001c10703200800859450101d40084030216905580e90344460110040d002400d0280d6075410f01d840d000c1081142105d4031750401400320240251a0b1a449007014000c0c0e40c01d4802c010b016240209808009110540c1d070750041d10052a00101910100c0721039002080450b411050043e205100110f019810141d01040841c4550f10401e8074140c004280b40c10070f80d441c0c1d42030040d40702007202000013030421001d0b42e01550344284a0447d103405107541e40c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 104810008 1250 104808758 104808773
    0x203090c0d120305010e0c03010b09010201110a0c150507050f0c01090209101d070504060c030e04050921090a12080d060b0301050114090603040602030601140c010c120c140c0307 78
    0x80108031009509a04440c6180f0f4240c403e070781c01807008000b256480d1400f51f000390300c24401400f641000b10700215101c14943d20035401035030340c003100d131540e0381c0d4880400c0c0010f05012602c107000c86000961400c00800034846002c0c1c02d008101c2902c41c9405e013900c0300004521504035840105c2203660b0781c2c060402603071391a02898000c0107007040c44821380b800c00944895560145d0341c1c80c00300c500d0320703024003080543c0081220f04660b02440c09070000c0102d403030220b800c2c2c012041d28643c0036041001f071116074140850b172008034600080d110344510403083e1007160076025009100382d2001c0740310020804003059482180600d07209818191500b00b2074042081102c010b50080c202d26000440148a596000440003411881c0240ca40d41484041000142c0a1000610092030b050b0088080346c09039010700c900400745c200030746240703444503a030a0596009000e0141100005805540c00b40b4464103035100b180394504565440030080044d890480c0419800720403400d00c0c901c006c001600226415 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 104811258 1250 104810008 104810029
    0x1305070309060c08040b0115050c03030a2a050f03040c09020307020a0201090b040320030f0714040c050c0d0c030e0315010e06010201020f0d050402060904140a1409100203090c 77
    0x191400241000181445000c98080c40340f03210a20044009010114242600c103504607007001c402c00b542d080010b88216030301d0050034605000c911000c418032051100c02c1e000303011400c5c554000f0145400c030b140e04480850144d10040000b04d0000c02c4480042c5d60a01e000b1030780203010740c100403c0c0540e901411812a40102c4031000142c01c5850520115a4401000e07001454201d03045810a420364446e039070b103002d000c1c040b000c2c12120000340c071000340c0302400020440b0444506480841d9035689415807281c242410051040c0c1c81c1c03046401e03800d4060420380710b10440c0c44004004d40640450241c9070380011410940c00c0c03000c0c1d9040f403249075404110369001240301c143d41d0007041d40b40001841c400c680c05414981035900500c80302404030040c02c2034502050307100b03402182c507880706d0000c2541031007170300f8103660403e04100b50340301401191750400e4051004403a0070040c0600c00c81119811004c2610b4022050700900c000e802942e019401841d0040d42040503550b2a0b007030316000480f0b0404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 104812508 1250 104811258 104811271
    0x180603080a05090a150e06090d0c06081504020412060e07050a120201091a0702101101050f070210090201080a0c03020415020c030d030612020108040f14160f050f010e1305 75
    0x2c00200f141c990300b0008000c0000703000390402d4050901c0106006005417010052440c0251000301d1459034a99a000e034441c106a007081c1d24201d016140c0e64003c006c1001142c1441182150a4011290303050a01c211401c0795101060030140213810743d900805421042d46251981c86260408121130781c0f03440c00500202071203154042151000c0c0b001524a50a6912010240300a150086810044902100d6082c0c0d411281d400c003080c080601a51000c4070403000c0012580780030200141490426006400b80c0c2c120340894101212441c02003055403d0050001d001514020104030420307030301c0c2c000f4a400c262505000d410991031740388010300c1c15210305d400360044e03018400640081c01c0602c04016840c4641c5018001203040440d104212000548024104801707000041c1c140050440c072203032103543c00300780b80311100c500300c0300380f0759920780f03200300c0c40703120b00301d444c002411280e0702c800b000486101810845910322048010b54044008c420ba45d81c1050582d40c4840e02e00c0c2032440bd6a20422 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 104813758 1250 104812508 104812517
    0x3030f0e15090406050604181e050a060302120303101503060b070c0f060c0803070e010c05030d0504031e09050405040201111204060e0f0102190206130b0c01050903090901180603080a 80
    0x100d442c000c000565142d0f40c080c900503d000c000c18001d0301004601c04400c5008607001203100509030281046001d10b07800c0030071a0701d1601040c442480c5041c0c1159080364021074403003030202c820341030080d2244801c4e00c403054500510325003009a4904400071401c52241401c00144095031002c5900303c5500080303080310504c0c1e0104062003440c2d01e003505080034040d18a40103505000503580d0242c90f210290400c410b011101441800b1a07114888020750305a010081da92103441148a00d070140800703072011004030340640f072024400e80c90300700781040040c1c0c03941d260300c420b92500080c000200400ba1003a8100300c4200c02034101141c040204072120740d150707200719139501e1071b0450041000c3d015109407031203a18071091480440e0380c0098000d442904c5021402c02103ca60b200003032451107496400d0440c01221303200002c1d8042c00b00060b103603210400000748915503c400d044c82e103d1080c0c5000551101c1c136100144074035000060342d0105443e56510000d85141c803901e40320300e10f40000c200d040016 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 104815008 1250 104813758 104813767
    0x81506040b1c0b0109030f020d06020c0c030d021906110903060106080a0c0504030305030c03100807170610080a0b0709030803010902030a0c0804050c0f04021c05071b05030403030f0e15 81
    0x10302d101d115016200c4000410100100f500000e040d082c0310700c405483c1c0c001032001d18080d990f509529001550b4410b10440d6604c001c201150345515030f400350244070b4020000e4011606002060107404d2561b0040c0000802e40143d49601c010096880301c44032254060201c0d81403034804220741406040c1e652510440d51411113210000e842c0d07031030040000c00905000820009030400f0a4030b403c90340e0400c030262a80c2e12038001c4106120319a016904621404900044000904100c410018090002d5488950f183c0340d008010503d01d11540503160b000329034070000b042020b804560070940915225455a82d03d07160104140c000b030304850746080e030000611440c68411b101d800c1c40d80f81c243c10300308007500e001d03100c1079101c5054804c61030003400c00440e00c0391140d4030f560445080018070300031180c402e4061400c0300300400307045a4502c00b00b801c000c1103d1851980035201008551b20400030b5113413238110f5070111100211240b4030b005025a2400e005426900c40900180580805004070340b40d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 104816258 1250 104815008 104815027
    0x7050306030f070509010902030c190305070314040c030f051504060605012c090613090c0e090a05370b07020714030601170705030a0807020a0501030b0d03081506040b 73
    0x611150b03010001080c2e0100c0303400c106030f46402c0110f41c11120f41d0f8100580702e50316003c881065104203040c96440c03034110b04400307941c590141c1c800c9015000781d9904211401016800302d24420040e00c0240c0500c807140030802c0081d0b4580003101c10180300708241ca00c01086111b8081381484250b0381160683d8581c0c0080c0000d580c4805404800d8400c00e44140702c0b81d0a010383c080107130720100b4005010b00c850400161658491940d09120f01882c03c000300412071103818040358489103805072070410030000000c038261207800120030301c405801c00090504044611002d003002c00a240c2c4400350500d288031a5003840c03010804200e10140602e0025001c0e00d00407070020f08090309900180c030000d1803041e8950103510001100da0560300200207012422031880d58252410306541d003e50380c9446170440600401c0002d00291002500c2a1031030142e0303d4894005405035105020002e400902007101c04001c01d119460307240d004031080c55412464075012020811650003600098908100000c6190b41c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 104817508 1250 104816258 104816263
    0x90e0606040203060618030f0a06140106021212041704060c14010507090620030c0a030f050a051c0f02040605071104060b07081c1b02150103030e150702030102030705030603 76
    0x38040000c481c11031441c0f80403030015005020701602d04a18042640c074201240d2810400707078112014240894510104a15060029120010041000b1009440006035003400040c0405500002422040c14404820860096001c2c0200207549262202000c0d81403a20400001c0000c0c0c10569600010001541130a840d040c0070b0118507801030780760604201d240c0e513000038424240c0e000740c68000310400c5c883c4515404d40042e0101b40314640800180d0040d07043d00068231080240c465141c0c0200c000c2c0c04030040c0c48074042c500c0c2804c0420000c110102288452a41011452036001400100c20113001156401c90f04075030000c00c00b141002a460b01031280100880450303000484083c001581014041c51803030080200090119002140d00d0082c03801000091f014109804410132102803174217851004001201424400741c001c10302c06102c2100c41510207410f0b83e405468507540d81c00303100d090048003620641c5050700014180000b00041e0b17000e00013940100c14039956540c490600c90101070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 104818758 1250 104817508 104817511
    0x9040f020414090c190210020c1c03020304030206070c140f10060801020c150709080105070203030601092913030606030f121106040b04020109120605100506090a03110a0f090e06 78
    0x10f10070401581003281c00e1981504842e810381c0e00c2c0703401c044510201003050f480c1c55103071034021340c615001252908032900c0004441402c40b80240a80c0200111140700382c049100940703000c5d0058100e440010b090350b004144200c081840b418140c19800381c90b0102070b040071070340308187d03142d5001860100c101b0034041c0a21400741c082c0b80c000f140340c81e0b84292034682c0c0e148550700c2103850080b0880010380082c00707120200d0041c040315009002620749001c0c000e40f41d900407a0000d010806c5060041004407002c0e081c1100640700d48034808046020700140c100704c0c3c01405c0e50807200403a011010000480b58042c6c000194440c14504000700a07501c1d280c0400b01300c2c19800c0c0e081120b001d0542d03050b10030000d02ea540150b04154078000b0389e1540e000485040000d078000c50112a0141a03070f40400030b0560000c1c1c4562408003070315007010388860400c06144584400c06a114007440301c00d0000c03917a06446006480d00003007004401aa948030180280e8105900c00300c900c650301d5040c4504140c0600805 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 104820008 1250 104818758 104818799
    0x1020307200c01020a230304030807031403041a10170303040210020d090b0c0309040e03030601020c041e111612020705010207050108150d140a03090e0f0c0f09040f0204 74
    0x2d01d01c900c20b5400003507880c0c50460015100b07039407000b00320402c01c40d00f80504042c014910b066990703840c0c403818541c1481d4803900017180022030f0b210b034100c0303140c1c444029240960b6000b5141e11070350000c400c030780400d0304020b4220840d007424a000042e00b14038440d1120f0344092008040c0d41c59103468010850b0320189240c00c041550400795446610a42c050304081c00d031440b041900752a0b1014035482445c5029815681e40c006142003060302c2d40031800800345d44201001d0f421540200780520500069424220f98036802c207a0241c4041d01c10003294101030304c1090910001410895070b810b000f06640d0350740c00180d900c2c0302e250f145011055410711000000e014280014008146030400013404080c004010400e413168404c1c600d1019502c424980c601070f504149a042c110400e9058a41c0720f01001c403003100450050880019480c10101210303116030120105082e80b0350303840c0d4025109601c0b00c8030a200a2104000e040405d5850303114814107580c8800780181c6541c10a00020700042d0a9203da = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 104821258 1250 104820008 104820013
    0x3170a0e190e0105121c020106030506071d0f0604140102100c1701090623010c051605040b0114030a0c110a120f02031e090102030706050f04020319080d05060609030102030720 77
    0x1150f900702c5c00040c0e0030711400c6000c40320501c08958003404a0040000e070f00014910700894013031160459108080c2c1c01041100c000b00504160171208100c550340062001c3c0d9000a410301c8100800c400c0b18030015005607060054600e039658410140e002c031602c100214010441d148040b11007442c0c10000240541414007081100d1401d2071000d00d4002e148038900e19100c40a40c1c180c03541644a075002c1d2410a5204040f07480c03003d4139a080a08440c200d001d030341c0c05985030290b071000030362040c070280d44008040580c443c69500c4000ca0a0042c1c50400700d40d2040c80485c0403400861030f4104951034059004641c0e038117401e541c03401c005020300158102c2c242127520074801c160002030501c024940041031030700e5442d51a1a0b210050b4154001c07484007500c2c0900d01810402d51090300f00380c0d40d2080b03108400b80c2c0d0400c4540101e80c10004481503000d024850280000e20b40c15046520290f08050700030803040c100300604c00000e00f6a8401c85000c4002020381c075118208038010301450150200c070502 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 104822508 1250 104821258 104821279
    0x3041406040309120305040b0d0b0f0a0f1e05060d02030a050f0103051903020717030d0605010306030f080a090905130501060506030601020d050d02130e010e0c030103170a0e190e0105 80
    0x7001400f402c55030050742980d200c2080c034581014003940c11500100110f2000707517254445540f01600915103005124050b4421a1110b5a5440c10901d40c10503036400c0c0b4080d41c4101d00b0b2807034081405c802a46240700040e00d41102180c56a542e00240040301c80100c401342c0e0301c3c602f000308401529130180c4140c8000440200600c0010b001041d2042484400402049800c40713a040481c64041a5440408a010301800c1e406411101100920700ba1034940d10610607c1d95600044044507114803015201d00c107a00184000200098010728441220385000160991280400d90841d84296050b0383ca6540300280c1d001081428082c100044c00c040386c500d4118504000042d46070302c0c492805808000d000201c030300725052998103490000c444400744980881d15405811014482800b039026a50900000580b100d01040100ca05880d0b2280e8005025404883c0e01e600982041184000740309042c8800384060300c501540b1650110341d401442c601504c3d0945200c00c808041e00124041d00c0f0303550 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 104823758 1250 104822508 104822513
    0x303150108060a1e030605100e0105100309080f030f10050622080a050303100807210f0b162a020f06070b070203040512010902031b060d0e030304140604 67
    0x1125206404800c1c01c080c001680c80e10001028111030360056840944051000002c0d801030002203819244660b4003040a622070890701180440305106144525074110010300a0b420485e5480c074a2600e00e09010805180666581c0f04c0c1e82c0212184440a0401000b04100b200301018019080303040d03140e01c90745241c180000b1604602c60400b404120540d07000c0e0841040e076002c1c502d0001030a800c815100c44c50b006160040d1280e02c15602002c0d4040070840109071a240402d00d1022105a01003c01580c01c00c0b2510080c21584544241c41c6000500005804508915602da00c20407290424001c1d500a00f5805400699503402d0003c01c8150f4502c51400030309c8003c204014a50115001940c90f004400050020b01c240c1c2c1004001440e0481030254054001002c0c20550b2030403200074150726140e000715030883c2c001c1c1c00041e5059015480d551052640f0b014082c07050800070380002d141420215815050318000c1d140050142e000204110070b100e070b80d417501429040200d0141400d410240c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 104825008 1250 104823758 104823781
    0x402040b0f13180209040b07030b010906020303010303030c0504080316031101020a0509040b0301060506070503040602011109030a11061e0c0d080c0d0b030c0a1409010e0c180301020405090f070e030303 88
    0x19100303a20103079600e40f1482007481c0c3c540003840d103da41c003c01c520420302d130501c2c222442d184103440c00d03004607003400a0a4030f158010f202220940b03461364019411a2310b181c1b400c03030250883c15603034028010200008591083c0900061910112003114803050a8561400400f08424503013045480d9106001d11082140c1c0603044402c50041140d000c981021501c0c0000d0047c069a441281c1c4114005070980c01c004021001d08120f5070307071350020042e400200c801350341c0c04d00c034047d00780350715030000b0915100191040951000403e07018244900300f4000072806001c4001c4001451641440420f032403041d80403c01c207062081800e45080da901d4140880381c400c05008000c030794080603885103c51903460311b04004900f07108030010401a0b04541d10030b01c0c1e4403c1c0c1c4124003c0cce4019036101d400400e42081c2c1014844c00350020140d000d00d085130b4094101224070200d01c800b98075540802001495030741d110310040c0604084080b461844c24806405841c185410070002c1c003e800178420401d80300c034036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 104826258 1250 104825008 104825029
    0xc0d060317091e0f2107060801080c090609060405070201110c070f05060f1615020711040e0d0509120705030a0311060a0b010c0611070b01030803090c09010e010b0a110105010602060402040b0f 84
    0x3516403940c00b19080540c1d040c3c9000005c100022440f50707010000751203910548003030480d00320301c082c0c0d810601d922050000342141103030040e1708000800040340683c10b141c2d01c5035034040580e10000510904045080c8040c2d400000c030158207a100c0b09040c403004007050180401040e084401c540350200490b0780b0011406074075a014002c01d0403104000501108091482141c40384000c115a45d118500e05011078848040f40d09000d02d250100001103110001031035242d06105888180c289503a403c2002400b01a0350b034030980e90f01410f0340c00125610200442103219200f500c4604012020070340f130303919011004080c0751456041c9a0340030182d03604440039170700706904001c010900b144000030900707051042d21310060062503182c00000c140035203d4042c500608034401031320f030a804880c0c00c02403226030a0003468200300d1712400401680c10b207880100b5040035282001412b5030080c03900d4a0071200c0985c40140980c2110042004600d080c0c03103072040c0080d04646c1e59118041120200e1154801d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 104827508 1250 104826258 104826289
    0x12010602010533041104120c0e09010b0a0506090102010609091101030b010504031703070c0212010903020606040605060301050603041106210c04030809040902061b0a02040e150c0d060317091e 84
    0x2174907000c518681c03a403d01254054201d41360a0031624003075280c6060f0740446407090140c4c6900c104081104964180500350340194020402c042582c2172808010050740724040c914195075031484c0020b40b0f00d10500032120414041c01c1826011640301001406580c0c0306003401d4104a004c01040c40065001c11486100909030701540d034580d0788080041c3c4050040000107580920308451a002d900750540040d40d02501c40ea0036a25541c8601c01404155840790250581c071081c00e10041c0040d040000203544d1060049122110800c0c148000c605181d01c402c00c4d402014848640000c800c0c040d4845044c1c120406c4e00010345071501e961141c00082c003480f01500e00c2103460308005c10a5545007402e81304804180b03111400c501d2041503549039591300380842240240e0601c18015030507040455058685000e2140128181c2d4954940c0318050744124010308103680d50b404c011004c41c0070000e81b000c040f0040c41441e80c1d9404403a0030009021154a036100d000d136034100144031389494100c5504500007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 104828758 1250 104827508 104827511
    0xb01091503020d15170d030203010501051606060f0326090a060c03020c04110a0e040908030f04080403150207150504051f0f0c0e010f020c0307030b06061201060201053304 75
    0x1603c1c690880074010400d034000d44003003001c0d4040345102d0384170005040300071a00c040310205000758000b0340507804241318117408110140101c1b0394180200d0004060b80b84034501c00103000e80ca03011844900030154000751550301c82303540c04400c2042440c8210b00350b61500d80c8481c1c00c5c81550300009901148034080c1c0400c1140d544807100806008101030042480001c00c2401408485041c112060300140890b400141e01090702c5c030b003141803e03c00c2590881d041010750786581d50b4940340080395800031344106e0ba2041e0810000010624018a00710191240c240250b0360f00c04905000784c0b014050345005160606d44000d004c00a140001c00300e00101c1210810a00c6001805070b440051400081d840c440500b020402058154011000103100d00241c941103004102800d00301d948460765802e043d0181e10860003400031600340d0705c0060b0704c540300800c0325183c001e05640012240360282e106d074002d80c0d1904180844560101d01c200e03c0a03641c0c604409600c2c101004254580f40c40441e20390059 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 104830008 1250 104828758 104828767
    0xf01140a1a0d05060a0c0c050601060e03070305030409090c06031a040c110709091b03030512060a030203010234080403020d03020705090114150f0304020f01121505040b0109150302 79
    0x700440035044111507030080980c0001d20060400710703100c040484404000c203140c420301c0041325014540e54904650458000c08203613003844c00c19110000c0b06806103615108440c00000090300400050018080c40040030850400c01d02c1c00307040c540d441303030825014181410380219110384040078400842034101d03408150034004039800c1d140188003106100c2c83e0b000304130010072030038202d404c12061740d0310505183c01d01000912810002040c11b00000380021000c0094142135000201c1c8241c1014008100816480d0350703a00107400c9034464030107241403a910565604c2d10552240c240e20440c03140c400302c0001c0d41d4456603581418400d501001f84282e106a03842c2050506c01c121034405000d0141080006503140c1c0c48400c0c40c2508005800c0c81204908a100c99a03170540f41580e1501000304203d80c10340d2242c4c0e027044840c4641409031030400006014041843c071460040b07200b5141e185444000c1e540c201030511040e2101462907a040c055030081c20405046415912501d46159180050702e9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 104831258 1250 104830008 104830031
    0xb01170c1611090609160e0a0b0d0c08071803031d090405030409050c090d030e0103140a02040f090203040206030103032304060e0306060102070b09100909051302030f01140a 76
    0x1e006503101c80c0d03081d851030340d2003008021030300c03801d105244801c480704080c65541d0802c000c0c9415040390381c240b420040b103071495641405142a143c210000070085144503448220702c5495030080a28440c03165112190910102d410811181e000007103840c154041c00f005240110010101d44001020850310140602c000140002c20b18a441c03030040c03642c2c0d071500b00341c1482c070760765006401404200d03403910012900600c0c04d2802c44071003580140000401900d0394805840c4400d83d82501410305854100d0410031140c10805540300764a440c40041e19181844803041005c00c5c4c6401040c0c50901c100140800350f9a50320980781100c3d854606114603485000300f55152501d44c080150041c82d000c0f901140f0700f80c1003281002001401c3e809c555081d90b40600480e55124a44102c1c0500041000005d2083c207041a2052003ca41c505220750354580c3c1e42e09110031540200d950b1980803030b0600107482149402d1040d00ca440c500413000f03020200a00285070690740001d0316401071b8a0f66a9562801c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 104832508 1250 104831258 104831281
    0x90103060503030a03020a0f0305090d03020c010e0d0801080c0306010b0f090307030f0804090f0506130209180f010806010812040501120e0102130e01080102070503030c0a09051210050601030b0117 86
    0x3400010342540c1c0c07130b01c140321400b4000c0e400901032000412800029014040c0c440e20510303115403000c00c020201401c4496040d0001d5204c05110007140d500c44120682c0e00c01c08009505820760b403595a0b004039031512803154203120f100b4000302c3c400e8001c41b0040200303110003c15901b0007606a5111540e032200c0700002451f00d44c60364401061b19100d07084103000c3c080c0b40f0300680f040750307000b00d0280070500b004203000c001c5420032205981d01440c00700c1c1031160010154007801050030301800d00403121544140e070708400351045821401d42d000103030060100b288140003840c014009000200701c610440d50341a181400307280a0345041000b041d03820001c4a1294000a0080080300d00856035540000b0084913140207500988001314034030800091909014402c0b40c2032580c1110107507045486600c6040340f0759000c1d0030500100052218041981c0c1e0301c56010340c0d542c60b01000248a0803140d40312041c19102c0013004981031614000460720b25076000700c2410300c41000107600d0011f07560764000380308 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 104833758 1250 104832508 104832521
    0x302090408180a1503052e0504110a090b0c0a12030504140708030403060b12010e0f16050105040603020a142d090a0b0703020703050307030e04051803030c090103 71
    0x9622619500038002848544002402080907046115107882072907414081c40c1440b0b489544000b60304070f5a910042403107544650307006030207505400c00300010b29201038480c0d82800d0245406c2402404208001c0c9818440e80701c210120554050804880345005440680b46118400e901c0c07a0025021001680c1800702070703400b5901100c0c2a00100a10b031004005040450303088274002c62206007040c1a0000213000001c895880c2c008514207425551500c010f803070712290b400d80200c800001981c4492083c0a5440f107880c5040040c030b01c9144c3c20350300514001c00c00c0c10715010842540010f01003640c0c40003c40301a1240c504016a941a01c400f046881305201031142010f9103000c02c0100e2284505070301149251132070500d0040140d440e041014092246134a81640700e501900b040044002c40009001c0303442c000e005941d0403547e207403580c2d0b0071a40308210490001b10540c52050b0940b8003407091700d80040c0a10500300102e007030841b505a0307911001c0c108005860000c2007020b8283e101340c0002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 104835008 1250 104833758 104833763
    0x9030c011d0609060c030a0207060623011205070203180d17030109060807051309080c15011a071a0a09170307020730060f090b010e06011407020f030703 67
    0x3084050580d08215809660001010401e40506800700d8401c80d0001030460040f03807410112071660302c0c1c0d55803040c0254000282110b91030313100d840c0000d120710015145500a2508184042607510030800108003d402c58070200429103450144503150b40c2c0003040d02c0c5111034a680d4010020700100c001403e0f100c1d118001020b00a8880301c0c4d4202c1080d000240d412034814140c24414184c8801c4001c0d10745005004486d08600a0001d0ba02c01c080e0581003000750b41d0003404a40c0c80c003548441114141300c2e5904190500f0000d130401040120400940c0704241100700e45842d04103000d0303503621040c001800449010300c005030710100303964028551020030309650140c03112405101242d981003854108441c0007016024028002489641102c4945510340c601000710040c0881a80c0100381030103015000da51182e900c03680e0508044041c403503002010f020b08044019507240008102590344c0003006281084515001100102d0980c5d0076107560030380c100c500b1100d04181901007480c241c03465001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 104836258 1250 104835008 104835011
    0x40f06060e0a09021509300f070303090f050603060121021809070f021504110a08010b09150604091107052406010f090611100c02010e160f030201050309030c01 70
    0xd218070030b45a80d1190703669034426915448029203082064100f0b0043d1036844d03811044070600240d003000c06c02d2103c0f642241e2403410b5001e80740c0c004111886e041c118041602158082074081c41815000580c2600601a1680041816080001007a40d0340405440756052000d0300004001c821034445044001a00b0b52104544a0384c07850411143d500030343c210b0600803402c050221307103090300c15501511a0a8203400414849061254540300550014800d96045c018030b0f8842c1c01c03513560492030600404141002041200c1050100500120003400c0348400f0900c0030341c450241d86500f0140e03012180b0354103001642801641c1c480c841841200d41c0249a401403140b40054481d841030070007503501c080c07105032400d0790b0348900644100b020b032100580400d00e95001003003120302c510806602e080388001514190540381d210340c8252580c14070b226002d030f5140d1940340c20090080150700600d02154405050311850100f03844841c1d40d035800041d04209000001a034001c1c4100b0482e4090140d4500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 104837508 1250 104836258 104836261
    0x9070e040f2406030b0603090c0904050c041803020d0f0e0d02030102040b0703051b031606020306030a0b04080414091902030603031b0307020a060305090714010c02040207050d091d040f06060e 84
    0x1201541e4583d0003603002082c6051030850050911b0000c0d0380c03103850000c0040c03602030155001c00a0404008104448038850544082038540b01c0340994120302820701d100760020710b031a1602a0034040044070010800807411401d628966011040d50a8881c0c1640c03641130b50b42c1d2600209000e40310b035030001318000364001036a008065104008124045200014011506600c41155124071416441104c0c0d01103102c401c001042945d17000b550000c00c018202e03640440550307148080c0441c100d4046c0c4036030b0000f01d810413141c1d24030203005021420444841e042c52906c464100c4c030940b0450040c41417540c0c0400040e60b2618104100e9040d60031a1441070340b48444100040ea0300e9210071800c034003030440e5120001d030050090003260b011b40711040280c04654149030345018213420310710511741000864034071580540c4583c4010900c843c001c802030045a503031841c0203040c1c900c0d50b82c480c0c0d40441114400c086500c501752502c641055201c0880e00784901581000c03405001c9507001410302000100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 104838758 1250 104837508 104837561
    0xc071b0302030c030303090615060d1e0b04150909030302041e03020f0d0f0b07020c1c0c05091b09040b1005030405070b18090405011401030308011409070e040f 70
    0x2111412a0700c02c40844250b0480101855200d000603a80096590312540c013007102c90203503542d00040d01c4070141c2685e0502e40103c3d01c4c0c0c0180d0340800f40a40e02c2d00e10030001d03404000300d0f50280b50050306080d1418044400242c0784200108454810000866035130014007017090722a40481300203101060318990007400c4090b240c114502d240c4001c030320961065006028a06080d4406032849030068140084800742d41c13140d1030f6101e402454801180180343c40ac2c25241c0d0f5a80800110400e51402e600003005546000e80c85845c2d00c1e0001841b6142220400a6400729007100c030744040c1100040ba9142c1013240c000c14060140203070310b01d6100c2c00b4101405181d65011000d507209600a2040b61040b40e40c480552096100d080380741c1c6e030600501c0031520341c5420003294540d001803051000140d80344a03260060007460003a0411030018000030010000420034110301c001030302d0210f030034109604000e48043c141c0606400854000c6403640601100c1d03048036801890705840002e1020090300045 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 104840008 1250 104838758 104838803
    0x90f060f07111203060f0103060b220e0f0402060a0905060409050a1b02030a110307020604080a03110c010806012708010507030606020705060405010302090d050304060801031101030b01170c07 84
    0x8480312000200c0380d50342d03a0302000d00050803030001e02880e078109103103458203030a106500711130140282c1490384030100014010160b100403d85980d08090b8296146400e80e00056075410304c1d4444000801c490041c080d0a00e0259451a003240c0e0440c1e43d80d0740c0e1348110800b9601c562059000f03541c07082c000b10380012409441d0704054480c540c008000c000103d1924003034041c114440240380d0041e03005000c01d040890082014a4207003140d281101d04107000b0f07900003952944590407420302600050300070800c00d83c01000120f580b02c9503002034140c1c4065140020025100103098904101c0f1200c15420b9050b25400810440214079000802c03541e01d4000650180100b40c400400103403800340c0008803948007282c100141da03c0181a280707498540070044000c0d4100003059540090611046400103000300b004000400f010381b120b56030f561542c201390030f120030850380d0541450f0401e17a400c0c459a82c400c20200c0070ba05a0b4a141d2180e0326140e80e41c400d2402480001003020038043c142c0141030390704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 104841258 1250 104840008 104840011
    0x60f1b0f0d050f04030905060309160305010e0f0303010e040807030c060f05150a03020a031104110a020607020c040b13050c0d02070b150a0806130302010b130923030d0203090f060f 79
    0x1d000c02441a0380703030100c0340300310140100c50240002e010040c007403040d0321b00314000390b40000e0f4a00840341c0700c1203110558411645030f030b8811074040e0740d5850441100078040c80800d80c00300c0b0b4000510b08562400c41e030924910340040c8002c0c00503000107010010540203190180c00c0c150490800c0102009100e8410300800d02901d9004c170844400c007811849140c050345000549034094250402540786d5951200e001002e090754075401510390910301c44100c5410301410b580d01d007542c000d044a042c241d00182c100314426440c03a00440c04c00700211780f07030340301c0041061541c140000009400d80c0c0302c41000c9840d0189000003079420703000095084c140206401210302511903880c030529094869020011801100c0c440c054054000034000340840e00d4080b0483c1034107000c0d00010905003003100000c2d80c40042910303048152039503103103500f05010458401888141c80400c5019900c2a00a03043d075a0340100b241e5000829000800074104070300c01c1c0203a44040e502c00c0105c560074100708003104c90310340c0b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 104842508 1250 104841258 104841277
    0xa0c020102031c1a100e042c0706120b0f0d02040f020c01020d05090127050a0f0b01081e030f07030909060303080603060c0412020108071107060305090f030408060f1b0f 74
    0x105104d0310780c0145003600482081110300d03160520a1007801d01440f004c0c06801041300c203451001d00310300215129403415001010035140c01307851b0705424840c01404034034034607501c1c0784441c2c6005d1181105480301c18a214003018200c5a80341410345510008010f00200840b075554540045818941424150050a10140c0315402403020b0b03640c80200b9801c0310f48240c48207030710582079000c10050410810b0a11300250290041c0d409941e420340325075249081c03050080b02c2d69040d800040180f0704060155001e411200038103180721601c00c4103110354034000c0052080240300000781e10810075000d00309050082c44ca40c1f9040c0070180c3e4a00f0090702441c01207421768068060400066a011803c608440a4036900e000540140035542c0044a005500402210511440b140e07009900030080198000400590740c010800b031924906290412408115000b083d030b0060106010000c004071b840c0d6404682507600d6911581c60000080c580c0120000c0f1414400000a00c05003032410b0348018100c601 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 104843758 1250 104842508 104842541
    0xa0602040f0b27010c0807211701060806040603060608100c09030c090506041d011a1005030a0213050907020d08060d0201170907080f0a0606060206010602030a0c020102031c 76
    0x554610300000c403803280880c0300d452200321602d001c48109243d0340c0a800c4407018500081400308a540302070855100309015580300c0c07070194142e00b10558400074441c0e0003504d440c0c04200103049000658440d101801600c040c840f0413000191641c4032035001c81c00864201c0303014071269036207090140e198042c20140421090403d601c6c09005800383c0c0400d02180c1c0d0002c05d00514614220b2181c00819000e032a0315445501c0e01030b129501c0c11800d1041500401800000554451480640040c50100f0301424010110441c1c2d1062141d040003c2c1d03603005030b84000260380c0e6803200e16040300d01d00b070a804c80e907400f9010720140b00450b5400990034035800c2d03140c2c8910020b40ca843c8104007004890030002400201a072051030841d03c140900c4036040700c0301c03404131840c1d180c07030301c2c1094140b2450071081e000700c0d40704403155010700040d8007466004008500103045554100180292640700340c880c90400d0214000b000350031a40300708222240311404c8100084200b81d41d02110015020001440c513480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 104845008 1250 104843758 104843789
    0xc03140304051807140f03090721030804020d170a0305070c0c03020f0a080129090103020306040305130b0a03020304030f1e2006010b0702090a0507020c0d050f0a060204 74
    0x1844000115419110001d084603101c0c00d185140c0c49194400400640400c010b12540d14020784000303000c3d00035a2401e9246944901d46044194a41441070740000a00c550f00031940100e540d80541c2c8040c00c0c0c0d0580750100c416901c0d0300100320001602d00d0002d000140b505541d00c094103840780940700d012a030790740034042510303095401c54503801205000ba2003e0030613002000149404401c1264003007000d4102c162450ba112942130840d40b46000c0c9103c0c0c0c14001914085071800401840c0800d02d0440300b020240d4116008669903010040c00202444400200c40980740d800c0142a0010985c6a10565440b01c08010041c082c0d041520201c010a4001d40000946030040c000a403066000000d010f0480e050340b081110740500001e000300110b07504d40511f1070010300520649001c0d04540010541d1095688140704449200601c6008580d2822040c40402a40491080000001142d45104160081c00c110303040c007159a1010725507100e040181010403101e60003074001c0700c51070401c80448 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 104846258 1250 104845008 104845043
    0x20109060203090915030a060e060a0b010809031905120709030c0602011a1005090301020c0c0f0901080307060b2d030d03020903030306040207050f0a0303051005060a0c0311190c03 79
    0x2d0b800350140d910f51051110001418509003d50302d1840313588001e048850400c50740d11030004840a0400318072240d08200200f0130f0300d10403406181c1c1916820300c1c003128145008132807a6140e001d0400001c6410780401c007143d50700d074890700581e52028202440c142c8242030100018110350050300c42128030709060607000500d5401842020142d4013407280701c0c00c0303801c1500708101c020340740d0403100000d00c1001c3c4010307001901c00344041c01c0084400c00c01420968504820485d50041480301c29100d4030350364005014410010042d01d103115404240032402200480010fa100c20b159200c1d00c6940103143e6034000e80020400e21f42644c00d100f5000e07a1448000070004a0981c412079104a80662040000c180281072a030f00400b1001d0040f0180d4910218003070b421130511303940385400d0f000281c60b10107120700d1000c2040490010641103402c5071509412110141800600c0e43c0c0150a0000f03149966040420a128003011005182c0a44902c414149800a03800380540026110800c041d1700e032284 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 104847508 1250 104846258 104846263
    0xf090b010902120106030c0f08061210050a0f0912120216030e0907030204051008060307090c0804110105090a0905131e050f0706090e070201020c0a080a170103080f070620070201090602 81
    0x14901680e50700c28101c2c008e803051318400800784c00e0355000b00f880000242d2218007480031078080c039140302010a060521498003000e075000c0f60a010b809501e0320600000160f010a800c801d00b64050030001c0101b5901c1024000038021b0722043d060b4001c4004100302095800340c1f012440480450381c1e0006034542440884c01c03030003a40141030308000b150110300011030290102c1940414000d0441c3c4020362681d01080c10794aa58083c6004504a80140010020b02c00d00340503601302e0030b1820b18148901000000c0b4140c94074850400c0d01c0382c0c3d40e000300e800c00e40f1080351720400a4001c0030b8494605a0f1a0f218182c008210800392050f000c1c0001c00400300c0000b0a41d00100d035116035030060a5403d000440c1c4c0d840c000584040150b6608000c1400e61000600130484002d0184c4001c80e220f0911401c0a4004006a1180c440010305600107000050b403040036654241c140550385a1031b040240b82800050a940428040010306c02420050b00f40441c001030030401d10030390301c81c04820740d10f6100703030b9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 104848758 1250 104847508 104847521
    0x10302090a1a0f1f020601030b090312010b09120f0709060e1501030c09091505040e0d090b0f0409060f17030c0a151103091006080a02030a02040f090b01090212010603 73
    0x24208101c0981180841c648080203420b1034030700a00300742001041c1030b030304c4004a10380310f004c0b405030704510010024440d0f008403d96000006d1400340d80752182d55190308a0b80740050145480f54900492008401c1d01c035800c6101520001c45d00325004012841b1034141d5441c500c3c40f07190384541c01c161001c070b0f1051241d40040e0284c401082d200e2841100c3c0b400540140c038070200c01d80d042192001000400030854000c07054184000c20704001c00508110503c801d940e001d0f25003104070342c059802c609015601142e540c08035001900c00310b03140c0c0500a02040701348502e1303000c003030303130506001000c030303960000700c68540848203102440441315840d900c644d901c87c0200429800c0c1c5402107a070800104607078510748041c61348001c40000c3d800341c0c00d180e80e414680083c0c0d060001c551012901c4080c0c1c0026120f04c20151600328010509480140e00190b42c5612030440280038540303a0b04441400300f41070300b112207001d40c480485000f541e15890403c0c02900581100f15484408800005495009100d40e5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 104850008 1250 104848758 104848781
    0xc10050714030a09030e13050f0a05040308131415090d020604020307061b0b04050606040f0509071214010203090d02061b12072109020117070c12030608010212010302090a 75
    0x114110f50b02c1050f81c03001007600e1001030741441088081c1c240b0642c2c650000e1010842d84c000006540d007040c3e48600762000e002030800140c58035210522002c00d4000b40c907aa0b110300d0108196524100c83e1400560564141c142d07118980300325084074002040394a081403064a1140484044c0740070050200c0e96a0400e0307030065090303003000c401808003601c908034000240369921160100780384c0035540d0248441d03080b0340c1501d0720f1704550144502854680030300440e811a0050a004600703214845a440d007045105006040000d20481810440114a9480b070030b640c00c00215103d14000d1500b54440000015003401402248001417644504035441d07848002580042ca0030700000b8041e5800903900542034209110b02c4110161134081c0300300303401e07600d83c1c2582000701e141401440090a140a145510b507800c0b01020204810305034024002c000342f0f5040760810002e086400d409074014109a00002c416500000310007101c602003504c2c9a048a2083d40c4804460b0b881200c040100ca0000507030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 104851258 1250 104850008 104850047
    0x60f060d060302190e07110f2406030705060f0c010f050405150c0a080112110405040c091103013b092404020d0b0a0204050a08100b03060c0406031d030c100507 70
    0x300e41130903c902e07c0c04000303510780c83c00c880480151208043c5061640314950b074404440c0742d09a08000e0707548481c65000038064000700f1580c0c0c20500052083d009032403119250840109810212900940041c0d0400b01e80d01d00810403800c0900f8240d8071a001d4640b0f148107103a090000c00d0201c580e480440c0c5455205546054182e42003070549658103d1f0030b242620404030104003900d080e9928810355000d0340c891000c94120340d1600c0c0c19a810303181064164040c0b2801400100304618000380c40302c5103019542000d0211003c004420418a0103821144680c440c14000b0440602c80019000c401c0341015010008008000c40c0fa50300402c0045030002c0d0021840750241000803802c2c4511354022964410150a1644600209007642c80c0341d03000d071146078000e0318920603a41030781c8915480040150042c005500e000208040c3e5441544607507020540c2c0c8070300c2c460155203122081c205003007100007030300c0e65100441290359030340c420701010090307540c07918001c5110b850151414211441c00c840c803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 104852508 1250 104851258 104851261
    0x60c0313300f090e0402041b03050105030f0a02010e0904080c0601091a09160815040c020a170717070501061206090507060f02100203150301060b03040611160803060f060d060302190e 80
    0x44c8540c071403005001242c12540b5142001d41c0c00d28000b2444811070a44d507400680c0303601d401c08062600850b0008210715402011003d030162b40d001c41200c0713558100b03031810325154850b4541000e60b80f141e0343c04800c1c20b0141a0002c50841050340000c03000d02c00c01581c10f0390a0498a041040907482501c034041d410f01c1403200452000e01415580d544010070055050203440190003140035140c41050380001604a000c00c4402c00000700c54041007090f00c82020b50810350b1a51b0341e01c002004071036058a4550020800d07104021007500000c01500980039101c100c6c20451501d01c0c041c15410300100c1322070045070070110741e035480384800303142c2c485141d40100101c42c1002c1d45c1c28029440a0011000146a01081e09060700c0c01d0040c04010124664040c0d528030700390a0680031903003c0100310080c600f080211001640344104039600789a048002c0c1c0b0340c0ca454410001da00c2c0c0d003582d450b25400810103c0c100810007642d510800840e80251040d804c0c440b2102c001c081c07070401c64020382880704807640 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 104853758 1250 104852508 104852519
    0xb180a150809070f12020310020406020309150403081c0c020105041104090609020306011e0608010602070311060d050910060503010b09070e010932060c060c0313300f09 74
    0x7401181c0008070402928500364503400081c038070458503003180c0652001d40ea61300b401c6003400c100300c0d42e00000c0c40904500302410000e00039181c2c480c0544c030702d02c00e983c4407030324a0b5000f0424003210000c69202281d2566035481d48100c20700c0c850100c0d86e1451551034407160700c040714010700a0b24802ca600c140218064078001d81000020004580291100b580c0c40c603400c0010717241044154040e042c2e4401d007400a004400c04808a2401c941100b82000b103840d0042080741c3d000203507042501e6000041c03069040111022078550b01601c0085100503051505002015a0102d035030401c00c2c1c604507003400165140d0040c54241c41200c03011740c0e0400700b00c0c00082c080910030f0714407a8031858149825030030300da519500311044038040114001d6032207281002d000d00100070550300d2204001a00c6180c20291010a441e0302c500e0000c03d142410100000022021803011000c020b00e035034441c0300c2240c0c0800a1070028a80c2904402c072403000c0711150303000710000b40690240e8561594558808110700e0400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 104855008 1250 104853758 104853767
    0x8041502030901020f0304140f1209010320071112070f09050601021e060f10080319020106080307060204050307060302030907120201210b0102060f010810150306060b180a15 76
    0x141030b40000c2d5820300500004000420046000724001c0780ca40d940c000c0e9510810342030600e51402000254018201d11025202d5102500c102107000d0a0010b070b501d400c1800c049001c419440c1400d000d0200007140d10030020551401401d990007550881d00b000c10141c0d18503a03e51003401386410300e4a22005c104080e911640122360700500c1841a1880c034070310441100c0c03040c6003011201c1c001e9000601000f2143c070300c4501080c2c4c403014040c0c843c80c00624122031a604e83c81034180101114103041600c80d1803030b0003508500001d10b02c89084a5036190309041ca10029001409002d1181c0070340d010000b1414842d000380c030302600700c0c50054513031180740c00302130403100d0406081281448036038882c0e100800d850348461101c0c0c0200340b0001c55001d120b00002800c020b401000c240d0743c2541c03400140b201c0000001d025041c8541c902002030809a10402c40c48481966440100f006040c0080441c5241840000e41000500c950417000040d0703100301002050005030041281c201d0407a02800281c40c0304 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 104856115 1107 104855008 104855011
    0x70819050609070c020109030b0106090905090303040309060c0314040e15010804151d03040803090102240406020f09120616050c060105090c120a09120804150203 71
    0x7007980041d8001e02e01819420130800c0c0365041c0340469004548550203035801a02079a215a516100280780c803100303016034a001d41c208004581d86070000801c0d40d000b5035064507500d104030308050080720f4150044c030b025010012088200045200038000401c09042c001718003500c1ca01d0000c0403038250b01c43c00141d05042000d0303901044049148941c141149402d580d40119920940d40d8014404410358010f900580c080007500007003104000004080500302a02518000710310001d1594283c1030b204c002c501c0c03210b4013800140c00640198001c040c100311340b000c1141800304990100c0c3c4002c4d091400148503034400c13003e02640041000000c15034003d05d1400c40d00d0503001036081c81e01d0b440103106050151840300d02048031402817105a80c03001c2401c105085035031a02d03034000c8000e0402c40005840903c00c2e812441c401d68498400c551141e900050260900d204139441c00d40298070 = true := by decide +kernel

theorem cover : BRFrame.Cov 104676258 104856115 := by
  have h0 := BRFrame.cov_init 104676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 104676258 ≤ n) (h2 : n < 104856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
