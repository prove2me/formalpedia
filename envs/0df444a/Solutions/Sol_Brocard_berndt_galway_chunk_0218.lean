-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0218
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:32:30.189454+00:00
-- url     : https://prove2.me/submissions/6f2156ef-6f6e-4852-ac1f-2a3a1bfc1483

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 39028781 ≤ n < 39208637 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 39030031 1250 39028781 39028789
    0x6130902030c040305010f0506060d0b030a050f030301051c08180118080304140315010e04020a15020106090e0c0310021309060b0c0c0315041b17070306050a0b0109031b05 75
    0x1401500400b41c216211880c516042d401c1d6120b100f00100954107201c244816610791000759220700340800c401180c20010741000c0fa280100600002d856886014007034000300e44048001c6069a8050b00e104d81040e1401c1d2100741e0f0714201400042010b4001c000e0b44141d401e480c400e04180100c145000808003984078000c40b50800030b6008044141c000003010440d0304000441804480c0c415009060345090003140c1190b001c0d01441727191000d500040c002421940c541602d040034000309016514031080546009000708001d0060200307092608460200080c00003400140c0d5500040040200303c0f020010755002c2d4002e42e0304e180501c243d80f035001c105040701e40501c0c0041c02aa80656407112101c225440c50081601c005900030381101403115807410300070b00900c0d0701c150800c01810a030780494052a00e48411036000e5600d10200c0920346400880c0070801a01303d0740680800e1200c1c0d150b042d889803c841c1c0c4508054040b0b030110703070108000740e0042c0291840d00c204a80031072009941e0400306d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 39031281 1250 39030031 39030037
    0x1506070605070305060406030503040e09030f04270e0d1110020705061009090c1a041208130605030c18030a1a09060a020301030206030a0207020d2312090303040506130902 75
    0x200c8009450301d00300410241d16100d0194422400c903028003240c0e1558503504e84030701c40c41c01200600d005200c00038820710000c104030b51140000c49a00340e616955212207560128960003010780c1e03502c8030701d44180c07401254025949071001703041c05000303a82c02c0500b080d41c00c9160342c4c054175018042d0f40c0319162508920320240400354000c101512840c50905040382c02d024550300f01141c42071a000055000c11041c200300000d8842c400705402c0c3c2e0026045124241d40104da002c0070b03800e002d9004403020005080c000e04030500725800c0403142c00751104825525804221080e4401c85018880301204038220b078071124900d100a8195007915199440b4000301d090900d541102c00c0d01650300340311240d40d040041c2c5074000c542c0c110450465045600044540c840505108403698003c5a03000030343d503545a040f07450710340c0080032540118010312540c80c103200d12106640d40c1c4c05080d80e403a0501d22500229494064010090b500d45420a020040c503a0001d002c04203840040781d4000c54501140e20003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 39032531 1250 39031281 39031283
    0x1906030f0501081203070f17010f030501051005010f0c03030213062a0308070302070501020c0d031e0b090606031b07081305100c02040e0a0203060f040b0606070c0608150607 76
    0x808038004020200d00c100340d80c010ba0110b400e541c08450110580a8040c0507240c02181a01d028600042210411140b82e500074902c00314141400c400091501d0b102003400301181e104000a1102d0f94a4440800544215104040c041344880112900305d900ca0341e18803400070311030f040042c208240320741f003925581083e40001001c607941204400d48484101007198007495020300318203002d507240d940100a00d5001d0000f00606030003080c100100442034042d1041e20069000301e50b050320f581d86000f80a011594000703002d00f410604102042e201c1b500070f01d1450b12000c1c0141440742c9541c2c080c45201d0344010500b40c8020f082a0003c14040000e80040443c1401044041c0c0c403154002c034455860943e0b6071081d442440c90094060055030004184083e45404031800a0003035041c0c17800c00c3c00c0080c882e1000354107010301c1003080b540504441c0801c0c00780e40038100e11186a0340c0c61003403103214881d003000135240c950002400c0001c00d202c1e40302030b0b51144034003a40543c800e9411001c00d00a4010030340c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 39033781 1250 39032531 39032537
    0x6090d050a0b100b0304170307110f1501050a03110906040608070b031902030601020a031107050a0f09060503030906070f05120c0604050609070f1e0e0c070507090507050d0504021906 80
    0x1081c06044410440d40724041c040134400390349107080990b50204221980c8203141d899040c0400001c06007070040304824420105107041d1485003400440050322081010003000003140d104001160a052407c0c8034070541ea07004268517929440c910402c00040001000b05502940ba1000483c0034942444000000e15011031420780380c2c28541d42000ca10540204800e00c460301c14010000d060303030300107601c40c08203400d401c02d5400c000c0641055802e01c0079603040f480c2c10003440c11000404a4106a48404131a044001008943e0310741d01056103910039000c00550105d07050244101040042d10380607006807058045800300e496168807940c035500a444007044980146007003206000c4103002c1264001a56009019860300b0220380c2c0300442804d0140c00c48540d01ca81e40c2010340c820304100e4a000d0924244c0d400b0162404509000c0c2c01d50003100220b03124029250b0018100040c0d00885015602c0360700d5840c184070b581101c1030010000244140e921080c1005501d82d418440b038100700c0a0b0680d95 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 39035031 1250 39033781 39033803
    0x19060206070215040b0415110c0c0a120c0302090c040801060e04260f0f040e040c0302130923010b1002030406090b040b04032a0b070c090209090606090d050a 69
    0x1210182c03c000307074100300e03070b600d01a40410040040d8141082a501a901c41041c0c00740701601100c100043c00034050048200000007504800e003540003a6940240f801120303100a07a03502c48407030a5012601110007404450f40070414801031415003001030380704800100175824242c0d00c2002c0c41c04d65015a002c400d140304900c05120500800f4041e1070040c1c044103401d03c0340004c0b1881c1c42201072042c0ca40c1c0c10b00303401c00821000110b0000c00203c4000340041e074840000c1c0d051900300081e24007128441244510030f1004014a8054a070059682030340e00940001e101145404400415002c907500600c401c0d56120024162035840c0f21040c2824a4207900441e2920309004001d0000035482c5c226110400040c0410040c0c0c2c101c0104071000e40358890401c641c100386103041c80c1000c2d101e040d410400d110007060080b510040400c0038003034040c007450206a51543d1240410100e103d80628641c0080c00c1c1400102641441d000a14410402610911100d01d03a80c483d1070074101d009108691030034180f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 39036281 1250 39035031 39035041
    0x1202040b0403060f020a090e070207080703150c08071e030603020603040605060a061d0622080109030f050a0c0f02060f070b040209011505030a0c02030f040602010e0d020f07090b19060206 82
    0x40d201d052088138103500210300d05100f8403400740c1418411703c13640701c1c15000c05c400240c005100380900c0c80101840001c841c0c0507601e074589114583e00031442e080303d143c58030070700b05403e91003407407071500408081e260f04415031100e103000045182c130098000141034072060000b0040c1c9a40000f94461402041c000401c0e0a0103010441d003810194810805c1003032071460200c00401d403c880100a003012649107a03144000b407031070b05a028580c0c0c0e405031141884030700045c004030190410300b8410311a548184030040d00141c1901c0a01409140307a0014042641204c0040c01c800d170a03614841c001003049082c203144550700045a0300c920812200410001c080c441141002588107000d400d84003480e001c1c21448050040aa0000901c2c422206403203a10011805009000716140503c1138106203543d1074072804064064010003110321981e01c1024014900d041c4081010b80350411018054056146030081c04400350a012036130390323402011015005a118814100000204400d4020b05280d140ca = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 39037531 1250 39036281 39036293
    0x703090b03160f0305060604050913060c08220c0603020304030e040501060e01020606060708030c03040c03021309140a0b010b090301020c0102040e041a0f01060c0f05060f090708070803040b03071202040b0403 91
    0x8601c3d00e40c0615040400b40621030355484140c80560714141c2d14000540e8a81503064040213600401401c5540380200e4045001d40c0b1220b11407240711001800a0803a98802640c10009885600070f006d00fa40e90364240040ca00ca82c0080d41c01c980280707409003036112807070000307400c0354804c4c1d0041000c200c1d668002c1c085960103000d40c541c00142204c0b41c0d4203110070340c0c840c4d640c40c0c80000c11461810a001001500f007007040c0506401842c1c01420107000412000713402c000501d45094107594001d00788440c0c0445410024025001d164031105000550340b90200c80c83c0181c003c502c41c030341d03d5502844010ba21500900c0500003c000780f180d60001814603050215000e100040c00d00c820510740010000310243c0507036100c0c1154a140ba003010b820354070b030501d8054040c05000040103801840e05002c44908d58070465409190304c6025038080958031700e42a42d03035880e1849000c0745908203001c20401f8808080c0590341c0030a05060480e00040303c0a03043e1304981c050b1300a000c0d028000304050042c41a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 39038781 1250 39037531 39037547
    0x414100c020609070605040e0126010603080405120607020a0305031e040501050a0506010f0906140f0304050703030206130203060109090302030f07150b0a060c0f0c050d030e100c030807050703090b0316 88
    0x82c41d8100745290500384490071703400030814051280e105d140c00040a0140ae40c81c690704240840400007001210b440e403906074415400b03440340ca4456a034007140c201240e80701040361800b8400540081a900e4403550b815103060300000d007841d12210140182e0b0a01a40d440062841903104100019580c60700343c1d0490304840c2d001c0d05040c10001e19100902e01c00760443d1764182504c000e030400b2800c0804001c583c40c210302c40c0070504030305480e01109100800400250b800280ea11036020703134240f40c0c3e80124684121440240280d8158081d000400c2850300581c00010510300a2050340d2800902c0003100b5030580c000002103544130f00c0034985c2c00b482c00b040e1048000202085902842076403a10380014008034011501400c02d050480307403035041142000e8254020300000d00105840703001400c0c0903041608401940780250003018001d80d25a100b0000c4070f480540c544c0301e920958035031040440d80e6400c640d5007242407046d1910302180110b0b050b4003840c4030300030300801c1d00359a1910f240300808880c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 39040031 1250 39038781 39038789
    0x2250b010608040b0a0911040204080307020109090510140406121209050105030403050406080702010b0a061d060903120a0e030304030b0105101706040e0309060a05040302180f0414100c02060907 85
    0x2c081502804000f4940345002c40d000f090060000c190000c807414080e582810840169074410310011340003980c1c09010003d003520034000d07203410114542d1841c3c0c81054980454000102800e030b400d01b40217180d1650040003410700090000580141ca0b501640881156410150ba007048085034254240d68480c00c00c101400d820704e005ca0035401e040d0b4014040c3c2c096070241d1014000c040d400140380d24400d5124541100c0002c00c0415401e940d808040c0c030605088800c4418908541480301207814864103c480c10103018000301940d0203000700d030000541215400e203081240040186550381d40c1000a000610b00400e00d40006514080422004680034501c14084c010112085041d149598200f640c0c46001034801180e544001d42c3e0090562050111491784100c0c0451505801c9a000d409401034030310946284c40942c900f1303208803016007000c48400d507a060030035001400281400114441c8031003c542283d000d0919152810700360350b54400c108005900100c20010004010000c3c80010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 39041281 1250 39040031 39040037
    0x160e010b090d1112100c0906050310090504080d050907180c0e010f20030309060105010215061302070501021606050a020c0a0f020105120a09060c0905061c02250b0106 73
    0x81c941c401241c240088540d020b040e40543c1d00030319202d81c80310480300300d50b6103000050701c0084d010071104800511001c082c07407001a0360034502013600e0b401081128014240c0c000b80004140c1780076050f0015090042088903040010b00ca440400040c60050305c0c0a2008040603008083c00d10390440039480c0300c0c01a464901d4104800501855045014056076030703020b00e0480a500d0b5451010354250030703901b1059041c1488401174008140011018502a801c0d420603035500d079076640e004a036a050f211030071040e0f05841070041025840c11003c03400c00701040d5000541848166181c81e400ca81013600b95103488010030045100f04800c82c410300f80d0000d46003408500b44144d4100041e61991081001004600081580c005584c0508199003054001e07506403400740c54400035040260070f0350708007107889034205868035001e50300400c3c2e6003007a55006040341e414015038808007000140b50350000e580540e420450300c0220854000f04241d01c07900c1e954203d010350102d207409080b5902c142e00c5a010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 39042531 1250 39041281 39041287
    0x901031112032217030309060f1003021002100b01180303030b0301150602160522020a0c08030903070201080a050106020307150e06010611060a0501050102030f070302030408160e010b 80
    0x60580c501540410000362240c06107961403140242c070714031500744403141c0d0b4550300006040050280031100191130b1000c1c0700401c507065001c460307a42da0000b43c4900e401500500c00082ca02c62521910070b600c041d12a950594555170380d00890b0b0140f0381d01c2d41120040e04134213a03009004d41a07001d07400c42c020080c030700f07120008081440819041d9031800700408054690611685554094000c00b600494600c540348125a6840000e5a5086a00d101c5486400c02c50390001d001d2410400310030102409190945403154018910002503101d100e411050002e00380c2c810002c01d5440010798070400c0c03420025517442103e4000034040110003055444140e007484010300c2259400b2040d10520b83c0d000341c401c0c0794402071031003100281c01d0214802c030041c4034410002500030381c0701d059510754a50540c180e40440d1540c3e441c08040d9042402440c2c0560710070030456101000c1c050080c5210f500a105403401c10340c49200480c20480001344101070500c10810522491103461286070040038030b0845685 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 39043781 1250 39042531 39042533
    0x30f1b080f03070e010801180b06041806050a120209010e0c12040516090209130908040806090d0806040509060411030114010b0306030127080f12090a03020601051c080307020c03060a02040311090103 87
    0x3141078411490100301e07903200c0c0d589c00d40c81d44072801580d024180e43c83c111031440700c0b1a0305550041040d071040600c2107401e294002000094154114500c0c0d4001c1c00003d0907a090030b800800e1202d01910742103030220304001c604035403110700380300724025403159010b013044600050104061011540200a20700c0c81003251a0240e8ac64060651070300350320a2012440b0505c1e810441001e01031a8400d500074012201008036a81011a04440e0b480240d01d0b03000c5a51616401e000480300110382000142d0702071008600031451040495410f0744005002040c01d2210750700b801000f03442030388145c2e03480c0004005d014840c94280117640d441e020070418611000080300301228422400d1340e001e8241072002078440041100041250140204000304403502c0c2403071081e20307513203001001c000c3e4014000e000001c2068540010b03400c00740000120070300103c0b03100792241e010f1544054041401e6124000401c01e503a2014441c5501c46c00041c44c005032250f1071410400c2c00c51480280140c030402d90500180 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 39045031 1250 39043781 39043799
    0x504080601170a08120702010f05010509040f05010b03011802090606030426090d0503030703060905070207090f02040302030703050a031206180911040f020d0e0703030f1b080f03070e010801 83
    0x30704540c08502624541c80750348501ca8204581400003400d0301e00b000030000748002c190181a8098030a0340e00801480c81440ca01d042201d2080c043d843d0f000301d01001240203d04110054220a4001c20000032020070b00d20000307007110800b640c1d80c0c6011403032480420035468503008141d171113071040d14802d103140b50650b81c170121461400b094403001179000380990282500041502e850301e002a0102041e400c0301d080c910b99980007120840c0000b4241300d8003280445050042c180074005a400600013103050143c010090802c9001c2c1144156080c400000583e50400900c0c00650051000d8842000c030341c02c004045281e11300094201d24201b100800141c0c103c8810349414104110002400a01c2c6180180080d100807002586c85403d003044a61003000c1a40180302c0490420000c01c07080c600840440d86a080c80d20004d004107075035881707400c4090b0081020714000b0074074545450b1400010351f00c00403550000102184038480110030400c0300c40d005880c1650b048001d003404150380d85400c20413 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 39046281 1250 39045031 39045043
    0x3090f0c18240603070305090f0705060901030c03020906070602090111010c020706050c2d0d090506031816030b0612010b030606061c061e0f18051003020319050d050408 74
    0x31004100708042480c00012410b42ea46004030b400a00f0701d0b5032400c0c0b68400401a00c0240e542a4503030140244c030031031034800000e00c1b408803400a403c1a007003403440401500202813150501c01495000c101003403007961104010184030740f089100507140c007107000005084682244030420140c5c58210942c114640001d03151040f02c055142590391200c40388034071030802101c0d111a02d50444440c40d50b00721400e0a03276604010441080440d0b542c4c0b60098011581c0040390320807503070008820404035942148840c10b8052916561086400304183c0c002150309542c41d03981b081d00c44a04d241c0c140021458560394a550280045000f80217418502c0e0001c1d40755000504030314070034000010140c02080b1078144480045056180402c8015903d9403203001180d00720740c6205403100d0445020821102c0031180703005480c20400581079051181c1c1400c401050054404c1c00f0300c580c036000c00030041e41c00b04110007624010254840c004615860310500d0040441e4105050020912040c40303403003000110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 39047531 1250 39046281 39046291
    0x10030b01091d010e070311060a091a04120804030204050a0603020f01030c03060911040305061602060a0e01020403230f0f030906030612060c04031506180510090203090f0c18 76
    0x248088a10010b00c1c1c1050042410310542e509040104440010205040b001c581c000d000521156460b01c08006413849050b50780008100102424442c00c10303115103010303580380300c082414942a211060741c0c80d02c0c290f0f02c400301c035401c90005050003141018061541c12281c0150103110172401d503400074030040b0100b40403504041d034800401d205244642c12007802809100740421031501c0f50714103291250b1050000ba03231903106400114000860791800c844240e1502d034007401d16a101c0100407070141c130000052000d15034003400040041440c1d01040e54000803101c421010103c9169030740707402d051090800b20055000f0038811103005401004036200f0480440310380340d50b030752540c00058420300b200e50b11101a00c5110100400007403004000c01c140c80c0203d000c8504425142845429200c80d8041c40002c01c412820151a411346900001c0e000905908030802c007603280d1a480003260011100d00d5a030350b0010411081c00310307060124181e00f002c143c441031001d1107508161f400c81000a01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 39048781 1250 39047531 39047549
    0x1d010c020103021c0606051e0307090b0f0409020307030507020114060a12060f02040e0f0a110412030e03010c050a0f020105040803060d0302030f030903070308070c0f0b09030d06080a0b10030b01 85
    0x100030801d96001812141c52200c401c000300800c46d12024000c000b6002100300e170702c0f40c80c2110038205d14050f41c002964407035003296903031100071410241140180c1d00200442c2c482c50a0600000c036411116001a622400346a0b400003400c0c64840e03002825504584484101c514086040c400300f40c8640d514002a00e4440800c071155102614001c0c0c000c121602c5030256142c0b002c200410410301c020819802034615080e022400d0700c0c0c12a44404503503240509106503075042104000400281210505117402410591524581140828203482c2481c81c4100010f10005440a5480c0c001940d16515a03c503c001c100d2031526540301c3d0042d00c005800b10303204100505a0008051007001200e42440e00c070000075840c0c1c2000c0039103660365000384000301d0201c5d000100090000d0310815600006641119040d158003185032540740d207500014090f40040e0000700505019442140120350081c802c8000500e0107007c0d0741040c600315000a407910b80210f45986041010504a0500a064501000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 39050031 1250 39048781 39048787
    0x111203070504080a0602031f0602060402010305040f1a090709060e011205032703120c03030f04110a0e0a05070201020702150c190f1101030c0203040e1008030301080304061d010c02010302 82
    0x85003079035036000d680d100050b603108180b042802c012182e0080c43c00740c3d02c0101030b41040c0b9140c041d0f805051441b40030303060043c2c0c490310024001d58820703040b060f0024095006103002745980d4640c029030040c2003182460f902c09210500020140800443c0024507100400708401800c02d401c01d194445d061107000060703040513101c0c000b409818021585813162081c010280d20503446109011581d0b4280755074881d000e100301e80b0869080c000d04407940c000311000503624540e10005009074034807001d001520f0700b2042e90144441c075120040d0081c042c000c404007054043c50010541401d030340c0c00401050841e40103110f09e80050311002808030411103a015a29190240d9150003854818005c0385901840208030704d035010301001d4000f07007460b54000c910b01508507803540d00560070b4170030841542c00168420482042007401e0541e001e9003149041da90314010701e554165051860b0400c0e040396000e900300003020080150000303001400240b129007010415540e01c0006012a802000c01906145d000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 39051281 1250 39050031 39050041
    0x90a080c01060816030c0902040b0405040e0106031e11030109020d0209070203120406060608100e06060708070501050403032910030c050702030a05060109110702030a030e0102030c030325111203 85
    0x20b42000001e410719400301c455001d9855032070303d2011a03501c401d640300030f03101c2004a003c000e98000c54054804500b281803130b0507e0031051100a02d4480d4540c080c55503204c501000095540c1031100130780301402d200701030511450500160b24600100302c2442070385030041c0c0400584a54a007540d9042d01161001155510500d085c2d05520450480038040d4a44200f0001081100e611940650b0550340c0d600c081a6034030300c0c40700102461030103803c010510390400640301d85423400c014042140f0036807079681014416510702d801e50b413040c0c4084002c42d4455030f130b10780a0003000c4803070116440d00c1a59500e84005a01c080307040010200760500c101910344000706002ea000758110b034000c0b40d01404a40740c401c10f500f015521450203005210009080c21044410705000f00c0a07220050380040c003902106000390b4041c1c80c1c0c0d00300244914158001440020024a0240042c522031a2a11000c0c86050608102d65a10403c20019081445590b841001d2840c02c0000c21440d844d00080340c0594035150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 39052531 1250 39051281 39051283
    0xf120a0803190c05070309080d020c13020409060902090907051c0207020406080f100f02040501171e040605090606120c041e06030305041a070b070c030c060204030b0618090a080c 78
    0x10210441c152030810904400140e448001404d40350b006c2d50343c06031402d0311600216101c10342900e0345c0f00168094221182540b8107505800895043c10100503e46555815228103030340c501c0c0c1c002102968007282c10002d034200940304541c000c0c15860485d15082c0300024084006c14000e4205120035804140d4100315103841c0d000310068440c49045419515041c04a20364980d043c50104c1003036401e101196826042c98000e9030281c0f00c050311030079180c0c0a066103c44c1e010f400246100c00345000094400031140c1c1c09140300340110700400011030140b500003c03140c50494050607260151581913141c0007034640c04100749039100c0003160080740d85400304c0003c101c0031040600e010125031030800004105600721008000302c58071144600342130100005805a58041c034180501014021400141524482e511b07020b00381d4030904211328111102c0c1c9a90003240c1060300100c0351030880200348036291074542112000c06440a28104a520705101c4180e25160200401000501c000c90a4400741c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 39053781 1250 39052531 39052561
    0x6010f0804050a0f08030a06090606020309012a0507032f0d031215080c09160807110a08030f060405010f2114070e090105010803030105150d05150f120a0803 69
    0x1d00162400b208513014204a440c6603c250364a9994900d0075038000b52103e218010107049038050b030003a50078a4201c01c01500c111444115140c0e451a14170440b006201905940c13520150149000b8510f041c01c40c40c00c0d0144000c02040100c908490341c10102130315900d031209040f580c109540c0809203c00c10714081e0360404800032162482c1c1c3c00c10301260350404d1110010421999001c0481e082695a4802c0c07044030102a51001d200103000d01c6415100d038003a05006412840d540340c04107403060f8440140381010411503080301c42820001c00d021503a10f810700340d0341d0003500442e41001194500000d241e502032041c400e11000c4d20503a40c5100c03015115941031000c0c1500000440c2e03808242e4281d00d5250340705801801d6890801c48041040d40405104003410b0b24084002540703142d080c1020004110b00c002009070300030400700103007918012107014590007907420070002e003c00c81e000c400300079803103400360131041c00b1346024402a5900b401c0061124491030b0810b0000c0ea40f62103001c928404c1d12 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 39055031 1250 39053781 39053783
    0x18030c010c051804061401030c020a0b040c0609091503260301080703050609030a0207090b0a05030307061d0a110625081909060c14010204150801140906010f0804050a 73
    0x351030039800340c1070345400000a001060002e804207184820301d2040004495407401201080354a141c000e2401d540a40e02000c500300090040f02c1d9034801e1591510941c0000b102c0484104040c05000c009840d04182280080d01c2c20006c10301c03000c0f880d140c0c070360200c20796880040c00005176032010821095840c4100d40009a5418007142d4039a11040b60725514044ca220440e468810000050414000842540c07072981544d0b0190032440c2c035003202c01010b0002d54440c1c40e0322400c1d009000030740342c1d0304200500c400d41c4107071808144074a550007802000c1000700c000348550307002210a0000201140107446094108442090301d42c020045c6612504080e0b200c81c26810110700c807074000b809504802b404070384503817149001580c13600c200d080320700c2c030020b00c50207001c0784d1040040e400080e0800b405c41500c401e008001820329950307400006908a6118851000c0b800c180010301507004112803030000540203940000300b600701180020000501d214022040001c540049400c01005010200180d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 39056281 1250 39055031 39055033
    0x602040906080c10170a050603011b03051021061109060a110d0e0609010507150501151701030803010608071e05250302120d0605100c12020304050918030c 68
    0x719894030b44190342d88080448483c450032405a134401c0c5503200b44c0448100d0366496400c01c06540344c6800450150602034a12a07055480b007002912100e41c036401000580043e6070046000d042005140403c829030342c10203460902500700441901e12120001102582d000000140300e00400e20b15110074054040ca15601140000d8030641c5158071100301421032001d141625902d554401041e00c45485140d03030f06812035028000025598059400703070000c0c030700a024462658035441c0d405c0c0c0854000360840d0010b16240c0e070203058082ea002000c40403440503450641c0c455415500c4030415404140320360810000440000754089220b030701780c40c44640b16003101461030341c00c40d803018210343c000018405401038140300c00b100c0450091480380c0c0daa6010b070041e0403081041501840380340c3c42514141c00c001e842c0d406c002525112002c4181100086c2e582d08604208603103441d2060882580c030010455100380014840741e510001c0217a042190300444400540020031824114004e40b0621802 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 39057531 1250 39056281 39056291
    0x60e070206040506090307020a030611090d0803010807051207120305040b04060f14120c0f07020904050109050c06270111010f0b01030606140909040206040807080d12050103050d030906020409 84
    0x28580014400e40a548100182c0d51140e0321481a140e990146004c040d43c04403104c801000462441d9010240101500034410b280074540400300f084490840d030300301c46801d000001008808414803041018040860325502c00341021038000b95284400c0c000d0300001c101c00c086a804040c02101107800600410790455121a500c802c0030b0030030703013412030582c2c0464401d80c48007041200c448102c2e5010505060303404c0a0317440b0803090780307000c3c0c1140301c240b41142c004102040240c1c0c1d0b109403081c07040b40724400201d42d58003545023043c103103a0b41000c1c090050f0014803c5101c9076545c0b0003a540d6140c2d501079041360f00e403c1c490040700c1c601003104035405076518140254041625a400410300d800c0280c8040c48010b580d298202c0c0c40c4045c1e54888540c07400c00b88000c0c0d000703262040710150806d0000741224103240c2c03601011410030710720b030b4010304150348510ba60900302608150148410350030f0401c10021503255032617254861580000304402c0507aa200003104000b0241d0664014004690003004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 39058781 1250 39057531 39057541
    0x702100e12010608011803021509010f0204080604060b06030c071101022404020f09070509010e030a0507181802010905040506031e0c03010e030412030f03090203030f0403021003270204060e 83
    0x4003c001a0058030515400c01789056600651007241031101607041e8010300c0f00d401011b9401d0740003040a0300e4807400b55207400e1008440407090002c0c0002d003094002800e80c2d400d241c81e000c0d044860f01d11501d03014040c140308000440419209803070380c0c00d800c401803c204090a00c0101d0600d10342004401411901141500d5225400234065114900c269a94461150104108514002c00302c46840004030208894a455407180da10b5802209001d8110780c1c902e1000d03922181042003541081c002c3e0012020092a2000240102130310303542140e089112400312900003d0025915016540c0256180d401042540d103040055441e100740351100c07408403100b40c0d440345072100e40c8903490074403e6003408029058a08040200e40460b0008150b059411010f641c041e60400f00c0c40c00144141907841c1148009a00c0038401461103a099503641503030b41c1c5c154410810382640862a400030036190144004c02c540325580d0380748011380c6400710b58082510f58400103001e0700b0560000a5610f851005003c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 39060031 1250 39058781 39058783
    0x702090114010806010c0b010527070806011206050a05060306060d05040303021c0b0f270c0310150e011101060305030f2a030906030a1b0c0302190201050702100e12 72
    0x801200076030b0f500c2410f4646000454815100c00c1c00545100701444c010420352401e01e0b507201e548150403803408041c143c031000030500040b08680210106050384200002982d00400c4030794103001451040082c00d04145c0460b81496041c00b80c94054000040864803a540e82402d4444202c1141414415841d2074a4010040d4218800d54003040c012800c0c4c414041d1a24003603110130306805000441d0103030841c03040006d102d801c002d0018070001d0503035102c405600c980702110300c5915071080040d6603041001c1568022001940300800c200440c00f4030340103455001d110503441200c00d1925280b1a22612241d9005207050743c070040041c400019001400703982c2c1c80c0604640ca15030744182d00040070003034820b0381070003042001003401d070420410b140a614150001e150402e42047e000541c5d001c44110051101030300c5084231000c905c0b031000640c2050f504100300024041c02c0b0700300b662015040d0380007824501407488028415008910726100c00b500c900080080d00328010321090645501541403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 39061281 1250 39060031 39060059
    0xa0309021e03060105011b060207170301030303060806070f020d0e1c03030b040f02030c040909060f06060c0b0c1602040906020d060608011d010b090d020d020307180b120d08090307020901 82
    0x70034002d00410780000b802d90300454180040e00013802e80104104000d41d1620025401a18110b603021900c0d1580354400b0a44405140038500c291400180e240c00c000311a444c20200502e000d00300031a400e800002c0c2035011445492614947c100000018002400945090403550340c2e100c0c2c10f180c0c510030806055051b000362400f0700703064030200120720041d000312090303100c12548490340003000c000810a21055503c01c848a50050300b002410140648903102614000e91028000403035103403182c0d090007504407915421001d41c0714a07520700381916508403960721521001a11407545c1d00b2030032003071201c1601146c681c858881c0003040090b40b640c01c09018120280241c580b84207a0582e001c00c4c0c021201001ca040c0c0741481d005c1810650754100300036000180c4242281c100309141c80c0340005032000c010000140542004682000c01c2020312442142c4400c0415886103a42c034019010510011403481c1c0d151405240c0b4031401d90b18054a50b1641c8284a0000d4103c840b19000060b4035901500e8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 39062531 1250 39061281 39061339
    0xc031e020909031209070302030a200a0603060603140708071b050102030f0106180303200f0703120f0206010b03060d23010c0f03020909010e0a0906050405030918010305070306020a030902 82
    0xb66241684401000d17031764480103400000c0d0582d1052a0f400e011510903804904101e4101e51081c0052281001080311016075074002400700b92941018050705806024007020350a941c001c0103024174001d0300040c10345101503c03a40500001c00007508840c000f2141c9410902c2d00701001b0755490800207280d8100000c01d2042c6800642c0c07036071404181c096441c172244201c98040c0c2c0c03030341940d50503610710050283c5110a1441540f103503908a06880d4000d0142100550103980c980882100348540a8240c1060454001c2150403d10060203406264016250491000e94011280c540f4625184503462003980c0924085120904c520b07035200c46c1500400c041c560550355400004d80543c2c02a4268060701c02c1281d404940c03900140070040d26048411745c400d00014012500c0c0240d5255402240c8080e20180c9a83c2c000042260311f03401c00189908540717003514801642585103440320b946901c0c043c04004d24994001400d1012203200f904003414140d001081409104003a001600401c640d0b908 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 39063781 1250 39062531 39062557
    0x8070212040506090a0806040309050405100b041206140405030712030e0a03030e1f0204080c090606030a0507020c0a0b0c06070914010c0206070c0b0c010501090203040c031e02090903 80
    0x40409101054a8020900d4400d00ca41894182801c001442c0c01500409820290302140011070f414100301042c0118029150280704a0034002030105a540c020718000e81c1c0501000200b01800a034402c54084407042d0f40c0c00b041020883c50001c01074002c1682100c0e0120301a420710080c0322010009091443c403501042d202d0304400581a02901d40e9240b209003190850300340007012034000d4002c1c1e10120741c103c2c00d840c0000c20781010714040c4820701841c844116070208091100d05030401082003c4107084900c00ca10307141141c006a01840010404800207440b0008241c02c1d80c000c0222645640c002001c06158079102c4850500035040f03c0f1000103d4403812011454a500511101c015180c043c64403c0c140f080813401500e510092800c00c90700181c0400418000c641c038100e800d0050806455020340d560144102c5900f92001a000001d0302031042040c400060b403040f4020b82240d500c16109031011b020b0700c2584c144000340300c20107034010b1152410410b1126021008000c4060162 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 39065031 1250 39063781 39063797
    0x61e0a03050907230a0f06030c020f06010b160501180f050607030c0801090c091505091201020f2a300702090c030603030c07060c0b0c07020a030b0c0903070e0601 71
    0x1400741c580c0d5000307038400c05401480d109059503d01350300d2104c0c000c0804000d410141d8581d51054030000d012601e030301c0f20b00020758804038000304581c103100310000c103c85280205125410506151820b1182544084081091501c90010000700703400c400301100e03101031030030030034001400d200700c03015142d40c41120580a1400002c003024003910551309607012680c0c4075402d0b41e080c0000c3c00000c1540d040141c00388a0362140000c1c910000c6c4145a06c1c050495440e20348a080b06424001d0124000510707148990042c010100c00b00c0c12002507882000344500001129510b06186043e00d01000400100310302a80c11008043c8900f25101c006071030000039188006d855501c10a00b080c003600400a52000c3c480b00424a2402880041c64001030024140c03450b000c0000708940c98456140d1043c000704a4004003001030101c0e035080154002c918607603170303440d1604c154002904c0e12610b000040c80f465051001c5603140c03880740244e41c0c03008006811108030036190300808006040071244a07001801c52 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 39066281 1250 39065031 39065041
    0x1e0106120f090302060103030516051207060c02120d090f020303030f01050a0501050a051204030917061005010302190c05011503050a0c09090201080a0b030c0402040b030a060b040501020705040902061e0a0305 91
    0x42c031820b0300b5290554090044c036402c613501140e030b40c1e01c1207502e00100c4059000c1400410828000746031000d000c400d00a075071706028500107040c1c5407408078070020354002543c10741496101c282210007100815000243c059020b280100300468006400f035050710000c820804d00c0700403040900c3c141c0d0401c41f40940750664980044680740b18075070410300055814400b0310381c1454803015081e000380c406d04100e23135042d44503858415040035101d0000c915a1008052014030380842c0c418102520b020719007540f4000088240418001190f2a00e00410051907074501c01d12800b0b5000d440c2452000540c0d141c0030703a603401d25654071810f522040d80d0b010b030b0000380010600c5040c4074040707180e58180c50385000c5030346008100b0010b02c280c07000d01e40c0502528252000303e41d110710003007028010114050740c072814500c0c40311080b120700c0e8103d00c0b2401e2b41000300707100603030300000c0a2085440840e40407902140520100e882030240c180c900e81a4080c200912520910201c041d00360040980d0303040201b07540d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 39067531 1250 39066281 39066311
    0xa0f0b040515010c02060d0905100b0a0b04051002071701061403031809040f0206120103051b22180c0602150c04050f010c120905130e10051e010612 65
    0x70b40302240c8100078450808035650140d021412440c0c00181150300705421340000405841d40d62000b1240c6401c40003000c50718440c0f901c40c0342c80c07081c0c0079038000001c1420081c50402d5881036000309885076520340001848244200b006001901072a03904c016107840c05255036010b005a401000c2012501122052207402c000041d100c801e10362202c80c0c00d20300b86032402d00150300d0024006881d01c0d0444a01d820151300c2e400014500c504014050032141d42c9036040c43e6003840115003400e03401048c05a901d03a030655a070010003001110008082c0c010b204000c0240e0000d00180c050300c40901d0f000c08543e805e0141a1503444212240d90b000d46480603e41c0341b81660204080741c0184c8004424801840700c0d041455100b400d007807042c180b8045207060750300c03004070581d040171401d00000c60b0308005100f10b00700080c1d203441b4540307480380620a8619000d0b8450319150b01549000c8100e50f0b40c400201c10000c0368145284100c00070321060050750b15600010050020650300d10303003c905000d02103802c048 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 39068781 1250 39067531 39067541
    0x1002060109061a04121a04030503150d0203060c090a0509010306060828060b06040b0d0f0c140904050903161202010b1c02090a06090f0605030c030304120b0405150a0f0b04 75
    0x2945600103450b00b828070401010b80360900000395020004c1080408246d440b426201d40501d0184d1111922890300c0800440c1a020325204203005150040d5080d005840020f90290000c90f8000360301e8590641c140444d14200580e840940c0c402c46a20000040c0001da50200b002d0342ea40b81c0c25602e40c41d030908050140c580321104d106402e80608003203000414119484696440ca0061120340703096541c0310f4200f540d130000c4070244026540c3e141c81c0d030b0991074103101c1d000740810036080c008200001d0950265039130181181140c012500c2c2c2c80058480c060030320440d000c005540b030084c64401c020b0b02f0304052803003400303410402562a041a403030007480c214070058804240c1800c00009092107600748111054058107c2184645468021860624a004e4001c0c01042e540700003d04c0c0c2c0c903000030180703040c00c0c40140c0c45c0207400402c8280403220602c3c66002183d6009011010507444520f459407800203010240118418103800303101c4660580d40010309401c140c02010b100001d2400c00300030441d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 39070031 1250 39068781 39068819
    0x608010303021005040809060a0f02010e0613080c071a030f15090406020d1b020c1908070b07030203091e0f010206011809050a05011104030213020901050403080711100206010906 78
    0x6480401c5400083e400d503080660b0080c8a0b94042e8180007204022400d542c0252180201240202ca07402070900c2d42445007502c503421010040115003400384200410740d401043c00340c01042c000542c154104410050b0700c0080c0681c9078161901c40c0754002942d5150000e5a55000e40c1c07150401050f0890500380b00440d2200c1c0081c030448490302c079951740d00000d6000c1c2450001082d01c5030703d11405110700101004a10441b500941600419542048948800d49000e8003040040003018003102c10300082e200b003543d1400d4000b40c1c4c1c031101c40c1010303031541c01424407860f441412070154904c442d01c880113100c500e040581d400802140010016602c0700e009000c1c0c9561079072090003c1883c8003035500101b0520f400340742916a210036940701d160070345004549900020700d0002d410011401e00320101a0400300c0c0c0c150450411500b180000c000344510704c030141003150017080220600484041540c0b00740b00c01010403950316008078019450f203009100c2c5c582600c1c6802000500c00c240e01841300741d00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 39071281 1250 39070031 39070033
    0x90302090c1213051608100b040213060e01091a0d0606020105161404120503030f090d080105010c110d0f15060302010c02090a090b010e16030b03060402010e030102091309060501060801030302 84
    0x3da8071020403a2841440c10015a054815090440d030b40c025045039810140c10001c000d40100d4503480441d500391384040840318061403040043c0411900780710b45900a0760341074984105201d2882004a900d95400d4102c3e4241442d50382c04550203041070f0380140440141940144a11036a4100c1607007250001c6a100b0040002d0b00f0180c3e031054800d00507482c080c190382d40c0c150704083c1c84130700803603d0b280135400031102580000148008840e00c05030039640301e01c2d114024582421032450040101c08184070300c6040c0000e808241d4100300c10164064801d0001a0544007014564204903a07101c841502c01d640329000840410150040c0d4090030341940d4040c2c50b0000c10000c0c41d801d0211a40c002450a0055541c400101002600b1005035500070542e800050040307080c08141c8214100c207214001040c036203449000040d40e1004150f10b54095024281120300e4401500440e0191144100d807680c00414000b0710120104241d0000d65003078043d54040003542c2c0c0701c42041e950950203000181c05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 39072531 1250 39071281 39071317
    0xc0503060d0f06020d11070501182102210715060b0906030405010209030106060f090803130b0306040e030c070611030708091306030c0b04030317060f0f0609060406090302090c 77
    0x200d440305400d61040c43c86035400624160440300c000080700c00d201615400002c0003d000f90601a09006210001c903110f07d41e0f01e400d441076900c440c44210201e0780c42d41140028140d00001c0781c02030040c10015110090740c1220050f417041c940301e059100080c101d9000050312048083d4030418803408054074070a9210b9031070160f281c0108081508003e10456056408200140c0076840c2030050b900200070640b55650040b040328801340070030100c1d400041c0103500c181b1400f510040b911134000e080301c00c5100e1180e40e0381c6595000c14043c00800c003d41200d8403001941d1200c100002426800315105590341010003007114103040e40b2441003e0000d00081818000c0c0c4406107000219007840005030380000408941d41d540708803a404103580026540000400d0030018590000d01c1494a403d2a400309400391800000007140350f03c81c00a040d000308504520070f0a552601022034056940040550b03844940e9102e00901801190000324000c00f41480442c3c2a5000d20301680c003565202030038042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 39073781 1250 39072531 39072533
    0xc0f0207050609040f1808030609011e05011b05070305030903070b040b030f07120f1e020703021b06040801060f060e0306040510020304080d05070804030e03070e04060c030e07090209040c0503060d 86
    0x600080c5c4060007406580304215141c2d291020280d0340c096200d140010785903d003217010405c1070b08050740002c002134200100020340256074800082507810034200b4500c005110f081654207492209002401d520460a010040c44400400350409020450440300b1081d101c0f03c42c0d003181d000724030408203a5401400480e01c11070180c42c60b643c1c0051a45001c3d8084031100041400307442032006052b0886955007160b4504020500d030200d1403c0251800350319243d00c41c1d400956036038003200010445191451031803007507940d0001b2203004094400081c07103102d403507007003180e030750056407140201003044201401080d05010403a180304a8120020b8541c518001501030041e600040c0f003200c1b0000304210000403150184201405045599148480c91900d840c015006202241c81a0310941c070408080200c04c1d800c42c000703544250b02c49400301c0d100082c00e0081e4040d0031000c03a540c1082c0290358002c204861580d02030820480100c60a100010b1032840c02d4805105c25203400c0d810108011000c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 39075031 1250 39073781 39073789
    0x1080c1302030612070b13060c05060402012102040905090c18010b0703020c04020705030904060819020105160b0702061e06010c020f0f040203071101050c0a0e012604060c0f0207050609 81
    0x1030b800700b401340081e40d03100d0040784c900e4146103c0303400c02d4500d8400821000155524403100c24040d00c124184901850070035190f1030390300c001c0140001d0400841000d501c0c000d4178203200c427440e036100300c910564440703480d070301004080d010440381d8108a128144d50501207250045c0017030700302d046650103e40070703900780107000000d580854004e50941c4501800d429081e01d4502c003d100b0785014002940e01c0d1100001040291580c2c0d501c225031a44c015103001e100d4095480741c00b520300307509080a60303482c0b012808982c50050800006040c0002540c200032100303030041203441c07043d03940e0130721001c04201520742c0454030002520340c00d000490b40c104500043c208030104115014000700290b6504148c000014182d0b0b00c11540035000420365052071f140442c00740942c0341c000000c000c00302d04010010030300804441c54251018108105e1684880b100040400f0716429070005e40f462008500d89410144003038420400072030002a40b0203a0105c2903880441e004050301c00040c04c00e4900303c407a90402c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 39076281 1250 39075031 39075037
    0x1e090105060f01080c040f14011e080a02090a030c0b0703020f150115030905011a0a080f0c0108061801091b170403030f020903030c0c090702031309051b031503010501080c1302 77
    0x8508629801c000111f51810702c02241d100400002980041b252141000104841c0c42001d02100300704100d08030b184003d800c405820f40c04440140c0040c0c468030b860b0000b0309a64101e5001804c80c04200001003011040f03000100038a40c00394088840c94540d0281090b65400c40a04074541448c805005000c42620221403126441c0c0a2402150714481515280c0c2101c00c0f5131a04e8554074000034041c104c0741010f894030001416414050104100d40410003070f01c2c1d0031502e01d0581003112a40001d80503698481f105c1e01c070004040300c0f41a1943c3c550121000400d0010083c2d440c00090000c0d0f02d070900d00c00c1c04c030001031028404415450b9212680d05070090002c5e801344c002001c0c2c09200c030140540f020006400c00360050002400001c084c18140400b0150191816007150410000441c411b1808944402120100000092943d880d003611403100c0a0741e003c134101c1c041001090268a1052800c0c1c00030f1294101d008100030399a442c00141e0314003441c072031b0340c1d00012a03682c084c00c2c1443d15409 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 39077531 1250 39076281 39076291
    0x50a0210031410081608060606070305041805011805060325050d110a06050915070f0609060f050a0209030c130b06030c0301030510090206090d030905091e090105060f0108 75
    0x80425040b18014079145070042c1202e100e030710003108078010070410742e042140070409104240b40030f801a042000e8107443e0b01d4014074003401507200150880400d03109804030340081ca03d141482400b81503400c5100c014040a104550400d40c8a1503042c2e01c807802031280b50700424000700200000140030f5900804080c4480c200e01000c83c842500040503110080c400c1d4903144218859020890a030741041800452504000704120b024454031840381c440913030031224100f15600d540d8072080d140c50b1114241035031340790040001c1e051522441c10032500380c00900c2c01c0e070064130301440f0740d0f6100f8a88000700d004124004e58107500140d165012414554140050f11000300c00110b59941d0400102c0c4c9a5171003a40c840c40a0140080108240101441001d40071081c0800030f00c030020542e00002c55a00a0140345c0c4d00c0b8240d9029400101401104071000500019000201c51728021081c9540c4507145450390b8100491480056445072040c80b520f40b18440007402d401113040c000004442c41900184 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 39078781 1250 39077531 39077537
    0x30f04020d0803010b0a020609061506030405010e030409050402030c010e0a061103090d03081905010302090f1801091b05010c15110c0105090c01030c361802030702010b010507050a0210 81
    0x4041c0452000e00040d80600811066190348018084000b80b51801c01800c600503504580240080441c800d014100941c1003111050b80703d0f107071810000d0041403000300003130341e03031100040c0054a0301c0b4a80015100c0c1f030088060724a14075003a0011b42d0144004600203502881c9042c06002c04c43c014a0200d030007003426001c0301e0800f403080020403820b4004004c198049004a010440040209480706400500190007440305515503030204482c8900a0840072011200800280d44900b0017100f07604905002c01c02804035009030b00344078a11842041d1001c0c1514504400442e0340c0d40030b121601c2019a104050500c10307400e81c40074030b00504050a400b01881820000d40203220000d0040328001d0310000e004d000900384400015089481d000c4068080c0100500b201002202003602039a400d603144098540554201e80c2c075a03c0392040c0d40051510010790030a00004002c180e000e1403040d10f841d0004c000c1c1c0e04a203001540d440c02254002403180d03010300d40801c01410000520007034455a81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 39080031 1250 39078781 39078799
    0x3020c0919060803031506040312050706090b04110108070f0503011206060506030c0c0d1407060b01110a0602030a0c0c0c1703040308030a090501050f0c0d11070b07120501060311030f0402 82
    0xc88001542c802c0ea0000589074008401c0c07001ca002d50301da1803a603c030030881e640752600c0c0c510340e0340321000007003820000103008000c13039a00144100c9400548455038868500f81c3d03d403400e494540b800c803020300202c0c1e002500c81c000140d405401020364030341104117511598116843d000d440441e031121140219030b0070703440300000166510b42c18041d5010b84042c0310125110903403020045c0c1f50070a0008420200301c2c0b5154010301d910b6848084804d51900702c00041000080000142c0e9107926012803805284219412003051203090ba016500400c03446200b8010107040d03600444951b00104005819054100d00421202c280c4901e10003c0c280c032042500d080a94031340300d010880d041100c45500098480340079204018081c801e5940c0300c60401584005400c203248880b0850160210800d503c035070319075607181c464400c02e0554500360b90007000954945456140282a41640140d0312501030501c400480c00c10b003c0e0203aa4554408001140d046135910147c0a4a2890180c020380c0c110f0074503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 39081281 1250 39080031 39080071
    0xf051e090307080a02030415170403080907080d0e0a120309061d04060b0c0c04091e0501060503030f04050901120b042d03020102030601020706030203090601090203190509011a010201020703020c09 86
    0x40010f021881105d40186498a184c82030001c42100745284010410075500c04501d0011207041e111034001d038143c41d003902c81c0e68940f003040f45400c0098001c80c00d50300c00d0203481264254030080036060b52406544030000d00d50b84501040003010b40c0000240490a52682400040c3c85201008440d202c0c800b40d46070300342003e00110341121015007102407400b800081e105400601041154a0050b040d14100101c10180d00c80040c5c005051150f411140c10122502042c01425003251000e044010f0550380da46d443c001044140f0750280c80350138081e0281d400000380f0900d0032340c4045151600a450300b603803591141d81e944003039041400c580000c2411000311034400d1300c5e24090295428400d400051303070b07810500c001a2501403940d200c40c041500400c10000c4012010501504403142c4203000750f166100d030304002c02055141c400101d5a42d2a00303040003140d09054000c880014aa003021104c20448440124281c1c4030b1001c01401591018583d0a043d08111102941c13000c402c04001070b40c0045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 39082531 1250 39081281 39081293
    0x102070e04050a142109040204050405010909060e06040f030503060109170601030c0503070602070308090f130204050a0e0609150a050d03050306040f09030c03030903050706050106050703030f051e090307 89
    0xe440c207492a07800381494801300007410500704c2d45a00e541004000c2c00c9203044800c04556007001c18525801c0b40821204440e49035901035401400000300203002c00d41c0c40d080510b0041030003150580349a400d1100140c041c250200e405400f850708540300454103030b080e0710300b520941d1025024504110a500000030003100504000102c0411341020f84001c0d495410f02c802440000d03001300b80309400c60300081081540010f01c0d58201e0303500440e0f0039140c1c01c40000096a04080310b06442d040400050808046c2505a00078000c0d0340381180c0d40d28070540c42d1450b0b9501d41c0780484040d60041d41c04008104562004000150850340051031000f4440d10f07400071500e611050001200420004400e2244c1c80c074240c01030252500000004000b81d1000e80c400070181105200040c00b81665070f411001030520440840c4d5205401540500c02546c0d10800181203900c25841030300003d00e00800082090042d02a0703a0295040d00001600e4000d005408050560094809241c0380320400c01603000400d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 39083781 1250 39082531 39082559
    0x40203090a030f03060807060c05070b0703050c06010f05210a02030f010204170c060f130b1209010f0608100c0509180403080a141b090406031101090e0f0f06010207 72
    0x203000806030007420103500d00074000c0c400d40c00320341007414104403040c0301807000081c0c0b08040310428546184415500c0c00d0a6040101c90b801900590340d0000d1104185070f00800106161807804045411a07a600c1d00c00032500c0e40d030740c052598400c5041610400c0110321000c84461003011100790b0b00700c0e211076800280340c2401180580e9040e50049000c120203810010850031014040c4007400c0c3c3e4005210020f9800e00c035034680d41d0900c21000c10303c2d00c00071407401c1c4001c4c064234025101c5550b4400300c0703684802c42c0100300c030300e031400b5030030644002e9004801c2d0058030111803c1b40300400c42e40300c21708101d5020380301c04039030182044410300607410580d03207030443c031501d50881299220303d500f09411300519414000f029290841d0502c801c66003c0c540700202c403580414600c40c1c0b44940c1048160741562440760940c40303607126003031405c00b009000b8445050004a4001d8072980c03006540d42c031854645d0300e4202c0d68006103095881c0003c18031034906d2800f50740410140305480b03255894900c0e02c19049 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 39085031 1250 39083781 39083791
    0xe040c21050126030d0221070201060314030a020c040e1f05010f060c030801050108041e0506010905100303090e04020d08070605061e0f010c03020f0f16050105030402280302040203 79
    0x603072180010803c4505140110303a0182095040c3c09280d00300b0209140d0340e1140c01c0d00031041d660300056400c41d09003601202d0b50000181c06842ca101d080c40c48000740a414180000d40701000701c0102c44101013000030840e801c01800750064200320b681c010800c4014003200c0b001c0d407014003462172079801112817402104141c0480000004140d414403084c9080e40925403c00c10510414601d540d020070f4220310b0085c111202443d01107160781e62480e00700b82c80b02c02941c0110300c040c1440e040c07004104010030041e0588607000c004010b141c0d81c4401030740d5100c440d4440600400c0c2900001d100d0382c94480169070340903001500341c1d21803000c00e58448144d13038000d05040d1140d136502c1c424841c1611b80415100c6a03200d1201c07003e509045000001040440b494030158180100b081804007014000d000801310804c0394000d903821803101e142600e8541c04d060301d116102c544141c00114043d07024400362409150007503c050742a034040f141c514545469910700840040040e800080140d4881c00154820 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 39086281 1250 39085031 39085097
    0x3010603140606040203070915090308030702010c0e01050f0f0310120b090c06040b0a080612010f090c1205060c07060e03070c06080609010302010e0f0604050d0c1707060e040c 77
    0x200030a4031200e03041120251945104d03030300401c1440211070707206030340074240e038146010819040350380f02c010703600904964001081390502104005403550107501ca00c0c8000a40c0d100d140d01062301100444c0e080c40f468009845d221010f2280c0c2c0c14051304c0e0400380d540516402c038201c0801d5111903500840c0840300e0411940d03111004104807050030300703008101004d8001e44991741480d0030050b401c0c3c414051116030108214100c0c00240709591174034518a14500b000700204403014242c1c0e64040070300140340003556404103040e0002460a6003141c0707a18141d0304903018101c070392980304000b14942c0c0804820740b880c40d03d80b030000094083c184002c015461040101000280c941440070b402c0002c02485544907036881c000420140c2d800140a800b99001100d040c0ea01d900340341c00040c0c0c070f8010364002541111046445100300410b0076441000d90360f5010f912a00507d00780319031540d8540785c2c011103000440304914004c0d242415088299008002d003010350310001c0755064441a50743c2c1007078211103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 39087531 1250 39086281 39086303
    0x10909031403060307270603120905030a0209011e08060106090e0109090210050a0c060f0c030b12190804090203070305070905040c0206040b0a06080a0506040204061715090c03010603 80
    0x10590080d40e4055912440d0034442e0551509100181d224041440340300d514040325200c2000210410001c4103c0000011b0100250340d12400d04d004204c01e0002d24101082040030041240e1070001031036040303680d00070304000b816030030501e44a02111620005c0e40e802c00c0c00f414003044003802072210700c2c081c004940c1c501001c3c40c0b40100000e120201a80000a80380c40c0400b00b4000d6190210301006581c2c0c28202280d0341c60714640d0880f214040c0c0580540401d00c1c0032022000110290802c145049107658180079050704001000b04440c011389840366903a0000c00400c1c542420000c0c04100c1b180100c2c0c509040c540d40711341c03001c140d9104841500001c0e607140c0400040d03640096040000c0d00060b41c040000084140029644560103000503000c0f040c1600026016240f80e0480700103002484165541d4680070719105990390800c0e9000c03407185083c102c0100364644603071a04403540ca4100010400c00303c00201d202400040600503030710500462006110b140c40900852009502c030b4400703288 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 39088781 1250 39087531 39087533
    0x150d050f0c010e060304210207050a1701050f060901030b0402040f020c0c030607050f041e0b0712111204140f03061317040b25170301170f0d0c0501090b010909 70
    0x4100f0144100c52042c0300a109000c041810841d00040c00c0e1100e03032600e002103507040c4080e8030301401a03100381d605c10801400803030345448241150401c09089002844141c5903902f9424520314221405074011700f2490040020401c0904056000703030028100040900300c00c02d601c2c043c3d9100c01c10089982d1f00c0241000007505040182a501c06c210f803600e40d0414094083c8034125200b01e114088098400c00048a1080d200003c401d00810350705190590b07805c0035160084485414400b410003080c0d83d400da410803080d02096080031240c0b451501442c060401c03c0440310510210421600541d0920117030507582c030308025941c065400320200e841d416110385440c2003461015030313100e12a024180301c200014a00e842c2075038405904224a1054200c0c1a0001c00c03600d20004005071800b00007101c584820340c0c40d0b034015416128607240c5946029244c0c90740c240e441c0f004030001c881985c0440d4504850704d216003026203030f2510520002c070b504041c3d611050401c4e1001e0f00001a12039031000004c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 39090031 1250 39088781 39088787
    0x3150904031b080a020f1501090c050d0606030e0d020706020607050a0c0b04031d040b030601050d020111031c060b130306020c0102090402211003030f0f11010903090305060604020f03150d050f0c01 86
    0x10720010b1606c00070008490036038031a1b41201818407a100707a2944403034030402000c1c081e00c180e40c0424105281005041c0da1100c000700034001a15503400e0a01a60405814141c8041944410f4401c0c90300144820f8440100c11201503020b42a6003003040041c0d45010006104660030724000c9000f40c3da13140395802d401d40501c01c504400d0315020702c51440c2900b0710f444c9481c0822401c0c1114000c540c00301c21980c0c07500050304c8001812004a4080c08001100240c1c04901d190101345042280c0e800c0000399101c40382c9500c140b10b40345070389200961020b41000040c034103800401707116080c03d00250070104400301040c20b03078020580c10b0b90714404803ca010740c00004214081e5010780c104021003062482c44e103000d0400d40b96280c0c51420495a5207041c1b030703814068100041001d0304040208400222130a000f40750300800c0c0000c0f20b080c0200d00110303030913141500940b03040c0340c12a40014038585600701000314100d41c241c3c0311343c0c0000c410010300c00805c4043c0185a00c95a0f01c0b03024160030305960b4001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 39091281 1250 39090031 39090043
    0x100501060909020405030a141603030305041101030e0606040902040e0709050105120c1003020307030207020a060e090a0608030a1b0f08030a05010e01120201031a061b0f0303150904031b080a02 84
    0x6080b0141c070612082086540001c1d0010350240c01c140900c501c2624001c3e100d08041d80e4005118803417185e607100008050345a441340d032256001700100d500d207803103440044042d2002c0c0700d440d174002ea00100104040c2e20302940010070385031006100040921303041110f58203002c000e074029201c3c1c50365a801040740e810081c071a221f85d503000f0030207050041d1268000075000920602d4032070803da408070000e1001c0c2d010342d04550000d600105645481340c0e90f01c000418803c4035006060040040d48003080c0081c10750301400c0140d500e07401c0a18241062a84100c40c1c16000303020340100518039000318400302e190030320203e1803207000c1d420b2a40d480c03421403081415540306920100c010750000d001008402e04010382801c50660918001c2060170035541021090007899008542c070100001d040c80c15009031603000d02c912800ca4091380d050426100d4803640303a0104454044200a400c450b03125103181c2040b150364403a2283c28451444604a21181510100d00740e00b19000d4000040701010b164040100d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 39092531 1250 39091281 39091289
    0x6091608010b090106050f0c01020d0504031206080c01110304030b0901090203120c03030105041a090f06030d0903020607020108070908060103060b09061c0809030a0803090102040306150b030f181005010609 90
    0x30b000301d00604000c100c003e5814402d0b4400c000000c42d4040748102084200d410b041a00c070001e6407590007203110b0760000d040030b035030840c003240461103074040007032040c01001d04a07052100605039a18800d001511a0507000020078120300040001000003242181120302030010140000764840c5c2c244141490b1008604100c84551414021000c1c0301200000b182e040d0b03003050310042080c009042d0000301d4090340c05006944070445208001c4c070180c12240144c4111030403812104845c040c1001075408454502003e500b140c4100004030140d40200510f07074001c1e10501e0030b56925a83c0388111820700c01c0a80045031503d03240c409038a1140b504001c01c507009002280c4042e82da8622030f010110b075840840c001490484041210000c03940e040c08070200075a004100e4959a1520350300140c000d50050004891070342c0341407201724103034030030040390416220380c4110240f45858403840207491102c020803080c40020348400c2800c005505210749405044000d102089550401302c000d003541c0c8040d08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 39093781 1250 39092531 39092533
    0x60203090109050705011d040b0d060203090105150a05030a110d0506040302030408010f0c1209020301061206050a05070f080a050619030305130b16030804080906030f01081203070903030e030f06091608 88
    0x840b45155002c87c050b216001411500015201303034000224000c2c04001e034018142c00e101008001c0115419000140304400700a407010040326054100719100d8035500850b501644141c4048000440d8120074103a10705000700b50b0540640380340d03141c03440c00104484c1100180c2011508102104d024090503540c60013020041c0181d174100e6800802e0300c9803030700420811580720403900c000c2d1345081d40000040c1c40c1c5040303c2c3c00480c140f810150083c1c0360650399041c010340b034600043d0b15103101d030b560151a09030300d0786d41d0318180d159004103401401000c0d0000394401983c01e8960007140761100c5400056100c1e4a502d91191107028400c01c15400c15400b080ca103505c100909405080c900c0410b511865040c1007a0489440300d04010101c1c2c01003c01c0c035500840c0010038842d42500c0786031158102d9052a0032103410403108081e03088a4041a520302e00480e008510510000e4020840c4400691016003140d61001c1c112010600e00a03084e00e0000c0645c2080c0002108510041d4459000d000380c14 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 39095031 1250 39093781 39093797
    0xc050405090403081b0a030e07090504030c021207090f09050f07030803061306080102040605071202030f09120a02031501050102010b0102031c050601090b071217040b0411010c06020309010905070501 87
    0x4004208507940040000302008000c00c0091007a034044240030b400400300c500d255032030b10748039440540109900d4144032040c5c402c00100054007174a60059602c0382c1ea0594a41141407080d0742030008014000100b0740c110b008101c004a2504101e01c14003000070058400416005500d0070542e041070150f004c0c0b40c105410015040c00454020310485c1c0d080403045d121503400c40b2265144000501c040e4001000950001400086243d880300140044074005d075118801205481d20580c1d41e485903190b0380c1d020034000d2042d600300380790849088003104496015074102d052154000303414904c0d0030814985c034042400060000c0d580c24031400b50a407800307000441c03030b240d83c030404a404001c50740b0070500090f86400000d03d10ba4404c031302c0440200000d1000544900e04c0c0c0c0741109418040c0240440040c0c050300354510034050001c49613010f40d4208260311400d80f240e8035462481d4030748508050502c52100400c0e00040c60501c020351040f01c480c000040c2078060b91600350b0410b14140c0c02103041003650 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 39096281 1250 39095031 39095039
    0xe0a020102150705090307172b050f071e050105010506162009010b190503060609040e190501150501020a0302030a032d050f07110c01050f04050306090a060c0504 71
    0x6018100d00704000710500d00f0354500c042100e5900c10400302035058090840002400381c410069600300754075003010ba80c80407000e20502d034550503005041408401580800220060190b001003212410041a441c41c0c40410b483c2e8140000400c031031007501018803819030080c403c0c01e2240c14090441119107a241285c2d014500300c0d04602020050400d5600c402c0307c00c4401840c402c00b01e0a0300c1d0180c8007031015a50340034105a00d400500380840c840e2a4540c8030102280f02d2403c880c8139041c010310703c40c2003281c2c0300b051100808104504c0b044622a0205282c01d42e5000702c4140841880740e000401c001403050000b0b410103446522180c150f40c00740c0d24540000f0703008026115100e02902d4006803009030142e40c074440c0e2802d100300840001c8403840890005a5a400c070a00c00c0e41382c40f1001c1206d441d07a0307804590354103c4c0300305070b14150845800ca4080d584144001c0c4208140c80d030245050075110b1001908100d82900c400b401c0303600c980b019a08000c0b40f4050041e55900600b04103007010301d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 39097531 1250 39096281 39096283
    0x1030b01020c040e0a21020705010806090f090708010e030a030f05060d080f0906070c06020105100b0a1b1a0f01090b0a0603020714060106031d010519050606040b0a0302040501030e0a020102 83
    0x208105182c0f281e611000a03440c000001c1000c2d0000030b4100d05800394120301c000110b442440c0a50306880140981300c004500c2d075000b80401402400050b008880583d19440c0b0980c0c9420084e204855900845ca00003c00407030900030303d01d42455a9014550b9012240340160440e5203d00303461058a05140c100310540d900c82e04c1d402c0605802c06101540e0311401c1c080c09a90f1302c55180c075150300c0040821100c00340300c1802c8100c02524840d4000b00070039242c008210b04200641c0c0318080100000b0041596203500c64689250304a440c3c00c2d00010345456a500e5071a6100549a0100c032440d9207010401030442c0185d02900501d004a010880a010100424000235140c0200c0048c16000035100040102150958003510080340517540e580d6141c00e4000d000e00f001c900310785080151014411306103131048c45042d000307095129491810808100021011741002080c0b40d501c0070040c0310008035090820001e001c2000150f070b0050303885041030000f5003100c8041500d15600d6104941c580c0050360 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 39098781 1250 39097531 39097543
    0x4090b042a090801110d020702180703061a160206090f03030c2b0c020f010e04180303050a0218040504030512010602070602160b0306330702030d05090117060d0803160e01030b0102 79
    0x31b1024003580d155514004620789070114044611400f40d2401080300d0079500d41d01c000107a030103400700b0388594050f05501e107850740119008072018001d404480001450940000c0120350030140c440502c5022040029056410440480d41245c100c40c400d52044041922610111582c540700c1c0c018441b000c403001410007054040007801030780d00d03501d02c940b540e004a52251101400410503c40c6010b0703075594440c10b50720500128003007400e050201300440682e009481c0480549000041d5600c13075601040060035001d8410740600c0010443c0d0000701c0c07038411038030340600503940007440e5103490444001e00d032820388107604011800340c3e002444502c001e941101c4d00054102c4e0301501c200c019950100000340245440d6a800d54070040c1c03154000e000b8000b81c8500f6000f20240c500500c005902551144035104940d8000782c5404a04080290601c0c070740794000c01d001c0d0804003035042c1651000d410354800c2d1142c048041c448807011101a41c081500025035a00f0f04e020b2000c000c191002030b41d606 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 39100031 1250 39098781 39098797
    0xc220608070b0d0c030204120f020901081b090612010c110c03150a0509010b0301020408070305070905040f02121606080402091b0a1409060d0617011104090b042a09080111 75
    0x75292132a4031079252003501510080d16000020320544602480c002c00085414a0124050340d6400000581c41c900400c1c500e0381c00010308581c5081454000800c41c6100b8002e01c2c103503106406130b0303209510b500d00f407180d000c4001d07454403600030070455500c01500e00b11191034418844d038042c1060500c03076080540b015070000b820080c0400c02d92140300103035025010300a81260150b101040024400c00c00007040011a070107901902c0360a0f032103034802000d54030102d50203040300ca406035040c0c0c0182401032280f203036001103005590312100c0030031080c990a41181d00520014184805100c2585054242141c1045641d46070003005d2808510016080c050748100c00240054900f500e43c110180000b195203200d0000c2c599680c40b22410303500c0380140b045014400005203185030728000d0780c8051160700b00c0c01e5241100c81c0d082c80d00d0004404064205074140c184c200751281049e800c048460311580114803c80a1092100414000000c0c000046507200880d50303810318020500e640380080c2211a00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 39101281 1250 39100031 39100057
    0x807060518030c1504140d0f02010e01021002040e01030c0602011404030e01170405150108070f050d110d060b030606032b05071a07142a0c220608070b 66
    0x1d007000400080c10b04180804050300410404020002104800300a00039a8003150012104007141003c0c03001c60300035403800a01044015104e840558010541111840014411984e000c0754810041003a0b8210790b1045904522560060003008090400c0c00e021306a9403008004014400790020151540640054140300d08862141c0c1ba5903c9606040e41041d0000c803104960f007050320b04541e9035844518106071240503d030020456000101d1003801302c034041c0009200580c1004200400c201c0004003c8809400e00c10b034091503034454281c20b101c0e16004080002d0450060814075080c060000c11051090304443c221040804026400300c1488801d85008000e05000620036a018840c400016120362070040d0108074124180302d00030300c15541c6da9518406006640001e41040c0a801c6210700303860203040522403c0b40d4012018048103801c403084030f444510b4000850503031400160141d4032941200c0255070400c403140581c1c802098158014009646082c900c070400e8010041c41a105c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 39102531 1250 39101281 39101317
    0x204051303080f1008030a0512060904080406080a0204050a06080a05071b030c050307021f090803030f060105090d020901080a03091502060c030403030e1608010c030506010f0f050409020406090302090108070605 92
    0x49000000002c025104490480740e80e40c07c52a0080c009800914005050442c00000500541061102c80340180e600080c81e604060400345c05450f43d0500602041145a081c4000251a520102d004c40100469203506401c0c0c24140800d2040e544000d103c0345c14400322038948081c0f0048002612209034044c940440c82101034640a415407040d010f01075402070f04007038141302e9103a000b2808800044d0396100e0b030a00c940e44074407850300c9000841e070b6400c1a54205000482d554000c4000b02840c04008010701245582940022644030080c0c2101c211a0b100300c1000041607002030071034003d421900c0f0300c90440141080020341c0d400340204101b0080b1000300129041501a40113403001d10a1482036400e041902c09400344040760300e100e510758a42c01c20110312445e50003441454029401070f5200d1440758084181079802c1e000b040041743c1000b00401c0000360b045c90a01c00b4001920095481004207495801040225003040e002029a0b810034a800c008983e00141180d00220261344800c034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 39103781 1250 39102531 39102541
    0x4090c06050901031509020a020d0309030c060908120103031d010903021309140102070506041106090d0803070507050709050103140303090703032001140a0e0a031205041b0b070204051303080f 84
    0x80600340b04034000c100c05d6991440454074244035006082103405581c2203402c0451040c00c1101618040a03014001c24140f84891000c640e040c0c000c0460070307020301801444c011002c804080044000d0380150300080e8465880705040d05a42c1610040940903c1c0540c411811070700000c0c030407406454a01a400d90301c3c0d1400007004850511003e25084903070003191642c8060401ea5294102141c085a81e6018400c05501500e8000117480d00540d01078015903440130309540344100c560000d410102440300501c880000035408011001c05405141d0021400f54554030b40303580910b40285a201c001d030400e000300f00350390100041d001c0450b40c241c5041102c0445a01d00030111000b141741c0301c0665420a002d041d032440f07005051a00806010004002900480c8899030315009001d038020005040c4800f00c000003400da40145801c41e0080e8604064a546103404603000e0642d81d0005428170004100b80b070943c50907105003940480180855000c2181c1aa4000d01d00c280082c1800302007601c40010030303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 39105031 1250 39103781 39103787
    0xa0b061c021e0403080306030c01080f070f05090409050109020f04020a1202090112060801090b06030303060a180b0d030206010806070512060d0521270117090c0901030b0403020c04090c06050901 85
    0x5402c0040b81c0744800c0d551601c07802c045400398021507589010b4411100d80003019403084200902c610b1310f5118021480d100e202c811200345a010280718100301e000e000c1e4002540d20382c4516980c0910610000071100c01620501c1030025420440320b00c91803040c400c5030315854104813000422500f42800682d15001c100050b035500c2101808001032514041c00401d0140056001e80a0709010390144181035407001d0426641c0d02c000c640303440d0040e07144174040180d40080009805000398060300482c10341400e0700814142d4403486001c0c0c00590003c40108040303c0c040c80740340e40040c2e461500b5450582c040c1c1d41150064005400c490255042c84190300500c0014086400320300d01c1a0110b0954020a80214060b03422140d209240f40700d403018103c401c14101c2c05040300c2000180c561152680c0c980c0d00403282020000d1230400c06010b81407082000340d030b038898000d001c2e510aa0ba560040d04060800a24000000300d0460150740790464071001318480080c90422680540307011981d0b000e0380f60040f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 39106281 1250 39105031 39105067
    0xc03161809020d050601020c030d0905190909050a0b1003050606010c210908070b040e060d050a06020304030f030c1805130e1b040e070608040b0a0615080a0b061c02 72
    0xd14141e20202c0d140b01e00c3e0b0010f07000903004900036800c031160070398031904254450a00544090120740001d03408c010710b0801408252088101803022961140c1e40d02c240800c2d600d5034078003210b103a007202e0043d01c1044519000c03181c000d01051002c682081c01e40e5515030b607400303001e01418107004140301041c04202c49110101e80100d03145501d034820761410a0040c00c2030030301d40980c0c800c6002d40e09021441d0800c42050b6021900c49400040580c2c6a820501c1030100c40c1a0007038445001e1303081b640c00428040d0009501851203a5a030b0b0803201001d2900404a4a0401d100400c0102d081140e1000e8040d10040318262541164641d650149047c2c041e0003d0881d50540200d90046201c80180b409151007280c440c00c0d02560706108511540084a44440c214002d102c0031801020105000c1100c3c22101a44800000b90000758542c50b401030080c21031400d0b5082c40004e61810800c007001955000d0246240e00940300c090500410640f20300303148a03041a007681c0d8a602060a0140c04004000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 39107531 1250 39106281 39106289
    0x60a18020d030e010f0c030e04050a15031b1401020a02042a020a050f1c050c102c0c0d0609060b1207030303060b0301060509010509010918140c031618 66
    0xc0d0841003040c0c2d00d00503194400c00c590072030104072058440c40046004030300c0510342c554507580b1080d40c240501c041100624024101d080019078070600c070240038003127400000144d40070320b224040c0c4075131480c2d500152000c9a00301421707049440e2035000d230690300084c03070848159044902045004462059410070f40b480003d18641d004540e00c029035a54003c51001c43c0702d80680b06441008896500d01950f4000b0003a0040c0c040301d0500412079828070400c00781500100302d4055889580c000c4065405a0b4803101404510200c00c2e000804050384004901c00741428240140010902c2040003640703523041401c01404181d161841d4004000c115031104c100444010500b42802106070109a035031030803400120017091500c800810b2040b000340589040703c1d9981c4c1c0b0249095144001160680c01c150f40e044e046c02918040442c0040d00e4000c0212090441d01c800642071040c80ca04044510024250b000000310420a00405040c000001c0202148a00700800741c80c1c07080754100924411540 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 39108781 1250 39107531 39107539
    0x11070809012a02040b0603040203070519081b030c01020604050c0d02040e0304030506100e0c1903020d05090d02241b04030614060a06080f01030b090304080709020a0f11060a1802 78
    0xd00a1080d4000e071603144014002c3ea4101700100e908001d0141e5407009440181d416441030030104681d180032060511749400d04d581314401c05a032a01d03940e02e0b0603822044125541c2c0345e41c2010305d10b41801c20003e012000c00f440140b50606080d00c42c0f944454050301c02c103000c1c40c0317800c02d40d0055407500d03000340f9410310445040700d0b5101e0380c0e401d041d9202c01c0156142741031010300c01c40c0028808500342c04a8050300a1202c43c0e481c04401d45900b45442801000400c2071640034800c00075860482d20404c0c2c49502040040d000d078440010307001703040a030408038800c071081401c00326800356820094940c2e401024450001c40b200b01d25004c00c90540500e52004040750b041405000010412150f0903008020903641a01e1060301c8510544000204460b585448140d60300104003180358482a1130b00100c400d030950f80340544030060681001c0c03094200c003007059000520704030402ea100c86403920814991030300155411803111a0f58441c48003401c00000c050304d0b8140d256012110140039186e582e4018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 39110031 1250 39108781 39108827
    0x8060109020d050c040315231303090807060509040c1103030705070203060a0623040615020703050c040e031215040218010f0e010f08040f020d03170105041107080901 73
    0xa1090042e5004000510000781450041a0a03000150031703078003602d074010004070802d0303405d0240380c00070038800c458148025106040c240032080101d1a26000e0301c030b80200050349404504000e4880240d42c2e009850a51002e402000381d15440820350705540d2003110081903418a00d5811244400c0ea62200700320342c0400002d000300c05810000801a00340300380c0581d20075640710003254048810a1240b402022205c40141001d803180203649005818014000640d55888d0100341442500712080c00025034092003042c002d01000700525419914125810f000903003051022a84901031704d034210300300035a80c0340419180f595038034031003c034228007030811915000086822092000d0907203400740410080c103010b00b00c540c07240ea9091443d00042c0c540009261004034101d40080e0004c2041d00c480d6251130034000180d440040d549550307030107656462080b101c00d0140c0405802c061f481544641d1a0031207518a4010107030035150410741092031580c942c207103040145e401c10840340c0029400e2243e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 39111281 1250 39110031 39110039
    0xe0607080a090911030601090306020c0a0b0916170d050307030f0507050405010f0201061a070501020910170903070b01180f0f231005041808180108090616050a020304080601 76
    0x348405080700c0f46060284100860f03c2162482c0c2e1105550b014001100900300340003164058004000d000e800300300b02d0300800319a8840d03910310b0a082d01c0c1c0351104d07040980b00301c4034101d1140c0050054100300c4184480341c260003401941c1d40890f040901d00348000400040c42150107503000b1102c2c840c82c07180c140014a0401d60040042c1d100d405103902003020f4140316106036205100b180c09a6040141500922400031091a4580c000a0007100c030341d9002c1100144507120b0f00c092401d00f8006848103a1241c04000e07022203001c01c01840300320654000d024a4000c0351000c1c44050449011150404001c0417004220002d401181d0381640e109090154082507820f455009068010342d01d03210410780c00c1e02000304003001d1016280803480740303291031045c0001d01c1e144e8044101240d02c0c2032415845841642e500400e900411801040c0d841002e40415865070040c1031160300210184c09040b003031074403101483c21100e0105c04003040100200b500ca81a60081084801a1076030108403082e0b5a9a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 39112531 1250 39111281 39111287
    0x90e3d0602060601030c050c0703020f04060302030712050106120b0703050a0e0a14010c031a040b01030209090108011b051c090201050c01021318020403030503010e06040b040c050c010b010206160e0607080a 90
    0x3c0c0d506900107443e054804030b09521030029150341c100ca11015000c806d2071034080101c40d9000315030151b40b01da07680310f000005070307020000c800050150400810f098195801c050382100e11a5010b1814814000803100c00111000441584101c0506000443d1b880c1e0181400040043d191100c8952244d003524070140720800d2210440000b01d0002405014940c2c0800c40c260741105c110300907201e115050b82080d915064100c40d210140c180741c010b0801a1200000d030800740c1c203074441c0c80d46943d20350700040c20b505c2c0d0070a07040c080c0f031481c24541d1421541580000d01000b0384103ca0107269a02d800800c11a8842e4040350b41c00c00500009544a503850f06040383d40c080b103881031408180d24000c7c14018444580241d4007140d801d600c51604580c40c1001062901400410711603016030b84106001d505d07502d511429a510714030340e890340d8440d02c0400318079086480c2c40a609040d944541c0800c2a04000440310341c0004d4110714080c0b2003904030101284c1c43c4c3c01903070f1000300390a401254800030168 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 39113781 1250 39112531 39112543
    0x603030201050a0f0c0c081c09030921020603060418060c050406090f06020304260102040608060306130c17010b0904060509060a0509030313030203120a020406090e3d0602 75
    0x2100c0d042200040c0b05130380c102111070a02c0d0782c6000c00c40c0c0300a2100410610b00280c818044008042209802140c0c038a03c1203886541049021443c042410300c2010481c2e0702251019804d4202240401c0b51900002c402e804000c045134486d03512a894072682241214140440d10303400542481403c40c0300354094045e030041d01460340040c06c5043c001481804d00200001180c2e841e80246107800c1c1400f003000400b140c181e2032100307040030500700342072000350034401440100300b51784d1402d0301030a2004c10103082010241003203941d503015a541c0b401280c000711300542210942915421240d0741ea1925a0150101e0506264000080d0081000740701868100f14424056042a10751035a0b400840500f20b681c04e8038000100c0c1e00c1400001c42c0900d103c00c03080c0e2070381c5c02801200d041410b4207102ca0301c0100211044a4002c1c7c0101d03040080c5030300b180605010b800e14004208042c038218204810410b101c2c03a8400720150b1140b032a4405a50b01840003090500300d048808805880b810065a182 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 39115031 1250 39113781 39113791
    0xa060204050f030105010e04020603040c170a03080601030b100e040902180403021c0f0804020604050607060608070b27060405060304050d020607080f0708060102030c0304081027060f0b04060303020105 88
    0x44240b0b500d100d00c0c044c400c0c3c038140c03041841502d0081d01d031902807001c250002070080341e202900d01008185c4006105540020030107582c010f20401c0b0440c03400800f00754000d45014145030030420010415651012044a41001807410071410019800041d000d0320345130314040c0d000303803d040f01c400500d811581c1c414401c900076001c0700c518a511070750003c0c16520203c03086001a1f0780400301c10000f84503110b10782d00640010446400c1c1521240003510f590710002003183c08990301c1800b002981e00501c010303001030400c2c11005090050741d042500003242c4112090205000d94030004a1540e04e20050303901410f0050318080e1245060303d0996620700c4121460b00140c4500b42c00a500d1070b1103640700d14841d03041d0441c00160307625000030a54000c0c03030103088681136000600603016000f02c104050402082000c0c010601898031024402c102c4000509010700b840c0042500424030000413483d20803550301034000a501030309003000000502e200452250b11600340a0700200b07140d815000b0314020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 39116281 1250 39115031 39115039
    0xb10082e0801110406090e040f170a020105010803040501021b0d060903050a0909021309020c0a060203160801080f1203040c0806010b041e050319050c030d050a0f090807030f0609050a06020405 84
    0x20500d0040c0700f035002e0040340708002c00208030070420311400a42c1c3d44c586402a02c290352a0f24050300d60b0341c2d001c2c5902900c1124004103407011440055259090140e14010b0403800c010710300d49402c1c480000c1d103c15030001d0706941c20106441500c4a40c03180200100d4658200e0010000e00010345002405907020007500c2000a000d4000480d038142c151088501c804044008000304924020000b0044e40221240c1c18050103500105070114126000561042c40401810f94070f92040b01009050000c041c1c01901995200c4040c2541c200c03c00681845010f03455208240c40c2e035290b10304500d0a0f2829041540607000d100d000060b0880200050b20984203602c950205451000f200008550b0541c41071a505078402171074013040d0740303006c0101600036014009072400034602c8808203140030101c00114001903c001410204079511807c0004c02c0315540c40e1266949203403407400faa5900003800060310740a0031105032030070440d50b580329802c940d038403400340d40c5124802c1c20080001d420a10a041c01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 39117531 1250 39116281 39116291
    0xa020c18040b0f060f01030c1b08030105040e03070b0414030c070905060103051305060406020d020d18050f07030f080f0403050f010605010e030a0f081305090901050610030b10082e0801 81
    0x218180240f00d051203200064031901d450302c80c0000440140050410400500440d610130400c58035048a5100040e8003d41c00e0035501c1d403502003030000301c4072103004c003040b65001413002c00c000581000440b5086600012a654100c082c8556542944901048038019101d020340000e90303030700190816407081909803030801c0140e0f1400001112907000c0f903001000c0d9048040060700080055020701a070200b840e00050074043c00c4401c071003c80b0314010410500012880081080000070400201840b0002c00035002491440d901c1903100d00400344000c4c80c449006c07071102582114003003610021a0000b0481d44040001c00449000300014090a800140c090b10451003500300012a5101c2076489050810801c045032a8801036810402e880c00c1e140c00750300c070f0008607969145021030055130240b00016003414010100101c6070704086487e8141030900e10300b030045540300701886030507000b1400c1c11080c1d80e8a502040e80c000d0001c00a01c40400f402910320b24240b81d000d01c030807080d14490402042 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 39118781 1250 39117531 39117541
    0x1205060a0302010c12020c040903051306050c03030f090a02060301090905060709060203041701240e130308010603090c05031204090e030301050a03030c14011107060b0906030c060a020c18040b 84
    0x10464603400060701043c2d507134140d4000110100020b00010005105460f0a44940400030f41681e0200c0c038164001000400c601002903414244000246240c0c00d003d494024a0010b8039100c0c0401060281000030500014840981c107001c94840785a006000c2c07581c07036171100000c030b00903c0d400001795060b1151000040c050b40c007645401c8150b42e410780003541814038150981120b0680380d16150500c0d500c0d0408010001107105150140811744210251780d513040c40300101503201c000302607410503c12014007038040b0b80c02256941c10765441d4500401c8032801030601900c180c0040e4883d070340600c5581580144280c00f14060000e0b41c0034003109104d000e918810082c3c0d80c2c0401c1c041c01ea800a011181080041d00a0b0194002688960000240102c1100310103084500480b2560001d10001600804004941c451070325191000c569030768480c1800302c0486c0c1d441000046d4a4010040007074200c1d10319008118100b41400018100135150160080b18003400c4406d40d4221420150030380426 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 39120031 1250 39118781 39118789
    0x19050a0b070b06041119050d06030b0f16050301030210110607050c0c010306230a03080c0c010f02030315090a020d0207081803060708070c06060e0a06051003090803060d0c0b0a120506 80
    0x41710440179081d05420034245900305503014200388600d0341404010000d80754480c07001d0003034800031130043c5d001413800e142c81c02450150904c0109543c001840303400ea006809070f00710701641d040d07940544803002c10002d41c850603100e0700a00030504c030a0b44105010001d00550000c010100c011000050750b016200b001e0040d000e44a19010300d1701d0b01918280b80d4941802c00f012a841400c1c401003205420954075150940280d000315000e0003e50080f61000c4203d58000715031b6103a0301c90a00c02146103261148120314101d8803104074500c1652600702283c1e4492032a016a544043d450a0840d034819080c50070344030350380c0580c0c1800d41702e00c01010240c42900c0d010501d144200c03d01e4a074018566145001103643d1880d1a000300e400c55070f0703000b0100c0c999070910409846150040b0000824900b04010003c604400ca00300c03c0405051145ea03600240354407080c0c9400c56010356240490f5003451070999042c0c40700c0d8110720031180002c1b0b0f244481903844500d506283c446201d04101680f40c42c004c0c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 39121281 1250 39120031 39120041
    0xf10110903100207020118080c270a050705040f1e080106060903060b031606020c040e01060501050a03150e070503010f050f091909050601080109030908190219050a0b070b0604 77
    0x10680c10382110702d145a81c101180c0081050510500d0078104410100300003094100b082d41285125a0040010040300e0a00f03050b1085865428038104480c2011028041c820010003085510310b035032200c01080322140a80c007940e010702548451010020744550b000c0005000034040445044286840041c8041042c8964801c2d207203543e035200c10190840d160381c0041d02802106d20b03014402ca071040f00d07259400d450750001034200369000e00083c14003202000240ea1503540c2e4841d041e4034124003000141e81040845145194504001c01c108507483d111821407890350b44000e04c400b040508002007254000d0055040c0c411004a074035a0075103a009020502c0850980a50810790352404510500e180c120b60030110404448003091560700343d40d43c2404c020007079000703a80340da444064071010141c102034040050501d02000301000b41b130030f40384025a00248800640200310700500c1c5103214044170200009030002501c20040140c0d240c07944441c50340110030a9446513800c1010030628a418010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 39122531 1250 39121281 39121297
    0x10c180311010516081b010f0b010f0e0303070602030a0506100306030503030a0504050c031e07080c090703110f160606050102030901081810050f0402010e0604060f030c09080f1011 79
    0x1a1000c5010450040d5919031050104400c0c880301c2c0504c81000540410040100c01c040f04441041a44804d05180c213464208126211003424140c41e201c060341d0100c8045105c1008e45484958000300c18042030039842180b1019100340c0c000010081c1384103c94003c03901441007507400c5140a4004d40301101200c0050100400c1d58008001240c040c2500342c001c40e80040c05401aa824640380c007002034076103800d42d08040326026101e0399595212105101140c0109150006420200c18000020303400c030400410701806e240d6110301c40c000f0062004141d034004250800490b90340c04140c2850f00250303041c02012191207041040100c1e8a51012081e02e4480c101a10b5110f02078490030000c11416822154440180c8194522888090032600900b80030702100b039504529404e1078000100410f541031480e600992040104200c459442070300348203541164640068040c40205003240c48220303641c0888079034442c01020034039806011404805000340110100890801c504180b4030038011084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 39123781 1250 39122531 39122543
    0x7080106080a050403050409090501050103020f06090901030204090602070b04050c0a0b090913061509020912010203010303080a0f1806050901060503011505040504060609020c0a0c050306220201021e010c1803 91
    0x1c0410302d500c00e2038001c10342003442814030500303050b140d10110089801221054466030b444800420640c01d1001072000c0b4090203450603490400d444011070150f001c103110003400342d0764800c41c00044c01029130554940c554001c000d0440c604107030808550701c1400e000583d1140d00a01000118001c40d6400c4440700c4101422103090359031201c405882030068450240c8403141c480d40c40301900900301c1540030241010300c50060301c2c5c40b485000e00006044d00900142e840e0301c1007006002080e00214071661201c1c600402140c04c00c2c0c0064080f014041e01040d0b041111104441e40c001c100007034004500c02c081d00c40080104990300c1041600381c075180c00d8101c14403583d60f2014845410150040d6510074085c20707000c58081d40d2054000308070f03441006c0c0c0c140150001619401008081d000c034000901049005005a04096903141e10034907080d010006034500d034408080859009101c40c01d0402c00d800301017940c0340502c404840c060076103e003601001480d003904828040e07007041c0c101c40559070400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 39125031 1250 39123781 39123797
    0x60a09030f0c0204060b03010609260604081b07090b03011803211503121b0309051e0306040302010b10080405070311130e01090b0c0702100302160c12030807080106 72
    0x140700b550076500d00c200c2684c01ca40c681801154007200e00000f54000c00c550341d540c40030280303130235558062a420b94030058000d91801d48400b40100300014500d41043e0003012484e55210300f400c041c14400c148862523075250160081c0000d103440c4961102107082d005500038072080e01c050000c007650709000400200030071300c0400044070f000118034000c0c0f42c110903414002100403401510203d5184207603c00c441226050090001c1c07a40c2c0a2124070400d01c280d01d9880c03c20031940d030040d080034214003880e4000d1040000700150711034500d8a040c0143c201406540480c00c03d818000d0280141070203160041e4601c1d001b1600e4917100d05a868412034003c4050504541540e82e204549504648099440034684055078191695031103900d50050384100000b034a41c40925001d81060801402d507105440309110400146c1c94101c46009107092518005948045180b0100c00721041c49001a040c5c194401c000b10351103024040640300d6038020744501c10b86540d0040100c0304a6824011980090070503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 39126281 1250 39125031 39125057
    0x2090906041502130306060e0105041506020304050f01120f06080d0507030203030402100e030f0106030309060302040b07060f060b0c010603050c1512070c0b090c0109061404050904110301020f0c060a0903 89
    0x3a8013810820b41318180d4904003640c1c98681c2c00039201503030091200035444800411451405201e2058200782d002e04d000b021518044003c1d4a07402103104180c01401181c601d1001ca030300c540c185e140742407100c1c01d0030800080d02d179161400810060089021a2091083c83c19180c0d000d030b030a0782c079144d500d603004510b550354560a000d02e0b202000c1c40b41080c041e1020503461a030740c0601004548035400c0e0700014540e41b0f9800d00500401c956880300d0141441008144100e10043d0704440e141500940041018121074490b840244556030041500d84408240288038034010342242040300c2c000d1003141e03c91042030003080641031030000b03600d070342e540204189111b603400030050607031005042c2402e4641100030748811503000d208507500c11a07600600c00182c41582c000510b003014100919040907100c1203c110440c0c24495409080c0c810502840003500f04081038106001e0b0420140081d07440d080c5000600800d508800300e08a030740d008400c00106800640d12501541c1505980c40310600340e45 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 39127531 1250 39126281 39126323
    0x902040b071106040e1608060405060a151107060c0b061005070f080f0706020a030c080108030a1803080a051333030906141009020c070b0c1c0206040209090604 70
    0x3680b1015030800300900002440c4d82d403241c034a910500c0615107400c3c202801b103c00610126008007400e02c03840c40c02003031100310b843d80041c10080e140040c031602e2705051042e005803200b01030070741240d8a910840c500858419404491404294440c0309120342c00d032180710400950a0302c0311100e00000d0018440d0802242410030101c14150140c00040c1c900030380d56800206075030154034160f81d01a0001290380c02d50790b1500c01c420000080d450614030039410f240070180c6030703c500f00e000f00c01c016200e80c8020414030365900017802141c1c0320701d00c230359542c0d810800504240c01c140c0a148080b84410750020b8443c0e15103800d4900640350800c002c0011049640e0000340300d43c0070100301308040c0c1e540e042900080080c400c80303604000f64208564645400040ca540102ea01c1e080360107098014484050a400005007140558000a41c5261502c5040b80001d143c0440c2c0c580d03901d010398413842c00d004100d4000c03031010f0285000f69800045541c43d515081d60382c0740290350040c00e90082d401e415041c481 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 39128781 1250 39127531 39127553
    0x512070f05040f0e1005040b0f04020d0608030706090c05091911070204051e090d0503060d02030307050a08120a0614040515101d03150c070c0e18070902040b07 70
    0x214074100242001c0c3c0700d0030f500245485039007001c0c0c58110b40038280300f500d4100d520707048000c040896082c0b220005584c041061220318a4889001c0e0340c0100703110030020075542007070018120450880c5c0c3c541507030b800d00034050700e42c00a050300e00585295011859007048044a4410501c06100900c1a11881e080e42d000303095603008000d884d80240b1000c0010390710741c02564010100030240c03400d4034212072408280d2000250124115902989031003183d40e401c081603d5022600b142c012143d0129400441e041d840341c082e008209010b0400d80104000070b01c2d002e8201f0400d50044002079035a0900075104441c1c542c0503402202101d40e1400d10545407541007150301c1450400ca0300c00c540300d0300012401443c1026009070114100343c1020f02d140d050050780140e120320440040c8100c207040300c00c84031003141c040c0c10300f0604400090300c5c1003130080e02c00c402e800910350000003034418585003008a08880d401c03031b00c1d1502e0f801903490026100300c050003500c040d03d041a01240c504801c0c2c0e559001d40307a07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 39130031 1250 39128781 39128807
    0x7050a0e190207050d0305060f010c0f05010209041503030f09060503040602090d080c011a0a0e0f040602070813150311090d06110a0f090801151203020a0f110a06051207 74
    0x1001900320500800202c1c0083e010580c13142c1d0042010140092001c0d0a89900501c40d900480b807410414010b0707a4002030400c07000c2d800030410b074070328003540c202103001e88500b0701419046401c1500003852001d0b910002e00c120ba002c0c0d0358402d000b40c0e002600b26580303141407003203a00080080c4049000f29446a00609024100911a9404034026502d000301078100d80f09908184c1d56402c2046070350101014000d034000002c03211054194202841d01c0401c1c040a0312206aa0312190005420488181c0c101d44083d60081b0390075480d5046c90380c01e0115418203001d04114880c0c49023070150558013a009007900041d16200c0d007414400010140410050b03001000d40d0280d03107032010381b039070405511b0050204402a070745d0401118180080a040301400e42e22040050385014001205e4040c0302e901e0500f42c40c40d181c0d0380498901c403810100c0c502a40303408090031601042c005075003000700d43ca44624003e101601d108442d140d80b803006503043e02407410304a11504c0381c48005002d041c0316003510400341d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 39131281 1250 39130031 39130051
    0xf05030a0b0315011e09150605130b070503090f01031e0c0c02040f0218150706050601030f05090606030f030c06010e0a11030a05040219030503070b0a0e030a030f0e07050a0e 76
    0xa0721001c5000006402a8080400340245144401a17480c1081100e4040c0c00382c26030501080703000d100c5d030140800041c071a0904002010580c4958020181c0c4d00300300810200501c25240c136071030b04100d501ea62000007500e1240d08031020051a80d40a8017442501099010b2020483d0003001ea041020340502014581000803c2c0c07103590060352144103200b0460501c0e9070040c0c8440702040c100005481081c0d0351071007440255180c001448c11101202d038020317032100002c181a00c400005801814403601214049814001084205100001d07401d2040d242241241c0122544140d040e4503403050821030281074100e00b0060010450710040a0340158111034005900040042c902c88640c006440d15008a51501c0612080d4585010515a00301d005181081036614595825546e8400d04c0b5004140e101c0c8000086c1c50b1065951101e55110341c40429079a6804003290300900030444032084013412450080d10f410b00e540b000070241c090700e0000d001100320710300b401c052040f200e1000f017200b00300c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 39132531 1250 39131281 39131293
    0xa0903020304080f0c04060501021c0518040615080705031302010809031201030b090d050a08010527011206050c0f0f0c0a020a03080403020108070f050417030702030109140d0f05030a0b03 82
    0xf60795820010504240d400034080c0c021420004100700903a01154485411075200320010007600507610300c11440c07a043d6042641d51076404003a603001184851003610f44c0549485400107541080410841524a180d59040030a995880c802d540c1ca00045e500d86028403900764240b401135000d8500c403600181008112820030f401200c040c11102000d03003044031183d0207001071259040003003000c40c441e007206040c014142286410003d240032414824a80b04006031600007510307407403c000c4900b0742c5d6a41840f15846e9030b141d80031048408586401203c2491403c40020a011090b10a1b02d980c5c1800c0d281c1545070414212012003950015120b940340c1c1e0240c4180c040050340c860600030300451040420079261842c40c0000342c80420010003800505c00ca1408042450340d028085a050b1201c800049040c2210300040a00e180a12400203401d50f10707002503041032003c01100e9180202c4c40b002280c214010008003103509241c02c4a5200104105102040d1800800d07048200029805021110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 39133781 1250 39132531 39132539
    0xd0207030c17040303020f0c090a1e0e1c110a02150f0310090b030c0906060f0403150218030313060806040902060d0b0a05040605210705030708010204080c15030a0903020304 76
    0x1c480d1082100a0b509140c00160800405405001c40b88101e90f40c0c2004c1e1a9425405c000300f4290f01c00141020a01d40c1d880030390041c0c1012070340e0207562b5240340c034004011600040340c0640d074a00d200074540180c2044045090105403055108582003031001c4058059030305141d0034440d03a4008c0c0780e03d490101c0c80c24841003c08406403c0650f109044c0c41220aa90a1900080004903407100c11594041d400402c1041c4150300da003030405800c4102a2540f99884e021103041000794043d0b0742009048803480444140e010300b4603006040e15494502d807482c5415002c00c20599a480784030b1280c03084407000c242c10081c507030041c4a80c550210f4050000f10342554a64001807407540103030550303101960740752030703101050070030040d00c0b0060282030300e04100103421702c4005442001060030f03098000030a081d038080e8540301800b5040080c074001c0c0c00c64100c503440d80040c40c044d4003d401000028400c200712001945000e0000f0041d0450100d15285151120000c138406016409400c0d0294801040001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 39135031 1250 39133781 39133793
    0x409020a0903020d0302060a0b010c0b040213020d02040603050f100810020a0201020d060803030f060418020d020301020d050106020a050d031a01270f08010f14071818020a03150303050d0207030c 85
    0x44c038944c0c82680a00f24900e00300200200b11110300d024141000962610f5900081c0c05142c250b0704036404846c10300b8280c034590110000707482640e820b91651070000c24005035268042d0440707800350110103652841d03955201200d00580a282c401c8203556071180040d0007844075a40e004020310151480007521307102c3c400c62510280c074100c0d40003200a52000007041002002a4102070300002d00b140c0600174140401c0c010100b405803840043c0c8100e000d50a40701c115502541151200514018107205030b44e5911000794a80c03000c6102903845001c5c0c5254030039401c3c07092040c0100c040c82c04075071031a0f818081c00115050054110118859400001341503000c41034000004018100c620400d2841c0e17082072051800c0d02c80200390f0110081c1000ca514201c144101949907020810707140510f0403a07510007008802c5145548010104400040c031104020307603a400030006050180c505105844400e004480000668030001c3d000407000d22860703641206c02d0b001001820b019182c80131090040f6102c0c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 39136281 1250 39135031 39135049
    0x7050904020f04061206080706030c051606140c090a15050c1510060201050408070b1e040501020a08090a02030d03020c01020c06010807050103060b070803060904030c1a06040e030c030409020a090302 87
    0x90b0380100e00464100200365008001508903101c65000744092803420305599503600440c0a09800e00d078176242c080e02c40b103204038260341d0480c0b2030558140c10088541402e200402c07001030204080d46803c800162010030034012101481e4010b00000699440c10440d107012044c1548940304002041000b03208200c02000720a40c5160000f0504035242080740020380c00740b40d240d0044055906250400012402d9102501d41d12504030115684561314030103c008007004032070050032040c0d105418402440390541c058041c8180b59101c1c0b48080d114201041ea940f007120000940c1030703124104500c201442a00540b200c01a240005400c3c0740c24042a0790030729400340c21101d1729078000002000f00c2e69050068074010540c40310120f04e04003150322004428800140300b0f900880c01d500200342094032580c10580844e410021411040c0c03000301c403000300034506544003842a801c064048103100004022521103005480040d4640b924062911000c1c0d000015501d0521030581000809a11001c4e05 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 39137531 1250 39136281 39136297
    0x204020316090609140d030c0b0c040504060e01082d07031a0705040501080403030e030702041103060a0603050105010219050c0a0e0a060b030601051b1218030106050409080703080705090402 83
    0x742901e903000808000c0c8041c59651215003000951070301040f009983c480300c241070660650340070b50403d8941c141139079241c081502c0280f481111800b00719030000b200300035005480b0700315400c0c40429030f55246c0800c5040203000309080ca400050186c400b5644074640c070070400440100c882d104120960724541401040e1340b0a0360050346e002d100d09090440000b8880d0f20641606181e4102030512000819019004000800341950341e060113000e8501001660150743e0f004006001e0b492100803c401150003d4420f58003610106034040703080384c02401110b061b182c060f402840c201461504840c0c2e028200720059a99000328901800726859070007484024203030301d995140490400c440304104480b059800041440801e0003031100c0341c3c0e8000c00f101c00c16121200f015400380208040c0078200300c8a5015041c110800244904090f85402192941c10740114000c0284542d03802c00c1c40141c410710500142119400c1101c4ad00003801025050382142240c030b0030608009056000c903040b0780c0320b008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 39138781 1250 39137531 39137551
    0x1c0c050307060e041404050d0513030c0609080d0f020d0c06021207050306030607030e0706050307022d0c030a02180903041a070c050d050a060c110a0605011514030103020d02010c02040203 82
    0x341803800e0030300412444805c104100d0105141c0783e15416116090740c2c1000d000c00200040c40140441c004400c074002e90342180c0d02000c21642e403480981201c801d84141c45490091402c1608410702820404000f0001a0050100f5100c2d0f44804c8401d400000790450750142d081c00544182c2c241400e103603100d16165100c050b541d003401400c042c6000e50003030440e001c2506104801b040c1030004284601115214101141c880e164500207a062012401c1e0101c1c550305030190f004800c1500982040d00c0d15a182d0685074503480744424542c0300d03150b000010303400c0440c3c030314161400f248510300c45034072000d1001600d0800b41c032985551110700701442142009174001c5100c000b0301c0410760110b00202811920186064100e42d2002c1d12030445c0e0034007402c0c40707035100c0207004224003a00b400340030940e0716800c2d66001c070018503100000300700a00445e0070002d03040307410004585c0910004014001030b103400f2415686158200300110004050403410003006401440c01a140c0740090b60052458007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 39140031 1250 39138781 39138797
    0x60f040201320307030603140d0801080114010317120103061e0b130b030c06130e0702070503071203030b0d05010903030c080610030e030f030c04060206060402091c0c05030706 77
    0x800014590220400301d291000c80709007150322480719802410b0700e001010302040f6160340ea03192060f002000c15a00c09043d4000c681540780040d107003c116821101d06984810740c40341d803203c004900300c5600028425030275481c0001031000c10790040020902212508025142c505c030344000070910482079004480382038840324055000c22840845882d1110030402c10011201c00304005006103100504541311265248218445600c6c107000488070001d003c0e00d003540c0c440316181c294020581510a200e10301c40c1c8840401c2c40380d440801c4080032100028000c0c071010741040400b044881d03c0040031414141c3d1189410042c0e15014816221580100000564020b02c3d040103815600c440700c8020402000c101001490740c3da400032034848500c0d500d000100000000e05c00c52651180d0146800b00310004000c11240d01c440d80000c0040d0746999013901c03a152589070034002a40920708a19a104455441c081c0c1a44449003896040030301903882d10010564900110b400e0038090340000c0300080ea82c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 39141281 1250 39140031 39140033
    0xa02132c120304020904080702040b0a06120605090103030816090e0403050901020c01081b0703022508070b07020105030c090102010f1e23010605070807140601030b01090c080106030509030c060f04 86
    0x248450440748008616092a51405500050032024002c100503c0306201040e88825922144e000076030200c0003800c0c00350015282c2c0000341c103c0a00400c4900080d0800c2030209944c00c2107285e8604030390341030b185d9581c5034840384240c110000380702000104000031540300142d0446030301c1c0300c0d6006030301903140c2c19a24098103000a00b000861402c985c180500c0c8800c1c494003203562424440402d8100125942b180c0781490b00300d0920004c03c007160071085001981d044030175401c540903411103100074121039109070303664008802c1d8080e014010b800b00e035052001440108100d0020016280d05100000d40c2e0780c421400182150b00100509a652180300e1059455440c90300c10304150911456140b07004040c00200092600d005000e050100f003404503100c1d00700001a01580c00c80e940c0312000b062000198031180c1d540c1d20342440107540b0b0500c0d5800009042869101311f039050440341d6561903181e0b0030451b0540207010040c0c607034002e40c80304008080b004801800b280780290400d01c0ca40c2c03041d01702 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 39142531 1250 39141281 39141283
    0x312060311090a05070804080f0708040902040503060105030d020307062307020708010b010309050718060f0306020703090b0a080417040f0b13080705030303160311030a020c010f020c0a02132c 84
    0x20041c0000ca56504d00b2003404400b540040080d0760080d84040740e00da96a07808104622a07025900d001011148040703408a845d9003990058800c3d07078002c0c0e04540a5a03628020590b0340c003048034680d409a00300b00413460103d1643e41185043c0b0410108103407000740d1405041551040440d000801078010740d60500000d0002e014001b5400d44c00d00c3e0500400c900340d202e051715045c8a10a4a01001e03aa2110a140703002035040b400c0140210420701418541d6420080040c1d030008000320005000110049007a0201506881d850425940ca208590f9502da07240017201001003110000d0000c14040054840c1c04400e006015000d1240b140c0d8884210500641600e4190f0300324800c190000320302801661400425aa4440c140844810100c001c0324000d4004059000a81c44011000130401111140c280c00504001c1d80da007000300b111801961500080740154031850529030412401d04001d40340150440c410b00c000f002e40003582c1900301d2092030840f840140110440c03510540042100300e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 39143781 1250 39142531 39142549
    0x100201050a1b050912120c0f0f0a0c03060216020301050c090307080303060315070e060403030914090405031b240f010b0415051c06060e040b0a0810090312060311 71
    0x1041c28660110060070307580140c610301a070341410740203001d03422841c501002d04102c46e82c8044c2c0d070140303960b42e14003101c4046500c0358403001261003e0300c140907600d001e6560015a9105503504910a5001c4c1407d540e2440302a41c09145010441c0301140c1d203480250f47d0a02c5103038040c449001d01c0c00d54441c80c1d0b005246c1000b81030b61004072150000c0c0200256070314046403a81001800120080a0b40c0d19908103032000701c503070741c49550007410115002c01007603042040d01c02074030340f890500c1820002e114108541842e00301c4000308075030400c3c885029040b0034100090082d9400c0d500341e881040c0f40130200126500b800c40744e080744c0c40c10758003800070f0042207900329400741084080d0586803e05201010248607140030550f410004006850301074071014118000c50445134900c28081240e903004000d10018400380c01c20f01c921b00e050030341c035964902080d8000884850b0805001d198120080080c02019892000c0d4240131551401003030403c010703c07030980038510800f00d0161400f80c103418070a41c09 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 39145031 1250 39143781 39143801
    0x10b10050c0c0901030b06010f0207030b0a0501061b02010f0e0310020309030a0e09130f02011403040b01050307090209090c0708122d0103020108150406091802040e0106052409100201050a 82
    0x64900001803010506c2200442d0b8404000c0c04e0440f49418902000c91401803130b588081e103100505c01c20300c015072440303070803050407211107540c2d02d0940005030700c1c1d850340c00d00d801c0c01c0240825102c4480711181800344014000030100202614941148680f550040c2d9000b1101002550000900c480300d55801c0405522a50001d96640c140ca00d84290048203802582030003400160820340c0e031b13008580c840c03d50f01d440204401b001d5522801c1500d01790201400a003d079511034042c0810103d9524494070039034919200082405d411612078081b20080c5910050007941c41c0001001440403e1900020b9240180d030200c140c0060110650b0515040480c010070140f4400783c00ca0041000d44e034000961038121030001b601c078124400440003c1c2c02040d81d5805021101e04000400c05e101100009400015000340d40c10b128070424504060300302c1e00c1500030240d01c02071038034964401c41c40c440c815007119400c5444640c601034099000500f0341c2c0c043c40040b80148c0d16907080003212480c60141600d40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 39146281 1250 39145031 39145039
    0x405010e010515161203090201020f06060d150204030606060906020606090c07120e03010e0c01120203010b0a1b02060d0204090f060303020c010f201c021f02070203010b10050c0c 78
    0x794104800280ca10310081c0c0c2c078a1808030042100b04c1d0f49a51a89080301d841e03400b00c55882003200b04071000d406803100031416809409100408444c0b110081f5406106002c0101302c00c5801490f87e4030000111241c1015102d07040e424813010000420a201c0c2101411258945c02d42a0b1700e400402440c01100900003030040c1c5402041c801e5040c101002e80e002e00d0742c400d690300d400c1c4020f00400c4804100507034a56516608107078654100d100302082401c018103003030380c0309901010f0b21a0b031802079220a12440c103203102d0400c4200e00d094819070070803041c0581e9141c0200309529903000241150800205110f816600040400040c00a40304c1e100940000040610200b4a19103010b9152510f45080e5414032243e101c060443c60320500003840c040c01c1c041c4a14400011241c816136880c1c12000940d8559131410138592400c1d0b00024040c2e14615100000703035a80400802e10f007007e904180300c01ca0b010364841005050503518450880002c030210b0b0344003904c03481c8040c1603501d844103803002c1c1801 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 39147531 1250 39146281 39146309
    0x13060e1005150d0b040f021305030a02061204020102150f01060806010e03060103080f12090d030c090e01030f03090803160201020c01030c0804061817030603070501110a0f0c050d03030b040501 84
    0x400c0d02c810300d0326500c0c074481281d00c0e0340320440c890124014050116540f0380c441c0c680401443e4102e419800b8004215920602d903c0302500c6a0602d40d44124003000658415011f1003041c1741400b84011850b4031038270610680d0000300909c140c00e4402c060580d0100801010f0000622a032503000c0346841e88264246450180b2558041c0440d88545041c00701404024000a080004509020485525025840203d01d0f0340c9003805c030240e02d64003e01480310009080080401001d440355240e4002e4640140c000070041c0d103550340e214211058450304505000c1040c0340022454000c0c00503001c00c5640102030002d24041e071000904180341c1d000d540c0d0501d442c100d0044541540b00d050150b01c60362040c000111240f40640c90105000f040c0c2e8001d04054150961804810a600266000b101e0079800c4604180d1030b8801914180210b07210758400b64000848840800c00c1e0409980c80039020b42864142d19403240f011681d03100318402c0c160007203600c1e00c00000b200d00b0b083c86401d006004004041070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 39148781 1250 39147531 39147539
    0x1614070605150109030201050a0305091608010501030501050c070506010603020a0e0909060612122a01020406170a020405010e04020d0b150703140405030309010c060605090f0406140f070c060b13060e10 88
    0x2041b0b01809e06200304141e55440002d0551070200003440d4980040c814215426580311a418041c0c40d003400101d48550a140109400d241c5440550b17049560040280415a082500450094101c0e440c00340c1008924100d05146132516481c850169401c00064201c924040e8240b02d01c128140705a0201e50380609103c0c0111030058064650803ca0b0940038802503d09006004500381c4240300b01c00154170018000900941040c883c1240000300da110403150f80d2000d6040040340244c3c403c403808220b07003070b11003800d0389041d900403c00c4014413100080d951103403101291140d151090350074101d800010b180410b040d0007041c03401c10070412108040c03800c1d0400001c03c0e101c2c0584008581440002800a810020315402c04809003c01500d40800340c40c1c000c09a41503500d09480036141c0038a481d1544110711000c041d8544580bd40940030041c68407100412121000b03501c005030b891940d80c2003806400e030703520144824114000700d404030b4140e04009000701001c002a1101d043c1c2d14850b40d00704 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 39150031 1250 39148781 39148787
    0x2090415140c09010e1203121f080606040504020103090f05060114030316030e1203160c060f0906051c2a0f0e040f11070606090b01050405091614070605150109030201 73
    0x9010010301780f038268030300101c40300400c81c020f1064003095144c2c0008921141d1800010031014401c0b808800510003000000b18030322200d400c10700a100ca20340042000850070b0038180c001e150080c3c410b240003e0020f1258454081d4000c4089044500e0b030041001000b5151481c03c0068800304c08501851402d80751605203e08900c40c51001020705c40d07200710701c0080c0e503110b41110009071510402c3e00e50b6130201048002200082120441e92481d40030400324030144200045000c1198039102d48a48605000c400c0c3c4154000020044080b00c02c80c00031900341009001c0d44042c03d501c20700c1c002080c1010140103007403980000a1b141000001c151904d00140e0201d24078001540517140084c200c42c02140f94005888502c810f83d2122900041c010100300141c1d1080d0100c800c41a000c10940944000450305c510a61040a5000b0f4441021521101e90012460320500e080c1c20300c440b400c00101c1da40c0c441508840020342d00d065850041052980c1481d0f42040e010200340327030003801d40c1c2c01e650010f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 39151281 1250 39150031 39150037
    0x90308030c181207090b0609060d0e0c0303031302100302070302032205030d0302030f0901020c0601031407030b07020a02090114030a020103020d0b040612060605062106010c050624040b06091c02090415140c 90
    0x107083c442f40c85890000c402c000a014131961110007506480d43c03450141c0c0460310070501300004a001c0c1203003047c1704840c188240b00b03507940c1c103506a000c0c41ca01150100c140324200d01ca9a1880f42d107000a01c000100781d54204201c0d0038450035900c0150701c914016426402c41d0340010521003071a40100052074003040081a0304d819a640240b07000c13046100d1401580c41c1c681e03160401000c0da00340800788902c05400081c48200c1e02d20032131700860785a0b2100c03138411410807800d07805505548401c00e00380056010b1b80262140d64100c21002881070340710400501554215440500c03180b1600141c03000b0312041d40640800ba0605a41d1907241950507074408000a01001078041032010103004220541c3c0700700350382d01540d500601210304900f0624802403112198401c04440200009004402818140070309440c51600500d03480c24282c801c030038041f80c82d228404900d03003c2d000c405150300603900c5d90030381c0380a01d0043c0107103880c2d1001d00c03c01070111611140003458141d19001001090b6000b1411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 39152531 1250 39151281 39151297
    0x2030712030219030506030c01021b0f0112050106080115050304030804020d0503070b1503070807081510090501030303020d0b061303020f130e06100501090308030c181207090b060906 80
    0x15250500409200301e00a0180c58003d0904407290200c542045915811aa00030304080b81035403420064640166a40c0740c00340d42900c1e107030240790041a041e16051b26880200c0c28181040800314a081540d0021a10260000b00101d403081c0018010340456a02c2d88800d214503003400391031814103031030240400800600c0203104101342c0c030800303041140c2030041d11160340d800005004c0c581443e0065900c010200010903019129452002865440001e40705c001c95a2800c050041c03000701402d0103c1c80840240b20340d08810030703400000350003495403088c10300a5019a42c0140c903066844000d00641d41400f8038280304903401d100f8281880342ca5000b075011664103c1e011080010403001140400c0406001c43c13004600c0c01c08440350070500406c20a200e4070030005801082502c0e000192021021404064400103060000802d4084650300801c081140340100148104511001820000c1403000e404a03680191004001c9007650380035542c840d000c1122074074149101000454024025424 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 39153781 1250 39152531 39152543
    0x1d0a080d0c14030f011e050d080307030b030d080402011d0108270304030b0f130b0c03040201020a020607030f020106090203011a0708210f0603010c09031103070e07030c080108030a020307 82
    0x34161201c6001c0c011900e506481109000c0c0c032403900c16001c03902d41109100301806100c800000c00c4983d0001e490404c240d8400a0000424040c80d0f00c030f000302d0303400052130300c402e0560702c03540d4989640c1e0411070038400c100c861355148040d29103032000410101151081111007590589818540d80e0007200791688a81c81c2444903440109256015885154550701c609041c000003030040305001c5005049441101202280403035515503c800c4140700e00f5400b00645040c0840b8085142200d00800464000c1e00501c110303007a4020903000119581d00c907080440200380c0c088102400d4980a0042c4002048800b908500b50b40c50225100090803403007041d0340c0000400034564040003510303c142c0350111052014003000a41078003812018042c250341200d000d0001c40002101e0346014050202d06e003e441d034403418064510342d079080d40b82c044400d03165414051710f031002c1000200300c41100d20405880d580030403103188120f070142990006800c101c00c0c0f80c00801035280050740010860340400d034451 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 39155031 1250 39153781 39153791
    0x1030b0c0a03150602070305010e0a02030a030507050703021302180102070305120a031103010b0a02060903160b07030e01110904060501020303060607120903051b04140f0406020a1709011d0a080d 85
    0x4500030035a00c8840d1a548000140210b81349034001004001daa200d07000030002030300c100b11103c5d50b44680c250020750560111080a0000384140c001c9c0c000f0503c5034040340c0040d62240c0c0007030103184c1480c0b84d5041d6030740c0c007048040c0514403080724190846401c2c0003900381c0074215214203855000f0303001d601c1b0802c07000040804210b44a9440500c41c1407400d10f4564803961a415a00816400304144c440140310310004561280f0020007100d85034601058403c0b480402a41c0e03890b000030f4010110800c0c5655030702e1403c41c0c03007420700a00d1700002c4e0b070842c2581c0e01e4130200d00b000202d80b01500100e04540c1309100308849500c40c0b0048410064012481c0110100c240744210f0b80030450390401000d6005240307803600700b003c5510813246415012542400000c3e41d54196842504088907403000c003682c00700c0420041441940180829540c6182012800741c080a10940700c030020341d204240e0360356034401d00c090403881000300c00640d409200601204030f02900d85c1c170350070700078011090300301c0d0307512 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 39156281 1250 39155031 39155047
    0xa08181b0604170606040c0906081501050408101413030e0d0c15030509100207110409060b04020705030309060a09050604032106090b150406170c09180403120501030b0c 74
    0x400d407401820b200046003c1228500096030711020260f80060249050064001c10307140105504800d9815658520f6a1070341d40a4003840d01d000300d906098140602004045115081070101440c036104010300071422042c09422190040001806540700c0c11990a521000944c8130203c04192081244d00034541e030b08c1800d10b0f0503540441c0d4417940301607030315002c0d0b502e0450301a00300e14401c00303122090340c40008110581d24140d05c16000d00400e0020310f080c0c19000c600d055482250540d010b100000346400c00a00401c0890b4050201610385610100402c0320428007041103a40c0050154014031600d280c950310b017a03851001410050502517958a41100610b0a050005103105251003d200655540b2412001001000101400b440d048074810051820800c2120201e941c00c1d40d403400807100c41070081d201074401030880d1280310420006500b09544001004501004006d410080c1e8180b6240c090030903030060070a50005030603d00104040340c1e001c01c10380da0004040340d50035070358828 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 39157531 1250 39156281 39156289
    0x20c0a09020702042703080703050f01030201050705070f060903051902060f1b0d0f0f0f02100c02030903010f0204050306010f0312050306060702030a05061902040308030711100507050a08181b 84
    0x1c01400a094410000081170f4113401450f440003a9a0107a20b80c0c0c1d0040d02c035442c04030142d5108507000d8a401004100400c0154407500082003e1802502940c81c1a44c580c0501c007000300041c0c0c84000007440850041c401c1c440c09005050085440080c0c500c400400d036404203555001f806a100c3c6c19407004110003005421881d075144020040406952080d5100d60000d0101080c0c40350300030002c3c0b082d0002c00c441074011007250030460030030740040c40c0c3c0c02030614418010b00407085045003140030921041c00d181c3c509000310208640100c0c2d01503162410f00050526040f416805054551801c00b000c00118031840080d00c0f00000794541b0980e2595100e0204805205040c0c00a403d44180d10040082c46030115072507000703011641e9020520700c06400010140c0c080d43c040600819420070120705281e01036482c03040440e0101d002c0c2c45000c18a10480030889004681c0c12000c10400901d8440c0142d02000c80e40c1d0129814510000ca0010104044d54400f5a040e80d0303009d44034080b06506040c0e407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 39158781 1250 39157531 39157541
    0x71403060c131503020d0b101e02010b190305010b0a0303270b12150102010c050d0b0d05070602010c030518030a0804060b120304031202030c0a110d080409020703020d020c0a0902070204 81
    0x3100740c007030754548402c543c4000c000358032607070410a045d45442142010380c42c150111a5540020350380e803240c80c074000c603c80d203150420300080c03409643d40c40500c84041c0c0c82d0343c00f440c800d07414602d2621042d54a036003403c40c00c3d540d100078401d12810b2100424000030381c0020030310555036141026070600031000a03c50f0b030403a0803030f0844e13080c000e000b190004c0f601c655049000e11a07101c00302904402e103420b10043e400d0703524a04001c1d010071010320140c02030842d076a0003420101c80c020142c0d819400d0300d481c1d00e820905560000c0e00180d44800c24409d846805018091f040075640c0d88845035440040001d03500c030700600c040d0b2810803c0000110302804103035001095560702c000c2a200d01c0c503220940c840d0303581d842440100c419401c0000243c2c2d0031400881034070400070201c000307069088480c1d51601490000c012201d6400348070301e024200810070b00e0001c0d001a0241e0040140d0302c009a00b0003a02d0841e108000e81c0465000060b6005a500e0300300c00c8070102d0f01c0341507025840d5481c074070000e4041c04d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 39160031 1250 39158781 39158789
    0x5040317090f12040614090303070212061f06050d0c0201060b0a0201020711040504080f03041401060306091506060f0f05120703150905090c010807170103050c03071403060c13 77
    0xc00590510111950104003503200e0785050007160801c90843c0201d000d28000c2d8030450000c907a451644040c6c0018400c01086000c00040035a484c00c01d450f80000c0140c1c4c0e40c62130b2800e03140d001d0002c02900300841420809455000240079150901d000001031045c8201e4940455042d16000d607010b02c41d000750884805441c0ca0300d0300d241c84a054820090003504a410244c1d45404186803261407401c00d0304c44c860140386c020f01c2c6907140c5412191324071201e0780090421030b001b400342d0160840411b803c1c0300c0c1e0009188601400f244602c1d15040c2400100c481024031a43c803858000c08214243d08203007000052107003402c00c008200da41c00b0068030b25000740b040c45580c544140c001c000407503525a01800225403250801d10000382c864601104442c0226036040c16544151564110756029942c5258480c003241b8200543c00d0700c2c06000e1512001c01e9104458a500401c14048545414401400544401c00a1484144040e0002955440080c080c0c44007a800001c407900c0110b91214a10050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 39161281 1250 39160031 39160067
    0x10312050f070327060f02010b040b030709020702030703080c061803160221010510260703030503100503010c020601140d0c0b071b08030901031118130b130509150106080a050403 78
    0x7903943c4000c01b811048040c0e6440005520305031246440e0b107440d114250401c0409001405090f080400311350083d03025803002e0340c0c10f1042c6400000026141c100a018901c6948080e200e02d0400103502d00142d400c00000e50350b6a04244202c00c4000d01c0500025402c94044804d424148103203c2c4890180381031621085140d400d010801ca02c50801902041c12101d0800361027043c41e484594104a04020303030301041b45c91300078840800c080f81c4a034024541200007c0c0e81500c41a43d9a0f0001e801c41d002c284846025802038401040306215451480c180f500e801d841d0303480d1602856941c0e020b45915401040c07429440419114248003c40c0b00c00d003251507010321203420b429116a081582c80d044441543d00083c102100e0300500314019083d034240b500c1c920316401c014a019020005441d0101a0f10081c603030b0b60341e140c01c010f941d44c84c243c2d0000c03d500303a100140c6801e20f00186814a02104260050fa0840800400c6190341c02426103520110f914400500c030740390380c60100d462641c0560300c203d407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 39162531 1250 39161281 39161357
    0x905060a0815010206070c12050412060b041401080c0103020d0906060f140402040311040c1205010b04060801050f090105060a02012003070f08060f040903030b06070308010312050f0703 81
    0x10240e0032a107424081e0581a600c0ca9000c0a410012641c480003100d0900c002000002200700040804080c01044101f908255042980724040855010180e071015151161940c21500250030103208001035a00b004034007244560610328100e6650512041241c109a400120001008041c0d400b5800140d0310049c1481f220b541c3c2d00c00b401009650340211480071a80c040c070100c0e00d140074800c81e005ca17075100504603c540e4943c0304100041c8200f05401062010304c00000c04041c0007840303114085c0002485040e121421716a00400d510016000680500038241c017280003513130340d00c0945045400c103c456590f01d01c40705400324050040c05854140304803001c003038020904d0b5244065803081d0410342d916203c2c2d4100303c908583d89401540c0c4141c110b170241110110b903051903040184464064203021801d1404c54011841c40c0c0c0c05441d00340c0000d1064801401044a01c40c007558401c000c40c6000c1d0f0401d85100184c02c454070680c00b0050920180090704140c0090150035120840e0b030b805c1400750 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 39163781 1250 39162531 39162547
    0xa03061103040209010918120c1406071409060403060b19080312070f0e100c0c0b0403020a05120606041512030206041211070506030a0b060a02030d1404030804020d03090506 76
    0xa0389800548089200b44114800442e07010018801e501801807071610407800c0c66116150b001031490000381e031a082040c09c030180d138003150800201e04142d42c1c4d4070000308281d190002c00140603140154050040c03980421540005a8994003a83c0540350840c400048114400000542d401480c6409481c8001160000240c605000c009840302c00685408181036a440850423945e0b40c95449400001c076540c0301c0b5064903401c0103401451410080d041a4141c0350064503045034a800d194000c40050f5000202071046003881c3ca1048010301040d584000345008980350580c48900060980e4001c641e40c0100d0f06c1018018883c180080200030200304c1fa01c480c3d810000c8d150802142c00381c0342c4980c28101d00c090588180102040d890100010b00a081c1c00d1004004603503002911450144d0b4603200402d290b960341f10004d08540010b40c00443da00d00d420785080c019565015000001809800d0410000c80d4221510551066045924203948000391600b9105001d540c1c0040d45c204034003007035580d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 39165031 1250 39163781 39163811
    0x912030203061008010e0703090303020903010207060b12030a120b1507060f050105090c041202030c150705060109020f04030809040608010204090b09010b0a1e030b06030a0507030b03010b010f0e0a0306 88
    0x5401101c0684081e900f001d8040802d42c2d0a080a01c41c482c1950101000121801c0c403c3c0d00010401c0c0c42882c001d4a080c1040e4002405c3e6002070300103031140359071036001481a02d8109402048040c070a00134609141080c5005800c2032191581c0340140c0d0f0b12100c048a0710359401681620300c01918402e283c4440d56070900000800141c01030000c002e00c0d00c0008a803520300404164495094210700320320f000d042c8201c140c690517011508036010302c10000200707400d5481c001c07501500400940c1c2c0b41c2c0c89440e0390a06a150580c1a40960307032861040102d00c41303214601d022078043e60f400c00c0540c5d98030400d038000314009018681c0082c50a503c0801e020032070501c9900001060b1038100c030503006590b00e48012210301d12501c07480b040428002d000c2c3c01001c05100d40c510226004d83e0a000aa50740c0f40e0300810322039030007111800c401540c1c82d01000209509445103c0d004c82c810b030020000100608006031138075081c582c01100b07000300d010701c100c111b50b107000c010800f55500460074002c1081d180c1c022 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 39166281 1250 39165031 39165037
    0x503060c09030d02010b03070b0a0309060606260103030c080304081b0d0306140f04090804150206041505060d020402030a0f090f03080601081302061309150e090a0f1509120302 77
    0xa910a000300c22000d48404d1050080c0b1800031001405091403900d050144a0340344c1c002e8528006068071080c1a20124050f031007204010281a00c4100d0852401c09103919280c0c46544044140c0d200c0038011300100c0d41c000018003141d41d00600e21503403502c80c2c3c2040140d502420601006246841044000005000c035814160f00c81c00d403014031500740c0f544001d0090104500b001c541004642004821170b02d4290044100d6a004d09086031805484000102c0e80080218010340941c0c0101c0031b01c8100705c6050780c010101d404841c4100007a0420340001585008010806032007190040042054210f0582c025207030f44242c40401c11a0910034606084040c42c0910281d003c0342c0c000000406950151104070b1250b07118002c0c1400020090382040103e420184001e04142c90084020418200b9442524101d2443e42c144c4042c1038034240400c00313544001000031000f80c1001000c00b0024441000114a10340e000c00010314480060007140002d00f034418015015501603404184881d80503401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 39167531 1250 39166281 39166297
    0x7030b19030b060312090405060604050604120b06100203030601110c040903020703060c0206010f0b0c0325060b0a23031203010b040312020c01051b1204140307050405040b040201080405070503060c 86
    0x2c0103040380e0b1954201910b40482c44041140068100101c180b01c2c41d265001c81c0d40408010107083c10142c90744085042c2c0d812a4014400304502048000705100c0b80721040d5034031160032070308054aa8032480000f9181c0c00068100e6051014015910403084030a215192048002401c00c00c42518241802592141680301c2560007a20304100c1100541c400310701503040c0e8006d0356040c0ca989203468480c00c41580039400f0000b90740020701c5000c20080e882d0924009a40600f142e0107a06501420140111100d11021911411000004110808181d050500d120351a1030f5964820034800021034140f135020945019904000000410030480703d0018109a0f0b00401c59180d503038a58403000d0381ea40c0e05211000c1e002c51000c0c411314030020b56440b6180e049107121802d4132100440c04000c07204a80094024450b54150140314070f8440c2002c001107801441e00300c4041c0500c0c2030a4652542104014101074100146540041e0074404100039400040902404550140c60f02d0318140c0d02c246c010b829 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 39168781 1250 39167531 39167543
    0xc131404090210170604051317040b0a0f020f01050603060106120605030304080a03020709050c03040f03030b090108010c1409090a0c09032109080a020a09050a06051203030402040c0c120807030b1903 87
    0xb000c216642821f202c0e984c0305003c0b007810300d40011540c0e258806c207488281410343c0b100c241004003054504802000d42908032454071140104026820085e09100b118101601c4980c507000401413155000a10701d4111021401c160043d080c4150800c0d019019640040d6010f100000e00003d290b180011060000c1d8002c2d800da841054035421203070f05880c03050b00d2460b9402418408200412907115068040034428200000c800c004480030610f041c40990151040d07035503d40780c079007150360804028030340c0f0110300e00c0040c90508010001450401d02400080e0760300e80e01c0d41c4501c00749010700c1d400303000b40d504101c0d0305030314681a10b85800c02105064040f40020140340e0006940302c40000c1c0e400c411740e8020060b894050424554000620000f054050b0b0145c030b07400002480e0300c03440c0c1030002440b0b4050246581e460701e07006100c1983d80000642c0c080003d44981d44000c1411703030030030b036070f07030803510701c3d0004d40b079103501c6030440161402950103a800035540d00d6146d131130000045e40500f280d100d80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 39170031 1250 39168781 39168827
    0x90506040204200406030c0e030607020f0d092111030703060209180105030a020f041803020f070b0c120a050417030702120606060d0e07090204030c0e0c131404090210 73
    0x1142c1c0480c1010381503c883c030300d100f0520017803000074020781068001502c00d02d44030306842481c0c00080d01e080c6040e01c00b800543c0100b42d0085105005000340300440d0814200400f032645009499400004071540c15408681d0303041040b410840d038584440d661181c000e003162040c03516410300c0c1c0b000f584000c0545104140748074102201c0d10f900055075048550041c082c040e0100603070244010b920a035621264481d40c0c442000e16680c42403003031070b01018082d6008000c0000701c0c201c800d180240c0e075000f6200d9010140150007000c03c2c0042c986010905210070071b520351610314002d072490300681e04101c4180000d1644201800000405013004600840307440801c42882840561200400c1d240c468014500700100e0411850741e03004003a00300b2165040310450742d80c543c101801c0b0381240e00201e444030140482002601072a41e00c05400500200c8490700c1d1101440ca49011007009210300000e22000d55110700c02c6036102c0e13108552040c1c02610700710350400f0038417006022884c0440041e14603070101d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 39171281 1250 39170031 39170051
    0x17030d05161b0b1305010f060b0904050a180f0602190f032301140102030c10060501080f090a030e190b0a020d09030c14030f010903081618060302090112090506040204 73
    0x3000002d024142c01205508094981058503010b48000140c01c0e41e0300d40d00e90304100c00b5420f00d8402c140041c03c43c01c644940390350580c020481540c1c40a0f00e5417801da424201b40500009100120001d81e0360311030b880014082061402401a004507400045102d0406040480d41504900664080713285550100442d00307441c00325088010400d0300c0362080ca02904010b0007803118458520300941070500440341400000c000241c502001c2c10036881a20b501c030361040060303580100d169500018040002e110b9442c3c0104c4240e03688041e404081c0030001e05425200e4561511241c8020211100200200c07035911a01007100a6000301c250340018400c03101000380440c03055007407405581d400308075412240c0c030f0706103040f0300c081451b0030580d03141c09100300081d8106001d10898421520949a000c21850407240f6160002d0999140c0703810f0204040c071440044070611321031000d6030138a090058480e51807400403a000701c400c00c20b010042e45458041006e002c1c001400500c203034401c840c24840c10360340d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 39172531 1250 39171281 39171317
    0x304050a0c2c07020a0204020c0705090a0e0601061e1b05031201031401021c05060103140907050108060f01050a0c11030f0f010b01030b092410030b10030b0a17030d0516 74
    0x403074040d0016041742c00c140006140c00d40042c40350040400895505e1a21000003130403502051b60f0704102c1c1c039640c0c051311607410018000e0074010815030420242410041c0780700c0c06c03044680c20380601040188902c108060304001030300c00d80c00703412200b101e40303c40d80545a828008020300065401d201000c0e4140150901402117a04c231206051982c1c9100303000160200251402510450501d5122001045000c80c0c4d418191721075605d080040c03110718600400580307511806465280200c0841c615001c199803c80b08a40107541030b0b280400d41c501031400d1100d070300c0d01030313004183d0f01d030044c4050318014020000e22a01c0d01e146100003042450800301c01541242c4180b10741c0c0d50030110660010b0040c2078420a850500d072300340e00e64104000a640001030002d02c80303504080109035616100d1080f41000b481c2d60b40b200690f810204014040480000c01280f220310800c4e07229560843e5401d4840030510913280c4014210405102d5414640540d00403a605080707901c001840000c000340e09842 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 39173781 1250 39172531 39172619
    0x80c061306081f0b0c3d0209030607021b0f0a030209060409060c02031e070c150c05030a11241302010e040c08011701090b0f0705070b010e060414010305030a050304050a0c 75
    0x1107400d07180f20a2800c1c2c20801c0c811b0790120001206080d0f09029641407900d051120343d114031000d078040e0481d0292905413030100100b030400f060103801d0004e2044040c2d221442c94005403074040790304194550354000090f01920850700002d10950074003586201c0103800202801c40c01d8600c5008800700c04101d40c2140d03250084107005003e0322901d000c10000031420b40c0345142c070000719140880315442580ca82614661084c602003001401340c0340210003959042c0405203408044a0030700030040d03030303000000440660140540000d42d120798102d6045a000e00c0000700e1500000d0014815651100b00103080d4100034442e01a07031b01d6a1180c1143d643c1010304c5080307000c550107008240ca40e04d511000c0501054010418405c0c40800c2142e0b1010840c3d088845008140382c0c058031105141c0b40040c0400e881181480500d840c0c0c41f2001800003e1001c000d42d40304042130b1502e00e44030f41e00c50504e14641030f90224003400040341210017052903012040d08540b4003510900d604c118501300071201c42141 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 39175031 1250 39173781 39173833
    0x3050d0b01020105060f010f02160807060f26130c0902030f01050d030f0305060a030f1104060602240402010509090705030610050306031f11040807080c061306081f0b0c 74
    0x40580c903184450347d030040074088011240707481140e6110201c4400369180030301ca0707080149503030b1220108200d4190700242c00b09692040346411082040e07860542d8035080301819020686a1404000502c4000000c440130f00c02a00700346110241c0356158075171402584250384011903907060318004619418030703c0d230502860f54540c0d5074091000401008400601d4050301e09684008680310000202d28a05061074109000d1031801140c02c20b00341c00c10080750161742c0b0440c1550007401401d16409260803c0320034104154400312810b680350b00c01240d0300e00c6200b52181c2d0003a10b510a210003680c1c0200618032613082602c612146917400b60084d02e0501086407145c0e415441810030900c903d082000c80507406c95a800003088107041d06207901c0b0150800d4100301c0041e07100b9481004800d1040240c000c0f00c03803003552203514120724804d20000c10711141c01988184042c000118403920001c0c0d00300c0b0603000b003400c2c0000e15a519160700d480b00354025116001c1501c0b070001c02c1c0c1030070010703160356800e03007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 39176281 1250 39175031 39175039
    0xb030102090d0803040809130c030c02060105060a05130803041e09060b03180c1023040e011208090402040f061106090304090b040204510e030a0203010903050d0b0102010506 76
    0x2c040c150303807600d54a6000810864151100788402841da8030742e041829282c2241e074030081150003401b00f0040840300c0e00841c000c2103511a03001042681c490030100c480841403494040e960700b154800b002c800d402c16a001c551a40720000380080c401a0800c0e250002c0780d103118802548650707030001d00c0c068601e43c3c00307404400c480810200c1e014001d06401c075140080b01c40207848030610210f00091000f20612611408140c1c02c910b044c911490315000c0c050703019554158103080c5820041294010074050050b041c061308441e4070b440034032043c8002e4512295004000755074032600c480c04449031080703500c203440200340c1c001000280000017103100791040741c01d140154181850403103c140604182514187c01c20342c00c1002084d01c0181302049400d02c2005142581c80c03401c0d42c0b1181c544104e0710702a03650344240150001d5500d290a8501c203007002c0c9549440c48800011000007800d101d101000298103620b0b0004110030103030450064000c3c008000800c1200c1c12080d001a421b840003221500d0380 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 39177531 1250 39176281 39176299
    0x60f0906050f0105030601210605100314070f02030d020a020304050f010509011e03060b040b030f07020304030c030210031b030902030c2b0c050306011e0f0303020c0427150b03010209 80
    0x10710351003000913540c804014506607508c211210181e040c6c002444120107001c40d141c007c14007603400c00307c9010300201d41d54941000305903004080c00300030100c060f000c070041140c400386540c400c030310070800d4582140158008542d41c64145801942d03a501c9441240c0c0a8258104165403544c092800e0703803050381e410b0315007640480004c0b040d0000420900502d109150381c2d0391001c203908070403070050300c01341a07043c45440d580d08140440d4810783c0307001405074086500401c01840000d0140100008599054514000c1602942000c0c4c02a004046681e0303a0420843c030080d60469041d04000c040e90300036820b0715189070091080c45580c180f450b0320300c02d4000440b152880010b00c005071150340140141d0401000c0c9032104c0009040603420383c040d00d5521451144a4004076140100000410441c00e00c403c64078a142d40107900e515048007541e01c02d903a07810448501c040d21541018166102548600c0070070198a0224183e0b00c17070020f50b6031050b02d484480085c80c00c05108a07120500000c0c44108 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 39178781 1250 39177531 39177559
    0x30203030a11070b0c0d080603010f0c0c0605010f030f06020c1c020a03080606130527040308040b01120c031506090e0d080906220c091404050f07060807260109060f090605 75
    0x1211f81e8090031640d055940c54401110890715803258612410740742c2c0e03884201c0a01030406405a40060b040800f6505e1680c00c2000044c1d440c000308401c883c1d00c501d000d6291303500f6442140c102025101003054602800a20b074540d5980400e600158038800d44030141f00e5111601806a6801201400d242c0701905120503c994a0324001144081c845c2e24110042c202185a1100b80f14005460880106030f88501780002c0006040c6024050852a114002c880d0303600e441d4024654003c1c403001c0c04008000d0003a90441080382c0011000d8080118140010030700c00380352a540c1e5046518034400a218600411222400450100c0c010001042481074400d0704414a0a081b00ba050302264401a00040061203d5640c080c501181050b054554218941420014241700303010940e182642c11100d810710a86400083c0d940d00a04c2d2803034065502500007030f01141c00d078201e40c400071000512380000941c60030581c1141d401d49101d0381800032003c0d6103884002c16204036000e0f40c1e501c054240300d001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 39180031 1250 39178781 39178787
    0xf030b09070c050307020d080a080106020d0203030a020a05090406080303060f03010b1f0c1208100506030709061d0d0503070203070501110706080a02120a06150203040b070f050106030203030a11070b0c0d 89
    0x181414000e10640c0c2c03a102c8582e0004c6c4180d141010300b00c4154230f01041e0140c0c0c05400420140c010041800906005120340300025101d202c02006d100c41141d01040205016215000391011000041c00400c10103440e1070109640f5001110400e2188401c50701c203210b141018003800b030a015028104100f4032a0401034501201e8800c2020020401003039010b90102c3d03046001c0c004090107130345410801d0304104100e06003014090300101e009840c01c000784480550b204600c60100d40d0030b49800c903003c2520303c0884e0540d005805200e50305c4070010100c0303030a1140100c010061140b0880440d10300d5a9220019100381d07002240c1542c9a400c645800c105071801810b2a0340d0100542d04010301e00400c410804c0d14500040d691012101d42c0c3d5a420300010f10b103003240d00070442060000b1401c0c246065200d044501c034866008000c00342c0f4485550804c10250440d5001e194014241e03a20350441c0380008141042411045046128106000034038520a50481d02c07044d000101529050520000c1a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 39181281 1250 39180031 39180047
    0x50307080f070812040b010506120f0a150303020601050a05040603050d0f1b0305130e0603100b0a0305060705030a05010f0302091303022d06060906030a02090705090409060204060f030b0907 83
    0x29a21207004100420020380b40c07100a20000580d506a4103c60038941045500300005030440350150070200a08903001c15459459035111300920600302d4075a0312819103501410840c04000310070540803502204060700400c419040e80d05c2030b200624000d5540042000380c6545100241851b044000c844500f80c2c460141c41100700b43d01d0420305681c80121109104a180c0380a05900148000c41e184000415000f180d0b40100010440c80419040000c000398039503130322981c01001955030300425803007500e45032220710082d03410005036402c0b460402d00140c0560b20032103903681001c0c0b40100205000341000c1910080e40e8020301010459a80e030440840405055081034056100720020034015264242c50a144030302105000103003145002101460010050503036445102100100061514006001040710760100d50740782c450f4450340801d4170140310700c0081d25005803c041d24407040c0720b42030300144100e41d590307a00c031202d509420b5001c404442c2c01810541d405100000400c040300d10070114 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 39182531 1250 39181281 39181297
    0x306050f030114040b0c160b0103021206091c020a080d0204180204060f030b030309090405010b01020d2d05130b0703110604020114030903041d09010b01020d0207260a0506040b0c0705030708 83
    0x80c0e8a49803d030442070311f22911130741003150580e205000500031401c151042e48202d10b4003000038412401c2c807000745a21084e003007080e500724149604108414501c2007111409580e0000d003045e075a1101c1da5400c01c0a54800d0040102c0030b214101c1c603140060b11072081b90103c0390300b640e0f509455a10b40c03904034040c0c1840280c06a041c0300034020085180c0d1200c03030b024000da02c11000040c88041d1140003a0600c40407154810501c10014845400380e40002481440c070111015074070618065140240d8190180640004072012102d8010441800c0d40d001000000c0c080d88901d441401c2c0556441e42e00c1c502210000e00180a482ea6140b84000303040146400442d0032041d00e05050325017030500000ba01c031905100c000c05c640e1092000109080c4070320308190400788090700c030604001c003010795282860f116142c140340400e86012520104250b0200001c40840240d654407c0d40341401503842c0b0b810340b029035010b01c1800c0881c9031fa8005404036111350360301801460802900e80c40e054120b40100c0c074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 39183781 1250 39182531 39182551
    0x90b060409050a09060b0d021c050a140303060a09020309100f020d020d0f060e010b07110d0b0f04060b0a0807050103050c041a04090e030304080d09110301020a0306050f030114040b 79
    0x30011030030a1040c05168491503200400245903015410250141c03214a006140241524042c4501503114221891807903242141c89009001440c40c24625049032400050048070010421182003e40403004600800c400c85400707507080e440d100410120712054070255410380c08810154030301b080c1c0313401c00d50803004010300050521910300388040c142d0b884441c0302500d0585da111190700b900305500c12000905000541c0d400c2560506c00020030a1260b43c1c4080c006840c1404000300070741d1125090714004e82d000300c14107a20f007003042d08910003402c02d5400312100c2e42004501c4655040584040301280c1c907510040031090b1406005600800300a8003500c64004104000708100e0801d40d10340070070f80d68022100b55510315282c0718408840c00000c0504042c1c0082042c007003c20003600559403082e07240100001c0e44d0130240b070703e43d413892840520150994000300e0b120401035050380c00030301292030545176210034030035040825080b03c000c00442501c2c048a0400b15001c20034051410f035000079961 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 39185031 1250 39183781 39183787
    0x804020f01091e080f0607020c0d060f0c050a030c11060a0c09091b180605030c0a030f0507030b031e0a1e050a0c0501030606030509070302060901020a0602070b0610020304030c090b06 80
    0x200c50f004201016554165802c641d24204001003041240880c030303d4410700545100d05008800030f4a0343c5290506610800c5010509028054640c0c071000d00c0c001c098108010001c0480805402500b100b4013040c0407a203403c40d10340740a0300800c1500140ba42c0040074040f0342c1d460700c5060004201c101c0c107220411103e000007280a0740b10340b085c144206c000d610802401d1703a094000030003c4200d442e00043c84040d01408000c01c0d0b401100340ca41000700750071816100c1240f02c4003100105054040d1114040c184014004540e42541c019103010600f130301552441c40880e0450302580990721035480d680c0d0b01400044010500c0c495042462450300100281446400c2c0c82d102c0c54002a18415154914005c504100d03560302f51142c4c10082401d03040500007880c046010b20b0700e41c1c03854400a802820300081800e816032081c00b40c1200c480c4d104104649842035810001c44002003101d09070b009540c201da455100c28000415502189d0b44030402d486514206002030000e0285a024160886814 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 39186281 1250 39185031 39185039
    0x8070203040f1214031c02160506040b06100e0906060a020f0d03060602150601050901210e010e0c0102060f28050f060102120a05070305031015020303150406060804020f0109 76
    0x102089030000d19003071600150020950804d5844103003480201c034410351080140011282d142101042c41ca440400c005843d03c2c00c400c6140404206004010300500580c1b00704010886042900c0f8000c80003035594143e003002c007580540b0180140f491860303209101d0800079149180150080c9414002441035800c07010b0b00035441442c4c200100280c0d008a502c50300c041c890307580c0c100418000300c19444600e00141c01e046c5c0000e0200d1140d0b6145170b0401000c002c44a800c480c0030f2007050444610404100140c00142c03043d00c0c000d104e01c0c03104403024021120803034050b40c400a0482d003d02205a07da900e25150344042910b115010325190580d006d00140d01c280f1000036205680c420f107000c00c44a9a02d1600c02c0009042441841c4d0100d07502200384103ca030159481030907900780b030340c0c0740c1402c9541e516801000002c514040e8070500848500a0030b81c003000b5404070286000c0e07041c1940c50341e01d1015800400050f0f8516001d013100084181002802514040c00140310102040c14900c94043d16 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 39187531 1250 39186281 39186299
    0xf03060103080a0e01030c09090f0b03030c07030c050405010f050904050a0209070c120c080a030f02040b040b040f0f05060f160501050106030e07060207030809040e03040b0a0e0a051804030807020304 87
    0x4268010355152402040346280103030819410a000382003461b04100c4406185d8000e031031202e86000704103a0765a1202c0804a41c2044d034040844140010101d945030030802a1440d40c5110501048904061811000407030f4142402514140c60418100c40c8a076030400060001c0020010b100341c1c1e2907c9004400005600e6088406003e90299980c0e100c0d46140341c00c02c02031541240107404204041161038a001c2001a0180c401c00901342c80c0101c5c034440404412800b80c0903a8014040a000c0002e00142d851030110052049820040c0c2c407a0245036140b11406032400130340300c1e094001c2410001000c544044d07900070300c040380e44641d400c06840b4a90720f44030300319002600864046542c90029814802c003c00601e0010805d42c030007480d01e0fa00303507a1802054054581814040d5803124403031140c10300140143c0300a8882c01a5a80d12a854248018101c91094807168050300d8811000304460800c00034100403662840b00f012410b0b1195982150101c0000b088401140428000410034a003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 39188781 1250 39187531 39187543
    0x120307060606090e010608041a0621010606030b1507060f02040909050d0201051302130b060c0303040602091c020d0b0c0906040b0405040b0f030d0c050304030c0603021909051c020f03 80
    0x2203a46007151241400c513a11940300040c0c0150051000702d000704400100c1c0102070b20210407200c644514107072249004070700070300c2000a400c00d01c2d090000280021550561108084400c660750074019000c0501c20301034884003054409240c100d0810003080440e90721382207006c4429070901e005180c10f540d0541d000403542c00c994111103d401060008082d02da090164682001c900c0305480074244403680000e04001e2859061402726031983d02c0744e201139840e00141c80740503840f07400b940e54a241ca031812100079404070108501c61200b00f140031450903a0b800b4820030455001d44001c044441907261310090701402000804500000c009050b841e46814010b00010000504056191414801080181d6014100650098240420704c20060b075002885007034103103240c102008901c0103402c1c000c0c1913104a8202401e42d41c0c014100240541d0315600411840c90840400c4030f0303022040804903040302051003600d40c03102c003c0c4a594070185550000c900b160b8402440b00c1416080c010209003420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 39190031 1250 39188781 39188789
    0x90509010902010e06130306201b0601140a0e0a060312020a0203070905160c060f090b15010c080405060901120603050a0b0c0403031e0e04090506060406080c0f1203070606 75
    0x41d44544401046580101d20300400800481d01542000d4440403164121540c501c0003414003600e40c0c060702d808841800082000440e91600315a0302d1003007100c0040307000e0300225a07401912a1000000d0036100447c6061141d501c01803003c3c509500c2c2021101880101030122a41b0607502c1b2000400102c1c002010240e02e800781c1c002d00341f1285180101401e01005070302604200781403100f0000210000c0c2400c4040e140340b420303c4045035003035040002c0107010006860210300c1c5051418014441405206407007400c2500a81c80503400840c011554406c10500003020072070b01f400203104500d000c0300034001515040c134010000e803602070380d808207981d0b07240d000382d4864018070040e83c1400140341d0a01c0d40031400b00c5105203403d02e183d800a110428801c1c0c045440900d107824a080c070303031090a141e800312800070014425010b144c100b05403110400d03502c2c03d108505d40580054036490224404007811001420240844401024004c80c5803028040401174001003000400090040c422070001d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 39191281 1250 39190031 39190033
    0xc0a0303021c020a081603020a0614040b130c03021014030a0204050f19092a0e01121808090d08030903030a060e01210809030d11060a0b0307030308070207090509 71
    0x50746002c081061503641510000210b40100e500300c0c011070006001c4501416040000744918843d5040490511115480003800c460408030306031403015001c0b50041c0510300542c2d080800d5100c070905c2c4990490340c03a20080454014030004c00c0076140103104080c210920381440142261600c28100c0c1c02c5c0d00072540c0e0105540d0220b0240154105001d0140200c00c00759505441000c8401021202e2041c92140e00304054a40da210740c20b03007111050701e03c241c410901050446904440010f0002000404130b280000c180e20304d00f2054408ea40102441281080c44944003d807141d220b81c60107a00035069103400c07c82b8200017000103840080194491801c140165032a410319850403820b03143c0a83c000c400946030f110060100381c0806000c01c80d0000c0c41030080103d44500d207004805030181e100c000350306026683c00200ca541d08803142c851280e141310301399240381c0e403080c4103442107402e550314207500b581c040002400043e00074414207421828030b0044420a40e55401d802044c0c6030110354801031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 39192531 1250 39191281 39191293
    0x7060204030b0609060d060b0319030302030411090c04060813050f060405160303050a1101110c100501050a080d051b011805150606030604020703140406030203011d0103050316050c0a030302 83
    0xb03000140c000660010300403500c0f0f5205040680c0081c4000d8049100984443ea5070806410565020803040500c40c042040046440980341000b400a4004413010340f01c2d1070590701c0102c014600b11099510400030900f15504090a00d03108030ba800d036000b005c0c074007a0030b1112191404500200704003100320270301500030100c515040c0351036070030003c180c07002c844c40110511007440060b07001000e950003500a80f0b4803610260341d50340f0b10303800760500241c800c0040400084060340000c010446500000782d144051040d43d90304d8081c4041c509685c0b00b0b4003069000310301102a0a0302c07800052550000e0380c6040707240440c40700d14940c05c40d0100301c2c001c4501441400024100201401030903c0c000050301c50a060b4a48000882d41609c40140480d02c5554001080700406020340c800103800c5081242c2c0c01c0d00c40c0d40390784000d0002c0d8002c0c010751410030120450b1036001d072800900c041c1a640d0060240d402d20741c00e040f441610008034201242d040c06a02007440c0f9580b03c216050300114025030040c60307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 39193781 1250 39192531 39192533
    0xa050f04031406010314160501080705070b040302010c0e031c0c0c08010515040c0806010804030807030e07151704080403240207150509010b01020a080a03020405061809010e0f0a090203030f0706020403 88
    0x10146242e03903a00d01c80e040304850b10501a61007c201049400a080084041d624410b0031189032090040040c00001171100340001c2c961705505c50082010941c841c0005102c0e05400c00d81d440e4a407109490035000d440e060307440d00b14454000c40600700c0c842c2440500c066100e0882a0a40d2404c40b01d4035580824080003010f24906802074507000100b82c01e262010341405400241841001480a01800b00200104441c0351080c0c5c002c03940c40c80e08400b9a41e0309038070351000006c3c0c640e40c8a010710014140c09400c26018602c900504e01550740319010700d192030300c0c40e968038031140c0c8860b0310244040000107088650000e10b0000f8900103100d04802149042c2d0022180101c03500034240e0450380c1e03d480703502d14050b6000110344400c10b40011019440b40a44441103000c2d101d41d401050300300c040410101d041c2c00204140b001203150132141c40c6010707a01ca2000c04415403048812001205c2c00b1004183c00c0d251650004210f103001400f074a103000c09640c80800180c1c48020125545540098204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 39195031 1250 39193781 39193793
    0x303020c0a060309020d02010f0516110312040806010e100e0f0f01090c020c1909090c06030c2a030207030b0c070510180320240702010608030a050f040314060103 71
    0x20000e0b1045050410030650607801055609101c0741c030080c14480003011142185024400703448009035a4910079440880528044410a940c51002c0c0c3c060301c50160304840f030388100742c242d07001c3e262030200618241e807030040c520f400244081c0c0b48128000781e407807000c07403d041102c0e40c05200b002e2012490301c0a040130f0444980b501c005a111084c0f45192440e401d27682035002c500c00361090003c80f01c00162040d40c07690300072305003415482540b65600c1c0464040c1000b02074650b0300c08071207a40d1001c000800341040140e071042541091034801d800b5002d2a0a01c607100d42c0c0c26511141d001e48102c2d1170283d2281c3d2a90814501564120948400801c420042000404c8480070898641c6001c0c801c1c07803106007120302c414584c00001020300000c06212258111141c5980c2da151059608035070b00c064840c0a400054003440fa205a5a1099400001c0d21280140103d808603003100002b90300c3d0156024007207900c0d8002d41040342031030000700400004240031f200490070b003c2410740a419503524501d048 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 39196281 1250 39195031 39195049
    0xf17180c0f01020c041d0102032707030b01061b05010f050105040b03010e0c06030402060712031a0f090601030e030412140d0216140409051009030e0a030506011a090303040303020c 79
    0x35115486180140100c0d0f40d01040d1800e05500c1900d002ca08981e486080800d40c00d004801c50540750310110400402c0100b2003036880f113680c042c0c4040c01c3c8600035010110b032109000d00024042501030350040102d5885080c400f500c40e00c52003200314440055555072803c3d0362000031114903083d190401406246403030300c40c189192100f20000c1006441d4048581d882e0000c0c0e10100c0c0c40781c1030100009080d0b455102c21125859448100081d42c00f03d081806001409420024141035410700b03424031030b50603c501c0f566650176000381401d0040da54600114080e00398042c40000c2404148000500d84c43c0b080c0320312003414420303409144401c80b00f210a501c2c208204400100315070004035200c004084c01e0404006440c4550307001104403003150701040c00380034181002003503440744007040010a8403503440041c92074441e541e11010610420200f2290003030b603006c09080341c0c2020004004107001c1050182480030555405400d0a0048000906680150f03206034051380080403918581e1800c1415 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 39197531 1250 39196281 39196303
    0xd110313031808060114120d0513050406081b03031905030603010f150b0f0f04030303020d0b040209030d0309050109020a0f090f050408070605040f080f0406020f030a020d0f1718 78
    0x7100010b03d00080e140c0d6820381803040c0d50114200c000c950380c06440b0150001c2c039000d40503003182c0c079034400400d00400550000c60444400659440c0115552a05010f080c085814060003003103072051411603040d10842c445004d075458441000901a4104221101c3c2460303502616221307180e00d000c1c0185807d40c2c00e404800a0510300e0665090075401a1540c4030041da1007001d1601e44520340f1644540c82d0b0310800d54810800f07500032500104150303040c2c004280c1098078400c140008004141032000340d010b0000419496001081d2421420b07101e41c1c040403690740200000f04140b125a004500c24013003d42198119046602c81408500014000c0d400da5420043c400c0003149056141c5440f43c1c010102d0040245807940c02181c01e2104000d0394101c420781042e200c0d80c0d00c4440c040e00542c56030186c450407000d405130007070842da411004000c2c0c170004500341d000740900c03c400200c11100c452208001e607040c0003207001c0c0704c0039400020103001d22803039075001480840e1078400e03030b002c4c50b11103e500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 39198781 1250 39197531 39197567
    0x20609010506030a0f052103041b0303021f15030302010203100617073b24040306020913020703030c1719020a02070504020705070f0f080307080d11031303 68
    0x20a02c40c80b5100042d01303101c25500140001d1222102d8641107090403401d8051840541c2c800803500340300d500005c01103005501c07900d886081c400512000036104881c910001e03002d0380120072114404560040c0300010405010000200010644180f00c603401c81d0740c02c00d84c0181c1d804000c020110716800082000790040e810301120305103062081e03038410308006140c18104580b04401a001481915500740081c40303901088100d02da05001d0702014030041e054061189151010400d041e0310f4129541400f603c10380a503518041c1561114001303903001c4803074913070892040c2d140101c9000140c4060304001c1e00c0f968020640310141b041c010403150f612641046401069400c0c06100034480783c44000d800c41c0c130400540c403240420403e0b800e0859541c8a00c1d00540006449000c010012030360030140c460100c08850602e844a025907459492030240380300039803007001458085a40040a01202c0d155400003184000381042c2d00c600326001540d00740030304206015030004154010288514001041d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 39200031 1250 39198781 39198791
    0x306050103031733030616090605090913050c030706030506031018020103090314070602030f0a020307090b090a38030603030d09050a02100f0f030207080d0c23040602060901 76
    0x1000b01360b03042e03c0c1c4012085444c0d012081110904001c00c000100c078000c01020350740c507850010a14041302646505200016080300c90101d481070240098403c0080c01512081007031f80e40e170300c54101045520109442c14800c2c1d1408446640e010800e03140540b049950201e028285402414030300080c10250403109400c0c14404007030801650000d0383c0c110b80918011503d8074035804c0644111212002100580000080400500400350029801624a0311040c44a035a40c00301c1c0354201c0c00141c4504000542c2002c4c104a0740688102400d90b1440003451168155550310b11585120f103000000361248104d07214a03080c050340076408110050080704414510301d89080082e803244100c0402c0640d5a80d81e00000e420321400b0403080b000382d40c0c00b900071180611004000751041000300c0a1360009030f00c0292500c080352103030098603115684000803c2c1441500c0c3c01c0e1201510380c5c002c50b00204480780ba0307843c201c0c0c2145a0a440f10440c80d112065a0340d0814800904201001b402220603130b040c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 39201281 1250 39200031 39200041
    0x318030804020607020d06020f090f09010b030c13050604091a03011e090303090f030305060901080f070e0903091302040501020c04060f060507020612010303031406031c0e0f030703060501030317 85
    0xd0103900660440d0066a034040d2480080c0071611200b20241c2000d00c08900302c1c1c10084607000804000c1401c407a403903900d10f248820020444024040c1c4010b400c41440802d909070589409424096140001154281c0c0c8403030200d821500143d10100c0950b40313903c400182c2c010b20686a2070b5503c0b05400921501103135807809904041d00d00c42c50300e135040c0d03104080d80905119902000d0b06942c09490400e0a41084c20700501800c400c1d0b50442c8141c0c20a4000190a0741c005146022103003800042c10740d403485c008074040021340080041c2035a020400564200c0e40e140c071801d5000741154500161100c1c18240020318181005001b240030b5840d02506100c0f100807202400304541581c54804c0d520541071000c01c040303000e00300c0e040000c0d0b1507210002c0b003010741642141a24000d000d10940f41560b41104140d6114a444910154034000300501190300c2d20480702c0e001c1c00180680002585212940402d191807420f510076981d559583c4014420554000320601212842c1c90310fa840034100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 39202531 1250 39201281 39201287
    0x601240206190906090614100303020a030806040e0303040501050a0c05070807020f0103090f050d03050c070f110f06040801020d0605010908060109050a06030b010303020607020c043b0d020a03031803 87
    0x1902ca920500700300e07503580d2082150b80e04020001580030b002848000818030703100c4054440081c8042400c42d9000009056141ca01c000d2821640c0640c000c1410301c0072500d0503555500050b142c02d402680b00c180200700c14a04100441c0903504ca5000005c2624298a1500c210b804014507201000010000040401c03e03580544019a804445001d5000c40c41001a030082c0b1200c0401800c41c4080c100a0082c03040119009038038a421f0780f42404a95500d130b400e0840c0d8842c43c0c1c00141200704110050000c6400b0700c40105003060f024003000204191080000d10540140e031000b00540c1d00012800c8100510b8003941e0010002801d04407101c900300b80b08c25440b83d00500425159559800c00980c0d40c54540e00b202000b90b401c4000301d000c0b56100d060094481034100ca03158050f210b04224215541400c0c07250b855640142d0025503481040e5120301c00c207880000b4000c820584041b010700441031700038002406040410b40051416002034a00a030a40301d00f640b101e001040d0060352203001ca07030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 39203781 1250 39202531 39202543
    0x510020c060309010b21010b01080408042c0c0405030f0313030b1302041803020c0d0209060f031204091508011a0603071701030809040b030106031e02130e06012402 72
    0x190803074001d9100d036104032001e8010412060080c0d8048a100a01e01462400c1030402d480c00440900a20454000f9001502e84030400d6030000c0c05000104400c000d04200740811055010705e084600d51000c04643c034a020030303103003070f00c01c100600400281003115140802100804400c01005541452850f018951101e0002e12010f000300004100141c0d10400d0344c2001c0031002d034000c2003000113a6000d00e00c500f0011543c0c0c0110094071540704241350354a44040b24030709060b4000c0c0001c0361940d03800c0070f000e00d4030201401c042e0140301d00c0406c1004000000050000340410020006400720425565400710720568882041640342c601103520710100c000d07500c0c011307001c20f8030200c0da01d4032030b5182142c250304800700040c86208200000300810200c2e100030450503000b1101849440590010107080743c00c1444000e14142c0c0002d9240030b40b00c00040500310b82400108044101c00c01e82d03104d101542c02244103803a440d00550014030000500070109414070401e94030100694003e1000650b60700e03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 39205031 1250 39203781 39203803
    0x40e060609071803030503070e010305060d110a05090103150b0d0507060318080307030e060c0412020d0303060810020301060f050c0a031808010e0307051509210412050a020109051002 80
    0x5950440080c048500502da890101604001c482c3c00c0a59681002002c0390000d848230000242d404124001542c401d004050107610000c0c2580f83c00e1401d650b1344086058000703182600600c500e0400191a520100c1c181e00a5002d0003040b00b2448944080004540350200114480c5020729210b03804070310002410b906030346090074006200e101c41000781c0c68450b484000102a80d0000080081003580341e005504010b03040001c9803201d8465200e01020341c001d5000303e11046d8203d40c83c10016140020706071b91214040e04000580d5615071720b0385030a00c485c14078146d0400b60008010000281d100813180d9803001c9624003d0b040a0040a4058981084a401500b000901d0444511180310700100740003c0800ca0020400c0d0400050529207e40040800f51840d0103203050075117010a000f00c0580c841c0181202500c3c052140f051000e200541c02510b030015402e041c400419240702c2e0503124900240a036008191b0007003244001451002243c108900800030711000c02c43e110b4000900003002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 39206281 1250 39205031 39205039
    0xe090610170102270a06050a02030d020906040909050a110109050a090e0f0609010608060115020712150507030f0f060f060e0d02030111030402011709070909020103090501050f010f05040e0606 84
    0x1c0a86280203000e4002c90000030b10a030740c0001507500c8011020600c049070001130718000351259686400340e803a80074000021016800401544045400c50b9006140c140801003e00341030549a0300300e01c08982c05560201c42d95800b031800c000511400c0d2900f042c1d101403d28050722400c0c1030501140c04400c00d485014056078079030711403e900300e1061255001221200d400c44100b0b283c0241101c0c003070302c060b21070000b460046c080041541c80d025500ca8041d450103030020804c092900081c400c82e00003404094900306540c12001030841c0407401802c5c011945650041360340c00c128400242110709105445014929140701004000340314a40c41040b142c0d02e0038528a500a000b000c01c90721103915100039415440c0c91180c611020212000e140918000c2c1e030b940d400c684141144c10703440041902c025015601410302040054940c0d000310031614818940801d1401e2203135141e80c00e4850581c5d40c13021100e080001408a107000c04410300051404850038031403807103400201d94a4000142c00e03030b801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 39207531 1250 39206281 39206309
    0x1c0909020310030807030203071a1008150f0c070c030305090f060702130c050c03030a020d0507020a0b0f132001030b04140105040b03010b0303040b12180c040509070504060605040e090610 82
    0x11b04d0300900c20b842e04aa00308234440c0070b0b041b018a4000312440115404030109802c0740021a0815001924504c0358001c00c0e0501c0403912034003c0d00c128a40002c1802d40c010508020f0000090002108030b00118800c0c0c44680e2900310200801810354241c022043c0a02020712403440540d8030520008000521f80c600021217032151007007251a4810001403e070144000001d0040842c41d07076000f0500b2118240781048980c0343c054080b612040b829801401804e881e0000c0360b0405580c145142c2c003c40f0381848a1b4083c40103a441181810481200003040f60040c0c56134542d95130107026203450200c080310308020380035922003004808501070248902450381c4040c641c055880c00d40c0a040c0d8120018212510b40c8d948400001c1c80d03602c000e8503a001c00c00c1c0e40010840c142d400c0407070b1039100081c4101401c0a043d55506000080c040100003201910414100060645641c413460010745215079a180d542d508102c140803024801400000c1c04d50f010004000801c0c0340c0003014429203e0003481421 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 39208637 1106 39207531 39207533
    0x30a17131418011a160210020c0102060a060b1b0102120c03070e0d0f0f020f09070c03080f0c03010302010c060f14060306060d0b060d030207081c0909020310030807 72
    0x184c3c0b050941460821040684d01070300d290801c1c19400b200e1030105400081105112400c0389000d600005064002c95a05010441e4414a44203090004510b01031458003607200e501c041402d2105540d00c5600d80070001e404a6000e024030300c0c5104400e08007403009003090341c4103950500204a00c0180c0c0411403c2840709a050710b82c11030400a400e41454968226103610300704201e034051010b00f10007401d03644295009003c4e50702556240400000b80c0b41c05002d1210182c050798941ca6100100f24016a130102102c0c1940c0d030a2a041c00c0c81e00c2140380c0003010f020300c0c1c100c03102c4242c2000b45540211040510f0103120701011001c032070b5140c981905201c011440c40e040030b8030a5080d100011010b0410030790740007096100c0d02c1165016991340c01c0044c14200355114441140b01c0800039190790603881150000501004201145107040c405a904030555a51100801d52180800c42310 = true := by decide +kernel

theorem cover : BRFrame.Cov 39028781 39208637 := by
  have h0 := BRFrame.cov_init 39028781
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39028781 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 39028781 ≤ n) (h2 : n < 39208637) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
