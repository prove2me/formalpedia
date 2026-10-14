-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0551
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:24:21.222848+00:00
-- url     : https://prove2.me/submissions/f70de6c9-c81d-4a5e-9bd7-3aa836472fe1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 98920863 ≤ n < 99100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 98922113 1250 98920863 98920867
    0x2030105010b0a0f03020a03020d0606020303041a010b0417030702120a050f0303010b0f031902030a0204050109050d0506040314370e0105090616050610030b01140306070302090301090c0603020a030e0f03 89
    0x207107134150000c0d04003000750000c16909200e601116001449940040c200035001140c40c0c0c81c1c20718007807800314030f220b1410082010310300040110501060903601941e4108a10702a000c030b0140215280d80035071080030b54454034a5001141c9100007043d2015614080e005803404040100301d595038910003031080711407400c410030408000c0c83d0034001540d0884800380e03091145060855001c810b0380c100340e4000030410f600080030083e541c1c002400c00014442600c0c401ca00d401c0c1610355a03140c010041c00036091040300840140d00c0c000305d00841c2d00341562581d955498403034580c54010301460160f0000c403018485001d00e00c1c5580512020204020141d4490346417030b503610103011464006000c5094058101ca440100203803082c807865208030481c05031208a1031450034408911001030b44665540b50041d0340004164a000c1a0168098618140035a440d074080e00840d004024050001d0002e039004000410210b074150028850035410350f506009100040b00f50b6512014003c03600714580c1c0c03003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 98923363 1250 98922113 98922137
    0x702130504052103180a02030c090714030106030204051005120c130e09010e120313061109040c110c010e012304050a0b210112020d1e050a02030105010b0a 68
    0x21541019901900c58030540354441a100307041e0342c03100c0581c0e15030304000d03401008024240c50b20006940d02c00051500030040180c1c5500483d803100d60317050342d06000340180b000264020f401400c11040002d28203448580e070751b81d1510010001d41250044900c50717079105455242c0140b00d24142da41c40b65501141e034030651558041446140d101082600320480c5511000440d07405141c50648681a00c0001190380c03000310a040b41841c81200a100e0001030a10911442100c07000c150403c280d4404030005403070848030f034140420700405400e940e2180c2407000303860210b68045450241c410060007141c2036001c0c03840040d2031038100c0803442d80c0054800c035540d00a028244952803400d00f01b40041c50301c0d10380c07154003052018049401024102c0b4002481508082e80c80420340009240660401c000e5410080d0000300702440600203403146024505079024040681b00b0800c40b9003552030a0400d05a0524107983c8030668103078168071039441c0100009080b003140c0201d40c800310300e5a980c07180440c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 98924613 1250 98923363 98923399
    0x90a0504050303190f090605100806010f0b1303060603030210050603010b0d081303141e03030106080106050a11070f080c040507051c0608160e0a1b0f05071e1203020702 74
    0x84420200a41ea11409184500c2050b84aa1b640660140d00c02144034640310103a040004002d500c0000300d544014010010035110010002c2903c00c14444290b0b00c6104845862004809810281c40e403441d0400c0001055000a032a00d04a11103090a00035690b0345010182268074500b011500101204d002c500080e001c00e00512403450f0b250501c20714107444c2c1d103840c01c00150500348103085a0240d8084010304100d004048036800b4008000d5140d581403c800038a4003c06201384800d00801140c0311030f41038000c20070f41800c22000c0f8220b4480d5030b540ea207400882c2000703201d10201c070b0250f60840340b424245405038a01c1000d240d1a0741d80707892401c3e495004c6001882c800100701c0c5981e0000810342d141d080c0b04504148200c1c20440000c0e41c200b070320490040c18040c01d50315080b032406100710740d0b641342d44000c48840352141c1004202c2c3c5040107003d5549110f0380c6030041c20701c00480c1000100450100c0c4c0022107a01940300703106c818081c802d066040388110400a03512101000144207821 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 98925863 1250 98924613 98924641
    0x240504090204020c06040506040b0f06010c240c030b040f0905210c0609030d0f0e070302011206050909070602060601390b090105040b10060804060b0a03021002010506090a0504050303 80
    0x303440604010310f4030402510403801c158058034215000d80011040c40180514040415003210120203d52220b06110b40040c0002c404400024044200c07545030442c18140c000004101c03004603081802003140783c40c03008004120319041c0b54403da142101c460102c2c00280306c3c101d07100d035211000f070030000300c051035031200c0030107504215120440c20442400414030501c4440d0085040c81d0045485419060100c07050340d4000b00d03c00c000900d07140807040c422100040050440ea021b0a1103141280f038645600041d00c032641065411140303038014400085000201201103580c19800d88841da114000119801d5110f03605185103030201d42801800c2240034114030000b00f00080c40710f4501a407551b60801564400c481500142e5074a004000501c411907660681c040e04203841e440c035040c18000060039511014101420342650340c0600741080e210040c00718095a001421500d022400042c0203010309400c403492800740c1c2c03a043c0495220b0303d0a0080501940c1c0c00802741d400c694a090164500d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 98927113 1250 98925863 98925881
    0x810030506190b03100c03060b030f040609080910020303191107060b0102010b0a3503180d1a01080114040206071e0b010b0c01180c06110f1002090103240504 69
    0x3007035403280f400c005680c0410655403490485040400d03442080381d03018040711403507442507060040820030031410101120503254880d038400b09c00030344d43e40641020078140c01140354050b045809a00d103410515000005544034440d40140ca20a0000200c80360043d60310300d4414032184213061043e00d000032299001210b804006100000310751100750001411080e559029415080c403070a04a0083c0300010302652032016070815440b07201008550366640ea1150318054031100c44140007102c110783e1403000705e8000e150000108a44114420707a1080818000e01c64451355600e0312940c90b00002a000b01c0c14840e5800418580c103001868480320700400c0d103440071560070040a180c5d07800082e0b0104038a8081d00780b607200079842d11030320707000903007125001505240341101407094400002c0010108100392030f5203140034042c0b4140080c0403440c02c00b0b1290510040d00688600e601e40400507806003441650903a41480400303ca61014424131800035054000313005000c1040c40383c2d0506070004501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 98928363 1250 98927113 98927161
    0x30d020a0308130606090902030d18050d050703020402041d011a040b07060e10020901021212150d081903060e2e09060803040501090b040b03040204050a0906020c0d0810030506 77
    0x3c560620b0750355030215500e5400c6050304075030f24a0400c040d428104120300741101c443c240b043c4ca200311400c0b10740304c10b109846607501c240d80f089822001c0200030b00c800340045902030005e41d12591680a2540114803408004110800341c80000601c50451207105014030320781070715a85428104060350000341e0000d1025145540c80c3c00381c43d541480c00b0007100b4118010b0140058403000c1460009007803100b004200d040ca020f00b4030000b1002285078081580203030324000c05610040601c408100c010242402c0a044c2000106a10341580201c00000b4840382c01c60fa01000700f40d0303c0e203070382201c030900a8540c0da01c494200d884080300b1000711000000300076201d90301e0124075640c4003007540a032803050308070031a640c0011030100142d50300600400d003d004040e250314101810101c24a440c0d000081c0080d200b1070701d41d0003003800c83c4c605602c4000c0c801d0300b00f44195511b02540c4a40d03a600c048681c034060005100d500010741c0314044d080c0d50360549502501914054851003294204c0340e0113200c0d0990 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 98929613 1250 98928363 98928391
    0x160809030a05090405100e040f0201090807060e040f090503160b100e070c05160f0807050904121b0c120203100c1b021507050609060105010c03050a18030c09090b06030d020a0308 78
    0x1c005d9102e94007d84164490f2001a00c28580c81c400142184000d512000ca0b5911202e011b10145d85c1065048038490f00a81e0001800111003102c034010307090308a009400d07800000354600c3c404050f159040d511500400c0d02c0d100325280c07240f2510501c0304030701c20030b48950007140c046034040e84145a00d808050082d803c485182e0b00140e400702480b24030750310601c128642910100000031040c0403103402031004442c844410300d80741e10342041b040c032030050f5002004503031100700301da060b0b82d000d101c081d594001036200441500c07038046640c00d6140ca1410303403281c4521248102030704a14002c40318403660381c2c0d031402d1440020f1800440c0e86240c4240881c1d01518061803401d22440c01c6007d071001d9402400107044a0815210003420150181c01a41c1006508900307440400d40100446002081c1c519155180c045508a03009400030070b0b8100500e41040100001802c980c2908480341d01c0c2e0007050101c9054803050f041590700e82c2c01c0032202026801008400d00400c6c000c282d03503540f100071004210 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 98930863 1250 98929613 98929619
    0x50315030a141005090d0509010c05030d0204060c0312290d0b040809092505180307140f060c06010902031806091507030207030905040b0117160809030a0509040510 72
    0x962040101c0c00002c01607800702d0010308000541e402136541100d840c0e0040e002048040c03d00030403a10a502c0c0040c140a14606584100310302001140c03480c140c0c00c141151625103550001703100c405000e900764009090260841d035004100e20400d42842e140507086884803400b14550003600021007995a0b11001d160070f4400802c101c102020302c83d034800d040d0326a0b5500741000b000b112182c0582180307450a40b0b603400a40c488421a80c00500840354105191210000c424980741620340c43c100c0e5816008442c0c00245c042c0303400841c0c0b4100c010445400868000c04411322466000d0090150b034182e0200740100030001880e030041da0400c0b690081ca040b80b41c116512589014020742e0040103503449040c00c01c00a640d00d69103260803601d41e16082d8907008003510020b180581c01e0144601c215500e4913140c169070b01582803180302d00014505001145490702c1803410f0400751016103030105040000113468280040202c0741e5030070054680506003007022003840014040148400d0803020608004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 98932113 1250 98930863 98930873
    0x801031122020c061e0604050a0902060a08090c010e06070b0709030f0b010503010606030b0102030702090711010603032f0604060c0309060905030a180609050d081e0301061106010303050315030a 85
    0x202011942841d40541c1d03d07001d4203041440c0000c014201c102c802441448404510300725000075400c0031088401080b5034aa640302280105a1004002d6200700c00003030b400c01840d0401651440b0307911143c10794104000c40001910b0b03400f070315112154408000c00c41000010140402e8540000a502e4200851502c031758030000c444038203c4041e1461480c41d0b00400080c80d007405044098034a03440c041c0000400000007070761741d001e8100003c0c4141c1402c4001204030388030b82203402140c08540002e001c3d00313039030341006416201e0070800d06a2a0308800ca0300c00c02442400820a9603986035401401c0543e1030b521090300401c0c0b80c85018003010b44a0740d58402081690060139020340c0142c01841d87c40407042d00c041c5c4020b2071984040030590301c600741000002e03049010341080f1a416100e41032007275103034640000a0300c9160001c04a45503214440031010340340001440c141e568030f03140c0588a120001a030f6540301000d100080012b0810000110002034070b460f00501a42c020f400c90f00009150782e50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 98933363 1250 98932113 98932159
    0xc06091a0403051201080703020604030609030e09100e010b04080717030d0218040b0a15050a050f070f02030f010204032613090218090c09090c070c0f0e0a020a08010311 74
    0x203074000f0781d000c18869488580500d030503004000b0031000309001803440d4081400c60095100252581e07036a00c440c84140340c013541d124010484d0040a0789503900d020854419080c0c2c45001e290309890050001050540c03010003160180d54070b10004010051901d0300b5100c04800524030212240020301c4007401c104405d002520884007202d81d803c005030070f42e41c00e1000b04c4074204009407140c0002e003030401c07030102c034980016440d5210f4076000d0360b222213003a000e4070240300e40390b441090004005450400d0180981e00160902c2c400c906481c408001c1c03862245c03e0303004d640400341c14518800d070704596440d50400d4155102c40d00c0824982801c1c2d00c200140a401919070080303a943e0340009480242d5a48000f4200707030700c481100c00c0015810000000803050045054950003946920007042d01d00c4501415681d03480d40c4100c1a4101a864403c9480788200c0380c402c1207070303c1c1c1c40800842e5881000d8004d036903082c04543d54103509a1310316151300300c5500c45951101c0d080224096000356901d45100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 98934613 1250 98933363 98933371
    0xb0d02060f0a1812031b1a0a0b060309010504030f0206161d04020d0509010e07080705102003070506060405160e040f020a02010207020f01210b0a050d15060608070c06091a 75
    0x10004100b0782d5411701910045440380d441e554207a0754080350f400900c3e01d00e60720149500c80481002590b40d591030140050200c0341d00154020404810402c1040d41508454490b81c803a64902041001c0c0c00e0090b139548100751400c0c400e12800c2c40001d40442c0c4100341c1e1800c091810186a0503400882000c50101c1c1d02c403980111049172a0010801204024040c3c0c21110710030500402c5094640088241c9882540c01164407401000c254220f0305d03446002300481c04041101c1008241a08000a40e9690b01180c01106c05014840025101d864180310722446006620079400c18207503c600d04079a10003030600e440ba407099031560090000401c03803010300040807441e000141c9c1c0300698010000c2210384104014100640145426104218249038400c100e03503056011400d00c0400c400125208c14503000780b60082c0e440200c0d9014480086c40d0210706410303a5104100440d01c1c0d100488400300708031000301c08100c1402c0f004000500c1540440c8405014088511500098076401d10741100d0603a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 98935863 1250 98934613 98934629
    0x1401181e020f041e20040303080a0f02190e011d0121060f0513050c0909040f021e090a05011406180306130b011403060417120403030501090b0d02060f0a18 68
    0x1604c2000c80090344610098030502c54079a81205149500c2000544030b1408000c04202a00011030b022007203a80284101034549442503440f010160201070a04020a00d00800101d81c601248078035405601c3c0c49006c1440301314180140210b90005641408117401e110f40f145e0301e0855100c07000d074410711544000c2d29003039070740c5008a4604810441803000301c0d80003107003d51034001404900030880003240c1008905645185030ae03925410b106c0790000300f480b00a5000b0340203403000743d24640540c0018030b11100480b5480b1070740d2140340e1000125442400743d161004901c001000721481c1c40d030054210070220402d4a00845580c03c042401c00c00182c80e00c4003040e5602c4071032010040c020001038003401c005002c03458441c3c02c0f5000603940d040003800140042d80002c040e42044501d04045449000e10300344580881c1c14a0300d0010300411091080042591826494413058a007070307038075010f403030303800410250400d40c035120143c1c1e403540b00701610340c14011240510a581c20350301c0950310040201da = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 98937113 1250 98935863 98935901
    0x4050a2102010c02010b1e0a0b03150405090a02180a110403060204140102030c0d0c06090b1005120d0903060e01020412062a080414030d06031401181e020f04 69
    0x6500082d0030745580003081c0c0c0c00c1d641014220348881e1100d130030f801c003607001c040700070700740700c1d00d00404030f54900f540341c100181c829400402c20605200c500b8203601075450640d810040b130717540c40c011107445803100311000b54841800c403850108150b180c3ea5844d0003068514000403482d000800928682c2c1c040e84c01180c8641d0049010031410b5141c0d00f052052100a002851600c0c040c880c005844120960300801404420081501800007640c4507010300c036070003000d901b01070801080c81d00d40c051203446014851944070240304010340e00468000d0b01a00d030307a00e030150101e007181d4803403025090b081080d812565003800002440c0084441230760040c0c0c0507910004007003a040102ea0035482c5a54100b80301c03105518488540c0d60360110985510607005002a5040003942d4451707400e41c8070364813004024508200d40801441480c4111030141e071041d100810010300c1e03409071f4482545410901810a9040d4106200141840507816400520041c0b00c40e0b1807012200000303040f0b95034000c81c80340c02020303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 98938363 1250 98937113 98937173
    0x318090c122d0103020a090506030d03050705090405040506100807060f050c0a0209042913030f022b022518020c1b041d06060103090201020109050d0c120e010203040e04050a 76
    0x306d144404003500348290180000d282c900c002c26138178450418200100f40d0741d840000d144612441c1502d0501100800c240054185414519a180e60966034104060380d94a00016070b1300b00080c01004072010342e19010301030740c0c1220060762113400a904d007403054041d0480c0c19005981e05060184914810500c20b103694080d050402c14151400c50346071305200401c030501c4803485446801840040d80f61400714100b50b05524200d090221a60400c6203c140700360403c070380e01782c06c1910108844800c0c2d0848405104464500407200444640c07124001ea00007002d01c0f60500d46e10348081c050120110140c035002960030858608606001c0000603920104411541440c0c04e01840b270311404592051020001c810000c00d1300c3d0900a0942414596280184c0d01164002c1d080010360a070404140e40300d04030940300182030b0564005c012110320850300c0d9000707152801007881c8050001c060740114209810300c818001a220041d009680c0c501ca426018000a0a05480d040700301d01016142c04490308 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 98939613 1250 98938363 98938369
    0xc1704080301081908040315090605070e030c041404110316080123041203021602090406090c0e0c0301030b07050408010213061101090206030c090418050318090c122d010302 76
    0x1c00380d031300c4042c00d910101e0b4480105040409071000c0e83e400910f401380c080e5109140342c00404c0d00f114000c1c203050600342080303407854100322904030800c410303403e0b41c0307201601301d00304003c0718500d0080490b21140305000c600441d86a14404804000107011519400707000039010b2580400d03a880310325941e440391540310110300e00008260241e904030310080c41c40d0520b0317541e48140c0e12501480d07808069000c200391aa4a04c02d4208803907180e009440030689040509105000d0600903c0551343ca000d5004009954800c0030310f42480745601d507140d42e00310703402c1d0340d5460381840003c4c000904004080c00081400760082c401440850074984d00035040d286889406003400d128071000040c01c0e450074a030307000582c943c0421294400b28070141c20b0782e01c072407540004000f496042440301380300c0409a90f8104000d0000001e0904110000000721003203030500030803a904400b11b03000d403141d18052000e80d55103403680312903c4d08500c0030078041c0611a460103120024000602080b000340c4600ca0040041d41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 98940863 1250 98939613 98939623
    0x21c06050a050109080607120b060703080a0501051f050a030b040c050318070501020703020402090a0f060c0530030604090506090106030311060114010f230903010b0301050f01090c170408030108 85
    0x90030300f4284c00092030f00e400c20752114402460702081c0304501f129410103502561003400c4120300106115114000750400518105089925000540c680f60010489240030a0041c0808480da08940301da0f9901e80d030210344941041c504001070585860440300503179030358001c110f05038a0a0303541503103d14104840380201e510008603811103800101301881941d07800300f203134810381b501030700c4c0503075140b0020300401c0080015520500440520540204510f5486100122100d0240c01150f4aa101c25841d2099403108000d4001582200c41d02c1d101ea400101405180e11450090001a20404a07140c041c1003c1045651030502e0355500e00070b1003010b4001c0c3d19850308122506c010292507041050b10401a80414a801c0c14405440030103174401d0310039611001c0e07030120709a00d0581c810510070b040c4c805411102c180f510035400d090f0210a075040520446110b0fa0301c041d1115816460040c481c0000c04e41c8445180030441100400c0d10f25103080000743d40030b01e02c10440d503a6079601d0040043c0c100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 98942113 1250 98940863 98940869
    0x9020306071d15072a1511060703052d01170a0b010608101202060a0305090313080106030308090105190c05090603090304030b0702030712080c041205070302010201150308030118021c06050a 83
    0x30040c02c1c8030b82804c59048110710002d0310038100c0d4041b6039101c2943c090f0350b40c06001a803140e82c0d10951041003100c6074550041030054052070380381e95000e0341c9101240c010b40b0090302c19502c002c4510b801082544028288001e50141e21000ea034910310103901c40001000b400d800040100300184e09100c0118072100a542c01003ea07004464119011540012520300c540300c111010945c96001142e80200e09200b04ca40307a15201d440c401d01c1e41c1c0d65449141c0a00030908c000c0c3d01050700030001803861501809441c0c0308490844003200c090744140309040040002c00002007c004044c021311001d6203030b0000440c000c004a100542d1114614030340000940402011074085410500048000400703003140c0045102980c140199141d498145c0c0c0e841382e002c2c0d644580300050248480d08180300011030a80140c074003c1e8004d1040c84030b07681075001c1c43c0013148001001024204010081c503000c2c907201a070351400d0b102c80035291203a20a10440d50550402d041d82d642a03451038100664030f4540c642d00c0c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 98943363 1250 98942113 98942153
    0x9020a0e010e0d170705070807080c030d031a040908090d03030b040501080102040501020a08090d0804061701090e030f1c0203010e160c03050412020f0301050a02120a09020306071d1507 81
    0x142c480d031640c0740321048141d20141c03000024046000785c1082003d001d64405445003008850038140c1d1511000c0c1e56040c803542d0140607002e03250f2186c130044d10074020f482e1400070000c01c4984c440c0643c030912000f014001019103180100344002500d41c1d58010b017000c1100d00a031f1f0041036078144402000202e50060b40040901d030f20400040010744d8001c140c400e001a0019001910703a036003940862205070040500814040d4005030202c0c40c0c5400c80400203c0c03029004444085a8803a02050100e8490308107914455100f4024003141e110158010310086030041040c110010394641c2c010203a1b0404e0f04000b100904034002c0041518009400e040892450b180c6100700fa204c40e2809001c81c442c901814a90740d100281c0c0c3e43c25519810140300c840400503008109a2070084c690074000c1d00709558610304100410041303540f04400d0302400c0181d0750014040d2200d5128108180c41c22015654421008014101d004059640740040e03c02244c041842e100d03582c4d4100d1500051170011340310a050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 98944613 1250 98943363 98943379
    0x301060f0e040f0501060b19030b130c09050a090e0f0d0e04022503031a090415200406030c0e01080906010b090111010905010e12030c0d0c050409020a0e010e 69
    0x2058991100120080321407941510850340c07101d042282d400b585111014100d5800c1010000d4548103480040c508a40038507041c00c1051107a460071000e881c400443c0030340c0046280d0441c020445161f0180100d0703011030400140483d81da01c0480c1010a50383c1c000b40d9076607590040f80c122000c1c20710515050061000c0035001c8034110400140103501150700460043c0d50200d01f01d804a80c04100e2091014504c0320403301d00c40d4141b400a0203060014688961080032554082150800342c001d140181d070720401a40041480010307800c02018001004225550819038000110903603200400182c001a60b010540d280141d40c05800802c600e80d2040c1005588420001ca06e00049149415036041d0340c00503588907484401201c44551100d1314500d07552828015400b001015440700c40b4403542c807010307213a0008170000110400d0000b110203440e201803c01030b22031109065030140e82d92101c03600b0300714201502c441c190b03412038128500c807401203803102d0400812580c100344040001c007000c4500036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 98945863 1250 98944613 98944619
    0x1020d0513060e0d021e0307150e0607060b090a060f0b1c0905030d14010905070e061e16200a1809020609060307090e0906070e190317040f05030106 65
    0x100380482030b00c51101000305506201003141d5070503031a200361540050907800c04265041c0207403249240041211300ca8840c00000040400031110222805180c584030b420404569105201c0154005e041c02c43d14140d071054400900d554a5200c64010b034240440003a0050405413040101005a0046440710909001040c0860708001d4068100144043c2c007081403143c900e0098074500070b144255150f1400c2003a2404802044100d45049030082d10041c803058564060035200988880101d40c0c01090410040e40c01000300c5110300480c506070b1200b10318241d200d6111802e403540b0584111140580349203a16850020f90301c1803400074004035040b501140c9014009000640e0002d03440380b00540300c1864109558034101510100301024055a580c0d29020340300a104060034015001082645004245d220000213980341c442da195072200b19540700710000304400540d040140c0c0b1440300c49250302000207126a503280031991400784016403207034240b40a141c40314500c0d820280c043d0785450020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 98947113 1250 98945863 98945887
    0xa061d010608150103021908030f071a01031a0709180501030302061005090a0e0705060705030a140c120f07050a030801080708060c040e18010203010f030c1707060305060d0c0b0901020d05 82
    0x8541140e80c1240d0352102c8003647d40742d440c01504c0d80d170301141040c00f0200300700c1000521000200300d4a840f034543d2600104840740c0241d501d00c0c0c00c3c00041d1050903004c0d8040030400c48000e036103400507000d04102c43c03459601d1040348600840034908150850301c071801001015010403c6c690003544440103001654100400304252901c0280854085a116030706500c1c6550184003c0700640f07030150046a0b00c1039141030082e030f2a80804130001c0020b603039100c81c9942c2e2140c0c800761960300081d4070207404a001c48852a1400b90410603038001c4018080200c800090380c20410994400d1081d102c0b43c0141d8902106903040800640c04010150880c204100b84003885108840c251402950180c40d04d480b0941001e03884c1448a00d10480340d0b100100200e603090140701040d0450b803003120399810300794070f416200207a44507048a25069034000641400554001e402c40e9034403103805800070070115602d0b250003003085125031122030844000241440956070600650b5804c000c2c80c1480c5191501074010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 98948363 1250 98947113 98947153
    0x503010207051c1704050d02160b04091a041805060c12011502190501062301050901390203060a060609140102012910021f0207050a061d010608 63
    0x603445070740d0f02140020003c1c0c01107040707049136800f020801d616450285451951880c0100380300004d0b1241055011840711608404400c1c1c4e4008010350b41000e18100440c00070b418204071903081c030b800d51000e4100540351485081c04410084500c3d461424007420f225082c0322015001d4100d0081c100281c004203600c8102d1641115051502400c1c1d21950a008a09000c41c00c64501d0701480c0300004e100500c80305401c248183c88040e1011000407000d85280c040d8a0301c1800d0303550200300d0511000c2d110b0b40c01045d103c484150045900c282600180c8900d080c6402c1e901ca04066044000d07002c04150f00302080304c03643c0241412010880c060070103502424a02092141d0705006204402f682c0d040e034802c0d0091000803120b801c11041d03403070448a081514500c0c001c0407901445281c01040469840003545c500401c070b541c450b0144014050901001079071110409480c68421103409a0004565114060b6403022288a100000741d00610701802c0d56580d600c042c0103544403078404041c0c42c0c0500c078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 98949613 1250 98948363 98948383
    0x10e0114092a0a03050f13120e030709090303150305120307051210150938030106090e0108010603050312191406150c0d051303050610030b01050301020705 68
    0x1540401e0380c0d10005184141407075025005002c100104140300046040409000000b1640c0c90500c900e030344008505104400403505c6050b0300c2c80044203c0c0c0070484400482405203030f285440b48a9511032400b0920b0128a64800c046155840030341c0402d1551503c0b84a01d2010310070000500b80e0325544480c0c0d60350301c242100a602c40c40000100e540c0c680200121400380309050006c0099280110300e0700400d010794482c0d01107050000c5c403119580c41c4188020b01c01e170b42c0c0d00001a045449401006402070680171401002c0501c6014090352009952010310700800365561402c00312418000b80800c10344042c0c3c0070518982c1450014000940d0200542d00404807501308040e0540d9440c10258145040a00d907569043c0f41107003003e00ca0103d03112080c82400103543c0440105130b40c1ca040c10b0180728040034032166800c20301007140828440c030000c000c000e420500c0c44080c42c2e181d4462904014003035900c1070314403008140820401903c000042d00402c8114003c50805445403121900c6000e16070b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 98950863 1250 98949613 98949619
    0x50a050d0b06061201030602040303080a0b0901090e0f0a060b0f1002060c0304020d0b0702010e280206030604060b0c0c01021606050306150409091406060f0a03080309030d0e0a0209010e0114 83
    0x40019203142c0b0b030b0b5400d03900d600e95142088545175a403802c0c6000250701c5400160005100d60000030544000741c02200401800500075825076860001c40c00c00500070369082d00c001b4000d0300745880d10b1344010042c9003c80790041d032001a101d070f407d80400c00342a1100b140305001e11045100203030050780100310780b9809215120344507078a039120320015810090481c80184840002010b12420301e90560042d00020040710807580503a401e030200b00081501c00411818200c40b113030020005040c42c0d0069030300601e0140001c540035488410781285500040c800701d4540e441240241310381d613030402c5054000b010101c60305400780c4c00c0140007011840024156801280002c003910b07201e403200c0c0700711001440810300030001d207011481c108500040b9640b4802181c0316280104400e843c1c101c07020035100c403004102070401e920f940d49844080e04001c0407035983e4001480340e91700507001c500401c00d04101d0355000d00000c00052042080780c140c10b0b00100c14101982e401070062861381048203000301811 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 98952113 1250 98950863 98950883
    0x13090c02060402010f0e01030902060a030c08010b030606090d02060d050403020a03090e0f13150c020703020f0a12230a112103031306020f0a051902010b01020d0c060b28050a050d 78
    0x40c2006238040c08040701c0080d080a0000745000b80d0592507400b0768140501c1d07648001c1c0c41e990701d10300e081c554001607c1d03d0384e2082003006541e40a282c215406641c0500c05010b403400c00c8070855048003110805c403815800f5802020011341050780c422000005088070041d980c025013030414611075402001011000380030f131150400310502808041d0340080c04681c54082c84801c1e40e202e0025145d1041d17110482c010b01290040311803502d0003010f200c058500284c0c6110031100c180d1102001483c102080001d00c5105008580c5402820301c18076820030f010f90040918903d070368052008130202c0c080e40301c034140d84410f4031403030860f4040110f9400042c5040c8005011080b410080001c1c0300300911581070038400507002139540d4112000e080701010b42107500005003891030051703082c0c4010241c52030050f00710311145200c43c0d01901c42c4120043c0a203e001942c001e4407008200383e941c440c0c038802007448180c82260102c41441a5900141c0b405481c03469007507181c540070448407012103100402007c0c032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 98953363 1250 98952113 98952137
    0x37050702010806060d0f1e02040e07180b0d020306180f0103021306212d0818120c0418050c12010e0601031109070302030103030c02120309040213090c02060402010f 72
    0x5407010344402094170a4100b01580e8481003d50003048413032200b0810224000c003445164204c0c0c804d6600319450700f10346070740c582c1c0d400c0e20465041d4104800c200340480c1110000c108284c8002c05481883c100780c000603030702d08001d0304014080f03a585241041e090032034004c1241d40a4905805811254162401141c484245001170050302c0c1a07003200100108800c59014500310800e984455140508010003404805003221070103415030304204030341c5400c607900800000d00e036480100701a1006400302e10140901a0018810401001c1020f42603030010744c860342989070610030355040310344407248004021039a55609881c0c101e0048010f12440c66040c010140e40000e40000b0515801c0d0000e4507a907684078500b15821500703401c0c2c120300170300740c03140003d42e0103019108990580e900b40d11225144181036080000c0d0311015800c50596020511a0514a4996002071300e80564000c42c8885103500304012541203074103002103001154401020320000d40d07008000000d0f00d80617071400c407018070a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 98954613 1250 98953363 98953369
    0x7020d060e16030c1508010b090d0f0302060f0f1006031503020301060e0907060201060b0301141906050d2702060c01150308030106020f070803041e030837050702010806 74
    0x18481c039890a0718000d00e44a888115050050b1000b500d1050194410080c2c0b03459800b844942000741d0200401c410b5001130082a0241c0082c05c420b030801442c4401c108890703031b10000b20840044044000d0390100050282190b03c0d000000d80c000400e82c00503c2c6032600f00b8407900f050740e541c03040000b0700da9120f10340c54a207a1500000809150003400074030050f9a40d000d0044505c4085940c40074a008000012681c5032060003150110350f01c0b40a0a815079003081508400d0003a83d005060307011503515241d040040c40700c03640718010911500c445449103008111582912044040009002200e10311910b60b0406580c0001d03825805031041a11a905604403a00400c1a050701c24801400d6000010411130740305e000b50305883d10b5034281d441e02c2c82c180700c2c201c0e030303c4283d1302401001e50800d00003130064040c0d404140c5007a40e0ba0341c9107041d0503692030300c1d80300044d07005030f840b00c4905188944c10f5400c2c00e81c2c046014540d448100c184000110440e034020f1060003101c40081c10801900d020410b550307 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 98955863 1250 98954613 98954621
    0xd14040b21060f010813080403053405103c0f030207080a0309050a05060c07060c17060405100b0409060608010501051c050604141e060d0302100b03070b160302060a0203090307020d06 80
    0x260703020089034484c94014201c1141d0358440d80d051a12042d01641d8000c0389a03403006080129100034114000c0dd40558a098401412080b090403a00c200c0749241e146160810a2042c880810380f000382d0700d07070308c90408024040d0280f102804140340c01081440c002a50f040c0440d0601c032850b1900040d0790b6007514145080840380407001d4018420101070014002c46a03009200161084004000e00d00545c1310a0350410103285041154940910010f2000e0400d50445a804215200b4110101d03440d101e0300d1182e5001a00411449a40e81c1000c0c800e40b50042145409400242080c0c0e08140d00d43ca40c01303080004c895144843d05032580003261a9440e15004998900ac2561048103586000160940c40c0208403400141c01820500420100d09011400c00d000c941c05034041c04074402007110020140038090300c4030340c26101e4064005030b0040107a002e803c0d10808100e0445c0308142500f40245400406460112103074410410b10a004070000304888103154155203940704101c460034004010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 98957113 1250 98955863 98955869
    0xb220314160c030b0114090903090108072010050f0108060403030c02010f02070b06032a010c17040b0c07050a050109091802040e1e0f0d14040b21060f0108130804 71
    0xb80252010210420440c41d440d41e050720114041c1507504d4126804010b0020000d0b900c42d001504100704400c095482060f101c2e9105d00f2508003d040c1120709800d02d040412054820411a040490704130300000135801519081120700341d818142c0e506144400d0744851001c4c3c0002d02749603880c964500424002e412a032070342981714000b152108500c0c2032998800c102115480d119028030811204042074580e02250644c0c1c841020640c200a1078005542c0c400c0201010b441d00442c6800b07900031416010020405801c4c034107186d179114964010050f140c100c10f170700003521484480005100c9a40d10415030000c5407007052000c2424440455103600804001802075005424508100c001d184005400410401c034254440400c0900054058444200c81c1e0600d0558000c000b0b0441e25138400c8095295010301343c0c00d61468295640c3c00058540d0207420f146c400e20b62000c0d1400c280c00111320a403030340490143c03050203100c0c40ca200001d1140000520320a2200300600042c0d0502200c1e8050b5400303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 98958363 1250 98957113 98957123
    0x4060e0607030203011e14010c05011401140319150f0e0109080903120702060706050601140a020a0b0108160905151e03060c0708070605060d0f0b22031416 68
    0x41401d114a004003c4c0d4024020f560310200e400003012818080e0344000c008844200390511804c2c0340350001180c482c420880c0031789043d9208c00c00111000a424040350007094051030f9125030041c40001d06041191004101030410110b44101001c51060034402541c00707100c103000582c805500240b48001d106010400351203605e04181d91080003007240050603080d81c11011513400c45070710158081244a5003a0080d04150309008501c00294150001500300c5414141802c00101410181a55070400003010300168000000b08041c070901241d001c3c05880c0300d0b0050142030050891000343c54a2034826402c41b030b80e4400c0028150103801203207207901003006120828000500f0349110011803080c000782d101e801000042082c0a01c40c4048400203584040c1031420064544c41d00d00081400500c120342210400343c8507000a904034004944040c42110000d0040c02d1241004080300001401d90055141c00c3c00007401190f081800c0320f40e0580d1000311f6581d01c1040d5031481a14803902a0004d00d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 98959613 1250 98958363 98958373
    0xb01110312010e190c08010e010906060c06020903030708070809040c0903021c060b031501080715090e09031e0a1713140f1606031a01080c090103060b04060c02090a0c0207050904060e 80
    0x10406d138440c03c4241241d45202c0c18202c145d880c0c0001c1c1007120b49034820000452400b03078005002507020340182846800007004d603800c0030700688131050305500c03110044030072580001c0c0c03216261816100c2c1d60911141480c003042c1c96411130340070031102e4403c3c1054000b1000c1030001d52081108507000450020805016200c00c22001448004482400e0180329407a0185080c00704441c80344088450030a45240c0e5403a02d41441c0c8441c01c40800301c041c1c003451840c0002c20260042d0040703228240590f4041f000c605564040c3c10900405080c80c11081c21864084402800101f010780090b8821141e0050700041c00204800c802a10b1b04998050b011782e50300030311417481000c054050344041256503c4d1001d0012420181e40d42d00d5415041401c0d038003250790800800d000d0071030f41002d8201c8000604000030140c1d21211207291680040d4091070010f008100c00780708500f000726600d41c01070f08038a400d010f000b601120203500d6034110b0082500910f0180009010310485820256884004c00c3c00d0368 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 98960863 1250 98959613 98959631
    0x3050910020a0302070b01090b0904080f1608040501020606010f0801050f03070e040803060a0e0405100b040e070e09010c08010b043302060f130b0f070c02130b01110312010e19 77
    0x3d80603400182003601e80c2e002c4040001140072042c058a455050001d050003001d0391240e42e4048140c0004004802e40e07141800995000d21000c0744d111169400f0303902090f29240303880002031506400038078a41c1086001c2c1c64035445990032950301c0b17041d02c0301207504910361342042d00031a00e040c1d82c80e401000c9100d02c5100384000d0080c103200560084e4000d17281c19202c581c0b680c801004035a0151801000c0758030030102007070b031040142d12020384c0960040020130702d101703100e9000c1e140040d0350300040e1003818800e0074007a650700244106d45041c2607506050355a1362510304803802c0c501440c800d01e4054600703550b841d6091103d070801c00c80c0c0421098500c001081c1020402552518101ea0f001e01003030340d4401242001240c5400b024029901c03e024500f41d0303440010a62010101410404c00e001007181e216005a8039080e40d0100145030540c000703600c100704400142010224804440c49400c20440c02d68100076049515040da001138050012a403a15a4640d1030b0541107250152000e1900401c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 98962113 1250 98960863 98960867
    0x10020f0702030a140f0a050c060304030903050a060c081b070803040201020c0d0803010602060c160f11041d0601050f06070f111002010b010f03180b0c040e010f0303030e0601051003050910020a 84
    0x4504007070702c0c0c41c200d07000c40022542699031a041e41b00054201d5000f10f0f03000542d45001002564424481d1a100300c802d0756a56509141100780c100032107249484000c0349406a5001c420254018102040c4141441c2082124009440b52240160501c20f0020024081da4001c0081c103441000151100354000064280048142c1081c0603403801809000003040007050a641500c4905445c0f0035451030240580c2c0d00c1c03040003401d00034200e410403100c950048859541b480317003480851400ca020400300c2c6d02c0204043c2000d10503008148601210140260280c540e00159003072107a0080e0084640a000d00304854000546030708550b21000c0c4216084505038190060034018000780c940c848500310409066003916610703e140740c0c442ca20514250085030840360141d401000c0044610310b4035440b500d503002c044c64260040d200011661000b0000c05074107205005213043c0c0c1d20041c062075418400012035a260240e41101015107445c0030613007001041c0000141311500810840d500d00c00c0501c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 98963363 1250 98962113 98962133
    0x180c03060b03070b09060c01060302042c2103090a06090c0e152b06060e0106120203040c14120d0315050f0a090926040e070e0310020f0702030a 63
    0x2003240c20504021840a06040c00540d28040e6002601803d003085450414042d458108000c40c400c190740f44c035400009a20340344101110001084107482c5200c9140c581506900311030b518041c015408010044221400780e10f0201c0e0707158031800916900d03203507004c041d45003034100d141c068040d80c5410412002c100000002d40c08131420b0a18404255580920701c00d00c0140d00c130001908010001508007011a40719400d90098811689105090001d44c907a001121800c1c0c002c130608166070f03401802545c3d00a0810305080d541041c042d49180382c80d0b80c440d05041814883ea40c0d039484001640c4a0a80c0e841c15911000403241d411034405520b890b8004000c0c0c88040701c01800182c502c4c101090a050800c0303040c031070880c00307015400d40502c3d00c10b000008100c40d10b41503a4030b400c20042100c1464285401e10310101c0c0c280720891300c0d50f00745007007586c1c00781c3c0180c82281400600c404580310350f01c0203c0d0002d030b40d04901c5070058458512014032000c500c00d80e030000f903060141074030007000c00844c140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 98964613 1250 98963363 98963369
    0xa12020f0a030b0a021209012319050108070905061509090606070b091e0705060f07020103180302100c050901020615060409110d060b0c0a15090807050c13050c07060f180c 75
    0x60110513152819520708952810480e41409d40c00c030007107100c0d0f0038600344c1c155400c4a40d200a020442c0407204004003110320a8000004070f800858040100c0b42142c0070740c5070000d40889801c0031401c0308a4550354940b180d02d07002d6011356015000500d07250340308800d0303403903154210920b81628170303145000300e8407031001d801a55261102c80032420029200024584195034000d0500c070300c1c0c21118a502846074100b498201d0400d6110590700b1102c418001e9141c00e99440380c0c00904021100108074420f480e02c03d4004c40070007000f402400320380c2c0e0b800244203400401010340202403011980c003084091045401009915040c05c100ca12100ea070070000b060700c0c04412408202d00e80d251601a450b601c02c4000f558800e510682c40e680224190032481d080f030524030100000c10600c190781760340c110b80054406580c0c507000452401114102501c900740300181c940c100304064946041c02c18011b002e032071409460740f035440b60328503801c0c502070340700b2600c10001000311810302c03425203403a03021001c440c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 98965863 1250 98964613 98964637
    0xd0b09030a02070819061d070f03052a04020306030a0803150102070e070f0f02010f0c0804030e0a03030f051b07030f030909180602070501091b0906050a12020f0a030b0a02 75
    0x30005003041e408600720b03148544042c031018404040fa10740740301602c0407007640107d9075194401c072130309a81c04200220050821030407403c48145141825410000014042041e40544a480c0b00000c52005481d400c222000c981c01038603034540b640480c0c585860702400074002c541c000180200d024080c550010388280903805c54444980b02c40c100754080c0000d82d142c001040b80004010240e5002c0d03008d00303035580319500c00011041c0100105209031030000083e013000c92141020f0109150b400310304141240e5042e42c02144032850346c0d03401044031050344001d008115001c13502207140c005042c418403071201716000b02e884d4140c80f81031030104034400510840114142c004005001d01944c0915203c01214801c1a030b02905203403030300406075001e864110b401d5540ea0751001c000a50486d0115141c000320103000f01a1401c0401017412110160400c40c40b8030362454080284081c100c824104a541c1603808201001d40c80b004a00c40d40c506400c01001d02e43d00d0002c101c2084d045a001c2c2440030201 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 98967113 1250 98965863 98965873
    0x5060f030c0319030c17030601030e030a02060a11041a0406030b120606101101020c07091113050d08040e07080906070e010806041508030705030d051e0a0b0d0b09030a02 74
    0x1010030903680d03200c00316009405811140c0d00c4141c40c2c1c07205840e00b0310740c1c3c02410720310180903190740d506074040803d82c0c12084d50f50f804410300c0341b996814860814122005802589041c180c40344c0699684001001003034402d40b92541c3c0c00c00c584905054070000c060907600342d0a030313201c0a0002c0c0d205811a000b91000286000c01c000080c1c0b6090740400400136404000d02400d0710307110b0600281e680c42c08014000d02100780154860580300f4401001d80d03500f00d90141c20701600707001c82d07142950072050701c00f295003105019008044154881c0308044800450728444408003629020140740a640c1c42071540489500408c1380c0d03d6001120544034005440a44003e03030781d04503050302c48001cad69031914009145078001480b03a0410381d0010300b00e42c02d60b90307000039210341d907245561542e40704886c201d909410208004220000354090070340c0084d410200c0c0002c00083c024600440407005000c2020261034001c85809902c7c3d05656001c1d65801040995851030304000301540c0c2da00030700e01d102c014450 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 98968363 1250 98967113 98967139
    0xf0318070518091015141c0614060102030a050904020c0114010b030109060503150103030f1e050a12060503030901121b170f0402031f060f1d0c13052206090506 70
    0x1180c86031881d01d204800e9174400c000e04268003035070032100c484000d50304612410007009050494080059019114032000b088080892190000907d0040c05d001d0541d482488128059504042510002c040980b40140c40e81090300c0a5030142c0180a6811124260100085403920b45100154141d6a64400521015698805040d40c98880504517500f0031002030040c400079116100c030034100c448078075003107040041c0040e0761403600801e0181e4030007060000401c00f0149800c0640d15000194203102009103628280101f5200e00c80c0103c958100020401c02d0380454025a02ca20050503950740f03643ea00b810110701c06404c01d03500c080161013040c2e045000482034105d80f03401920a40c0e0280141c59001d440750203010312a4010700c1202e10403a201e000100f0780c941e449030200300512072004003030550742d4036031104d00001d403001c1c040300c1c41060304006105007a81d10a0145c1d00701d99040c0c400c880440c401440ea00201c1c0003418420b080282401000650072000e80c02c8140560700032200c3c2455200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 98969613 1250 98968363 98968393
    0x20606010807020c030d0509210d020c0108010e0f0705070506280c02070303080a0216060203070306050111070302100e04380d0204020a1b03020a0302060c0f031807051809 75
    0x2800f81013141d260b404804140d401607c2000507004446c07000d05140304c900c0c400d0242e5500740b0496803010220b41d0040304840310003541040109000d43e401e0900e0401035040c000010100a402481012855003000108108030701c6401100c50564111095401501300600460000050884201d402080e41100649005030a201c1e50038050229001010110702c0d50f601a01c024100074071000f07451b9800d10140040308008848a03800502ca90001a5603141060f0007804071801c9801183c1003140d074145450800800084100542c3e404840c503400403e0092405c44101d08000c808a40003800c0034415948252500403001103005501c40b821100450013003e03034003103600090180ea00001d0b070109540542041d600500c03044900e80782141d80b0804144100e803011080240840c016031060f0b80040038141d0502000790032180a0300c0045c1303842200840c40c11a400701070459540b0144412103108412005c1000b00003c00c009070082c00320f070003222600d040c3c424049408440b18000c04080c128030036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 98970863 1250 98969613 98969623
    0x1a040e19020d0c0e0708010e0705030f040302120f030f1b040311060d0c08060301061401050d020d020c0102041206140c0d05101a0703030b0301020406050f0d060323010b040902090a090201020304031202060601080702 94
    0x42c200d54171142140d40d072001185233440d000d00181c0c1540201c0b80c00204000390034006065610b000d0320f081d0350b80d00309184d1a841490700107082074004000000c1e00c2c0c2da07a40c1d0f480d0840e800c59420140000e010440b650000341030b44251464512001e10b0704101781012a041650b0601ca01c1e0300310000c101180da235408800300301015019881c0010410000d054007080154041d00a180620000504040b40104001d0890344203801001c0940c4032600c0d110200881400780b118003030407410100e503075814481c0003c0901d004076030001c43c2650300c03031000a1904d007080a0240040c14503541008070500754003410200d030b900c203038400d60010381031515600003414140201c80c1120015942e0a01e00365206803500c1a5401c8400b0411f4645d4480c3c2001002c240c102541c0a906900d8108166203060411211800c450459801500035820149440056501c117408254007480d1101b001c2007052030303440101c2c1903110325003000305084160b103000b006032640007461620410003a00c40400c0ca881d0140182d94035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 98972113 1250 98970863 98970871
    0x1a040504031b080f0c06040507060513050906030f0109030806010f0e310207120305070c021315090e03090906030f030d0c11010c02011a040e19020d0c0e0708010e 71
    0x1180c4a0b00c0e91100864200b602c09a403980102460b50a111000c04c2d07080701a880700116a41c141d1001c000e00084c040c0600c64400100b0782d504016280046100d42d0070343d000124410944100d60420005969444c107003d80c400c500c60300d0000b0440f408862030007404804040d1000360002c2c41c06402004024003c5001010118000301426403404405c60056024105d04210b1100360202c021020254a1540003515002d8881c2c118440f50700d8080300010110f401c014040020000064000c00160311360000c2503c161421480c0070034a4240001d160352007205a90002c03a4041c5421024a10000b000c405000c421600f00c0707000c1c00d203858840415030b940c0000c0d408441c0701d030800c018403030b6207030010b034000898a1198209000d000c444c042c2d0280c01c50301c0008114001d07035162000100c222140c1500d00000c4401114104401c03000205096078036001e03200710320284018901580d0640d610424003a85269202005500b1141c031807999a078005029228a07010540c00c03000401e14120340fa10351882 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 98973363 1250 98972113 98972117
    0x60306150302031504020f10020d120605090a0c0509060f0909090c090a0207020117070c110103051506070f0c03080414060a05071101111002041e12030f1704061a04050403 75
    0x2c1c2d00e00c1c503084e443e10081c0a081242d0114082841960b030781ca600e0b1a0281041031784d00905402a40d03500d029041003801071140400b145409004c2c0038540e51007040356040b03828040c000902c025927900503602c520440241d1039200501190060b02844000014000c0f000c1c1911003910035210900b041e6038030300b403031101294007a1008002071b242c607400343e000e440f80c14014502a0465991044181c820440c25903040340094001550340003441140000104c016000380b0b02088103242409440b0507d0f0401d9208600c54000050403c05015188240000b0150880150200306544c4e18101400741d116100300480d1805412103d60513150550030340b40989030b00d444851600c5100d0340c800c0c0c1c0c580519a030340c906110000c1d116403030800d010041100e08021042c801039440e420301e00040c101c68200c00c1e161032540128103061040c29a00c0c441140046d515091014900c44412425104100320554402459801a01308018404030b5003001000d01ca110703002500365001d501c1413000f42c030000c44000d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 98974613 1250 98973363 98973373
    0xb09031903020a020d0c0e04030e1f080601210f0c09060503010b0304080702010c0b0c030a06080c060409020a020f0a0b04020f0103021e030c09030604230604051009020a170106030615030203 83
    0x1c0541403c1c0c0051705050300c1001100d44146c0c035000b034240c2110040d00c0c141e001900c035044903201420907403012440c0c4403800f5121815071002d0a0003d208030801440a810012207260b0602e60002030411192201c0311540c0c10710600c4d14ad0141c00d0300802c1c60b80391103000240c41d6007001800c0f601a1089a040c0c511032007803140b842c0c3d80d40d01c50002e03039404200308034100b2001d25205801319058880341030003141884c090560328104128004295080d1f50403032021030304001c102c891540e50708011181202c80240b00941c07103603e0b00206030300b081c041590440050140281d81c00400c0103201180c1d201c1d5200302c400c0400c03414110011000c074040c00b0300481180300ea51801a044049000c051680000c80700710079481d02c0d8032900030070b08100050b142140c041d00c030001c20f41840e030042d802c808803407060600107103e2886c0c00c1e202d4507074030410074800003282d5a4070024881591100781c0f2010141c51078070f0403400d040002880d01130081030a84020390f541c62515505e121032030300e18038105040f40d8005000305 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 98975863 1250 98974613 98974633
    0x9160e070807200102030a060f08010212061c080f0a0201060603020703020a030804022701050906010509010203041a07020402040e06010206070203090a06080a06090c080711280f0602040b0903190302 87
    0xda2840c0180030b5040f000c2c0b80d07402c240700740303071109000651180b240c0d43c0b0046082464043c98040640580d000480e15034018443c6412075054400290f50000003190803080300c084089101ea800c00790744002820310140015040210710018000300310601e00c50b8001c01200780c3e916000c50480c051054000d00603000000e860300030a01c0788005c4c80d00540020805021481ca0200000b20204002c0886a0220030a8010011031400c540d10300c0e44690b083c2010362400c420300000075224481e9001e2250b1150f202d03e078183d030a0004600356140c0c00c4e40604215a01c907140c42c5150032460b000c0340c1150051280000250340240301005841c20050054a0703503c455040080550b90400001c0c0101c2c0703202e550300800202c18a00b030049104030400c0c0d48035503049007440f02000340800800103202443d54020002000c000d0300400ba000006401e44507114200d001a2030b1402d1481814400904442d00115003c01e070b0000c4a401426070000807011181c3c90385001c215401300c0940a84090090307082441c0c41c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 98977113 1250 98975863 98975867
    0x30813080409020c011103010f060201150e0f0a09020301110702040513150e0109060204062610030b04051905010e0709090c06200a03030f0f02090d02040c050408010509160e070807 79
    0x9002c11124402c00030460b05d090384200b1b034403a0000d030700000703403503a800c0302c1003160790380a210320640711a18504400c0c0840c00d280000100c203c0c007600000d03401422030300141480795180d101ca9102e640c001c1c000d001800070640510720726040341409920035440c2ca004180c04600302c80210705559405094600455840e026400080640e448117032565502e41c039000300042d003584000c0020b01810380300e02c94510406070f60b02c95480b83e8604c5010910548009000b403100032407004004881d4030541005a80c0d60707929001e0f0514130f5500e07490100d060521600001c0040640290055016060482d9501d81e6104504015207041c1000504222134094042c41414450505448030125924100d10449404055a441d000209109400183c0d80e410b030001c19840d04c0c007804034240e00912055050050304e00000c3c010039540070f002882155911580300340603025009540c020300d0b040d00204900e01d4060311648d10381c0e0b0400903101280b0030364031011800c20310380164103028201c25030b1500400d607500303041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 98978363 1250 98977113 98977117
    0x13020d0b150316080715020a17071b08060a360b04080a02070909021819020408010207120519180b04080a0302010b04022b1d0a03081308040902 63
    0x52440c00c0300c1160200d5449440c10444000001507144a181a6500e0481d4990500d200c503000807038840c1d082c0c6e045103c100d900051048809800c41380303681c44003640702d4840c1da01d40f1820200030b000b4a54412058540f03107000c400282256004c0b01035801c3c1d6555402e01200b1a1240c000362050310361410000044c030418864148020ba800d541441010921511522900a4121011528900001a581d00d9142c1c180091002400324101c1807000d680c06900140c03003011403076844010604610001030541000601c1d501078621031440c215a40c03a1649846070103980034410680e40128809241d040c0940f042049030000d18410280040391020440200d1340c0592100019144000c40c1001003000c104d68002800180f040c00000d01503100035181c042d003550201c06201e4400c520602c484014041d4040c4915804802c800c1c01c4c00720440c030a020b5400501700c01c40d48041c404200d0880e1000200000341c2140c0d60790082d240c800003640c4403620200100e03182c100040aa0b04103101c01c11040d00310b900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 98979613 1250 98978363 98978371
    0x8010b0d0b030705030303090d0e1906052a0a0318031109040302010f0f050613090c0603020901050403050109030302070b0a020a020d1d0907020606040609060b0318150a06030b13020d0b 81
    0x4250f07005039a40e203000925582055410440c10b801c100f40b000082a0819040512a101910001c00300d1202080030002e80300300b8800da005101c40020310b0102c0f00500422006542d05403012200d02281c1c0c0ca14159850034040c00c00c0b008124855404022080f5509043e011282d00501d85c0c40501c03565428007000840140c8200d00b999241d12942c0c03124211400b524052080c800c0b00055145000000c0048141d116072074030000c1881c01122202080e0389504140c1924104c2c01c001da642d007087d41c0125420701c501e500140055280c07080540403d03600d9001071500b140107109003460341d2a41c088603c2244500b071004400351f4030000794011083e002d813003070301c034010b036030700d22020b400d49428002c80d407500780488036500180c010004000e039920301840303403c000d00711045040040509000c601e4255101c0a84880e4805414001100801104001d80d44135880c107140000720324106400f030203029041c5400125006581c45000904240043e5035540300c094004210711413022032a294942e258801030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 98980863 1250 98979613 98979619
    0x5030d03020c07170604030807030b10030b010215010b040602060c0a0815060c01090606080d02031305150705030a030b040f110a08060f06040e09010b010206070522051011070608010b0d0b 82
    0x211000a0300713407501e01c0c09000001800060221460a03180040282100a150b0000e240c40d111012090303480342d00e4806992101810000340d0440744d64011f0340341580032906200c90100314000401c45555088c0508200c60498080b50603548bc1c1400c010194000d5884c114000340d0b420000445107450300d0700010310b0100190900d49885014039006081d60f0040600351a803a46400003007101d15420860004550300c02d101942c04e2401c1e110708403254046e644a400e00c03904800121130640c1351070108848006071300c01c04580d911025690051f029022800300d0782c3c8514602151007604400a00807400440c0340304298500e80030000070300742e074151000381180740c106450707111800641d1074680042018040c0c1c140d00c0300d060310f00035104600b503540182d101d90441d00803406028005030003c0503102800e404011807251860b10150041c100107242d0710140d0310401c1c0205901c089508070845114942c103001c10b840d01942c82c3c5c81c0c00d0398102c10a00c10168140d4080100540c024107580c04604a80001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 98982113 1250 98980863 98980873
    0x9041524021f23060306151302070203010e0708061009060f0b13030203030c033006091905040f050f0c0306060d02060702092d0f06130905060405070612050105030d03020c 75
    0x9184169500c004500c82e50303402c80d06800a0105a00d402c1080d41e5001c80340078202d01c1c044040c47c0103e4104403114902891844e004502441195402c0d00103024411030034040f24000ca54962500703582c0c2c40150340115019201d100045107105450103064182c90000702c0110034a480c19410386819403000c1c3e040544140394400103c0140e44c10b100a0030b0702e00740c4000842e02c1d21000341d20711208c0180c500d0310042c4138040480d5803030001c40c550310082d8042ca080b0341c001201d5440404e0a040507003104907900b0220324140401c000c2051800d400900c030f03800ba03021541229907905400e039a4084020140707606901c42c170700242440c509011f01941e180d2010b0301080c2011201c1d800b050b254001234468080300c028092a01803100c02d01d440184400c1d0304400b800301a810f0003081241c08900c080c0c0303024060350f1080300d824600019600410001742d4044111405440e141c10019110f440c3c5000710400180c02c00c40105041c3c8050007494140c46009001c0c0520030302e120410360003540615640e840701e0040b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 98983363 1250 98982113 98982131
    0x80a1506080c130621151217040303050a030b030309010903080a1214060f09042604180c08130302030415020c12010c080c0a080a1109041524021f 64
    0x90000100700401035a01c41d41c4c0f504403400e59600300c03041c0d1124171560007450f01c0e4102c483c243c0309500034021102c03000d1900007040c11501700180300665401d08007214610000703000080562080003070000e40307481d40d400c0112801c50410991603105503014103000514002d01440072400090084c01d500742e0354113200341c01e000d01a400d03a054450030051400000155030401105081640e47c5100c000701c100c0e0010300c0303440c040e900d240e42020000c2d91032443c00040124910f0a940707500840e4041c03c7e520b040c0c1104000550440ea029040ca09131140004000c100400d075030552900c2e81a09140e4035802441c106801c00c82c0d4248000c4076904118218441c03040d43c01615142e1200070181600264008190390715140e0001e0f100003005804c141c41c400301081507600700e030b6004404d241c220b242d1100104048900140b40000c074040c02081075400761810000860610203000283d0440d4546090001c1c815001082e8001c0f200440b000180940c00400040e500e0068030100781050700401000000c040003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 98984613 1250 98983363 98983387
    0x6050f101116030302280314030a06090509060a140601020d0e061306020601080f030a0909090c030803070908060907050609010804030201090b0a1e1b0509040b190501080a1506080c 79
    0xb030345078000d40c0035801c001043c074114021192100c0405121580d804200e04c8683e134020b04145c891961600c0c441c3d80400880c8154080e03400000042c00b83c00b00034001d0781403c0503069151101620b034070110304d16112811126984010426104000507009031010710341c1c41505070341d00203811010680c0b020041041c0d11042d041d400001c1d014241a42c002c00c255810651250b04d00f01d50020802c042e58428440d40078065400b0100380c007503035540400810114068070307000c000d0108075000100400b1000c01004415a880002002110142c4049a140d5210700c4001034840406004980d000710040040000550295088603007185c4640300000d920021501c5500440e482a81e40100480e00c1d1400100850b541e102400306401141600b04511050100054041018440c0b0041886000b0550852507955a44a01004d83e0041d01d042005402d540c0795148403011802920b01080e40c04011405c085124480d0b884c44685103025400703c1800c110007035900c1c01c001491005100c03010002111495 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 98985863 1250 98984613 98984653
    0x2040213091d01060e010b0a0c0b010803031504050c030615070807030507211e0e031002040906060f08190e0a1101030b0d050a0b06060c030f0d06050f1011 68
    0x461007000000c2c02c654002500150074900b8030109806a041ca04244105440c0c0324a190455410ba10070590b02d6492440544151800b644040d00165400f8000260740e14080001c2d0710030f5010048800d00381030f41034200b004885007510b0405107280c0910008100c3d0034400980d40824050705801400c14003c2d41d2800ca5550082c86c1c1100060303008503d200030803040140644403201c9904034058508040711005007061031010001d0304004402c00800c403098001c7c06800c100e01c8000c0c041d03803001040041041c01a620131b20030302c41034074605040098181d02c51003080095003a541e54120251301d0b03803000074000841503000040b44a5a9110490814104001c0350302c03181c3c850004803071008880030002d03044640358050740d4040d0000c082080c000541c0400c00585455019042c1500f13602d880700820300b580078242a44080c0d200005800040780e00320b50140c202c02221420611104c0d031203070306000010f00c01c0176041e83c00000b03680b010341c06580509060f02c0156143d008880c0040220824000c0710 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 98987113 1250 98985863 98985869
    0x130f05100b0906060304050a0605040615030305070b09070f0b0c0712150b030c010c0204091406190f021804090201140f1e0a0c0f03020712080307030e0c100c02040213 73
    0x100d562980c412116081140300950f101e4000c5036a07600354901525070b03d440b04503901e4000d20003952080005e0410030399038444500000700741058120b40e034880c47c019050754015a41602d40f04c1e000000104115070000e84801500d00800480d4440c9182190310f41d0f6940000c214840359008480011501c0002881f035000d0580c042e60020700401440711400d002c4840d030b020110f002c1e8001c00c2e040b1150380d030055a0a03104036416100000d904c407031b0341808454419040e90b41c1e9801c5c06030b0030900c21545000c1c2c48046002402c000304000c1503c500f40b03038008a20444984604401240440c10b001d46025400400024010304200051000032b5000809580c403050360002d84100108010101c5512158100360b08134005088601e410748000002c1c000c250710310350081010494100a5042520134087c00c401041c02500d41342018000349044181604110340d02c00c0001d16040807400503481c0007503079040c0510040e0000710503c2c030340d06d401c43d0074144c200820b98206400300400c1c0040c0c900325a1a03030007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 98988363 1250 98987113 98987143
    0x10e0727110711010c02060406210204031202060a0603031709031c060f0602060c0d020703050403050102160311060708011e03050f0d030b01050301080d0e010309061b020606010201060e130f05 84
    0x5682c55a00c1c140420100680a042c104001240000c0060f00c4280880d41a240642001942c4141025049a41644011014003424008500002004540400b00680161940950f000c40c0c2c0d81401e804200c51440c070000e000a44038000c907100880b900d003081c54109070018181d0340b034010381e080700c2000c4840200e0030701d241d00d958420401000c0034540c1814090041807025288030308000d0341512060180c03401da03050306c0340d00042c81401c141c011011100150b506c03100075034481034140b01c200548c1c0750207038080e0302007a4401d41d42c41610307a01040c6e2520a602c0c41d26039402c20390078010342d154401800b5050382c0e00c1e1101c800003c40811001c10100d2040910a001040c009a03019001820f4804c03100c1128140801440140700a00c4003080300c110711850b6107400880018001e00407409000814406003400e4070f041c0c012205080b90303400020440c22150200c414940701c00004901b00d4855124001d076903560324012800c1910039050b100b1403036000c1d2a828510021540f034090a005001c55481c038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 98989613 1250 98988363 98988367
    0x51204050c19060504090f1506030f0507030902010206070e1504030b012907080f0906040e060a0e090703030c0f020406180f0c080606030604140106110609010e072711 73
    0x154503040325042c0114681480100351945010781c05003182c040c5004900110b03803902c8219411400f02d174803041d046000c540c4130340d0341c06996100c00f4000b44504290a8001403c3c000020700160103400b5800107154107074020411503907030a5080303850034103995442d40e00c0324150103195a620b660324058000340d80100203c2001e0b514203034241138950a006071303400120741c10101317102007a0001400e60792240c0d04083c000e81e8916908403400382d584141c9010390b038480b2022030040b480d000c90980b0b6a208110030b036500032001d922006030380140341045440900300d03404810f05200207440740c450055503d20071780c0c6003400070100754000b4081c1e030f00d03603045002c0c3c80f01c1108001642c40220b0040102003000304404001c00c60b01600018030121000b040c681c01800000003240d40c9407907a90001e04c61103a00756845409584411004220444d101000310f1540b190b8000729211138411b129450368090200010240ca83ca0b000031101050310700614803910760b00d4007e0048468041c2d0040e040385140703509400b6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 98990863 1250 98989613 98989633
    0xe0105150f0405010506030403050307210603050c0301090c050411120403050a2a03030506010e03010c0f020114010807031e08030a060f080a0308180705120105060909030f07080a05120405 82
    0xc1d03003040802040d032141c0e0600f00104200d48508044039001501490819070701e907508002902da080d4240c2c0405070022a1010760b6081d05160703070000741540d214005541000c0720080801d400d0301c2040b080644484880072041100b440e003035001c08075400c800d0f80464203050455080c120013600444080d4089800003e42100090340844158001c0703810850404454102e032004001c16a004403000b800c1c580c1d00c80101c1c1240e80160400022407a005000313111041014400a08040466070514050742c01c00030401d2100c0c101254032416100717004028a0802d25548503404003801c100242a0341c1001c129500340031891800055102e91820000070030744174948265000d207044254008819074110040c3c07038000990184805400c040525a14030121100500030360030325286a00c046d5004100110784011148103400c400d1241c58101c552420b181d40306c89d0403d46a10402c00020160b85040100c0400581208060130b02049145007041c10700d52103036100c01303004905540c251070310781c8861001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 98992113 1250 98990863 98990869
    0x1090b03010b03030403030e0f01030e03280f0e1314040b04020a0614030402120709150509060105041a07031202030c030a0507030213050d0f12180602031306080405010e010515 77
    0x4032000b800240d00640c5800d140d614000e0070320040700496446400c034003180c03c210b40e120350400740301d48140d00280e0341d44a0090b08000170780c0783e07140400c00201c0c8403940e035009020301983c2140d80080142d2982408541c0500401005c2803d0b0f0710180d41c0155100d0034201805480800c55218502c1240c20700c801d030074180100183c96076554800c5081108207509070b440341502a0a42c2c0d080384e4191411020300c1d940790142401c5c24810b40140c0c0305189004428801c20181001c1c14044940588840d115601e40c0c03001110a8401c80c0a0303455036424509601c060099608002c211007130282c80e0000b50303c1e5515081304289ea10035114440c8035100030061200f0035003103129080d00003195003000c5140044500181c20060007078450301e03219075203d40110051007904c03e003c60000b03500000000100c0d0b0f00d02da000c2d0641901c1b00311418002d61040c40414130500001c1101d11307064030260350f450090320305002114480b10042040b038a654942c0c504940c007407800d00030389028800c0e032284a100801c0340414 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 98993363 1250 98992113 98992121
    0xf06061a0d060e010b0702120a0b0702070603050603060c03071202040b0f0c100e0d2105010914100815071b030801090b19051c0c060216090507020c06090102010b0901090b0301 77
    0x303080200f403401004807400310000c44690680c10343d0842c0c031084852810605044110074058211800031003000180b945c0400c4007801d45800b03480c204400d8550703030281540e480045031441382c0c01804101042013035000e0200e400e00044031081c05403030203445a9903544c3d1600800e4032000700500100d00000000803d01c14007140461040042128000c246011591503a940500f10144101061f81c50048100201e052900907011141481196034a4403144010000c46032400034034210040829140c100103810742d4219a1058010070391540f103ca009100040c014041009110b20f18282148682090495484842c003e85424500750715100c06502601c09048103030f07115075200303c12003604c0345101900c0010b6410680d041c204100e00d6803990004002d03942e8010f0181d078421400080c04550002e01e02034400c5d4000c01c00940c240d83c0d0900d5606891080e0313442000760304864903050081c00c001c4043c0000d0f03041403001156600c100e4002c201c550300207810420040761581804c3e481030600b402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 98994613 1250 98993363 98993369
    0x90b010b07050c04020901021509030a1413031106070f1b0b090303120a09050a081e0901020c010c03021f0504200108010e04151a030c0a050d0f06061a0d06 68
    0x108041c41c0055070355030191076018201d41240b00b55404190f078016640708001000c050704204070b185a40b400c0190013203980750802403c850000316219032840440e07038071f40d00307403113815602405031241e05080d980d400060102d583d402d42c0d0000001c2c083e000200300f80481003030070a40501d01c248110115150740340c041988a80061500c0001000740d024143c400004807038400b42d00c0c00c0d0400f10750702c81d04079210191804920103820780c85040e00240500c84034500514003800c00444550006580300c03c00c84c2e0038040e40b02e200303001d80c1000fa0031089950040b0303410807a02e4070901c1524291003540c0d0080304c0d061001d08036030780c42c0f640d100c0400007000100b0700100d040c5152020601824550b00c0002801c40005000b400c2c0e802840c0400f00c0d00b0480b03000c03461007020680040c240141802e41803c80328000d10700000510034440c1d9203059800c0d051450182d0300303548010b0103040801c10f03952203511103e80807050031549039945800003d00e4440101c12240b11452447d4056946c880c00b031012825100150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 98995863 1250 98994613 98994629
    0x60503010f0b0d0b0604060503090d1412060d0204021308070b030103050618070e0f0f060906031002070f050f07051005030708010603240b03100b09030d08130f0303090b01 75
    0x5100039101c0007840700c21240080380d031558a0460700c074203002404402c00d807140c02620115002c02e1007500007001e075100300081011500c0c69401690203c40c0b00c10813a6181015410820608101e2200103690991000d00500143c2005c401640404c00720f0744004ec0305104c1e144411010b20810030203000030713030081c00b25421150965045845694070b801000e400c0f1032110251140c100134686051161900401c11088415221301e85400114003000080390081403c10f40100007031004d15100009038010300c000f03402404c070480203290000003588020010783d2003400001805001403010040b1a6810829401a002562070070341071104880c000003201c2c040c001c0900801c9641c592140b10746044840030302d0041505000001d610a490403048001e03014001510f002040c1c4100002c01103008403070000c4105411075640c80302010303500440c4512581904517001107c55544200d1713426800c00014000f10009000946c2e40c80200032030071000710007098541c14108140003803821407900400307004c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 98997113 1250 98995863 98995867
    0xf0b091b0405160309030908030c03031902071a0c0403020310140924060d120207030302070801140c0c01020c07080f0d030603113a12050a09030b040203101d070605 72
    0x3d040d202e00c0e0740d9490701c6032000301070b07480c000030703050602c20b4170520020240744043d00d60351100461b079140c0341d900440b60052120400d500740c0c02c06002c1842185d04e9181c0041c402c1507807010100100b002810b003d00b807644811014080030000d0380d01808858062070744840000b40541685c2031107081c29030003c0c1051640e4201d50b0100702104c8268900c011486c042d0081c1011640d2400002907800c1543d0034050818005a401c0441c1c040e00000d0b52429640a07070226010150343d0a5540d09840c0d0380780c80a28071004500118a120030303800003802280d00a000003500305068280302502e030a0055110980740c1e80b00380c2d40311110b0f030002d0240c1da050503018038041c411581182c88400745205440c20480c0140c203003001c0c0340d40c2c40381003000040c1d400d081c1002c0e469404980c0c4031084016681e80e001520052040121055140c5c0220222000c251031520303001800343c5075445111784403c1c005c0080e03030140501c1c0325101901d000c510030700b00802c0c10203614440714002445c950745081c159811440c140882 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 98998363 1250 98997113 98997121
    0x20319030f1d070e090a03031e050a0c11030c0d08060303070f0507060905040c080712060806070c170307080117030d0501090603050f0105060f040209040b060723061003030c0f0b091b0405 82
    0x400b003252420280c040c00d021401248804010094520303089d06a0352003850300080c003c00700e1868010300c81d03c603501d036580d003402c00390014115128850840084004c1d0300000b41380c014240543e0400d50f1012008040d6414290203440b056444642264100c505402000041c030401e6001950b10019040640d410450701c51000d5000c3c01c9108040c0241c07060250030801c00c11014001d07045607024065038016240d00342030038407010f0b121800010044480c044410fa401c00031076003501c02c0d68842c0e030440c0e072211090b901c2e00800ca0b4440c811031401710894002001007c0440c0198000c1030b00134001d52200240d01c900e1400c0190900c00f0340380d07036201aa4184014031051307079170b001000c4075200e004880042c0d48014601c0000c008094507008160003000c0400da00091180d540004070040900c05200034442c03051140c0c0540b0352400312400f1420185c1108140b000c0ba220720300d135840b150701c6420550b0031020700c1e0301c41c0c0c0381c0c60074100e030102c000743c1c00a0f50461a00f0a170200e080103c0b03005031428400707414 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 98999613 1250 98998363 98998381
    0x6010e06030d030b09070507110d08030a0f05060d030f11030c0a02040e010c0e0f0a0503010603060b0a0f0e011503060504021602010f02010902010c0602130b070b01050901050f01020319030f1d070e 86
    0x5d00500071008101010801801341720110392880002100107000341c0b1541028030b0088075503042241c56440c42850100071411124560141d1442544002c103440c24250036541c080c2c3c0e80c1c900c0b80b140701d800c1200100c0642414102000240301c8900010000c0030004540c1c4100001d50381d448064a071141d0404c030f90034441c16000802e0ba0120729045075403010140301d0a01140840d5034644c0040d80c15801c052000060165641c061a01000d098400f80b0295445880020020f1100e22030802c05420060040125000c225802c4000c3e10740c504d0042640d07030350b500c000ba01b6600501c149002406040c0c140078110f44c1c01982c1000040701a000901039070909400103050021a404060302064000825074644c01c40c58050f10040c24100b101c0b03a0700c0e00e6560602034402e1303009006040c01100360500102c1d0358a0804900020018140c1c0214074041d541c110600900781c040c0c07a840c0c20b0540720910541400101e01540c02c0c1e208080210310925240e0180041c070344047c07a80301d14440070f500002d0021440d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 99000863 1250 98999613 98999629
    0x10c050d03110c011a0a0f030f030e0a090903050903061006020a0f080c010518190213021e03070f030b0a06050403080a02030403170304050f06151009050306010e06030d030b 76
    0x581000038901180408102c524468820654141d518002000584503982c28030340100c08400c1c0c400e80f0159840c5c001141e0b1001c518000540030b42d40c0f0800182c00207104456040d5405009406918101d9aa40240d4162203e144085010560200320440d550034100086c80d445070038003074091040c0d403130180080d490f850910005000040d04045040510080c20110b60725484070400802c8240b401e0083c80e0800c107120482240f1500075101c001d41a446281403803c1e605030014403102e40440c0300400d0703000a62222030816842145030703007501098007a01c3d002c1d5100d801592500b4440081c0514010101c03201c2921852040150b103000f44881039012050f24196503010310b0090b40c620800005914600580d840200078009000005640041d60740181d80654480d400311903905a0310b24650340c40700002c80c0d2400c149900d1000a04c0c00d4a090700d91544480a0f81c1840a83d403600c1c0d801082c2403003070903000340303400350600000d000160404102c2d064100ea45071030200444d01216000a2100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 99002113 1250 99000863 99000883
    0x180b010f0521090105011a0415120e1203090f060c0304060e030408030d06030201090504020a1d04060305030d06030203070602030c060f06010e040f0504060c03021305040207061407020a11010c05 85
    0x100c400702e1882c2810a81103810918811180c0a040007450680c1c1054082e00007402003c0800026560b0308549911103016602900d8856502048100c540c03542142d14034071103003685800c5500c41080b44c0010006119a000f00c400e40700c1616a689001d4441074a048020910106564000360400400d501d502c82601d4006074022000310310345031000220340ca140102c0e00f019400780000611004060351607403101d8100c0f132013a214001e51507682c008000482c001c015209020610340d04040c00e034030000d00c0c0b81002a4034002c000103a06c03602e03521121720b91f400001c0b1004032180c1d203072410300640c5010403006c40104010702c000e502d4159800c043c50349480001e00101c00201c90100810101c1c0e005a01c030242c1a800940f041089400d03051300382c000303803e09542c16141c091500c22280e9001e032007402103550071500b2031a811021460001444025481100c1c01d88034a0303503402c2d140058292800320140124103070382c001c3c440c1010b01e081004075504421591410312045843c200d00254000c1558241 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 99003363 1250 99002113 99002117
    0x912030903060b0316140301050c0414040903021606050408060c03061509030109122303090a1707060504080a090806070813050c10170c070203031606061a04180b010f 73
    0x4000d05440400d00d00141940c05d042c0b008143d00c0007250000000480c0e04440c0000c4009000301d0321601c07a0301149100714054a501498044001c0c40d50f41800d4000d20312040c401e10440b8120a0380340300003058510705030410000101c00140c2009111410407030283c0110310050028550b05100300000c6044103010704650304004086040c1c42140c0e800c0d44a6208a9005a220301508a060034014500011645c00c3c0c142c502008031816104d8025506580c0301d041780034000e1a10a02944840c06078009812080560a00800c07444c800030b01180100e50040e403040b00050740710300341d980028010500700c0e004110580d12440402010079807200c3d6a42d001061200300d41c54030019424030a00707050103e100315402c02000c2d1400c2c60807503880684102c02152004101186032a1014001103038800e55001a50581c002c1c8900b81024840400b41c6040764860403000400c0d5a3b20704240c1d402c000c59510118050340c0101d410854040d402000d0328000e020f0301001c0100710306450020300744c3c1ca608620042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 99004613 1250 99003363 99003371
    0xf031306110d020312091609091a010e1803130f03050f06060f0913050d0e010e1503010e09070f0602010f0b190b0306030a0605040609020a05060c1b0a120f03091203090306 75
    0xc5c40b01800b10051087c0070006800b130302922540d50101804500c00202c81184a084020910142400e45141a5001d02c40d00820546812a02c040e51000790422103405000820008041c0124509824018070b88508074a110600e5801e00701c1c140000503001e142d00e03800450420002d540c1344034031060f504604660100c0315450381c0006128108030994014600d00c00c0040120b034040c1c02030305070030291000f4ad0303d49400c400c01c0c0d0140548031442c2154121000418001440030071840311101e41e0040d100411240d5240d0740b0804c04003100700a0b401140980d554a201c0e44615a290207840d14508082d1080030403039465184a401c0c44d90780e0b1055100d00312011001c10701755a01807121880c8280c0164091045081a04103007000f40b004941c120b111ba12038600014417418080705030354074050001c002d006494400c00081035141c400380e0040e5402000758501168502c0881303401503c143c0207289000c0e0b20700484c5000707041000650410402d14116552600000380e210303446d80140c90740b10740041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 99005863 1250 99004613 99004621
    0xa02070609020d060b09100b030606090d020a06030e0709020708070b090705040f0e0c0102010e030403030f14040b0d05010902090307063504060506060711010c0201020f031306110d020312 82
    0xa04112200943c0b000c003003418242400301d5a004030180e0a0126030104541e01d48101c0c44032150f41c0b91150780c030241d0303040c4009407a0340b81c800d000d0041d000024190342e03600502680080d08104045d0441d01c0803ea84602ca503002309401c000c00f101415800c413086217024601e803200041c50150342c200030824881080001d0f8420800d111101c0148006401805400383c4c042009028200f10f08000b4458401c0031500380241d8414010100d0b004000000781d8605415070310111350000903a099075050145080395000c1440640e8014001043d240305540d803940400c10700d490950380c0680c01640c10500612581060365408100401222102d00701010b401e5500c04918011600b200d040800c0000356000b146014680c1d81344a0b84902d200c5c000c00c01c259659041005042e004000026242034480212038082d94025400f20040074014012a401010350341c5ca024550b9005511180c80c0c43c0000701c04009aa4010441120a04082e4081c0c1061244284025a42e009441c4543c01e07506280000c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 99007113 1250 99005863 99005873
    0x203090708010e030a020c030109030903120e03120d05071e2d02060106170f070f11010606020c0f04020f0d090c0b040806012606061905041508240a0207 67
    0x1030010030024000d443c1d031890001c0d201d030407605081015008009030031940e40b0b0184280c09076164140c9403580b0460640d00c420f01c2803800c28502c0802d020301821407003070340e81d0104400348041240d0300c11545e68200b0944100150760300503200b032040c4502c03a58901c541002e2a03141d000c0c907040518100c90301c00031031401d030507036400e025404100710340207100c5c08501e02c0e0f404038605050710000c3d201c40340c26420880082403800c2085421802c540903000c040303860a8807071101000c50f101940340c075a07520080b2100c0242102c91a9201102591000c2d95107046070070401440484100102c5d41181080c0458200c20700be1302c181d01d080d2201c140d03500e003203a00304152610f000010309081d007031031034035103450f07810750f580d519002e00030b10a4080700c55503800900d41ca259401000c480d40b03d4003a000701c1e20b8900501050002c3c4a1600550300002d080210301c546480c811031000400754200c2c20100342c034004982d410242c07989051508510035600300c5000a500c5c040058112085d0400160348a07658140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 99008363 1250 99007113 99007123
    0xa0c0308100b03010906030c05060a0c06020a0e060c0c030f191103030f0415090f060c060b01030204090e0618010203090727110315120d030203041a010e040606060f12020309 76
    0x202c48864440440045112280e0ba44450f058a02c038005030b5800e99114001c01c0580c0c00303440134100c0011b244242010020710a5006031800004909100c800d0f40100c10015406401c588000d07107840e40000c107012900e19040010b0701d4540301c8407000d001d021203200c2040c140310400400c041c00c1050004600096610108100c6d48042400700078a6151522028640901a0400708000c005000d980c030104034010348140000c12940503840d6010b008119568200141480e101190705265007031000081d19041805540c44e07505402010b420a454041c074610f15003165030600190036032041c020051000c100003001d0742a00ca840c030b20340000b5996207100184160341b5205a805190034a501100000d000e00c02950061a081620100d000034002c02d020210420030b0074401181c0c02120440c0705240a0b40c002c54015003c0c0c0484048891500d4902c05040c400380e1210b040260f401c0204402d000c3d403440f030350780a8200340c98042d403018007a04006015950007030803004c180d9400404558400c02c1040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 99009613 1250 99008363 99008369
    0x60f030c0903160f0806060105030403031518060e01091401050d0503070602040609030b0717070c050705030313030b010b0903070302040e010902040617010e01052202060f0d050a110a0c030810 84
    0x112010f6404400032100d06075018400d805120050740c030081507114010801c64441c030010303510181950382d0750314203c014081702c404040401181c3c0c603010031640c420070211000720030340c0310703003c01c8103840c00208504150050f4000081d032403810f141503d050700c5a5204504507802111a200045d020b070600c80e045210300000140442d10000300010019000b2603801c0449000d110020241d51f03070303007500740e441e10040b030304c6c00c1c9009101b2400580c14901900d0041040b50182c012540c400342c685020a1941d40287c1090f484031131494003c00401c00c44d00301650140c180d1140c454100400d4a0100c0d07650030807804000d01c101e07102d181007400064254007600003a50014003d01c81c0aa07100d5001909465400c0030210950034134048800109050280303d00a146c070490511904030345500521220749040c5080341c2c07190041004da490b074900c1c030f406041c1c4160048000225411b0081490040702c0941c2d032500c003203500a21103124551740008403480240e41506101c0d260341e442441100700380c00250 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 99010863 1250 99009613 99009619
    0x51e070902030f040c0504090308010e0702030409051e161209021503040f0611160206070201170106050c0106090504020d020d0611040e0a0507020703151a040513030306050103020306060f030c09 85
    0x1104001d11482c400700410f004601484d8100c0986440b1b2080c070059841c1c0d0180540841c2023540100201c050601d0140e80c8010644142c0c2d041684841c07903801600d400341c80d139a0f840c400b00e54040103d2407518481a8001800800c007007030300025a44040c0c12461007021540125594049031021764071106803c0c0c903628009026980d0302d2506250184a01d00b6101d02920700c40d103020302c0300c180c620888003191241c06140e04805040d003004d03800c000300342d448114101d040190042c02907840303c0c581d01c129406821262640d5032507094007044c1c6403c44815170321000302241010180400368079400000c4031240d4050358049600d201e142821000303424014901401c4c04800140000c0501031081540d005001d848401d111940b03d0205c00c81c0d580b01140000b9001c2501c480501c1401202a8051400c0070488000381100d00214000541100c0007251402200c15810700c0703c404140c1d0502c50030000c1d01c002d0804500710b00700940411044c0c010ec441258490360000b02085224501c02e0039201020001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 99012113 1250 99010863 99010867
    0x7050a1205060105071e050c04050907051201090606032105030103080414150a0507020406142b12050705150106051803010e01061205060106050703020334050601150804051e070902 79
    0x2c49403101b1075a55140290303414000d007942418249018040c2c3d40c0900e403a4001420040d082a0030046a038000300c51810701503503224000030005503e4090f00d0001d50050714905803004411009113800c82900d60080b003001810001070000989034001d4405403040034204010402c2c2c06000314200700341c0001c0d03484035600d0101e008503030950303c0310081c0351091003500d081c4602541e03024409840e1a00d8418194801d81200303042d03c003c00c0c9240400b201714403402c841180b280040c3c44010f24040100840b07800180c0000341003050160070055140c00d108000c04103e665850f00100500502940352307105100c5910002c503810a07502500024403003501c45000308480c60b82e42156035122064141c0c00c48490185d9400015064019402e4a000300e805402541ca001820041500d001a06004440140028409400000601c2034080390f4051064009260a5042c14600742104001c800a0410400d402c01048000f450108181e424000c03c0c2d4044925885200e104906245254000030040780c40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 99013363 1250 99012113 99012143
    0x209120303061c1407090b1207030b0105040513120801060806091303080705071b0504060e040b150604080105070206070917031603090b030702070603060e01120b0703021e0c0607050a120506010507 86
    0x2544011f200c404100e8075065030203040426651229900e103c0989410060300c0100054105070300101c0d840550182640301c107004a40d10f045070210a01095000640800d00620009400034940b60304400219034120047c584400341550720380d8252030080406c01d1800125401e14040c200b1380303402c1d647c00350041c1e10802c4505055101d001003841100c2c822400c1030000200310040c4d2078154020758000c0d950300645d03076a54648119000c080c01c4041c0d0001c070204000203520b4001c0c42014090f42107035010f0100d5082020740100701d400306810040b40101301a606903100c42000007104c5411212402000240c00203040036a8002c0d16944040000072000041004066000c1065401c2e554070703071400c10180d41c84140040c0c0502d000d01410300010060103001000c1441d04000e00c2c3d001c0c01c41c6c030f0090315103240e03110034142e90719240c0e5080c06c5809010803518040542400100da119045160490a00e010030600602d440382040c0ea400c5490f41ea4400304507140d01c04d80c00c850505811148100c00d1201c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 99014613 1250 99013363 99013379
    0xa030c02010e12060402090c0c0607032003070309020906041b03150f08070e0f06010905010c06060825090b090c0a09030f1202010e0a08040528090209120303061c1407 73
    0xb10717401c910032030700d800000d450480d2603401d0700c2d25000c91b10010070706640e494006a00401000d43d000046081484000c0003404010005501c241039945d00071540200324410b100f11420003400c081d109070b0920903440d0710400602e550394014840c5290200d5900c16812640c0300148541d041140c505103880c10104941d540000c01c00304844010f495006155125003040002200c1a40c105000071a2800704010942c400d4003010441c0f405100d0000b00301303980300c078100c0c0381a4202052100008203520b0120080701c5034112003000306544801400031040603000200c040d0001020801c0d40304012641c00b85080c41806100e01555100303243c95a145440e09103510b011142c007480710010b6003000c10101625101040b0400c000d0f0f40285110b08181c03c0004000b01801d403041210390442c1c05c110303a101c0c42051006a080100030300240165191412828403514440d00e5210b814164810010700146031291000542ea4400080b0040c6200e1160310b05002c8074415265040c3d414402d00e034012403154 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 99015863 1250 99014613 99014623
    0x140f03060c090d02060d02072117040203011410050f01031103010618030503070318090c0e10021002040312020c060301030308011505160b09010516080c0a0306030503130302010e040e0a030c02010e12 87
    0x9001d4227841d2850000c004680240d02d4400122500099400b2401c0300101c1c082c445564016200074000700b2401170071039403100320304400c64617a03000c17030724050040015051501d03240c0d00208c8203203424400100c80d21f560240d648418415031041240048510031880c913007070052005554090181c0b5038075005420f00818850000c1103026110b5001c00c4001540022032143c465038a03010f890300310106480c08200010a030520706840c0c294003a804541c62010018030052024510a41031881044c000ba00300900e818807a0f8a0f0707038043c600804c018800f0a03002070355141100c0c40c0c1c2a05180156150500312100d004065429584550b02e40e900c0003005615803441d8420180711008000b1551024007259040d4001e45000000c18840300101e416410600c0082139418000d0601251050303907517480321300c3c690281c0d29038007045003418014021581c0c001200308072131030101d07014000008007401c1c20ba100d2489100c01800e100c058000b00045900400b0607121101004281401c4030740030b0b4a0117a124 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 99017113 1250 99015863 99015877
    0x3030c020103140403020c040c05040807030309090c0207050a120303060b0324040501061205060f090405031801020a081602011709031c090f0308091203070306140f03060c090d02060d02 81
    0xb007400c00521440520502d00424031a40e0564020b150f40140103080c0001052030070504010088200804200c1d1032080100b2801503200c0c0c5d030385042d0140780c1060501150140e02c1000119000200104003c0d922203aa0005840c421f0440c0001e88590780340640040c84030b60f1100203207107404000c101c088031038a0500e00762110b00d14002c0d1101c20311801000b045903424091800403404103607042001c43c1c4a81d000d294001d80c00360230b11004002c1000090304042040b601210a0350000826125044483c2400400940203000400c1c001100d03507074034000d2740a25445862444a14000078055a2207000f2032034000b6000c010014090808843d966103c1c1c0c0214410b251507503007120449a80c2d50f2078410118000d8104500800c1101c081d50100d555410107800035038184207600d01b6000d400303043c0d80150b000f05ca69131000110249014040081c10031685410b0740304800e428041c000503140030640c181d1108007980740c02e0b651001394002884140c4d01003000b941112006c40d00c1d02401c1d08070b900038000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 99018363 1250 99017113 99017117
    0x1e090c0f021903020706030209120f0102030601020d090311120322090c0212040e070504181b021f110714030309160b040b030a02090303030405010b15041d070c0c03030c0201 76
    0x124103003003945480202c44840000c0060344110410480b1038030a03409014070b04d10040013160001641c41d20b017031800e0740f000480c0200341d50000600c0240d603010054480000c116040422400e031460f21210fa2895070704c40700a014000c0c45041084101090046034040310549107071414880d55103010302c00007002c41c001c015850785090102c0000c1c5000040d54814608841034036032903d801c000c074800c281c800160800c01480010700010940003000100ea04518401c4040002c02c80d001110700045801140350303407005e43d085060085c0c84840b50740d202e05140502250081800c010f10030341007525101d81e1034098211808004d2110114a0100046015040c00800c481c0181508042a02c05005030700c10080132400420007000b0203403100000d55840011043c0050810742c00c1d001082c2958412502115144d6603145000030030719024030084503540c4080e01040c00c003414800c8282c03003048210784502d6032a9010000400c0c0d039100d6100346801551103140b0b03c404581d2480d0103803c11036542001c0f40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 99019613 1250 99018363 99018373
    0x3090b090606040c0509060d15081207060c080c030f041b06020f060601020c01050403060c0c021302090102010e03090d060b030304080a0305030708060105090a0e13050d120509070303091e090c0f02 86
    0xf568401c07000d0b9451b00100503ca6440c0c11072413202c01c00204481130140c1181114444c00085642041c03100d00d0002c07902100c800c0d500e000364901a401c032070a2211000c18044080300f40101e207151103055a40c41722a90102d601c41e6203e5050403150b82d2050441c1c01c040070440e003000700d0120b5000c0381a000b118040700840d603a0351900801a03888081c50042c0e98001101880208041081b503004000800307114144201d0441241c0c000c07500d400280401e10f15082c1d0005460012940e0900c208008003c1400c051401c1c41489000260b0030b80d0b40c0310019000d1070710f582c1400313401c0d1b5052040314010050302049440d800c1403860050400d0300101c904502040c82c3c0350004140e5400f41e01101e44517807004100c0849036041001c2e80c0b22030500a044a181803e40010800004000b080545080395407510741c0906550400182e0080c2d45004040c4075958000d4002000020b4210040d030080d1040e0740440e0800395088030007490f40c41d203158086406d05040003000c407111a000b0701d80740600039095007030303031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 99020863 1250 99019613 99019631
    0x80d0f020601090614060d110301090c0e0301050103030815010302040e160f09290c0a1115090303090603071209061407050304050606120106050a0801020315090103081903090b09060604 81
    0x201103504601c505451019010300c050174528001000701303940320b03901c80d0000358a103000c038000a040d04260410203a10380e03200304036480303103030854405401c0f102e040b80207204c150b04507500140401000713003621680c2000c1d8003211441e81e000b03806860103070031071050351410f6240c02c4000518400180c8803403400324080610519000d44a004600c040c0d95100c54a01c40e0049401c2050100707200c00b90f0440c210410600036035041c0241841844130030381c0100101850a1960340800100c2d48018036a140000420080105d6a0f1408400c1d144100000c5410603242c1e90389880a5440e0100b618041101514002109042100710392124072403544030030001c1c002d1f42c1e50704000c0d2080c0c8020307200a841035000000142c4146800c004004540d011007002242d21130742d843c003041e244582d680102c20a0b9401104000703054001041c610781f44001200c04020325455500d0f01c0c4428800c0841c035801c00b089000b40c2c942c69030b0081c4c025a5035298840041d4020b4602404030301d8072500250380d4640b00b02d042003454 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 99022113 1250 99020863 99020879
    0x80601030305120411180910060f0e04020105211b03062116080105160504030b010902250503070201080a0e0c09060d05070e0a0c03090c0302011206080d0f020601 71
    0x4181a00d034141c50307082c03030500b5500c4826442080108112098619002e8035501a15149440c0090318022400c3c03a00750b0034003030346460400030104015a4045e01e011070030080401c4170481c02048031204084035045444500040f61540305035401e40c81550b1049100c05008040424040d2203030141401c070f5500313083c0c4450814a6071009983c42640803040c5240c49020354910103055400800305801c440640701a603e0301c1c1d1801d80c01d83d01020899658070200000b010403103200c2ca49680091400c6803809046a4554800500c1070203120940c1c1c0e40880c00d00442110300302c02c0d40034103803e0180c144445009181071640c07a40704200c12030000310707080301045400101d4000e0f40ea078041a078001d0411803c03003906201d81488010801c2703500c40454034403100803640030b002ea41d0203006110740b5620f00d440e001030000281c075864078402040514203c5180007040d00d080c09401620780c2440c1c20f0041054210346030014000c04e0700b22481d140203640741c001c6459004000c10310348900503001d81e203081c0c1e40d032942 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 99023363 1250 99022113 99022123
    0xf0c01050a1e05180d0507110306060904081b01020711040b042c0a15050103050f0d0f0e0f03010c03022104052127040e0d0c081602060708030a050108 66
    0xc02001c818024002d60403501c16048140c3c45070450f42291544415404884d00d00525040e000010038030000e00c1e0070910422030102040d0a82c2036004000b20b041c480e011604078503004202400c0b1000c0460f550020120900d201140e900e10040255141c02312800c007214500c0e0f201503110701c1185840041041402c042c040d0003a02d80248441050400310004002c2e07920f5a01980708030b103030080ca1140d0000416402d208807402c041d84000140560440c60070380d140407140b040e905841d034499800d4801266103d0a1025044181e280c4110b42002d4500402c407109540c524a0740d040d400d00e1801c4041543c507502601440104960004040480f0120700c620958140c030301034400c0d0451611400517500010b850030a01070000202c514008104800090f186445000364039050341c804001c0102e0310b054042c440207403440c80301500d0300481c80f02010340000d800c0e181c010200305001c6a590780d0200e19500c0303552440d030082d040c2c0e540c80d505840c06050b15070045070761082c6240b52000109550340002382c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 99024613 1250 99023363 99023381
    0x7090605221505040e010f05010806090303130c090c020606040f090c0905150a090b030c0a060e0d06060b0406020304260d0c0503040b0f0703030b0102010c02250b0f0c01050a 76
    0xc8000411030000d000342010300321004a40350707400da44490010f902e440364810042d07400105000010140f81c0c0090003415550103a111030003a51008050015031100481100c0d000164054440c0071000d803031030a040450001d40c400b42d0300500d080c000b102c8964003c52014481d1201b190200b18001d007808401c0101c600464024049801c02503003407040c0d050640c44103411013860700528481e1185038000446801c0c0300d03000852174035100c0880d4071245c1002c000031140c14a04603851140c903401c0020040280481880151051440380f058005010056024001400c0106403035070f03940b608ca841c06946c030b6100c0c4c403400c03c40300d1807181c2c0e458400010540307440d81c01d2408070103005c3c0034030b4900d000c950040d44d406003550709000c20800017900000304001080d00050f506600c070745620715400d01804941400303102038103690400094000e0664040b886010300500e0540110b4450404a5181583c540b160401154444009801280d080e603076400780120118042c024409951008a042e0a48241c41 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 99025863 1250 99024613 99024649
    0x102030a121e180b13110108180706090305100203010305030a1d09070903031e05030109180605040503070c080c010c02060a021501031b06020f0a0308042307090605 72
    0x15410a41840040e00314909a4401126141e5800501a0b40d075044a2088019640d220308407101c01c01005601c0c074405500c10001e140d14044840300762540f101c510440803855040092040c00034807102650010641c0c20b4000d041160b1503562110400381440d111404140c2e03240c440c41c010442070790040d0003181d060720386c000081d42c01c2c0010792005030b5220001802c4102042038000c21040983c035090a001c0c07142d05980e8030f05515514505010300381241c50410003103000c01040c08082510b420908480c1110740f22003000880e00304075603402d441070354607002c02482d190518081c0700500c04000003a01000380206a00c1c004c007507541580540e1030780f40e00007140c0483d00007a054005840d10710050a18100280103603510380200052249682e2130036001250003d40310150117625044414585018108a000415880000e409030541c1c0c0d1140d01c80c010200000c02002408001c01d00d000320700d0800d00710b40398401c07003030f86507140030b455031124020b01c0b00b100d10f80000010b0500d4005400080c00200c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 99027113 1250 99025863 99025877
    0xc0918152a090f050303071101080601030e0109060e0606010219030c0309080d020a030e060a0507110406080708060a050f0f040201080a11130302030111040605040b18041107060501050102030a 84
    0x12204910180003081103115074607960041d079028810401000e010203800d1561014415410801c042c0020005600124043e85c000c0c03000e04002042002c410342d600d82d0908040980d50388100c0100d005e04030070039400c1055400d01417170f2000c1280701e03000201285418000e681103a502d8000480e90b998040e48003100a4160700340d20400b0900590199490500078034080c508a0b8550100f140780c10021840f0000603840380441c5400d15910400380a80500c04403a424506800b441c001032440c024504050120b0314040004130190f9102c0c4d00c0b420007000c44600381c60340255101e030503030313200d060484d41c04000d1800d0000042c1d104a83c1c2103070301c0c4035039410502d41da141d4407580c00440c0da03c04018000324199a03103030a1340da44076a80e400504249400101703803880031401d5105040c2558100002805141d01c2270100f44100c6401c041500d0a48000c0b140a645400c0d248181a100011070802540c101c0e15102002d0700d01c016403030042411034002c031703030074845039a844004907500e124a0301504006052 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 99028363 1250 99027113 99027143
    0x70504050f0c03070c0f03020615061e130503010c0206010611070b0f070501060323011406010504050d030302070b070306050f0f010e04021e030903030103050601170c01050304021305040c0918 84
    0x40c010140d5008242c1d03191070301d500b2045985130784c11181c1b0800e090740580e0084082060074503801c042ca00880d00181c1d07100381080001c0d07100d52201c0da081900c3c4900748038040307022160702c05d890007013200404c0006d00a11000c1c04071400a51200028003c0000040301c404c1c1c00e00c20b444000403903004480b0503004440c5001c0700c00392510905e420007a0211155500c0d0303900000480e40941c001d0301400050008500c40d44204194542114110700010b036a060101c410804903a0b004029542120f00688884450f80ba441c50120002d2044c003900414185605090100303c980c0369219405841c01500d40e002e110400500300080c103801150341c0c0c0d00080c410004080941481d0f0040c00c0c0015194100004151030010806403a03081100e201c4e40715480400108148401048600e00403c40c0700408441c40c14503640b41501c9d45900144603050003c0003000c43c0840d100c8000200c081410301c9d204000509052605000c600860301c07031800903a04000f2004081c249864002900a900030003010303802c44 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 99029613 1250 99028363 99028381
    0x7030e1603120f1115150a0518090a06020c1f051003031b1514061005030604022503020f0d051309050405070510030603030f090b071403131403070504050f 68
    0x18075400e0208010841e4030b1100c5095017000554445d000d240000e18540c038116981140d603080d0792900da8480d5010307001c00c004507220041c584035001003003410780040c0d582d00b00d1100d02e808807080700101050300c0080c250f100b1040214a009403c02c658118071034800150300310700e09603032090302c2580c4c21906a01c03040000902403460358280005044440a49804030f0b180d8400307804408a0750350f80b8503101c0e00c1c08800c009150100c0c50f800b0701c04544440003a991040c008110b070000401032806107500051b0307030010070341c10541c0b120204804101045492030721700d0001d440700d01c039511440e81d03072189d210640d210310700600c2900d080c1510170410010003880c0028080c054600a042617480340030341500414103403070310b00034441c7c0050b064402107882483c528009000c03c003881e2064080125101050101c1002e01e0201c61803035401158044041181d40b44060a42c440c464a030343c05909070020003c0d000c034400c04610890750045081e124500d6680c014001529030488030040240a01400224070325 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 99030863 1250 99029613 99029627
    0x10e070e12030d020301030c0b0301030305030406020723031e18210102030f040507090b0d020d0c08030c1e01050601230f0d0609200306100c050607030e160312 70
    0x3000082035003040c0c503200101c0d9400c40e8840e81a108801d84c0000040c420f000d007000000b0010700640400310301d55031650f10010064040070704010107541d00003a5281c103100003811441d000c1291100941c80a41c1c0d1003039051390b250f00c1841c40e0300d240c0c413084501d1000310007184251540800081d1040c11407074401d00070000e9000740d09004802c0050181e0b03100755000740c24406103100b642040381d15070413410300e03040a1f45014001e61113900d0460900880641603120421101007266054422121801443c5041000405c00c0d4201c04403030310000c81c0410488100046111803142500b45421029a0358402d90f4240e40e0112581404217103002540801d8440920150380c606900d03050103800c00501a1101805510a4000081040d11510140200f010a128112081d0b802d44c1c2d0030b03000321000400c510000c1c000100601c0c0b042c410103007415017141c095508030110680c0601500c0b51440d003103002070024800444e88007810700c1000c074040404580f89541d44c069a40088c003250007040707034450032141d01d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 99032113 1250 99030863 99030887
    0x120903010207050d030903020f0601030218090a02040e100b0f0a030b07020f010204030302010213150801050f0409080d02070b01120302030726071401230115020102071209050a0608010e07 82
    0x1641d402c01c02c80c0c0124100b48845101480c19907004100d001150900a252420307a00da0614540c2000e001000103030f6948482800c00081000408800d6031101d000c181040540c480203034215042200c0221001e00110f10401826103a0304204464000303001131180b0f08604a96881d00400c50032000d0000c544107010079030340b2100724811917035160b0300219014260380090380102c0140c1c0d00440c1750452002c1c0580818040e00903002c0a01c0403440d01400100102c2040c864940103c4e1040d40e141c0c00e946458105100e85500080c14503130b2031020800f007030003c0d44482000e4070340c4114807001083c1c3d1060701d2201c104058040c0c7c000c5050441030f8071054112007800710004d5607042c00d1001440d407250002c01810409000b114a032601114074200c40f800c1d070b031902520b110b80030b1905c042e040340c0d08090707040a0f040d50244a80d82214003002c01c0c09a0080c401c2410242006100c0d03018408941d521000410a50300c0550301034640d03c3d42e500060f2204d14083c0a180340d040603400010300380c28414490f48041e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 99033363 1250 99032113 99032119
    0xb13050a06180f0804030614251209030c060b010801061403070216080a03020601050906060403031b06060f141c0605060a0302040608010b15042108040509180f0d021209 74
    0x28200030f546507810081640401c507501a030204041050082c1e40c0f2500707205081c20111201c052910000c2d19520408451b0360f016610842c034281c0417090f2040c1c2c11400314044d820300030480d482d094100134020b85004007003241c2e81810060881c03840e5114120b80c6040f0368103616020312400000c1c1c01c184042c0c00041c4003c045108450142d40480c0401d060700e002032460001a00340040c0b1428002d04041c0c050b000240902c070782e6003d1180a840d50822102140e406191180d80c0c01c4040e010f40080e500801c40c06080b003418001d0104645590310120b00484602c0501203440c40d114200340160402c0c0310181c071074422070701d02d801c4020503550341000341e015200502442965450303038000703021540d090f040043c00d0f03955905000c80130b0800b0500e23210070800102445041900d4600f4404101e2400c0105202c0424600c0414080281500c00c4c1e60140c0070060170b074541c91070410a00d20f241403042072107081a100f40c90840d00016008251500c0720001d50b030241100314900203141c1625804050140e070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 99034613 1250 99033363 99033401
    0x7021503130206030705030a0b030a03080c0f0f04030809180705030112060915150806250203040b0c060a111903020f0903010501090b030c0603070906030c030207080310030b13050a06 80
    0x7006030b0319400214400d01168031415285c1c1080740000c0304550707821200c0e5001c1c0c0e200c508560b000c680c0040c2019401210361619035030301c00010156428a01074002a0180110041400310401241c0c1001d0039602074155841018201c545e03520f240c01c900140d03203080110300c08000500001161180389103010b4002e40000c078174442d03240d54122101d5205da0008665039a02c1c01e07510f0440000801e05001003800b0002410300e41003001c6018408500c40c40e200f204542560701080340d0900900a03100140b108164064481480e0006240c94240c2100d42c4462541703021440050040031034107540c001c01c0900414011011402c100f80c0095000d400c51f00300c21102409601d225980c00d00880d80070301481000880c642003100e042c545030440155915100d01170a104210303605c2c3c2c0c405a030340125015072601080300c20384404150028450500040c00c140e10000070040003240d9001d58070101c9101d01c5c100030300d0355a14801310940e0070b100701005105030880018500480d0803034111003002410081d0f940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 99035863 1250 99034613 99034651
    0x240306011b08030f010306060b04050f040203130c0b0a120606051207031d07051008130b070c29090c030307020613080703030210050903090d08031f12051207021503 72
    0x80042e0f00121485400044001c00600821409009942c001c1c02070481403410181850700040c4c00e64056040e40d8059075020000440061600c44850b00ca80c0c0c02000c6852459207400d560003190788134500c0c920219441c1b810b054140700c0700c1d100d11411a0010390380c56042124803c041100420040d01e00420991118209800410500300841441241800074412145041c00b0300842c0d6481f02c06207030038400c02c0000c20a911806001c6134211a510042d14066131b500c15605817004050194043d0001c8406600100142c110f0141c1c0c4180ca12012a0527549a488449055603458405000350301904280014170060030b05e100030380314640c6407015840c1981e85032440646002c025520940c0181c0c017000908580c8052446566002a21400614a4a41810042856011806c9004102c0c0c080080003641000c03402c844900c0c0c400381200c0d0114007603941ca0312041c0703007080c1560a80c0d1a00880c107082d00d11405060450352401d502074a03401800c3c10489030411a504020403600035520f4212401d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 99037113 1250 99035863 99035873
    0x150a2601080705040f14010b030721020d051302030709020a030204170102090901060804020d020105030c0d0c020601080f010501210212011503060605061303020f0a0e15240306011b 79
    0x11501070000c0c1e10041c92101d28200400064507500002c0e82100c03868150041404207101e200c0b641075448181c40e5980d01c1c1c442d000e00302c44000c818043c1180900b2001882c400314038480d0000c08103403000ca503091105803509402540d10765060b400082d4035030b00101d010095102181c010f06025031700790030f0041c106903952240300e10304030020348900900e95001882d8000e901d40541100e02429684c6445005032038654080b804d94030382280082c0c140034012000860309480700b402c655841c44800300502c80d00d90075400c00b0356105020300406030039000d880760300c2001c1181485590f049074105242d441d509003103445c40c3d8850109241040e60000c5501448440e0080240203803610449030300007003844585907040002c1202d4080d000b480c4215010043c4a00802c0c010700c80c10266130301202e50700546007142000440d501c40031b601c11103009038128100002c0c030b41107100304040000d0540304075000f08024031a040100c9681e2420600029061012070b04a5215030580507180100600307104042000d503c0d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 99038363 1250 99037113 99037187
    0x15030109020307020708030c07050d060f14010603061a1909050604030803060109050d02030c010f09080709021206010305010608011205150f06120102040503030a030207020303090d030507050705150a 87
    0x100103045a000401d10800b1541000010000d00d0918080c0d070901034241041604c40501e40305051258014410700030601116502a102150b82c0000420400d5441c240e0484005024425103010070301e0290001074000b003610481c9000200708144902d07120b041d074520060800441442c1080204030f040115007904c0700d4000308081c1d0b021341e00440d100c1c604440010145981a041140100480c4803240d0040e00c0004107180e00e5030007420070444050200744101c44500c0741d54001c41c0307284505540025216203e6004000d01c3c0007002c0000034547d590001036003680c4007031240900090791440100701403614200c1503403115228105179003468000034803400d02c003d0107030751340c002d6104030f101070110a2400001003203101c0c94020095007000e1400000a441e0700480489005064000520904558050040310342e410b40080140b0b0b00d44c80641001406600408401c850500c143c21010481d80b5000450b820803111803840c080c41c000c0c1d8041c003220032020403c4030301100d2070692101c500032003a90742 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 99039613 1250 99038363 99038369
    0x30209040c150f0906110a0204020d0e011107240905010606080108060a0905030d09020321130905011202040e0a020a0b1c0b0a1202010210050406020d0f020a08060f150301 75
    0x100740c002400c255011000459206102c001e00800344503255000ba0000c150f2412510a4282040c48050104060342089030340c01d402580644001040c100b00f906a500c0003641c0100c66000b040b0319062180040b0481c4644000a4002e00c18260510190303030030820303214806c0c1804140421602810f42c0c8560941e81c503a041030002c034640700018440080304011466001140500c241300d8401180c41c0c0d942c6134842c0d220842c5207941c880d202101503440400407080741e000219050350409044190010068210001e10806641e0403440055040105d00415051b12148c0d17100100485e00d99081000600c030104c8921018091660408090390301c0c01d461f64000c11802ca601680c1d50130038249080b55140030032600e60458074105490405840381c202800a40c0e40003024007010079101e000503450540c8241e10119014240820002008022b402900002040300030034803162004225043c103030300600b0080d00000b482c0c20300280745d80c81c0840c00076149182c0540314001c4105040b02c0c412999000360 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 99040863 1250 99039613 99039623
    0x903071403040504050708100e090312010e0105040c110c090a090209040b04030f0302070519050f0601060306080c010905130b0609060a020105040b06030613060e0c060a030c030605010f14070c03020904 88
    0x1060030400f0f401d0a000d501e620001c036240800b43ca1604007842c0d90107440303502030b81c503603401907500285c40c0c0d10b41081100c8002e51501c441003819a9142642380e80d2030024000c3c180100c2c240701004440c41c1c05170348d02010083c401c5001d007048100883c24000d00801c0142002e110903211107100005d600c40e0450365008070701907544404c0c1c80c6130606010b890059401060810075104200710b0000c254007285a4a010000d95203d0002010506100c0c0c42e0426500ca850458002e440000540f541c065102038200c4503d442901c0c08180030500640b29600b0a10443c0e81016003504030000640c51684100303048a070081480307080480301000304015401c51000300c000b40c0e40d540c00340020311945407105030740010b08400a02c42868500700c410340403060207100600711520340345202500740080c0910110f07450041d00c0c203500e685030400028042c1c05005002000b02e80f60940200300395108020307400c3e28900d29100c244005512044584032580041d500b41d405800030240803005a071402d040c42d0050740a2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 99042113 1250 99040863 99040867
    0x608060609070504052422031506030c0e040309080105070c0b0108070510050703032714010b03030a05090604030501020d022113021c050604120f020609150903071403 73
    0x100c0248055000090030060502209000400c215650003224a0303003540c1c6d21202041c036280c04101d0640038007030280340d5442d1728810007030424030702c0c02c02268a0841c1d004c0c054440701c07101d050001d03108452440c000139150003010101800000c3c0d4411055400922034075104524543c1c2e010141d0860750300b42c6002000800101c42c2501340103580e80d480740500301d001c0241078010b28040c0080c00c0c066201107040c00703108000c980d40c002d06029900c1211340e03040044000a81c4820b5a00100008140c008100c5042c94161420340c49814140308a00b0342a801a00075450401004c00944984d00185070007a402041007102200081080c000760014022198016880b003111048602c4055038189034404078014200400198160140c01c10111540503103c12881004248036000d00107941900688a80724960510080012144810100003e00d60b1070503401c40b0303808001c03610340d1800d540340100c0d68000d40000722220030046005421604003812246010603030307591240c001d40700100b154915000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 99043363 1250 99042113 99042121
    0x2120a0302100606110a020103180f12030c0f02060c1c060b03060109080f070902091305041b050102010605060301031217040305040f09062103031d060907080a05030f03070c0204060806 81
    0x15003d01d2028108605004100720210006196581400e100103410913031107001c104540080704404090b0a600003103503100c260351b2401c1800307903004504000d00c0045d20300480c50740703683d1003000301c107a5200d2950b002d000a84c50388902001e680d0442416802e003840c4c440640c2240840511a41c801805c01000c0d25440b440c00b030001604aa03015406070b54942c101e00d041a40100c0089045000d0b100910350060700c40c420f1201090302c845081525041041c40c02007440240301308104140d100c801c00c00448030304561940012800e1b91780904c10590408010300041c40000c0c0c1c2d400c10740a050307070b640c5080c54541e800b040300380c501d00c4820f480039000300d81c000a090220085c112114005402070b03000900445240c03031403001003c1d24111441c0f43ea80c0c0514009420103100360814120140c401e900c602d1150b0200c5805500d960382626010424401d541c00002c0e01c1c00c010811400f0183c202c0061820412040401c3c00250700007840c500c20000151314800050741c50380300da1006407041000901041ca8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 99044613 1250 99043363 99043393
    0x804020102010b120618060103050607030507120c03140108030a020d050c0f0d1106010602032a0a02090709051c08070305031b0f040e090a051906020d0e010e12030601050306090402120a0302 83
    0x106c100c078070708600c1d000040188003040300003400640042580c5000181680c405d00115610000603000c00085401c1a00d002000c551540100c85032a403260304c800c510340d07640d150107070b521f1291081041c05a0442c90b04280d03054010005030005c03c0c0d101050b2003036441050401402c01c0c40f85446040402e01c61a0380425810007080450b0244c101e5000a40c0b030101d002c1105455002a1202c000040d40c01010502e00300009005200d0a00d41c00740c1b00310140d081012000e4405d0286001e5540100300601c001d0000e503181c40b286840864000c000716182080c2a01c048582d070f40001c209007802e0a50642004010b60b0a00c000c003040c401780342070700343c486007000c00958000401401c02151907000a000c4400b08001207048820b03840b02800304a0302070407510349017000e400740d00711491415107040c03402d02c2c4098043d0044400c20031043c054604502c1c20000ca00740d01d0206480050005800717000090050500604058110340000c19002200d203803d1a02403902c1407405003107005821040c1945030030341c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 99045863 1250 99044613 99044641
    0x30f03030f070207030b13050f1506010315052412010e0412020105060906040203090c030a050d0206160e040c030f091110050412120504050a0f031a0c03070804020102010b1206 77
    0xc2c2e00d440900800f92a6869074810410040c0008581806505040381084030030882a042569001c0542c0c0d6032502c4901603d40e0000200c4550f80840d080c100b0301311513100d12855a00a440c0014102c2c0e4000c110290091640314104000341d0780c03031b0780402000054240c50400c2c0c074001c00d000c40c0c1d0418240b8040c40d10074a0210150180f00035607041405110300d40c0e43d45207548ae449030b0252130050300d80c2e8800500d2850300a1042f02039800d40103071200c3d1014020f010801c131035480481d030219490f83d203c1e010505074240d4205145000548120001d0101b450640c00c01c2c50070a00c540350209844901749110803c45980120480e0a8250340c0407014482c1446221000e543d0f5442c20020300703040c0303000100054104c2451004107000c0f1f80082c504455406071042c1d40280a0260004d401c490311a01c02410683c4140000d8807080b18854210184e0101c01400d144146403602c146400c1d038503084c00a4402d0b04014008074155502d0714100300841c0c840d2600403007008441c800510107802c0c403007411950700b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 99047113 1250 99045863 99045871
    0x40c0f09020a080a1a0a030b0f0c04120f0c0f090f0b01030507050d02032205030703030608030403020f130609050a06030c05030d0e100c1b050319020a0b0703030605030f03030f 77
    0x15801480119100341d00149400d40c001510b132030201d10001e8440300c80d0b030304a20f031000c0d01e903020b41000008024409401165440303403590385410400c0342c4a84465000318011071140090903c400d04421000580ba2001001c2d100e02c50100e403c049a2a25040c0b000300c480350f0040f00c2529610301c0f5203200d19059000320a0841c0c42030a081104e420b10701d0f0010304500c1031341d028070390031a000400f048604184502c0c141800000074140d0401240320f181840e12603100071802c2e80000c2c00c0000c00700d8580004000c99046030740c000d00320b1001e2030840c801d00030b029000b000a5800181d40300c20015083c5400d009442c412001d103030000a9884c150b00e002c0140ca4416041240250f000c451a05401d90b00602500740d0084211810344d40105608800c44071400b0084000b010700007544074801303075020080814420f03218100c1c02e0711501c1e03400a004202d1a001d01030041d500c0745040031304001040d48100280b141c1070083c40c0c041501f41e103800110303191185000070f2680503880041046403441803a0141600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 99048363 1250 99047113 99047129
    0xc08070201180507050d020307030206070320011503030f02100603030e0102011a150304021f170601021501060f0306030602040308040602072309151f0206070f0206010b0a1403040c0f 80
    0x100c500143c4400e50389500c54003c1c1801040042c402d0740540d50208100707002181c0c01082e203503a03408140350042c2405500358008492403a003000c18036000106000703600c1c0c01380aa0341988805071464804948414400003410194041e400b103203600c01c51280079405c00b95000c0d84a5a4844c0d040138002400c4541d034450101d130078040f084d1500c40e03981c0e499190342c08016003404a5901e980303c1c1c4c000904540b810445035004051611140c1000c0e43e00580b0302c1009010745880c0d01c0b82540c0300801681c40301c00f250340203481e8001ea040103000c0107004100c100c0e04004541b400186d841c0d16941c8100486e8060703003040e43c0c10b41c0003003801c005041e4100300712009040240b6017030740e500c4c2c007100421080c9040c141d100e92007071243c00c000981c540381c0c0340030304280030310014240303041c0c0d00c42411035800701d944811000005004400018080320f00814141c00025419401042c0701e80c681040445107401c1a0001c00030020542d0712200603100b51005117000f80d00490040302454a485242c4191505a0380301c010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 99049613 1250 99048363 99048401
    0x1c02100e010804080904141806010b030f04230a051c030603030918020f070f0c0801050603030a11070b03040b191a04022b2403022101020d0c08070201 66
    0x560b6841444190080d90040d111505c54007900d0004001d083c0a9407000100c10b03886c0d0030824207102455149200188800070386030304d641c07584c2c446038483c4002c0b560318040480c0d06010400051500844046160540c0f800c000d5903800c6060b181e0030001c11110a582540c40549450240c0381c8448850741d46141070308040241301d00e95500a0444061751141822804080340c14540c4c100d580d4040790204c10400440d55994880b0b4980503004014812050716407182d0700744041400c880c14440d0500901e4018021420000030304000c550311100c21140070010b0081038000910500c489014500842c030812200c0b549d8903001e080c600e0700d1600400c100d40414108001c00424050041150120210a031405682e54001261a40500020307540c0111040d460710a06a6800103075404038407201501340915484441c4121410441c0c07500340070180d44900d0042761400c03601d00449030f000c80340c420f15001504007210744a0100444211a038004081250501000102c1c3c3e8281304110080308a140e83d10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 99050863 1250 99049613 99049637
    0x310060b0c1b0904030815030319110703031b140d03020a1106040f03030209061902030c0d0305041226150108011205060c0d02161112150a05151c0210 66
    0x100d21043c058400b809010340e4401148484042c0944030031500e0000e000c50340c0d281c5c0c6071213103c121880e0800403840001c25240c40c411055801003803a00449415a46062080c00500c0180c41300d0301c1c500a0443e11503114404501d58003405002850404240b03840050721420b485d40c0290148a070311042031640e801c10010400000c80600c6595206078040c5801600d50501d039001c146648903610104224466074680d8580f071035400001401390040308030940d11101e080302010303425241c041da00181b80341c640003409940c1c02e1103041c500c420f0b13440c040d2000350182108613145400300b80540e446608004200e108005a50b004202d841c0100100b0000c2c80b24010f00c0d89619440c0c0c0c0300a80161010080069000301700f24082c1c05850404255a0b030324002501149010b051050786200541e000d1045600e0f080a4440c0100c1e1070b1500c560380b09062190b5a544290031001000c00401004a030440d21070007008589580e0001c2c8402e060289040c5100b0759a801001294118207803d0410808100c2d556 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 99052113 1250 99050863 99050869
    0x10f020315011e0f0309051515010203210403020304050d05030a17040203030304062a03021803010b090f060d08030a0504020102100e12090402041a03100b040506180310060b0c1b 78
    0x1d01c0a03d41c5003103034140b4040d10703007100903100c0d05030701428900c5002503200000219030b2003140621580c41266508507100303801607813280034201110b0f80c14400c0c1d02c90f140400d5030414060340d01620904c10b032440e1984440c006141303c0d0381081c0650f0141d0001c110205e5032078005450100c800550700011042d80b0707040c0c0c0017a80c0c0344001070000304100d488200c0710b007205a084404501c990302d2800390400e1500d901e103000b0025045441e5540c0c18000041215a00d403c4c184510386e04404043d08001440d910040b20345608035000c1c180e00e400042004031031000c220190043d50260612181c0855507003020700009140c99405400020780b20b01c1c140380c034030110a0001d00100d00d128003da29948031151540050700038011613100c591001012003182c0c0288040b00021481000c00e01c00dc000e9117900c55410311114081e501905421840401c0040c40380340e1320800c190049640241111071f8080c0030f025200956005070700c0080b554901040300c4601c1e42042c402412080c1d00c001c1414601104c074800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 99053363 1250 99052113 99052157
    0x30111030103080705010603061a0a15050a1b0c06050d050a11041203020f060a140906150409020f120102031503010b0609040504080d06060804170a0806010e0102030408010f02031501 80
    0x2c0105015800541c400800100b03401000003943c01400400a403820600d000f0074011003020814460352884c40d02185104401c00e0801036641541da45504084030413405941140910411010107071100610341d000801000240014248a9940e140c80d40c2c82c4001c1d6000b07880001c0d0000e0060760400c0050031951089505680464582d814001c01800190506905140344011150240e001c2c0310b0801040035800e4100042c181003540300d29007a40c1e256010f0030780f01c0100717403642102d4130515032120340d50345855040058654001440039443d03400c0400000c041e07a805445013011a500403041150344e8031044240d411042c01a00244849049140012842c0c860b01440070b00c200d988002160501600c1401e5810001640c4400c004154035204050301d03052045404076140100d580350300d00c01d4404401952110449038881d424140c0383d400c015220301c168226564118030050100040300c4100340142c00038141410001030b942d0030305200401c1c02803000d861590502180d4041180e5810910031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 99054613 1250 99053363 99053369
    0xa2409080a12080c090405090d0806030312070c08090607030207051302182806020106050907090e06013005060f0102070612090602041223011803050c030c010203040c030507050301110301 82
    0xf41983c00c075550120a240e050044281e075541062030102000383c1d00c1000610b001e0300e402c441d01c44503415980c0c002010303903d2103030002c07603904c031155280400c1c81d4a001d400140ca40510070700742d40742401200c1000c1041500000d100350010b07403140f03008202c2400e02c0103070540b203010240c40070761400d401880c0400902c2c1210981501600800039110894201c8208180140c20030403c1d1055841da6128000d01814450040d41e04c162111004241400c0c0a0394141003104d08141c0c900740c55031f40306001500e0035601d030200e480c003000c040d86403400c5111680c5c9030180701c10b0b4801c0000689080603414058003008800519040d54410000ae0040c00d800131030903001032a00140114120105141c03400c003034000e90703001c2e5076060003040c40b407400c1000440d035039440342032107020401d582c16215010500f03035420030180c41091400d0355105404a071080b40104030300313801e09003200c0ca028010264182241d20494055585030406942032040000070b0000400802044000744221004c0f015241c84c00d02c4184 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 99055863 1250 99054613 99054617
    0xb0601260a060902040b0d0501050910060f120c02070810020c070509220605060117010b04090b040e0601060c050601080105010503120a0201090210080618040512090a2409080a12 78
    0xc000601280807500180090f00300307020b0540d102c65580c0000912034000008140000c0d05080000c200c501f014841140f1a401e2001c041002c2c41c54014292210200c5034881e200b04400003c419608208600540b000700985600074070840380b80141d8542803030707000c03088130311050700403c9101a2243c00058480179600110381c1d100b080d0716124000700d02640c05500c001101c2245c0c114150074009503034400391161f0001e0302c40c112075031180d00c3c110400345000d004070a030407001484240301c3c4004940c819007500c036014000140b08440e0300040c07440c01038241c0c8004000340a00d4410000c00c2000e11502e030040407058000d0026505180000e525051103112241d500c070070100d000c40000d4401d40000040a8000c0c0000e2089066102c0041001c1c0040356054060741c05181c44070102d001c1290231604c9103800c440a441514041c4451403141d5100c0302034294050b4238068040350310340344d0b0580f6200010900b0340901206018220240ca0303894550f00c24106900a48100d01c08245954042c030b41f500418 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 99057113 1250 99055863 99055937
    0x30f06041e06050a0c1209020a03080a09050a03050c03160e0705030a0f0f0e16050105180301060513020c0606090403210f020c010603170a050d02280c0b0601 69
    0xe00518001c480328010007074400c42c20582030103400784c030035442800ca202150b541c0381c0100391221030782420794448140086d00305055003000c00103d094a405401c60045515051405542e144002010b41c81c07160000d45003a000101d03030311060314080000f004034641088119014601d8014500018680207141205000e000000202d00080c5036004065041000b2002c00008000c0d410343c0004003048607170600c9a21401145c00c0d10724610100c100c0403220140e50f80c5107080004820002942040214150559212000420550f844c050740101c1030340b0705807005803581180c041c1c1c61300d0b090010b0320550090f80c04e2000d0001095200c82c02c010300f11111000d1900d00100071108074003e2010710b2103ca0f602d440811200d49921043d0441e80c100c900070505c54046101d00c94170f150851051404010104104104500c1038001035005003012043c0c1540e18152a001680100f081141e1458084000b8020310a40d4040200411900703030080c0c0d0030b18080782c040c0e0f43d03028098000c50031201101262010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 99058363 1250 99057113 99057143
    0x10030911040504030e13150504020708160b07031503120507050c031606120b01051c020408120c10050408030612210c0d0507020319020d1407060e030f0604 68
    0x4003100d41155410180c03040105252604000308880c80c6070000074030510346944858115485801161651602e40b45680240d9103860100710081d031210170201c4000700b003801481000c003016404811500e001c3e07800080346103400da40040440742c40d4a1000b00502165405102050100d08a2442c0380581e051956544801d420410324000000b10305030361501c514002c04840480890b4408102c1c2e115031a14441c46042203614015036200002050000b80107008024070740810380c9001804020080e00140303840d403155000344c145410030621074068000001c04c0524030318104117448401080c8c0c0000c2100382420368403282c180c4405091a031050403510342400d0004424480800c1154200e826500074140f9584602d0554001304030815031401800320602c0e201d03000c1c00489040c9a40100034000342c1c8508010521103030711014060760406140306d80c00d000582852003425244d1400001401450314151000f08840704054503030b4082e0704030111032aa007400000380c440d00507030301016030b021001d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 99059613 1250 99058363 99058373
    0x50408070203070f0602010c05040e04080901090306110306100e01020d030e16240c1e03090b0705280b04020f061903020a0e01110a110a05030706120f0902100309 71
    0x140c0001035814021544006510400310011034101c650304d4000b400500d54101d820765080c040c521550300d600744142c00007000180d02c4001041401070504000c02e0705600c0e6150a82210520300d02c0d02402900081848664500700075099403e00843c5403c031454200803000079101c0d9075540501c0207040c0c0320721802c001000c0911170000200840c1c151250030654030355508820000b0514400a11515440754a951912540206d103210b90080d0302140024025044039640139040344007075040118601780420031400300002400f4460207a0014203000440044c2d1034007002122030094100f0f44101c14480010b155005c200390b01c00c0d0121a2811083ca00d0300c040f40b4984514000c001d0022207071000016032a8050740507040200d441c4e55083c3c1c84100d41e41c01511030b42c046510660865002441c040c00148083c46154071052000e80407104403592600480e14201460300b02e80085400b5400c00030800c0050302c58060000c1900000788100740907a008910b0503441c400c002410591203080b000700b802 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 99060863 1250 99059613 99059617
    0x150a0b1f020c042d020315190b0a0210060806061009050d02060d021e04030b0f01030809121e010e150103020d0209090106030209010311120c010503060d1407032303041503050408 78
    0x400004c4560b20303103072071408000b0b5000300c0302032440148040b45150181081c14411000520154840000500340000305d08560040e01e412000c51046c1c1c0c0f020007252240b0b01928008048050046c0803c5c1090000c00c2100401d43c181a0300700020340070204010b44c1c8001c00c03112050740585070b19035100314000350b003000380c400c40440c104e006da2088020044d4080c240000d004490041015100d50344234180580742a000078031025100318800c2c0141491480d080780300e030549050400480304100221200d840c1000d482c04c50303070003050b592140005104017040c06881e0b00e4048944085180c2c0d811640001d80400020501038018050000045c895080952019014580040c070701033880d81d40e440c1c0316040d8460502c0b858024600000c6070845414001200102504143c44072811582c1d0364003481222000b8800649691a86d007814024000050003680d01a40c05403440540c042038410f034000c001d810b10004030130103910402041250010410070a100380311907140100f00c41d151403e001c9007074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 99062113 1250 99060863 99060911
    0x616050901050f041e08030c0a03080603030903060f06040606090f1203110703060b0a050603040c0b090d0f0804030201020601080303040f17090303270a0b0417150a0b1f020c04 77
    0x2242d800a000b10b1000601c0501c460b005c586222105502074903118269203900a0040c450b060b584074030240d03c0000e0040c814242c0c02500030341101c0c1001d005500090ce0b00000350354240203030800c9000d00829083c00c0c011600680464140030000a1520300180c044103481d2045404445000c001c4608052140c3d00914104020204454034030345c4031300700b090040106190040c42341c0301b039100004450030101c090302d214503008030440c070049151401541141d407080d80216440213000d00064002070320b41507800e4500d4018070343d03507031217600f035100192401c241a04039801da50320500c108000a5085880c240c58590b01120f03040c02000406044611350140d42c1560303903d4040465540c00031000c4d0020040f8400c0c40313605d10301405c00f0031b400340302022103540a03c0801034810441170054cc06044100c800c0301c138441d000c440760079904041c2a01e610009403400803d40d82c465084103040c2c603000b00045041030401b00c0241e00011103420180d500e201541c01a405a92210222545510b00928080341 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 99063363 1250 99062113 99062137
    0x10030e0a0503030703060f080606010c06020408030f0306090a0603020622050a030b16030e0a030e150301290a0512060a0306020a020706020f120f070c090f06090e061605090105 77
    0xc0a1034034a060340d1a50011078544c0e00003460a040040c545d403c5860100450790184040c0c589a243e8000450b500c0c5040001910026000c000000307240e0410801000c0c8040d00545198582c1400000c100348400054412403159041c01014270160b911201107402c5d158950307550192000c031040310300300d2012141c0d10081d40406840800810700c5100300c0704c0c9200f04100c0351540c99203580c444041e01118500d260100c001e83c000e43ca03900000e070046282c0b0140d2080204440508110880316484c0c41e4800d8010704e20810000340e1200c2e42c0411504400321090700307200712504011401000131315074041c03000b0078480200402e0100f9099207440c1111405503402180c155030f945080c0d900603540c0e00307591140200601c01d03c20012242c01d0080f0304102c10310b10321200d59107411780402032582e83d6003004170140d450000b01c1c1710004a1414506c15a45074141d1400040b42c5986804004421101006070044031504000104420350324085000940302c13030541000d03615601c0d40c0004982c64082c29000041e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 99064613 1250 99063363 99063373
    0x1b03100306050f0a0c0207140d05030409050702070e01060f0c11120105040602030114120a03080601020304090903020604020f0906030a03120b131b1e120b030d0c060b040e0c10030e 79
    0x2003c1107103001c80c58030403150207000b17011200c0e0040c03040303980d585240700b01040103400011503082d03841c10400081c14280643c2c02c490901751078000040c00c0f01d5042c0e500700003580c00f0000401c8000b4910400da4010728040c100032501c50f458600281000141030401000d91910103a4510290340704085181c10018000080103c0d1030180b402400070b51081c02840003080c108a280319042c0340c251440f034010030648000d020206e00303a5405841d0100058100e9040d4041404080340560f542d21800100354040d900508175801c090042c0007004900303205150140c000130301040503588001038291044c035410300d01202d0b200007140d4450002d008607603030150312000c42580340d5108580c1d50009036500030440014605003e0126080e2842c000803080100d110011241c1e841c01c00e03000d0075001c600c00407050400b1401c0038410002030705003220800100040354191040c003040c00a1480751510001040e9020040485180141e0740e035031060f01c2c80c0070310a640305811202a00c0c420b82050f805160810b0882d5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 99065863 1250 99064613 99064621
    0x51e01062c060f071104110a1d0a120b0f0a0908120a021309050f090606010f080903040506030915090c012a060203070206010608060301060302010c03080709030c090209040608061b0310030605 84
    0x3105c0005030700101071003141044544c002800f8031004a4248820a458010004134a290303d030422a500b844e0032540402d20302c800042c504809014420310300d1186402608500d00125000008039001d403000307103800e181201540004411034219602c0100c1a04c0d809006d81e0381008a0020b0704c52019500303002c000ca000c00154046480d04400d0107981c0d0f10b010300c000307580c450040ca41d9410080b210940041d21402040460710f0080f4a00c0b50402d407040145c03880c0c41c1e11140400c0300d641c801d0380d51582076480500380c3c0c1c0312500001001d82c0c000302e40402405031540d04200080000c00c03401d00c1821611040d418681101101d084d4805016038040f10079500c918181c42c0103903e6100910510003c130700140c000444502c0c042c4607800035240c0c140c554060000c5c45031001c0310f4070b42d0024000824015100740100110750311252000080c40c18030b4026a44081080500c000c0da04690301003100381e4000d20901400b09132640501100c50400c07096180c1b0390b610403222950b60002940081d0045103400280 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 99067113 1250 99065863 99065873
    0x30a0e0714040605030109020906060a050919090b010207062003040f030c0303080a14131b080705010905031617120406181205060f060a09051e01062c060f07 69
    0x252101c0d0000c880412800f50303a44149801c1c0c41404200940c0003840c0e00015100745028005401d0300714603880c001d800c0400c00c60124000440e4002c0d820400d07106003208004c812040c3c0645108242c00384090300706145408006080030200c0c43e90704000c4054010b28000c403402c20000d0720000c210341c07401d04d04c41d6696400e0002d400541c1d80019000245100c4c001941d00903180603541d1201444032801120b075030b0300008010b0b48284200e00715010380c1840440354021001440303141c06040d01402500b103440c40c1c0300015000c400503034445806074200c00d12200900006038400e400715504038511094039651903031054103101d03c40d103111401c4030300030402180403984541d40131070049203104c0f030303c000325203940250f214000c0440c4003d00650004000841545016134065005a0090081003401da140c0310b1400a07610b089514059492500040d03031070b80e24121841500605060030100380c20b0381b40b180d0310007400009005c10075034803130721035501c1c2000e0b115841240e0390303804014840b41d101c6000d480c2c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 99068363 1250 99067113 99067139
    0x30806010f02120d09050d050408030a0f0c06050a0605040506120a0605090309130b01080a0b03100b12010903020109110109030218060d0b0a050405010606030606020307030318050d0203030a140408030705030a0e07 93
    0x416261403142074141201f6a00441c11101036520783d000950801aa001e01120780f0180803070074404024a2002c1c05c000500b0900583e030140e650030744041885800c041c00d2008941c4010f14a80c8580071003101c1c00300180000c6070303d42d402d81d0030800111310343c1d4680607070070314521605801941111500c2d004400f4400d184d441040c6422090380c4160650b103922045205684601c036000303a040c0c1101401c0f0101000980c01002c1804000d070003541000491504103003190380804099003d07075101e01c030040405c456800341c008604000d00b41852418291b03000304080e50460b02ca041c010080c5070001c17540c15502c500701102520b510050b840d00c0c4d4900149200e02a000503101240d9640c2016408140540070b401948290b681907401503092054a03201140070f44004507440000da29003124903004503200b070054224642e079035001180d0b6400d1404115040b64400014207a010060909202c005038800c0704803a002020303071816684a44496044000800703000f030148402d4815200d00042181441070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 99069613 1250 99068363 99068381
    0x209120609010b0f150a140c0a0507050a080a140c030a030f0807140306150c10050103030809011b05070503120f18031201030305070f12080a06050d030806010f02120d 73
    0x30302041d4090002e020101c1c030406015640700c541c400ca41050140090090140002c1c3c03407a002a401f180b200c1d00300c0c4594003940c2c004c01c13240c0020090200380101002104010131054940808591030001c09c25180e085804d0020040180c01500243d81700d000c000c413121031400101030b14666661842d000c2c0c24106040d00500200d0031440000340c20b540180800c100b03403001c0f02d01181c9035903112000c1080885c0e0360441c0c41c1a0715410711911603c2071003002010301c00c1c240c0f00e100103815410750402810b0110000c01100c5160b04107000c001d0301d44010030002d0440e4000e42440d944980f0580781036829401010000d603c02c0c00c1d0740040003d8100c4003441c0b580070f250011003001008070f2101c9003070307260301c520720b14800300c0e450503c01000064403c1004083d0360f40a9400c00315071414135038a41c1c001d210a03080f048000b900d243e0610420001600ca0ae80c01414100c40d2507424202d42c0e50007600e000001030099040c080124035070080b1034000d110240b004106c4515183c0e0750409003c0240080070504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 99070863 1250 99069613 99069631
    0x80c100c030203090c0f0a0305100209030f030a090e19020a0201060302011b020319051c020f0706050c0a030e040605181906080a060e03090a08010c11030a0e040b030102091206 77
    0x118550310814000c0c82200e00640c014005000c010b00c8402c00d20024942c4604d00c40e0f000120042d00001180c801d00c40c084400075001350159440400c2c4042502c1c0ca40c115040e81c405810070807542d94116008010b034411079039801807600540d40e461807034081401e000003c14400318000a84011001e5040d8003c1003928403d8855500440301740c0341c054103020032000c0c02901588403810030301b101c140b0020381160341403180084525a00130100540824144014a1f0000d0f0744101d0031030702c90003024000c0e44080c008500c1d1440c200402c80c0401e0360f8400d1a4030024003408100ca004141f280c8030342d0440c6014010152128015070b06101e01c04100202c1192460900369410381d00300b8502026000320b00840749002d008141030b10389504c0e184000c2400401c43c46c03107884200400380382070b19a000d58500808100d03000080c1950602030103002c0c001301e035003e62210342040101641140d0880414540010140c40001d401605000880d0092082d001e4a0341e00205541d0881c0c0181c3c4002441c9200380707100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 99072113 1250 99070863 99070871
    0x3030e09150d030e06090d0f03020c0105030408030604020a09081f14010b0301031407030c0e0117010c05030114011b211b120c0b0403050309071205120306030a080c10 73
    0x490507600c1885040c003040740e01461400945020038820075800c0b010740002000c80e86040400c0c400031f0030000d8082e02c125081c100c010000014950140a04115400b0a003001e501e10b1425a4842d042c500c00100000c3c852680840e80c0803143e845265050081c2c043c01c000c5500210810f1889401002d484100d6908141401306c820044020000818100c40792030646c107007035074250307a55030031844031641d030301020744c822040e001001ca441c2030b041c40010036030688960b51a5060050010701905903a84d440d12a03030400d040d40e002141d2103c00c032411240c9244070403c4460419004076500c000e10701ca0b0540d010741043d110410700100e8850900d9400340300e040c03460440142c12040d5024040005807040c04d0103d0000f44020490030020040c65204628281c002c81c0c0040e9500e1900400c151400d13030001703501001b0880c840304200002d10141c580324000f0812814169175150355004000742941c01104080f02081154138100311410105500c441c040d501c501b01042c40740e688030224245900c007c1c0c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 99073363 1250 99072113 99072121
    0x301080f030405060403030c02060f0a1d030303060919110d0b0a08070b0304061d19030207080c06041203030615030e0106060309110d0c090f05040506091c0e0301021303030e09 77
    0x800030460342143c10140c030079414140341d40c50a685100c03400005a80100c4200300943c14401a00020200c0700019101c52821040c42008101281500407540b40a50f10800501606a50300c007420b41e44035104002c0075000107046200031025100c04001c40410120100b5000c070204816000352849900a4031642e03280340d40c8c0d81c03056644905900c0350003135881007000840c02289141c0c1100c0140c1524003407510502460740d443d94a0b107290f840035605403034200f04c425410140c1c1485071100400c00303580103100c030380980400520701d0310507449005c807071015204100e010540250080c2e0007d020621641c9140c105601024020b04125000d1250651030200e01081e0580203104540189400100c25007031200070905203c8400c0c020102514885c51421002a0014007400340c003000e88120500422030342007600d08940303021030251103100d80e0b81000e003419074408121b412450305242da510742142c0405110700440e009100305c045820800c84400400300a054000480b81c4088605503800003d640d5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 99074613 1250 99073363 99073393
    0x110a030b1f09090510050a291e0711040c050304060507080f061905090109150905040506130f0f23070b0a030207050c040e010b011205060d17070b01080102030108 71
    0x10301d0010010101e80e0a0798240300c081c00c1c5511540c5c1c410b13500c0303d880601c19101c40000303081075003d601252410340111440d2440c0344003410040c1c022410a810641800c403040941185070305c5007202010701d0703540860740d00140845001003504408002c0c10400009140120041069104580c281c5105043c43c0200720030b0744c46030844901c19003481c48224460784410041182984200604d50001200040085400e43da0316481c02d0003030000c030800258035080780814401d0b5056583c04100011700e000c0030000810408121135500481050743c0450030f906600e001c440804040d00040c0001d40720840308000c000c00040880100300359542900c03a40582c1c035240329601c1240d8000c540c06d8000074803117422028040e4003d40017142c401d0003510b81c0e98041ea0041021100106540349090707448641700400f80d41c004040d440f41c02e41c6e511003407203140740030008a03045a07401e88004080f0f1940180f40d03640340e03626805880c3c0c01c0c1c3d44030021002650f036510f0107e000c0d400a0184064900944d060500e40305 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 99075863 1250 99074613 99074659
    0xa08010c1107030506010302120f0708100b0906060702010302070512041202040e010e0703021002070806130210080f13080d0e0604020108010b070209011514040b0430060f110a030b 79
    0xa138001c008041c1c507800c42d0b00303000350310240d900b030481c00344079803201c140780341506000920207029000020f160000e60385172014255500500c41d41d010314029002d011850325460f0440d80c580e5021300300507a9800c01454903919011007010200320740440400c0200d01840b000c0350b58810b641c02114240110f60749441094201d8207495990401c96100c84010801820805078000d821142401a20480e5540b648a107041104c01c48503000b01c9034147c04408210301e06007801c12030b40719803132416084a2418051550300d95402504003602181100c07104d4041040c014115000344218100034040b031805010f6040e0b580170700382c8089001c20b114034004100600313800241c44401750010b04104059180c4092611054071080032507081007a039075401041c08068030001c000030100c00031880c0c0e8940c5000801c031000303004581c3d0345445900b140c0f00c0031102400c500440d0040b9400280000340070310b00181e94002060840c1507107501c1640401c2c0d282d0100d4040e40103443e00030007600c1304061144040b038280c00303c0e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 99077113 1250 99075863 99075869
    0x4061a09060d020d112e020f030714070b0d020306040f0506030d0c0609050f0a140c0d12090e090c0102010b03030310060c08040504110c0d0c020105091e0a08010c1107 73
    0x4400c1180d00c07040540b40400b00304c0883c1d801604e081810703800c0305010800d880414403a250150000c0e511502c0800c820315031400070440300c0d03c0685442d600611010f42c03240b04426020340300300002e44100003200001d01c00300000304003046c3c1e05c0c0e03660710304043d490000e50004c45849200e98a014140b0300c1e4002c5a010702442060014081c00389a4100700c3c090380c060f401c41c0c41c1580c895039190300d01e2002540401c015004181e11f034000f88030446491514080c80d401c008180c102907017106049104580300c2c0d00c0e030b041c9101e0b840704c6000300030015001b04941111950f031005186a0185040c421a00307400318085107140030030790003402004507101c14180d9034441519025201b03840c000080000c0c5205591403030f6218450b010f41da103043e644500050a03181341c0c002442452200140340c5054080c204506003d480703030340c20401c0045a0940001c0c0c4075008025600d40a0060483d034a0103c42c005030f0b4401404400900129505440e903004600030f200d21003580c0003284100c01c0212103080002809011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 99078363 1250 99077113 99077119
    0x10215060306131502040902030609130b070c080c0a11040c180b0c10020304060b10021f110d0614010f05040e070c030516051c050f0f030c0c030304061a0906 69
    0x5039880703e0100714043c01044034251200b19800000c3da00c40c8881d4002800105001000980c890812400b0840391000192080f8002480ca00c1c0c018000354194009951094803030600c141440e089041c000d41a101d0150742410b80c0c016210000c082006c1c50142d400c1c603820540e02081b00c041c2010060750034840c8054400c0510440322010031456580b4001401c044580c60309803040056009114016608141c804941541c0c40f00602406d038106000116070005130745c40245020f40007594041230a920030a00c030000c0726140c04150414000e8502110044c041640003003007400e540d00c03001d482d008100114540001d0000c4411000031380300b08141d4050314055a50f110060700e9841065508941707000c0700b142403080a0082e0a1803203d403031351444001f801000509034685141808012000415440c5e17000d00c60244070310004c440300e0f14191140d00102d8000c60366652144a0000e000f0302403d0464000751200100f0001001415000080e1003040306c690700740006d46039030800a04807070465486030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 99079613 1250 99078363 99078373
    0x610120213020f040e1b09011b170f0d060506130e04020102070306020c0a0c0b032403030c1e061005010e06070f0219050102062508071404060e0102150603 68
    0x1016140507203108002104074800145400e860714400c0d541500180d1025180c0018a8100200e21b0b03d03c0074082400140420b1161400041000103080411512a281c0600b490309903407008004401703020b006600d180d681d4281e101c000000011005034007550402d00c540d41481000a000e080003816aa0408652a183c010850426030511500302e4001c2042e81103104081001010988038402803140ca021400074000c00342013410300302d1120307480d0b604c01490f9100810801041401c4440c00c1e8000075104119030900c5208100060b1542c02180f855031400c0c00340159280b180482141500d10400b2140d05803001541c9200100f580722000c0d200e628080340c891340c498030071132409000a1a00e180714000c4038641e92006e8010a00e003d004610440400810000c284259031301003010745c2d4894652a016001c1c0c4481600d8040c0740d1401c8113015082c42014000304072440d006141c840f51401d020b00c011030312140d072142d00400306c5203401034007809809440490352404004208243c820030010340241 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 99080863 1250 99079613 99079649
    0x2011205090c09040305040f09020403060506010c02130902120d02070602061003050307060b22020c1009050703020f01051b0c090106081b0a020a080c070e0c1305010e0a03020910080610 81
    0x101c0700c2030f0000d100300c0c2004400c00001c038011107a21045000303402405070041e00c55080d032905d00210740014000703505010f041850500140e60320180c1c02c44241545001080b80380c05840414180c504202ca10f141c90f00606003190308130750b8005182002c03a4082d6007190400d440f0510f59140f03040d5140000342c440d030001c000000c0820810f4204221500e4081c2442184190701d0012044a1640043c4a18030035000241c0d5184070004100c011200e21001d801002080402c1c1d032f44941d07030705a91000a003c0d20081640d08140d07030080b0141d41810b02c2c0204000500b4032040403594072400f084260303c1c0b04070045400401d01d90b00c10403000d8070903000ca80d09504c4004041134002d4158003c207503260110302c41c100c1e1003030000e50050084e1030541c0c1c1d450f0003052002e0400c501c41c0c01140300106100805030090040310002c0c038051500404581081c00d0803050000d00c40301244046115400281d001071500e01444100b42120380002d04031504802951250380301c001e429545050b241c400d4200100c1860004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 99082113 1250 99080863 99080869
    0xb040612022128080d0c020d020c030307110301060f03080d060b07030210110c0a030210060b0906030f0618010602030c060a0209011d0d050619060e0403050d0509010e1902011205090c 80
    0x344444100b0310003043c2100180d43e60b801d080c0c0d4448820030100340d8440000e186255010800b0403a1000c09001501c0d2060380c2c440030a950b405031440152091942c114285445d480030750150000e0304801441086d09030f00c1e13041c00d400507840704440c011450303c3c4c080001b5107002d50000742c03001c40d076055016050020030030301c02c2c10250440c1620029201410040e5502d8001c00308460402c49111b9000b50240e20202c126581c03c48095038003048012104001c1154640da984013101da0240c015a00d07030019803681004100c4040e24480300610940505001050745a000006040d900904d14200d92661391a15080700590080303c201501040309940c01d035050702c402501800e050003014202c0010320f100354a4103031a00405440014440c040081c030307150342200314000d20f0081c00c45a02c1010490916580085c401d01c02c0d40c900440b217503650300c003041042c20203400505845903140c0854001040810b4121b00401405004074007051200310f9000c030018250081c94070501194026000d03408080c014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 99083363 1250 99082113 99082153
    0x6140f040905042d0501050f0705040b0a031b090e150a1202060d020a0305070801080607090504020306030a0c0605030601091d040f0201091703030403030e010b0f040b040b0406120221 80
    0x490711212030b0703034580600b41c8440d001307520044c0004e6210420302d075041c00c10900310744e00900f00314000c0d200b10040209042d00902190b04680d050301000344d81d056440000c41c0180801420000c013181044d05c104262640f10804c0d07004e44d0029586211291200030303005000465400c1441d400c90114101006118920114804514005402c0381d1a0a43d4040c4003401c9901c014011030100f80c7d80c2d002e000c920740e4030110260150001600500701420068005858221b4a100300c601c150f0b00000082c1c41610244211151564401107440304e068503804c0181030740d042105c04074005005401d000452040080396090300b540c843f054418030380c446d922881030510b485801a8140541030a00150301c022003000308131003051220245da02c0c0d09141c54000c094801c5c0081c80b048036070412040e2003d507514401c02c50040c000441d8005803e13806c94001c83e0260180b4008198041d2900c90001800d5104664003a0094800c6070074035040c0c0041c0c1480036062000c040c2110459100700320360043d203004d85107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 99084613 1250 99083363 99083371
    0x510020a0309020916030e0a080702041107080316030e010612020607020a0f08100f02030402010e090907150905100318080702060f07050a05010510080a06020d0b0604030c06140f040905 81
    0x507022800032856004a543c0da90306682c50450300345810031400f10f4a50500c220b070080c00701a4041c00c408400f41d01c81d001c59000e640806031103959500400640c106410089404040d8004a01d5850f4505a211805502c0300e1114800110781420144014010f0620510003030390198401d28104e0100d0360240b01450704880707001c076040218990041003800c41101c007500100224401000018449400310003903800c2c1600100055006009020060782c000e440301650707030015606503203079039034040020b89840c000d603002d403043c0605030310756403400f40c1d01098150580d44207445a500ba03203c05481141121801c2c1680c040d400100240d8100061080300107020040c0020040750801e486143c2c81400ba6004800482c0c055000040120410200780034080e4424450f880c12030440c0d140541e0075072646942c45000b07282950020704200e80c10010ba00411141102078080d070b8542e030302e03807810ce10241001c0c0a60300204284060a5581d804a5822035101130501c0c1240c0c0e09242c03400c14035201520b0094 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 99085863 1250 99084613 99084617
    0x702031c0903060b040b180403020c01090f0528120507050307030b0106050a02070801151409090d0507081605070501120501050105042303060a0b0f06031b07170a03020304060b06070510020a 83
    0x40e010441540c0c455900200500b0b1400c1440310906142c89c002c0e140990916040d81800f2803400700b0840074501166010449905072512200301000912002c00c007a25000354250043c020000032500c15a4001c1c400e6180d803042c021244420b8407042015910f250510004250911030001884082e00c11005040300c2140741c0101c441c0c203a120030103d07003590100c03a1050440042d10000b0050080002a0705c1002c84040d120a4141e00b8114503007034803841500030410510400140350420402c1c8e000803204070b62413201c1c10b400e241d407143c604a505c0e030034580710b49030000b410b0300380889003141c3d1449654105c45058545504d0b0600d0300464107241ca442141d500c4403003d0030030440c200d5850920540d0310944551600049220f625410041080c0c1d44900c003a0042c002072080140700010380e800c3c41401c4251010f0f050700c0b01d40600e0203600a84105407860036500c004a06a100103402d500658010341c4940c1050041880000c2404032500401c070011b800c40e40207801d0451411800e9004100c0c2c04240c1c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 99087113 1250 99085863 99085871
    0x150c030304170f0711040f0e06010308031b190e030f1f140703050a0608030403020307090e030f07050609010b100e13020f04120b0703050f010b030606071202030702031c0903060b04 79
    0xc0c0b0f0310720b10140c2002c802a1000142403148605c2d5240034402c1041c0c0c55410b0208000d00400c441601c1c1d80d413401400000c5c20b1303003800004640080340216079101c00c604d4200003540d0307408c0e0401d0090403106284880001059404005500070701e40030075414241d502e000010009810101d03d003001c5111140d0820980f1075940981040c603903100c00c0880d104082907100441c140c10100c058800725450340d482150540c0090005200582c2c0100d285400c8032000600800d001816021060441c49601008003000704002a00d108201c1c000ca560b507c900a200b00801140032300c403041c401d25069002044000a103e011a136416203000c40701c1840e541010a07005042000103103841d0b80550054101030f40300001c0400782c07002c000306040c3c5594401144d1500340114244442d0380015440180982b00100c0d401000050180d01c8050558120741c1c1c2091301507400c40803204001e9140e60060300268000c1c040c0305030020a0b540500c1403140c00c4a050f984141c5418a140c680300010004920200d03070003130711 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 99088363 1250 99087113 99087127
    0x10b1017041118151003050106050f03190504151103010b07060c030608010501141f0509060d02070b0a0219020714012a03050a02071a04090c03090f060605150c03030417 74
    0xd20310388681315440303114a01c081540200405050030380b00c0c003070415041000520105c0e03444002d42e40c003100341901890b202d44641c031203030a607034181c1107100309601d280000b000240510103c49402c0000840c008105501c0450302d82c0400e84424000c01c03080fa00304106520014285522038148090715207070000d07105d42c80b11200e9003512000e0b403102c11805042b81090550349001400c00c505081c03a9022001030022402e0050b0190043d842110f10601003c940c0044640c4950104c810070b6611000390340366444c0c4210104001d40026038000e12002c2c80c9022404000e00014880301030300c43c2050301c604469811401152040314090310440b0001540c1c80038285a5502d044604e0030320300c44c1e182c0503110040fa120091412103550701100d06140c9080c1000c100500d06000c41e008d0740d050382d41c04256200c01440c141c010f007170f0940c40100407110030300001c018008075502c03080a80e2421a0100c104500c4444501030500030822110b2058104002080000c0d41c290760f000090203141401904040c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 99089613 1250 99088363 99088399
    0x120e0d200a050f0c0102060112022713120c0c0302060904090503030103051b0108040807030c0602120702010f060b0403020108011e0810230c031602070b0a02010b10170411 75
    0x10307800ca41540c82604040c807031030010701c11807000c0d9000f840100200d40c5414940c0004010141020b8041c3c104a0719444107405000300c1003c0e001c807000349040d030905005966000710280c20109a5a0800c5143c01d9040d1520840030100c1f43d5400040070400c081c110307020000c0c03680c0300c424056840f51355001034a002403000d0000d5402140180082e0900c1c030b0b03d501c4018a508241c41000d03042028190420000a60001c01c1d5a4119007600d05a00e5032003240c600140203100f60080380822140380010043d8440d4150000104a0742600b818400d85503145501c09490095000080c040f41d10540140b22a000000700e805881201400342d03001c56507a1a42181484410380d00c041044e6160500c0c01791810415181076410b500395200f0344540c0c50721074008486400098040380380031180c155003000d0503100300940760280c80c9103281660f44a0807101d01078000c080000700640204014203220285d140200d00341545040014450709640da541d07a101d214400140385a581c0c130018031820421821 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 99090863 1250 99089613 99089623
    0x109050103060b3123030f250509010e040501060603020a05160203030d020a050d0501081f0209040618020403050708030a02210d02040e070206090a0c2106140106120e0d20 75
    0x5c20001c0090340507410719081798404c0c1d0b00b050195005100c0041e041400082a10850101030180d4241d603084c41c1125141080550040b035003e9003400010400c90548519036000380d110b10300800c002c95940000b50180d014018040f800b250b000d110658001c42c2c0e6040c2d54401c0762000b400d492505214a50402c00c1743c1001c0c6820000940c085801518042184619800741c041840240311207035104180b400d01607000d4501100464001c01d0b02403490f00e40f0342150003c2c0c418040762111700c4410650b150000c0d041840266000d109000002440c81000300845112034aa0b0b8081d00c100b048034840300041290a0803031148a0500704100110100c1501c00f07000980360240e000715183c01c0905001b0701c0e019004d49908582d4005a004100144000080d40200c6402c13038000005150f487c800a89510401840604100e050406106c0c82c91100000a4144c84064580c521552407070400c02c006c944500b08554100d50101d4500c600304c50207030144d80a05440300c03011081a04100700c5582c105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 99092113 1250 99090863 99090869
    0xc1205130b0c1b0d021003240513022215141614010612080d0c090b0307030b0a032a12020d0f081b0c0109050103060b31 53
    0x84010a1008889044228410080c072000c0d040c81d050021180040e42c6a903480e02c003e038282001d004070800300d6141d0981414a07150000c010f80543c241404001e0090720b180d902e004654103115000f1a1421910f4a000c4152100070b40f44100702d000d09510b1000035442801c4422150786a0140b903441d5014512840d0050f1200a0717282a0b0f1549540019006200c02d010490001c1c000f40600302549541c40084021150400c808091280240600c0d900428064000d01c490f2410115030105004d90314000341103400403a4010018102002d2080700c2000807802455001c40041000c2400c0c20711a0b0040b20b0002c40082c100803140d6920390350110031255100d407000408a41d4074881404540010001c0c0042c04108480100d0095039400220f0255401100038218400a040300301403007502810340c0c84040d141000822604500b0942d0750755010740707400e00b0380052207194000c1140e503c00e002d210110380842a42c141009088030b58100c440d140318190306e0b01c10020025a08440291600140c02 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 99093363 1250 99092113 99092117
    0x90807060b0a050a0b1c02030c0306010c02060d0603060b090f010602150a0b0d060c0806060c072d0803040e01210b040f0602030c180a0308070206070602040b0318011d060105100c12 79
    0x46c411011540a09a20441c2e10364a0110710510420076003c0023203003120b520640900e441c0c8480080c41c80014114000e5a0300300d1070300e40ca40300021041020b5640310b4a00350200700c1e03100029941c0e00c0d041e600c1c004400d00443c1e0068104504c1c041c0080403000501e900181d09600102d900b1012001003501091000c60644256441d12042c05032320380c000c04a50f401000a955892401d4050701c0300e0b5690348098404d129030b480504803242c0c1700e02c2485030541c40b010f0440031001c0c041ca1341c1d9030a0310780d0b035041405010151034990000180900d100701900e55480c01a00c041910310083c2c1c2c981c41c80d4840010004c0c0c540700b095050100014601c0d100841c440e030710f802000d0351543c41c1c8591104ca403501080301c0034000d0758150001d01c04243e444058584056048a1071a44d4422030f00d4110302a014650040708400004401c0c40b00c003210075508003c6141492008225070144240c2e8894403440c50710700e2000d107400100040c8442d0a0544007848180001e090480140c043d50380d824800000f1107901d600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 99094613 1250 99093363 99093367
    0x80f032d04051e01030513050601121a0709061d0109030602090103020c0a050d09060809030f030709030602040e010303080705182103040806150d0b01090902040e0109030c020108010801090807060b0a050a0b 90
    0x915980c05215160b0000d82d840b2241054602a40d201c270399905060050500050030400c1d01820030054817010310042a04030f5846c042d5040440c00a051449039016800105900950749403520709400125202200c059503a41311141c03a6440f598020750010f03901a04041c0c003044101c12450341040b0b06d5514030300c213600400500e54444d0b4014000645500702104100b600400c1c0049948004103586152402c4150580c3d251941c800903695541d4a5100600e05800072400040ca88600f40f1200d040724004e8803000c0c125a5051001c81d01c0317210324501784000010090f81c00d0103a00341030410110103802d1174031400300c07050f03e681c0c0c551441d0001e42c007400d2564030110401c080300c84882484500400c0903034004d04840256075030344050b80d034140603050165549415203415560360760022186103140344003c0240484a04000b07100e64150201a40482c228800005008805200e03800c1115004500c040c2044c1a41d92844054501070a10030390040f6050004109a030b12403001000500580040c0c603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 99095863 1250 99094613 99094669
    0x92101020a170702070b180f0a090207060c0507030203071b17010501030204060503160e07020a020d030509090601110a0b040212070b07170403030806120a08040906080f032d0405 78
    0x34402880043c03c2e9030864001041c200180c481d44001d65003840320908440d091f510604000c0781c2c1582c0180b00c4560b0242d4080d00c001032a1000340d005007182802440d00f405910070210302610144541d0800900680c000c01031103001c141741048813440b0860089410310410b07601e40c17150040c55424903040c1e406075920401001103117081e20500008260950180685240004862140c902103208103007000c0042800600224400d10809030041d90040440d04005c0181c02d004155400895215000e481c1d05d0011a00940c0112032290000074000700a1022011030754a4148020700a03200b03d0f0001608202030b0300400044c02001d0290201a40d810740f0344000b41002003840c00c15082620008600b0842030010950090b400355001c401135454000000c101803c032481c1c0b2980f05c1c409041c102c00458041448007032608a0b1040f00c401038125500060350145c400e4482c03050000042c58400741c03408010b0307a091903402c1d40300020061045c407410613076508045050342d1100841c0410b108001e41d218 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 99097113 1250 99095863 99095897
    0x1d0405071d030601030b06120c100e040e16060f0207050a0303020c011202030c040e131a06011115070f21050601111504020616170304020a0e0c092101020a 68
    0x4035a18074402c9000b4460741d40f450301d07582c00320000035000720300500400b40c02181d2a5010001c1001221000d800c0308100300800c0c400400f00e200341c210b1284224180300d0140f0482c1000500e4607844801c0c080b62400c81c2c1e141090a54143c1281c68020055000f1110001510f540750081b0100860007038014105441c480c40c001000802c0012001481e03d1043c0148500c880c02c05055800b42d0b1003402d5100402d0311608400428130240140c0100001500d038210300e122190000300500500080e03e407001c4508a48030000d8075603011303040f00000c1440f1000001d22280c032814000c2007545550a0208003400c8038010f903802c65000740c980c43c0301c0f5619103082c031026591040d40c05082001070030241040f02c18991520b8079a90011300040c0c8202008600304111008998400709040d034001a481d180320482c1c01d01c507440b5081107809070300c641041500050413401003801984170355043e540303203490405030f141002401c09a8036542075081e0440c000320b0714020800d100801006003941c86002c0c200c1c1d1040c0722 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 99098363 1250 99097113 99097157
    0xd0204091803020705010e211005090a0f020405183f16060608031303150902150d140106110c040c050f090f030307200a0f05011d040507 60
    0x1c0340078401100501070100781d0208955090365003d10303200c4107044040000900915241d010122501c03c03003030040d095800c0004e0440e640010240d001d020a550708600c0c1d0b03448006411003d040d000c214400c10b401442c00e5480541d110f01420030380400e6079060b4070001e14080140410109101000d02481c8803400c100c649030b401c92104441c00e005580c0c5000b0f0b0a1000d02a18030328030000307803044000b6001c000e007a801140162100d80100c03900c505008e040c06003448a24407091760001a2140b0b43c10001065010b90803103507070040d0640c020f2403a14214406964407803516492040e9803a418940c1103810310088038020019503036285c88800a8648442c20840c03012020380c4154038102042e1982074004081e10003c1c00594107464440692001288103044034203185581b41c00002621010490042c02c0300e25104041c0321002140b2141d5400c1c411500998020f2082551202100304502c1d84210980083e60306141d42540d0601c0f4407101140c1603c5094031500041940b1003074a0240750060b860b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 99099613 1250 99098363 99098381
    0x506090715050a08090703080c2104050607020d030201110304060b03060a0c020601120309080703052b08010e07110706020d11070e07050a050c0a0c030605010608160302090a03080d020409 82
    0x1080900c008100e180905180b04483c2403d09000400c40003502000041c82136100441d04220318983e1000005412525441d0010a45134216030407400c000e40b0079a680150380c1640c2000e1308052401030503401708141d42a100300100c003191740701c0c00301c2d02005480e200a1409688150808240e1008042c101800c1440081060302880d1400365540a240d5001031100d046130701440190051030b00c11f0030101c2d041d87d96a00007091921595030000200200001c0c039142000494104011140f44142078852903d098614140019003e01c0180300f003000380510560400710034100003036943d020280c00790604e0000d80c40752002d80c0090340c0740c00078103401450001c5910a1600600111420100700c0022450043e04440c2044000301e20900341c1c9006808030303244400c5103400c40f81c010310a45031131603c2e403286000c122401400c0100014400303000344004c41c040d40321010b52641e6500003010490080d0844001544c2c007078403a890003c0810803503001028015180100907a946007420046016642145 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 99100719 1106 99099613 99099629
    0x6040803070306270513050d080109151a09010921060b0108070f1101060914090c030705010f05030702550f020a030602030405060907 59
    0x8005544221059a0248489601c2c2c0000707a0040800b8445521001941c007145141d60505411040c0d200006208041c0810074503100c581c03501c0c00c98907001c03020a07a00e00041c0801002c9005860a8640c0102c80321086858851140518204491011160500844c8a2101e07138403c40c02c410003007030081084803c0400c2148010040a00e07480b08880c2e42d85003100341c208a5005000d00c0303105162544031184d24074141c3c541900c00003003e001c80a001e541e40c6d2000729940d80e19100e006c207101c040e0102d8099515100c0587ea02d401494070119110f680014810003080c1c0e409a071408005150f0301e4019100d403030f2041e0a80c42c141000202210820702c0114945c200d00030f110002c0c0114498404040e60850342000040300031802900d0034803031a030901c203107802080303040d4841d02c10f052025001518559407900c0305004c0b0f17002502c0480311a00000240300e0540300c00c00c03e0300080d051030 = true := by decide +kernel

theorem cover : BRFrame.Cov 98920863 99100719 := by
  have h0 := BRFrame.cov_init 98920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 98920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 98920863 ≤ n) (h2 : n < 99100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
