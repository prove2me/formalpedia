-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3509
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:52:09.334849+00:00
-- url     : https://prove2.me/submissions/93d4ee22-5aa0-4ae2-a883-149f5f837377

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 630935251 ≤ n < 631115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 630936501 1250 630935251 630935303
    0x6020d060e01030f0f1502070b15030c03280f03120b1206060d0302010e0f1605030a050d05160c0306140f1902070606090c0c3c050c06030a060305011404 67
    0x80b041c401e035840c451081013840160780010400389c801c480d4880074441240341c18002c2003100c0f4029030241c03010400100000b80c075011032800c6038100ac0054509865440912422907520741d9000115020f03403401030070000c205030682d030443c0050318031300b07503107a5114035200031001c0503408404018440c550b04c00701800341125403064100c0540d900d40314001946441070281d14140c1203090000d00300c120b00c03005200703001c10144d07000300c2c001c2c0c100d0500000030440103d40501c410080d42007840c1e27284075031801c0400380d489041010f4040c495403400401007041d190003100012100011041054807000e2080500c0d5138203444c1d201080090102100441c40c1c25006070003058014040000c0e120350f81c201c85c80035111070180d60800198072201034002c100d8110741d400604c13007aa0740c009144d0341040b513001841d081c0085038401840480041c05041100c100b04c1310100060182250751241858600e0030701804660108907101e50034a0880e401107503000c81d45901c00d0307400c44980074400c0650100c280002c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 630937751 1250 630936501 630936503
    0x1608030319020a09030c120c05090933010914061207090b040605060c010209030d0f02060c1b0f0d0906170408090a0902041206050711121305090406020d060e01030f0f 73
    0x4013200c000000480c4456882c0001001d2001e001c9600e140070f8600040c1101c0c95800c000d00c288241c606000640d9000a030645416081919141610343c401500e00c0c02075034481e0001001e074020100114014809401459440103c40e00d048140e40b55041046810349800c11181201da226120800500c03507039800c01c1d40b407804c01071300004200d620703400800c540e030380310740c814650076900000e0410f0142003c1042c0e00020300c15280c41d003510261400e0094490402030312a4905610100701c10b03141000241c0c02803884421001140c00aa003d03030360032500d03101d0309220b10000c40c5041c800040c0d40f50003a0301d5024150031354085000659900da5501200381c10850885400205c924008995210280300a01c0507010400308031241c0d1f01c6622b0903006492008001100b0850103484e1005910300008101400c41c031221310003901d4005d0312940303e00d1018964002540482c410003440300348140b56000380165a030001050160075191843c69030100001e20000304046c041001400100b420880060609 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 630939001 1250 630937751 630937757
    0xb0103020903011a181009050406111b0f0d080f09070b040e01092901110c030109030c21051e0d1a0a050901061403041106040303021608030319020a 65
    0x1100c1c100100307003102d100d0804c10b02d41c1c11200b0074001c042d20f000a865546001c000303440313441900d0500860501201c5038481e0b0b80d041925100030030100b09158000c10341440030181200d8803200c07040c0d550347e01c0600700360b81a0794034095200380b65001d52000c221115195003e0302c454480c0d07260809400701c5003000416180d02c0c5d020345d19020032418000c20040c801048070003000e14165062480b814200d0300b00c10500f0480d20618a80080114840e5680040340d9a00b42891003c1d09d080126540c1410151211164076519200108007010f4204003d1659036000b0340c60b22001c03814100101e5540d180c01c0301e5410120f00207000b048806051015400d6148181d13205480c00c2010724602481501c1c1005020038003d225000d441c02d150515103000402040c0c1160088500c1d4581540644800c00005540d40100e0300000064107000e102c0c2c0c036800c05500040d200aa440c1e94a0900035110100d10f0003100c10860084000290030800100f0743c0d00602e01a20860904000100584c00039840207460900f4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 630940251 1250 630939001 630939007
    0x90a0e130b0c0c0105070e01080106080403110f1e010e06060613030b161704020f01030e031312050601090b031e011806060f0b1e0f071b15080610030b010302 69
    0x180c0100c0041d8090280c60070602d0300d40c10010b58003400c0d02d5008010600300032a02c1d1390020f05a80c04203415044800c00e041c58240f603191420219440324015000c0072152007030031380c2c102c21355500040c8111500110400e4020241c000c90740b16007a03034541110829540d10076004a40149041c2004003034003440c8000001455035256900745003050100c2c1e5100c0c400011008131403000c1c0e00215183d100156000c0801c0e40c03890a43e0001d1103010107400f81904051381c808600c000180200121110b4003240c501034101c140d900d828100d5060b02411045561380507040c00098108003a01a900201c8001400b62140c41300400d0700c4c0c07124180030307082d40383c043d07482d03035041950140c51000340072042d4019800421042d007072041038003041c50680d01021403043c013040b5544210b07048206c066000c004490b42e007941e420709035107046070781d00941e02e0250581000c0302201001c0c21600070720008903107415903501242134000c54290b56800d012100c50380c002d040c40c00f04c49207203807103035100c44e000d0b1005047c0182 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 630941501 1250 630940251 630940253
    0x1080a141c020a02090a0227030c130606170f040602130e0907060f0212030c070501200711040204060509010305090f121305030604030c030c030c020402030a02070215090a0e13 77
    0x14a420003515000b503001007000324254205000c0e065440b11110038154504002030601109061540f15181c3c188000d1540852490b5410700010484100040100442480c81403085004280501c20480032640d070020103c00c5519840307866102d00400460941c803543e81d51100c50203940140b500c599a03c030341035804114904050074180c000c60916004103000340c00d008001e01070440c0b41c5590702c03e5500003140385c0c40f90301403030302129071084c0800c0f61a80c80d16990700d440f50241451010280319801030340540d0130762401c403102070140d1601803c202202180301c84180401c0340700b18044c050018a08001c15100c1c0c1d40a0b40003144c0000d518800c550484480301403c504014000c0360320030190a0000740c0c0c00c040341c2400c1c4208003400044001d007a0700c0c1001e80e009420f0081d520001402c4c08a0f00304c5510505010300749000304690040e00a664070300e4841c0034107009500c002402c0f4401c070b05808070320a0101940c001c0e80d0f10100060907040915052001010041d900200390025080c4a840400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 630942751 1250 630941501 630941533
    0x903021902060f03090a06110310121a0c13050402090a03030e03070305191b050a03030c1e12081b0322080d0204050306071803080d240801110301080a14 67
    0x500c0751001700081e04c004c4100303241034000c0c4c401d00d4072401c203445070620034840c0729500440007030304480f80c0d521101442240c071319000104074000791040e1411441d1000300440014150300401117441c800010480c910344800401080307002d0304134900d8000300251020700000780101c0c1c1046004100904581815941e960f0705881c040c904d85480c0845403210390329000308094281c0b4182c011100401102d01c00d8104000f062036814107101c054204082c2103900f078140003840481400d01e00300c0c5031060065901d01d04002101408580c502000503002c9400901c1c034850104000e403450712540420392451701c409903901d001954468003c4840481504624001584000100300c0e540d540d580250700c943c44c040c01c150812400500400c240940a980301012400707024008040d00e0703000c5e4030551502405a1030340d00901251094219101e507142100ca40a03858020410444481400a000e1140c0d41c44100905010a01c50070200381d1100c0701c49000200b90ba0801c00001c0c402004841c0101044142c0c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 630944001 1250 630942751 630942757
    0x80a050114100e0429040e0a0201051b0f0606090108033c1210080d050f07110904030306080c1504120501021e030121030509010807020705180114040903021902060f 72
    0xd45c194804507242641c2c0459040380d1801100002c8404000c00700120810701d48403844920000d040100000382007100c02c2caa0311401c07a1403808541250300d044140700c01c6950f500c4054908900c0f48040c440006131200001007210241c1040c056011120311844178400059002c5c034105040c0d035541c0100d4540d43e1009580a07211455031500d91201c5424599002d01c0c003c1c0b01a00171407070f950003c468800350183c004003201c46200300010602d55502450a12074003840162070b51a500609540c144010301da45608503d058410f4141990001c0601104002070311001c48c02c40803000300300340420008010750072241034805005400143c5010013032483c0000c4680e00403d0740c503000394040f00501195600440c1c418404c41ba440301808100312030b0b1000340c228042c07844243d04000d0310300d0000e40e40b01d100b070044d00010003010b81001d10100c603004d405c00c40710f4824010013a04850725040d00800745868068100040d4041c0c0180c203100300c0310703100b43c1d415a51100050340c0041d420407074501803252440013 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 630945251 1250 630944001 630944021
    0xc1410020c03030105120a02102f01050a060e060d0303020f1b0724050414010c17070311070e1b190815042c16060f080a050114100e04 59
    0x10310fa81358101000c020022a102e00301d110254400c0d450100161110015a180d041945c10408a0000c81c10a00c2d1307140841c0f4001d1a0709010903442c0c2901400c0150800e50051240c03a0050000e079403245405101400200c40c02e0f60320200c129a4440404e000b0360041580d41c40704883e00740791120134508001e28440c0f0008003d041da100c650100803404034613902c55101020f88002c0701504c8182403008115024074001c010701c0001c4424500311680c05051032020341039000c0c1c0c10780c1c04070399001802182500101c00c2a008620181c0b29200104c401084032000c4e00d07021011400c3c5030b25115050f00003040340e407a8070036100c00c0400c55416640c20b00f41c02c800307851050356074140315494001014407890500d620076900031420021000e140c10703d28244c1d45512045a007105c1100000106010f180183c00c8550a4403214040d001050035548540102901802600c030502c242c0c580c80b440c03804843c8244500b443e165000903500440d441c01000c404070a045074a4600504100d001c0007508132484099 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 630946501 1250 630945251 630945253
    0xc020d0803160203090901210624060908061f0803030c07150513060b011b08040503060105010503070c20130c0f03020f07060504020d0f200d030c1410020c 68
    0x1c104140c400c20303000c0044242d00540b002d142060f40480104910090602540000c10010010235060490100b085070031650400414010003074000503204004440442d001e4400e40f0040020a00324007507500802181c140c04010b280300d0741c40546a840707240d078003140c0c45d811508141e00010020f50800145010f504007802140d0380742204c2c030300180340e0500c0100d1400703054141020000c0700c00800c41c2c100702ca10780040001c900c0740c080d0740c0100c0306c004100ea0382c203d0b144204400e082c28400c400000d442613410030f404980d85662240010345640c001180e0800004100841a60010f022003e02124004255130b840303100d40d52950000710500810300c45172411680d2007070740c020031071b5012060f02208030090508510b059440380e2400780301c0c80b44583c050009074664001c141151a800030303c000307c540150025141c5c60207480c0c110407000d0030451741004843c401002010380d190586000742c401d541501c504201c895076940e810303d0300502003402800e80c00b0300c50140701c00c020303070380010041240048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 630947751 1250 630946501 630946507
    0xc01020918091f020f04090e06070e06160302030f0c0c03060f3102100210061413051503010e071a04030503030601180b040b03010306180201080c07030c020d08 70
    0x541844401e03001c941c00c031601c803208142440521003000c03510256500102a9980030103081040030301c080c0c4908142d900c2144c20005000035000e00550003601001c1000d020f0722425201da10707080380e00b0560000039940c410003c1009103040401390404540c07251083c01541d042c020090501d82e41500f00f4500d403070050b040405080a94034091110541c8503100814080c860704041014401c0700090140c03515400c507440030841c0389004190405c6842c03680c0186480b00c285501500252202c0060240301c1c8440d0a0139400302d03030701644039200c10b8405000f4001c6034007916035001030800b034400a0903000205500d200030040d40d4030203000e00450703825040014036800c0c0c0b50003003e0442d101880c010090700c0100384028400a43d010044136000700003440c0a20722a0b0303044001c9080c64001c0d5010f0400f80d1000030303000030008081409181241d0040c10100411000516222013003100300c68000e0018a401c0c00090545e0a400040c190803402890134140c81000c0e540400c801c0454940c0c1a44e07a01008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 630949001 1250 630947751 630947767
    0x403030516030509190501150b040e0903040510030504030e04060b0c070801050f06010305060a180b0a09021606110c0a0602070b070219170d0f06030204180c0504051305030c0102 78
    0x81c0c0e858184404146400c0049150030148107445200c88085500003e56034449101840025005680092080d141d42500c46030348041c00e0300300da80280304030328a11a0050002c0c00020780481078504032200603210258100e042c100031801414014000c809019081580a00d107445a1107080040d011175090566201290b001007031400c46a1342c88484160f040008011006441c600c1d6640c21007000c0c00c010038035484040006041c0c0140d81c200709800c4030760a1001003002096000754800c07007400d0303417440c2425481e08032000580c802c0e543c0e1006c1c90361107050030340d0011346194007100400e408024030301e08140c0070780c0406052080b600300c1a10f007160086107020a00c0b081c004002d40040765400205019000102c220006511280c0c004d8403501d17605800000030900007003210401d0501500c1080352003003161402d0020191030005a0086251001e081c4c0c48074240c004a40c0543d800810802c05c443c034000802010344001064108000c45010f2001c4c0012401c0001d81a1031322841c001688409031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 630950251 1250 630949001 630949021
    0x7031205071d0a05010c06020d090506130b062d030c31180b1b030f04152c07050d080a030e030a0c030e010201061509050406080c010806130b0904030305 67
    0x102580c1940316aa41c103c040003541c0e0003070500408107a202c6070145c1c84020b41819000200100340340034006000d80020405486000d203102c4507400e02c9841212030548607881030050290031146a6003405000362050414940b403410312036138103140102201c1b88440c01074089548404081c1c0c9400141d41340c040c4103905218901849032600510503010082450548540440c120920001818442011000c1840b6680b60401041c00314810500a5178a051456524501caa03080b14285d03034801841c8442c0368464003074051884c1c06440703010180c410141c1d0912513400380d58100b40070fa14a220f0540b00182984980c00c01007051030144081c0380c0c0b2511000406400d843d19042e00c0c401903001001190800ca4000609402c0582c2500c0c080c11504007500042c1d00415280d04040002420b2800c0c4420040c0d100004109503001501d0501155640321841980c0d4001d14030a10301094940000914505002001c0c0080c2030782c5840c0440ca1500100119443c4c00060340d00303400080d203640c108101c80711 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 630951501 1250 630950251 630950297
    0x903050f0a02062b091202060a050403020715090f09150f1203210e0f0d02030c0601050108190f020703170f1515030f180d050f0703120507 61
    0x1910102526801036940d0000d84580300d249500410100d0149540104d1920000c402d00701c8220104200041c62813410601d001703800604004006115940000383c42092902400b4052589500240081c0f070034a58201c0a842c0301c0c060a4007040305200c2c001032100c00803c0e014004010705140011618a611140d0b440101c80d81c224080c00c141c00041004040c004030945503510340c152600e503000d802260080300c541b01c1d01c4800c154000e4140081d5620000c1c0114680913100d001104076500a414032406a84038042c441c01c00b071454200d20010851540101c02607540813400c20031141da11a90716200c2030482c1d007900c00c404245540483d000b170403d900003c0220400410295005181c6030040e004c0411180041980660416020b0301c002c00e510303480b5050701c805030341c4010300d03480b850001180085610100d601c901c0546a00380000101c0a010518502e045003c3d41e905240c080110401081a800508114200500c21103510000083c038884d403070080d0503da03920001d2502c1c00110303440d035175 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 630952751 1250 630951501 630951523
    0xa05090d081506070f030f02190f060218031b010e061215030102251e0209040b090a0f030503071106070507020411040806010e2406031909080a090305 66
    0x1500c14503124040c5034200d464903074000c6842c90418142c021a002040c114025154003d102c000b0001d000c204064000d203610aa0766802e81c01c541e022001840e612041e82031a0b00d020f0210054664a000814541e40040200f0011510351030420701102000c6840e12015015005602611140481d501d41e8007220711500104200c88860521180c1134101c01303c02c402402c80c09541350110001142914290150780d01141c04402c0e01d0b060a03521000c0081c50032030007008031107888031103040c46411164502c804002d05e4000d09076101568503540d60100000014008140038804d034404040041d0003140c003001c086200c0c0d0794054403800c240401400e280e40f502200141c80c4c005004000c01d050340f09041d200e030030750119004500004042d00c0c0d00035521542d040b00344580954000840c0806098582d54002c2c1010820380d1150380c0340c0200c00145613201248030381c2c4581d0800100da113040d030100048003195a00680000c50f4030069484030210f41c0541c40102c08981c01442c01c00a0103c14400010a6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 630954001 1250 630952751 630952753
    0x21801121e330c050a0e0a06171902031006030b0102062203051b0304030516080304091d0604060c1b05060a02030c0c0604150507031401180b13050a0509 67
    0x6108165100c0715100035031603a1541003203140420300c10b142e0441c1251110101c11407800c01c503848031000d0080c90ba0344101c00c0302002c01c034101e10a1299052410011003103800998a800e5105d40980594000e0000a0701c1d0b01222000c11a0b640360b1211644011805140f6084a094465141410103407d440e0002c11040c155040340080000c61000102e04150b150315200c030301c141c40701d601d01d0141c0e42ca0041d40000d40f01000c0000c008041004e002004009983c007410880c0e1020072520003410b1f606095008446070390304140002c101c01074040d00211028100305440140980f01354100c5803030300004980a072849610f4450701c0321940c0e000742c00b142e6481c48140300898100b200e51141075462002400d58107c45034000006880c5190800984460090070015500f66040c242841040030f940104011202440c25002ca850b4600a01c6211303024140c5d9003014000da1b1a100490914110b00c4400404054980114034840d950301c0108401c0d401d010040002c46042c03441e062000c03504000d085140c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 630955251 1250 630954001 630954053
    0x2070b01050f0d0605272407120f0519060f05060a030b0901030506160503090619020409060e10080d05030f040609080d09120518090402180112 63
    0x11404a1144038199442621000c5001c08064086410303100141005001189004180090105900d181095804a40c890101c86804444140b51501543e40c1ea490540d10410b8041d911a81c42640c100c1c0d220469080495103c0a03c141301400e48030201140c00c8425520802c010080403924800e0b80c2032072100e10104000760900010200c482c0c0300e0f001c0d0303500c030b0030001c0343c01094184030707030803200c4000c4016000c49031651b0740746007041d943c2e84181c0304203070302c40041c0207007184030f510510903288035000c204001d001030f4580c1c0000b601000e210402c841102602088041490744d010300450300141149809081240340105194082c0c1031190001115a00305443c2030100719402005c0d00d820110604d184e242c503454030714001c0300070100c41c00002d20180c0007080c4066242066440650040e000703941c40a0802002c81d402c036154420000400e585000c121004109410852074240c2e00074409008500310481e06200c0c0001301000b40e1054940500c0d20a084c410480f18014818681c1540780c40704803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 630956501 1250 630955251 630955253
    0xf110901080d121104080d020a140307030801031401090507061d0402040b0403140f010501031a070c0506010b220305010e0f01110f0703020a14100e060c030a020901051c06180207 78
    0x8030ba05411405036a1003915054074030313848907140c03048030020501401210520307100c891000c0d45a5000070415031b0b40728520030007025001c3c404421101c40652607610314066070300b556a4004640e40e100c6400e40150f6a482c104c0e400039204002e038401400480c4c40d000b000318150007082000c202c07003482150280b801400100117901c6094103a0301500ea21209180300035268240141c03814600340d440355070a600703000000061104c0c0c06251a0074000c801459200c0340d0300d00f5029035510447c4032000b480d03a803180c401040f05846120140003020504058080c0d600064601003c3d603844d19003040c0e405940d2420502d017103413000c00c46019907110081c002e02002009052000e002e00545125142501c0c00040302c8003014401c2c84080340450b8071240d2000040c105500465031080d5446404c41c000e0315110b502c41c1c400e07000080c1144618001540c5600e0f580d60f0510a4004c0e4005643d51410f03c0f01c02d01014444e0f00391800c02c10404500c4450014940d072404500940900035038102040700c6104215070306c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 630957751 1250 630956501 630956507
    0x10207030c0e1f031b2c071b0812240607080f070b0f090a020f0402090409170a14030403020a02010c11180402100e130b010c0f110901080d 61
    0x4400c550b0400010141580c81c01d20300100d100d21039010641003019200f0220170801d03030210315100f01c280c410100c0d0f4843c2d02c402142080074071424040401c0da001a0754808549031090f00b89a00402629002c2e000600d19480d4203080c07030b442481103c074040007181400305130071078801450b804000440742c85000c002808a03622800024001580944000036000e401c4c080c0d000101d070350502d01c0326404c070761301d00e190306004903864401e13503100c810a01d480002c60b0560f10000741000d00d10b07400900c0e4107410745c44401000003d600c00e040040d00f00340c4854401006c82d280d40c20301204c0b02140b100c29035454600002c010418502403031014200c0e1814020b11020a60010320001c101340d081c205114014420300b0030b80c00d14100d03610490380c08002d481b206801001e40e84820b5000f907100391a91060100c03a9082503420400c070b40d2846070892541c00d40201c51143c0c0e034015403009041810110b0b88c4500750f881e484103002031203005a81425010850605504014085900622094018090346200b4260003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 630959001 1250 630957751 630957773
    0x2705060c031e060604030c120501141501030f0b0d081305101e030e1e1506010e0616021005031510050406140c0124060305041e0f060608010e070501020703 68
    0x40e42409105800103845611035104480c0030791340110455009560f40c0502c035450400203923085a00b54281030700c2c1096009000c11050255011b00f101c45482003180d00110001c0c40f01c401d0341d044654a811300d04a883d1a80581084458003030700c040c2c0d40d1550295428000060280d0026005001d505007102001d03a00820b201c04244a041e5089040d8810200071006814031460a904500901e54001005514201480507103000c1c0e00c281c42d210307005054000f001440440e0264041001210700010358a00304009002402242840c20b0840d0496004a00da1074520700d0440c000c15000018080c55030701d0500c56556440c0d04803031003003038489142c0c00104540550b00c1032006101e051012111044c00e150140d030f40340d601c03040080040c0f0140002c100c100784075842e5080060380c140400420703524428007405205a800c10ba01c0040804549a4420f50052051040d9030020640c070040c1700084140c0515002000d83d000041039601a404100d41040c40c186d110a044d03600031402000014410503003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 630960251 1250 630959001 630959041
    0x10515040b04050d08070c0b0a090f050303070f05280b0114010e0415081203010303030c0801030c0b030c0d050a0605040b01020a0b0a0507050f0307020d08010b07081c2705060c03 78
    0x30507480c2031107280c4507641d40030b0000e00a0402082c7c03c1c000c50301000e03040142c043d520145c1e454050084c0c0d500d40740702000b4503d000b01c1e50142c00400040d07022510480e00d410755a8480c0080703c42170707588509100440ca000710100c0c0404054681178a0a0140d200c2081c2c1c0940001000c45030180540c07000038000b440c1d000f881c103010f59110320500c600e1b850410420030040c0084c0301900c480107480d083c0e0002c00d500c00d0100b140800e2510351081201c85c8030761804c6060780c0e4000c039051001820300d038020340785800040c105c40c4165030410078500040224096103004041c1c401005c280d10382014100010360340142c9580d81107510002040c40841d81072000c480e0031040041e030006242e10742000485941c421000900b140901c00000e00980d81e900051905114026076140c000c166298038041683c2e110741c11011780102814802514003484552901c560001d03601c0e0001082c18003001a4a440300d1050a1103d110390b00c040000d00307000c410701c1025480000ca1b40307402d1440c500000707028480e00b41119 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 630961501 1250 630960251 630960259
    0x90b03060319050f100f0609060506040b0711120d020f030901051c020d1401030c122a0305010f090c050613060f111009050c010207030c09150504020f03010515040b0405 74
    0x85050103001d000b541845071400b004c4d9178001c110300e40800c0241912500300a01c085c5000400070322410584601f50580710010501840d051511407090440d81000c01e044c0d5204214803040c41ca19550102200485070b2980007614001101c0c00d0003030700f85042031000580c582c00800ca2000d25a03844002c81c0c0b903402c51300e4409039071000303003800c0c0030004c0c02000000e503007141c54072061500c01c1c5d1041250328126032051411900941c0c550106500c080100c280c003c01412102e000c0e10321040c03000440040000307a410381e8071449a40c9444680c20364007042c205281c0103660b241818103005040c00d404024101c15910140790045c4840740030710301e544a00c11141001b24285221000522542501c0100d0345070300701701c84854881058003001010548811603040c03203035540d40c810550001c100c4404494001000c803000b5843c0c000e031035000d4509010031042400784048007048aa039144054412000c0f011841d0381c8942c107080c02d20a06600b0103a264817021030074002000120104000c0300c0035148240c0d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 630962751 1250 630961501 630961543
    0x1e01060c08090a060306030b071d01081305060a0614150706020702031912030b0f0f10020f060115110a050c060706060b0d0506030115030215030705040b040b0a090b030603 75
    0x401c0594680c040c000c5034980c410310202d80040c045a242d00004147e81c00b41000c101e050300d81c03070825116504a10300c03004c11010010888041076000c0c84506601040c86001c0c110305c084141d44003130401d83c00b10341c809072051b50741100348079603241103d0300c0050440c203441182c07100206508031a51b50056800c01020380381c0000c3d0050454400f400181105107590750b00584c0006585401100204241c4d41440024500140c14013a403828403a91030065801618140d030002040b070038411044c4490010009500c590b18076113003001010003045000346403403190350822503540341004190700010300c00e240e00d60744030382440c501107140450b0602019030100c0b01c0d20790b00e0b18180341240c0506200c2d80080080c0d4030100e81410352108030381200703210300341c128003c12600d844103d01c000400400d0102a400118042683e400303011030b040115003184807828004e060503550a51511564007542018000581c041120300410340c10003005405402282d600500394904640425643c035030491130750f501c0d44062 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 630964001 1250 630962751 630962753
    0x504060e030307030c03050a0605090604090c05030d0c17040f090c14120403021005150609040b0406061d1f0c03030b120703110901120228060c0201081e01060c 70
    0x55845004141560300949890f803420140241c01001c0000c4507102090030000003821658081c4140b400f81c9100a00f281000d4032080140402401c0b8000200d070030311240c01b004102d55804101004500c002959001540d1010b13182c085801c0d007550100751040391090100f803080880d00d0320620144c905020b80019000302c1001c003191005081000c005d284817002030702c011102c0d54542c585104034065001c461001042d008860700301e42c0d00320703401403185c903c80014030203518001c4000c1904900040c40440d008100c62300140132175440740d00c41c1011400003603082d495071020303221a00420070203d071070400c02440c41075110034850320450032030100001d03d1611820503001e58891408088050540c2d258605440d200caa90b40400703002c280c072031f5003603260701180620704003e900341a1808a0485040c008031a400e101d40c0c150302803900e5003401c4586540c42c0301a0a10401c0000a10040d951010203140782e00000d03058001c0a0103400c0c601551014415190307142c5101701e81161600e241110300c1c503440f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 630965251 1250 630964001 630964013
    0xe0c150904110c06182d010507082404060b030f04050d03020c0c0d0201051e0903071e0605071a04050c1f08041b030b0c1b0703050a02011407050105090a060e07180504 73
    0x41c440e101c81515141a040c00c482c5021b092801c40e0750107500002c000b00c2e20744500641d2550700448800900004001444007407004a66040f841030901901c0030420035201d03143ca40741c940080f1503100c0700044500401c8207029041008040c445814202145031004883c0b0060b2269002b00301d1034040d83c011700140c000c59108070300720755221642c2005d00e00c04502c1d460000086610084100e40700e4840c0ca6408504c220000100d800c8940042c04005403162901c0f03020fa07090780068100742e4000303028842c80c000216814540760720480c130480207031a46404000c200080d0240d0701c5070010010581244c0d481043740c01180c40d6410a030865040c0c0500d003940024825521750540008206038404000e0100c0c01608001425941404801c00c0b402c0100b00c80a155442800d880701a056a1009000c0b50265001e54180c050500403d5009441e001568595900f13484099900c042e003030f40300900c039105010451040c24048410078000d00445444c00d0703059203550a088540701c840310740c0c40300800c0410030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 630966501 1250 630965251 630965263
    0x606030705071a100b090612100302030a060c03060b070b060906210c1005130e0405190305090415060906050f12070801030308071e030e0c150904110c0618 68
    0x544520700d041c0854a640043c1c03070021050f40c020250203008000814034090030001d41e941d4480141082c3e00b4950900c0c0e5103140c890000c0d0400300c1140d5031600110150310103121420a00d401450046440c101001d001811a4034560001488010500c070204c00501008170040d08080d0484082880752034070030000710103064601d10a202400003081041c0f113014003140402c520320b800c841d80171221000b103409861521480340c000c2c810720104941031052140084007240c00c28081c1003121481c039030a040c20650f01250300b200768080786011800c248c144c94280100d80080c03c070703400300b0ba0340c007498036502520000150003144140f10b400704500c10061540c0064411100000c0e000345581e003405903024050240c20300098000800000c00140810b014a244c2040c02c46004030031107000f11885003c038001c0c113602c26052068040e844840b107255440c2aa030682480d12800d449954002c1841040102c40018000044840342400000540b142c00701b0a15401600c413484518285645844241000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 630967751 1250 630966501 630966503
    0x9050111041e170304030314040e0a05010503010e0106050f1302070f0309150801060804080f1306030b0f1c06110d06030609140a05071710020319051e060603070507 72
    0x840400c00241c0074502881000c00c80c9816100440801d03180d19200301e06520102c0d00e0f07815507004102c01c00000380314220480f5620000341c0401c0c1881d4031041e040c1820042921030301840c54031080140304070f19080c841c4941c000d0440000300191407400003c600e00240e1541128802e03103002409a070801c400360104c4540355400841800c0048841c1340c0a00b507100f850141e01140005101400481d070b01800c09541a900940c6404102c0e40d1540d036a180680c3c400002d80810113001c2c00304410360b4140030a620007a02031602d010501c00032810900248170f887d440d82d144a150100d03441c48035448656600c04ea4160850360124603a0306880910295105040d611100c2c91f1030700000000780b0007150f2140b0045449030054200000c0c000c02250703503850643d040507081e0740101e40100007000c610b20041280d035246400380c0f040c41148a29181c201d8008880e180380348038140b0040d186070741035441510b41c8a40f405601f00c0908480f5204420342007001803190b80200d0000002c581c03c1409802503400407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 630969001 1250 630967751 630967781
    0x30b0301180b070918050a0b0607050f0d17010b0304050a140c0108100e0f07030f18260a05071511070b06060301050105090f12070305060f0604050c0706090501 70
    0x1145001c1d0142600201119003070ba80d41c002c0070b002c00e202e280300d0340c0510b0448041c124000712520040d081c0760010400941a41403c5584546581858a8840140240c0303402074028103480e12884600505105903183c0300800c100101d01c9800d0310825048140c2d054030b6040184584a075540d2810a01d4654004009031010018452852200c84001648110400e0070380e01c080a03030701d405840e150a00c20354010202d001560900280022900f1150345601107050300d00807404102c0d5030000402c80349121089070075910f03040440b100784000c1e80340c0110200b400c80100e54900c8180503000303210307010340282c2c002085400200c0300240040500e0a41c0000c08822080100c4070b5091307001c0c1342c140d00c0307500c0881d01032040c200018118a080c0058034121641078403460300e85109242080980541902e0040e0701c600c071040101590141081030b000510301c10802070020b81030500100149100042c0100e02ca24200410403400c0f42c00941514a015844800424101c42c00d20303000340500304440c0c150440c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 630970251 1250 630969001 630969011
    0x9030d0e2103030a11160602070201030906050106050a1409010828060e091501060806010e030f01051302035d0904110403170f040810060e06090601080c0a030b0301 72
    0x1d00d00072000b18000e5a451404004800b00881840118064155641450481c0a0700500456942d4001f001045c4c0305140c0000d15000e6070742e0700b00458001b81c000400003000400d400a40c241c000126a1600c1c10750000641885101e40008242d400001c00b240c5800700c4102050910200305100001e00e01100081031200584a4001e1104480c0403100d0b07240314829810b401441c4035007180e4050694226aa442c500e9070b9072580150350306044d070002c05030184900000f203138401d02c0a1244c1c9000e0f80107504491520b585074010075191801000d01c51914213056002c1c9040320703011030081c2c3d424036540ca00e9500840001d02c00b002103412028071101489001074428552416108010600b208040f1030404c204803100c000f0107601e016600008044410300c8030645515204000a00541060582180e1a042d21106090b0406403228001c120464444a0038805000d1000c0c101703038800c006503044062403500c4030008080d510301a015204500000404400f2107210390404403007048054001c1c40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 630971501 1250 630970251 630970309
    0x50d050a0311030f160c09140601050906071b03060b09010e1302010507050f060a050901110d0b0307030c0603061410021902011e09080714061c0603020a092009030d0e 73
    0x654007590420032505c0c1c0034114004034142400d0f02ca550341d50140e004070815103276507460054909500c9010080e9000318103001d00800542d2051084d809101d5000c0500044c526504c0c00c1c0b0265050b80042034070407922900180540c040e40344c0390540c0920002c82da0458030815000580301807045100203419030168582010060400081060151a40c12000c0000d50740b958606400c07510588020300b01d028040002448002c0c0390b4100d409240d9000b0306032000155a0342d101c1c0440e802540c4803001203a00e410302000400e1b26030b0010201520140c0d95405d400352079034030094440030400e00c44208060110780b03800659216500c8244400b410507040341200303481d0040034056050358812004e030b170311400c0310101d4404040d0164141e0000301400742828082124030b203280b200d030403250300c1d00760903a942800400740e9590079070311006140d20381002842c6807150aa030340c1e505503110903607190030b00100f0120040340c9000036a54207681003450305001c541c03c0b510000b1004104a0010300b02d400d09156084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 630972751 1250 630971501 630971527
    0x708063709030206071806050702030102042105010b0f0d0803040c05040f0e061311060c010e12070b0f0c0d0c0c050d0302041502120a0302031302030f060907050d050a0311030f 77
    0x4664003d800321501903540d490308079441e03000d6148010350401100d904002d014000c030081c00041e8401800941410340b1030f50486a040f0507580c17100c802c5110500c04100b400000c1c800c01d8420765080d51402078050804002c15480495030200600080e0000000f0302409541c103440d80180800610600250442c1c00250010305280694000540030f60000b0403001c90302070036400c07900c80e0301041c06941221403404100a41d089824410540d540b2040500c408420610038a09801d03840340305a0703280c001904002010450040c040709002c00c041090040381411030b01071303401100c0d0300840031039013100741041118840385a01004096200340e41c120120590540c01400c142d0f04110030310410060743d140102d98401078103400d407101041c20404441b11074403030307001194490610008282c2841c02603010900c0e0112407200008190002c0e0140310503403406000c402e0080c1f5003103a00080c00d115a0301c5203622030307012407001801d200791007802080440b030500503075803014440c036103244c0c540d82c10300811 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 630974001 1250 630972751 630972761
    0x7052a120301060318021837060e1311040e010203151512070804020a031202010c08060303040803090d020f1201020d0c052110050d11030601060207080637 68
    0x20703c042401e0401000741d00c019944c01c4844560000c02040c00138404001c69000c2c0d0700e01910104e80e040c1d5003503245002400c0300d0071040c5001c060402da0283c10143c400301d1811034078240c0258490201c44424071000d025040b4000981c02e401860714142d280446001030010b007a440c524204550022081240c020501c0b121846c601030152240929010b980800d14003a00c81c100c1140c1030b2008030404180c80c00d02c03e58829a00c50301c00351014800b103480303841d4014000c8140c0e2040c0c00503911090701070030040c1c0c0040d20a80049050b8019401c0604000041d51a40910006e0501a07804861900159518034410403c1d8002c09040142113090f4a2038840c043c0d0312a28516018508024055038a94412411615180880c0c0c85406d01d41d00c0481c100c4000b154041d00d40701e03c140003030341d0109081c0d03207003072302d46410798421200301a2206400c0141828070390142c1c004400e5400152081003400c00c0070905a5100d192a600c1992032100d50502c0310340720403000740800d00c0108481e0078090341c00003a40700d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 630975251 1250 630974001 630974009
    0x2130f09060602060903070807061409030304021827030d060611010b0d200d081b0c06030c0a2001091203150503030a050c0a1a0103170307052a120301 66
    0x400c1c404030782c49940a03a6506015195094158010450000030038100c1020748449445410f002c00c00084400340f0701c03140300f4203031902050703a08000b041c8030031813503e0990100f0b6401400d03001031840c0303441e540f06951250102503258440c007002c090a0040c12041c02199246001000200700e90754503070380c00410082d410383c00b2040540c40d01351518490320307000b41d4400226a11090071032012292060301603008803188a0150005550300b280d0001407081400351003a101d41100c040384055030007101e589000014000b541c0100010014001c408845800303c40d1006210305100031880c0703010500820000081d0a4100d0303035403030914420200550104140d11981003a80c040c03140c0390400400d403540001500c2256810361080160007001d602420180103851040130948448441c181c03218074082c880d42064542200020006204002070061244032403550448124194a05080042c100c0e204080c0c000486001d01785480e00d8050f2211581e00c0c0604504080c2c50400140541d0685150000c2c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 630976501 1250 630975251 630975269
    0x40207080409110712020312041e0b07081603051303180b16150c020d0807022104050a0605070804031b03050a050f010c0e030c09041a0c0304050c0a1508070302130f 72
    0x8020016148004107480e9483d601e030041143c99240c5a44192000c01410f02110b014503001c92b0503408911842009845030283e5102c0189518100d1000d090414040c40318805152820f801e1105011109240000080c0d141c01c2c41c030104a00d44840f0341c51140a03074003001090000107401640d01d03410240068115110303c41c5c042540380151116415225142d01010050b44401464190988124281070f0841540d00595260110b0b44036000481003220700c1002c448034000400b080503042c0b41951400606407490454100411036a406000e44220f01c4090110ba40320200010400e08440668008561180448480010034a04651108948903507481c0551034003000b079031014000c40d00b01e03a0b140c1005015140c0642481c00f00440341201070300568021040059501c00384901044060144200089607030b00e901e01450410f1820f000e203280c2c42d0007100454410040b1040740e09044040c0281800c0182595542d80d208500a008441d00240c0d5060303200000140c42001031856400c2c0c9823560 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 630977751 1250 630976501 630976523
    0x706050a060305030c161202180408090312040f0b03100e06030c040c0215010e060120014d0d02180619020f070f06081f0311011d010e0402070804091107 67
    0x41f0000c290440c2c51806508205a1000c13030a8091660b04a01d9225108880b201d04010b42e00d0042843c0001c514808009243d0000c0d05000045917001c1c404000c0c2074400e0054910310780b26082d5140c1c084240b0900c10341c600403c01181442d40d003070040340740079900030348104050b100541c3c0c000e5850107441300310982e00051000104808502a4003240304103410786030403401c00b84401d442d4012240ca034490210315582c8904040e1419144040c5100800150714803200842c025259400c2e0300a094900b4104205030a12850380300d00100191140b10340e10715001a1074410080d421081c5129502d840d40c2d100d1340020b2616109c041090801501c10840e80c00c40da071010100340859030301c0d00705000e00a0180c416100c00c0002d07e200d80179450703000408121518a00c1850108070041c0c900c80d800031540918a8212082eaa50b44484403d401c441e82810010042c10384100280c083c2020043d560b0003990001402c0c01131043c1d050898000302040da9042100c1018041000441c0e000f654040703840000503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 630979001 1250 630977751 630977759
    0x30c2d1a0d18031e030b01022508030406170a0207020f010e030102070c0902040f06140d090305071a0115021504060506040e0f01090203010c1d0f04060e090a020f0102030f0706050a060305030c16 85
    0x3d100301b102e0040180c000706401c1d00804201860102032410394035500f184c0c210007007171084003070002d0002040b1503207810701c2d58109400280300711100180158a098414090300c1c002d40d40e071112a01c925102800c0419000160901003400b9110320707080508115000500054140320990081c01200e80f0b80c180b06c500d00391618002c40d00e034120b241d10104004814000c105580a0680c04503003000d03c40d080441ca840003540d201e40c403e95a0600185076603000b02c0c01041002e461205021040b115403000d8046007045500040000e0005000a00415038070000110651260b80c4041440302014007202c6801060381c02a50207040c141000324025400e0a082515042c002c0b0703400104d038403d5010b041640f0318000180107081d00e180c1c2e100c40d401a1241c40c0018088030301c000070fa005483c100043c11b007101150062107890001001d440d0f04650003048480c00c400030700d40c1610a001c2d441030010880d0303144c901c1600043c1869030000380107800f0000303000044040c00102c1a0134400400b01203a14240e079 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 630980251 1250 630979001 630979007
    0xf030e0307030f02150712022104030f030e040f0204091a090402150703020a02131505010914011101090c180e07060c120306030c2d1a0d18031e 63
    0x1244002082154180c03680030061a0804810480c0200701080f40c3c00c0c10099140c1244e05101110b5100142c0c0140f800109c084100e50070026034003000d5003d4a2078030b45503036113040c441080c40780050700700110340b600c0f69002c1d5a00e40101c43c104c0580f010554855071180c0306507009205040d0b04214604071000040303080d0500d03a503c940701d5600201404030740005104080d6290380310394070480031801901c0d01040140c3d900d05540c441e0342200400020324020088040e8060b81c401d4101505004a40b402089804500c8035423840e5040d0a281c004080c00003421031502500100e03070010300750320f0509000f01d040d5000600c2c00701012861541806030620b8400b116495125602a0400040944010102090300c10800d0016125280b4000810503a2602c4899412507150010701c055114001115240424011000707c510b59401c0e40c02ea1151810340c1c0c00040c0c55448003000c190b03090115940c184c80c1c10650008409840b02c1c42d00031310920f4a480c0007012454800401205105c2c2c20700c41c9150948 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 630981501 1250 630980251 630980263
    0x306010609060804030212040f14090402030c0f0f04060e2202030c090c090405070509030f030c1b0105070b0c03070311090915040b03190204050f040c1208160f030e03 73
    0x905622030070041420001c08652035003009100b40c041d8890402240d891145950003400103084520503401a10b040580702d800c203060541d80103104080c51f0040c4800750740c002c01c0403030001400301c034180071903000d15001c038140c01c44030b0100c1540b10f03181190000c0c02c504101400d5100344420203580f00c003500c124509a0010381208400f9400d0ba02030750000c0d20600349100c2d25a040306030400d90742c0c10000090006800e5400848090001a1011030603000d18102000443c2a090381b400266080c06910703407240740d90b00c3d110090520001054403030349080341d00480c1121281d58002c2044802807410700e400d0f1030b00c0e40c810390351207000a141c034416003041581d0741c0c1640e4180e2002480b17481380303031207140c4501c6001c50121002588559035440312001d03950300700300721002d11800705a002811100c0340108421980000d00650b000c001c0354041100060350010701d07400f500c2d0303280019440740c580350814510501800608000010a04031140c0030f00c05100c0c644d4860038841d0381c403030620210324001d141e140c1b4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 630982751 1250 630981501 630981509
    0x6090f09030d0b06040305030a030608190809040507030b06030411030d1e0c05070b0c01060302180c16050330010b04050d0618020d1410020702090f060f090a0c03050105030601 77
    0x1400500004080c02c0e01900004001c0f44020240c60820b034580d21500d040d64010155100460f9480c8410480f612084c0820103085403015020900194145c0741c514143c0308914030305125560300d40016103143d029038000544000701074500c42e1a4600391400c2191015403800040c428800e050a46407150300c02c10b4800805103012500d41c0380c0700d121000503540203203543d03006c407240e004080c00031407002d12000c0900304081100f030011410341c0c17541c01440f000c410b100300c0c8450000c20760005c0111a0b103071807049583c1100f80040440310350a150500c5400d40c003805035005000c261021080210900d942ca055030104030100c814412070366101755140c1d40c2d04c40d510a541d0000040310354100810026808403901c04017401070a18103015903170000300d0148200408849580713035070400b10303403e4004116802002c00500411480c150f00340d0002000c0540007812039211107a00350000e101a15007a40d81102035402611591503070400189940280611580e048000303803424000082c0c0c0c0c03400282d40d41c122 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 630984001 1250 630982751 630982753
    0xa03050403030c050c100e01030b030a0506040209042f01031d1b0402040e011203020d111f0f0606030203060f1509063105151806030604061d06090f09 66
    0x840e107107035000e0303400d0815a44299000d0040c82c4040c081d684034040c2d0b61214009a42d0b0340c10800011000141c202c0301112141390096102c4041c0c40c00288c00025010313081a011500360846507181e107810110039091500e00b00c0c0d42c00132842c01483d070032031006e00c00d003060409032010f001004054004124950000d50124040c0d0300001c6145181e03030b02d840000c0002600500051f20f0319460b100707842c59802c0f0a1707000d07108814031050b41809266043c4410400c00d0302d1850100365140340c4c18191951000170650070b40184902d26800540070816901445000d0394014cc20b10400c0c0d41d952011b0001d40040380c40c980182514029013019280028070800303c0340c0300c02020750400b0301031014030038a03800601c50941c0103e0f15024199000d103240746000e12040c6211100240d145c1840203000d5030420034881001c2986040c85462028407034058524540e2134190342440e266030350300c40090058502503001c00b000301c00c4413001032031403a504d4214a225078404d840c6034626458414008010007001c58400c526 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 630985251 1250 630984001 630984007
    0x9090f060501091407140c01021603090e1023030d030504061109010207030b0c04031b0303030c050901050922090819090513020a021216140606010f0305061903080403050f0a0305 78
    0x8442e00844507000c00c01821b540c2c441c1040a452202da00320390040d4885441d0401d1007124601301981301503020007500305151a05940e061072a061075030201240140100741c05041501d2003064411124404000001400c5680c180ea4000c8068000c110680e0700303480680c100048003500d41c4100d0100c4a1103501a402450454556111101000406815036502c4441040000b01140b425a841d0a0710307601b0755000d25102e440d605d0040d0450300076074810001e021051222a0349680c00105079282a40b095400c90741d902147c61406024030b002c80c002842081c41c0a0411061041c0f500c0a04100311901c10052100d0f01c0076a0142c640700090f00c00c440e4000c8c42c0b01c1d00c1041d07000c50758014226480b6030f40100c43e0411000100d16010f600800201c0e100c0c081417800351003d0005c40e011082503103410304003610b118100f42000824070300c44c0070f4104041c0f6407103c2c0403030305985420b80b00b10303d0f11614421200c2803640720b10f0810101e81c021310080d9a030f4071920684450380d14011615481c1c407071b415264546 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 630986501 1250 630985251 630985261
    0xa021017090d090b090a051005030a0e0c09060d2a0618052103041a0c0d0825020c03030c0d0f080112060b030c040c030c090b130e06060409090f0605010914 68
    0x1180d0f0380261610fa410035400c040007e40307622050402d0700c185000c0e458603900ca1130204e1031101190000c1e4004050744d8010554a400c54880c0d11000c0c0e04001d081d03422500040050070070307a081c00107040003000356007200d821358005401c422881741c05444013a501c42c102000155801c8581c0c105e14000d00754460050302c00c0291a130711481d00301c4030121582c8142ca04040c0c0e074100c28081f00c006052418040140001ca551000d081448a80302c01001da0900030094244413070b440785001c0c0491309150400c2e40440c44050504c2c000c014680b00c03407000604599940848100f003030384904d240342514011a0342ca540d5440128025900c40341a264040e0505800c5803450301c559000d0402001d4858050040100d03004854456000c1c0900b0446241c40c00304000900d01401064046590b0203056101c40a00c80c0080c80c0d400070090300101e840000514040f5105c04c80020028401c50303000c00381a518040300340040005070b001d883d08550150400304066a40c1d03001d4201a954280e0402d800c400c030b0400055 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 630987751 1250 630986501 630986519
    0x1e0106030b0a200c070501030609020313021c060612021801060c02060702040906020d0e0f1b0906180a0905060a0504030203070209073b0d050703060e0a021017090d09 73
    0x1100100640030b510040741e0158030f02d480150301c10300c03c0c122035410800061080c0c0d42c15005403c02007010b840708501d0351a10b402810b141949020000f44a0b600d04409803c84a41c02e54451344400c0e0803400c1009400d81c0c1d05040e00016003e0700c03089000e581c200f052020240d0003a20014102c6140762104c1a4101c129800c0010b290b00c100c0040303034480e82c0e81082501041083c400740c43d044982130000940100c2e05044e41c0c0c5403000c071000c441c1d01c82d400004001d401111081480d50501d009442031400341e2903900c00034100329654003c10707882140c14820014104140d80040b0700250041003522a9070b200d03c0c5200302690f804440140c0903a01c01c00180c4018109505621350000e06032402002c0321900000350f40030700380303d640c601b10686508040500c05a401300010369801600311100d5444071500c0c2d42d01138941c10a0b10002c0e107040d5136040e02101d569802d200d01140b080d40100054143c0c2e4000302d001c0c01094805504011140200b4006514a000082d101c1c410b940591a98400249090780070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 630989001 1250 630987751 630987761
    0x60d1209090e0606130e07031b050303071a06100f051b0619110702011e021903050a08060f031e010612060b090c070c05130216051e0106030b0a 63
    0x151041000060000514040d070b4070644040b10102d40207803140b41412000c122091102e80b03c54200140f0b0304400e40d054600c00607040b0116680f01c02001c1402c1c41000358065401816845a03406000004101c0200f01d040310340702800c0071403040080c61503114403040c440061601b19a000200740c10600d84c00e80c1c80c0c0994060038501c8969030041c50103070510b00501d800c0180c16503403442100840204091a80a64010350b60340301200d05019081c40b8143d000203080c0003016001400742e0034503810030001180b0a12100d418030750f24442d044040b103058600140f50b607100d03900d100d0004004401140d0700307280c02180c112007044020020f2810710580c8121082d04107400001c1d414546d40c41400041c90210300d00207100c401e01035880000c1c8000c0d28000d00ca40703030100414a00c02c4003410032050000552282c500340a41e03030301303441c600580b00d40c1150000c028411365003090b00006ca4214094104200040c1c0650b01c206188078100c140c0804000aa00707032841800010000c0f1407000004410720126408 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 630990251 1250 630989001 630989033
    0x70209040203010f09080c0d0e2b050303510d150606090b041d040c090203040f03261302011403040b240f010f03020405060c060f0601030203060d 64
    0x502c107134030600410100d039034100046a00807008140e0780f0044800740910701482d821400e0101d0001c951b000001c46401c004401408528900e242100b95090742114080c1c0456000c800c0302d4be1b0b41403030004030b8000c1d02c810007032a084803203000e007462401340000040307084015140c0102c09205003aa05c00400c00c80442101d030b8011100b0204ac0c1d0120b02c61000c2000242d042c0200061124200500108258000d03003000000c0d0500700010006542c3c1c6611a000c1a4016480f406194680b4a07000075136035107603441106105d0020040c4030034040d142000ca00c020307100342c50704903500030003d880c02210800082da070100f400781180021144945c15204480051051410f00c81900c031204105140e130f00162401c1d2506210041000140c4030401c0030070241c800303850704140980660302c0008900c42030100c202c60405c03007200d2901c4603860094041e100680720080030355489000c849500c2c0c1d6104070031605140c00c41034070808542994024803c680c0a02d90242005e154640551501c80b520b0520b409 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 630991501 1250 630990251 630990253
    0x9071101110414041503020607151b11070602010501062304080f060412230c100c033908090a1a090f0721080c0a03030926070209040203 60
    0x300d44100c2401c0e6038001c0020348001120040140501c0c8144070489460f04950411500008414030140c4c0e148020380c0c000c60360000c00003144e0b03804918100058411514685004c4181600402c40f071030f00042440f43d603080440c12070b50004c2e0390f0f400c00c03800c0e12400e12509011441040e04541c0c1580801502c00c0401c02c0c21103c107140503520001c1c5843c0000c820060807041d0031034801e01c0100600d400b50003800880d9841d04401c40f60300d064820800d4014040c0707c0c250782c1000103a0a400081c00e1044a0113400240c00030410030040480180203030001034120a00040e41d10405060b800880c103124102182d0000d1040801c00400426109000050400309152091640f10750004503000190319100031a844901035505141a64a1404503440c1ca000c019800c07000050000854482640000e126503008020b900410350515620740d00c945190709895010300c8540740145505500304528140c0b043c003500b0700842250b5605c01c03402c44054014620504100810000361512862064010740024 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 630992751 1250 630991501 630991511
    0x8070825050906030a1d030906030a0c020a1406090106080601031205090d0c090603140102270f0a1739010e04020a08060f010302090a0513020f0a0c1106070209071101 73
    0xc001941c81c2d003003110801029621018058554516442c1c25021b400010000b5070400801d0000140280001800d9004807951104030f61120340c820408403c1ca04c0c0c111002e10b1200c5000c44250ba10382c1c02c1202d60031490360a203840010400030028483e0f0403641c12a503c14182c100142c03040f80d590340b0030f03091a0ba01560b42c002003004110784005180040041d01d0000030707a1403451030200e44440819584c6c0780d860748103003d07014500002185c403140840f03a82140710440307020f10300080d55450907449229044040107101189500901000300c55094002003101c801034441c0c0c4200100ca04a941d00309101d58a00d8821140c4a1070030f0407803401e101050400545021490b40820b00f00c1e0009421500040c8884c6d090124130300f420225800c1101003841c09610380400754000c1403861860780b1076a406001110324080c072091403035059980a01340001030301d9654081d040020012500b0480036101d00025441c07142c8071303141107400c50b65204c0d070181c516402d6a54094050b181c403d004206c11207203540791 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 630994001 1250 630992751 630992767
    0x1415280909032c15030c070209061507060501170c1503070e0409080304020a171203041a040507030c0e04170a030b040e0a0b0c031b0f07021f0807082505 67
    0x190b1544803912000380001c500c8903154001300241c001400b60b21072003540e01082400181c4403694111502c5c0354056071183d059865140c0480e400000c9590002c1f500440810b62a00304890b0f508014100c80260754001c940c5100400b03617a84502e004102c06a11424101d010f0b50801081d1001d107501c0059401d0800042c000f800c0132030b00b521204041101d50890001c1000110b03c0d1001109010b455082c0301c5d80b609244038000c0d15a83d8070b01010107a030103803001c800203040003020348081301d02c0707003488a940741d490409140580d901d44a07030108a4020905200102c0c80c010074441d018420394020b482d0b20900e060500340030540c0d40c41030222004240e251100b40b041922280228003507040020000e109103142d60411406402003d401e92240318020403e000c0403898810322070a810140e40b507100daa0310b8881890110314400c2c000003e422600b1014201c90382c1030000040c0c01621110345411115036106070b021902c4240031034000800d290b41488a421449130f41c0389009a010203230911501d001c0070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 630995251 1250 630994001 630994037
    0x5090109060806100305120d0b0a080705031203060609010305090a020415080d03020f0301030605101203031a2d3c060f090112141528090903 62
    0x2604091036007501c4440400000e0380801c01d030303540038910036009040c0d0b50440e5940c03038942d4801d40c514100e00c0404103040310301c03030070f42c0c0d1062540382c40041c040f800c5640e036240b00e10744906070f9100c1d0900c68042c025010740618030500032a17101c4c000081c00c103840c15000074015030080c4000340a01d9041c0c030a1903040b0780141c03110303c508001d41c0d1070300c0c0c65070380070910780007100d0300e0000201c80f404105401130145503004184035050300d0550354010004643c1c1c0c2d41d502c05105514100b5880300c40d60b012007004010034560140e003e0801c00f250401c3c1c100c82c0c8151082840b140b4003c0c149940840340c4210801044281d02014110013410020607030b0713420f482841d144c1c441c030b82520026030301d030320f810320300c05a000207200c242085405078207079410f40c00e1426940122845000d0b5080c0141800b202882d200d803401d800b03902c0980c0805040c04980c515040c0b10018a529114a00d4a10302407402e5402e1044000d1801c10040301e41d504418601c0c241d18186139001c0c0240042c144114207112028800802c1088 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 630996501 1250 630995251 630995269
    0x512180118020a0515030a02220603020406020c0d0f02040f020d020c1f060b030f040317040602180a210807050a0b07020106060e0a060c0309050325091a130605 70
    0x984036584101d802410300400c044090503500140c0301d002c140b41411403a00002c41640e62040e00520b0041e11b030490045441071030504046042c205800444002c1403071501035020f031090f114075500312900c000342d107400c0c400b04212a02c0301420000f2402c1c4040018a469088004141120700015062094070f031065010b80c0c001441c004880d070032280c1000811848149210000d00c44010f0a01c10a85840700d065400c1c44041d143c00440700708600082d05150003080d02848104822841c032030703035180a0404000035085003c40c1c0300380c5150b4480442c0703c0d14040840c02d01780c51030907201c0c1d0310300104851a00c8500202c03400c00c50358650f0511000f40441d205000c003200f05401000f0b14045894214002400c48009800c45401e01ca8511719480c1161030340b503136000c280c80c490b00b00074244d4030f4107040c10307200c2605a910003a414400c2061604120081c04044011040e226248480d01030321000200d003034820401c440c80e00c80c001d10f545110706240c401c181d000360014000c00090000e48480116140381c0c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 630997751 1250 630996501 630996521
    0xf0809030106030c2319230a240c050325120f1e020d21050c0901030f110f0318120a170702060c0a020f010204150e0604030305121801 59
    0x100342104414869004915000345210085807040e445104210004181460380e0240121040150303c0e0701100ca15a06907d00c80600014034841345242c1d15100c07206007001c000a0a080400c0068082c52180e0103001041640c0c0d510001440c02c04140c241072005201d5100c03668450f9051002525022a40600c601c0782201ea456403054481001c150000e44030320802c511220340d002c02003040100080d40172400c80300102892501e032104c1404603194402d02d02c01100c0045806184c40e00f1b0120f01340e4084001c1075114400c0c1c0302440860601140c0c0011a408001250060300c2d0402081c501c44040c5001503a020080002200a02d11000c034043c0c0707001c000d81d50b21042c0d601c0024103184806e8000c4204049546215803482562400140082d04c410000e402c81400d14400b04882c030301d81e8003c0c84480010031400000315200d0ba81c80d1018a041848a29094003080e45500c0341701181c00c0000c12101581c1d0180c84040c41e004105005014164000f001130380759401302e000400110000b070050740e1041c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 630999001 1250 630997751 630997769
    0x11250b040e0f0c16060236030d09031a070c140d08060f2d030a030903150219050c0715120b010905030a020d050a0f080403031b0f0809030106030c 64
    0xc0c0340004650311404000b8041543c8280f081c00901d101e41070118045040c0340d0310003000750311840c4104440c011114400000d03d400904040040300400c0035000e2824440ca04800b118030181c0c8030103081c1c407684d545002c09820400d141801c0750002035900c1c400c0c0d0b0080468602242804083e03242e40050030b41d80c0c046581e031901703c558800e140c25405088240c1258003160b0342c4007102440310000c0c2410290003a4104d40c21803120240d41d900c0304821030100b400c1800340c00e4490900b490719006002c0041e50100300c0707440001d40300c03d21143d1884d1081d030303c01800c1f00010301103015021a040d100c90300320710044a41485040b0010402640402110380c000e01c0581310304100240482007581520301116191b410007548030010020b654000803948155501610150300c2c403001400d01304d05140a284c0d001c0d03c0007822200765020014500c0c010800c80e40290b688070303d4400c12a01a00300300c21038002c00340100d6070b40b11184001c01c128100402c11458000c00008589559907143d00039051164020a80c6e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 631000251 1250 630999001 630999029
    0x322080d09081b0102040b0a030b0f03030c030405040f1a131e06171203071803080c0d0206011202060415020f01110d2016020114030f060f0111250b04 66
    0xf6410703021180c01c0e982681030000d5041a050400f80b8100e0b0085100b1401010f0b183d5000305240d03152802c01c5000c90b040502543d03a1229107600c42544e0780d0051040c0c03409103192800d03020081c2c46030700c10110445151110030201141100c10043c0c4240651442c1182c5560354035001e00c0140c00c082d24140890020343d010031081d14060413000c100f080200c403001d5a0300514a0b2010861041040b00d03031060b1a03003031149600c07003508241c800203c142e030802840e13100c001807440e42c110310000e0ad03400c600202e0350031103100360f07200d4206d95080401a40c0083d005031060205207d000342040498811450f02d1044940d910340302c400241c02c1d90000060b0341c0c2c0b00200029a402550701e04d000715407a4290f091520900150600354880003440380c1006030368100d80a02d0715800710780c483d8401c1a80c031403a41e0185500c030304108124640803601a6500c9129008107000041154082c51003503000a110714050b10410b881101c1c800701d034803081034009003100185440403a110700c0303940107080542113030301c064030b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 631001501 1250 631000251 631000267
    0x1031b080603120a200102070b0c2b09230c04090812070e2b0f081603090e01061d010f03110708030a0c020a240915050a110322080d0908 60
    0x1941172000300c840e0500343d00400c0041d0202d0000e1140a4010505805c12542c03110511086841a28002400042c101c0e02d80e0155913009541d82080c604107018010740d0210320983d0b84013818181d20760300061100c1c0c00010586501e480d095000540982c0078011013841d04586031659036100a044642c84080740381c506040d0101c0c03c022841c542405100707403442d100d40380e0024180b101549200c00040641404804040402c0070440c1562001c0c0900d4002403c0034210b4900030b45000b525018407500c010b429000013400c40d02c11400701140c0200e444035114580e9940340112101803007000c0301811706031611164682000c04c0b100410700680200040f03510f07070900d08041000d851800c4205411940410407030004280a030803240d200d15103203581c6404030f5400313040c0040076040304078018160545242c90215150641e80003903110f22061a010469103030415140103841c041900c0003080c80c002000c000c40101e004404006000740501070441c2403814030981e0b2030517581c0d01310044548600104a403c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 631002751 1250 631001501 631001537
    0x110703121e0f0e040c170c0409021611190b0304020411030c0705151027020d02040303180b0301050d03140c0d0807050301060215061f08090c01031b080603120a 70
    0xc9042e0f01142c081c0184115481c000300754031040d40002580c0c03880d00c0b0104100030344c02011030b801805800000e546070b004020380294401100300d000d403080075009031920560300c3c11410b02c3c0d01f84050f040500700164141171801801e07400040c0b007242c0280c0c1d1201410030b50031550b00507621407405220b00c25035555440c03900b1400c100501c0c01000e9888119418043d10701104510300341034450070702c0c48060064810340c1d40850203070800407004d105440000c4100420090390010000d490094888454050300d41560b1a901078339840b4070101c00000f40014450362401603100c2e01558060f1811f82079a065103803014125500c0299071100c19405001c1000c40030340c00002a6a0204080c140b06003151714044020b9160714072444001404415000000e0041e62043c00205805481100d1708610041c412405092010280e074809403034440e110382000d40d0740c42400f408140c1c101181180c0d00008094500355030380321014044690600840d04c056100443c3c0101420745880943d0301c424201c0210f5141c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 631004001 1250 631002751 631002767
    0x105150103061e05010c030215070c0c060806010c1407030209010b07020406050a030f0f0c0b0d060611070311040e1f05040c060c05061602070503010606091401110703121e0f 76
    0x1090b0010880b20345900c0e00000149210204c800a0a04a00c1c03210549000c81c01c0c00d0500d00c14640380d680c09014040c8050f40316a040c101e6a00c00c14428107000e0703c4100c1680c0380b0004864207130001f03904243e09000611107000c00d88805038108102e071155a203c2e40001d8000d8001d800001c21600302091440a51a10303018020013031006039910380701d550458480301204009504060091030f9072904001c20000c0307450601000381410107132540c81b40011400d81d00500b00c1481088009030200483d04009180814400e003103139032040c3d0544c10960400f00f0b1002906a88940305454015010170314030348a034041c420b0006002114000690341381926000906507d02c2d000042013080713070101e070b000081000841d0741d00002100e010801c907180c14241203151500315040300f50035500f00000050314540040c0f201c1c043e1126084110003014801d401116494820440c01c29103501854080005c9210001c000032207035094504409060010000c0308520492030001d03100061024003a11541c0d40e001601e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 631005251 1250 631004001 631004009
    0x50415021011070c06030905030d0e01020a02010f0b0303040e0c12100f090504030e12010603060e01060806011d070807050c120a0224070518030714090a0207150209040e010515010306 80
    0x22036043c07808075102d42030115000d0181c00141a9100305000500c1810400d0b5004d0000e442c4040c4520030050783c0c2c05002c0d4001226070400366081414a41940c0524000d1000100c000f038001c60605140c032a412780d0a450290001118160812602a140301c0d001c03d13652250001e1905ca0807001d10700354184841100550254043d10b00c3c0c101800000381d40824038841f4180116184513101d641c1060841c01040ac03503100601c150b24100c000480c548042d0081c03400c0b90f505405490b041e82c3c3e540c59910710706801e243c00d0f0184a012400040d140390007100e001e42c1000503071a00303900f400d510408080c58010b40e01c80fa201810004681130302059410891038402805040b80c500350f0300311800c101442581d0240040c01408804034000303121100c140ba500e01e9401f00141110084d550390f9150300015400e0000840c00f50000e034000400d03501a81c022102d40300ea00000c0445c0c20101011120300940240c0c903c82c0c2e0080e100e0501502a103000d02130240280c4210686c240d40b0541c04001500700e699541c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 631006501 1250 631005251 631005281
    0x1050f0702153004060e1906150801110d0903110a0606030b0106030e1b011b08120601081e07120c030605040f090f020904060b190501020610081b010504150210 70
    0x250400003c09003885540c01940c00300001c03c0001445241500f00a034188200d1074402c9504841802c0c441d545d0890310480d03211803480d400194856242900f40e03200250b4642c1030a10410250440785001d0f800540d10074000c0c1b50170511a40e0300050030382400054903060341e20907140e100510510680d130146070300410060a0400107902d15450250f12040601d48494008004147e0003a459002d403c40c030892002000ca01d064000052800b415075420038080d4000c03071030520000981c84c0d40030300d46403401408540e04640840b001c40d030410390003c030001e01202c2040000021100d51240c903028044030071419882c04141a82860706000440301984c62a42c0c415080041c0000418040d2000540341601520100415a500e06002024001d0050415001800803003114084a10303c0071400659070260700b41d60b02610b8980b040b01c030b080402d00402074a50000011881c46038900306200c1842901810654142503491828100d07080c07100402c4005a00405640d1005101d20721541d001c0700030b004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 631007751 1250 631006501 631006567
    0x90f030c0102070303060e2e080a03021006120209010b07080d1e0b0102071d06060403170d05010f03080414031510032307150c0b07031d070e0601050f070215 69
    0x100c0d258100c1c084c40c5102081c04962548c100000040b4880c032840a0060101210300f015503e19009580c1d400075102029150700c0c01c6c8011540040c0465a0000e01d40c009007044502d9003041156092a0300810080b208424104403100d0088568010030b81c030900030609058488030581c2d0440260388504101c03d04541002000344485031181074100085030010f070000207075545000110301188101d400141c51422600c00200c0085200c0c001440001e0545406001b80d90341d03400040c01d681401d01000340a0003041c0b0003031040c0960040842d0114100900b00e03100b03030601e650200d500201c190b64210b1410a002010302c1400707207c2c1e0b440d100c7d20003817203c1440c0036500c003049907456590a004940001c510080c054440921402c0403480c0560426482d01681c00c00700e401400411a0904080c00070032181079542d2803400100d0303c072080728070320070080c10305e540e442c0011150382d485510620151102441007001607200e03090081841c0002c80d400f1075171000c45116046607508201c02408941c80301e5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 631009001 1250 631007751 631007761
    0x30204140103091203020a09030c0308040303170114040f090f050c0102012910021c0206061309171308060f04051c0c0b060607080c0c1e01080f090f030c0102070303060e 74
    0x140508013500f404626005850380940c10040750354080c50ba1002e029828510350110600090100900849103c0d4a84044401042d000f088404209100c1c0c1005800310900034005800d250b040080d142015640000c1d001d0b00c20354501d0450b13283c084040d030301a0b20400d8120459602440340001d0003010b40d03042600c0d412414200608140742d4a4150700034900c00142c44a0700e0b0080044400c0700b0b00801d4090015100c21100a589042c1102e1075072090042e9a40340f00540c1d00341c412124503035008101c2004002450040b66266171050b1146008040020030001d82180c091060600030b0301c81149541e51810300c3d090852602c00030810408a082c076a003058a0584c0d001080f2400042e4019a4950181d41d840c0014280e8001e0b079030041c000301c600146044818034082602201c0400440e481503403026502101c000b100070040c00d590100d64110007040f1280c40c2c4800056215003803c0813980c0341428a03000d00c2c2960011050904243e4020403a8020580c1500444000c0e06c200c84480c5c00500d02 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 631010251 1250 631009001 631009013
    0x80f0906160342050d06020a03090212010c02011104180506060c1603110909060f0c0706020a08093f0f070f0b0105100c080703020a020a081f020a08240a0603020414010309 75
    0x103541c170300030720690307002460404040c081d270401245a42c000341403007003003c0b1001c1c400780640740c0415000b005501e84400b0300f03e1604c409003903c06032070351465510b0548000445020003400081c040c180d0081c805c1c03100f80700d0340b1010401c110b202c07065a24580022032842c64800d0209181d0701c480e6104d00d907084100300c120080010401d502048007850340506865a605402c6a8495180301410050002810b50301c025004a0075501629155045490b40c0140035a0100d090180c0c2503481d00c85000d41c25408800d404030040c02d00c1010541002e00d04c0c00000510b202b26981c8403100c100c0e40740c0401d41080c0f0a1046490100340100030a03940801d80b03c0d075040008005101d00c22000700344500100f00c001c1850720810645007807560141c42c1241c0a602d803002207603200310800e402601c0705c1401e030003500002c2c03050003a14603411007601c48041d603888a2002d249541d1000b0a5607000000c1ca184001c056900c4032803010040940d52001692542418900486201c00f05484c40c141400e018803000080c1e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 631011501 1250 631010251 631010269
    0x718110c030708180a2729060d020d2004140d14012f04080a1e0b0a0506010e0d0b061909020d020307080f090616034205 53
    0x1610200c1a5510028240c501440c5904c010700f503a040360342e28001003500c480f261504a0303100c6941e2409414425002c040800b901c034103076003160203000078103001043c50841030400b45a40300000e090b581400c1205402804903001203041e114016207038010000c00c1501d40103010782800b00c1618940c60182088003d541c030310b504800a9001d80d100c0c0c0280018000f603185020000e0305020000e018224904443c81c120100c080e5000103000c40181c007180d401c110100441c0c080709c04100103009000c4c0140c5410300e40300e0840c1d20b0750300b107080c0e4003502038006101d00b114648140054000080c880c10300d080010728020784414100d009040043c000000f1602c405003c6130f014100700c90018101c11021440011007003d0b034844000e06001040c104100e65081c3c02840c41000c80b80e039101200d98490000240b42030040c2c900300c401d60402ca011820a03068440818206030543c1404501c0310029418040e041c100a054031110405a40c002d4a4000c0102d0345a08400d9070071a10f1401c0350704000000391040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 631012751 1250 631011501 631011503
    0x30307080c0a05040302040f090615031a06030319081b030423190614090d212703270501030b1c0b0103110604030b060402070309080718110c0307 64
    0x490100d140c100e000d10801c04c0383d000d07540c0900244203015801d003050010b061210022181d00341080c011020002c07400c2800c0c4105e03908030702d103c1089400014002c1f0b103c1170240405405020801505040c1a11914140e4811050703607910500b914009403203000d21140341c00d407d010710300f00304107100110b000c034411403107c0b5820034a06042410443c0c0c8803842c1100702a6462150003207607a92000744440d0398450081149844803c0e4441c0d03846e404815200e20f196650030001c203140d81244095404c8250f06250035142d44000002c1d80400340303508140d080703805000558026210281c1108141e0f20a0102020a60400b20420081010f08401d18415180d01400b410160b43e080d20610594541030700041d0308000044080911b206820041e0a13100c00740000c1d500000c04d000c03075110ba401e25404a600f241c1d04080402c18540380c220030080a988100ea0641c1000032100b000b007041401401080000c000a408050790031741940e000c6000c1c0c5204ca600c00306010020301c007507207034840040b003110421 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 631014001 1250 631012751 631012771
    0x21070807050403031107080f0f0729070c08070f170f0637050403090e09120702030a05070b130905040c0504020a0504080102030403180b090a03060b1503091e03030708 73
    0x585c0b40c03248203203080c2803036114249510402924007002c14001c20410902c0c5a42c00c203881c96030762510315240c803840719031000500c10340c02e40c801d03211220362000141c20780907c200c042c80e601940d580c2802c0d01d0141c0319004054403494020007000008950b42808048442e850040c3c50542c5401500c151900c030010110720300540100c00b449480851a1098045403882400c8584000c4072045d01c0e40040404403070450100c5c180c4100451340d00c10b00003129110f0381120009101e0b0305414003111000f41c002e20b2040b6094800d5550f001c002030740500070308014048049a40d40c4524140c080c2c0311942045602c4562401c1c50003040c040850690040798040d15400d650144e921001c82100711254895a4417240c01c5500c044144030402d0f034002c60181e01e001c20120441001511950042d203284240309203140d001030a01c5c03040002920075042070640d039400904407000b1005498000c0140e60080781c0100050300030041c2d901c00c103100c3e181e50121200d5440000c0d03085d46021078010b4101c44019085c0060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 631015251 1250 631014001 631014017
    0xd03030c030f050406060515040b031501090806130b0c040b070b18060405060405120306031f0605030a0f060c020607021f091e0606050301180201030b03122107080705040303 76
    0x10328000d80005010a24a0b0750421461810303003030460041980d4091070b8401e1003408500c90240d4040c0c0240c0b400e40c0c0c200c24006155403900481401c0b0603240203080360511030500000a400681400345074443e008000d16481d0900b46494211040f520040c032003104800184400c1c08000c0c11241561038807030f40700c150320400d520b44081c0e00150072118940303030969102754420841001404100c2d44d01407440b0360100e5a1202440400e00300c1800300315240c60f01640300e0000b441e900d0000d802549094400c1813000a0130320b40741c0c1c000c207041070100b250540d0b01654105500742000200e2241003081d00d814800341c00381d824004002516805c0d4400101e100200500a940b04442c40d94440c15145074040c8038020700c0b01506400c1c1e50301c40c98004d0152541c518101e000202c41c1010f0141441c09080e403c0d5244038003020358019001010164450740e003601c41c030075441d82030140000080c030032880d16090390080390341c41c000764400030f400061103c0c041150030414820000d4120003034a0503039a1605040700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 631016501 1250 631015251 631015271
    0xb0703150f210203070b0a2c0607020a0306020a02010e0f010e060423010f0c18140114130308040317090a03060f02070b0406060f050109030203030f03060a03120215060f0d0303 77
    0x41c114501c1019604d80503445000070700101e4900203044030007283e214100a05082d5400d908040340300032044c6400144c22401b4a10752400200500080d8030003442c800e101a1281c0b070b00c4003260484010000076079501c0c001c010800350100a0720424114460003407104010380780200b511050b020340000c03c01d030703445403403041240200103541103e030307400b0f20080148bd00c80d0b2540d2030141070b140c101200820f641820700d20300c10880d4032001064a00300f9141c403100804d024011100152620848032150000303014518403100000400b4000354000c1240c42d4446045040c104070034001952071940701c580030421400180c480450300c0c4200c0342c202c94006869002d10b01c2d07070b102901c01d03c038006000d80f01250400c010052241e101105544a58040081c0a07894200640e41c3e01046c1c00003951542c4207100b0745880d500c6c101d00466120f0009000d41d00c0d03c640ea95100e20b461049856450090303080848101718015072500941d502010469440714946d1800c00890070815088101604040c0c848103942 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 631017751 1250 631016501 631016549
    0x1c02090a0914100803090906100504050d08030603010509060121080c101a100815010e030708100f0209010c0605060123070209161b03090b0301030b0703150f 69
    0xc00104001c01080c020950704441e81e51100004440c60202031000c0c900200d48040000207642104c036000d04a5040342e11281d08224211a020151a0800404000100d41d94942d82d03200031200d881041001e480782005401c02d82500d42c024080507950b40000700420810200c07040d40c044600c480e2004014100c800e04009040c0d20604d44c0f1442c491042000305103200c007140c3c0c8100d586518800c4500c0f580315a86042040d41c030007801a040018080c0000306000724001c482c481110315050406c640c42c03200700400310381000d43d142d20480c200d400030204414038040c68010751200c11391406046181a60000c0003a1501c01404805400c441d0740d01d001880301d9008070301641c01040422070f1540220482040ea0300030758001302080340240d400f940030610048104560405200c4a9250741039040d95036000b8007503018a500c025000c0140003900001c02c1c2190710004c2d8023850040ca10000c041c50415009001c0d42c1c02210b804207000d410003810000217250840b070005403421031200c4282854040914 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 631019001 1250 631017751 631017769
    0x10c030c0b060d17071101050a050a18081c030f05060105040e0a0e0304090207030e09040305030402190b0f04061e020d120e1203070206130506042a03121101021c0209 73
    0x101302d1044144810002d00185024140036442a0f1502490403e4800115894095a10a200030440a1004a04003405100845c00c4141d440c3c41e01e0703103c2503403104190714014807140c0040c81030342203032040b0342060344c5401851a10b42c001107040c8410b080c4075000a02c0c62181c1c0c0b24114102050102007a1040110380006031200710060071039440700c0d06c907002c0900943c41903e048020400d030403540c6c0100d00b4140811840746400d0b40b542c0f03055a8640c1c080c400414084110b00c1ca0f55214074038041151400a00030382050030426185c90349542c2005005030403a088a0141c443d41a040781900c0784840d800071701a01859580c0c0341401d00f4043c480034072009441e40e2018100c007802109125002030540c2000740d441b540c00740d800c03140c95407911160386500d1041c2e00d00180158002c0d00001d80420308040c2181c4028082c80a10648400008501108036100350070494030a038142081b12440c0d503000d02d0400c0c01007103800085103021600e10741001c2c1080a020680300300d54002c0381c1072543e41c2d507030815 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 631020251 1250 631019001 631019003
    0x81f060507080315030a05160e010806040609140115321216090c14030405030d0c1709010b01300e03040f0e060405071d040506300606010c030c0b060d 66
    0x11031b07400c200c1034030f001a105c44c13810824072001c0241c1140007840000c00203c00d41200e1042c0c2c064461502c40b0b4440300d018259002c000d55091159401c442a411803d1098440c460f0000c0d05803000d483c1008503c0700d00601d0403010010983c1862036200501340c46495054140404842c400a04000f1102840c18401c00394070000c040700d0758000c0041c2503800c503040803901140666601d060b00008202200080c00705840c060081c2d8002d0001417030a54456110120b000c0e01e900b40b001034103807500e280b02220007003242e42424a0b51140305002255030440041001c00e01c08211141c00102101c00c2c2c03c0a0b4041c88a00300c08040e222102e45481600500480c0c019201c42d148100302c003526a400c500d0300ca102a1001c902072458a07000070800d504c5100c00c0032140340c030008820302c2020083c0800029000c00341142d50711030000075051100c0c000200c0303020600c0e41d001044141e40f03807011030000d040520040c02d16051041d12146040003035440340003181569403000240700c00741c40d014086800c440050748 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 631021501 1250 631020251 631020253
    0x3080a0b040e07120b01050d0807140709020a0c15021602150928120b010b030709080106080709200f070609020a030b090d020f03090f010c060507081f06050708031503 73
    0x40410600007035942c83e05001c1c005c2c050100d1990340c0d00c00303000340d00c4400750f001313030aa080512850000071816882e038911107000ca0200d40c3c0072901e640c1098102c2e8040204000401d044911000c1000b68a20071046480349413002141056400622103000803100c0d90000c0c42901c18040e1001c0f6065902c042c0d0747d140c5000b07001111401440c6000880810101a5002082c182c041000624158080c1021481a8009031500c10b5910300105d0604a80001e0f0149050154010000c43c106600344224001460050018009146004000001c8030303400305440030740d01e00320303c9150b000195200440f21400b00c0010456a035240c0c605001c40101114403000354421506400001842462141ca81c003480d1300c0c2095510300180000280d27511000c2d450b108000d03400c11311101109140c840707401c1030f20010606012010301e066548020845e1401c840d070034003143d1208148070300b429015104080307455802180d14519410109c0c040e00a0140b041e00903c584000000143d407078600413082a4035520180c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 631022751 1250 631021501 631021513
    0x8010203070c150506010c031b020d0305030a06050105090307151403041112010b0a030212071701141006080c07031205040c080c0d210302071703060414010303080a0b040e 75
    0x700c000705402200d03802510420300401c01c03c0031082d002d00c030381d9010740c1058480082910151342c06a07019800601491103a1145481550141c1c64100c07107540e1440c801c4d40c41541d00d1a06101c00400c41d02e444d080070f41005800e00c041c40440d14000ba105c8141c5090740801100e000050200f210b81120404420003d130380080706000c1040070b00c60b00c0006845d0200c885c000c0322200d8210080c2200c42400e40654044517801c0c00f02301504191015100c050165415180b0140d1100803030080ca540001c10004161b544800d40c103400d5040c29111508805540911040710b40b07044070050030072001410a010509000603c80c08160150030300f4021100c0d88501400300345000d0800c588001e80c20301c5900302a009520400038607142450428003401e03801100e6412512418184a8010005101100a05500700700140c00324a802da09001a650050b1200e03640740361041c00d01c801e4543c0344010181d000c2d4150018030009801c610303203d90100d000e08001609510700c034000b40140840c00c90640e5240500e1b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 631024001 1250 631022751 631022761
    0x120209040219120303140105100c201903060e16210c0308030609010506031018020c030c073308070e0a061214070f0516060618050a0b01230408010203 66
    0xd07402c80c43c06403581c044140c440b40c2c0d0311410f06c03545244078803002d0000f8910ae20014001a80f030b00091801c0d40c2c4001d201c1e20b9124403440410380174801e03403101958004201c0c1c404c2080102038000c8030f01245102d0301800034040341c0c4150a05600c01400b0b030840a20301e01d0929440321090140d0482c2040e001218500c810781c0d0707401c00c00039661041d140e10f8056040303500042014100241260300484980d5150102c281c41d004a070440c038018001c80090b055000c000700401e0010400c06400008001800b030301c2c14900d40741050402004003140700c000c400c0c4c90300c010030105013035245148506403281404c586d02d580c2ca000403242894039080c00d0f50300800b6114080f0740940d00c940b400c3c0c0e0054008500b0404001e00d5480d071802500212040f00000e0b08095005842c1442100038040079070340c0e800f40c11000d11082c1d69040c1640d145070084040c0d102288000c0e48019030602074190031400b020010003041141e180020915980030803407080c3c1c6500042c1c681d40300c2c0b91a1042360000d014410086480e400e003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 631025251 1250 631024001 631024007
    0xc0304140d09090f05070f23070c05090901050906160e030601090507030c030207020f042304120f0e09070f181806060824120a1a011202090402191203 66
    0x4580a5200b03c1c500d0125600021526441018042c40c095150040720004070802164000c0c0c029140c100d041000d10302c2aa00c6007540b002500d0001c0c442da06440d04641003005000d10303454003c06440080e03050100f401070f45140425241d400c40c020840b016a8490204d000755003581d1001031040d018841e0000006012141e0751116000c2d86080e6410710034141d825400318103038041c0c00b80203540300100c03108410351460254020051107004d030041050800702c03081100001741c41294290f58016020b012555041e0b40301d0003d911081860610302c5021410801052004400030244020310207c0c0c914034aa4034020515500d0060170081040b003010380310b20450291410101154420038200302c3c0205041c1d01440d02e240c41002000d540c405800d014889070380f0101007200840d038029071b03511300d1446070000520851071154020074182c01c0029560710002554072050303202400c2e81c441c0d01940f00041e60b039082c2040c1c001c0c1e0104e5000045529142c030902c0728018581c000700c1682c007480f044804150f0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 631026501 1250 631025251 631025267
    0x20f1603020712021f0c2a062c0f061b0d0c1a060409060e1e0c030a02061315170a0b090c07030e031608190b0c0304140d 53
    0x4400e509481c0b4655458004000490340d0000c000d50042100d081c0c04d80c25138041007a000610341625054143c900c80b51140c19490f046400b60007221280d9011075050440c00940c81e10040125103446d42410321000d00c0c4039003611070f0110080041e2400144c1411a03518114004001040108960f0f03030794102583c401140c00d02854240c00500a42c02088000c60040030031085e9550041c030034110070300c0100300004042d440246003aa0081c1e07290742d00030201e52180701c1c007122610320200802030101854090208030f40d1603243c1e002030b68800441c0280603100887c002008980c107507140c0f902d1320321b1111003042071209038100307e0f034011101d61041416503101c900d070302c9504848030b00c02005841e00d03140b003800e403100c1c0705005410404c2480400d0000250700020814a4080d16007a4040030701032002a0030701e103882e00f000300800c6102c101803003000ca051208be44114402441ea2150000581e0380880c13202000b0660380040802200180c14040410300316805440c2038401ea234cc0242188a010300420 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 631027751 1250 631026501 631026503
    0x6081920130e160f08040c15030c030e0f03090f04020d23070c0308040305030405030d0c0e04060902070c05061e0a08040606062d0e1c030e060a0c0204090204020f16 72
    0x19103000208558425101502081c1a0315a55250f91040000c9050319203200280007250306038065800008c501404611440207915280d402190500b03000c1e8004082d24034403000d00c0d1160300038104d0700003004000422165001800d0b40c03101044400480000c000303005402c4522085c9080c50320814000d140e0b041c142d40da84440303540c0007185441d81030040301c03512030310000200414001c101103030100b8000e1f4003850344503115000716031500036445106800e481d150081e820200c1c1c1900c0380200140b501c0d0143d10701038689003000314103000041d1500c446d03031041846001e01401c000100b007003825100929082061981140c2c0e169210184e0310000e1038030030101e030217940d800d203000b4001c100c00d13200304010300300d041c0c070400c001048400448112901c4190940414280040c501311104e41d83c9640f04229140500090b1558044140341806041d1240460031688158410494519000e030018500c210544d0103071000a248501440410002d20504418108864000c03c1104d280c22070848030310541 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 631029001 1250 631027751 631027769
    0x9120606032307050103090609060905070305060901020f030c030903040b04080601061b0818010e18090d08010b1801020a0602070f0507050102030301121b1e0306060608192013 77
    0x30640b040000201000140701c00086821030300b0200041e42c4031f40c02c1a400e450086000181202066035410110303140044101d0f401c0d0000501013050000510100da44007000d03030025440c00c4201071800455110081c007400301c440000c404202048400c101713807030240a8401d01a5680d5469402041d5140401d11801e8005000a8100813400e055881d0681000d80d00c11000c07800d064130804040c020040c0010054104420741213101402d640e12410301d1080c15010f0f1411000e030500094043c1000303140e0681e0801d102c698801044034a20f540b08132000070440d5614800d814450b00e00407801c2c14010007029000c607001003a4602404895000ca42340c061044040340c4c196552103006a07124042403040b480014161481580442d504800014214030f4000100c2000746d100d01c840703800d841c484a4416500c2d00414018410001d081c4200c1c0d002d0861030520740c1a40c5407880300340d668401b01100c200140d81c3c0312002e41c4159510303a52442d00c003000100505880d29192110f408000c41244910071030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 631030251 1250 631029001 631029023
    0x40905210d0b0103060f21060c030c03150501080403050a0311040e01140f0303040b0d020f0a02010b2e0f210b0a0e1b0a0c0503030a09060e2b0912060603 67
    0x558001c0c072801c002c4881c24800f881c0b2091501040745440140892622000da68185a001c0003614a11500549c0748094500142990b01540300408841402c2007502919041040c1881203a8001e03401d51350055041c42c1c00c1c1c2e0343d0356142c02c08402909010034591800d03540414045003880e00c1540e903038140c5505240054a400801d41001003c3d030401100c0754051300208814094401030a0042445512440340549458410102c4c0c070f699606c034113200380040c2d5481004900030f240c1184a60107030f8801c442e80d45402c0009007890303010075035003024400600c180084070881c0940206144101d070380548120381d0325400041481005403140c0c01e00d451141d07011880c0401c0c01c6494140c110301661401d00321800d510b2b60b5001070360055200130b000d8824018582c201d14000b03401000258440c00d051180802c0c660200e05c3c150b001e0703400150007260540c00000815520b40d50800100f030031121544582840c000b2041c0007590694a0364200c031140050440544041c8011500010110391142c000452 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 631031501 1250 631030251 631030271
    0xd03121d24010f09020f160c14041509051008061314061612140f0601080a1a0609011e050c1204270e0a030305041a060a03030f180e090d051602040905210d 68
    0x101c0d401009031602d140c2c01040d00b0300cc0448103a100560015680c00941035030303a20303041c20341c0c6095000c803013280705000c000e04400100306e800c0d48015110000b0034000c0840f410140c054400b0140100c940c0f80800111142c9545400101d0700071081300144841c50b049181001003e6134080041114610701051780e003000b180c065030851292840080c204082c0458254044040010316441248003e0402c08801c4205100c0640043c2c410003000c00c648803280e540004a600c0780c00c12442e540904981c200511082140c17402029410302101682c0702e075010158111102c44000b041c903105015110304c214000b280815415601050080780100b241030303600c400c500c2c1c0c498101706007242c40da130300181c07c40001c1000a000d1215441d100d074180c204403000000f890500c8146146540c01050800b22010912085213014000082d030907a0301d2030400e20700325101e80b51b602c11220700c000003401942d03034031b0010051020504c0b40e00c20b440203c05503050810388101200a13107400468400d006946001001c207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 631032751 1250 631031501 631031509
    0xc1b0103090605070e010f050a3e0d02010c0f0806040e011407320a0c1103030d1e050c0f0d02091003020a020d0e0d03121d24010f09020f160c14 63
    0x3d0443c0c00350703940c141c03140380c400034094886812901211211140c0019a0029410b24a80380cac1d0359030313070352001822840990f035002800d50300c60030f5088050068001e003801c400c82c1e2000e40254000001e0340e0108c4ca0040c4001d086006144482d8014901124503080c44101e540c0450607048034031403803020700128080b2501c604c0c0d1050300e144410b41a07a0f810007064100601884071807040c03900a200f608034648802c0c01107410365210400f510500b40c0d80f820b20301407480c062120a8412240420708001601c1d041e0901641c4d40300b00042d01003c2c29000c905181801d00d150100c50440e030016004c40c80703180204e41c028020350081060703640940501d0f2500451280b041441c01d940c060000c001d070310001032980382524203030071041002c0120b94a80c11408006400713001d101504071042402800c0030002808880700760341080045c9410300008030010041d002c03105004606a82c0c0607800183c3e9801c2000140b03019204400d0101403c0155800c07503410b0110480e050b100300c0c1e1000c45401c90b0014020100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 631034001 1250 631032751 631032757
    0x50a2003033c070c0f0302031b2e0b060409020306030607020f06071b080a09030b1b071205041a090f0402030f04061d01020f1902030c1b0103090605070e010f05 70
    0x121907a0b20000c0075107460105114003880d0050203d090120350500252600440daaa858606801581c400103001c080550454441084c118501000d040481d100c5c0c504002c008500b5580c01c044200b44401c046003140300d03a802101d102038004c00e85550369a40714131150280d007003165240e2007400b583c8002498140045000113001803440c01511083e501c1100640e41600658900c4000a80100c80980060700c003000a150000d000e40b6000c100e5840d520348821361900081050030404841078118403511411030a0307031103803548070a0300a40441c0c41d42c0c1c1181c0f44d02590788400803415a40d0303880308031407440000610080800743e801000d49815401030000364403094030b0080ea11300d220130026011440d00e9000a4520840454000750080507440b001d09a0f082401008840c044c009668040301e0312030b8403085c0c240034150001d0f50030005207542c12070712646155030320410090641c00c017424603803081e80701c9018180c1c00740007040b050906010080c0454103410240340070803d080814000c0f0f501800503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 631035251 1250 631034001 631034071
    0x110a090f0f030f030305041e0302010209090106030c020d0c140303010f030507141513180b010206100b07150b060d0c182714130213060b030106050a200303 68
    0xa500c0f8070096a80c0c1100102070041050329071841c000ca440d5440b07038001e074034005028002c0c0d0000d80c17110b080c0010000808410f900420034103245c44a0858510b402240c07010406299007400d000461a9040c5084030607c1304a110b07505000000c000705c2e11010050450055900880c00c031341e0000d85031004038004034100818517600102801000c40d940100034000d0804146011004411503643c410900074403000b80d03101100d2a864400c400306a5030f0400800354052507402c10910039515042640c152881030400181201200083c1070032000c02940105c3c0c0d0000001d820559103c4020303080c0d0340200340906400001424001c56042a0445a40408140e0b03040be5150074030b01c02c150420b441a0b00c81840944000d94032080240f4000c1030440703400b88203010b0500014004402841044095684032070b158811916082d0140031908000094038103580c840d0402c660303640c0d41c8010586200a03d00400910450b1903210101210004000b41d40104a4204502c180048800ca076001e40558105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 631036501 1250 631035251 631035263
    0x3040909080a020706031a061c1416020105011206090c1508010f080309100302160b041a070f05070b06014503050a06090c050a170c0a0e06090604110a090f0f03 70
    0x1181f01124034211004080015138030b00c5400180003203139511000d1f21144201100041650000c11220511620320400c044082d031000f007000350b0400d500940f02c070301c00f000058100d0381d841c21050300f004940383e410000741440c0e80c111900c5078224074008164036401d00911000301200e2000041211001050700d03504180203004540c000b14521044001790810318030f040300300c000b031110400802c8218003014051809081c3c181c82c10800305203200061000501340500b0440a640304641c0c0c1d41d8810140d58886038441200c04550b1140350040750a00425540240601c406904450218400074801011500c00401c3e486940d2a030790100d20440d1070510020382950000c10000000a180c2e900524840d44a00908001e1948420100d0034091168200b40c5890103004403003030307641004219140541d00c5c1200c1c251161810400c0c01c8005240c0036040500807600500410019603468103d4441000e003403080e2602c5046210000300a80c6040c0b00700240ca26000a011506080340310049065a4001c031b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 631037751 1250 631036501 631036541
    0x50609061005040b0406090f0b120115021c030c020105070503060303040b22120c050402070f0303020d14150901081b0d1103070308073e0303040909080a02070603 71
    0xa081c07007031150741c00241c4030070014204404900e000e640e1018201030455a0340396003c3c1c0303080c594400b9440103144c00035001d00c4006e00002080b40c10100304241940d14072003601d660740920690603840c201d00c89000d501700104403601920301e00d070705600c45412a00140d0003400142c9a00c50240c0e5644401d0b0344068140d0400c00c41030141400100040883d1011114501700d220801c2038104040440b81e0400d2000c03c0604528000340a04505502c0107003204540071481c0190680e20302d02d500919442c001c0c10305402060681d460301c4180c1c81000100c9400d40e5940283c030f0480c40131000b0719180c0341164032400801e0008a0204400100c008105c5041074040b030074200e0450400540c0c11944808070359010b05040241e030281c80c180040002544a498016112049454544501c0b400d0307907407400f40c114007a2441c9861001c3c450241e5148420385240220303010440380480d09510864120700080703400c200051f000c10103064000d1540314450380c03c1c2c0d440079403102d0044044d2012070b11500b042d01c04c15 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 631039001 1250 631037751 631037761
    0x1c1e0c08250e0d08041514090114090a090b01031d1902030304030c0806011a0703090302150c03030c0d1b0f0f090801290d05070b0f07050303011e09050609 68
    0x900724852622046060140700c1030340746400105090704510003158521004a410004010740c911130f00403030101c60504621703d20400c1c05c000303141c0c010014000c4c10440d80414100080143c14100ca5a80c0009000000e45c2520740b20030f5000340001c81401070000b40303040103044094010000307242c0c07004610360282140ca03810f4452400d04001d145400d036810300082100000045061540000500c18003005d001158035041403240310a01202e1000701070002003006070300181e40300c3e00f9001943d0381114800013044140c121007100d0700601c034054490b07100000c00d10030300000c64800b414621281050a2040c4400800c05500c2d0003480038880006c580e40070b40d44841907018003c840e0841082d4030b81b00e01c50030390342d4018909503120070801c0050f03000c54540203100c80f60241c0000741789850030707234101e464039515603101c5a80d0310851040140218000c102403078074100c2001100c25081d0454110394403035840b2030543c01c0447d020800c0500c1c410b40392000042440031400f819200c2c040c0203056480554070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 631040251 1250 631039001 631039051
    0x403020607080405061801090b040803070b27010b0307140901091107060627020f09040f0b0d051f0908091e1c0212010e030306061c1e0c08 61
    0x11441c12076060009020104241d2900d0b00174110305040c804c00c80c401900d8440004d03100075034039044200850010001132028103000012500455440a50716804d55101203c4060811040d14502049907854007030000030007054006840015044060720030303207591100d03214101403100300110f4000a43c08010005c4001640c0700421015414280c5442c0491681c0c40c4030845c1d805410000031440d2a112100e80c00340e001f0400f43ca05c006d82c42c000c610f0803012004000d0700d070184901c00e52159880712110107864900e5000380d0b110500151510940707040c02d245c03460700d4541d5500c40307910b40c0340150140c41c2d0901607070040d051869000b019061400080b0b01c28803615011040030000320703903c5100b10902540361b041d4070b80311540a0042c4040303a04018070410030048500900a00541c0c10225481d6603040040122074000b1421100c15685240804206443c150090788030300c00c01e880d14044558464882e126003918081030b40c403c01200c030138442c0584803c40306541100b000e1002061400d89885 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 631041501 1250 631040251 631040257
    0x10503040f06020d021804110d0902130c050c0616080a0b0628020c120d2105010902090a120b0c0d0207050609010b0a05011103031f080a0609110f010504030206 70
    0x10081d82200581d01e2240c88840070ba900c030038149225541c2c0001c80b800205205a036541c41e80c03508032001d012014501c041030a250103400c0341e0801140c1e40d945114119610030149643e4200e00c00410700066042840141003074114845114840c02600d00052806036038085130682d040b12902c41c01d00300c1d100e440c0c1003001840c1c002d09058110204100c402e054550f0780f82c01510040417480c4a124265034118000d00307020350321489600a0742c1085c80c0b940114408036070443c00e5011480c00c848000383c04107244064004921080890300e10b0034002089079078082d0018019030a054803c8440e0b5691404450584450b61101400c0150540007049210b100c0303c0041505a00400c0e026040a2080c0c0700c240c03c00c0c0040c1c4500c00315039500c8100c020342e4100140391000800090800012103008a503002c1c3c0c9a1000804c543d28904000c00b03a8004550045000c8000e441c440049410401c0c49240240c0200305810084e070b201001241040e02910300803202c54040c080c10b170345440c00d003841d55080c0211a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 631042751 1250 631041501 631041503
    0x30b01080316081e0d20041410050f07061b080108030a030b0103110d1d031c180b09060a050f130609050f2d06130f110604060f110a02010e01050304 65
    0x188980c40c55816100f90b0703010b046900d8954000051100700c6c501c00c1641150a0301c1e01013030b10f003001c0c44208802c0300618450125580240c441c0c030700c0c140e4051070032285840388440ca510400c1000c5a03030707420b10a0355880660b68001c42801e40c201c5885003401a40c203200e0901c640c0c1d4499204004480c4028405d4200718011501818085698510102500101c0d0059481000c1e200d0756128141241d4503221005942007c4100140d440c0540c004480c080c842054003e20b45c00c1c60326000480000c243e91104901180c1d0401075400e600d0038036005d8540c503100d059031254000350410001c030380c0b404802c0003500c4c000d8040d1508181840700030340e83c150280c404688291160700a0554902801c4828811002000419070b0508024121070140b40e00341c04a0804d0b6910591021041003007102c2c2d1090310a0f2010f401458801e010900b0b8a0055600b804842d10700d0b030840301c0400d0000d0520b0f00301ca4190f402d22884e0b100c2d00460004140041e580d2012004084e00040c40c2c810030034100d5011348000c6400c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 631044001 1250 631042751 631042777
    0xc060309080711030f0d0302091314010e0c0903030a0915081512011509090c060509090c0d0902040c11100b03030307140d020a0f080603060f04020f060418020301030b0108031608 78
    0x304001382c8000d81006d4201441e500466000101980c55241c81c1c0d1111000c40340b2020200300c10b240b40e10341590342203414020220f1007a810700119800342c00c06000d64101010081c112036460303001e844018584282ca00c80e80e402d0384c2e03125810350511170082c4000c0341308903858a40404405042d000300200210043c44001243d581e520069101b03c1c0007140d5800603000c071040c04600fa038503501d41120318080300e500210401100341303c220388a40c0c8010007181c1020701158180c0c0c8400d0703d051424010074a01074025032051401021015098224060031100c1c501041a00c1c003035003040b044a4151481c03400400e44c15042000060610760160003580c0c40e02141c414010708100c6040c40340300c100d91002c80502d0110324040d03034a81c50164070441807a070248040e0003426807402c4c0700d02c0401d041000a44006d102e08000e001070001511250180c5004101c0d40013860401503d01c26080002d600030300040c1c0e5582000000807500300400422a40b4903071400818540600c107540b034a903515081024509c9003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 631045251 1250 631044001 631044013
    0x2090f130b1f0f060e09010e010b070312142505070807030e0a031109100b310b090405070f1d0418120f02010614060c03041a04030c06030908071103 65
    0x380880c0038095806880440d0183c0416800d1041c05807450b10507110031449100c5000043c42050392a091090456642c0c1440b90340710f07032081c6000d88185d0b24582721654030600d40107070006501410140c0354006d12100007218550303645042140d528000480390640818000c101003000180501d0040040c0c038001e15100510b001c074003000a50500040c1d0061300c0c50b80280c00281e00610303002c0383c0f154011750b91706020030710f140c80c149490316503000f0840710b04005156042078003856100701482018841d5030b01c3c290380003076840340c2d000720040e008032003824021840c01c00001d28035801194003402142c110340720720381c0111254a1401030814002026900640c40380c0840c2d0141c220009450000740c8030b4001881800ba07411401814481141c2403582103a04010080003088601c4540c10759150342601e040c1d80c0d03030303031002505840c604c00c550024213034204c00d031244000380b0441006402900d20a801e99070403295208030442c296001c0c400b000d44441401c22030b04000846a020001103504060181c0342 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 631046501 1250 631045251 631045291
    0x60708031b03040c09050601020c01140702010909180611030903030609130b13020301051014010f0519050a022e02160213050612030c1506030313030602040302090f130b 74
    0x68542c20644003251040d040110900ca40c0c525405250781c004820702c000c00d424441c50b000200380900d20000201000000180705082d0391080c8144d001400d007256041c44801c000700c1c101103860b00120800e2303030711901e05020000700a030003404803805180e40f40000c40c219104e0b8410480348090207030114003c0340303600701010009900350080d94820b403000c42100d00024028010301d401d4075401040d014040c0c40c0c08000344600040040b054100034003e103002c0340b2107281c0400988080c414590b07600140c2518424114810303a00000a1820909603800d403001952608060640e03c4107036044546420822483c0030a014040e90207070130a6181c070a10710070300300441c4e004207108128036940403655503100c0e02000020300303050b0340b02c80b8440904402107103441c0c2c0070200030f03480300344104903001c000e07001c00017181c000ea50400503103501300009510901c4d515568940794000754424070040f03001d40c3c510400074800500040d19a889019000b20000e24a00d40b56102400c943c002048104600340c5807807100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 631047751 1250 631046501 631046551
    0x4180c021c05130503010902130e010b090c0c07060801080703080f07020405181903020615010306030c0825120f0206040b070507091803120c200c1002070506070803 72
    0xc00e5141c2c541c1d0390b9410100300c100d034041d00f00d904181d01070307030401004000680b20041840d148151241000400e802e0445540c0e0240107040311003079000081e1001d00525400c00c0c80104811028042151071700e6644aa06a0300710703034248561140e50f0007500041005c180010020f03c441a440403078249400c4044d8002000c1381d9007502c1142c02c2910039035480d41e43e51410000004182040d8401e41c0481c504ea030350095594000802014241804680b88911b50340070b034210b000510307407000800d0340c265212080300b030f81d0303105540c4003040650340d0f013080700d00004c643c98030321046c0c80d04054082c13000c48182d183e807406150301d80d0302242c0180301040f00081050107a005048158072603009000c0080c40d101800041e02c0c85031981d015200201800140040d4020b900d2074120114968003140040111205864070095012103c05200703a01105640303030341021500600d03a1404460150030400640412640d4096078050550402010000b80c00401d03142c074041c5611400080022000e0f40c4540840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 631049001 1250 631047751 631047793
    0x130f020a0b0d0504120212090d0c0b0415090e06090403080417030c070213060e061507050a29010f1e0f15021e030703030f090b01081b03010204180c02 66
    0xd401c0c1654403c14042008012500319184220b144028500f9003600751000841b8440d060140d4418810f002d245801c11400c030b080c0500501d80d1009594607659600c040111a40c1603c003004001190200c0118882041c142642e02405000c0c04405d017a64491b5019209044082c00648400d03002103050004941c07000d00551180c1016030030192951121710604c00700360070b85611204401c1c20414140280c0d1140821194486001c58005401d01c0030300d00810700a00c40d80360094071038080c0311030520a021003101c400703800d0501c040c54125514441201032070856004c1c010040a4a010981005151040e042d80c408040307100007070b90003e5964041480352409180d0200c001001c51071440b114450f01886120600394100b0031102e86c500c40440060707281d20400750002d0a1540e91210703900720703400e181d0128000c1c07548000a10910350310748032040e64844999425540e2650100b2241007141810b00a0340c040ba80f08140500b9600c4501a00d034020300354542280c800c500c290340700700e90710844010007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 631050251 1250 631049001 631049017
    0x1141e090115090e06030a03050901090b03040602071e050c01031d1c030b190504090c051305100b0903100b01110607050901020c04060b1204020609060408010b0f0306130f020a0b 78
    0xd0480340b0140e40c0780103860100c036540043c0758030b6950300c10072003140c6000c07402c0000c080c1d062070020750782c948400058400c10034607048213400d008040108010000c440c5e00404c003c0340a00c0c4035007012007010313203c4130324200216802410358111405400c0c881d40250054407100c8503550064103040c42e0321100c85e240c009071f1907000307144045000e000d00c402a01882129400801500c00c1070101e18040070070044c0450074450300d40200c3d80e0760600790620002150401c040e0a0007440e04d05410001c82000d009481c0940304044d4102821800040040280d0103e84080401501410303032840070136403041c004e1011034101814003079040c00100e0021024000144500003903201c41d6141e0314000c00080c644a80380001600580c5400c0c010300500c01c1c41420b4a0250b40c0d029a500e46030780c1c03984007150341c50150460281c0c004c800844c020030461419001160125800d8175040303128002c07002056074800c0c05071404c1e489640c10265940100300e140f1207510b1424005018800031a0340d450f41130003d035110140c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 631051501 1250 631050251 631050269
    0x1e09150c0415120e0c03060f09030d0203070314150d0803090c0414090d0f05071e140c030610120311010b0303070b0411101b060e070806100b0301141e0901 68
    0x9030a4010100512510082c400100c0c0105905140c050201f55914006051300004001034000552420820400c407004900075100039502c0e07081c6543c014010b0302c9001281a4849824070003d0b80118150082d0751450342c004242d0240c00b00103854074000d81d44098a80c10042c0502030300050551100c0c000d00c11020040c1e040621140f401241150034180130480000c1005064161804443d91081c1520605ca4100d404c0003101c08110202d0031030422085001030079220825454060032030040b4980140c0759050b010381d403c590301e080f40c1c200d80694a000b110004036500400801180c130030301340c1c04031007500c61000003403201480740042e14582280c0381c1100c054002c0c208000030071140c50b9244c521003005441500f0203a0314001c001d03206c4008920b050500e954040045010702c08160030030301c2580203003015952665191001c42e600c1d800116054412065640b00019011000b00d040b24102c48090790728101ba10400e404200d420340f185012481240100d8000b1005aaa048030180c004e045400d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 631052751 1250 631051501 631051517
    0x7030302120f1e09030307030b0d02090412090f03170705031c050601090506031003260403050c1207030c1406040510021b010309030c23151e09150c0415 67
    0x18060005043c2e24031091420340d076071a402d1100c150000010b580e002403007800c002c2001140480802c50106480303501035444404607090100340294400141d140e5181940c4120140380ca40d441888180d180d80300003000300645800321420325603180e01030185d0078822420341e1700d000300395160b03102002c4106042c01c5440390303520305001e000d60300001034500515003a140603080d407601c40e421030032502c014400a13182988000744000321100c2c00300032804c0c40e440300404944554aa040c601d640719400c404180c05044403d44244030f0800020301002142d502043c0c0d004280d041c6440c03008800c81e1401520b820240901010500b643d41d101500c0555680e40c1c001c146480c0c2e00a40800c01032441700405050600c0e091001020991046031080c81700e030030200c06440c40c00c4548000c01c41240c0c403050903682d405103090550340503421162850103049000c00c0c09242d51401050042112019200399503558003c04080071441811002c170781e4041e09001019050541c0e803018045207480744032a0f50006020a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 631054001 1250 631052751 631052761
    0x30f07270b06030a06050a05042319020a020a020405010f0b0715020d0603080a090902040510030209360a140f070e060f2106240c0718050a0e0d030207030302120f 71
    0x2502c41f0b03e00a040869003400ba5140381c84400c3c000e45aa9070b0780c402c1d4440402c001403182140c0714400e0300c2c612104101190740d0440d1042c000d441c0c900b000c60072441142014000903443c1c6c8401e948805580401507002c1c508045996100d541c07448500041c03100540903c030401c48505548900c500450017040010b0b9600c0b04188000c04040306504080504c62041c03001340240d84030101c8040800c1e505081c01030b41c03100e002002a04040c844e64540e0300542d4548400c121584100040c40c0014882d02507921b11520b55000782c0082c1d4600b840c14100c1ca0660000280440c0845640c5907042511420441d82d02001320001c41c40580c012030701d080044100141d41000b540c4100e03410103c0c03901008803005541452000124200c03124110070204440fa03c4044000181c0e0904a43c0c5c40d090440488246942d110841c106445001d0043c207000d914280014800d00d42a00507921429000310141c0b071210707681d44040c0c00a412400040d01055824090b0340804a0700c204514090f14846600b02281d1a103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 631055251 1250 631054001 631054009
    0x80103030315080d140f031807060311031518090c1c0206040b031902070b06090f040f081b0f0304090606050f0906090f1806030f07270b06030a0605 65
    0x24011041c2408030702d032004110b0014003040ca411844403d1030704000480020751071107040e000d0500d40ca85058000403c0c44000344203c86020448d003101010384001e9a91003506800325003980078800700f040360030800921801c60903180b616110307000600800030040100500c400d030b008101e480610a41c41406004264030300b1480141103183e050031074091038603455010403014002d510501d0444031020001c59110a440c02461080d407440000464503401541028034800c441a940540203080c1000030484c19450350f2107140c81250480961040009155600c0030345070300c88800021606030322000a4140320062003c42c43c4550318100030741e00d8504010300c20088a45603488a000d0220800c640c030301405860b401d8405460301242d040380c0743c0805501240004900d07603415644002225240010320144c0055035018003c143c0c100d42d519010a80d00e036903121014015440107070340070700003c000140300a024500e24a0049004246604a08003084c0c15800c15900c82c0c28480d2241c1091105040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 631056501 1250 631055251 631055261
    0x70f03031a03150a020c2506031413020316030b0f1023031507180e071704021201050f040b0a1406042d090507050d110d0317070801030303 61
    0x503500c003002407850341207000a0707807040f00e03446203c0408a03000c005150203c90340e051320680714500c01070b500c00c4556500c000042801c4c4010700307490100d140d0004180305201b4802c00000c0001418804040c0c3c42d1000009203040c1441801c0360b1520400a5000c03c01c800600322340010340c801c070051501d03070401900e43d0100c0e04000301030300040a00a4010441c072000194541c6484040103209076000811074003003400d05c2b130283c040940818405060040c001c1e44011000c03412640c80c80015480c0e40c4a031b0840ca04000c081e00e464001400d11044401c40c034804c00141070308684020701291404c04080407150944d941100e040c3c44a803014000c101c24404d1074012142d022403000380801c50303118800c24070510054050802d03401569500ca886c42100ea40ea820b01c501c3c0611601811260442156103101400b4000411200c1c7e026248001806052504076549203540c400d805504074980032050140c0360b142240d00f6070400070150031212804191a121600505c19507448040d590306606014055034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 631057751 1250 631056501 631056521
    0x210a03061202090121020d230d0e060f1306050703080703020a0c030509030a15020301090e0a020a030212120c011406030f150c09090c0d2004030204090c0803070f0303 73
    0x1201e000c051500583d2800c0702641550540f10450141513101e5009071032681c0a03c00094002400526000c280f092103d4074174020b024445640a40f14207c2c08220749a0080d00850302c04034152100c202158600300b405031041002408240b41040080c0d0300014240300b60b9800b090100350000340d00e00c02c2c1940820700b25071101842c00c09501d0320841c4240140300d120304107005001c001001c2410806641e062207408043c5400c820540b055100007461280250300a2262003242031034802409251030300400c01e4100c4640040c82900020b145400f40304100004150820b414001d40e91401ca10f05d50b060040d0841d900c440f000001d0500303074040150803200340604414800d91001d035008202c44800164a0b009541c0035444d125252102448a02580180303170344075901642d43c42c100710b03211070640081e10305400701c2e52051156040c2c2480e0503034484483c03c4d40d80c0706084208000d1000d82820303000348010707134490710403064580e40c2d684600b41190080f042c00c4450500f004080e800740756250061100351 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 631059001 1250 631057751 631057769
    0x1020c13020a0318080901080408070204050f01170706020322170601030201030f1a0f01023a090e0109091106030a051005041107030c210f23040e0405210a0306 70
    0x34204e585500e4840e0050360440707030401050000003410072810700151558503038041d1040c001800d100154100c42c2c4400d0007480f20b0b101c0c010300c0c400b24841c2c00244d404100c40198000e145010b0440c0c003840c40f4504d00180d040103050081d000064902110b8098401024160340903144a5045200040c29240d008407216500c41c00c04d10203005d5904400c0704000b1001c0102c90112030154008010307803d020718044110102582c0c0110654120200401050000d8030032003540c00007021070100b5151070b07080d40079054401602c0d000510280801e917000c19885805003240340c5003185550002000c5030300440d0b002e01c4854950003448041c080d4811000042c0c00100c9007409922541072000d609802001c00140c02c11040154070424882688410820001400007078074105a01440203000a01d2001c44400003c0643c456000707160b10b1500000000990000381b10300d00780c54428900c07020280640195018040e0320349450000d0103121a075080c0c3e01454140300d8641c400140050102c0320150300400319 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 631060251 1250 631059001 631059041
    0xb040b1b09060f0304210309050f010203090613050a05061501020c0904200f03240f040507051512040c080d0e0a05150d0203100f2c0601020c13020a03 66
    0x202d03070341c02d410340e141e41d01103c01e9607071a55611304106607082d04451148500e0102c4400c50a503d0341e254000800243c06071013160f00f64903002c00c0c650300701e00c03007120003500507084540171a684011503400c003c80300b40141c048a180759255104e03582080c0c3d00b40e60203001c112100b02c1000c4103513014800c0050b10401200c0001032442c2c15102c050103e840080c200340001c0c2c54440c270200390341d10021007550081c0007500310781084000a01c03082d0902c5d0210b0751852800d00d61000201495000030311280300f683e001c0068803a503482c010500600495490306020310a8041c407651807521200c102d00d5106034010071042c02d0b640d15154620f410109103142110411440004c0f0401d01e48403d00301004541d01990b103c0c005007080c01545400340101540002c460340000140b00c102103c440030807007602d1511440c1d0f80340c207075070303030603c0d008100d541522a521402d807906481d2090035041301140e11450600595a182e621880020b54044c0c80446001e486580850a00703810740e0b052161010610038a400c40700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 631061501 1250 631060251 631060267
    0x30b09010617060105030601030603060939031209030210020a03141e0703020c09010f030203070608040f03231c1113090e0106051c0b0c0a05040905040f0b040b1b 71
    0x4400b07030002c03d65410f000001010407041c0e40b10364410401036810039001c0000002d2032410302c00141c80c140c06440444038150000508422942d00e02c501003159200c04540e0310300e107a4601010b1130801d040d08c0103102c0340850010244c0c031201c0508880c03c1d120341c060121041d403403030043c01494102826058002080c040b26a240d009100a64070f0340d01f11030310068580324146412460440e90b8000980c0046071200006841d400f01c0d049103080d0391088050341d000d03a481d00411240c200c000c8601130007222001402c1004240104200b4004003c0700c4485071240701c034070701540e0156102d0840040050a01c881c03864007800c85100710300076007840f2024249000c0381d45030f182e181d0301031900034082c0b0309544000510204c4400d5005d4001000d000d000c040180074107504010700c01702c1d940c5041d02c103824041c00107010842186d00b1240c0c807842c207455650030315040141d000024900240211442c680180140c000300c0d0a45401500c100c0c441e0703644d4003446c40c000740d50313656080b18a810606c101c002804209 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 631062751 1250 631061501 631061537
    0x32d0e07060f05030a09060612140d0f051308011e051e1b09100c02030d210213091401031b030201021b0d0f080415080105060d050c0c0d030b090106 65
    0x4a0541050303e0102d440b034954407100001090b821900034504e40ca0480300043c040100a4010749190140007074501d01c812524440c1d413216013001d0010009820003083c41e99050203000901a1510040e60003003c26071504030050031144030040d82128508804124a0038062038003032103600500a00f908885990100310410b40220f0184c000c4e400040145c1b4240500400c89003a035500d04c1004002000701e030140ca034058249501d6103010380c0a40901e012940d60140605940c2496035480c624104440400e051140000d4010700616030004103075a0300090020b880340100e0041e10725401c00c40813103500d10b09d04071311115692048454440d1111404001503a004283d6829205451481400c62a50540002c03481307030755030310000d100d0a1001e03a038100380030098000d442070b90348000d45850076000c081c03026038140c80c09109195000f05d04002d5900c892555402031f5801c043c001020901300000c00e04014105441c42c0c44150010340d40324529801803a0501c841c0f401041181041a03000d0080b041403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 631064001 1250 631062751 631062767
    0x3080301050f0d0f21050309060403031a0406180b0a060c080a21050a111813020909010e04120305090a021e060703081006020f0604030807032d0e0706 66
    0x2d00c41e4040d0b00501c0c40e140c45418050f078445a00030350b0744c44034400c0c610b041080401c20380e40c00320748031601c0210700d482c07240208200c0340a400e420008080540d03955600b14040c0082c0c4105412040f207000306070744241c07a81d004400282650035046011306c14806645011114610100c2c1d00ca00c40e00f20b0700300000c036042081500c2540d0011b040d0b507510100090203441e00c18144081c01c100f0080b0b076107110344281099001a0107038010110900003804040221070050103154444081d864030000f550100d031a00d00100c0340645c0d00c5204c09801d141801d0006010304500340d003c80715101c1207004000c01c0098210540d0440704d803504040003070341400d080e0740d81c0d10007419000034011511803c00b1484603525007503c41d400b800092603207554001c9403600511004050b9032041074045050004941940049480001241e0810052080d903503a903c00701d40a01000d06135a00385030b40c56034518468000d40192030460b802d419070781884120700a084108641102c0300c071a0030f94101e118140200c1e64030a2003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 631065251 1250 631064001 631064009
    0x402030610031a090405030309010e010b0303040519090516230301050f0d121119080a12240302030c010c0819050d063b011a1e13090603080301 63
    0x10000b0620a03c0c814440b0003201c2419030b640c0b11800c00200010001e000000b1031040111030002c0c440490003103a51800c2c3c0300c1c22103403151b040d0014041442a4244a80d1914454071604105800ca982d1000401c003200c00a40e003031950300700c0d00341c109525660480c0f150f801e00007080203498124115204074101601060080300c0c402d0140807480b11641d81d40410f40c408443c0c01c4684640200c00007a405460040e040b2403c102c0340c003540303440d03402c8655808650526203810502245c684428240201d490483e00d6440d20500b9584034003541240c018900d021903440b200d12a001016810f500415140c4a5040c1100f0304002c44002c1100000382030401351a505032025600140604c0c1d409410390b4036000b13055420030050324000000410000d603141031507815a02c2803c1541c821030310056041040030044d1900031074500007004201c00c10001c80f07513051941d200e030703065400d01d40741a480782d40c041000752400e045400c010400c01303010b030140407500ac01003804800800000d880d40d40c6400780d602051107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 631066501 1250 631065251 631065257
    0x80703030e180a02130e13110d0f030507230a110a090509071a03070801050114070b07020c0405070c02130f0603050d1d100e0d0303020c010609020c0c0402030610 71
    0x4480c081d0307032a004118901559a908801d52900e0050358040003900884c1c0d01048540e054100040c000000d5101386001d0280800489510501074840708002d101045980d030704200e0850030078000c01c220306900c0302414880d80e80c0c41d6454000d0f0901a50140100502501e05000b09040d19210240000e800f2241c40d0305c07212030200d0310b001e8070000d03410607401c0d4440850700b400c080400503903185c046201025203400c6125040e0081c00701c9402061401300311101c60205034603100600c469070040c181c400784000f43d800d03442e20701822a6250040440d040c0e648401517480842020124506405134651280451400c4429000503400240c11084c82c00c5107260400e1f9200915611650507803c090069604103044800000102000601042da03240d0703c3d0b014160216400c030540d140003210300d00c603050a60f55a0b40102c0d051800c0201c2408581c10440c01d00d0f50810080c888148280215001000c62010041c1c0310640300d0302090504400030301e510b100b2403040080112036a6205c0c001b8503580c00c146 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 631067751 1250 631066501 631066517
    0x91a04050c091203190504030b0c0403080d05090717010504030e030616140f0a09031203060e0a0c17090a031103070b1b09030304141c08041404020904060303080103020909030408070303 81
    0x40c0c0c0f00340c298840c1c003100c00d403403125408120310145e4100f4014001c591007a08100d21966940d82030000a0241c0d02008044800400030184407035200e80100743c200e11120151a4000d03a1507801c001c0410000010540b00d035110303000c000505800c541480f881d408181c016141601d82a225500c407042c40c6036a4205004202403c2580000a032080d19201e1050076541c50ba02d10001a000d4030610451000316052440c034604045501d00c00e0140e90222140b001a2400d1601c8005100026203400d035014010001c003030340410300008071240d610703000322503000260144d880300c1c0c10000d020403200030341036920303520401550f00021441c000c0749071700070460f060102c001d011528421030603200d03d14120707503d0300c000b280110b05020200a2650313081000c940445c40880740b841e030300d42c10207084203000e01a120144410418103820007807001c07159030010302c01441c080b00580020300b242c5060b0000d900180ca40c3c40188110309101941c1908030914400460425240400c125564580d9000080800030741c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 631069001 1250 631067751 631067779
    0x203030a03020d140c130b0a1d0402090910080d0e1c02010207080105010320030c01090b09060405041802040c050414010f0c050303090a02011d090a02070f0c091a04050c09 75
    0x3a5002e012880c4c0010402c00c0300381402c032040041500000080b000c44000e600c0300240701d1110008807812401d80f6100c1c1101035045000c51840282100000c50308580c080000003000c2d0b0382d04092901c10712007a862401414203045031249040000720290040c0704020345081d0696540c00303119139000d035064000303030540e80c00751004070309103000d9500c454495070070300d0008800c2210303000e2041c1d9450401100c64441a00344800c00da60340c2e9003c4091800700d90b03462800e00800c56088018224000054001d6241950703070b2020a00300c0382201500042c0030b101c1d42c074100451406000d0a040c580b0503291490400341015030004566141c070514a052080c540d0700d411006000308401100150820150b17034680c0f4080d107000c1e44502c07214001724002074203c1c3d000710071860700300d03018125070300041c08010595075a8400d59000b90300c035860582c0c03ea11685868000141484411000780a101102140c0380000c0d60001201010051540740700d0b908100420064070007207401e4aa0003402154441c8258400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 631070251 1250 631069001 631069027
    0xd03050f0c010203040302010b060a1d1203072d12050a0c06092004050c040e0603100c0906083304060302090115201213082d0105040203030a0302 64
    0x400019408100d80896011107035641940914800c50182e0001c0c480c03440a402001414826182c8220108071151700c0c403d0081005048020000c2d0042c2c40d1105540075070f9030359469900056001c964480e01c800503510081082034084415111902c45081a0351403540c03000800403d8007400000c1001c0400c400c7c207030a10841c000400350790001c208200412180c1080030b2569a8444d001c8034151a040c041c5a00382021b100b0a071003a80403071202030802d0b05004411480c64805481d01d5407510815405019a40503881820b0740000c003500c403004214541704001d01002001804aa0940c01140c800421601c4441c2c00420440207103204642000541d0000b40007420a9000a900b0118070000425072008441040035001202e450710201410164146603c10f040760030007101607007190503501310f41062070010b050052044505946e0007501d6010813403902d640000105017140901d03200c10b821505103200d02d05401d0000000780424a82500400e40c0c038400e032803d442c01c0550000f218a07544403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 631071501 1250 631070251 631070257
    0xa1a0717070302160b071b02060a0c03020a0501020d05071e02030a030506010507060e0303070201141005060906040306020d0605130e150c090d061a01020a0507030605070306080a0c0906050d020f0d0305 88
    0x200d100a00082801c00e2140c03004121490008101800a520680e591000c011f80000b40d005040d1450130135284da0469181d00841c000310150302c030f2240348400140e1300303001030310703200030a040700080920b4105801440c02041c0b580300c121003c000013078080400c0d804405c8541300c03650350901007040e172500e4004845521800402404080c5015645081800b02000a601a64503540207020381c0c07128104407101f14206540791134004500c01420022428680c000d4007071030030005e1a480c01d046c8d603511140d041e6400342c141440c40f0341d51400e0511852a003108a5285240c001c04104a509408807a0942e00c1202e80405042c7c0d06e0404000b542c29500c0c0070032183c0e101c40103003001e5062000c1e8580b00007e4210b114019104101080500c06654400515040d100360072200170f0040c18915100d4400070a0301800700303010917448030008508110204149a00c03148100401d18045140510040854070f0a03008180b003154816031440240e41d0f02d10140ca2010022901283c1d0b00c00e079882c007690301d44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 631072751 1250 631071501 631071517
    0x2030711010903050d0207051003141915030515010f03050312040c05040c05121308160f1211120f0d18060c0c060e0607120507200a1a0717070302 64
    0x4031403480c41e82481742d40410350008445041d510140703c52251340302034003075801e0b01804160604a81e000181ea54020344100074240d44c40200025181818030740d46010b0701c001d41c0050b103066008501c24004680c194003058010040c55448ca00381a0a40d641c60fa201c0c1710f01c1c42002c0c030560b044008241400110980103000b018024070801030201c4100001c0c04c80c1c1c0044a103446520301d03c500140352015129441402c440c0c1c04040303e07142c96410b401c0746d0009c508000082e60b00f0303c00c04115000048110001c1024480c46e43c0b182080550340c12600c40c5004800102201054001d0214942030503000060b209000351604011802d0f010030740f09094051114070300940303d0340c00c00e01307503104030741d040100d460703419006070b00c180071800c021040c80360b5848003583ca440004601d11b00255409065a109940140880c0381c207119030064061141c06580c020324070b00030290441c51072101001410309440b205080710f10a84041450040c0d00034001c40c229500d0051000074032800910960710a504640401d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 631074001 1250 631072751 631072753
    0xc03080414160e150a060f090b0a1e020a11132406120c09090b030309180601020d180b0715050108010b040e150c0d110d0c090b0a0203071101090305 65
    0x10b1804481503a4881205200f110140c00d0b0400119603220002d40e144481420058005541145008811a96005002d00341410440582400716844c840400141460103042da03624204170000c21010b52044e1807242400306543c03090403180300040700c10a1424000d50211503154a0a0713006241c0d002411420039114032604440d058120101039244900e0191780403a0b5441040001c4030810303004441c03010520381c021a075043d10800c290302c0d1a8000c0070310000c020f02500e0800c8011000301d80c1c0041221a094090b00f54901000002d584c1000181041d41c52842c1180e00c5030000741c4440203800c6a4002e6490108000079072500b440310382c0d20031048103074404808000e1036a5074092140207010a4030220320560900d0100030400400107003902c4824a030389841030080c0c49d1004d0049881d48052280301656454564040c6070780e4610b80a003403140070401010500070340980d001003412481e600f0103032070f1010038458000405e50010a94101e01e52146500491144c11030060342c4076602c45e070008200b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 631075251 1250 631074001 631074013
    0x71a13081b030a1a0408040506070b04031e0503010b07050a02121f0b032a0612060f2413170a05010b030c030a03030504020402041d091005070c03080414 67
    0xc460014074106407405144148415511030010951114180308000d00401403e4a40005042c0f25842c160b400522400c6041e241507501e8000c1a155040004c05403100b94410b020482890380040c0454176000000c2000301540300c0300c5401400030300041c043da154400020400c0340070411308008130071925400400c16041c0301444441c060b604c002e01000c41e44425030402201c400d0071414000c214141900501600301441e019041c404000e080c07003030a60440d034503040684c9043d101c2c0001010500c03400d40f40c010661034144180005030b1075034000c0c1801903010103003031410040078030804103816014a0311240d490450840c0007010850541044240c0d005164144032031240c0001d0960801d07200d1b0740280009000d480030591261170b01182036400d40c0103404d0700303000244654485940280f0082005041070b40314020110f1095030300d580d08050034580307024000c000c4820409050328030017030341c2c061119241c00d40000303141020450300201406910070100701044a9a900850018480d00c01c03510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 631076501 1250 631075251 631075259
    0x2030408041701020909011509090c050a0908070f030b0405030706060b071b08060105010c05100c0e01080c070f140a05010c0e040b0303031b16120c03120e071a13 71
    0x9415441031060950712810b01c40b001c00070010600a030350207804014081510b82e81791101301035001000380c1c040300820032180b4001c5440c6d42c03203201b0040041d94654905480d1460083d0203031842c100740d0003089a0780e0041d6420440d4144510582c42620350140480c4070350740355882c009141d40103001c0020001420040082508801100640b1602e03000d010803002010b00030142455a2495001d9100c00e5040200103014550103aa82a201c09100d40220707020600d110100c4001c80b03c2038130469002501c840d100800035a440030065400c4542c03100410303e4200d0030780d80e500013440c446d0002802c006815040441040c02404000416500311000b031008040180700140301c9210f0541d035500c6603150815114140c240081a13a01c60200054104042c05010000303505a4000c016420080d14040c000903000503103261600c0d2001d403694883c000c0d00405481d010348803c00700c15103240e04511303200c0f01e20990b00001032031031304864145040c081c2404109200c06d44502c920100c0b404070b540d11900c002 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 631077751 1250 631076501 631076513
    0xe010e0a1d0f060f060904150203180a11030f030a022505090a0e0f03090d23120a12051513020f040f091b0206040b06060d0504030302030610030b0a0b0319020304 71
    0x28801d1989002000050f174031582040484002942c1c0500001c43c283d0017030100720050790040d500480d100c0e08034003400d9010341440e443e03e26404011106422901110002414100420000340c002d41e80550b0810010090007907540803140c2800751800e42100c2d80003031a10356003400c00040c00014108080902d0100f103254094064041c4d80d54081c03140c05c005149a03100070090304c0c0c0c5590001c01d500440340003900c03880800c400c140c10001c0c0c011784c258a614010b81042148811809080d4511a00c2d401018406040310b00c141c009002c0543c1071104000059070701c42121a4038420444442a050090603e0440240502c14008000c0600003401090a10f41c0483c000125001c071001400b80c0f9034100155040140d8605108000da844100454001400060802c0c4d12040140603c0c0c01d00080f800c1e0700b01a0f41c01558150003083d400020701205041c40075001400c480a4281444074002000c081740381310b025803107041405840400414107181414500c018070b800e0480042d03440f81840d0800b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 631079001 1250 631077751 631077763
    0x19050609060105181b0d1b03020307020c0d080405280806070e09070e1c06151a0d091b030b0907030b011404020f0c03040f0905060303070818031c090e010e0a1d0f 71
    0x71f6000009002580b441e24403034003c4a200b00b0080d8041d14001d1244024080700840c947c0d002c64429000380404107043e281c413400e480604a000c0c8400382041040c01742501801d8060300142c003560400700400031116002000b4200004040c1c2d440d50060340c50340000c60318080f509100c50b41c04401006804841080340c80c0280c4e10901a5004011549038440c00030700148843c03180b181c041d5142105c42140d403501d4006004545041000403034442d1695075411100d40391700015040e0003400a6040c41071003041c461442e402080000201031050860b140d280200505209918204003500c00200041e00c4680540b1080f52450703510b961030b107580901d0140c40ea0054012450340e043c070001c002030404554040c1071302504010700a10300d030441c3e607107034036102e035002e000d02001c144c91342034020f003107034400b000591410103c07c0c4010220110344440204403400940c860203108403020014421410070240b020b401c041c0c01c210014070311045002850304041c21030040100c60042c1701d0000d070801000710312 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 631080251 1250 631079001 631079021
    0x30306010f090510030e03040b0d02030f060402120f090109051009033b0402070f0b060a1205060105091312090501080c120411011119050609060105181b0d 68
    0x7405100d0010764401c4070b02550500c034603507101c0d0100034000d4000b4007a5110400000034042070740d19023034030b80c0ca82c40d110f64480171038119940d9000081140c0c54000d64115500641c0486095180180d0300c1060070310480080c2040c42ca46001501080580302c09600034640e840d030100c1910741d400070a44100004181c000703016000b103414809005024500c5140001c1c0c1c0c1800c0f001040b100c0342d1300104a00e5556943e144440c6c110b5030801c5294081512140300c1443c0758030892101c1ca041c40c003901030202045aa510003e070503402490081300044002c64440d054271810350300c4609503985c00350b0702d9110100c0c010000d07001158106020518035800504081039a00c2030300c98415948803100d580d030592003134581c0b505646c3d081001080000b046518000e5180005243c03c46048100146490500c0e840f840c801400c60142c540c284208081408081d40c0100040041c0403698540008240c0400c03c1c0307090b0110f6028814006404110004071568007401c0600389580c07103046880d030400c014520414 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 631081501 1250 631080251 631080257
    0x204141e03011d1618150b0301180b0405061c1109040c0603050c0a090306021806160501050c0c0c091b1303150516030f0b0d1109100608060f060d050903030601 70
    0x1110051808280d080404030f81d21078151310b04d490b4a50200c00c004001170040d5400d40601d0382c00c005061f10058000e540038125111041d035600e1801c01c2400100c800b0b000b038007800b8a041c00200300d81c2da910400003a404522604030b1082040003803503e410300c1c2a070742c0b01c0141e1141d22001032006000d8500c0235501038450b03a86040059441c0e90982030f0043c0201c11074500080d0612000740001034140c0c0141907009802080d80c01012003400c00280d05030080da1854640f07200c4030159030b0501c8002d0045c00c0d0024031020181d8a8024a031900310b485202882880c1e0164291401040d04405828800104030b4110300c0142c1c0c1314200840000300ca0612844140d8408036103d03c02d02c3e200085205050140d604400d0311802c1c07802e000404e8000e170400c10f01c000829030340c50b00380c100d02c0e448455041c1480c41c400c0c0007481c0c403001031400300681c4070009040c1c800039404407a1300703100c1c00e80c00844107600f1a0040f201254405080c4000603c24840c512036030441d02d08080c24000010b400002039401044262 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 631082751 1250 631081501 631081513
    0x210020d021b1209041d0715031505030d080405070f0b07060506011706010f0903080408101b090306091103010c0306030302010b062a240702100204141e03011d 70
    0x31150b15a54000807044070400d40c010000919146060350100321007070080101c602d41700180100180c100301b6290702c03841410030024140320000c0d9041c891881d0f40240f09403146140381c2004046581c9000c42c016070403e10104030049028401d00f0812800113000d8099481c66641d12000004001e0b00001e004a44c2c09051a02043e030660141d042d140340b004d90321824180707999a203030045400348040034a19041c481019000700c003148200340180003412b4074200900c110500b45103e00d0440710501c00c984c480701c83ca1814280d40c680e01859100c100c07608868081500c84c46400c00001d1900302ea000036a041d0700e044002e28055806411002c00c0b20300a4000f0400100c010050144d1403040c0228215401901442c0151101d0043c5070360703000c14280d408580c2413416081140311a0342580a0075140c444450040215195041164011403010b002c429814289054101002d01c801082031a2040040d01120080c4000c0712a02e0b45035018010000d200800300382018030b4100741c0c9100300c1c00b605e0241c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 631084001 1250 631082751 631082797
    0x50703050c0a032024040806060102070803040303140d1a0a17031b0a0503071b05031609021602030d03020715060311060d0605040c0f030509010e030306100210020d02 73
    0x100300003140c1d00301c034580051080b8904d00303050031503d401d0907070f5024110404811401005000c40540c032400c1400140e0f882c0d080120207450858024461411580718035020702c004070700401039404483e07160400e81081e509541c0104c69034061030721024142854410300241450309489038010280c02a02d00740c4495440c4d407001c80395002d00081050b941c1d8820000760907192500e4200000c424030440503a19500e07626070f42c0f036046030700850b07084d10041e04020303503d004469007003c050f0041600714000d0003040300061301284002100e2040d400580d502046520001c07180381c007000360499000b0141c44010360905400f900039040b1881c103036984404284d03080400880d600c03424081d40e801016a0f00000060802c0002950181d20000000358860b9400110317602c460064644400240c2c0b10403000c003150803002405c54000038607251003603051180a1a032001f020003201c1d0004425204402c1030411507070141e02d440c10101060801e94030000b82546101e105d540503009040074148906078000d00c0e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 631085251 1250 631084001 631084009
    0xf060e0705061e120901020714010213030f052418031303080a09030501110304060e2a04060e010902090f0d030f030506180702010504060b18010306020307030e0a050703050c 76
    0x1980200398021400300080c40e0340b0066181c0000882020780c501c1da04d00801c8910200903044240c030500c1c5242e4021803a801040904c0c42c02607900c0010000840c200070580e6001900c00300c0b0341c440036090a10010204052000900600c60451490a5164070007801e2031645040104110b4881000c905c402d400c40c1d0000d1004021100e0314600c5843c601c1c0000c0c290784461090750b11012f4000c3c14001243c82c0000040c07020300480034001d0000c203107103441c0d10f41801c8c518103840300041e15840d0b5410181580001521814003205841d5600407504402c1600c440840c0040450340c001d00040300d140390000500e8401a0014220110180c2d05059201c17103070b106022444c2c40da524001d020440221100210034400da0043da0720181c02021209103040900040c00e03070540c140c400c500144d4650381000300b0301941340602c5009401c1940c80140761000321450510004040c0801042d09400001140e0264400d811546801000c40300b86d41e131f2440e40346002607a03006144000c4803140130740340c490603d03464 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 631086501 1250 631085251 631085263
    0x14280f1803051b0d020a0303121103040203031c020c0102040909050c0a0b040e1e130204060b0f0a0503041a0f041a01050a090b0d150204170c0d0b0a0e03070f060e 71
    0xb41c0a401041004601c601d0094100f00290701c564001552510380300150b41e42000e8580194001c5d201d00c41002845440582500c48940464007503000070018880140c600008039841001c4014241006405038101400640308003468900d103503001080204d480301d1b0b103902c840c400034410003c4a2111a282080c001002824070a05d09481400d12082190308039400416500c842c2400d01c6a1a02060b00c07940064400240d41c00d240e1182d4403034086003103041c5489a10301500050301c500c0e0610118640c0692140b080e00104020000040086020021020110301d00c7c10a0740a10720036070b141c50801d080000b0f8048130155071802a540160a4081a410203541a83d2029210440c240d040c041454060304108090710380101051401a002c03500d208101c0d0350300c1c4540c0300050707a254038004080358a8100c80c01c4c600043c2d0880912070106e5035804458402d081d500000c80a0580d443d42200ca008040100900026000c0000d1420030080c00c000b0f102c2101d84540c00030489072944005140e0340714 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 631087751 1250 631086501 631086503
    0x609052e0b09070503061e0307060504090f062409030215030f0a140c0f07121d01020f15090a060501060f09080f070512011d0a020405060d0314280f1803 67
    0x5482040440c0c81414407001004041032046c491903152040800889e00e40b030501d5200000051010605000710318181c080c484410445c54003e0044a05000081d2030383c00c0504103128581d0310680d0300c1c2d01d00c0d038041c200300401145c0080c003085414803c2c425600781d0382c2c4200c44404881c0880c0e00001c0482c5600e1164401c18818460903003103d6498080380b0b803041e884030070a03500c046401d200034400a010340301c500d0a00030032540e07406245901c164541100b40c00031420641550013503d41809003041c0002c6800c41e18001050007c429201c1c2c5034000d080c11100d103130241015091400100701d82e0780040300188a0b4400382d54205c02d079550394901c1c1382c449101a0700d1088d80d8024010420a600d8028080d03000c0c50f81a2000241140140144800144a035941c1c00800c0d0049050790307003507280a105440c0e2144003a5020307104415aa500201401d44200340d01407848400304407040b60705c0c00c00c03200d031050a00440c0440c0030307030441c40d2010f0700310245181c0c0c800000b000c144454101024030000c82c004c80f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 631089001 1250 631087751 631087757
    0x807090c1710060e180720120f0714031615020412061a0a080f0d020d0207060309060906140609151c11060301031a01060e010c0609052e0b0907 63
    0x440c00d0000449483e900130514590045a801004a0b10a000a03480b8054543c685940300e41a00401030321010510100c110390503500a034207e22090000b003070440300e0403507440c0320150340c482c0c0c9480c0c9280c1420380c0c06078040c0c1074070001c5002c0000e10301c0c0c94111030406d030107001c0d0743e0402c00b004500c4070140e10840c00313004000c3c00320801e050000743c00fa030000301c10404c4010040b810b00d40e0000100780c1c1c14015070300403902c9034811700c22108018800cac03241400078001880038000d0401005c00117903842045220300da00305581c482016092181c10f82c42828125031205003840b0180e00301441c1d40e403034001035030140c0c8603410180116100f00c05a905030704044102401300b2202d04e541d1021703201200701c280e0f02682d41e414031000480d9107035180001940078600c1010010b00380c00c1c0103106404416016000300c401d102c0b0345910302816a0300001040c0b40991b0080300030410030020310384141000405990700300091a80c809079100ea20344045c018600702d4049a041284032004820041400400e494a03008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 631090251 1250 631089001 631089031
    0x151202010f1202181f0c02090403020127052a15070602070b07020f0a05150408090d030207150e0f0402090a1d1008060603060c090a0807090c17 63
    0x154025114584184031030b081c1500e54454084200060340c0c04100d440c4011440e5200300c1c00540742105100b1910281ea0741000e418940c400c1c4058110511070030003130710a40e41c6500090416100350000c0c101c5144c10381c91a40ca41000f1404100024110300382201c05009854203411402c071091444e404d504960552110f4140c0540300744608000000444488043d0401030400400c1e0702d40001e0080354441c2443c2c2a151a04690090400b0101200303140e00360400c18001c8045500000d00c0c40021280200b860705a440d00e03e0b0507080d5128095159403c50100d0b80100e0a044c2c01064800071102495400039141e40f013204101c03483e80b404040e0382d82c410312810f40340c0c0150400c5e502522041c00d0103030000a040da2603c03641e0b106891400d45901c010903031982000011a001c0c00400001c10040d0010070b19800d090300046d85401004105c624207400100b0a5030081c2e50303000300d00c3c00500110050360070050300d0f4054200075010905408020a071440e00764510208580d106900c80e804540e01106 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 631091501 1250 631090251 631090253
    0xc010c020c01081609050907020c0306010e01050111030301030c060f030e19020901090c0c080c0316150b0108090d111204030f05010501050607080f030c210f07020f031614070b04091512 81
    0x46000c000b0f0603403000c52081841c602403644033084224041c0410040c41c0209614010004003a0f2039444610b40d0742d50824001040025200d80484041c0c4800341411241080308510490080c40c200740c101e501c621907000c0100c048030244009a2032140242c03121441d983e00c940c040300a4030030760100c1c6030001da2a000c0c01c5021903000b6002e0207007a101581640d2802e20307540000c0c4110400341e0002d0340c7d12824540c5240760160303648109030400c0c0c803c0c2044900352500807007864071030900c4100c4070203220b068008610700d028140108000c42d00e0210300c140c1c540d9241e06040c0b406982000b0304880c250310700b50011840e8603094007503608050348204140d14104854103080c1c010380014000700e44215081c841a03c080303601b20700703052800a070007100060b83d142030b100e0f0119070380d400340841007550010429800b01a002008032104000002c041078070102aa20f0002455104545400500d0003540400324114645d04014402c455444000b8030078600c02065000180141e881841c5c0d0000035840588 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 631092751 1250 631091501 631091509
    0x120302090d020f040e15090d090513090203010e031602040f110307121803410c07080f0715080c0711040f0603030e100c1112030c010c020c0108160905 66
    0xd02c252501400105140031440e17001441c204101090345001468407040290868003006015107a0406142140c0c0d810301c1c000201c5c6c40e5000302401c01400350f444141c90020341d102500900301400074442202e54807911406e89da002459960800c80c1702d07a003030410b044030300340360750141c604001c0300180c02c980b0f0340e15941c0b015540c940400f9494ac0750143c07603049580c581d1185404110080f8001d45442c0c0c071005040c03054120040d82403510f07850b004400000248402001c0b50b4061102451801699a480e5071603111440c0020f140c2c485603151240d0300441c0c045400124000084035074907048100d5544040c80207a40e0400103c90348002d00805100c180d002c104018051001c039003024000103a00b280107000789058501039081540402c96035035600c0414100422080319080c024500102c50818564440004609440c0a03501c83d3380703494611041000107008581840700854000c0241c80c1203141b0181d200da54145805003c036400c2e0001401d240c0060010210400c5186c1d1031541c81b1741003100b00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 631094001 1250 631092751 631092769
    0x406170603063607050901090c080c160b040c1e120b070c140f0c04060f091109190f0b03090d0305040507090608060a06050a0b03070e060d050f04120302090d02 70
    0x11807100f80b00b9910940c90182d5030021403808048440078000340c500380700500084800607030000200900e0120100c00195200d0b000301e4002101040c0c107581e41002d4482035881311613111010700148181c005010801140b0036050313045605074910075544d22900103082095451511542080c10107200031440055414400e0541c030000303030b090900c000601a00c85101a501e843e03c0c01e00b80d036010310b012509280c410429004203400455050000d14240707551800b90011901c951480161220320300718038411030100343c484c440d00284c101d0f034400b0030080e907564010055105182003106112000300e090205081101d105d4403150008010301a0422012001040b0060069420b0300880c000400d6048090050340e00502d4140000e20160400000d02001c458540e0700461140356088000c01071030398000246d80c1d2080c80c500708050480b240e0f401040140c4034009035200858509030401100700d00341064030380998000d0350707511240010003400b6803c80c0b080c10000b40e44400d040d0004401031a05080f1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 631095251 1250 631094001 631094041
    0x50d020a060507020a0b0a02060901051006020d0819020c07090608240405100c090918030c03270e1911090609040209040f0e0d02070e161107060302040617060306 71
    0x10405c4007681d6060f4004054100c1c050080058220400344100c45200b401040e8018950f450324102c50743c80c101000c3d50b207107610f0300d0007800c3c400301c00006001c03143c003007503e649000003c141c20340d17507090f80f80019070b1501c41c0742c028203803c00d18000003c503c0140000300300c2a6000030501c0e5490f030046545602e1508100180102c0310703440f846010740c0c200304140c01401c12680141d25054411070404051000750b8801c000c401240725662801d00f00441e60180204000c150103007804140942003100300e0b0303842c4040410620b080d002007074001403e4650224040d10514900001e60124030000c43c1110503510401d5984001880a11040050b40303800001090140700080005207004843c2000c90159800309060b9280c842d51681c00d250009018051480000d4452020744019801c0c1260589175807805030004030b24010b07020040b5001c40c060010008085504021910242c2c1c3d83c9034000e002e5400740c091703d0000307040c080da110f80104412120718041d26008010b40890380c0c6655585442c0021403034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 631096501 1250 631095251 631095259
    0x10e0c060c0f100209100e03102a0203070c05040902130c1709010b01090501050f040e1e100611030c0718020f0a030501090b060304120c080421020a050d020a06050702 73
    0xc1020602e0010003070300700740304160716015866404400070404480c00b080440d40c140070501003545515940414403400100c48542c0018491110049130004007040b4256608041c015200c4c3e1050181c0005c05400914450810444000d4441003800203844080360000e402c003020b690145140c503c907801452143c040380ca811100304a80c104e10340e2241405a480c41075696403100b2a6015590086040010b0720080c2400f81c60080302d0f1035440c605100c0c5101e003620058038100481c482c22066141e61460285000410b07038203051065400401c0c2d0f4052180501091448413420201d480100603200b84502d20300c00303000110702d8003180b0035100399a40c954000155080102038001000a805000303003040c6540d0014256050161120807607802c082c04520031070f400c4c000c100009a200300c6040ba0000300340707054084035a03a445c2003c1c1034015604208100800d070b10008c10550182450491143c1c000ca0340350000c540d942c07080c8000b00000d1000030703401803031814013481414081d1008080e4648003034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 631097751 1250 631096501 631096513
    0xb0702090912131715040f050102040b0c10060e280b03030715060b031014010e10020a1a0108070b07031103122e1203091703040e09010e0c060c 63
    0x4288090503601040c1d03102e402107103e00701802a88011301a003c03680d000e400c000d251902c2c05a540312074100000b80002c01c4070700407810440c104403003034041d50300906298a0040d107a0040c04107540d110f07840b21580364074491520800040b5120300213400c5000303002c0c49202040c1c41880c03071041c500e8074400802e40540c6d41d4940b82c290140d41c034200002c102060043c91881c032a1444000c100064a1043c0d1003c075a4407130a2061095800c0c400381442d01712241c0302c00f41c8255804080041e20160880103000c0ea100c1c1b80000926181500881c00503c0d20784030740107082c0a20740c1345414099024082c0200e140e161310030442800201b100200500e0b0490003400c0c82e142d809803010200e40344da480200da100c140001d01d400d110182c0185803401c00c0f250046290340034407000750302c0d02c1c1d080c0445620544820305842c14100c1c041c98020820320001c0e0103100140d03171050404010f920350725403151184020b5070410000080748140180310b201109480500500000f01c410010040f142e000241880d08500940c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 631099001 1250 631097751 631097773
    0x60409110a0902250819031e02251a1b0a09090f181b0902070c08060c13260d080402040e1207021309121d01090b07020909 54
    0x2680041c401030408580169a94400c105030080078101d0344580f80b1104903141803c400658041c3c2610080010540c0611151080d908110003070304015000800380e02d8500c0050100c0780b980d4000b0301200380c8408108035118108552100300210501000e40281110020941107500c0002c1040e04920069a0f6005c420400c019406190f4441d48a001c0032450101c020800500140603c98030603510b02810081584c2c2010403010101c15860001c0c64070780e02e0403000810080781e010b000054502d9607803c540f10545d6151155404505000f90352651003490002051030120501b1500c01c021013800c0c0c400c07200e103070803240310802800d000b11404810804a4000703034004200700916204030b01c1c0c0e40d101050300342401400211100c40512104a40045a40032400804001160541541626031010361200820002c0090854600045c0860800d80344081c002d6030207040350107207406840703209843e480c8840040d51030203420310030420403100a200c02ca02501d440061740d940f00c40c614040c0c0c1c0c2c1540f01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 631100251 1250 631099001 631099009
    0x60812030a0203331c020105031f0b04081506091303050d090b070c14030c0c010809010f020319140f07112506031a03072309010612050906060906040911 67
    0x84c12071a034208070b0150807240510f41040c4883c400d074882c0e20010390100ea603400013446484018041140312403604441c21250600e0320741e45004145030380440ba190380d155490681c8642c562110718100751a4440130440a00e0030201c0e00d0300850030b122280c034004a4556003070700c458100304881c0c541c1941e40d88580022039006040213104000d00d43e181641119549408082d045180e0000c2030594014032001c4409a80001c158540f002c090030035180350b40c1c90408a602401003030031400421400031003400000a106007460b045000f400c1d205104682e0305984200c0680411034000700c030032403484003007548c56000d0072811201d612461305a0b0922031520f0b00c03420155020f114680c00031104c00204001e129810b01c2a0079901d9214007082c0b14194040c40001e640c1e124501500a5281c1c205005820444070f4450380212820040d2001540d0742c0c2d5190090284541c0c400381000d000d08240001c0c0030801e011030751a1141c030b80204264a252100f10030b0000a01e600300c01100e8500c195111003940b03581d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 631101501 1250 631100251 631100311
    0x510052d04110a0f0f0807030b060d02041d090a020d030c1b0608150901080705011404150305180a020907050310050303040801020309071a222403060812030a0203 71
    0x1c0d070042d80d40d82c02200a000f09181c11084084040000030410716004e294041021608072080b0300d0040b65100c10034000684070320034100001d110380d00c00100080e90792509201c646180f42030262041c520fa8400300308a456200e46c0360006e501c00700040e8640002802544c903d003080b40a004034000c0b40849018080350211143c10084c0451070390b2042100ca5000030b840000111b609541030501540f4145c20f05d551101c050007010705001646040045d45414002520020400503070320550101148601400528064415000c001d00c0070001d40c801840004803000c619a000c0c104c090255a9050304031125040680510040c00000900140ca50fa0810107400540503031400141d982c103241d0840c03132810307800307900403066074a038414104150342580043d1243c82c0000e500300700c0071000070341180012880907004a8621085401c041150100c410000c044464080e10108a01525664496691061280c5043c507100040001400c10102600616042003804510b5401c41e04004051800e400c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 631102751 1250 631101501 631101521
    0xf08070f03110a2102161101030207080d0c0e010908190302030c070602031314090a050403020312070c17031909260d060b0a05070b040c0806010b0d0510052d04 70
    0x240c00030b98a402098182104c0700000d001d0540852038600c00404074291040b0340e0201070101c0c9645008008140d00035011600c00d00d034411035141c0d44c3c2c40709604450041481c1085a00058440d4420749004d500603c200825140c40390010044a184200c00000003850510102c085020a1010311601c01c4108250400740000d0340145440301c40c885140072084400350b1003504107502401e8000b0b0300343c0f150740b44103401004410012600d0390701d500f010b92a41c801c1c46034202110030280204409103074840c0d01c1e0581c3c24410500164043c0b901c1c01e00746080d00007610800c005000c0014181c3d0318000c5e90380040315480c450b40c0480d50612416040161b40405141010001c0100064800c01340740d8501ca0340000d0702d0820b01032410421039010092103030140a600401c000c0d00c0c0360102d014003e41d0110140101040c5e41280c00e41e40e1943c000403a90340148001900a03410480494071000f00b85100308140e62026111004218006811a01c2040c901e8040004241d482003030410790b840b1030058003840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 631104001 1250 631102751 631102757
    0x1020d0204050f0607030801050d062a02191e030c05030409060314430923060d06051008030c0703020130050604110c01090b01060f08070f03110a 64
    0x110300d05010300211103d40860980318040070421080002d40000c040c03419220140c4990311318180620b01040104000300711241444100c5c10b181c814000e81c070100e4000100e25900f83e68226118210842a140b0190b00045c5102600300a00208070219107048603c14000e25150a008040e070322800d0465029403c4440d52a0311040e0034002c0c0030046030307083c42c0310201400a0503c10360180c1d0094440586c481e450161440301c054564400d00001e4001000e850040d1003030603810303540c5001070300514040c44014103401d06c0341d03004d41120018000d094491840030f408040e6001540d65040000c00c0028854031100000714000305160600708080d041c01d0b0201d100500c0d81c14150700000d000400c20a00d0601003507030311201c41042044802544031800c58280001c600c030303203903c000617000d071440004811820b003000c030f0a003602500540200113200d00901007005166241c16048603080040200c60020411407004140254400e111301213010300c061800080f180300343d42d11100c82c1d5100b07000386800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 631105251 1250 631104001 631104007
    0x15160c0302030c030706081b190c06050903070b060f0105131403151302011223010f0906210f0b0c1308030a0f050c0703020a030803090111070308042301020d02 70
    0x1103040400c85003d40800c00c800130584a844d00000520200e0000c25808070302d240400c0e80d1a04010b9481560580c001c075101d0080f81e494255402002c14085040c00d40b211130800010070920303203001c800c80340c840c0c3d086020980c941e40d421041c05a40e00b10020725a0405c501045520030280c009180d10024240356001c0c000341c0d440c900b041500d4051090300380100000100e041c82200c1c071000000086007603081c01e01000d2448a003004800500803842c40001d40e44120801c02124003500807564141e070442d0014050b031540f00c140841c00c9030101e01503210110804ac00c800180030751004440121407281020304031510782030790380d1801c142080c0d440c160502d0b0301189054401c2c1c8140c14000241207500011070411130301b810020074003640c40301d0300020f118000409410b00030050240d60060340e005405030081c0fa5580ca44811182d0045400301c3c180c1d403038520103e611103007420441c1c18543e0541c0c0d81c0030050f01e680d2074002040c1405079141e41000c03070074032100c0200e50080c006440c04009250300143c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 631106501 1250 631105251 631105253
    0x607030c060507020c211c092301080103080f0f0409050402010e01030507020c04020c25060f1b080a02010f0903050c0c0a0b030c130b04090b1512010515160c03 70
    0x1042c0c072005085501903410080103141c0980f542d4500740200e100101342d0003144204a034240d810010400c17415000356205074060b52a6036084146a811074016115140c42e8101c850a1941044c1040a102c0d000614800c010008502a000642200d081d0103030f4551818451101030000b6901c40c3c0d02401140b515901040203540c0c104800c125441c1d070130b0070b081c0010b1a204000a4403410020071076440750781c0c0810f43d02d022540410000b819038807940301d110320741c003904004940f8003551407007540d0000344281825800188a0000912a0a200fa0a00c91080443e5507032200e1600802c103030f10308542d41c0b9460700c0c0c200300e60f50042031003c50207034603502d03580c0342086034a038204000d19004074055151008104810074840e42107aa014038441852515801c160700c84004d9040e99920050745104082804103824200da40280d01e03c91007100e403a0401784407580c4140560113120151500e16111000400803801e141c040f40318152110300100d490600e000d80b00d0801001c508505403121300c8040c4041c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 631107751 1250 631106501 631106513
    0x30614010803071109270604060606140a03201303050f150f07020717030d0b040501080a02150d0e070e06060c071a040e040b10060509030a020613050607030c 69
    0xa0142003010003451a102c21510350303244c0100051001400b03540f8550001d03001910300003103a08a81103103014003d503890117421103aa900ca05071025a840e80c548a000148140030740c0003404034100d890107450400314426419002000c0107401440384c1807522a480f140e50105000918910a1019100c0145800d508020340340c00d161180c8040c0f140c2c09000001c001628165041d0303444001c400c450407180d0348906080341001d5090340840201c0380003148103100c0c0100070026041c100d8504808014884c038607010002620401c1c0710b980401c0e0428071580001d410016030150a1440900300e06281c00b100f80c1800080302c11a028144c00c0b50002c2d401400a100b0f074000158101e2412500603051417440420340352144018420980c40d00c024002402c6071118a20a6400034911f840c01d80c219032030641042101e412040300c0c1740c10000d034440c0c40810b8280c012000d890281c50040e0040c031000055901f445540c4e88240c4c9000203c000c60900021a5a0390034000d0950a2007555040c3c1d4490041c6041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 631109001 1250 631107751 631107791
    0x8040801020a03110a090b09120604080705011422061e0606020106080d050427050c07020102060610080106120207060f02121e04020405070309060501260303091518070306 75
    0x701c0c40540300b00504044540d006c000754054403016a1026035982d04040019107501c08100000c55074003403d4104014402010701402c400c03401600207001d8020042c4070f543c20341d00222052441c800015440208515400900c0d00c0c64074070501c40061900501e09954030700c3e8504203885000320380c58071380501001742e0a0050000034042000141449450500c010700540154000e07800d4602e0303138000d0082990550b0008480e0103440d6041040b150800f4107101403294001030090f8058030a020100d00c4506105000102840140d55040d400d40d003019808c0703410700c8982c09a90a1a40c0a0250101190b12442000203003c1c94404c0142e403182a01205030480400400107000c0444000882c1100f100c0c000c07141754416030440c2e00143d40d98980b0001d80c028410303000301030441490000040380c0c84e424401300310000c1801d000000384541403000350698905c070444803c452900004202940c0440445409802030500c6104080090780100b40cac500d44141540f0a6072002d403501000c4e404810003200e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 631110251 1250 631109001 631109021
    0xb01091109060702040b1c03030f0b01020309130e071d1b030408040918081209060109020705030405102c01030b0d0201020d1d04020d05040b0a0b0108071b08040801020a03 75
    0xa030364106000e07100003070202d009a02d400390040d03403228900703c201e0b81d4240301d020203041c94402081a400850070020002c0030102441c5403102e00d08a070001c1558000003c2e600c0d00c0c44010708010410811400d00c1c0c0107400ca4985481d01c40c8541003000c120300c40d51041024080048450141ca1842d120032065801220a4860022540c0800078040811860021a01030f104941d601044114445002c10ba0340019101c02906d01e10001c109508410a6951000d001c0d04509046074a42c3c0d803900c01540c101c0c412802e0084c6682d01c05c200030405400c141044030030f82c01180c00c1c00d001c000d842107100407007202c0100307200401c00300c0ca1403003038641d681500c9403e082c018141d4200803030050950020703650b010300030425018800e00b00c840c14200794130202407100c50703c2c01030000e40d02d5491580a00c0040c0c14150340171503241c031548001034002e9040d48600da1103804160341d0300c0740c2c80e1181a01034500d104403901700d44a04a07001e10860209100324011300050140400040c1c1c0d5a888120040803940b00004c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 631111501 1250 631110251 631110281
    0x240f0a05040807030c0c0e04053016060b12030a17070527060c03040e0618040b0901090f0c032a0b0906040302030f06180d0519050702030a0b0109 64
    0x1081c0004511035400f543c1045071315040c03044543c0d02d130b8101902d0f1945194801040079081e4000c0104214001c1200340c00171841200c21100c1c03120608050245525511a20111200620102c140444021b07926500e0031f0003030000040c02040d01300131031072a0300e0100c0805455840010030206450303210703000d035081240341781d81c40005040c040030040c4140728296071100e691101d07161500c0e04800800411106902c010310300c41c1e8414080344805d480e40c000d4410586c10180d80350004029042101c4035103110025420302c3d0385156250350b940c40c0303104009012000103650340c20b06040040e1240340c1170000e581c01445802c0400345145090455a10b8010814085110644008140c0206070100800b52a05851682c0d1580c8107080411004e0040d580042d41c1485404510070b500b90001c0f4069000d210040189a81c043c0030040c1907a2310314100400380c00141d01004107440340100900c01c02c1e6204490f2512500d810038a8000034502a000e40003516070208400040100c05011f2241c108441d02400c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 631112751 1250 631111501 631111511
    0x7080a1e0c0e1c170304021207031b0602010e0a0b090a0b0406050105090a291c0b070201061d070311070602030a060e0604090201201501080102070515010503100e240f0a 74
    0x50784414022041440c611139484022000c1401c56542d0384e0442e0404a080040b07403c07040e81c9007040e500008030f9049501c003181e10302e50003080c8a40b040c080e807549103031072400070194a0450741e0342c01d0540b140100445514080d041030321000844040805000c0c0c3c0c058400488c0550400b010090040c1c030141c140e900351031030080d4510802c01c04400c02c04202c031501e440b1901c01c06075100841d010010303200585d00441112403280042124400055020b00003e50003088019102d0241d0300c1140607000b000900410030100243e14588640c101d40100031640300e00a090030055641d013400c1c0d03002941c142c8416a280d07001070041c5001940400c1e80004200c0e410b011070720b203540001e4801d90081c01c0340000f20400c4c42120722955001c00052600315003031800c1024640e584c950190013500010021505401096030280704010701071030f000e041e600024041c10401280448144c000d0642c08200d40d007500034943c000d107100d800c0c1e203d00260b200d0f241c1103120701481c1070f0b0140e5000c3c080c0100b00050140c504 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 631114001 1250 631112751 631112753
    0x6030f05010501120b01031803021c08011a0f27040f05012312030c151e0112110901060e0a0b0408030708030411090c120f07080a1e0c0e1c 61
    0x12040500c0031380012000000c03c24540d60040b0081c0c03501082c51410108170b2249103041660000380c1d0810781e0740300700d03003070000a5140d281221813800a00c00c0c0d1807050f200440301c200c801101c80c01050f481c05441d08652420b00090526075000d0740045020440c004800458903090401c0d00482c5503440801408014660510b5102d80f40c45241d2540c1c18000444d10411540d9a101d91034a007155000c3c140c102d80c0c50f1140384002e1540da0b4001c6800c04c482c040d00c800415152038151030b1075171000200450300c60980c1e00300100b030221501014015540c8030002090502592100400c00d8040e1920f80d441031243d2206c80180540c1c18966032200448140401040188910109c1600e0300c03e40d01c040016520344507810032034006010304240c1944903020a05200300d807880b000040540d011317000540d44440da40c2c18011f20201d06d0032070310b020216481400180351407141e544aa2203044c0300c42e4810310b03007030052103502d02101c05100c10035000c15440840d200051801700940c41d1065980d0002504403041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 631115107 1106 631114001 631114007
    0x190e090d0c020d032114090c03190b0601140424020318063a0b030d020325050a050a2d080f0c0f0706030f05010501 51
    0x6603645110564021194040d60540040420440c69050b0b10241d6408a0041d41c400c800504160b00d00e1000009201c1c440e4490600c81100030140703841c6494500c4c00034065290b5100b9800045c0f18030a1004411012030350070741c0b1601014140c3c03205801610707103012002c021002c049022901140c1c40d2500c3c03910410028071820021a41c28198500380d0302c9219180900d03200d80596105500e0504104000308503070301500c00a800000e0005c80d5001101d4240c10403090112000070540e4103600c42d50191081c440f401314054203090070310704406035480c455000c01c030b641c024904012160b2568281824005907401505644e41d5607014644907455606644045401040104800c010041600766014001c1d8020307002000501c150380b5036038003542040d0712400409404001100c0c426805022181c1050040e100800f6914200382028003a1401241c8412141d441c110041003981e074 = true := by decide +kernel

theorem cover : BRFrame.Cov 630935251 631115107 := by
  have h0 := BRFrame.cov_init 630935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 630935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 630935251 ≤ n) (h2 : n < 631115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
