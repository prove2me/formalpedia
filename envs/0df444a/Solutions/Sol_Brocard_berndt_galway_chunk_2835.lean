-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2835
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:53:10.440258+00:00
-- url     : https://prove2.me/submissions/c7900aec-34ee-47fa-8d19-e0c9d67363ca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 509712230 ≤ n < 509892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 509713480 1250 509712230 509712233
    0xd140c06181503040b041e02150403020f15030a0903110102180a0b270d020909061b0909060d0201090e130303050a0c1d120111130803041d0604060b03040609 69
    0x8007581c1541d0580000c941503081a0380c8017a0b5070500600014005000d4030034007184c041e0a0420301400940040902000c0300b14006503242c654810700080c0e00680b00c1c004010140d0501c4c5081e0303d81308483d004003e14503a14240c00c03070000d2200400c103c042004040207a200a032003400903081c41e1103121101c4505000000400107942002e900c01810f8420034014001c40d07141d5050400f040c1c440208a01010910200c0000e820b8400200c000794444100e2007440081d200c0042c510348038118403140004907a40050800d5186d004000c002540b01ca20b800014010741480d44800d400c1c184181400e034000d5032a400f490100000895500986101d04c0070030006150345802007a421241007041003210011000c00209103c1448103042e0000e00041d140b50000d84038050030100c0e050741c3e60001c1000d50380e46c03110314025034003981041d910000d201601080801005c4100c0e005c440860785115101c0c8110f420803500010001c011542c001e81d81d840c00200301040070002d51107070b031041000090a03e0306 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 509714730 1250 509713480 509713489
    0x91109060705011b020d0504030b13050109150c02031204020d081603050309011d0a02090601120c030905070f0b1b19140615060f0705010e010e0d0306090b0d140c0618 73
    0x8011303064115401901e0b28800c00760803104541c2900e03007080404000d45d8071581b0b55503044e41d482c480100990700e00f030400018045034000e1426281c8240c0702c20301413244a1a02241d40340202d0640c10341d44040c42001c20010329002d00000a401d1150080e2402e0185411640441444180054007c03a80001c200400440280720300100b405031412084000e02e40c03646c13803d0b5605e80780303200240200724075030100300c81d40e003e50000c50180b50015002c1c072007415000e83c010060006164202c0d0640b0503404045007044440c1010740541f41c4c0b4051490501d03080b0345401e00e4694540040c585d0f64050704c10314005250301c141503a03605034000c40364180100040d04039580b4120b4010640d8444000780201030982d0b90721031080341c0c55003a880718896100c5034142482401001448000300a940c64000040c2240c0d101186c0303260445002c0d00c04014850307660000c0c80654250010b40c83c0d214140b950044000707494950305d0441181c8880c212645007030f40d00c007c02c00d01c0c5e1004805014a4600c1d40562565152 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 509715980 1250 509714730 509714771
    0xa0f181e0f0e040c03030e040b031c0809070e13030c0b070801180b10030c11150403021e0c0112020d05040602090a1d040f140303010b03010e13030909110906070501 72
    0x303120002c00d51482d03d91600110a5030600008040100010102c44140c3c3d458100f40c21040340102510743c0301c054010355a5000002c82141d002040840001601100e80440c5841c129030320100b06134400d541d07041001e2145129240100c05020b40c1e080b1540204400700305661284d1019150040d4075410000003940b41106403801e0443c090800344001c0941c0c8902410110301401c40c24007040b003882076441070f80c031000b4404100c1924030079099105240c01038170350401d0042e4043c1e000c1d28a02e105440c100c2c2c21685001942c078540e0b91224800141d82d5104003034141158040d81c0c0c0050070000110804811b40300280c80c2a01c60781e8020881244134030b01558290010213810041ca08090582c07900310205500044c030142040007159211818002400c140010789500402a6580c0350384900f88101ca98000307005444051080200040030301d184012403039000f41d01a160300b21028642501c07400a1725684149508400741070004450300e49500d00076044451082e4000328001600c511090907144 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 509717230 1250 509715980 509715989
    0x2102041e0e0d1b03030e0f0f03090127050f010e0904060906050c030708010e10080105090a050d09260f06010e0a061401050d0504060e10320a0c022b0905060a0f181e0f 73
    0x41c1100d4a014403330b010062842101c1c03043d00c80b280b500c0604001a03800f500d80c4c410302c5070401240000c1204002c6260300c0300c4a541e1040208100c1a10703070541c1190745010858804c408507a900c0e006100007022500401e500c4161f038849000125140c8d2129402c1d208140c85540345980804403840c01c01c04103001c198407060907460412461450861844c3c00507286121000f07114090703807511980c52000340f040034042c4603200b00301d5910f561344004100d06400222102601980b0b400c5010520030a17603040020080d4050b035030203051000c81300410b4000c0c400600120b4846a442451008410b414081c08803501e241100014907443c84400340321900c0381429400e0782a0780007210343c4c1100c0700b04000e82074100400000018020355041d005900e0311140c0203510740303040c11603207017140c001100b100d8440d02e9111030368412031216524400c2c00104d00942d201280030402503040404100c7c4908600b440310711020721a0b0f0411941e41c0d00784074000c81d6542d181c000d03003800800103022a03000084860000c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 509718480 1250 509717230 509717267
    0x1d030607050919080102040303020a0c050406181d011107030201051503190f1a01241e03090c0b03070809072102041e0e0d1b03030e0f0f030901 63
    0x1803400610040c0184644000c180c40340008101e40f07810035501c414240c0141141c80c008550340c5440b0b06029641d0302180d01c0482d0700307a00350600072a07142081c1c000c040445201502d2001107018551035007025210b0f10003601003003022a1444101401d007405069240710300c0c0c08206591b0445030500900b034410050140e070021141d0f00041225440020310704aa80d80d141c04d89000f03080c05841d208020600d85803001d81503a40c4440c9842110480500e460f048410510a5814541c610320700c0c2d110300c0ca9070f02c00d104045500311000b4410707907015014424800c156850001858545962010700e4107407941c00640e03c4d2100401001a05900541042d800000c031300f0041081d80d140c24070701905080b0031810740080c405000334580c215221030f0031140d054140700461801081c414100c05000300f400304022041d41c403a20304240280c90207665503410390300c0d01c10800c3c000c10000d51420b6000d050b41c00400102c501c0b50b41158040c02c1400d1044011154807440555501c910003400148003801300200456007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 509719730 1250 509718480 509718493
    0x80a0c0806033307030501170604050c01030b0604080303010b0a110601081009031707031a0103021312020f090f04170405030a03030b01090918061a0904200d031d03 72
    0x2940c2c0000c0c0c40c501c14990707001444101c18122400050b2404028030040c1034100100900c03680c03541540046040e00d80100105000c4101040c20b02d41d030703120656011300305401030172501d801c0394070039040304040b441e01401080c80c00d607a8901451550b07000f40c0c4500400d40d0040b800c040880e501c180041c030300492800044c8101e5041001003500c03822030b21443c0300000da8503407450781014092603000030301c0ea990081e051920b1424640c043c0140c112059100742840b4140040300d440d600a01c20740b20805070104140c085c4e541004003007440700e111000309036800320746100000960765424940500c40c0802201c0c0080e5400e0034a41411100f1900e002030001e540103010a02c516100060f42c41e41080c0c00d0320f0b01040580d08480140c5030003801e0781007610582e00f40050510f01e10b200440d4480268802c640c00c1040d0120780d030182d043c42c4c3e4490481d60f07000344080c001c43c0108403907007c050440d40350701402901000d0075000041d0720492014045001c9940c0c60210084001740c2d038101444400d0690141c2107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 509720980 1250 509719730 509719741
    0x31a0d0f060605180c0a0e0904150c0f02120c0f0304120b010504020a080a05150a090c0210051b0d0f1508060a0b03060a180b01260a0804090c0519080a0c08 68
    0x40304d00d001480e10842400100d81d40c1c080502c40d807a4000019009840c008113030a0030308003c0160740d600200d500c2d0890500c4e180103851803141008076030483d5141d001c1c0000308404250700b5200c3d0710071900d66040d44982007011b84850320a100420080400c40714204078a07400d031500c2c12826005a020a20a510501958488980181c2116070001d4140000180b9030703201c00c100200f03040c100000b50b0304034084400201d050041e65129030345403200303a003c0313540104100b07554030285c81c000c07183d0420641c0580455610010103a0140001c0300c1d15840c049800380600c02180d0072591803515082e2880a865000c100882040c0700319a00422071450501c20204a100070965a2001410f8052819500e000e40c1c151026180140b00301181d2202403c101c03940c1d50581c015400e811590326520443d40718080b291a0440007512070303c4140d0280700141054581406540100a1500407100780300040050f8942003903d041e40300c13045c1d0241d4032004035504120080340215031030003c5c6c000c1400701d40f07401d012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 509722230 1250 509720980 509721019
    0xc0102071e05060702120109051b0910090c020f16060f02150f06010903050a05060105040c050301151404150f09090b060f0a1b0b070e04050f07031a0d0f060605 70
    0xd0b030780143c45080d40c80b1054800718010308501554840c26511b4080c0072002c0150202d02d5800074401c45170950303514255101000520001610501030500ea100410003040c0203540000d005c982180c01030382c02c8030400107440ca0500c244402e9851020070003000c2889007642100e8041e41c03203140c41c4020283c0204011a0324500500038000300300200841e40040c00780d0384940e0401015503448002e80d01c5091003032400e85e58440d428050148118140301c080510544100c007034904036602203ca662001501290686400010410301a13950904000100f44c00034001c8141d0b400c4005591003c50350b0845040091440746036800c0010801d04140c05400075540c0c090a440c400082d42000607541c903070030300003515600c02d2134505900c05005081801c05201100c2201c40c4526250340303d9051030703c0c0c48410002100c1d01128a17040c100d2403000400d650b1407003075100b056840880c519906150303254400040d0300c1ca0440030f04640c40000068640100b1400e801820700410003583c03e84905140b030391480707 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 509723480 1250 509722230 509722289
    0x13020a1409130602041505120a0e0607030b01020703081612020708030901051c05010f0e0703020a05070b060d0c180b060f03060d06020702130e0c0f031e0f0106080c010207 75
    0x48a240602c0409501445100c0e4100c400411813507002000140c2c0c03942d0f000d0f0a90300b12046400304016030700000341080095004040c0d0b0a80c1541c0a40308a59134810180c0062038980c0b00c0c1d50447c0b0a001000c000031307209000800b90051100141d00c0140c00c24900144902c4007401c0400071504060340800c410400041030b140d10305d609003800b68880054280500000c0c1c10582041c25890504000103800040da40c03003001030b503038005d00c0640c090392038100aa0a0388200b11400300000e0302007240750302080002d03d000d40c00010051041c40400e4954440041130f42032a0013010001540c044217150300c0182d449003012111082d6102c03401c00c15030346440d400b9030000400b0701f80104810141b60041129550440701003d50042c603400c0401c0c48a00e144e402031218015040d264401e600c1c000e082450004583c0d161a040100140720301caa900305d03020340f00403202d41c1803802403249030350304569918280a042c0190080074003c12203810300700002464450250321490206880303c040c1810171599000c01e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 509724730 1250 509723480 509723491
    0x210c0e01030f020c0307080c2514120d02010516080c07030f26070807050c0606040b0d150b0109050603010303080105010f050f030f0609091b09040804080613020a1409 73
    0x604044503042c800007034402c480b0342500e01d02000440f0010460610041c0207000301d440d044450f00c2001c54924281d48151803c030641c2400a08820004810a03e02065a884010f000c0c140c011007100745031460440c4942d6144003607511002045a1f21412456003040b0302c0139071410031064140800c0301c2d0b409100b508409410000410761000c826401030010002010f0300c10143e50b02c200d83d0044211031001c0c141c1d0b010000684201c04112458410300950354002c0c1540040c1800d51148001c0000074185001099003285030885480041411400c6c4010040940c40c03010076004000000140780f455260011841202c4c20b1005101290780446200d042d1365080c02c1000201c014188103542ea030041203040744031640008100280001c1040c00d01e4010f0b0383c00d80d001c1c0400c0e110000d020b038448040c0c100320305010900d449000d0310703072800100d0355801a0140c1c00840c41c0a840f0040c081c00c00c101201d82040180005203c581141001801c41d0000d103690542c0c000300e181c50768001088044081c08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 509725980 1250 509724730 509724737
    0x3090e063114010b040f050901081005060321030a0f05100e0411060415080105010504300b070804170a0903080d110a0906030e160308130e0403210c0e01 67
    0x280d000e05009194000740268002820b0b2012542e5141100ba002d58494007858400e800c0c1c2600008603800c1614101d416640403d025214502e003191040c0000e07d0002e10560303041c8150120130304030f0100303681c030703190b140b1480400c955492508a110400340c51036031128030602c502e40317001c20007449440d50445003907424021455500303231a10705090065200510101e6070100d000140002c100c0e4518820081e4140306807202c2c4034076a0703240d0055505004901c141030250002205060400c000100001003500d00c0303414a003003860703464550300c0340380404136080c0b4041650321080c8010710505001c104213504040c1c041e64500502402d00900100f00d512008100c172802245c204441d2005400c60a4043c0561044c9519621030403002840340c8554031616007c87d15010a1001218003c1064241e18084400c41c2414520759560860298001c0804168036600d0503804200b04000c070381c0150195009a4802801005820080b154081000500900b01385003009810582d500040801c01110003400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 509727230 1250 509725980 509726059
    0x10e010e040b040606050405190b010c03080c1b121e0903070302220e01060614040b0306060304050a0506040821092107051e0f0d08010308090112050403090e06 70
    0x21303200700076020a030051903005081400b00b00c900034101d40006e0b604000c0b01c20620101103600015900c103040104046c00103008074000801850b0444011311503000d1107540202103c0c0c0d0000d00c5800e0070074000c6051242400090000e1408413819800701c03107140050949480d101c0e0035070000e541d405440c403000740650b0214150522288581c50410f41446881000b0310440b1484910103008011900030500411200c4100340108000c142c195019220050501c40c655114401004800c2d00000c004940611801030b10600007402801740fa40510322800c0304a03199003c020307144010500207030b03010f143c401c50442017100d100301c000346410031454043d00c8180204030010181055225030240a000e07803052150700d525104582114a8008084030141c41c010381240c030080e5150308241e03e1640002d8442ca0041c80840d01010041c42ca182e0141402c904417131003259030314191401102c050340440d001b00000c2003a5440000042e42c0700b142207446141790035107000ba0700c400d0510103544100c0082d104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 509728480 1250 509727230 509727233
    0x3041a09120d0c05040909060c0f0f0e0f0d020a031406060f22021603090503060f0403081501030906050a0c1101050705040b1b030304121106010b090d051c17010e010e040b04 76
    0x40741105c01600ca01d81c02032140d0000c600f008000390040311440740018064074261f0700c106118001101d0681056a644844105170104001040707002801490384024450310000040c6e6850064071f000314441d40d44041c2e031a80c40625282030902c0200141e0240502d480f80006983d200108a40c140c49000d01c5030302d225a25840f104002d000d1000c0992441599007081414542c2210a150880302d00703e0844016079104c8074001c0304080c00365002170102e03411a0100f0030340c80e504801d0824102042c0b60000d66409980ca803001900d034190342600c00031b030392036030fa000400e0740c01a007003400b1000783d200900031070900040041c5188a60b2142104844001c6800f004203181410b400c05641001c408407512820035080014200007003000d600d000c14a4802e0030904c111004c6800c80c101c8070103035502801c0a240c0400e0000c807810010b400c941d5809801700c84101c28594600c1141c005040f50748420310524200080341c103a0f4010380006c80030344030003801044110705608542e640140c2c410310009240d1982d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 509729730 1250 509728480 509728487
    0x4150218060409020c06011e0302060304030e210c01020703120309020d02030105041a1006050403060209030102090a181409030403080f1201090b0405150d110d020603041a09120d0c 79
    0x26411580d07208000040005920000e40c014001c100720420595443d640c3c2e40344480b0b01c1c154039100d200d000d145000b070100050b18107130f006140d000d40a401d000c2d107000c05400c0040c6140140700c10700c0580b42c82145506400c1f80381040200c485540a0000740170300f9003503860b052412072560f2016020107803680082411508e80c68081c1204d103034060000e100301c0c00d007458000c440c8014044003080715003003500092003004041c0d08175400c64005450b510302d13040c11915070101a502008034190150b40802110030a91121030f207240c0140308500c0e40100e690600c0e1003c41c01d803424250b006030780d058140300740070341e02a012080b10110b0b070b07101c0002c907540c1604181d000b0382409003000280e1034845403000010a450190003809021070b048a040004e650303021030942403110980031541d004664206044000781000c000f440351180020549802c2c80000c0d80050203e0380111411510100d0b02c0c420600c0c15220413002a8000b0b04d00c038040e012940d20300440000034082c42d581508190384440746103010030301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 509730980 1250 509729730 509729767
    0x3210216051219150b060403081e09030a0605010315021e0c0f06090601060906090608070c02060415020c0a06020718151205010e06010f0b0d05060a0806090f0d020303041502 76
    0x10503c1c0b043c440080ca4200099412001300d051a8101d00f090101d060300c0c0340040464068035801300071242406080900000c124039503d4a1282c861402c00100e40300756001c100ca065068450003005c50b442d03045181404000031014400040c4900510200014a4028042c140004406401107880c1c0040c046c041d8507016254100154601800c03090001558000c070300c0a060710380356206c1c072607100e564810032907140b200e07032185500051400e0042005036220310044142240002c02980c1071076140d050303082d00e0100b440c0c2c16501503405a1103410140c1001c0c007200006100340d00103000c046142200702191a5814002c2404103980c40d80c2800700d03000c0c54140040038214810b00a02e0205013031400d00c0c024407224102845a2040070000207a0100c0c000031a800d58200550450801050001e120085c0030090180f5a201d44c04140104c2c0045042289520500c1c00000908003080c01c1400075050030410344941c4110f40082080102041c000c000c1500c0801d020a00141d441500c4004e00c1d41243d07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 509732230 1250 509730980 509731003
    0x6020d0203160e0102030a090501050c100501090207020a050f01020304030b310b18070504090c080d0305010e0f09030a0f021c020d120917091306032102160512 70
    0x80c404020300420340c580790076080103580e00380c842d540e41080c40401641e481c06610002000155190010320a552007130028044061181089510021008602006941d03090300302041d03903a404100701043d4036200049500801080d201c04043c8020200000e441e44600d000c054103000301003000c40c0503005445040050100c600c041c80070140882240c000c105a14110261075507280000421000d07031080c0c0c5c02690140d03a210090004074504401c0c40090700c60a03d0a0b1402c012044d00013030f80e240144400550341060344c0c0c00003429030400c220149507050151507841e400260108000f1181400800c80c6e844884034100350900c2030f441c010891800001414241e0b000714105140302040f5000640383d5526011a150003a0012000301024104c0c1d00c501800742ca60010104845c152a00c540000c00c0c65402c09403031078621400c0090f41e9030070f4071010703441292043c908203c01516007003c81101d4112201c03d102600d124a0700080d01244107105000f020b115005031200d80200d00010000030050701c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 509733480 1250 509732230 509732257
    0x1d0a08070f0c180b121c05040315060f0f030c030204110903030d1b1d06030406110406020f060c0304080d050601050d090b0f010f030302070b09060d0e06061003020f040306090602 78
    0x68450030150300e2800c200403c106032600f0301c1e807022501d113012032400c128034000000802c41d00305900b022600784906004900103100d810040400810440d0419824810703545401281c0c180c540480c1c012807003a40d601400d59243c07034200a00c0028900c41a103811a5011035011030400c000b49400c0181d846000003080d81880009440c180d84040d45d0072400704d00c02c0440e442032405c26090000e489401400c40c09202440041441c00142c0c54040051500640508000940d01030901003e000551150b041100503030700c1100c00300c254031001c00200b54004c00e00c0d00010b0840c2070581d65084075000d1000900e030465151000201c0503403060302581d200012000e000d1101c9100c4d401c1c400780b17803c001e880c0318100c2c140e808004145129041d407000c0031640e066000380000c074503009849230a0303000010350b030380e000d2010404414881c0c0c850007041c01d50314905020f4002414104100001c170380c0b100003a401814014000741409800d442d096400316900000041a501072500d443c00081c8256508140032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 509734730 1250 509733480 509733503
    0x10603350c010b010e040c09050d140d051e09100509010c0813050a0801060b0304030f0221030f0f04020321040b070809010906050304020d12051b101d0a08070f 70
    0x2201c8054210740101042a00c13840703036143c860b00510054030600000c2e0320224030040030801881c2004000c100b803050241c54500c180c0b000c0e04024234200080e01842400003080400d0708034054500c0b03004010140c500601162034001a400499810300d0950003403000e00c6008911028503902585500c0d400340ea201d09583c1d600c6108050040481130f03180220360168000c82d20115520b0014810391080d900400302e03003402c50f501c80da0100c50002000c0c400000718020400c0e9100604400c1c0d4074501d0200d000f22000352240381040440100750401030091100c52920410700025171404074884071503101c100428000c0103440e80c100c001620a50380704035515100096204140003411000e46020402680c80c84c4010b90707114030445407404243c0d806980800d501090a002a0340c07081e0b80d6601003020b00b00b1504007a0700d00e001303200113110401060031030380241102e40300c64010ba2280400e0b0802e81032a040b20300c89a40c07400b80d45c80c101410b0040036250700007060750501044030490583c4d1796128812040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 509735980 1250 509734730 509734747
    0x3030c02130e07080f03090a0e1909030f120b0109090c0201021b070e07210b01140307021006210b060f0a03050f010609090f030e01030b060a020105100801060335 71
    0x560301c3c100d203c3c01c03906024020303c0165480d004012140d03c1e0200170a050590303402c3c41d124090312a0054032840c0140308401e075814000d901ca016080003107004e521140b810000d010800351044d2884905144141e1502c0740c1110310f6a003142d440b00680f014440c00185445041c1000d81c024400c0780031a4030030700001d00050802d0743c0b000901c1800d80e01c1d007100d1300c0010b03120000140e0b0042100040720404010100b110518070026521591016205240002080e0303181e01e074481c81e0340c2c4251002c00040e0810038241c40035580030f008100007803400321070035801c5801c1000701d401c02240610008003214004004188940c3e108d140030f25003608000d064182c03075980da20b00309556102c83c01a14806508000300000c0050142c450700095941044d9444c4804240790b40858503c481c2c4a0300ba414180da41c449251103032102c5000e070041c4e40c0990000120740c141110005100c0c002c60f0303c001d40f16070400c007061000402101141103152900c2c5196034a210405d91042ca16001c01803920202010101d00500e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 509737230 1250 509735980 509735983
    0xa050409050d0f1b1103010f020a1b0309051c051515010309020d0503030c030a060b0708070312060e0109020c011107030e101209080a23091306051503010501020f03120103030c02130e 80
    0x4504460440003000001062309184060340a500440030100c4c151800c00d001c49015885803168491091418400042d152400682d03441c10300919280c0004107030303032202b040020421000132a11100319840c500d5151501442c48c2181340c04a8603030415451b41c2c0c4110454075041c0116442c503500c1800da13a1203203000c0c500e08013140c108071403180506007445400609a40050101d8800701d030091129460045603032010b840c03c11541c07501c3d4010513500c000002d071450084103a640a00119140583e4035101c0e2031100b8250380c401d007201585403000701702d20000250420f0101c25051400d540380c0d031000c0500203041d2221460030007a40a41030030a00d15000b0800c2410040c05032104581364110440c002000740020080f038164481c0c191401000707124484d2526003805c04211413128000b059881d164008150728201004201d03900c80000720040c4030542c0c05000c140e0f11448000011070822803c04c0a062a030031040c84050284060348030144150b40340d5401140c920756124506000089800d40d185 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 509738480 1250 509737230 509737253
    0x16060c05032502070509191104060f050f0405190305060f010e070c0213020d06210210081005060711030f061b31081b0a050409050d0f1b 60
    0x2441c0041000b900c440580c0d600080080034980e66006041080c100801e00180c500050f18150400c00c82c000d0301c40f00d110180c01509049245a9011a1542e1600c9001740503800b0024816050107800d0020780300d98241002503400300e480c2103e4a40d5905040c2d00440c200210f65003001d0020b000350010404500f00101541d4102c0341c41204001c05591141c404440c031811601000b544082111920a07024840790086c01104000d01000140e440e65461256840103090b038501403210319290244003549481c44c0580e401103880c2c02c0070910303450024030040d00383e40c55000d0a031281c2804a034040c20300011100d8894851006401c03103281000909405035210011210070040520020000300c40102807802c2c0c40c4070300e6160101600d50002c00260031200f01e4554081c0d50181c0c03c200001800d000200400001c00b441a444400750441c65400d220700702e4a15000315008500703151018000600c005141da2503640039241460403140c010000319040510ba80509040c840300715500414855032140c0f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 509739730 1250 509738480 509738491
    0x9060f0608060d110a0608160306030f02100e1009080f0c060403060213050405010b0304060506010f020d0e060d05180601050d0804180603060c0933210204090c18140616060c0503 78
    0xa401c238a0030b29080460a03104503001c0208165951564440141000c030300010300400b050809c4c4074001146008508544010001f010000d81603800400421605002c0f40024203c1d000180c10007054540108d84584242d1000800780c66001400c4071400c4802c403402e50150800402c18080c6507551035a00015401c03d1302e056070f0442c600004118107601509034840c07981e0194002d44402005110203441078800313a18a290001010029010b0407846441090310440c40000e00326040011840c4c090f06c0c010058104a00498030b940742840890350700e105840440e0f081440c240c1d50b0041c13040d144005806180d1000306114285507004045c4d40c0c010510205480c1e40c00b40d1507a00c0d0000050010301c44001e0b003d00e540c3c80091030f000b203000c188a1140800f680900d9908441d280600114601c00c03a0300c550301c4100d2123075903800a03050382580706d9581e04410b000d000b5101041c60074011070070b00801e00c0b2014a841580d000810746090100811040780310380c0c12010400184141c5440544160707c1102e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 509740980 1250 509739730 509739751
    0x30a05040e0a050f0112230a140c09160c02120c030c0105070b15120d0e01140316110709060e060a08060f01030305070f1b09060f0608060d110a0608 65
    0xe0b121101441101c1c4101440d800d0391005911301148240d18108400c800e079024140d0300e00040c0c40314200d400f401210342c003c8005181030541410b00720103500d40d00e083c1240642000704910016541c4007140c0e600b1541d0a058104100c0d940441920b2441c007080e00290850300030006440311480c04500340c40561429019240364000300001180c492080c1c1d040104420400004980104a00c808000d0680c1c806400200180140809a0314207020300d4a00c0001400d130310b50007403140d6400300ca00c003200000c80003851305504000c002d01006245080c0408208a024028210912030400c501e03030003002030300010040c031512043d40c0324048800700e03411030180120100009646c00c1c000b801d41e1003039554a4035141544d0030340c0da003104c05521001050700e504a181c1010000318207030080a11041019100320081180b501c43c2610aa8000782d201c9108203045032000c0103483c0c0c0003401164001000c41d080c085c00c81880c0303444188024900000342c1c012070f00030000b007000c92704141c040780600860003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 509742230 1250 509740980 509741009
    0x40b070f020111120a0b1809010f091511190e040b060702240f041401020d0306050f060d090c180e030403031b020a0b2208010e030304030c050f030a0504 67
    0x441a420f90391403000f180c880b4141003000b40345014807a41c0140d000310400402040800d42c050000d94021500c4080b0b250010700b110611048400900c0362420300211060180121007507501c03500c03e0f60116a0307048401039180c0000203078804010040307a450b5043e101c081d0080640400d002055004e8840e18280034a1030068840c440b854000190b0f540140d000b45214500741469454012400a5140c9401904028800d2007650700c4024060000b078900c00d10705030740311000840024a041c0e84540d000c1c040c545040c0c414040307500d5210802c003860009881d910b9540c03c90703803905001010744075006489030040305404500c190224000340740501040d4014000d0f544000080ca480c0c0c0704e107110040c0814003031444000080400360311415007900051140c0d00d100e913504030603407090340100903c20040c00203145800240341e4042100001e002d60f100200309554031820500d98034031010380068140100481508104035041207043c10510710982981d4541038a444058030341e421a0003007000f5034000c5c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 509743480 1250 509742230 509742257
    0x270d0c140307120f030608030a050a0f030e06060607050319020a05060c0c070e0903130b04090e03090a0302010503101e060f1707030c0203041d0114011103120604090209040b07 77
    0x281c550560300303e030a036030740e040c40503c00790b416005400380f9009154480714001006d007030600162601340d019445542d91050722840c024180c2a44c400540d06151418810403480100000d02a41c401c1c400c0d12219070740c00c041c1c1021b80ca5030180141c01000e10100321243d281040d070105908103224482c004590040e290300b10305003498001c0d6410176000b0b50064000f0042d44c450390307140c030f50000d2001c0c05881c5429141d885d40e80168896802902400e48001020840340c06039104803890a00e07940c010318104201a0002003000001d0b2001904102002c8003259100c059581194010102c40301071000301050303105032a5014070103100b5400410b10064400c038080c0c0c01201a01944aa81c444a2496595051068008000240c0c464085210900012403058103481c80100403920b00190007038103601d0321141401030116080f078a8104012071000d800070140010035541c40744107000c841c0c0e48561341c000108000304041d8001a40c0304d401078041c8024840e5120015006020543d914206945c46 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 509744730 1250 509743480 509743483
    0xf060313061b05030411061b0105060907020304080c060307050c0703030e010315241806020c030d031104090e1c36170c04020708040e07080609270d0c14 67
    0x300340c800810f00410006000401001341400100402032026081c141d03910a004042a5030b11260b0f80030b6035640e000d029081c60260111a448900b6100951600782012003882c0c4445550880034090400880495801d9000e401a12040e843c60805c845110b6900e0900170660425040060301103880c00307032400d00403158000000e095a02049054040c82c580c400ea48420400069121003081049241d402d4440c51141e00c500c01081c0541c010310381c901c007100805090007132180c01102454078214020168a400100741c2d4102d420b8150b0008220340b40c4a403680c10a00d141d605500e00c2c1842800301c031895508a600a01c0007440604503001221842c0322542c040e268641c1c001c13000c070201a10401106240d0072442201c00800e40a440d85000100c011138242e07041110222880b000c0814280a18200c0300d035601d600c1117487c980b078625414801d01013183d1078000f03811406009a102c00b403011020041e41c4415110300c0440458907001c414050042c0080401030044600d014070b18000640c5050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 509745980 1250 509744730 509744771
    0x7030c060315030807050f030a09080f1b0d060f290306091f020409050f07020d0314010911090a030809130e10090314030406020301060906020307030c060b0f06031306 73
    0x80c0d07002d60b5086141192184000c0c0d82007a942201c041c428007003810480d4209101401000e01c158540200c49030400213414100550060040e03400d521601e200100c8414911240440b000195110412034940b414004040c3c4048601e5080e49410a001ca400345035020205052003107010036a403850f1f054540070942c07149001d86042c8600d41c0800d440d400b82e80e0380f01000c54034031031700309100501d040d5403083c0c1c5205840b01242d07411000e181e02c40403c400746070140142d0700c0181c820314041000300e004000118880d8418020500c465a840b4030100302204001c00719949400002d09001c640381c0d0b41d18101d101c0d9844886600e008202c40e0300c4c00403030901d050203002a00c200c40409402c0204501007100d0003050086800d9042040b4542039040d029860303801140107600880c40903035650306200c40540814455800b01c821503104000b604046030340807590f0480c0c207601c1500865070280080010f004940c0303100c9c01d20b40c48030b000001e001590541000380380000d1f10a48040c007600895030421409a40b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 509747230 1250 509745980 509746001
    0xf0308070527100c0f0209070e15091c0308010b2a0703050c120a0605091525301b120b1005120907241d0d080306040b03030c07030c0603 60
    0x1004403018801032811100c0395034000700e01d189c040710440c0a90300041070345c0b82e180341c8003020160000f0003106900b0b14045280e007a800d00420060502415540240b04003014403500e40043ca0110f1003d8813541002a200c0c0c2c04100c5a40700f400030014148200e888000a10007128688585100407505081c00c03013540c0700300d0308424090a08084103494480180c8801080b8402710301812442501840307447e5040e9004e4450b04a11520700e4414940f000d2a61940542440c24000070242103030100c204282c940c0c003e6445a00d2100146011000d1080500b041070f5484901c83c1c020700c025183d0952001c2031804400e200750082c0705003110380081c000f801e0101c1050fa80024000c00112100701d403e951441d41002c4598102c072801a038558007400c0c900c04400d00e417448041b40e500b55424a0340c2c03080c581492042004640e64107044d1140000d4000c48944a00810308200880001c50a60380e13a80404c040320070240c2540e65800ca00d1035035070f84807807440c00700f198030100051000c5015032080c4581440361 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 509748480 1250 509747230 509747243
    0x602030a0e0402070c151b0b1f09050c21060303040b131e090b040b060313050f0a030c0b07020d02070918020a030b09010e0a0f0308070527100c 63
    0x40c0d099400c458800c824a481d5070040d4081200c1c500203440303a40454010300c0d0072010f504103141007002c000c007050302150200c2d88510b04641c240000c40e040030001038001501d840380541000f840000724030782c0f44003544040041854030003086541241140149400c401000c030f031041c040d07101030150048500550781144c065005210902c034600803007000f0480d481c0d02d6100180321503070b20306004010307882104140300511450f2000b0080407490340a0403010760400c07641030050400070000b117655030200800d120004413000448506000f014000350560070f6904068030a01415420044c12226410380102c3e480240c160000d03298a00c082072801c20240103902500d5010301d00060980a03000400c0c505000060b0b0503414001643c1d80d0101c3d034021445940440e246180c42c40b2802e003100c817000c0700e03101c1680107804e200340010210906020344507490304007002240c03078201007202d40e0700420700305240035008100d088800e841610038800c4d2500c0c041728050194600d698cc1200c5e24105d84e08020203c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 509749730 1250 509748480 509748487
    0xb011401020a05071502030705120414040504020906061305061b060919030f0e0402070f05120901050910030615021c14030a0c030209041e0c090518041533060203 71
    0x94800b100744170303084504288101c906000b0701e511114104020b400c410306042000090030003006200c0c54100f00700c900c00b03c070300b0400740c5000e40204115200c014078040c480d20000030581700b020400305141c809403402030032882d2180c09a0b10000c1450241c0d5071030441d02c1c850310000800c50b8030000b03003410900504d4050300000c0b058555041d5800354416080d14240060701920715480d803141d1014085aa0103030880854881c400d04026090000da07004180f0001c104006070501e07070743c0bca021158410020384d102000c01460071002c800500f90354210f21002044a454810f400741d00041c181907018820400051014203614140c1c0d044d4032840500d01356a005100003640c01115a0080103440c6090a01514251600002a044500b401c2843e8545924058010203104141c4900b060081c040e0070600d04481c02c0000042030041000344d9009012005000101040ba00e9141e0340c8000c1d540d003a041c8904d94200c0152180d403c030414202500344c501400d5115481c00135000c0c40100c2d40560091482c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 509750980 1250 509749730 509749739
    0x201020f0403080702191a090f180609010608060307170a0501020a111006060c0201030507020109141509030307350c070203010c080f0a09170a0206011e15030b0409050a0b011401020a0507 82
    0x1842d410140408c0e07070040200740c1c2c945203030b1036080004242d02100c030080481483e000041000c5604107801c600d041154a0041046035100016800d003584e52280d12524821550000c10380303000e240c400010080c1d4008a081113007150000c80019180480d0000c0c2c4001d2100e4030101003c64480c0c2c4205030005102818400141d4040d40c0300c0303608030b00d603840042480117550300c504a816440400c40c1303045500079020355081e103440c02c500307035040324105001d940b031070038a030f000200030062007000551203000e0041071101c4060000101524251248203c104074500034030203426075008180164000d5081c4130a00c0710f4140f01d5986103106040028500300c40780c540380041d2004281a0a0884201c80890708804118101c58054a04400f2640c018000c960424200c1c0d80030240d410310050642d40d4030041404288080d984603000c48501d8600000d51944c04000100034040c00000a400c5006108501c814441c00e45221070580320007a040c1c05030810700c2c03c012641c42d0080d110141c21600074500500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 509752230 1250 509750980 509751029
    0x1a130c0e0411070605040b150409050d052109160b07240f0509030417060405032710030c02010b180115020a02060d09020a1a12070201020f040308070219 67
    0x30440200c08441403d11140740c1c1d074901201c9040da415903201c1c00d04d900308800242e8400031401e09070300603241400480516502c4640d1a90284412002c2c004007040c2503030914500102204030318608003030341c482d07820f02c00c2074581c0f240b000602495040089020104089009034221207843d64002121000b81c2c010411141c200d07041841c07400340c4103496480100d404070060185034043c00001c000f5595861510440c80b80c07040d94450070302e080d034124800b00720110700d0201c03e440c981000161090744462015007020350559001c90055031285c030004002005a5040d40f00303000c2401079030001c20528030b40c0020054220024603120310841d0000005110301c2c1e402502c6001e203292030b80102e811920380d80e130002d9103541100720141e215640d1584800305600c0c003004210024512900010601c030b040c8485200603110341c001c0c0c01c07001c810301804240403601c03d604494040401c0c80205032074a0b00c0e882c041f00d0f2a071250f0707000c3e4414101066207a101c4144101000c0440303000c1a03030b05680803095403425 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 509753480 1250 509752230 509752241
    0x140108070e0a0801020d0519180303050405070b030702010207230a1103010f02030c0d110304030e0d020109051509030f0706020304030f1106070804170a050d050c010f1a130c0e04 78
    0x1c0d005a100b200000f040c0d002400908401c880212003c5400e1400000703009003d00b9400f500e0100d14201100384284d107201007075920215405103408a50b99a07a802c10a1800c0000e40c440e0411000000400c107007958107501a1035000c0c41880e0152440d04112001c1031520f802c0f844240044c0c11427081c640001d40c0905900345e9410025001080c08189904054100d820481e8000c607095000941c001070104140706001020255078021811800c180c0c80c010445c4405002542c01082d0007181c5006581c0560340e010b00408009040d060b091000c58008800760f0800c0a4450080c8298600491a0000801c0d41c6040d5140d550081d0304080c91601c42440d03000e4150703030a0f201200d1070b64901109445050041c481c21780540d43c45959203141007070b100c0c82c28109001c1c881145d0406680c0a0000f0070203d1610b41540e094030300980c40f8075142500500404100d4810380b0101d15010001d103065042f005080c036010004c42c1c542089507800401541501c4202e41d041d00040d40d140c2c42d0740102d16007640503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 509754730 1250 509753480 509753507
    0x70f030c0210020a0f120908040e040614040615050604031703061306030b2413022a061005090f01050904082104021c080d0b030a120503010801050114010807 69
    0x1100c0740d1240b070b200510200d0380100e101900040e522040c80442c5900002c10380301c1140c9900c410095852144c071502403502070350083c41c2400e801703000072030240000c58200d007852014903200e0260a09040c0340000c0105400082800a294210000104c51808205440440f90040e80103252130002030203900040d4402000b1540c4840c0860b80460b000e0b08a2080c1d5000c5e41c0f0a016a0006080084100f449501424400c0740100d98400c1c40740781e80d44581440340d400111020000da120030050001406d4948a20000d20700c0c011030740c102d40c10340840000e41e40c0c041c0c0300303108505002070b07241c4042c40064182200c43c0c2c03603c1c500e0200100440c1c141417640f1a40240140c00b000c1c00c084280180982001c070070a892101e0040600500056250124400310203081d4220308503e100c05560300c6041c54007403800c80c60803082c2e8581290166460500003000d00d81d900103503443c000004040003415a030001e0058401662030032001084000e42e550f00103440000c16114120305540c0d8040031900414200c18 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 509755980 1250 509754730 509754733
    0x20f0d021c06060b07050a03020c0604031a09010b0d060902090c2802070e160305060604050a0603050a06090c05030a050a050f04020906130608030705010b06040e0106050d09020d0b0a0b030105070f030c02 89
    0x3c000420014400242115a00c9000500001c12003810002c5c0360205048540b40f00750820031003040042e0103594030102a000c0352021824564078216841d00400c0085d42c1c5d141c0011013030124104204840e805404694402c44004c8465203a0030408a680e002d0440c00c40c0b035603450f0500568420000741056908010300e48100c60360103880307103900a03045109903040c1500c0140641503085842e05802001d50110068569504041c905000120500014031840062542d1000421600e240c10b8001030050b003480c410a0056038142000240640d10458024004a141c0408218403141c58040c03d030090001d111078456a44550b000c1100c0000302412059019a001462854184060003024018080500034603154582c50801e039003910110205640300306c508010070f00c0442c00701001581950310518201d6141c91a4001113002010300e00d4000c0d5100d40328105000412180b800d5591203121400d5052048001100900d4282c44050300d00c900410840341100c01124401e900c41c22205401c0e10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 509757230 1250 509755980 509755991
    0x120708071e141c050301060e060c160e01060809070e0a0e07080106051003020c03030109090305120c1b03090307051012050f0402030708150109020d0207120804020f0d021c06 76
    0x200403507405100c600c000c41da01c4140d90700703006031420184202c00915070030462036100b0f50040318008111307102c14001ca800740085580d003030503070b030322050161340280f2804030881d007843e1030229a03514181c1003032040a0f0840ca03980002318541e481807070001d02503082c00d40100606400c141d204200d220000b4007003412107517100c0a000038410708101c510024108070000099541c03d14003404250745046403040b0616004100c40003a25000108a03411920f5090000a80440603d0101d03182d00c07504c001e0341d5003041200c2c18080841c4e144002440d02c0703207805002e00c061f440310a48031b40e12401404561981134224a0301000b075410714401c003000d0710307101d403a2260081d42d00d00d83c64022a80155034000c3c0300c030035039810041141810814240034003516002001240d0025047c0c040654050260038440d0344c0128a200f85074019030140c610040d03002c5c40480000b03400410040200c0030446e4268450303101400c2e05451410000d1001d040107402a101c01000220729501d011421090344084824aa446 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 509758480 1250 509757230 509757263
    0x10030626010e0706050a26040c0f06020c03070509040201050f18010e10050901030504170a021c0c050601180f051f0e101a090d080a1e08040b181c080912070807 70
    0x1e9200345c0c40354500927071441c140115016000d400350401029544040340c40348481c0d0307001070a8030403243d01321002003c5a0ba1480100d503640a0782020140982c804030325101c0311000e1080001a090080e80c0e00032142454008010161503901104000300c0c1040105050b00d51003904403591043c042c01000f003458403140a03a00301507100300b4103100181c10065000400f1683ca040142201c4070320b290920644a030758568646808061203001280100000e80d02d1145081e40c01000300e01d030340c06000b000a841c100084500400400c001160004102000490740b400005009801680800c000151240c00e1400f103a20441c400720000c071500005000c1d176045a5586d0088020141c800c2900d540c49950106000d0321b410781c5a80115030420f01048034800c801c3c7d01030050750344181c009259400380c5d00c034441110301d0306025a14010680c043d6020301420781002104001c54802c0942d44d4820301e40e282c01a240e103808140740200041d5408008900100305404094003805019410700c20803400704 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 509759730 1250 509758480 509758547
    0x3040f090b040b030d02030406030b09040804060818030a0e030d030e03090105090d021201390e010e040e0d1715010c14100f1406030c10030626010e0706050a 69
    0x10745c0b0410010780c00040e01303004055141c0609607008406071440411814541c0d00e0010700e008078043d03c810407034420b00007014009081006c2d400080380500b62a0340c0c003001e000c02018803421707408060003403040e0054100454400d00c550f00441111101950034120b2030001103a05500001c020350f8071411032000031000d07175144210400e80114210000a03101c0e00700c0242240c06880a42c24006a28603450030310201840600307158400742545010a03501da0142c0040e035403581c420090a1b049450801a02d44450707000071403481800441d01c400c0540d400e40310302143c110741e088551109000000100641550041c281704250921440f45a41c042054103003440c036041012121401d4180c9070b5214041000c841c2c8509084021010045c0301140b50900211b030381d0360641c00003980034549131000c032010b0501c2640079002900400d1066600ca001c400c10031440c40c2c05c0300c81c1c002242c0d40f03045103250180d030000401104a41c01c60300d07003d0401000d120169070700c00d846060345004858882612100e00038 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 509760980 1250 509759730 509759743
    0x5060d030c06331a07030c0215040e0405060612070f18060b0c03031504060b0a120204090e06041b030f060903090b0706020a09150507022407051e03040f090b040b03 72
    0x3800e0800b002e9403811300407503014407105540e50a01d13a001c000c80800b0940c85412000300c55015980c4481120f00a00d20003078500c074903401100400a0ba00511040040128645010701c5040b50200e160441d805407003507e8022078402c070080b2901c948010011820200e4034140c151102d00e5001a5039603407180c451800341d01100026010740c0002082201c09400180c002c012400107503010410709041c000044142d03c00d02103100c00303006200e02c11600c41420342d01128098034101600740100a00510350315540c00003601c0441c0c2c2100002c0115510f00408641f540803032390400c00455003017801342c48000081c41410030940400c009104085540840715000742000da100320401039a030451124010911202e640180203014481144804110303800030984449980480e022844002c0d810f4110340c4d200b401041e485a108400f10f06074007804008601c10340280d100b0180018000202c61091340c59105500034941e5048203420180041c1c61a42c0c4848914107000d0000034007082010006841c164 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 509762230 1250 509760980 509761061
    0x30f081303030f110706080f040507080f07090b04110415050705011b030c030c090b0901020f0d3504080304020117040b150406030206040902070f0c0909030305060d030c06 75
    0x20b0840c030302c100b030169115000452013100384001c0c10700c40b4204140100250406455140b891503400d003c9410311009001500041c020801120841c0c6403041720103880c0e0f0b40510543c100c01c3d2070100f15a1b030a041500482e200100c05c90081840e0a090101c1982c0c204da0031410b0408010040c0b004c5000140c0074411102e420380f643c1040e00701c0c0003045000400340e03003a00300810304042c1002040d090031908500c50000b9031b100c0001701503c0342c140800407031500d65044540502da125941c03058001c44d4210700081e0b0140c84170b030380c1a036600103c030308031281d400c070459408210000781000281c00b250502014641051051504d200520410f1346038004102060f40c0c180c8400c032540041c07100c1035078507000c480c0f042c90050b2401c1c000b0b2403550700041c085000b18418440129000a102e900f00718100c5c000080c2c5961201001900c10b4650800c000100300c030500440100c0d203044082021481d16a03000ca01681d8960b0f1100c40c408800d55588028000060309801c00c04050544071280030342d8080d80d4201c02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 509763480 1250 509762230 509762237
    0x3030a0b0f0303070f12051c02030a0605030609030a1812030e010e0109081207050102131e0b18041e1e0c0503060102030d0506030304030212030c010501060e0a030f08130303 76
    0x5155003401c2105100041140c54400d80c41040b07100005140c11714002d0f2169000448028a6440a041540d5a00c80d80c1d201c0390f580e8078103d5001d130340007581d0385c0514014002c10600b004240d0b211400d065803008280c4002003903900c14400d6010b454800c2a98101c03103481820f151030440c0c0d442003908813a1440042c1200807641030182d02e03000e03591010340f03820818000d2034840001450249021b444404880c402d240182000400d41c041c010250129007041120b202c141c4821580c4224010454041c03600e074440c09614858002101c030684010780c9c061342e0610300d1220001c08014108402000030910301060065000328046110120380314024201007a510b45010040d5010015421543c0c044072400c18044107005200d80da0364004292503114244650020355a1611030010f461402944c0c030003903000d074070070f003200c020501e0100103000d081e904440203000301c0e40c8032001590140c1d03100004642000704cc80080011401d0071030310000c2d450180c0c503814580403034a010780382140c806400c2175011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 509764730 1250 509763480 509763491
    0x3152304210f030e010c092303121902010209060a110c090a270b0412030e030d23091b06090415150318020907051303030f0f0203040b0306010c030c0503030a 69
    0x400c0c3c0601400380d890034001c0c0200441c4130000c3e0042c20050150103030b921400589508070348058500e81008107481002012a000401d00c61031040465008481e01c1410100f8000030741480c900500a68802e840300604250510b114904d0860b01c2004004810507188111201e0a035180c40b5041074900903201404082401c0744d00c181c4100110381103a44800380d071400d420409010400b0807001c0390304207910031610182c41c5d00c040021800382101c01e0504440f8000020710400001c80d9502c80340355a41c81503030703c01000d800700c003404480c040e003100c081105402c40040018111540803281d102d042000b0500303402c010310034000c00c04071590881c000e8299041044248004800d42e24015101850380c9800e104031862502c1689511103072a0001b4010711041010940c00340c040c0064036114082d0601c0d284c10b06540e410000c100c2c00d080026500814085c4000c1c20f5182d202000711000d07216015041071450300c410740110b0b02c155402009608101d010702c100d2001030b1092005500407502c40130007007803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 509765980 1250 509764730 509764757
    0x1030b34030c170f09210a0306060e090412020f03130807080d1b0201170a0c0f090830040f03050105060a03051b060903160315230421 59
    0x22501040c40700e00030701c000d40c00c0b041600f002001034980d00c00c0ca041e181001c1c3da1038801c22689092001c9140c04109901450304010340140f01e8060648a0701d1a6004d21405503906000e0b5500c58200300c55a400c44a80c2c000039000c42c1d03149a0760031480800e841102c0c614002d464901d42507400c001d40ea03c4480c08074900c1000390740c408114071006003030413030042d14180340c00e018058030b410b440340b00015908007078402d28029a0b0058207580d81c514901d240307248840ca00314000c2c1c0d0007080d92480700c00100d81307c0070a4440075071050b40e0b2802a6542d820040400d10702c14007881e405924100c0e8401402d800f60202c2560ba41a4180500020001d8840f000c2c01d150031490000d00f500c0d8028000c070b0041250740006c02c0840c00024540c0c03144a0320005000421402c1c07004a500b91046880c2543c142c82031004080c083349003c030310b003000c50780103d840c51001507000b040542652041d0207010341e0b82444043c083c0e8544144051590014450300c00a00d6260440b0300d000e048049040001000c9140f0700520319 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 509767230 1250 509765980 509765987
    0x10504150503340f03060f090b0301110c15060d0c060c0c0e070f0807270305121801181d0a1b02120d0b031501060f051201030b34 57
    0x544800c6600c4004010304510b040f00e6403084484443d410070415079a9407101203c1c06039100501810403100b04030410f039190f000c3d0402600306209007501a62a20044e410321800e07a009031604541c481000d071400010026417065a20000f0b041d80303a20594580c00d1f0343c0092204a084d0f00117000d951a0700e50701e41c0407401c21014100c1c10354007840c4500c2210741001142d5510000103400150319090801e12340d00d80303100845c0c80b80e07141c0a0001c0061b00390883c01e114440320a4424045078400d0003110466400200d4080c0680210420310901c4d4400c210740b40f00070345c059060302000e005880c4070085100e81c0c44114903591304100040711815461541480f0402c040f501503e0001041011010304500c0e0001d0025503da00740040b0514951000c150041103955607000000503200060455964101d1006c80f07080c006002e11a030030110342840c02500550340a2070643d0303c41104129500c40907865a150b040c80907100030130a4451015103081c225201c403100890000708414401d42e822100e00e4041d025 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 509768480 1250 509767230 509767261
    0x216060c08090705090c0a1b1b050d23150c030105010f080702060c130f15020606192105010509070f050d150e0a0506091f02030606030a0902010504150503 68
    0x2007043e080804107100d00c0c1c68240c105608051080702c40c5a0303440d02010115203402c1810800d44240317005414407000d0207403603218603115040020074880595074800c200b00c2d04c54000c040041091205061062941200d50260340b000000c03e001e48450f03060b1250410094a4221225100d8070800f10040c0301d0395074041c084c0d413900e49aa0411f1001410917000c06035907000020724126240d00001a111500d80d03101b401d29000f0100c50815400c1280c031030035001104280300d4192001441580c0000fa65407a14504030051049880000010305013411842d01d00440a010403419a4447c0e10301d030350000d082441503130700c60301c0044050600d20f41002e01c181031204043e440a841000f05401e450003007454007144440000f024440012070b880341c844103904105840c0c0010327005005483c104042da01001c034282e40107808907841d0f001000c7e4548443d104a0006440d850b400c0b038001c0c000107000491036840400c0482c0141010b90401d42c1d00c0554900151070b484915002075408400d000d219011011403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 509769730 1250 509768480 509768491
    0x7210b101a070206090d03020f0a06021905070c0e040609080301090209040b06090a12020a0b340c052206060c0302101a01180e0106050304050d020a0c0b07060216060c08 74
    0x1c035407810701103800281560080b90f1816200320b002d010724174101802045840c0c00583c00c1c000f969640469810408000d4000103980c1c0442242d900c01e03c0c032aa4400e40442d098640d01494030661a810710804c0300f03840000500440d103942e92440c0c0c280214a442018500a01d00b4003000340c0e403810500288400d030b450120029019003000d1200345070658034001402d007a203030001c1c60300c40c001740c041c000110035008540c440c00f102c05000414068000c030180c0c1c03041e00040b02c07980d001c0c210426284060b20303149150b60098820051084207011600d402c1c0c4607a00d00f28011030007585102142001e0004842d503651100300403590361000d0341300701a018840b01d00c101d8502c00080105480c50313401080304c4440c501e101070400c10180002555212481b540c0c0700a0032052100b0441c640e1076030409005035000b07944c191512b103e1600308461952000562101055012211201c0070b0f14150048140e42c103d110101c0b4810703003d000709026807491322161007959000307840210388401040400303084031401828 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 509770980 1250 509769730 509769779
    0xd08010b031504021902030903070e0103020117090c0301140621030306040c0c060504030309030905060a122c071e1a030402040603330e07210b10 64
    0x4110100c088400d40380c1c071915100c141c810a00380b22000034000e00c40c8104069540010884a01129a00101500ca020030a41c210b40f1002d44401c40e459500ca0f0911000703001444095600e8840001280c966800c0400402210b100c0201b140009081d2034800000e03006c0c00e4048420010f20b890010071a40c03800310311204071038044403540307021500c07440000c00745030180e44c1740c01030f00510512401900c41d00341c1e00b0890400c4507007031500e401005070581d840b0541c0000c80c800d202045514269007198620b40b01c03a04c50001d941448c0b08440f015107140c04090755820202c45407481c110305c1110100c400c500e01c01014006280c10001c1c003d468005281c140d21080a43e46400c1c041654500050201c60b6603c0d02c0082d1030782c2e00c030300c0090003a02098000a050750551040c0580e0000c4c0c8022215400741003440302d04101400440120854101d0710807000c8a50124004120110f00c00c0300c0007640c5009458a0b61248a464580b560300302419221840038140418040285464075518000c00f10034058 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 509772230 1250 509770980 509770997
    0x5060a030c03060905030714010218100804020405100f08010b1507050703110d0c0803091807020d121104120c0f050f010e030a060f020c0c03010b011704061e0605030d 73
    0x11211100074015000c000c0c2031690701e4810009004003003041d030340050740c000c450101900d55040114003030740211400e840d10003c0807481c411145094414586202025524182c42d036840350204409000c014042d42030b40c00c40d50102191480d8801d2055002c3c140c070400101d000710280040c442080010713a60204014001c0c032070b510011380007240341c00843c1d400c4050000405640000a001c0c1840248014003816805e00c001564070340100161008500803070300c140805107036040700440040308a03281001070f040005681100750182001c00507803201c902c1300050001c9070842640c182d91003904468045a801d007240c0040020704903180c400f4040003007500710039a2505000c6040443c4100b4094180b022083c180c581a840030401080544d8000d0000c5c80048801c3c090000203602001e42c03410b0501503507085e28034a00b414010b809030501d06a444d0050020b03001d00d507050b0410040c0c400c460f4186c0b2001c400c0e03601a200510031203506142e000003c0c400f45024205880c00c001c0030b46000034405000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 509773480 1250 509772230 509772233
    0x512091504080703080c160608160801030506070f1101020d0b03060a0905100b0f0312090f18040b060a0e01061823120c090c030604110c031602010e12060a05060a03 72
    0x860841c086030345c00024a40c60700d03070410f00c03070303042100441c02082c1c880c1ca12900000c1d010780c4482894094254a0902100c101409004607004c000c2400041d245a0158000c50000303403140202c091100102e18018201c1110034000c83c1c2a80d000025030002135490b401c20383e20514061040c65005200c605d020010385d03d4542c1c1c0d080d00e840080c06400445d903643e4000c641c00b5210f4001c000320002004050b02d400007618050401103401800010b4002d8064402114407420b003405c01d0701da1035500f01d4485002d0350b55030b43d40c200c041e20001c013035980182c0400e41c00030343c043e46a00d00a0290800340c6401d17002e00760030200c000d064030305075019030712243c40f110160386440b07205604041442c8042c0c4034580350102ea43c0180e481e01c40903c0e80107030000c80c10010031403025001009903010700c00445062059528071004180030b07000e09240312405170410800000348100c03445015040500c1070500c070b5004040c100011300110700c1500151f25a8100c0420060211914465a54415001c450368101d55046 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 509774730 1250 509773480 509773483
    0xe15031609050709081501180b28050909030307170f041112030d05190e12030a060b070f050705010f0e0103020d020c060c0a030c08070e04020a030603051209150408 72
    0x903108503001c0307682d1200810f01c0d0601c1142054040c3c0403020803181070441d594048020582c0911030040c42002500d003e6400304028055084c034400c0c018000c0350008640d00445040054184500710468070a00300011161030385061240300b811302401654591a1043c406040d01c02010801004d04644104101c1ca0105460f01503401a401c8001490034848900206440d81000044900c0354407000c550341410103e80e030421441041c40400b0380702e1325202441c078681503c4803007040030440d41001c0200741d81c01c99900c0155138080b85400303010a0715aa141541d408640c816131041d1070310001c0950804c188041080322800800003860505002404014010310440100c81045d04060300010500030840b4142c040c2c0d1000d103020300903070b00e40342064040e28036168011012440401d0900a402032414011002c1034401e03506521940032401d069410840294069001c20050503a66080440031a8003001071604030000200c24594075121142081100b0040d03a0010400b900104010302c1810b40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 509775980 1250 509774730 509774773
    0x1d0403020706052b0f020d0c020712030e22020d09030809070b04050d260703120203160507020316090501080c03192d03020610080d1e03020d060e1503 66
    0x400700c200c00c11500700303a50b0501a05d201c00b0084221030010450b0450a806a0b02c5220400000d800310307010960740b040d26400f41001510050302180b11710f29110580e0618102d00d0354112580f000814000c2c9602c01c100007241c00c596065644981d50b019408101900b12600030340002002d03000340003892078440013441c01e20842c01110700441c215298841081529060311000da000100d02c0f405450b040c07440d02d01e480d0806a419000a6100c041101c0c3c1c2a4403442201c0c0608204c5c02c2e10341e49507401c820b05071400c1c0d100c580e00b03e80500c610540106002118100c06001e015144001b154035403600c480c0710314000344104c0c1c0e54400e411045500b00102c0e04418000c07116036101d031101c19203024190b00580103210500b60710603001e03502e46003c1c0c10554045100b900c9000280d41c4012525142c00341e113651400c0c1c45112102040d030310074401040c000700d41040301d90342d425480c02500d004242e003000c0c0144c13a039030b5001c1200090f245c0b0070b100d550000c12480d000c003508203034000d1075401a86c00790310f1820038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 509777230 1250 509775980 509776027
    0x80d0c02010e1c090906090507080c040305060103020607021302030a0504150c0c0f14030a17101d0a0b03030c010e250b030705121501030b030c01090e101d040302070605 74
    0xa0103075281d80c1080380a421380c07900501e40e210013084065513401681c405890112901c100103001040001e45004504040c3c40650b42c128009110680c00e6600b88001a841910103981c4091000550b030304000050005511034000c0d040086400d091903e0315880340e1961144c3c2e9003030700d420b08141803100d65020311800361441d000703085a012031603142845034009078402550201800001605490241c00040c10495507035800c10300300156035120a56204810240200d140c0020362031110603424100c0c651140d000b104030540007401e00014000245164004c921382d80059460768050345840d80306102c00b0038242080340c00c50304640103408000398681400d0042c41d000705800b10201c1c2e08148035000b619000c03445a070094845050004100e105803611716002030000742030961a0455041c04a80d0f0301500c401a140c082d850760800b55840e4841c54014800e8981846140001585000c10100244520692881c1400074203041c10000d040c41120703044001030080070002c10129240402082a082 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 509778480 1250 509777230 509777263
    0xa1202031c050f030c0d140f0906010605040e070234140307230301050c0c0d09080d0c0609170705060106020105010b19031508010f06050102160e0c0c0a080d0c02010e 73
    0x17035442e00890344c0b160140c41d809848582c074004c060051100300100f020301503554200e03030850039a205e02a11b5520502401a4800614144410401d1100b800701440d00024240141c6443d08004510404110650303c01c0c40c40310b400825590080e0150203a00c900176040312010b005011840002083d0b4a0000340b2800860a0304041c20303001406080c01c0000409000800a0000341050066000960080c0700b8070340e1140105030080c04824011381520007211594000342100c241440d0082d1000c1c50000740664606885141280001d28021009899017841038455600da107043e0030300703924000050f0000c5080d0782c5003000502c465090b50b4191803585800345c0d030005600540000460252074460502d2011000c0c0110104901c3c5040d0414100032144060401940d0b503107a00481e56030501c682c040313102d81c0480070300344001c07142101000e03844403129201c0751805400705041e6141c013440d03400c291012000401c4c0d4034074040d0303640295840600340f03100034172003240304600103500c5952211003001036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 509779730 1250 509778480 509778487
    0xf01050d0302120301060c02040c0507020a03080f09060f0703020f1b060f0f031e0907030f020f06070f03050904151d07020f010e030316031808030a0b0a1202031c050f 73
    0x10148200540e100c050110000113450396540c0070040d180300f00d0003100f00e03c50790810900c280c06d9807007401691318070340e002845031f0303030f401c1c5152039502050744030082d041c00c802410003040f1400c1d169030005151720551040d00982e105141c0c24000c1c08c0c041c0814032448a80c015102c100c1f42c0145d00d400c150070500e41141e1207556503801c0d2844403c248a85400c1c4941e001010080080040e0001c2c685120a465189407107000d42d1440350181e2030300c03036030b01004152181c144003d0700942002c100500200c076003d0b042c80d01d01590340c2c80d040c10211a07401c0440008200143e451b049051600914118048030300700ca80015080101004083d2000e402514801c485800010361061080000301d03c1100350304002c2108641030a00143c50341e008642c07814201a1a400f2540311a22a104810503d0a00c01c455440d00c910740d603510f4001d030300140400c803400e07445410440d1540d803003440e44030040245005c501c60342091403041c1410595000755503d2442c4032030484912054000c411036032002003409001c1e41c2c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 509780980 1250 509779730 509779733
    0x2131b03020d151205010f0c0f03020918010e10090c05070f0c170115050d02100c050c040f0509010506040b060d0b01020a120f09090b060409090204020909090c01170f01050d 76
    0x14070b0905441031a0403001c903c0001d60440d100200d4100a0040c0024800f80032070b4400b00065882c1b01d01c14000060300e402810702d01510a5002d04080c58004001e0903c0000695070505100020b0704083c440191031b2040c414502c1d00c070103480c002003900c60014800c1c00c87c0305101030302e01c0c010224007a1800460711070010402200811a1001c1c01078101c0c2200c2101d0440d0406000300a01110102074100d10750003c21141340411810120f01d41c010201004401c0200301254130a40007442240c143c410030744080500d903190f00034928017088001c4009400e1500c96002070035079001030710300c1e03004d54603025240c48551600c0080717401800c182d1201080641d05400103d00c0c0c040c0b51a005081400542481f070541c55001522141e40c0310540d542039002c50311150341a080710400740802d41c3c0300c40c2c03c01040007105445c0d01f001341c0d99400208018100b150f03550120710405000c44902100e60055104c1e0340156030000004a9404250000e4000300d1802d10f420548401c0c041c0107c5100d458800720400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 509782230 1250 509780980 509781007
    0x3050606062206020606101e050c0708030c0d09211205070b15030105100803031b070203010e0105010509010b04030b0408031b0a030902030c0904052d01020c060402131b0302 76
    0x381284407062001504030b6a80c0320003500c422041c6c1c1c100384141c481c8034020394031510503046000f42442c07052000c41081c40c0b0a0060311b00703a102c104280c440e40101c04000507400400d0000d031010300d19410180c00c980380c0c0790750020301a42c1e181e041820300004440d99031340903280441d2122407035980302d0b541c400b143d00301050940e0be40c018542c00921941044080040010381c0c41202103040fa0281c00a1102d034498907044028941a4010107a45038403e000060296920aa10842d1035031000c0603245400040e4002c20700b964200c50300410079a441c0c00040140b410401d28190042ca0f802642e582000d08555035034007512005170009d44060404030105206001d8007104180d034200d46e6045503903c079107404015028225210040c1c1c400c3c0a6054003801138200000454407469001001d01a54ad00404115078091203100d0701c5190030400a031000302000f805d1000304442e91902c401071140b03240510400504100d00341c110440141040407040c110100c2500c0407000102038140540c0300c80919844e030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 509783480 1250 509782230 509782267
    0x5090a0312110403060b040b030a0515042105030f060a050d020103020702130203160e0d0c030f140105010f08060a02040b0708030c1903060303030b01090f0620010608060106180305060606 82
    0x4400c10b10015000081254940c00080944020303141442000100301c20540c6908048001500640004400300940000c0d00c90440d4414468290071011500c04e40203101c808254400500100324004140005001154206944602c080728680c1c0164140000f08104003a9540024103040d0042480e81c01c665030705040c0c058044074000115203914040f9022445912020740450125004a41c9114a41843c68205d42c569030045c24103d005480c5a96820030b28000c18000c3c4d600168414141c41d001d1003e004140c002c0c031a044080307046074202048107080c40d0002c0c0c4198925881040100b1aa040c5882035881c120f0b000302c00c59071a583e40382e05014a0388550041d00300d221041481c1c2580c5d0342d0f007550141080c0ca00940c0d0403c040340d030784d00c01034400d0701d810701400354500180701c0200f000c0c0e440350700d4090140c0d0248408034a0308404401103403d40303509030452607441d00b0080041c07049640c0240045c7e4540440c018121000d45543c40d05901d800d00504000d004da100080d807139240c201c160f9000b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 509784730 1250 509783480 509783501
    0x51c1b0c1707030212070e011229150117070f05041a12070804020f040b13020408061e041109060609060309070f0801020f0d05130210090509010905090a0312 69
    0x181145500105900c503280d50507808104d10481310305c035540300c080700b0004011060f1508601e03a003240ba400d1030401c590088801d1812101c0c0c6144085080618401004c0e4102c40c80480c1c10018050801441440c0440341556803541085030184c94400e039101c0300400e0603082a100d00b0000c40d0044540811a0070f81b01e250000e0012021124203045402c11510090440c4001200c00e6901e988490508450100059030088e60040e60025000340300e26245d40200d520303100045c41d4aa1041b42d928174076090760000d81c401442504828100040500c21041601003200050b012110034a81641ea030001c4202d80721060780604480d10005003030303480b61011030f170b440c40340200030035240e10b001880141d0350211401031b114400e1600d0000103e482d4140255082394003070203415400c1110001404006020040ca0440080c10303605078000984c4440d04040950740256841180f02810001440348030581a0300000d8111b240c41701300100ca0001003101001176915140c0103403056015440c80000e0801e2191 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 509785980 1250 509784730 509784749
    0x2070203150f09060c0306030c0f31050a090b1810020d0c0e0109050a060806130c0c12091d190f0c02010e030309030912011e0504051c1b0c 61
    0x60011452450151521620106081391055641d4210101e440d00041e03655a4042e80b01542c0700b000c6141280741180100c4000d0b0500310704521540400f44c098021618412014400404403101c0d400b580c0210b65000d12554410301040c02d83e40c1d280400000c00078030982464956034440301b100788050055440101c16403400b55152a100f0407a44000c100800c500030108400000005c482e50103101d1520444200070314200000f8a01102610050402002154440e4100c40b9804400015100d00d000002d20b950714200c2c100428508200c4920034141150b06110050030100310a4000002c0c40680ca08509548241e54076a410030060500d010190b501242e410010051084982c030741c05034132104041e40c000d1044403130300c110440d1207101c141c921062035001040302c4011402d1040440171019904000001c1000440001507200e1004910301c4030f60a8441c02071000303000042010360300c1d0350003a10024104540b003410140c80c2541040c24642c4c1e840d403a00c840c105015230ba108074001087c80c02c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 509787230 1250 509785980 509786023
    0x5100c050619051b0a031802120f15090a030c020111070e06130608120a110303090109030824040e01020706060b07050609060f060402090406050303160204061a0d02070203 75
    0x26a010800360820b0100856246000c001030007200c610f0080340340e20950b140115150080048046015000c80450b0f00c3e00c207a900042c0c50b0060b1200e009900c00e103401040908403105000a50700d0404084080c8148007031705047c00c0c000128000324205140783d5060620b0382c0d45069501c0160390500d0f2030783d00c42c803c1c0d009124000888014000c0c43c1c40c031683d002c90701543c0c9242d00c41c0540046602501805c1d0782a0303c2824407014441075140100008009070400c2000600e0191034640f031035008442c600c006035182c1c000082055041402d15801501d0140d400640521031a03031009500062074265200d6611000448070103482941120b00494120006016443c5c071100c0002c8240e204120888041c0700d070340d002404c0d0250110310341d03018074503001c00d07115551603603c1008040c3d0804c607152503010b03541d404001a0b542d0104010000e1014442020302400020f00400c41140c440303612140d015000e240c2d00d200c500210504492484200c50001070f12000305002080c40d106050080300310038019903 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 509788480 1250 509787230 509787241
    0x3040b090f061210060212030610091203030b010212090f0904081905040302091003020d330c0e0316120609050d080a0606021216050f0d090303080a05010302090105100c0506 76
    0x4480207102c0c1350000c2da12400d00350f031290704903a5066031482e402800d59080c0041ba445150081e801c2081c041a0318014151507210182590300800136542203010960f18036403400c59503010b01001c0341c20f100c0301000d18100b0302054046a24982010742082c030405100700080c0070010301ca410748140e201c20010b21032507250845000381040d4040e01003684680d14840000d07555080102c16442a0795026110560f040260740d1400c1e401e101c0484060003116104803c1514214500405004a4403014002c03803001d5111401078070691840340818080d80100300c50018a26914a415088074404103021030a51480e090110082400000040840c0541c2c401d4420941c1d020000034040e28540d0700400003940d890800740e03910900500030190086c028445810140620719603101081d0150080c0c95200c0321012407030f81007041041010700882c46c04d100500c140743c1d000540c6580040301c404104455411500003500440052045078415034030b120702c2c3d0030f26510030310038114040d0b800030845001e82000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 509789730 1250 509788480 509788507
    0x5030406020705010e041814101b0809010903090b070c051e0108090304050310020307050705070803040f0914130c080d030618140c09270106020115030503040b090f06 73
    0x20f407103442c0c0060b08a222102c41403815108071f41710b40e9403008008031041c0c4250b54084040e421420b18100030700905070b40c5074400f09903000e41740f201c6a85481c0f1408001d130742da1024043c0c15000d0b00c04d10850b8501a014000030707400c8981102941c2d49809a151074400c40e10b041d140804441d00126004041c120304003114407500450500814003d807076000345d60380c450440b55a80e011780e102d503a925a2003c90004c00c4010182c0c002c5030014880d1a020703180c02c0c2d4a40b55507191082d543d00200326a440002d08000c0041500d0260b006000403c10911051a0b0180c03003085095001e00650345900040b0002820414a042d041c40101003c2069892030002c0c1e1a015008105511a0700161049800d00a9108a05214003d11003084011940c041e80302d920b2650310350b8001c2c80700e840e084404081c00100030110031010580703804481d13400c01d05940c1070100080c2550000e1041b24400740a200f41400081c0c0d0200540d4181e8801e80a6030752540169000035903041c202107081900250002041c8005590 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 509790980 1250 509789730 509789743
    0x409020f03010806010602031611130207050c03060c160b0a020c060708161b0b19090f231e01060906030318050307060c02120c0603070c06061a0d180503040602 70
    0x110f6054444c141c4e80c402003641c0703e2264103078649070700e80c0d403808100c001880410340410140001c1d01d40c1e0606e101b00c50246089a100c400207a82a0703201a003090710510701042540e80c001003883d02c003402c0581640c0c503800400754440e40182000c007000d001036124071a0794140c80410644400312a0035007050913016002c1d10003179a90011035540c42844c0c08040d03004040016002070751014000d41c0f540310742c0300c440046102501030780581c1e004c505e080c814403a9074001c02c41d526000741c900381e0304a02c062a207060f0714501c1141e8100b002071140004500c0503c0810304911052048001e400040300e500705042c01041e45407c80340450303240c0480841890340c452139401d0f0440401e150717034000d10307165010076548080c1481050000760318002c80d10010300b00003010004164000c812a0001446100083c2e500c1d00102c61883c0003e400c3c907601c1040c84010301500c00109000700d44440c1020b02000126900e205040062440c10744400c001031300c03443d5000340114803580200990b6112034403008000d46560 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 509792230 1250 509790980 509790989
    0xf090d020f04060e2d06060715020d2301050307120602040e010b1c06050604150c0c03030512160f0807020f100f0e011802010e240310090c0c170409020f0301 69
    0x422035802c10210845d0b5404a1741c005100c40305207081c03a90303402c0400c10715512540c4112034000180c20f14035041d0300036002801d0002250003000c1000c00d0f201d021b1010300303010300d505019840300401c010015510f01203100415652800c882c44482d00003410007801030b2203a54048024142e408000040403442d400c0540f00d0400090092240304680b81805000c1c0c401c00e024080d4080004c0000f0401c03036144007401c4003002481e08183d10810065200c00c4180701c1c0b550b1094011947c0010960b038061419400d0a900c00d100100c030f80080c200c0f48400916095410303003244144540c0801041d1168001c1001d040140c0c580c408403000740f0b0350740c1004406070000110604005003040b0042d00c006006000740280781c2e0358140c1901c0e0720980c49d00119028094940c441d500000d400000754400e890b82d8030a5174801003c60b65099980c101213030003801012031940b01e90700042c5440100240b055010001c0da101c650002c0c1c14130803225034801403000724861580404491880011b40f00348020201020358100d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 509793480 1250 509792230 509792251
    0x140d0c03061d060618090a051f0605011106150d050105072a110607061103070c020f01030b0f101407032a02030303041b090f051504020f090d020f04060e 67
    0x10039008120ba6402040d242194044002d09941c408500c19a45c4540d10041d070000303c900d038000c41d446542c1448904038042c01003070f40d80e540601c1d48092070300030704004100a04e0b00c0318500100c407860589a12000d403002d40a1406480f26007881da440010102307e042c2c10000030000d078105000c02400d00748040b4a05003104011a1107880b0342c0e540d480f02001e0b820b4210001880b41d15602040120300e42c03004c00c040300d03042e5565500c40d400860800241d48544900d4540c00041c02e11030040048000116114070304150030107402e1081a22251a01d0b628100251240810104000020341e002c0e1705d0442880c0310040c0202e098024075034450303130461710785541d03140307007400116030004008806061a078042d406174070400100b00002d141c13006e0320a8510055211400040c1c8407400201a44d0f089240c418506071145c0c184400800540c00d8926a01822902140340441c03607803204035075005801c4020300c903e40c416080015511015003000030510020820480c440d11103016000e40c10003511640c00c0b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 509794730 1250 509793480 509793521
    0x302071703060303040501180905040308040b09070f03020f2b0c0506030f070503130b010609031a092a040f020a08070e1f02030d0501030b060424140d0c0306 69
    0x120004041141c0c060b50026014600d02403e0400540345840f5031104d00307088160814001600c0c4006108990047d44280c1d40c40440b0304042c28001041d28001c2e0102125400c80c00e000c002c560100004036046035416140c00e0318900c00040014402c415070b400d00302044000a2523010464681071002030030074418914089861780710700c14066680000c840b103204008596004c03903849401440070750b500c26200712445a894519903111a146d101c02e034002000b00340640c0f018030400030490001d006201d00703545c50f003107546014914155110b06004644044d030504d504842c8aa059602405250b084054000c6c0726990071080118000e42c00308010300c0000d80003034003090300c0030310a00080e048280000d0001e0441030a07101c1c4c14032207011149a01044d803000704070b801150a07107806114000c602560200d0005d280c95002d10003665621640041040821940d40e020584180402c4094460604546115502c08004940c41c490a002c01602c507241d80c40c80002000380319048140784c050442d890307150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 509795980 1250 509794730 509794763
    0x10e0303190e1005071e171909080a020a0e0912041806120308010b1b1c02010b010509061e0c030f03100f150c150e150906102112030207 60
    0x3614015107800a04084103078244070528011120800c9102c1d0264101c81d0740e21f103529942d0103456014031030103800c245034a5400c0c2003190300312003044001e00744000580000340d6254001103000a0318007442131121580004280a0a0200a0955201d103000c4400750785640750008901c4503280c210b0031800b92410000049a01c0e900c10000d00c4440354103486814483c2d00340000c8200582000340084a1464507040580b8040c208022101541900f2251606c0003330341641c009003501c55488030a41030003020403504040b034441100b1100f032004401d07820900e41081d4945c004847c4548901800f06100220314040195185c600a45c01a0710a01210f0b044680c0c03081908010002d0f88180212041e450180c0000b2901421103101024450162102c0070400009800d0071902c070116898020340c03001c1094002940044602c0d9004680741c4001c01c804e141424004900c03008a0196a14401a80d503090b00b2110700c4109064000350310440000344508a036400074000c0d0090b24056603907600390b45d19030340c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 509797230 1250 509795980 509795987
    0x105010b09010f0c05330a02030115030f0608030705060a06090908070b060109090609021b030702060a1d0d110405070f09050f0a081b09070206010f0302010e0303190e10 74
    0x70404501030312411081c409840c01038848400c041c0055410303020310182451103440c102d5036021102100315403072420b5070700564013a00c4403000404a400741481000180030305a090100380c048a042c92401042c8080d442880001802c031030b900c046007078400401c91004002010940d00d214041c8814100440c9503a034808005441000001405c05402040030b480403810410016501100605100346000da481076100100c814035801035194980c04101d924000c00600718540d14140280021400c00b142038000a91502c00c0700b000000b4081c43c500c081d681440e40500086030201d0040100350801c0440c14001c0752403070001c0300240304500d03207000640607034080d00a00301490b1103a07a401000300c0c184024081d2141e000f140e0194850310956001441550400c5221020740f0b9029000c2c409030116428420200d174003a040800b5500004d0060248030800007030807007202d809280c1101e5242c1c180c80405e0071481003906a0032079803c00c80791003d41c25002046900c41c1c0506890900d2440030803401103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 509798480 1250 509797230 509797237
    0x6200f1c1b1701051c03050c0601090606020c0904020a1202131505040b010503100303030209030a140709050c0c030f0d1127060c0606061308070e06040b0907021e010209040c09080105010b 82
    0x962200b00d01c1203010681c5c0b00c0e80d0007200e44600c00c1c18a28504402d00107080c0c039002c026401204503a84170302c0241301c3c1c15418409090021003d0f21a5420b5080c1640082c00c0349090b40500c0030f441c6500f61045081d56181c50680c000340d04004420070821030120720a02130b0300141e0140314056400c3c45683e0b100d43d40f20303000301e920075100c00d00d030303024518250b035412000303035202c044120b0b80b600c00c0703d60a4000c00c0070290400d100c1c4040b00024007040303291840aa06680d03004162058a2400b40117001e40848c0100c211a04030f451980c000d40d07240300b540c20400040142180c02500e1176000716803803000f802e2034052070034841000c9504003010180482000746520551001c483e041d0000404680035090103009804103888904c481540e040c0c44002262401c1d0055000c1054001c00030280306a5050610440390200c00980e0006160b00e028140a941c800c41c5032100c02004003500d941c0c2c40012420750507100400b00082044c0503200c3c48500003000b5032a1800340b56400d5103031200004081159070304030b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 509799730 1250 509798480 509798489
    0x60207021008091c11070b04140603090a151e0507080c270a0509091510230a09020f09030118031b030908060f0406200f1c1b1701 57
    0x9214108845070042441a04e01403680203100c1130060032010b0f90001e000314006407070303d8400151035601d04844040c0ca5006c4000301401810108144150102c0100d621003855030040d1036090013010149000009142046510601480d0925003c024505581107240144e08942d01c0c074100e42c56030000d084940c405d1002c5c0c04100c030728600d007503158140d103000d1401c04d5510040c050380a070761fa0b40d40800c281c031400315200406900300c4004659032800041059400c061000d100c00341c03c600706800802541000132540402c038008000d0f13204542d5828407500080c0039200d40542d02d482c1c005d0410091a040320303240501c2542890418130440b928803040c1312105415a5440b18800001c0c0b00f98101e825140e0030a40c00c0000d02c000100d09028100304103809070407040c00c4000f03649000e040c10401c8131142c1c07942c540e280c1c0a2a00718140c902084007994405204110344c00c1e9502d100f5800048443c104c0d402c0710071514141101e400b075000b602c500346816044140c42d0800603240c20240038984d154240035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 509800980 1250 509799730 509799733
    0x1e0d0e15161d130e010b041e09020f03010906020c0d020f0d05030c091906090e0c0403030809030f13030b1f06030c0903060608031803071206052d0412020d0509060c070b0706020702100809 82
    0xb800d070f8208da41c108190003030000d49081503034800700c0e000c2030941d0751510054406035000101c10b041c192041003c690010402d10241500705508569582c0300e0300c1024800c0c04105000c00405c440c0324004003180c1c111000249000042d548044009110b05038610603030001c41e941880000b00740c00903017081c52003400001c103958074050450f80c06841d54900034113424003a01c42072000745605454000180f1b002d02c40400400d030901c1c035502d002c02c1d0f1481c00418030301f2800d41c00480c402c551030110070301e102521902c1c200031480c4c15138440103e07105060303644090803603805e011000074803800100003031006402e0900496019a140024150386441a10540c44203c915000e034401042a5900c03094021b07980346180341c043c0c1c5050588071190200c0050066403c04002c0500c4100807a00031070b420a8038050025000c500e100c002d0107487c900a20101c2c0f40617620000d818a2460001c0c007444000d00380302c4860176103a1989081c03040007034124490890044a6010101c1c4829010343c0f1414440c011080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 509802230 1250 509800980 509801021
    0xf1805070e150f100302070c090501092a0309052d120412030c020103020f07030509030c01021605090402042408010b0f0a0b1e0d0e15161d130e010b04 66
    0x142072189180c14130107000c003015401d00c1040001000c10940030010301c2d24400105440d41403065030b504440c24204111381500b00c0d44000030781c100340d250b6009501400c6040019400c5400c1c00e2071402c05650614141c8461344003008503040c0300c081040721301c1c0784040404680c1160b03028a4140e0b0740e846180079040e9103148020b9142c0010f40308d05c80e0f0041203071041c580035040809044402c0210307084943c0171030224501042c0015242420000620b04240910082090704107840b4a81100881c88c0038403030061100b640020155115600f1400c0ea20203010044146c002100740d0144681045004074540c95007000320f40d00b46071801031529091498003d00c444002403904a122060b40e01c000660440401e01031300314414002448050321035580004004100c030001441d040f8280460b000c2401148506d003020301200812440041c844842035060072030304104081a840ba11521212009a012541d4101c40c002c025160300010b480c7e0070711034001e2100d442c2010400064411040c0c1c01c40036421500d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 509803480 1250 509802230 509802259
    0x302060f13030c0603020403020315061c02030f030a08041505010b0909091e060105041103010b030402090405070f060e150306030a06020f070218090c0d11040f1805070e15 75
    0x6801040c2a0071425200101030381d40f60385004881195910180200f41e000c6400c005506051000d500e44080584441d601d40c58010009104038400503903d0000040500122085403420040d400502d16038500712038441c0c84241d4002c2601b442105d003202c624015500d0340810001500a15040c1d911130312003142425558018405c4000c80202210020b01c100c000b40004486122182618106240081d003155070404060009076048508900c002034002c0004000b007007012019207400c141c0c11034100a554032a81032840c5400b003642c008a01e05d40065600244082d0003d00041c440803060725000f04188041070940000d00007140c40c503030560000384003c000034500c2d600070585030b41003001c8281003030303059008074446280154481040c0350070041480b001c0e000030001d81400d00c004550420b0444181d43d520035030340380c414461078021611003d00302a0510781d900b000c1c004403200030381c10740125214103015a0311022489041c078141c105401290703068011403420801e00001510031224131010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 509804730 1250 509803480 509803507
    0x1050a0806070206073608010e0c030322081c0206130b06150d14040c090b01090303030506060d02070807020108100f051504080604031d0f0a03060e10020f1b0304030206 74
    0x1750350500c0808100d041040a01b03904100e60108003128103201c0502c0982018441400c5414401300f00660394820304402c0b0103990004101c1e400489a5403a070003071034101d070303408c40213940e80360700300c61154007407042c0c02c2d82500742202c0070440300031807a421120a80c031001c441c0b2000081c0c0160252640300c1d440c0c0016094101041251202c49440805a140803072034a54601240c161120000980c1d103400184810321156100d0311028001800e4200700c05950440080c0080c15188002400c0c541c45a0000d11244e035040b0545800065002c8295038900c154500152a039014401c00c0b07020500c1c0d000418040c0042c00700c9002910314600c04050a1814402041203004c00981180e40d407580810020800c0c683c01e206150183d44a41c5504101072400c41050002d40314060080c0c0c007030320b030013a2030345440c0d6640120202181d410003800151002c680c4c0f4130908116a0710401e03080240001a03d01d109030b41c0b0700c0201920100c0e41006011604004d00d074540700e1045201c040e510400a0102070f881118 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 509805980 1250 509804730 509804747
    0x1115090103020a1e270e0601110f070f0501260109020d1d0d0801090203130f02040f090b011422051f0f06030f05070c0311071d01050a080607020607 65
    0x10b050410800c0c42c60b09540c218a059050f207007000001799201308440c106009041d80f9041030b0312441c8510031490620059003042c00b001480300d03042140c10441075250810078000b82804070864002e41d150191604083c0c1c610b060144a25030014005406a41460401c2c0c0071840800c40900780c0c0303145a0746020740a00103500582c81c0d02040c40d50301c600851074101c110759201500410742e0040c0519481150000c1c1001c04168003d07071049004204008160025040c09809030742e00c00640314a81c030150000c103005001941c65100881e14012049043c00034580030141200d10840071503007000ca00c103043c01140c90080030042e01c50075404000882c84441d5400059100300b0b100c200c000300e81441c680941102d41c40e80d02c0b00034040b0700c6c95000d01c002035044c05001c52000300c003182440107080c041d400400343c042811010701007200c84000d14001c20070603c07243c0b00a105d18001e030424040c0380c18510011080078440d03140710724204080001d00c0300e40442da1903c591180d0700079018075034407000141c0d2902e1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 509807230 1250 509805980 509805997
    0x210e0a0b0c12090d08071b08130e1f080106030b0121050303011d06090112150b06181008061c0609080a020d02060106020339030406020a111509010302 66
    0x10288000081800e064040b6441500d50b000180004c0e200301001801d030300006000c0c030b010041450f119403040000244201051a444041903540300c42104284094a04035040151b04a03a0082840b40ca00c0b0052940b0f2421640c0010803429035503a03905040c221855440020b250a211038010481c11507005600392510b1074080104d4442c10469460364119070098010502c0d0b15000080000480c0c80e08411aa0002080c5c0ba4942103504103100c1600740c00b038290340141110f0354040441c0031624030390410001034201811260300e0f4401d00200c0000119007030622401006030305819450b4900c42d000312402644003900c82d58010203d101110b241c109009002d403031403611082042d0014202c0c000405035010142c0c06868902201c4100906060040e40f0200c01c43d07005200c4041030260344012940b411900060091210002001100e1229091589400d0502010034002011600801c0c0c402c041c80c81421100b0348030007400d0400074500128507100044803401d1020180c1540268010304060 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 509808480 1250 509807230 509807251
    0x4020f09010f03031e0e130905070b09241c020f130e100510050c0c03070902130807150f0c021e01090504050405060a0c0915210e0a0b 59
    0x22401402241a0900a0b4888042c07010314803820010706074001c0c1485200c40e00503411194020066000a0080f0540c44500d441200344000704104151140c2c01100402d40c0002591038450359401c00450b960095100d040c081e01c2d95518462032140c002c50403036180b400541509041688071101c400c052290070003600b0a0342c3d0b0800004203c025030501900f26219452100c40189081c42e002c0b02c0d0034040030b01021a404490070042c00700741d40c0d100c034100d213000440c82d00b240c448400746603482c500742540040f1034160140400200740c1030b1441d00101000100d01000081e01c645d2644404ea9654492181d00a900844180d01308003038031448043c024400145030882000301c49400003140c52001d00780e404c500f0400700e0140e410f19600718409400400c000c0303400700450318040d00e6458413140e000f00301c00c4150b59150007044505000741c1008014011040b4846149440d0607800b50110341b010342c5001603080c2008070440040494010001d888110801803e00350049503100075450002500e0003084 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 509809730 1250 509808480 509808499
    0xc050a0b18070e01060e010507110405360c09010303020a0303050403111009021f0813050312090f0615031c090504020d02070b070302120f0a0b062b0e070e0402 70
    0x1040200078040140103032140c40001545403170400b510301840480e100c2e041c8031052002030081000101c400c11818429200818240d51f0f8400092681403501040201401c1d001450b41c0440982c50036070814400c07240460b52036851880c02c024008009220050059201d48954000a440394000da0780141c440c0c14641c1141003031031142802d00c004148144035071aa0381c1c50480c298600900e5071002702445c084040f022101c8228014105000100712440d150350320301c1e490040207000c1003111884207040c800110582084180c3e00c3d00e900107200004441c1c45054049922042500c00342212184000e008050b9203258000e4031001d103010600707020034020361184c00582030301d072030004001c0e50548500040ea101950302d80040c40f000040d00319004c1600c140032200c9140c4c1c6e002d03600358011155000300c2d02255030340840345024100700065560480400300e00c0543e03106084d401c0e8500024054101307200c0f114150700310340403100034662000c8a544620020010f40c0c683c0224075800c54009001c0490 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 509810980 1250 509809730 509809771
    0x50904080307030b0a030b0c030604051807170304031e1b1410200706080a0b0a06140d092906010f2102130807090b0306060f01120518010c0c050a0b 65
    0x72400d00c219165240500c8c0001005001e20380351066560041c074091000042690714002955101802d000b241d800c4120100700114180717040058078001d43d1b00140440c800c82e2008603c00c00590016401c881143d12102c00e000d40407225010b1000b40d8442c0d000880503211000d0410108a10445184041c040502c010740d40d40340d50b040d840c10020300510000e04066240c028001c1c0321013401401e91284034944184801c165440d1b8602008407825840d00d84036240c000500565140710300f41c5440a2180342541500030000b80d990301d0703041070b44401d07280000540c50710745040d0b009a08030360703190000f44101d01e450200d0b030040c45025101c284806c44a5800c4091b84c203454220b80c0401c183c414400507000c010041d100e03003044100094821003509015001d540c0e00480c0c1e4940d0050041445402e00310140000c1d6442210910700c0c00c40342e1041070015003000c0c13404019581407100b005100d0b50030200c0da4a13006014000f04030b8000c0e4040c3c001c1c90359182310388480f40048005000240a0310701443c5011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 509812230 1250 509810980 509810993
    0x9220b040504050c1201060f1e120309060f0309020d0204021312150b030706051e0c150402010822080a0512150108100b0a030b060c010c0c060501050904080307030b0a03 74
    0x91007244a04014004002910304104020900c04240c1c40170b40e0421605002e01c00c0300700c10400444d141501510000411300036a00d001e80e91540009011080c0d16885000341607210070950700329102134640346c09408440d1403c4041d03c2c085c51010750802c0070034101d1401030505a000f000380c0340d030310620780401903168281d01c00b100400300002c1c3c0b010100c2110b055841d41d4180300f0703032242c10011070043c5046403820b0340113840e50003400c000c0034419401150803250030241c10211241200da01d8159821400381c0300203006040001e5600383d00007240b00b0000380c0e00790210840300c514140c21603404c000502d800d548611559201074980800c100c4103211100390500b8a500d614040e84000c109003003900c00c0040018003801e0024170221050030703d980200200380c205c1040303c0c0404c0c8146404034015140d0300c08204184128011300100b5840c0000e46003015600c4901602010310404050100e0790f82d50040001d81c1c03109032400f422200c81007010032074150003584944005540a4031141c8031a50300c1c1c8034074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 509813480 1250 509812230 509812241
    0xc190e030123010504021c0b0d0807080d0c26040c0e04050703061b0f030e070e0907140f0306011e090615080f090606100c151506030209220b04 63
    0x407003482c1c241c15400b000c50040541000d015040c199405c40c2040210040d01900c0340b100b0000c06d40c1c455540020100c1c0340c80d50602c1d000391503005070b40c0300c3d951060742ca46644207502001c400c204c0c003883c01980c140250f10036030400b4140d1501d100c100c0038101500c181202d001704083d1040320292140300e00000d0745480b48070254452405500500b1101d8030b1744c20580c060300ea201030007008440d0303068440c8031140c0e00102d10182e81103082c5030018841007a0850203280940c59044800345455100401541e4000010428103032502070b200280302c0388243c0d09102404905812140d4075411407001804500400c9015410104299079580045580c801c0000102e6905400c058a030301d02ca4a07410070319541020700c8075003041d03400300701d21030a29200a465072540005003885224030b100b11f200c20005449403083e40c0180b6040f080200007801c44c07a55000c01005e092842c0f11703c980c2030600002c0d40318064800d8802000d005410214503412030b03012181000350095444180d181d48450342c005603120f03071080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 509814730 1250 509813480 509813501
    0x15010b180312090a0602030403170a020a060f0615080609011e0306020406050d0c050c06010501260f01080f0610060f140c160b09010509040f06030b0f07170c190e0301 73
    0x4003607943c2c0d12201030180f64a5250402030940d4410002080043c40284851084c200b1023004980c0f100c84800f070480c00e02c1e440301c0d0090106810000503100004041e80584201c4500282d4291210400c8000707407110304084030001c1d031291011004000c101e00c89010519808040d04c09400d400b6180e5179030b00c1c100d0700300360031503000140c01151440c84580940304800061440d800c0140c241001c2000895940405004490420055452100110140c86031181d034580003014070f42c0407861300c0e2020400400003486440501d108404003c007014002141ca00d00a500500c1c66035252420250160307408501c0008000400c078214010a5038510414081c00007800303000007400403441c0305d030201c0001c00c030660800e5006140410a07196240cbe005002c0b40c06541c001c0d6804100d035800c0b44102401841141c0c00984800fa680701040782c1c54414203210361080c0c0c2d1544a80d0725441070841e95034040a012601041841001c205141c0385048030744560b00c0480301303450286e6601102c01c010a09580c030700e028 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 509815980 1250 509814730 509814763
    0x903051c060509160e010c150b04020d09080909060f1804050c0d05060f1b04051e0d08030103030212031512070b040f0504180f0308041109070806030c0315010b1803 72
    0x4413107a1039446500703280018024644483e642e05940c54400c0400246581030310a590344200288840e11250140c440d012a101c1007082820a1410305207466446801d00f14402e900040002d000c41c40c2c80c018034070454034090080032020b41d0300d440070242d003030016005039000d07c80c01080c130401d60f40d120019030002d440351010384504c0c10300c0b0030501d0751480041c0211000100542c04581e17110700300c4068a0442c2c60884050701c3c07a031082d22085882e019000b0b041e84d000201d104c459014045c20400440c1260b101e90308540d600c82d4000310400c5203000c01c2c6c41900000000311081c3c2481e203411500d4254440b00c2e501510203090340c0e42d041c1c0f125988642e1100c94000d00c895400c0059260a00c180042c1e0b80302030b038000c1c1002c0c4240e5210f50102102031030003014840c0303000200e4148a407500741e20f40a00742c00303098844281000c0d01c014044401c03c0f02d0030f070310910540032847c0c981e081c086049100c911507003a254035680d090911110031500f1401c1c514414000c001e0b40a101d56408015000f8403002420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 509817230 1250 509815980 509816011
    0x6030f061b02070b2d0a0e0a090e07030f02063c0f09010c080f04080304260604031b0203150103120207060212070204060806280903051c060509 63
    0x900220000c580c5070000c0040d50080380b0704010000c2c5080880d442d114203410b0560100b55903403115103404150b0b40800820000105078902065048103c912645d0701c1220801b144550322140642034987c2c1c1740a007101d9400c0b0010130000510350401e000d140a20040c40107041c0b0035900445020702e214000308024025400c02c40c0407020604c2c1000a2044201c1d840c040e1070101e851800f00d10754842d880056040051041c2c00c41c00348000742d0309680b440a000b102c400d5079140c1d6007030001c3d40c0e50094064004148054075036001e0704400c00c4402104c5104e401c02800c10b580e92910103541d40d0f50f1440700501d1920103500c1c4100141c2d024003190b21040d5590560110030f506608101a101e00802c40d40000d541c010241030000c65000561401080005905540e8900407031020601803c4140c1c00340311980329050620003009110f42d8160403440d8103407040340040521613041d03025140b10301c20280100e082040340c8200010000d60010101e204880d000c141139948401262855504841c51804051480d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 509818480 1250 509817230 509817251
    0x4052127011d01090311150c060a0b010912021908070e1501050327070315020c011b0e060c0703050319080702010c050d0504030324050f0d03140703020106030f06 71
    0x40c0c60300c810455032440b5091001114006049188070340006400e810034030320944502c0c0d41d000550300ea20702010301c00c961500d07458481140c0d00d40b403d90b41c1c04c82c1c280c00c3c00010700a03540b140030003008444060b81001d0f4903011a400b8403e900380350001410507a0241c0c24040b41c081403c0141c100185a00011089035203020080507002c0f00b03021503043c1c1000f80800078013030305030b030075076200c8000021400350800c43c03001e81c0d030001d45482d03141e0b400102400c080c130803e10361016a503030150a2120b4038000034082461819040c000d0107101210803404142c00a440314414104180036140c4da00794482180d040380d40b641c0322140b440d0020400c6640100c1c0000b08203652591214825407c83d100e07000a102c9a0000a000f4140e40122000c084415135210000781c03c1c18400c1e0001d030f4103074202c440c0444e40b10f030b0000c5210f4080000340c0603550140c800000c0303c60040c20114101007250343c142d610814283c11011122000743d010300400e80440d92217039804004141c074480e52034010b038800c1c440081c09aa01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 509819730 1250 509818480 509818487
    0x1107090c0c030e04090b0601080a0209030a0b07170925050607062f0307030b04020702190914090307030507020607060609090b090a121112041206050c030405212701 72
    0x1c001c00c1134010b90504100000060340030448940220090800c07441aa42d10b007100e0000380111404543e00d8070800100308107008070400c00a00401c8280d0702d10702e40b050010f010444407a8255071610981c2e02451441200030000303001c510070082030450725102c180d0f441c40052a1900700a001b074840c1c0381c1d0341047c02d0349060503009034103940d101c04003003104900c1c003d00c5200060000821035030078151113215000c410756075030b81102d8003e170740108031140d04403c0501075131040711755016601010346030180c9880ca440e04012071520a81100c0025403070417015950441e003c1d007002200720b0300f02000b400030b0b4002806034003610028000d004400038100820781450b0403800b0000d0a080e5103508081200800b02c1c04000381016254040e0405000e008200340b0968500480d814401d405614040740110310100900a4029030b00d002d00300c00d2041e51990b52505100340b005076401495540708100076160008040200704400344085102030900e0307400308200b00b50401060b08400020350300c400b28101581c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 509820980 1250 509819730 509819747
    0x5040614011d01062015012309041b1d06010f0c0b0f04020a090908070212070b0318280c0807210618050703031b121107090c0c03 57
    0x124904505414010a80c6a2160801c103009010411a41c030601500c0b101442c8072490001c04001d048480000241b818090398420a0007511075441440d1a400d01c0103400c0c82008401c2d41004221200310780b1a66600c10401801500d541c50b001a0581c0008a8201c20f890503a07424062040006040ca041c00c001041880c1a02d00c40d8240724560480c8808501410111648642803817101d8107591140c0c0000341041000d903001d0300415090110400030044c00c0001f07840214402d0b82c90017030300d0712000117190301d5001c0346c040d03402c1000e400d200040c5016603d0010502e084000c6050700c0c618900c0b5100700d0948803c0c9800e11000f080fa400070401005102d5110b40c00506403c0040c100c03003401c0184131040b505500940384100003410101d0001c1c8640c6901c801e640d0180442801025001494015160512440140c002c24220b400c0b03900364802d88100c1c0e80a02e40d000d14650a104501d22082d24185481c001d030035030b42c0c440d203040804e040d580c80c400c0040100e002c0d1204030142d0240d1400411606 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 509822230 1250 509820980 509820989
    0x329010e0f040510061e08340801110415031406040207020126180102040302030a0605130f0507080d090f0b0c100609020403020112050f07110c040504061401 69
    0x14000104000840c000c034864222031004008007554550b400c20628044100a401c0201c80c03030002e0005500760301c5404005c9507898800040301160b55422216100e80d84c1c0708020342c0855072382c000307940280894014820100111561449120385560a940c00c44181510761034503000c0c0001c050107600c4011725410203240700d81c9800d0014450322609400603603006000280941e030082914811680600500c658010285545613151a205860b10314481c50a481c1081c46c50038004400024400c18001c0340c0c10b0b0790b0080c004000c14034587c1c0d9030000504009028059008241d06007000003468620680d50032401032005001483c2410901030501002038414403d02ca40d080040110b04008503178002100c034103284050f2101c3e00d05080c070342054081807040c41d0041c0340c040c2c04250703800c1503400f81c41a6130007a070b0360a03035001040c03009400311442074034242480b108e040b0001f41514811583d00e403101c035120094401041d443c0c00401c05545040d58120b800e50344642510141c4082108042d0061 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 509823480 1250 509822230 509822303
    0xa08030d11160503070b36010915020301141e09061f030c08090f06180102040b0412030210062303030c030c0a060e0307030f050d0603120f0e04060f17011503 69
    0x1d41c44101f0307580d00c41e034441d2000962103812039120601003029486905100d4028903014510303c51014500000e40c8240030b1200f45141802810010f0b0a0030520248803600e0061400c240d07510300802c200d8005802050b40364403041c6411f84003c0400c00481d042e640724015140414101066440503069020040000c10b640e402048425550400000c065400201c2c0880d1a41d80c1d09071220410301900c195004413603221030008001860741c1516002e01102c1d4060f900382c410041510082c2003d0740c40c144a40a200030703a003050b003d42400620302948007410f00a00700c9207009000c55001d03086070030000120a0f260000210315080c031881d0700484480b1802803001c8c5103080466540544000c03869199a020040007040c03a12007444140c1c460310245d5000a1400c03000030281c0f00c0102800016041f00c40010000038081c07c40c2d0500340560302c01c1e21142d0038031113106803c0103640d80c514001450491800e40d21100c00074a0340c0c0044c48032002541c004c261070305260482e0200c1c8001000d441380c114505 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 509824730 1250 509823480 509823511
    0xb04030f020f0418150209040e030408010c0302040f050f03010f05011e0803210901150323011a100e06040e0702251205100c0513050a08030d11160503070b 68
    0x500204d8881c10b12069014038030400c20340e050000703100207000380c09113540c0207483e06a890140440001c090401c86004800900c4040c22104048080e4000c0d0b101e014941c0e00e0884050002c7d180c030011481500386c000c0c000040016103c40c0c81401d4503c05c1c0c1c412134514401803141c0380e6000d4000c0051018040d110003e626000141c1c12007401e084101c0005c01020403034001040c0b200c902034201c16003481d8000d80350030f1a251641030152800c50b2280301d1090b800022080c0110003c03041c044c12a0314aa03503100007108011020602042e0401258a901040486400022103583d40340240c400303003114101c410410300e0400c00c064a00501c801c002c5410f0510740a25056050340c1c08840400d6644590301c1c00840b5809261042c46d0070b080088003201c0303d05110034284000d07132103000303003c90b00080d01c00060519034400a06c0b140103118002c03181c5c3c0d5001040054141046078002030540303c90205501d01d8981100e81282c0c401d0800300d0112865040041d030b460501c0421241250029220b0540881 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 509825980 1250 509824730 509824751
    0x220611010b132a17011d0406021c110408070515070f02010903080d0c0905010c050715020c131e0209030a061e020706050912040e150a0b04030f020f04 66
    0x305918009214115181c42e100d0320041e01091001c908200c20f800b200d00504a0410702c009028a0510500c0c0390100c08442c00009980411100d1103503000059003000c2c899441d1910340b01d029500610b410503104440898540410020b445400c4560304640d2001d501e0303030f003420021400c082242c2e004a00c5071540c4183e490040480070f04580e401c0d070344040416000d011078401600d0390b1100b940058040d40004c00c003059043d21a40040d030041906541d40b20049032a0700041d20014560740c2c02401590003034400b48501407032281034591a01e1180110317041aa20080018000c071003032070741b1507803040e21351803900e9100a0200c480000400e00c0d07241581032800100110380d44032030568014101c95222110300c51008030103041894026100101556600d1050412a01502050340e259805100e40c1d02040c50603010707542514180d07044180310280039102e00115285c2c0740105039000741d00841c049030000380083c180c6c0041004511807904840c8202d01401081550030010f21001d0146051020340e02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 509827230 1250 509825980 509825989
    0x308070203010c08063709151505070305070501111c050108240703060e0a0207020f03030c07270603350d0914030301060908061608040f08220611010b 66
    0x2c2911b08000710b00c1d8107820030010307413103042d20764100c00c145100d0131030b04089580e84840c0c214855110710910341000095a07010007180c612000166000080d03c148861000244248003c04845001d4400460700c2d0007402a05042c55100c11190512140c2404410143c0b901030b02480340180b80c114041c11704001d1380c2c544500d16900340115504003080c4000041c0916001354085c1010700700d401d540070205d103004c0380308500a40c003201c0c042e8441c000540e00304000740740010844001c075194001409040f85014041d25640d048914054084001c1010031003071800303036206600007180a844180301b008910098024a11001c0748075001c1c0c031086072522190425580c4c203c4d040340341ca000d4001030380440c509084102c000003a003035a003180400000003034550b9200803580c00b560344910a440994840d4100102507244440880c2c012031020000140800d10004281c0301a80c0070320045460104c41c50341c0c400400b20302e240452042a1101400c0c000035500c000035088010000c0d0003004014036907070009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 509828480 1250 509827230 509827249
    0xe07120e06040303050745050604090203060109030b072a0f170403051509071d060906041b03091727010302120a02030403121a01180f0308070203010c0806 68
    0x10f003d064503000400e50061140d02558a40d510004c405881c450417100d081d00348103481c0e1f69455010303000104445ca002100800003040b20b50013051146803615000d10391020f5040100303030070706210074080c00001013404662141e2060b503031030b41d481c2c0036440e2000e90600c0003d0344001c14007840103000c0182c0000740e82c0d0b2078032281d43d5030000641c0d40103501c1180f0082280c03040741c1008206004940a074529000290300d4140206080f60580c1e0b0b4079502c415480400f40007030341801251155201c0443d4150030f14011503500040082c00200f1141a41450500d81240204001e80020360b51410501070008003a120603803444001c080c5c615020000c10094060001258242c2031040c40c084c80308540d03070196040320310424110030100060f06d05904004d00940040341c06502042e801068200e070481d5a1040190326a040d00e003420302120b00c54011100c0d8048a0342c03c40001301b61300750116030420000f04400045215050407583c0e00000d10500d8251580705051368180000c10043c01056640c12604 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 509829730 1250 509828480 509828483
    0x90415060f0f0519170a0605031c1b05210d0507110a1b091407091509140d0b0f0a0b0a030206220503071401021204030c05010f0915030b180405060627010e07120e0604 73
    0x103901001103400c0ca00d06008908040d0240c10002c0191518003c18bca804ed064420118034100850785e5800070681e060040540454a5900711807098000140c0968030780c8441900c01e80d02401590f00c40602d0000c41c0c94514000d04080c141e0300c10800300580c03103004940a440000f1405c488002400c8000d40484158095807074031007000c1e0780b00d6945895662002155582104110040741070000c2c00c140403150a0f602e24000380c2c1440c1d40305d035031410015421001c480e4040e100c107242002803040c0e001d4900011180403007071118400c00148556003001f109024045100300c00c0480800e030b000191800d902107040e0524a1000d00c410400700380c40c2d0048034201c3e5020708021189010781d02044541d4000741d000721241210601a100c005581940701454070b80041d00d54030032004601101303942c195822100203005610490000e82a030900d07000c103d0306100c182c40d4601c2d00340c0c0c03c000c9540800c50240c029103030040401c0200302a555004165005c40c8500200402c400c1c44040441901c0e000014070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 509830980 1250 509829730 509829767
    0x504051302040c30180b0105090705041d09010e07270b030307030e0d0503040e040b07050c0606120f030c010f060506070f020f06090415060f0f0519170a0605031c 71
    0x510b28542005d8001c280810840190480300156a2810f1a4007001c28000c03d030143c0307010070008038114000c01c1101c051f02d0440c06440c1d154520083ca42c20038040003400e00f1215500c0340c07021400e184040280f074000d4640700c041034205010300c0c000040c4500303822000341031300b0741041303c1064507850200440d14440e815203858480c00200c000800e6040700c4a41d40140340703100014000a014a00c1d0041a010324418110920b03207403110070302110b050247c0103440620742c0101c0041815882e11000a80300089400161006086507000580c01c54000d0400a80c1c240d440d00006a410242c901ca0507002d02421110b103402d21013182c1381c0125013041130354001d0144001182c00300303459480409644c0d94071401030052192004403101c0b038281c8440e512071800491541c01d000c0c41c10034044c140403000207070f40382c0d0703103606041c5040500b28a1110000c40c5909014a20041200d20400341d1940c611038a507082000c96907030701d0032003403503e05925039007000d140744a065031802003168040c6524140d0b048292 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 509832230 1250 509830980 509831057
    0x102040b04050607060b12011e0b0f040b011211040503060a14070503061c03030218060301050d0f06020d02030c25030801121106180301061a090d08040504051302040c 73
    0x1401740020291403110b25030024080c0da61000f10b07081500242401c200c601d00850304d04032600c3d10081912000190258030400c3d85440d80d880342813982c000103c045d4140350501d01007442c80d105608540b03600c40f0b14001100002024003003820100038207500054103c00c20130501c00178090a004501c0c2c0a001c1004010000001c11103540c1c0d800c0450440780741d806403d28160450703250190003544646d807402e40a038040002001d10b0315107641030300d04a80028004142000c0d80360707a0566200300f0600c04483c616402c1c41403084070f03446440554800c0394800d14183d0b80305001480d5810940410a0440c40c092a10000d0780002c1c0d40004894112410b0301c0e101c0000042519007001000e510500c4960800b00c0401c0032002948501d13038209244a00f40c0003007061640740d041e449146456146400445d0b02c04004c0d0030b50900700040c280c03400b90301841101e400d058440d0000b40540c4e000f81c4000c1050303181000d449040d40f130305101754120414982818116401c0d0f4001000818400114210051130180d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 509833480 1250 509832230 509832233
    0x90c0708030a0204180b04051302150d0e150105031905030d0218040c0e01030608150432101a0a061b02060f0d0c020a150911030f0a0b06030102040b04050607 69
    0x60b0140c8014044140304030b504c0300c0510517040002e200e04030100344160305100c00316501034600c62a44c401613402905030600141511000d080f17903445a080410010340e20ba08624a00c2d100b0f010318081155400005042540340c84201441c05030320700948140388807940b46220018000200302c81044001c4440540c41c1c2800b80b06940b2540403503c0c0c9181c109080c040300489081e03008014501d0980244c0b405c0220b5a00c804046645000c20200d10580c403400d840410007041149412200600d1410201070150890b2070a03200f008080018070714940c1c4c00035070781028000c100d000d220b208041e800040c042d58002c000005600c01c1091003902b0501520214902580c00c04865003e4040d4018180300d07504c1c0005111507415602c901c100d00c0740c2c0d03413034004a54030b0948041580f40c0c44a07001481c0e050f11300041a040002011801000c4031110480d0007010400d49040c4842030324810040c01074a0312100609100c2c500e01d00082119210364810842171041d416000b068505442e0140c45264445805 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 509834730 1250 509833480 509833501
    0x1080607053f01050a0807060e15041706010801050a0903021b030742050a1101061a07050705010206092a0303030421051606090218071d090c070803 65
    0x8501101c0001981e0b400050010b000b8200701c1c1c101d501c1a582031000070340d00c0816a4542d1501c3c01000d00042108032003846a1806d525810450000200c0360741c9095a07658003840482ca2022640200e500300c0f0700100800203080c4607081c1d2200d40c0f514144103a0610b075030003d4940b1003504803110408001c813801c00680c0c4040003000c0140c4a84400e650b0046d0304050600c0d1440c50200c10148610f68034145000b1319103011000c20981420342d119036040503200c407420345441c40342c0300700d154440d1350701c403c0024072800d4000d52005c1000382c40318080e038130407140c10514106145034025506561103181886500840002c603e0b610446521645000149140381c1001200d448681290f0520010060009020301e014803007400a1400ca00c540760300d1083c040582e0f040c0120841642036022004000c0003007069038204039040f0348000c0c401180e07405800d22400900d40c098136603000040200d0312034100d010849001000c03030b1a0807181c202007868410800080ca1140d0301c0002c20340350700803001c11503081c107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 509835980 1250 509834730 509834797
    0x40f0803070c0c0f0513140c0c0309090114011b03050d0c1e02061f050108071d0d080306190305030706240803030f0f060312160204020d0e01050108060705 68
    0x74404001880b00d0344c3c43c410499008240e000302441081e00700900c048004040c03080b100c0c1801040f0500c0b6250b902c0700c1e02e01801303402030410710020340010044400b040c2c2d6801040c5000c0d02104100c0703990f481403140010884101d0201a4150100154009010a80080c26208106030403000414900032000c422940d8004a02090030007604042d4544540c86d0081070080c4102028501c040a003044540d000080e40080d02c2801d0100e0a04008203010074031a4450b140c0d11070280024145c0724034901c0205241c035582c03800030703a800300c4e003c0144915481c5c01c10690700181d0040302c44020050854440e203030ac1e44101d48001300080d54950412100307050261800030014440b11840451594400071191645d20880704602c40000e5140052050140604010300a280c090024100d5011650302e080036584990025100d03000884040e00041e5203600060440c4603845074081764003a8100b19131400d480068210310080d0300400c04104540354803106844200c1c0c110003842e40181c0c500118081c1ca981c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 509837230 1250 509835980 509835983
    0x6040b0f090a0606080c0a0c0807030c081207120b061b070b04090f05180d031d0f0a02030106080703031e03022106031605132a08040506060405040f0803070c 69
    0x1e40c880c00c005020002da80003004490301a100c101c4107a40d909400341440c411006220086000107002002040d11100900304c1144a81404258000c0701d8881c5003541d0050355130b0503e003030038142c1000f00c03503039000640441002160f41700740b00c0c2550b00c0740051001d0040034044c5111540c00e07244a0200321003001001d0040c2064545c4950b0382d6102d03010000a001c4041d0031a01407401c1c100407510030346516400d140510340c608064050f082045c00110054a190300a40d90070f003004034011596280c00388008810410b82d50000c0850005c184140340c25541c03141c0c4502d48039008840c0400200b6082000030b07c0303c0e4008144c111a50a603140150001d0144003d12100340403144506602194000c44981c0502c0c4218110f44400c080c001108480350800c2c0107807504199905050080402d503500316840b540e5000400c0b1030204034011202e4000f100450042000402201c02d0005203c0244251500032074280c90510040c034003500c81d02c0c01c030240d400c0002d085500001c0052001d40c8240f02020026 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 509838480 1250 509837230 509837239
    0x50108070512101407080c04050a03020402031f1205010e0c030c130219050301090b040e031603030b03060a060e011208040b0706141008010b1206040209070c060e01021c02070b06040b0f 81
    0x440d08820004c001d02203035040f0128a0341d40218032400180e90640d070850390010003600703c050666091001941014001406405000385560300c1c0090070441e920180200b40c40c1c0350081c10640c10000d0941d4034100f09584982c00400700308285441c0491659080b0100f0b942455142289001c108001e1156101040e81450001c92000781603a110002b94120342c3c82000c01c0c0580d20181307041108881110035000350f1948100300c0b0110540c0d0510034107800a02034100020803050390f20204c1e080000803943c08091030703941c03441403242c00f06456609014181801c42c0340305102c080e64401c0001c2c442c90140304034203000815500c08100650b0009588400701042c0141d550400407031902100681d0b0243d040c0300e508000c9080c200341020110f96a008403500f00529440e01d0325000d00c449043d018203043c00304241c001c41c43c0701081b424060444003040013000140d0303456005e11911401c41c10034040ca803045004020120104860404580d0000c5048600181c8044100d0010308854981000e25400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 509839730 1250 509838480 509838491
    0x1006300c0603020a0f03020a08070e0303120906070305091506151603020106030203280204020d0e0313061b02010804060b0a050a0308040905250f020a02040203040506180105010807051210 82
    0x1070701c0c1c1c56000b800c0301c55075540b00c44e40200300341c03c8140d059000e202e20081c0000d0341440010042413184062508040d0080c0682e882c25141d844050958601228424070990028051094003903162082a0780030b000c0c01c0c0502484201d81fa5110945107015000a103d201d1a8074082210488001200d6032254021085400701c402c620b006806014980300580c4680074190040f034040000004208003040807407aa1000740c446582000025042001d10450441e038036420f000300c24008000801c2210060200300305032a1a0041c018400c801d503034444640784504420910050340c00502d542c1c2c0181e4481800718542124a02103401c0c40c1043d4802e55000083c000000b09103c0b040f4014410f503844200c0074171040d03450082c42c06018202c3c0f18210200030503c48045001d074071421039a40c0300156031040c5c422506464000071b090360016102a10107800200911031f1004844811501d000c0100c03009000b203602d0688840d071151040e11031280901089580b014032140e0502031214841c44880c0c04005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 509840980 1250 509839730 509839739
    0x90b060d05040f06050108030c03040b0d0f06030c030b09030910030f0b030717060c13050d0503040306020409020c1b01020d111c02010c08010602031213030318080c1006300c 76
    0x80c80000f094a086141100100301c034840807044404011a900045190030316103502c0505a03445204d400e0201c0e5a507401c00003c03c2d0b101d02905004501070083d0b90541c50447c00c201c0460700d030251640d401c6910401501c0c2085d00c03a03140081c001c000703a080000b01401001c4090002d080c5c03814020303515001e003400c0419030050f5101603800d101c40040c100c0d9200d5443c1041010b01c1d2045000b0320144881803d0f04000528040c104554410b1048054904140d6240e5460b01a60440e4000305c00094000c500720f2154181006001d03241c441c501c950b610224800c20000c0c0d121003812145900708030080c810340150b07440400040141344051029100c0f18200d004000340240750b0303424018001006040001651803001003645d601000c0c4024010a07034803004600f40300614030010031010b140d110307034000121043c000700c0c401d0458000c402c0030742e5030004144c803a41006428140c11854034600ba5003405520407805002000050102d4241c00591a03160200398081d84540e00401040d241c820109 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 509842230 1250 509840980 509840993
    0x2a0c06010303030507110a0b1f0e15100302090d020f2b020f15040905070c140d091a030c0a0c0f05160902030f1302040b03072310020601090b060d0504 66
    0x180b08055036078402106c41384252107180c43d281c442001402c00969900401c55040002003410305901e181c190300c114060b516400d040709070b44200c1e40081000f0758031041103110705041081c1c111402240c40c0441c03800c40210001904045981d001a00580d855606000541c9403000040c410440c00d00f49074440792881c0721205414030048100f240500740010301c0b240306040400c00440301704072010b80c035800c1900300100b850007000c6c004e1202d0308100c6207040910104444500801c40b1130030b1030018040b80f410409001d403034160568440c0c1440c01d0400490901c6011240541c1d4021098511312075590324803d00c215440071443c08003a01840e00b11310300c00204080015445280300000e0700e0240c2541ea40c0f42000d01301d0104850740a4800041c50015a075003044013485010302d44018000901c86c2520b80119180c62404d4000c859102c20a54941842040001c142c2c20510380c100d40541c0d000344500b4000703407501e030107100b0110040e480c0c000c03034800b61340c80c1d42c1900c5110041c0a01048203281608114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 509843480 1250 509842230 509842241
    0x503160b0105040e0102070201050730021c02031603050306130e0d0206131101210f020418060f060f0507060906140a0b0a14010212030109091203052a0c0601030303 72
    0x10b22940c1340c181441344448044c000d43d4041078058480c68144005c0343c130b400460400c90340d140300056079800076440100d1002104000005601e5005001c0b0248103071031022140000e01c0903000390743c0140289020050009544c040c6581c0c50b2816540300c0c0c0355180883c0000c002c401100c40c4241c10010f0b010030030f40c00040e850a00e0020703a422580c907901c903840302c408044a04c40001d402c0c442e060764149501d50082010406c80c840b41c2000340070481e07840c0100c0382180c83c6074111001c515000601001a550002003207070034401c201e402001040c3c9085440c2c071000322184900d2080c0080f62801c00c0240340580260703014190444414070480821b4a40f0700014104800340440321080d01d0041800d0a1080c443c0541c0c0c0700d13005e4240c88543e4101128503e4007081c0c3d400150451044483c1c9130165a81440610f00a02a00d04042001045490504030342e140e69443e03042014600740030030204101c4008034484025812422041c40c441302c0d41c08030602d00c115401650180b1860000004042d0f055101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 509844730 1250 509843480 509843489
    0x10c0c0f080a05060c030f01090b0f040f1508060108030403111c05010606090611151f1d1f050609152a0304060c0809030f0a050c090f0712090503160b01 67
    0x984e400d07662000d040e2609804195091488090001e0041c01007041c06d50080708040d0f00100400e051046403c00141555030107400040542d071950721a03020011041d0241010b0026940600700c60344c10300e880030342c0da8007a40c40702038603000c1c000d10740c11465100c003519076407410419200e455410b0351034100b05029107075600c1a2400541010f000141e06807148103282a01c1e00544040c100142082105200296010301801d28116001040c0f0b0345143c441030040c001040301c092182d4103000898518032103000002c021810004101c070418070240c40e4404c0c0c040039201c0444889840700d5803000464030403581401e40c0b00648400003041d01410348540103428902d40c801243c4101d1401118969807a40550310810011482e03142c0b942e030000c0d805c800549005003024086622640350010058070f4005002800c0c0c0e5160407008108034075046c032072034141d80802c488203401ca0904040c60b0092846543c1c10304d01021030740d5240880c080140030b00403514402b50501503d200e040280c105900b1a150a208 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 509845980 1250 509844730 509844733
    0xc1802070c0f14040509120d060e010608040c030f050a0b0c1309061215020c010204030c3206031b040b0409060e040203150424020306010e1806010c0c0f080a05 70
    0x100080900c00000030900307442c220340750f00c6101a031203c28040581005070115015028000080001c2c6508901030900042c0d68100070504500d46140e2640031501030300003804014100301000082500440c2c081b0842e03602c0002241c10510701d09209040203e424001420100380c2c105000e400e10750a405085556203c1c02040e4140e039a601000303040390740606c9590030480321440024040360513120100781121803c1ea002d840d10070740031451422039000d90011102c3e564900320600c003010b22005c1445000f155800e92030a02210b91510009a01c000a4010b204543c0040000d0442d10201c4010f9036131403605d035810717855070385803c0f1070b10698006028040089160070340c00581e0003040f071811401240c018014100708210a1401c21354443c0c01841500d079400c034001070190452020035405151190340c000140c40742022000103040c0210034450314420401201c0100529002c44030700340c1c00c00024241030f8858035262900c004190074650014180503c18400000c0d84403010a004201d40e22420 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 509847230 1250 509845980 509846003
    0x16050105090723060702030d0305040312090b0610031e0509250e060d050f061b070302070501030b0307170d0807023d152306070f0c180207 61
    0x10642982d6441510609000c040b00f803414915594650480e15511403002c2c0c0582d10f01001e03500420b142149007034a0400207540c40041200b07041d0b00068041e034860181744144111007454445140d40c580281c600c1d803007803c3c0041c0d0030b9884c5010340c0c001105000b104003076501d00c58002c542d55009000c00c0b5400d40300c90058001c2034107440c00340c00a0ba00c1c3d1120951480c1070b010709040380c0e4480c85034010a269006409200d0350408940200001e0401500c5d1000610300e600c1c10442105240312841d90204c04801c0502604000907000700715030b03041d5074080c038000a00744da0072000030b4a4980c1c550b01400501906051540304104007043c1c100a00c1455180c040c0c0d140c03039510b0126518089584802c40290800920480c080d07813071540f14811200c1040508294401044508121103030080d91a522103403240c41004050b04a1180c2030f0414030042c070a500b002c0025011560520031500b008045903e14084002000f41d095601030240c080a40c07121039018480030f0003002903001380c100703580091101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 509848480 1250 509847230 509847241
    0xe0103021b15090309011d010e031501090c0c110415180b09090c100804050703060e0109121404061107030f030c060e010b0a15020114130c0803090a0b03180316050105 73
    0xc41e402170318103950340c00100488407a100c0c241400d0044603410000310038103c0044d5501000102440024001090801c0d454070b03036079800b200e8100302d0714828484609460f04c081072003035180c040b071480c2c241d60101d4000700300380e01e400310b4150319080180e884000200f8610207500303990260344481406d851541a03900d038030425555440b803083c180390f07110a40c0144088034038031502016400074032a1048600f155101c3d03031041c01350707024420000010781d9142d190700300707112041c0c5841617550341d142080501c00070041031003107403445640105d205010304001000080141081000010741c0c03c0b81200078080c40520300100345c106440b800761566400c1251683c0d5003101031156540d40540100b144145901c5c1c0740c03912158141d0360000b04d09555aa134003c042c442c40318012207100c1d800d184105800c8100c00d14180080c03072244d4001d0aa240c4c42400344c81119160039851105640034107205540301e981e404405844607a90000040440c04040394000140060050421a0900c600001d00141d03039003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 509849730 1250 509848480 509848483
    0x73b010806060d0f0b24040c120b03030d0c091d0618060d06050f07030c090e0a020f0d14010918032111040b03071e0e010e0103021b1509 60
    0x380101030107904040701082e92440c00d003074003000e4a8030802d011050510030f501c5e45604820200c404501c400c4005c5207410000c1030440e104084030000300c0b010050b0020408008255400e020701d80c0c0c0c0401d0f5107403c2d410b4a99401c10954042400c1141d0500001c940388200502081d0188144a4042d826204143c054114484070f140302e454054001c22a0400720b04102c11182009400740e03801841a0b080c0d2000304510f80a0544540b004c50100003d41c102801c2c020210303060b040455007009840d04040c080310b00c04c910525040090614090380b1406080c0107581103218206540c0811031401104a861005031121a412281ccd41d801c01c000c4c3c4c000045d03403505075a2101200030001480c1c0c0610b40107004010410315440100c0c0f6000258401d2407202208880e40140c12a031490f810100030090750301d91209418451410851240c40344641d40c1e803010f0f00d907503d07008440d4107109500d150344507103920035410748500c0e1000c081d00850920200c20b1441e156001d01000007000260000001c150490 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 509850980 1250 509849730 509849849
    0x30a270302030d15050d0c170703031d04021306020601140411120c13090e010506010903030f030c1209120806010212070b0c04050402221a04030b060307 67
    0x10540c0142d85040c405900000041804210f902400f00d500140400e00351030704213421060300d12500e040e0380183d080441c203811154081c0800c65036075200380c1d41840069800000c0550994a0101303101904004400080190103040041c0041302d90f4a800007513915400240c1604840d030340300c1d0101905503030106100950300e900e0003c645c000000c20056000e0740100b03003100c2d40305030042d042505180340308840c40d17009420740d4003403804140c541c05100100d000a12942e1341000c070900344140c4c050300d07540e0080c2c000b105031a2184241999500543c1310140101d00390064072355500001c203c581c416140c00d010610403107070300c040019003030000070307a480d40001480300040b1600000c3ca03050264503903610241c010b00400340c0c580d0726000d200000c1e403a140c500182248856071030b081c0d20425040c19501c02c01002e968000600c0070310781c900d2044034248070000c403000c0d2900000d40c1070090740c4500100e46000a1640800981500c1d40204918011030390311a444402c0f08003240a40307000102d030030403040300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 509852230 1250 509850980 509850983
    0x1060e030703082a19030905030102040e04020d030201090605010626010b1e072013090803070804021903050d11030301081c210606090509092d03030a27 67
    0x2008240003900034144c03a4518107144805225a1394808910b00d801c1030400d09800300861000c00b804030805801100d4074001c0d00d410b4000310b00306813611180d45402035001d403029020701d000d20501401c3c54400e41040b01d00f503400c16000d000703a5945680081c08200322301c81884d11880034903504003401402c0d04116048030f4243c0380b0745060400e4070750904586400d0303c220301001c5c0f500f0054032002440e01742580d54030040c2000703180740780030502e000e000400c040c001c54070910900c0c000320000090708a8007a660024618900f4140c241d40b04c7c0b0104e0305002c081980d5000410012100204221700020358a02c600041e585134503200e4041d1095a0703880c0403e000c0c40009401c50010700c0200c9000e9122440054000d03d07000e00e03448140c1110203540f600780301420f900d40340c940c1c0dc20701855070040504c0000345000c0d500781030640340c07030400780da240e030948084100300d000c200306c0242c404a035100003040c1119805c42969a00d0420100080045c9202404c0c91400414547d015031004103002100700390700d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 509853480 1250 509852230 509852243
    0x305070201022b0e1510050d0b07050d0204092430110604030510050c070f1b08031b1c140a1b03030f14010b040b031305031201060e030703 61
    0x5014100030a14040554061400c106544444c43d00034030f94104449104280e01007501582420940030001e01d045450704a203014841d024240740c0003412040c081580119a45895500e5072039120050001e48956403207031501e40d00700782c803200d0b254580c8290361008100c410342e901070032a0b950250300e942e04c41d00c1c00c1001d0134100b613070b1101c10b0702c031300700c65845a0491003010410241c000c4400020215089904107460b16485008028000c00451003550303004401110114244200d0b40da80c13680d0111004c000a26031802c02c54807003002e00e00c80d102c000c0504103080a40b615101c10410f1041c41081c500801d205e64407854514003101d8103030080100c104105660303803808800429805a900380d01802d100010000d0b02d5001c1c1c06d0b800141e4845c00a1948079070780201e03181e42e4000c5008140c80040c840e0345000b510940041240c14203100c100e804a81042d600c030394581d910095660700e01d582c2400b0140c00c82c0400601030010522000e00241642c000f503c40030400f011301e6080c1541e0b542c0740e01004011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 509854730 1250 509853480 509853517
    0x207030f05151f0302130b03070b040f081204290301090902041404170304050f060c03040b250e040605120303160201020f12041110020d030b19090203041a0f0106030507020102 77
    0x244c1400c2801251b1a54408408550180c259010a103071049030340c40380294410100b0241310b00c480b0301c070349e150060986000403c103115150b5000401845103115483e400700d0032485c0d4020071071030000e80c01051000050015101d680d28132a1030f0141480c84400c13403185280c041c101c1c00c07030216020000c0c000c6030000124140280075a6884080f64070240c01511144142102000c0925042002c1413040745241c0c0203d0716810540f62042900c1009080c21a98460003032010424a0307400d01402c5581e00c0b145000940c02400c0800316004220a421080d0000c03241a400d0001c03260000085015841c1800911006c0b60070005c202d08030300940c51080b20850b401c12040c960380040d400301c0d43d00203004903990410080048d0014440c04103030706940000d60042c1c0c85400080c1d4040c428021042030a4a41d03240d80c40e060803038800411a00d0280d2821564080041800e20605486182000d4401a5501a40d00300703800344502d220002d105180001c1e041000003205244180280e030448141400348a69 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 509855980 1250 509854730 509854733
    0x1203030e07060206061c0b071b0b011e0602061306050a020c0604060204051903150f110307170702030c0a1b2705070e0306270304060e090a061508070207030f05151f03 73
    0x11660556480100c0c0270000c0c05012020a03c1c000416008000858a49a01950f41166109980354039444141590804030800424060b008500d00d40b156010b80700040c640d4961644900a01510207600403a00c2401f0410081081550003081a510110b5904a600c04c6100341d001002510380401800442141114040d090aa400454245200c0c40740403030b081c2144456024503170021034960000030000c44480d940d02000100103500310b1400d2010b1032070154015070107540c0c0e42c2505001403c81281c02e800c0350740080924076600280c64010348244011012170070b000d000c0f0f0030401441645c0e900d0400441d42c80c60151140f80c2d0003442c0500a0107540c2c3d2419541d1f40d0078200e044110740068035500540540307600c24001000500000d444003500e9070303010428460003a8000340310500d1245014001e1040c0321401c40094a916418980300860b07a69078201241488207aa0004001048241e490001c00c4004142c401c40d460140e052a01d2644d0341450a801203d0300d00c10b01060406110003d10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 509857230 1250 509855980 509855987
    0x3160f2d030f020d02100503042d0308180703030206040c050a03030c20040f14060d0203071a07050706090905091209100c170723071203030e07060206061c0b07 70
    0x9202d500040c0840f035203822603004140c1c43c206558802c0001000081080300301300c0700c6400500400c041803102e020b00c0001c246207509050b405d1402030301340b21101d400104800d0080321048907054560b410348280c0c41c0d03a450040d55554054132b0855550380e6525000c11039027041a0741c0d0040325050782d24140300841d0b41e2691f070002031016180b80c02d40c55075003013000d00075141c50180e20f554028001002130403101d0b894403a40000c40c050030742c91040d01821210030141c0d80009603401610b13899150300c20680d10070071583d88240b0581e20000d02c24007880600041d0300da007185030a012288a2038083c801a6100031800c5c1d01c46c02c1c0701c40c0070b10518070284109943e80c2030501e820411458030f800c100034101419143d540745102d88001051100f2030002d084800c02800384541e1900407000f480514140404500180d1242c03290b004d030910040004401e0020b0512903004a02865891070680c1d442584400c0000d4a6901c200c4400b40a5801703106010a00b00d0480504507049405c0043d81009489000049 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 509858480 1250 509857230 509857253
    0x2040e0a0510111b1504050706030b041a090603030c01150f05030a12030506061e0403050d1d0904060b06030a0c140f03011404110a0203031f0602190203160f2d03 71
    0x40c401031207a00709400804005c8440c180c01280180001d1810b185000b0004003941da000b456076004a0500c4070b241d0400d00000d101e55001c1d201216104030302e50b107030001f191440c081d840010110b90700b0036958105d1100402841010f8400e04c0c5080b00c003140d1144189a95501c030301c540144189c122547c001c0ca540d05c213a01407038000d0402003809140c04002d20b04101040c22912440d002d00c03000040c00c1003040010041040e1903212424039a5510080c580e802d0131b6900030344030341030144c40d81c000090100072a59120342d001e0240181107a13101d01b400ba014100034030b00a10b0304030219681030b0303d01c0400517103542511090080d18050900d140e003440c071900050f0840101141d049502ca80300002c0e04409a405007401182ca603004503200d00e441c03c024942c0146005041c43d0026501340306100c0180d002c59141010203079002c00c5c5201c02c84c1ca202107131400b144029480c008038814040459120f0080c00c0a604484480000f03400040b551002d03800000390300a0580c40105020074108000340d07000290303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 509859730 1250 509858480 509858527
    0x120504020a0f0609150f4a09060301020315040914060f1006031427070602030d0b0301140f1003080a0c05100501030b01060e0d02040e0a051011 63
    0xc0c140e94a0b81e45181034200da0341c0e60420804101380036020b020302c0c2c04440210b2410701c3d051130041240903c201e0040e00304403002100b025000711141046041035040c4101002d2461301d81300c0d030a000d00081603031080c00090082101c1c8180b01080c082012450140260703030040106d80e0303c100d180d2246400f040005c0006034001c54004001910460300586d05114542c031803440c44e411852249044440c1a0001480e6007001c8207240c900610b0306041e2015154495000103141542c9401c8200c034101030304520041c445200030f0344501e02c40444c15540c08406814041030450080c080c4031070400806090b502d80402e500400403130100010000000d43c807000360440300b050005000e454a80d214418658804050f18011a20250134181085002c004c14503403014041002c00c22541956101459401c040c4100c00410521282d645c405589a0000ba01101d50062040001600d40e145998507060603960070341c0e242c0903000c0e5200801290b03010b80e400c0c000c565115140781203035212503804103100741c850 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 509860980 1250 509859730 509859739
    0x30c13030204050f1b0c030403060f0b0a08070603110910032007060902120d0e151201030c050925080c1603022a1e030c032a010e0112050402 62
    0x40000150300c5503c01d41c0c2c082c1d40c54109642c000d1804407402c1d50043c191161541c84040e04002c002108030001c0140c50aa95012902248414440803140040d0002500d016444055144001030407400040c80c40101c8a2548082c0900301e800b69500c0414022200e40300d4100c2060044600220b220b9030203080c00b00c80744803020b80d0528100141429a8101c540211703a55070707039030103500298903040703031b002940c21060402480350800080c40100039061740d070240ca0046500030040001c402c03264040d40c4500041c02140d1b100e540c1d40f418640b05c24074803441240c3c0500442c030045420690b01d007404500481d0310101501d611b515400045803050002002080c2845050041c2001000300c0201d201c402d6020f54000e080f8804a5488003026005906940400d050016401c00281e04c411402004005600948d06468405c603004681800000c102c004c1e4140901101c0070a80c503041c2845084205000e03000540741c010200040d03882c0c542c0c407d003d601044c099540310641c0311842d08220780c803510140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 509862230 1250 509860980 509861017
    0xd11010b1305130c09060e160512060105191e03020a0c1b050d08031509010807052713420f020f22050a03030f0201150f150201050c030c 60
    0x220783c422144134980142c0001da85524003000720070084018a41c2004000000002d080200c12001d0218469150b01c1c2c42d5a11540f4002a00742c1c0c080c8046e02c01e0001080e41005407031003201c01c01000300640303010f00c1d40388242000448422030700ca4801e03140282420386510f581c404540d11800c40b480050341809010480b4220041901c0e00c8041c06500300612401d10b2030b1302ca00b800503411000b50a0352000d9801110544010002900001103a03012900191025180f4080041d0590003e0020300e000810300e1038100240651841d103501112012405101740b00d01c139541001c03980c050300e0b1015412a17138000041c02800c00303103d05907403414035000e8100c00001d0055160454078007a07030031101f084c80303c200000c43c052103c1d06041010400501d80007203010b05250900000561248180c00301804003c030582c40302e483d0368005d51214405c40c50560002c501a941e40e6029124108140106155400004210410301c0c0c01405843c0c000c0c4820444030342103903500860b4204541091501c0140b000d0600c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 509863480 1250 509862230 509862233
    0x6040b15030102041d060d02060f070314070f0c060c05100f0b04050c0405040e07030b0f0601020307140c0406150c030f120203010b12010b041427090d11010b130513 72
    0x903c020b0006081d134001001082d10714140c000750003035004150500850038100e0010041c1c1d2448111050100f984c02e040d034a88440d42004c807040000d0807500100d260707000580606101c110790b4103090741c1c1d22890f804001d594460701d0494a500d10030900802542c00115036103d10103054002e0304030010180800204011600d0005c3c040c0c0d074081d54018111800024180f005041c02d0013074a1100080c9002803080c28034541e26010041d100800903040c1c60703c00b4000c950644c0c1f00740100e48845800403000c980c1c09613003288147c0c444440d410b20324400c0303161480001d00701800d00c590419503206500c1d560a00121a10145c070a07100d25140b01c01001b081400000b40c8800b140b02441c007030600c0f42e94076030325204e42c2102080342d2a4180c02c840c041c1103043c4001c00420440001000308200191007011030b0f0b007034440c01c600e03108001c03402d1514441c0c0c00b0420850340c1c01c400680c240302000ea40d900e0042d4880b000d10031500304d8250305001a005900c007003100103222000d030000760b04400d4107048070003058900e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 509864730 1250 509863480 509863483
    0x60c0a08240d1506080102180405060f0d05032203031b050124080d030b03071e0e070804030f0801060c060e03040b03011d010605030135160503011103040506040b1503 73
    0x1214110f516908010500d12074003020b225001c041c00055008519080d81c0c800c544044c21000350f12144a9a11000060042d0b1100f1a813a201020702520504000030180b51a94481d00040d540481501c1403419888000010201050031640c140d00c07001d07000810140d100c10902007010080e1090342d00ca00b05062241d640d165004c11501044150101e0b007170500a040341807248101c848400c040c2040300c00f04076a6004501e00d0b003101d11104102c1c0d1040d955044845070b074842684590310070b050040400c01c84542002c2140e1081c2d1203030b0784d40800c06010440684907100d00b03000320780015250b20059800110b4a604c01c4d5540d08210044a00b05a42ca040081d0568403d8019000120b45604249041003240412501500c2242409820b41d07041201151100c120308120042c040041e01001c203010700d9503004140c2e5030400d01d0030365021010f5142c80341c6d07003040300e4490765001c0c0d8079064050207201000c2c07054a01555000740078080c1030729035031144038003000301801c9404000c1501001c1c1e8003230742c1d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 509865980 1250 509864730 509864749
    0xc060913050912162f0603071e120f06061b02030106150f090b030609160507050709061502011a0f1206010e0103030908030a020d0302031308030c030405060c0a0824 72
    0x4a982c01140b85111301d203059030708500c0c0c0300b140210242d6103034500340b15000501100d104000040c0c0c0c9880c1c4940d515482120410b002c080280d40e00548075015040141d072140ba240b80884090030144000718002c010b02040354410700c07640300020103640e0300c01d184200c105580108940000c0c00810810b441d8040342c0c3e000709036841a00e01181e0b502e40d00101054100c50440020b08440c0402802c0d8a040c4008c5100c41c2c100604803100401601c40754000d00b80105c080d1400c0d9a000002c9803180d546840c05c4000409081c090071000c8070900d280e80912900c14002c188c075140340c10808203000311522091103003c460030405503074004006440031920000400146000304a0101701c1c00f01549036003000f83c00d0350007980240c40240c2040084030965a000070301000640d50600d0016620713660900001d001d4100719074020401040001405103049021010f1400ac1e4080d40940e141e07a00c4e202c241815030700c0f840040e040070944110000d0082092141e120001c2401c20700c3c0e0000e06004000040c4030b2a2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 509867230 1250 509865980 509865997
    0xf090203061009031a070903082a0f030d05040c150503070f08070e09100801060b1306230313080325090506270316080c060913050912 59
    0x69000c800c000e814901100ea2403011000350a000c1421800c1d5110360031900c0c010040c0c5100c818151010401c03981c0300395400b200440e00805407a031070b00b090a041a82c95000440349500e00044009408481807021400c0c1c02c41c0407a010065142c043c3c901b0269000c0d00e00140159036007808004002501107061301c1c0c40ca141d000643d07135995680b90052010f4210009807982c102005841e80c1005241500312040c0300001a044503032031019030780c07464929961080c0f5001000c01e035081600010b01d02c840d4401908220241444207984103880b041d0407140d0380320a102c43c1b0f4020a469842002c101000d00007036400ca040b01141005211007912110724503841070b9084900c44031004078242c1c101000d10542c20070074211b032a2900c40189080d002517042d0062041c407240c2c200c03902098888030102c002112140040240076210300f81c03049111380c4900c100343d100c1c000c510700406203401520300d0850211000394000230240b9542d1140c03000494000c04005181e040f0600c10003030150001408440507140c0c04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 509868480 1250 509867230 509867249
    0x50a0c090509360628050c030a090221070e010801020c071208040f06080f090111180a0314010c110a0201050703030203090a0605090f0d031a010f0c08030a0f240317040f 74
    0x4a000100245e24001c41c0c1c12001c8409140006021110710b4440c02c07260020414040483c0f0b901d29400000e02110942404c0c601003c00344007840141440401e4100c11140242000001d50b1b0340c03881d4060907849075403003141c5260021a811301c0480074884c052019903001d0785d042d90600c0d03102c4100c0328040800360402d0b80421040e01c00c000728004100f00c2551b0100b9580300078413451b00000e014804600a9403001003142081911201e12a00c0d02c600ba00021900820010840346000581e24004d02404000c0d5000403e0b0444440c40882d0028000d800030364103075070b02d500c0c002403034030b00710b0017500040e0500c50b9500400302c0001c0441c080e40100c500030041e400192031501580c0411602d45580c05601800b8542040340c0122243c0039812071900d01d14080c01c0844c0c3d1034450400880700321040c003400a0030000d01100b03001da811032550021760340c403640130f0040015211102d0420120b14490603001030008043c442880050420540d03c002030080b4000b160806848805659514003250030220a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 509869730 1250 509868480 509868511
    0x60f020f0d032c0a02040f0f2301120b0402060304140d090509071b0f080f03150f06120a0b1201140a0506060f04150e04050a0c0905093606 61
    0x410080800078003401c00c0b03c0000d1075480f200104482e8582c18034070302c00380c0700e1907440c2a43c05400d8850f800c5801902100402003080301144401403224648621100d0710850034040040780d102c0e8003041200700b1940102c44a0310b140c0d215820001c041c0c0c00100212040b160700351502000c044200054006041240c990101841c2000184a42240010801410850360001c0c600f81c520301c1f51900f10307400d038020460b10255144c9080c903480e548511981c03606010307400410021258801c040044040ca003c4034000f800004900c10010a401114100c10003512118041450b86000340e20080e401280a064100700c0c0c1c42d1002030908480305a11004c0f400441c0034100700441d00c4a2003002d0b0300600032240607003030046010310700c00c42d40614055842043c10200440c80b816018121400801c60002c0c0240498501512005c1c003420072040ba04021075400c05000ca080c2c9000d00078588184400321040e800072a581c044241031030044014000700001c0e103c080d10000e401404907921460364440c02080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 509870980 1250 509869730 509869751
    0x41707080a0609052d28140712030819090803070e01090305060a0914060112082b09050d0809210c03030705040806070c0b06060d0b03060115180f060f020f0d03 70
    0x900c6802c40b050711b03400308420640c2854452540700e034104290484a00e0060440800c070300791816031550803075022000031801250030503620906a5216a00c900d24204480c2e5008440e9030a481061000501c043e5080c00010310003449000101501a014500100f009540e078807a036044c07800c181c40d1005110340741e056090500a00c943c1c1d40418a500000400c103661504840602c0c42215400050204500240c005107160440f00c007400040201c14080055154002c0f10f90300402074018200c07078034082c2848812200c0c1c0035004144c86003000701c0c090700704842105420050f03440d9108100301c09040501c140c030142d41c03042016621035402901d07042d582d1801c2c08219454030100600d41c0741040148503c40e0001402c2035401c9412107815523651703403200c034034030040030140c020005000d406104501c0000340c4041c11400407400441c07607440340c100007000e611043c00c11000b1130042c0601d092840204215030740c800c04003050b1550003807054500c0c050240704200d090008118420001948075048840c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 509872230 1250 509870980 509870983
    0x301140a02090f010c0c09090302031905090109050f0a0311030316080306010809070803070809060409090302010603031b020303180411070c0e24010315170102041707080a0609052d 79
    0xa4508090a24115074017195a44040c0d40070705006110000b0744581f10202014020010b03195a034810030701c1c400700d1040303281d002021500940c0340c19000505242001517581000300007060105401340c0701c1c1a080741540c4400383e015145411464041c8002c010049510107031307035500e80f029031189a1b641c2e40d03030508500060504801809151644c0c1203c2000c10107110000700703d0314051b17032020303515480b9502e100001d10b6a0045e5841005080e0900140380700300347e4103601c02415244240c0b2411500300001c0004400640100802034040c1c0c81000b04000e42141d8400c0c014141d08001c0000c901c08144401d02e84003608403401c122001c04491105200001060500c1503000c010300408034000000f001c030b00e80c18850302d4082d807030515031707200000001c41c08520b01c100b02404980c214105000c1e04400418000e5100c7e10915500769031000041c2c0f80300c0700c00f00d2046d0480c2c4100000b00f41081058588100a2a13440000c0300e0500c502129040c506c00f0a404c0d203402e00c003240c07c488000900301c01445 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 509873480 1250 509872230 509872249
    0x804030b06120a060c0c12030e060f16140706021216020c09011e03050303010f091b020a122a0203060906070207140604030602030f06120102041a090301140a0209 71
    0x2148900c0c8100c8282c6001500014510105908580c001c80c104001d04001d80d2101c5a040018102801241c1c0c42c034030b51074041d0048018441040100c031501e56488105180c0c21200b65003410600208484001815100303000c2504c0000489101b14034240d955954035040f64004542485030400c11010880012002003003100d04d2013060001c0c0c1030030041140054100181405000940035081e11040c440000c0e4500610107141c0c003008490356541c4859168444403018400c2950307145c184039a10841c4032442e0213034007221010350010030720008281e5500303195103403440d00c890400040f43c1c0d15020004a5640001613024090617104401c4032600515007002c00088c808041c50384500140f0661950001d130640c201d8406010380903409020100081a500c55580f000e40001d00103c24490000b07603800104c2d0260204807080044540351903900c034242c3c0074522400450111105a01c0b0070343c8420f00041801980090002603401d0076901c44200d40a01070329494072856000c1184034036420440b905 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 509874730 1250 509873480 509873491
    0x21e2b0908070b161a0f0108010c0e0d080307050c241e0f090c062a0a0b0a02030a0b030129060f3004050a0302010c030204051e03190804030b 62
    0x50320a1038209803c202e214468950340f107542c03460107164030003070154910342420341c0d0460781c085940030f0a04089200703c0000a0080300101d520f01207a4804c5035005180034582080040e1003c3e80107041c5494407100d07138000810400a0240400ca010b0f1109401e109021507101d404000d40112143e09000c00b2407a03200801091101012500800400701e00440e0580d000504c6000c0e000705940b00b2501609050b001340e0140e80180c004548158a00384880084101001c1061031090700148014110303030303c43c403800c1e014060120303e00110302e6405040c0c0040d5400041d00c40045028103042010908441521422034210000f550042a00345205604000c0680086810a0906003400040c0d0314030b10507040d80d82754000120040c1d4056a10052804400e141c46c44848407071481c107030600300d0b01c8040c01e80d8110b0040d403800941d0002c0038000e1080c2c0d0140c69002e005030302800c1510003680e01010519107200d6040c4695098503815420f06001c103541a403003146e11a40700c0b40783d46040c500143c8042e20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 509875980 1250 509874730 509874733
    0x5062a03060f0f220b0913032307140d02010605220504020f0a15110d14031e150301230613090c060e010f090303021e2b0908 55
    0x1c1c4a12662038400c21418008125041040803964400040303024103055041c10b0040c2d900030a81002c01c03001c1e8804800400150b4440745603a680900d06218803440110003000f01d00c66165070041000746034141c1044607003840c0c0d0586454110f44403015101c42c400380d044083d41c00710101c0744480d41e080c01204000d140c1510710126078900c51a00b600c001c290616a251901d50702c800043c00d65951104079203011074041e0155003815142e0581000d0626070300c00c00d002107149540c0c9107040c11400a600510340e8881d680da00031554100c1c20300d81941e4000b0301010000d140011100080390001e0181c0c60150040304544040d40b1216000d25094445c1c04030707050b2001040749101d5810700e085103002075100d82d00300d903501d10140852290100174070f00d039040540041c000040200d0b6180c1c00013000450420246c0301d915804c84680003c07507207528240001001a0090f403048640e2041515181003007a0f00310741520b4810f0150f007041588004900701c00980c6182550803010207917001100c1d280074180000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 509877230 1250 509875980 509875987
    0xc06070b0a0e060129070f080306090f040b0c07050f0d02010e0c03030c06071115090106030314031302060a030b03011e060608090a150b091014010f0e04051305062a 72
    0x80800e03007005c100f03110410141c1c0c028241003001c801d90211100154440000c40e040d803210b04000c1065041103030103d004e1000341000c00e42c0390400c180c08510855000341d0214503035860a04602440c0c1062008540502c207012101c48280380a01080740e440025030b000141e000a6440118904031444805038007035002005090811940070400c664004140d04020205021140c1e4003858080d01c007405100204501c000c3c85002d030410340182044034000d5692400f400942c0505212900c0251012450608071240701c80c0182010320103040d1070180f5040c00a2004044404a401c0d00c0c070010302444e0f59443c038913401c2d040c40b00c144188800b40c0b00c14504070410345860315100c3d42c1c500b03c8400152550703211a500b0941c1d400b00f84c000e400c41c180060202081810103c0140442d000680141f1401f41d80236030030100c1651040086104910300c0356181d43c024408202440010328020b0f00c103034019060180c1c0040454000c00100d8040c2c80000d581000907a00440c80d07500c0c0d00d4441d40310820803803081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 509878480 1250 509877230 509877239
    0xd1d011a130b010504080a03030b19151416060608010c08220615060810140303090d1109040503130f0605030a021309050106090303120207170a020c06070b0a0e0601 72
    0x119600d08041c44042800200d603110b150060380c26010366802003001d0702c03803100030b1420107500d500010035140b8252580c0444010030b0144602c003500034018500000160345003d000f05114400c0301324001d10f201e6206c1d1412500080c40408000d110405558103501c0340300401104809104000d1250107a1421f40a541000440c44e01c0b2100c070b03480065551005800090288001d650000034031081000740345d0107071a61040301a00c00b8004540401c104482c0c0000046c03400300082d400f00d140300004000d140390001c0d107002c003c0e03020300310402036407a5006c034003480940361158002c0b0780c01640942d0003183c5036100420070b05070010440d080188680310543c400c10100390001d06807904003070016009a00e5a000240030401c1031100c0d404070820310f0a100002402c140c000c80c000303080e00d020390f0f60001d000e4a40442202a0700c240680240f6000070a84824400c851000182c11598024415a00d00251010001341030760860300c0c06681c480c605809010001c4040d228502403100550090101503241 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 509879730 1250 509878480 509878489
    0x106140904050c150904090c170a0521090a0e06150a0806040203040807051c1416020103090c03050145080901020c0a0905010806090f0703170d1d011a 66
    0x2102c50b080c02a10019042000d03011a0400d841700c01e04050010464007082d070400006040035889400016045503032503c03543c400100701e580781b190300900184400c10040041d42007051100810030004d0304207104a208035518010454020081e080c0d1207522400c11004000041001140c618020340d41005001140c0383c0180c6400e03404881182d0050f181d54031814813112911a000004006010700c1814881205402000e111f00d0a0117956181191380207030310825040c842d40b0703241001803c545410000561089c0c010a414a2007000554403d50784c81d0788003800d4581d00940c0e4900c0ba5007400450500e008900360006041c11041d036002c45424206108203158064010081c0411900084410180c0d0003004065000c80f0090710f41c40c04103030b440603820000d00e028015403a460091502185a03503030009041c4226074038038400741040380c1c07450f82e17824a1808416030400502c58144082c0b4240d00c1184100c041c100208440328140400f05003105003102d40303c138491048030707003c1da8545072203444 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 509880980 1250 509879730 509879743
    0x20d09030b01060c11100f032315220501091808030403180f0e0916030203030307231903050c1c02030903040302040903050d060609060c3002010614090405 68
    0x807035090420600308503080c81884005114017030354000c101c0a40402400354000a0030030211800c1e54100300005000c0020284942d1300310710189501c0d0040003040f0940c40b441c1c00c050051800804d50035481c58585103054005419420f88429541c1d900d00420446449009400c0310201041e50f40c0602446030b40c0305001800040c0005d02003060b440e0310f5849500a40d106600038203603416030a00442e94546003140c6142044500f0095402002801d1085e0303031600c03945e4001d8076030040185d41150f8900008030341020381034006000b4042d951407141c4140c2c08650003000611a064400c2002c00f0303041d14041c00b41d46d8060984c4400400c00c02c4103000a5a10003440007082c07800c40030251356034032407152003841c602450304003a621905e07001840c0b04043c0c00500800c611115a4020312000da950001681e14028a2180a0121b500640c0303503070000317a00d901c0300030440d03001e403034444190b03180036240c680c005150310307200b40142c0c0d03691009004454100030a655810004c0310907103a60b01e416030f82c6640f502d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 509882230 1250 509880980 509880989
    0x30303010e0a02090409060203100603110403030519170408030106021506030706050a0c060c170c04061d1903030908250308091c050c0901080a0f120c06050a0507020d09030b01 77
    0x1d90201e0984c0301c6a49a80003c071445800c0340b0700751346034140640303403d401e90700d03a120381004246400e114540c0742d000381c000d07102103a40588802c1e040c095014170495070100423940000811500c8402c0040c900d4542c005240110301509415480703605294010389070a65420050380281078100410009940025055045d941b07240303000c80e01e82402041c1030b6240090200000d003078608117170401e90610792111005182140b400a180d44903212407203c000c0c0c40c421405400700060b0f001e0f940d0b01080944110f0910495806071a400b001d001145003847c400c28030b40c104400142c0403281c00c11050904011200c46440311450280401450240242c86a5141e10004100b003101044407100d40e6900c03800415203c1c0c4807016007241440c40e2608070385941e8406600e601c03841584001056000001800511903644040c1550b00d07000385441740712560400120520800026840c488001400360007030324001d0014500c041043d042c0404040e06201500107042c0800094a0080000c106807514250448 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 509883480 1250 509882230 509882251
    0x1050903070611010e0316061416081005030a030e0907030b1809030c060901060905010f2610150f0e040818030304120803060f0103020309030a08090a1a010311030303010e 75
    0x20314292043c2805010f500b801489180800301d000e0500c0200d86020801c4544150002c20244c0c042801503401000300b0b888044068420400c02003409009542c241c0c2c0002c009804031103030564a41c0040d10f84030000a046001a42402059180e03090044910741c2220140c00c1c140001408a8080307000c804c00c00c81250300d25030810003c200c80d6542402200c90200205060b94039624000001e6406095588110040783c0d01e06400061091145404003042c1d40700751100c02c04210141e070910110203a8050521000e010300d2360b0b020b41541c803504c1000d082c0a55113035004c5010749844028102105154000d81401c0c071100c041000041c5e0b150200c82a4030018418044118548004203246001c0c0c0e4000940c00326450320282c0034020b48102452141030120b41c51668240c1c0e1200440c01c2c1c1c001561074008076070040c020601128040c490660b8844514012030f1512041900c1c0c190303100700c003245243c0e10000c0c42d000500900c080c8800c00b128030b500907002103180d54035003058104890001000c05215 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 509884730 1250 509883480 509883497
    0x15170108060105152d071703061c0309051e1912020907090509040803040b0901060b040501030b010c0b0a050f07020105160813140c031b060a2f0307030e010509030706 73
    0x41052130000c07140d0b203c2005503100114010300c01d841165407000006480d081407401c03287c0c07644e813440e20860380b0425024000701c03074800360038800104103003a01c039045080c08140d80011803030340c031000391001401c040003c07100194211001845161255180c0301c41031140ca075401401410700191500c010140d05542d803080c0e603030300c8a00403140310159810940d4810085001d00c414010362102460003603008882042e80c9071246a034081c01ca42d0b0714403c40e41d1866050108004030741c043d500a201e05081030411242c2810309994802e20350344121170265080d903481c01408018080e154030310368080c130341d130008106a0525071942c4222801e800201c5041044810000c0d403040500e807001c11100d81e000300c08090311103c002c0d4a039228520b45172550b001c0d120380c2d13900d12604410400058038024007c0c2c030951400302440c900716124540400350b00e0140b0081949030070242c144041101d880c0c09280081d40c0c030365440c2c0ca0700411210007030b40316a0400c1030a008007070702c031350700812104104c60007403c1042d032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 509885980 1250 509884730 509884747
    0x6090402030f010c0e040c0806010806120c09040c091104030c0e0c0403060203131b03080301030803061f030f06060c05100c030b03101d061b03060a1517010806010515 73
    0x42d06584020201c07107035007000d407180c01c0c0c280c0181e03048000700c600f11002c0c03103041e03a1883c0451b0800c908541490018001c040443c900d42403c003000452056048241c442a03010390011580c030540035a030031141c40d40100400c011020b028440c000510f44050160b925062941d11001060b0070700e405041d010340030311004a580001c6401c201c6004562005055481e4540813941c0c030860740c80fa40301540e55041140e880c0504460102032901981e90000000e030459085448000040e00010091070300700302400c030700340e0010904025040d0404a030340c2d404500c3c2c40410506400392a01c5d64007800030f211841d4001c0f00040c00100b0b007085a0803602800184210218008801410000c48201d406000d40c213091803074044940c0105a55101038804030a10701c80100c8126a05c103411905000701c1141c50324458600d100000041d41c108100610703c3d01d107980c84070301600b90103000f50020804a07003c0b240b010451041c040c1c900e030061004a010708403561500d0040b0700e440305425020340384008000b50b0a01c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 509887230 1250 509885980 509885983
    0x708090607050a021501180b030304050d060f0e19060f050c0d0b0a05090c0409270219050604230a180216230f03071a0403121509060b03040503030609040203 69
    0x165001c1075050000406c0d6591610300044c1d030075100030740c40f03503c4c205030074a101c2c0e0a00100b1501140d00290580d0211191a1039020040c120f803104444400d803540b0310308009000400c03004100c120701c8100c1c410181e0403458900c04070750744448280c3c02e19046c0010000b164038050192001e00929400114030b241250b00040c4170403c083e00f02030b900206002c00c0c001d000100700c0290013504c41c0c40108102c00d03003854042e9030400181000ea0036013820325079401c40050a184a0804104076604202080c01ea2540d00144003074210b5048215a000e0320961900005201d503041e080d14901540d4032a604c0c1d0030700500e100c50302e0011048655081c0c00046e415480404007114000190308460407008821b084420003c134042c0b966408810fa00c140d13030104040d81004411500c000d60f0021640e001c205514040700781c0c8800c024410350502c0006a00c28901c80740a014032003034240c22040106115050100100407035640d508002202e030000e204100c00282c0010460317812120031034181d2007551700ca10002e0b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 509888480 1250 509887230 509887243
    0x110306090a1b0807360e060d06090f06140a2307031d0a11090f0c09040c032702090a09030503011403011b0f08150f0d06021b070306050708090607050a02 67
    0x1111191290071000717502c2401328681c854280c0440f04032540ca9070b84d0300211070260180c41655001c4807100e003d03400500c05610014280b8400c0035030700002402510703002c080340c9048602699260005007040342458880c46000703080c0d6403007114001c104042e034501c03141c1c8100040540c000d140ea00c5184082d09051007806107010707150101103078680c10162800c1281d1a4003140c0c002d0042c200702020403900080315030483d20442000b0002c0d4200140f80381000050141c19024200389541d40844180041d88241d4800d24900c10080c0d0a0540c10742e0320510a070908004c00350f000c5107181482c90400039501c0310850303044801d1800f429480c5491b40d400a8010710043d0061403100d04085100c841d110703000319003c400081c0d503454142580c2d0b940c0c454611010126101c55074443d25880200d41c0300e01e090040010801d000b00c03001810107400c0c1b1a180c004c40705100501106901a9100300100704190080303a80c0440986005505401c0c0f1040d103503034030301c0064180740c107000300421042c103154401c00c80d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 509889730 1250 509888480 509888507
    0xb03071b06060b0f0c01060504110a0e010912050c010f0302160b0903041203020f012a0f030e060703140a0606020d080c0c030f0414090c0a050702060409110306090a1b0807 75
    0x541e549850b40008800079074045c113284a071550030010001010f00d41803203107075903404401076218504002010112100314240b040d81c2c0c140314284030007280840b28903201030031062140c07004200c400a203000140000c4680d007803a4040600400007007141e000e00d030701100c143d00c0e80800e021441c0e44500c002e0300e042d80501d07007040405002c052950343c18140e00140e054250189071001708031014003803aa86c4440c0d07980690120010304014002100da620038480032403c200589030000e440459894117501f4010292900c00c00a600c400c541da2034001c000031802c0d080f884d1101c04100c1c1c40e24001004c0d48500b121020350040c8504000081d04000405080f00c41c45940a400c3e25500e440b09041c40b446504140034043ca81c0c0b24003c91201c01d810066100d41c0520710341c0c1546410405d52000072203460380084003c0b0380144050000146188641c06a2403902c0c0c25041080d880c0e2601d00700703110b0007040081c002000b00c2d0620032201d1901c11108441c2c2c1240310b00340392004086d85d6480065481180204a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 509890980 1250 509889730 509889749
    0xb0102030705060703020301050a0f081b041b090536070c0b0406050117010218040e0a050a0b250c11010519090f0b131211090103080705070b03071b0606 67
    0x4204c0482c1d031690043d8180c490807107820169603110b0060351f0701802180542c440c0c903403144583c004200040303a941c142048000b000400c410841c00003415840c1c1c51010344c0ca0200303507a48824807551a00074001584041280201c00107550b02689250800e01081d05107503440130031401041c4200e01c6120701c542e01035006a004403a908062034000e000341000d11544d00c84500503107860300291018000c9600c4003000b860441e03814512035003040f0041038124680d595510851050380c00243c000d00c500b0788002c1c081ca400c4101450b00e6011420356800e1920441694240c4060001400c1d401810160450b41c10021994030300410200684042c0314203040050305000811480801030b41c0400c000e0b05440d40110401740150f038a0042c1d14040c001c11500c0441c4c0383d01181d0502621850341c40c8900c05901841c00105070105000c0414091002030300f05039035000000880c0c20500c0800c10210000b82428009585103242c400030080c6402100c080840917030b005140040e040c80065040b25001d0500c000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 509892086 1106 509890980 509890993
    0x121509060126150702070906060305060415120816080f0a0e030303060a120606030803010602030a020d08010e060f0d0206030a240b090d030302040b0f0406031401180b0102030705 78
    0x180450304600c06e04078000303480301711405140000c0405480002e50303810f001090006a40c4900d81c601260761000004001c10a18124086001508a0009502c850352031124507007174200010301801110703002c5820f141d40f58218004101d2103955891707004602c51030b41c041c991240011500503902009141003003086079501c506011030a88604000100652269102902078100f81c01a41c01030f4004a10420f190b9010402400601e0383ea08101419603d491424500740710300414090040518400d5200b540d101c03040c403201e95035401070980307483e440c03c000c0038070003046e82071586100e200c01c0201d425010a0b12840240070340d12403000d01c501d031580a2052001c2c882d0000012000c2607403c010000d050b02d034020181044c10460961165250700c5c2c080d0050907101004000e01c034480c40c80004000010354a0400c103c0c001503640003054140386000180c0c11805095805001400b642c2c = true := by decide +kernel

theorem cover : BRFrame.Cov 509712230 509892086 := by
  have h0 := BRFrame.cov_init 509712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 509712230 ≤ n) (h2 : n < 509892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
