-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4561
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:00:59.09598+00:00
-- url     : https://prove2.me/submissions/7f26b5a3-f0c2-4487-a398-78b4cc15e590

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 820143884 ≤ n < 820323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 820145134 1250 820143884 820143893
    0x1d0603011d0d0e060a17130506131103011509020d02040b0d06051309081606020918011401020f1506030f03040602061e060a030b19180b010f0b0a05210f04 68
    0x40f0741d0b8510034040d00040c4502078086801c040480c4070f01605600b04106a42da482000e40040c0d01f1001c0907045025150a01c007401030700d880702e405403900a8901305291401d0506041c00c0b035139441c00380c50112105400a00121045400a0404081300300300582040d07250007600c07000d42c0c443c0014840c45031b900d400401ca5820414183c243e002c1c1d2302038042060300081e464425a51142d85548100c440c0952081010000542c4c1580c1c080c10015010004000c10a41c62211002007030182c6100940c015216144035840041d018032401c03801c00140034000d20b0744102c141c0c4460007900003541402402c1000841d5082000070f80010403083d1700500143c02d000c0d03e281e003150034600c40241e224030f0140c100720050325a1700794241220b52100c104002c41c0d072060041400d07504041d2209501e5414102c0036403844c80380c003200112a03800b580350311a160340d840c010b0703400d4030303910f485000c502c100d007441303000c03001707400340020740080d03051401d15110800c81081d0310380c0720302001c95442c850a08203400303200a00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 820146384 1250 820145134 820145147
    0x1c0201030e1203060d150507180f0b0906280c0b100b092206030501051512060412020703120f0807110a06051003021906080f011d0603011d0d 62
    0x9511501c06401c040c10440300882240c40000d003031502800b000e105460800001600e040b4000064500070407260030540320080c6050030900c0c2407004145441d00c0803d08440c0c188004003161110114203151481c00424400c0c607402c074000c2c04466000b14901481309243c0100c000c4000c915580d41c80d90091140d14003c66a0500500750b0390810740a010b0500c110401441110000d07a4200d4072407034008451a80d2030f10300903149612902003030030980000708010701500410f015080004480c0303004841001400110705200c58441000d6109002042c08030ba290968800040e0307480c8142c1c0c2c035050f107076242e08400c0c119070101e160001d050000300f1407945612048030341c3c0104035443d00c3c7d030408222814640d91040f2500024050f03d0b942c502082c0d8021035441c0b541c009643c0580304c440c1d0388100340988101188144203980c081841340c3e0014801c1010b01c05d00710f068954521200b2004a65040320340341c20200281032075010340d40c90a02c884010003020b485040030000000400c0740640c10340000703048 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 820147634 1250 820146384 820146401
    0x40e1008010612080304050705041d010e0d1b170a0503090c12060a021b010f060608070e030613030507022e0305011a07050703060905012a0212181c020103 68
    0x641e450101c040c000c40d00042c02e01202c00b0740000b00b490b01c940320b43c10b00d5820b00041d540041e6005240400c01a0b45605900385140380080160081042e1500c1d440d49944559a0804c0e0200003442c54140c0c8010000d80100c3e00c100c036010725000840c3c05070401004896921184580b0003003103011082007812841082031110002040c2d90005000c038400c01c1c1d6660b550350140c9264000d0744c000c54907001c1e6200414005241e4540b14000384602e1038012105030041c0000e00a500000303501e18002507026002ea2801000300002800812181d81c401140384d070361101c0c4110031030401c1010400d01001d40d0b504449040d855245039021059a00030200c0003481001141c864030a2604050040010800c0e520000006500100e05c250f03480030a4035103c0d04101098000822403841c215807517040c000d055000d200e1403420040e41d11041c486110700c85050010300e068440040e441820782c01005003001c005041d611448903110080030b06880c000a055034400c0c04140b03044240b695418041d0369150040042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 820148884 1250 820147634 820147649
    0x605040c020c130c030b03070f0602010e160911071514130503090d11150c0d0504050d02012a050c04050c0a1b051516120b0d06090204060308040e10 65
    0x401d101031000c80c0f40800c24000450a0b04d545143d25024a4000c1e0400071100308010141c0c1c02458440440d8521011140206030040d0b10f03102038480d0301c03100080c90281c010b058071041c449152600419201624100d104038507100028014000021041c0941001c5102100d5000c80d65a0f90380c0300582d03009600810724030b039200d034400195000c05d1000c41200e83c000381c1540c0c10074061101d801c1000b04414066000c6820805602c01d1540041400002d05900041c80059404002404400700c945000b240a4580e100082e0100303500158040d4847c06022107000d200b08010b001c40c111203803e41c1c0307400481030314103801840c8212140d24040c42001e0f48444001001400d10b20000d200800c005010b0f004400c00c010041c0c600401d004041024003601c0c10008807086240c0307020104100b03916001c00da404089083c1d081c40c0304420260b401001004240030340b000902048a0304c8100140050403810782c1c0040c0c2d50000030002c50764200c0148050300104800107401d003000340300c08111500030380c071510 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 820150134 1250 820148884 820148893
    0x60e030d0509031926180f0d0e0a0b1c0b040f0b01030605040203040519210c150603080a0c02060702060d06170d0c11030313080d0201060b1303030c031209060605040c02 74
    0xf14040394a6982e28161400b17034000d07915a210364228101c240318005580daa44565203040f0200b0034000b904061155581d0748066060295500b03200c80c02d0743d24040e1030800403081c0084480081a032454003c0b00c1c11080d4080703034012442002c01c0486d80d0750081e171702c00d8503103032144550b6030750b058094078004003c292011031440c0f4040e03c0382030300d464005d2079001c131042400d50141c041c090015a00c65040e02004440381c00c0004142028050340c02c80c500441e80d40c01080d03c0d000c0c26032030600c11202100e41000e001450320b04064003c88c3c982042c00c5c0c049a11a4080c03083c1c8000d0303181d0350080c4c00402c0408400050031070a110041c1030004211005040350f9100d540b081c600c0701d510051000400d41d12412580040f090301d00040e00318062001d6031840b0320300703018000848040c006121042d00d46190020081203460301c0d54054144103240d01d6050300c10b038107102013002900c04d070300c5040c00501901d400720074586600d19007010703a410104c0507165640c445005204600e428451940d204041c0d00062 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 820151384 1250 820150134 820150157
    0x31e0807091e120302240a29010e0a0e04050d03051605091903020409061e0b0d1104021e040f140306060d020a0f031401050a0506010804060e030d05090319 68
    0x980100903600030783c00726080c50499481018002c011050002172981c100001c80e58072112421032152044540300340442c140a508050402290b4000444005009494064611020042d0703011410b008510b83c02900401c2d0024019002c3c904582c0038034400c1000e48006d000041c1d000301926409054031040716075500c2104800d94202d01107500e011800d8500341c0e83c01603070b00c3e459044020968070181d00641413071075080c20400c06030f014954905035248a480003181d08840802225002c140c1c1680108113240d50001003062402c480d142000014405403401e48000242e810f81c0280c0e808441e20880c02003420b000d040c500503581006001940c408035840041c0000181e56250098409409411001d908409544514410034064a00e9020203084240e491030a90a004e1104204403140d510342004201c1240860103804d001d042c05942e294820744560b00e6400042c00101c0d45400c20384010045441c40c500d4038024a4400d14034400955214520080d000b84c0c0110518655010000c07801c80d003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 820152634 1250 820151384 820151429
    0x18050a0c140d0507020c040f05091e07030609020d020301061e0902031b1e190305010504050609040206030a020706050f06100e06040b070c08030f041a190c031e080709 73
    0x40d02d03815500038402041903103d44100340e003006050707001c0c0380e0854101340d411500036001c0d03041603014080480c2118050003c0d164a404e01c1c100203d051180c54001440c10400305455810031061280002c00c9415640d199138002400c482032580291900040c3d881200f0541c414068040c00502d002c04041d407941c906a0300e50341600011421004c02807002203444981c00064441c1c100d1030f10003207034030166914170004840c44048183d1a5801c0000d052100100340c0b800c1c507001e001c2c00743ca806444840681c465608000326500010100605103509100340b0000c1a400c0c0501f90240a0b208400d10140c10102c083c00120b01e03610800703105100400001a400d0b071580b00485007111075008200c1c0e1180751a00d0442455201342d44581d4017172102141c494081071181004200720b0744010040c80d081041c840b0b4041260007214000102205040d68a100c00380c0515211900b081c400e25040c1ca40390200340d4103d001440500480000909171010491103e0300300c41c46602030006d40d0000c91098492400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 820153884 1250 820152634 820152637
    0x60b130c02060f070e030601060201020d061202060a0c1e0b0a050708060f130222090b031506010c1a090f0708070b1603051b030d0c0503062818050a0c14 67
    0x10946120060004d81944c2c49090a080e00c0d500c001c00782d507015603450800034003130340145005104092400000240505548003042c00c1941c1c041c000c9400d0a001581c140d0b82c0c401ca408050300e110071078501952006103804e50b041421403040400d60725504004a951048450050070340050201e0b6005010152b40c44106120181004884920400001c1443d80c0d01a0040382c00d209c026041c88030020881c000d2281e21401914401c150400c00d02d924401007645d1201445240d20840355400c0201e011548074450894081e4084c003000504200740240e48200c841045603a24441d41041030808808032007404000001c0004000411445083c6400c21030300740b00e80020400000c1822844004040c000d5040d18251065071098900000303071803032090703141da0004d01c0e408030300c6140c45a20b00080d07000c2c605490180d003000e80140c48a11a649003042e249861042d0300d400304a00303800011b440c500d4440d01501c203805c6c4040200b074605205403a0300c02e82d02006580814044070b440301006006040c0c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 820155134 1250 820153884 820153891
    0xa0203071a2a0d020409050f06060304031706010c14010f0e0f03040504020c10090f12020114060d06090b0106051b0c010503190e070621050c0a030e1603060b130c0206 73
    0x398004450072240080c20b00611803240310114030741c00802c2c0040d440c1500d0703010500c41d644401c40280641d031400300b041a01c0c17000310313402004543c111004141d485400340c3c48662010041c100f914070180c040d10340440d035480790b01c41c48203180e440e0420b001440c0454001d80301c00a20300d03802071940c640e0020303840351240154014940a1035022524a03884013040208108081240d4010441001181030182030740d055035a0070340d00582d81207440d0400920520884085404004d4200302c25110102004082d0840074815200c0f00d440b41e085001050046682074020211512419560b010203c00801d036a20b0240010b0752540018604810030b0341c00c441100d03440903446292403000d4400c8142000100f108403071002907441540400300d0019000b8a035514450b0b19038088900a402005032042a280215260b4559540034005646507900070b0700312800c00d4070420140c0f40d0340c007211030348011051981c0c0d00c155080e0307441e041d4092007404c2c81402003c9081d4100c109005e464a00c4c0d60180d900d103c0907 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 820156384 1250 820155134 820155181
    0x30b01140405240a02010606020d05030105010801030212150f07030c092d080307050a03031d070e15030a0507050a060206130807021503040c05030f0708150c0f0a0203071a 75
    0x503281d4810308600701c00e41d0358420303c0040b0b500761074101d2940000d0003890107000f108054428450390b06401070190069a040319816903c0e040561709503030900561040d4000c01030f29038481c40f0a00303001101500e04e41131045040d11400304141c5014000281500c0c40d00c07913481c0074041402d1091084d2040185042c864140750345031322020540c940704030428030205900001c4940000b003015020410007090081481e40680e6003880401440b92501c01c01303502000070820154030001c1d00f04002da010003042580104500307551204e040444000c2800d01c420310000301c84c1604403040030710082c505051070001420883c8000c00c100e2a00e4404450005c06002d07000d00b403948089a0301c41196101049a28400170b01c04e0000d4a0b800d040c540000c41d0712042c041c191082c002c105080310803120018100007200d41d0b01c8001c4c401108603480ca5008600040d00c2094004070030003403803034200c90320001000c0d080500d50086688422a04084010146151005480c08100010300040059403c6045c180c1c03c000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 820157634 1250 820156384 820156399
    0x210203090913020303070b04060f0b0d060c18180e19110d0c09050402090601050f12060a03020603010303020a051203250207090e070303020c181609050303030412030b01140405 77
    0x50507410a194602c0b1200254580f00000c2c9160800580d14015030045100342c4c800c4c020000403a0502c4c0540d80d0710800c050300841128100c1d00425881c0d004540300b030445003010b1201600030b840b4011455415049418403601c040040c0020070b2300c51080d002c5411705000500306591402200b203580f9005284050403880c036601d0850381aa462404034069035611510f880780c3c2942d5078031494060300044034242e104100c80000101194002c10031144400d180101e0f4501e0280b1440d181d0084010203020581c114408400100058540030003c6010b58002d80003040b1091031480c080d498843c400070368213490901801480a070100202c03160308001102100c2500c542d000a50403490b10140d5408020250f0500c0054003031000702151a2082c2c038000c0d401d80300030b101400103011b480004050703c1030708440c0c0000011699051811001146c69081c603050610b2540d4400017032941e002075606654140a40d20400d120581501c2140c034604002e081c2100c905102c484146242d015078410140140c26 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 820158884 1250 820157634 820157641
    0x613030305071505070801090c09080c061e03150a080a0209060d14120c010c180b0306120d05040608280e0703080c010b0301050709080d0e01050c0102070f2102030909 73
    0x10041c1d10030f415250759010405071070264001800110f0a01c02d1034003075898149203030000e9210381c6602066404010083c590074480b24180a51503100d00121400010000105aa00d461502c0218000e6862105e5890321901d088100440d0034401c1e4441e00081d071000c1d004400680301c04050590050b401c03103407003011f007851742010310b130384c60324000b1445140c002c1101906e030310070681c4060000d40340c8410003000b0046592900f5130f2480c3c41c003801031000c1401c802c0200214610703d8000c6601100191001a110603041991032034250f040d5011400310f440030605000f0598008041544080b08089498100a4240d480c60325406c1a040c1d64415036180ea18290b9011010014100295400440c0550320211444103500a0400c10074940c400c0d400c0802064681d44603400703e8090f500c4c04005860002e070480815150712241042040c1030000034400d0388001d01083c405000864011041c40d44c2104c0140303403842c448008810601c0b01a01d41101c80c0c2c0b601580003066502c00764041d180c6041585 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 820160134 1250 820158884 820158893
    0xf0f0403090518040b150108130c03170c16031a0703110706050f01052e020709091506060206090d0c020d080c070f05040b0d0f020a050a06030e0606061303030507 71
    0x1c0c40c82c1c000700c1d0400920b10300f2490500020f580c05100b41e0095202141c240c503102d0441c1e55031454032490078005103844010640400769403022141c1c05e4404e010800d40103540340e48840030382101030020790841c0008690005020024000d02403214903107021070742041d05540e503030801ca8084214080c4000c407104000b5990302d000b640315180352860141c0d160b440780540d140c12006400d0440d0007504076814000001580c1c10054508440003c1561454200449840b5040021120131680c50114450003000284e800454401c00c1d00007401807014156141c0304001003020354806e5401034085611031000c0008190700031403550040446403415450301c00c1d1354000504a051400e2014240d18800030f1004800c400c00501202203800140d0002c1c0d0440d941c40800c0215502d511045810400130920100003c1d00c0e800c000c07604600c02000300d20240d40301c8000c500381c164250400350110340d40b650080301c2d145040084a501503400c984091501016918001c103684e410302c4000c0074000049121020803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 820161384 1250 820160134 820160147
    0x1b0102160822080337050a020c0a09020d20031f03020909031b060c070308060415030b090c04020f1911030a080411060310260718060e0f0f0403 63
    0x380c15004466182911000a952a60f11250910345c84903900e0300a0401107080340a05200c035800c54484111030110100196903690201222000314010801c000020b40e0394840d0071030181c4501e010040c0c44402d4805007404880c850303801c10010701140038100d89580886c2040303d40c420740003044110741c420340c19940915a0080d0300000d60050302c1c102089482e070700020281c1141d008240041e02610485106107032219019201e1040070101085a84c010038000c3d201c250300414003600010314464460989005240315030401c4070405004424498810420461610140c05c22a0114038041031144032003801c3c071505150312001c2d00c801c510164002e0040c01d4a603502d21600003969550320b10030000610410003103030219182c01410402c101c05051810a4034420207410802d100c0040c140b941c1001c0051000002154000d00540910381c4076006101520060074595100c42c80e020000350385000b612441c0d00402071000a500400014116482411b0f0b0002c00808030440c0700c0c1c0326402c08803500f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 820162634 1250 820161384 820161427
    0x509060403110a06050c0c011d3d170702010b0904050604020a14180402151305090112030c060b0612010e04021e0109051203070c08031b01021608 64
    0x9080400c0001c14010a40006040c440702256500d420341c0d02c50310166030318001c200c600441603019103410196940901184c04c6081c80740302400c40b00003403040c00948a0310401c8603010012420400c032130340c95410003000200502201c0c0308500a01b000001c01001c0c1c101e1400150314400d0070501080086000394460510440c000e80000c00358a42801c04940d0342c54143c034106d0240c20ba00400044a00346481c00081c07801c0005d01c3d081c19241c180c05002e164000c00b42090b030740608502850700b6020202d20080549400b00a18103103070610781f4003040f900d02016030006114442c1100702000081c1c0c4001100c50081c0d12200005294400c90080303a80d90254040c807040b15000000049044004000c289110728402c0b00c2050012107406602d2042c00c0580080d079000c0750306c10b0810b11081c5841c440034405050f2100072a81403403e03035101d00c101c1c2500e40d1b01104041d080000c0e110000e07401c4a80e0302d40c0032030540000354608510021070030004008800050300300c0d030010541c0141290210202c000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 820163884 1250 820162634 820162639
    0x10140d0603050312090a0305090613090f0c18080607111f05150a030c2c0406230c0d09050c0405010801060501032421050703030f17250509 61
    0x3440e49a1400d15500d42c404801c080f9000702d81800502a0100000c6d1102c03c81e5041c0d9541d030404420000b03020460300a2284030955480300300c0c0201d0300940910a0450306040d205001c28000b1582d074000e0100e01070340382c0d403c0440c0350ba03400c00c0c0002c00c000900aa0800314a10b400003a6003220102e0606212016642c0e00b0501201d0000c1141c54209800a502510340003402c0d01c1c040700010100401c0100314400103048a84040013002075400305103500d00750742e040d0000c0e091480184c001400750500125406c9400359a14054118102002c07880c0c2c50b03c43c0c180e50030643d51400c0c02480380e5401d010780c11010310702c552900d0055040003024021840c03800130261051201e56152140d0074044c00040c051940000d1501281c404030f10410511701000c0c0f414454003c0f00142051511094a2081c04a900c800e1950344216030003c0d808004000096020f81d4a9124908800200a011002c0b42d546043c58030b9441091000c00c031001044000500c101c02c81c81102015105425109070141d00070507603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 820165134 1250 820163884 820163891
    0x619030c030320030c0a08030a09151505100903060c110a060b0319020a0e07090b0307090914090d080916170d0908060c03040f140309031005010510140d 67
    0x30035800c03080050015400f02c11065001e00c0c46140203a80c2d0143e01c045581a03400025254007103010a4021a0010345000c0040f0701d16480e601e80e100300c0c0c071000f05151451665007030b00381e680c13858541040001e004200c400785800c2020700c0d00100903d18500019204650340c01081c0b903481e01462000c040320b00d94600750f58125205042c5034004002c54400f5502a019030400c240c0c002510405249560741d0040000c1d400b182002d0040d03010701740060802c0d051148072100800c0b240140c002462190004c1e5542c03890351414040b585064a654140c3c2d034400080705001d0243c40200841c00700381c40000b519000500f0341d15450f0807882c0c22045020403000903440e21001c01d101c000c00ca583c0c500f8000d840c08455200000040869040e101e910032120f5540051012902d0088048001d6400c40d020301e0211101c81616140d0444e8840b20b50034002da41da00000c1e40ba081070509114803007109000000410896151801062403d00321a00c21820841c060f44610307840e85503070041e00c212885009042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 820166384 1250 820165134 820165139
    0x9090c05070f140601151205180a0c03050705010306031101230a17010b13120609060501060801180912051308121308030c0309010e030307120e0f0d0b0619030c 70
    0x3c80229540c0024002c0c0d0b0040d00e001007600b16032640c030b40d0b008117520b5407803181010039902504010440038090b00f40030030752078407207010f03043d020460240c80c00c0c003600400c01e0651031881c00c203192850380c1e8071080c14541031a40030000705da840c918060f48003100b07003000722590750080d94950390070440249403614402c002c210300c14902d9010321017591a0100340c1c80328520383d0301e07111249450301549178080b940c450035120621589045902c2c0b8000300d8851040400d41210070f54580c010344c0e009030860800204200e00400c82407101c80710500c2c1560781078008000e440310988600301c100c54250300c0c402c20b0040009030410405403105c5100d00400a038829103400d10000b000603801c1d980600b0440c0c01c01c6650348404105410701100f201c030420008801549001242001500c40d405e4000800781d140c04180108400300c1c45c1c203030140c40f01101c3c0c2e0340d83d8409504080b04004200440d401c0c3c0034000c64a2100ca9400111401011504180200c641c618125201c41404031880003030b80004001ca41d013030200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 820167634 1250 820166384 820166393
    0x80f0c071104090c080d09060201020909161823010516060c0e06180f03061302130608010e010608010c0c20060403020d06050f2203030f0209030708160506090109090c05070f 76
    0x101e07a029112075480703410741c40d2354501c124240c0c0509412075901401300c00115038400480c2c04040760202c51390904181c0e080c0d00b08481403038804540c3c030030200500580a03030701038030481d00300c1402c4000f02420100e040c08000318029107101d206607070003407070b05030b855181d5264140a02294101c909000b0400c907a1041d0350810b0040140e86403c0481c0660540c030142d208074540800c103d0f10130f920b055442c06451100f0303000c10000302c4901654081c05903643c100482c90000038000d40742c24007145000401c500d171030008030508462110586030b0401092060841c00079081d5940e100461460919142c4841e4101c400107080340b0655100075440907294001108000d1070f40c01c264840c45210195910980d40c1e1851200c2001c3c081141c41400d15034801c2c4100024000c0c0c2c00310403030072088480182003007822404a80fa19001e608401c0b041d910110b012203041c0444941c60380540b00c00e03100282884040300c0003a1a400241c02844659600c58800d040c0d90740c0b04205444510f40c010030b1350101041203081 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 820168884 1250 820167634 820167643
    0x90903030e1002090d081e07030c020f01031e0e281406010302010f1b060e0a1704061b14030d050610111b030a0b0115080f0c071104090c08 61
    0x101e11090003192101c02801e005842514090080601958a5498542da0303045a560004409084d4130303e10a04813410340950303402411800d40b181c1c4070b110900145004100980c091840d0050415041442c01c00440081042c00d00c100c4d49141c80224000700c4c1d00c11214141100809401c917005505d980044034540303060b40c4280c0c041c2c0a180c56160f0480c180c00c14a40341e40c02400068081802c0b006511316061080300249144a9008208112840035954500039202c0001c14030215a10100c0a8428411450401641600707564829807825103041005488030f46600c9000001c201c035000e0010600c01c41d24099501e54444405a80c0d03030b52001c9104000030304064541c24041c0f401d80149900c0103005490b01c80f080c049010060805200d41459060541308034001d1319010f020300c1a4020005265030050750107016142d1aa0441d2481c44038001c09607000180b40440c00c80703812040c80402805e000881c2c640341d030068070402020030b2103800f05025015400303000304820344044000654520114 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 820170134 1250 820168884 820168901
    0x31c0c090602030a02030a0503130203100c022a0f030a050d031e05330a0905070e031b0d11120f06010920030604091401020d1413030e0102030409090303 67
    0x300c464425a4448030203c1e941d0040c0d403010000360380104001074455005001540d40100b10503400c00082d035040d40820f0400b8502e00c0e07031110791f42d202c01e4460006501404034241209610829100f8260321407041c0320001c8611380b04501412809460550b180c4041c4021684641c200f0304484010611200040040a54401e9218801c404910f102c2c0c81e003c1c0c0d401494040d80314506001c0010000640012072a13111030f103442200c5550010b07000d00340c1c42d0700d06078800404400b400044e0518002c00e015110b0b812030b241c0103100307800c090400098070a0305070301d4400c011401d4402580c0d1024505d0b04e4a50320920198455105c1c032000140c0c0001d800006803520007400c040c094134041d0341d0300c94821041d55804400840f080f444181e075404041d900f100a142d20078402400450f02e035001c0d0300e1304800401445c1500c805d40c1d40005403040f0a00c128041e00c0c00b500001d04207203140703140c02161001001400c40d001010000300c040616402c2e0310030400d4601420411100300304001491401400800c0440d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 820171384 1250 820170134 820170137
    0xc070f0c0608090c01050307020322091401140405010e01060513170c130c0509011b080f0712020a020f040c031d03040602060a0e0c010804080d1107050606040b061803031c0c 76
    0x13100d401c9103035482002505d024108a40045081c07204c00c043d03880055540b41890010468071500001720a040f6015181281608034203061555051090803500c54201a6407103000d1420320004202c001c00c5001a03904480261602c181c481418074a0307814014916404102c0c1170030a1090310a001c200420119400001200c0d07660402141304020b0041d030740c0045542010807800d004110295000d2030348003480b075000c2c008042c8583c41598072812190480d1071020b104000c0401c406040112400c0610300044060004003088156035000800c0c00250605c031500494407402c40120440c000d4200f02085204140d100441c0007800c0307001a9680c01030300c03c640041c03060501040c0c80318812311070302c1c1074480740901400300034254000555841201034412900c02100700101e0214101c50b210f00d0b4202990041704680ea2007a500303000b4034000740078140600c1a450640e04140c035540e00c0c81220391111040065041000d000000203080d80030702d80c3e4110614031242a848400d00595100c455030f00300d00e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 820172634 1250 820171384 820171393
    0x6060e060910061b0311120403051e060a0b040212090624060307081008060703141e1b04090509030d2004031e0203150702240c070f0c060809 62
    0x4002d0389a440040501c5600c0101d810048074807656842c40c40c000310a54000d00f065422010b800c0b00b0a45044000380640703130003d40108050080240607c0f03920f481c54192034040d00b04e03509040781161604000b40a5a120b140e9031100b0081645454064811114840004604500d00240328a0302c40404880345101e042044094140e400b80d0f0080001601c00b016107000c2c210b5451846c15142d4090103000c150f18142040c43c0050700742001c1128500c81e5a25907804542c0004860101441d00800740003003000d000ca0101c1d03140042c8a0001080e4440b0803184191110b0005e101d02442621881c0c00840c0003904000030809040c038000300a15481110903c20170031102c0007805800103400e030002d0f058440c1c208001c104089105004d288080f00c41c01c450608055030b403980001c5ca0300304001d02c0800d50381022401c11881d0b9405014030032001300d040e100d001e09c03c0440000200c001e440144020210080031409500388401c3e81c440c00c1c4042d41c0202c448221a4075080040c0800408643c1c69050340714 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 820173884 1250 820172634 820172641
    0x406060501080105150d09050a020a03210e01020a031218060902131b080a15060f0e010e06070807110a03050601082a10141c050129030a020706060e0609 67
    0x8000c1c0c20854600d954005175414402e140d203040d006400141001d6910744246161840580d80e403400d601d0085102d10700007807208444c441203001041d44074803000d003800850030b586c5096903004503032203100b142c0c03615101c041300c2005249100109085800d1a860340c148040b09000c0040ca944807120060080303494021410380c00741641e050b04e14140740050301212074003000c2c0209000308040c80c0c000303280310004103080d82c080d034030708a0010456010350000342c590840f070020903401c2551002d8519082c80c10312440701500c4042500c61144850082290400180d44010700000d11143c9140100c000d02c43c20440e607803400d145503101004c1c01800d035540900d4240c0c25a070f6007210b0b0303071036036021440400240d07400420302008180044143c0c3c14040c0010250010710520080c40100610b40000b048130300341c0c10442c08080120303581600800e06050b038222903850716508030340d00d800303014440980e140e5030f80e03881a60074000790040d40340080034a820941c0c04100040000300051090b001524641e840d07a8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 820175134 1250 820173884 820173889
    0x1c141e2b02070537081c27030513031b1202090604180605040503040603060b1c0203091018020f0d020904031b0b0f04140f03040509040c030203060406060501080105 72
    0x30034000000c0031130b40420344c1c503a41c00001031035003920014103500312540d40c81c0001000c075400c4680001101c4101d00055048074001c900d2085c1d85440030310190820400f980518500c41c0311180c808000300d54110b01c1c0400c420188228100d0ba04510070080e05020756540e45060341403081000c3d003580d401c40d00c191000c950541e603015a07100c050340050240446031505001e01005082d6882c030494406d050603101004600c9030b0080c44d0046100e04011035585180c204020100c4509811150440100b0402000341d440004402003514401602c0141d076a125a4810f80c5466007211000e0891414070010f15859a250108021a9402075411807034140240d000c00c0320718250118002d510002400109001c20321800145000c41c0341a4000255a07406031140608c01c40b0031911590000d0040c001c04c070401040d000c6103040000da0130000c186480c1d500c00d40d0342e20f0f800f8500031207006403c4003000074244100d08000b03400442e00901a6481c504107400c060000d0121030003500e0201c6d4154000280c0d50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 820176384 1250 820175134 820175137
    0xf08040602120a080112031b0b06040b060f191b0303140708010b160602160b0a061505070b1b04091a0307060207090b060408010501171c141e2b02 64
    0x200090380c0c81c055660700304003241c43ca008106c48281d04021481201c05400440b5400b0420524007828803912103141840400082d141421a001e0044009100300002c00b200d40301601e04592000141d60301801c80024201c070200d0103a00080d41c05080141c89100345a015440031281c5a24224001e00d45d6452481c182d0f0b0006003031046118004040101e1140034502100620b0704510400700589804142030311500701020000c02540c40c08000c00c02c1c409a40800e208030300c010095443c1c110700ba8000c121015046004250001c3c1c03180121000050800802c05201c0d80c060350044561503d42d45c4504008009280f045032056a04100c041c1847c0f1502d00091600c049030343e03e500070a91207090044520223801c42014680e000441808040b42c503100038043c960190a4280a10181000440f0380c00d1400e0b8403031b00f1810800800186000206500244104000ca201680395588a131849001e0040032420068140c41c031001003504011003d00f101207101c1d0003064007200704134060301100b0100700d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 820177634 1250 820176384 820176397
    0x13050103060b0307030515060d060e0a060302180c09090a0905011505150a0201150806040506180606060c03120a15081218150c0d080c13051c0f0804060212 68
    0x190700e01440000c8030140311b034118a5011011658192041d608540417480315000848400e41c4240c942906101000c070741c840c0c503948803100001c2402800e20303540210b42d07280101d4285102002d000c000190083c0e404504554949a018040b600c26251600c50100101b02141c4201c519508006101c860a001c409200c03083d01c50081c00f010b070300020380c0c1e0f94020326400300302501700395500c2da0800e48201d00043d2962005180e1038000d800c0314a480d103051400c006000304500c1403420004d00c0e00c814418000f511641c0520103403841c0303965078485c4c00318524601419100c1c07a0800c3c0c56408014802e01c0c950000800103042c6880c0840c07180d107800344d080d2681586405007150354401d00900c3c1d90000c00401c01170700c10001900403901f4070006018102180e00654401c80583d2001030748607820360f4800d0b0390703070b50041100001d0b600300b4100340100000f1001510400d4800d010010048011440c0203121a540746c0d444414606c82101c98545407049420901c18900940111071030341541c2c80307895044609 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 820178884 1250 820177634 820177649
    0x1b100501211205030a06051201060f210f02040b04021602120d0e10110f010c0216030308130602130611060901051b07170d0b040c052b0f020307051305010306 69
    0xc2c000050070007198903800c000c2a4401131912043c000440c0d480b600c110484081d680000410594201505900c9214040c0e004030a042ca91615100d000044000394040083c0c0c01507400001040d1070000a003c5d004815a4503130082c07000880301a0071408558001c9e90900c261007450401c0e107001007103529101602071440109072400c0d1070200c58507202e50600d1540c00c260400590b402e4032032080b50b20708851502410410707959465401c240703075010410711030003808511814600c1e44c10f542e402440690054000c07074401954112400800c80d10f031b0161200c220110171043ca06c1656001e00030a001d0a84a01c80300e80d000f5500820503500040c0030f810310a41c10249110040c0d41011604005544404002d6940aa40c0000300000c27805a000401e9500a003003c045450451001000212805031000d8030601c001003001c10b801240b030b0b9590701c030140c10703e0590ba82d90f0041c50f80803e01822350111f00c1d001c0c2c80c4c40001049240c039008070280200e5501c0c0c1410000e100e841c1d00041d005c6680c24020b101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 820180134 1250 820178884 820178903
    0x3010f0e0603010f021b1c0507080c0106031b05010305010902070c0b07050f0a200306043504030606242f0703030206240a030303021b10050121 63
    0x6400c1031204055000701010b8000611480c60780501d100b03e800c4001e10301031400351440554900f010400c560b180307000550303944203820b21599101419038403d0b010010104507001c5400e1040103800c0d40090b00543d04002003003074141502800722040d01d42401818046880c00e0700114880009100f0b0780d000c1a888501400c203181441c02861450b080b000c0d08541c10701c20f007604806101000c0c841180900e01c20503504120000706103410050301035001c0468000c2d03000e0010080800c0348607001400c03560020445044407002c9441d0140d0703080c50700401d03d00f40c070030001e000401c001c2540c1c4808212186c03061385411044a00f650101600070a0b41020000f500381d00ba000722926100c11840005814280c2100e00040000302d078a06204a552003038000d80c001e40200300304070500440d038000741524111200b91041070613000441043c0f441c0000340405030b0100c1c81a1042200039020200d02d50900d040b41e41c0700c01c44142c0040504000d0040e015003070748110710610056000300344c1f042c0d42a031045000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 820181384 1250 820180134 820180139
    0x71d0402060a031104030606080a0308010e06130b01020a020402030c0306090105030703120503070509042306010924020f0708010603051903201603030512060306070c2603010801090203010605030303010f 89
    0x4901400c4440d44c1003011850401c00000014818400c5500030400d444c090000b010b80c5080c00340119070b050703000007020303100b050400141e699000c0c1c01c800114a148000600700d00d8640040349400a815002904648000240699440c892003c0c52046074202d60520107680c0791300602d17849115030700c80244030001c510700414405015101859200c5214079184c2d042100850000301a10304040c0400501d0200720742d03481040c0001001207600c10000c0c20500c6606242000506007140301c0001e4980d60302c0511089a4501c0c820311041e212400e002040b00c62094540f801300d402480684411500c51148034a01d4000c10b81e0030808252443d095214040c0e110709810200c0074064a20740b0b400118010a00305403a02e41ca00300210001d1070080da00c035a00c1e076030035240a1150520150110707100b64070040400846075400362100c1c42d01544001040d000400d038041c0300e0a42a1050368001c84c2c580c0c0400041840342d4151b02102000f03001310000c4c0001c40d518024152244070038040d0842c01c02c441c0c03809 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 820182634 1250 820181384 820181387
    0x70312030506010516060e1225050102120906100f0b030c0a032a0809030f07170705071526160e0303040b07140c030a0f06140405071d0402060a 63
    0x74650189040c180b00345800b400c201413492040c820301c01200c1080c1c2e5050180ca01075020805108200e050550f440e1812144040c06a02c5007501d40079010394600044d9110200b010a4040e243c030800c00b23100c003842c1070500000a80d101d01d41103590381c1da801680c2d5400100c5950050042c011148103641c140d1564445006040d01c5500c001042014151034044072103080c1c0d20389406070903040440c0544030420303528020061a40b84003900d128520707072081c0007600c00c00701884c04640c502540b00341e4040300d000a4050740541802000006029030085034000140300e942d04d69544016200c0781c0c8c8110754030040482031088032080815079038a207010700d03001901c50042c0340000d01d0011345c1828104009880540002e1941e44550132481c800f12001c40c00340100000e05440c031480700b0520300500014842c250101e1303540e109242d0f014103c403d0025000c2c050100c1e03a8051940001d03031803c03117502890203040c12540c521003445074840c541118050b01c29032071100480103008a07801002d0500d04400703040f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 820183884 1250 820182634 820182641
    0x80c1c0e090402060c0f0304060e0a031703061f030c0324060e010203041806080c150703210507080403021b01020c040f1d0f1207080910090b0c0303040c0807031203 72
    0x2203800130803c00c4042000c110400c5803c00300100c41c0c00a580d80e600b0004c00404d0440c08200ca240a2100f141080c030010b0124180b40e0512140240741c44e4880e03503900c000a00c5a518010f0580300200f0015a82803d107030725402c91407410b501c5407010301c07400d5070342102140404c00000c0080500b44841ca0300b845007a208403055103c101d01441120309294407141000c03104010201c00e01c61b846da40304420090304105102a2010300c0b0f00311b510f030b492001b410310405200c0c440c4220040800c283c101a0819940710584400390381048584200124544810301030051071041d80c0a5001d4460201101e803426820302d03240e500030700182c0c05410144281c82c240000f9100c0c24403085069074641070b4003070040c1000441840c0d4642100d0007050119081801c403820000d00b83e40306510120100120300c08254002c003141d10442d81075a0222080740b1a444c211041041a0440492003e00107480d982c0484008040c0d030240b0b0160801d100d8040d0349114040d5241554800204140300610254411038043d90 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 820185134 1250 820183884 820183891
    0xf0e040b1b130512030403080412030c0c180e0105090c121e0a0605101211040b09070314090c0306042a03060c021b1309021507080c1c0e09 61
    0x445140410100d03025480154000050b01046101c841c4000c00503860019020034075004581c001c0d42c07501d03003551601c0f20944241e00950380b041040103554030805104512080300d15800804150708a45c40b044545110034105507144081820b26103203540c1540c042c0315603801009144010560f411281c814003807540a41800141113000f0903101c4110079000900c658040901d0314050b11010486182030011208041d108110b8014004003d0202c0000520680078482e00302e481072264000e040001000741c0341d038200c80c6130404440030034440d41942641081c81c51403c00141026207564283c0c60a41da02400d01102d070303055100001040205106c43d0b203a46407514041100900da011030982c145190315a50703c04c803a810b6481c0012010164184200050002d800c0c0703048584c03002840000b2681c0855000c1407230119a81d5081e201199200100c0e83c0d46010700c1507050b41c4400c900d003841c4040d0340005401d00c0c4070340100c450b10380079120540030038038034908541c947c00305001d014002d00412881c0107 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 820186384 1250 820185134 820185151
    0x70e0a0c0504090e0303061201060e040308191d07050906060d0e121801030507170601120b09090c0108070f0c06020703200706030b010c05072114060f010f0e040b 71
    0x20007001c54840f10a00031030859a00c040011a0b49050040610022080300319800040e0703494410144205a594010680c01982519107601030742c45100b0040900c4c3d208100710106146000c400d540514906280180c40501030801d40b00b4050741c51051080d040c038100d03a01030707006100300100c14a01c2115072284142c4550041101c03616a01030b0b01124156015407034565a08001c21341000c2c0ca903a1600586034441070502d441d42004604101c10b0707151810280a090502107054000f041c4010542d01a9110310001000e54640d4205030a0440d211480c01800c03d0010b8181400548894051000c42c080c4448507611301b0714000094480c035009400c103c204800308646642c45542410a901c0c138542114120390160102528260b4050100c403006190141070040320078000c0042a804124501101d00750020f4030101c522000c082114009481001403c191134100804456000007640910400c082c0024801c1c41e62502c401004101c00e621512041943c400c2c00900040c2e03600036035540100e0324 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 820187634 1250 820186384 820186387
    0x30d0e0f0307200f13090201030209030a0f0b070e031c020313030602030a0e01420605030109200702011b060e10050a050708040308090c04020f04080f070e0a0c05 71
    0xd030305405041d9801400140d4070625a40c0d44034842c40c030340c004220b03d503141c01c4032080b042180002c0031600780101c02104408050b611600b030360969029404545c04200d00805030b941c0c1c0a2640f800004448440c4019a15500c00c00001154140230340c3d40c00c0c5507540014000e05c160a003084e44601d00034020781c40e580031400140700c00c000990310341c5a0f6401540c460700c8056241e01c0c14500d68000c8a9009940440580c104141900381c042c08542c18902c411802040c11404c450b0000c0500c810081040314a00146c07a0140000e0341e02c0e8040d01640c1621103400c410301c1900818145020201a4075a40342d50009040064900642c021481604c40014002c100c00c10600701da10380b441107908508030800030f504001401d504040c030300e11600d640900076000400c0107041c41e00c001000e20000400c020184800782004c200b4404041000c601e6030380c001030055580e20703050305500c54290483e108160f00c62192101d8040141c801140c0f0805885444140c2804c0e0380d140801040641003004081d41071050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 820188884 1250 820187634 820187653
    0x6080f13050312193602031903081303090b0a11060a020d06081b0906031903020c0f2409011103161101170c03040204020f070c0314030c030d0e 63
    0x40c14030182528822543c141d01592030012040d1403140c0d0034000c0c00b89071a20304440e40034400075003c60707006442600d4514040301404070080c0740442080d0341d8040d40c180f0500c40091f030003070000340c0d0303180655100f80e41d900f132981c454401d00c150103550420003e000c1b4031044800d0124603201000b0b000421101d14141d91002500c0c103100341004405e50f000c01780c5c1e540001c1c4032040303081c081c0102402030101e80010411002840100c144412104000d1481819030310089091a581000000200300b00001c590100d00035a03e40a0360324100b03c2007290003503000809912003440c0074031401920b20f100c010706403c64001000e00c00d00300d6001a06841c1404000404422659001c001500d00352101100f84407580045081c62a80c4200a181c01030400a80c22521b01025032040034094101ca404410300e81c890300d0342e10000700a4018000c03100c802c140007188010501c81d00740107000880340500c403003810f1151424001a1203225041e0034071a07a038010003102c10010310580c01420824038000a42d440a074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 820190134 1250 820188884 820188893
    0xf030408070204050f1014130b03011b0905030c15031833060f060a0c03030902061801030c030e190c0305010e0607020706030603020904110a0f06020a03110706080f13 73
    0xc40540d0800031702d441c0c030410090300504503015880513100c0300d1080850b1102c54000520011118244010720329107500001070151000d4100f403e50350706081803645006401d101c0103060001c5481458441c0c450b49220b4050f40c2000603131003e8828401c010707580746640c0c01403040d4031248207125220b490b01c61182803a074080101d4441d02ca01c400c01c918191360b103044542c044256541c0c0a44003910a0039078a204545580e22042110040c40b900d09024440c450ba034141903000704a8884040e4203d0b80012342c0d0303c03103c00e880040c2c11014401762000c20030f2002e6850111700312520001c2d420f01a502030101d8100380d40019500210036031080e000310750789a0700c03581e6945c01d540010191040640c4030740240502260140301d180041e10051504000301d61464001401040000d880034100c11002e100c0c141543d10741003030000182002c404005001955040001d589612060069001035007041c2d01044c0702ca0003003600c4d0204c900036034841900ba00d540c2001000104094a00c0e0100000141286c0005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 820191384 1250 820190134 820190141
    0xd0b060a03021329030703030f0e040203070314091f1d160815100b0a0507060606121103010308070303050705220e0916090b0604080604060507170c0f030408070204 72
    0x200703001c40c408104950003030f0340340103503050720103042130131100c0f144040c0031075100000c01d04101ca07014607242d03051120500055421101503820386401a00020400100302e8050b00101d40039240c0c0980c1041c00d503034110400f52551003640d050600120075080f1014041600d070010300114808004103401c00f5038000b0711510740a180323400300e80701ca0590b00c810004080280040403030340b0042005441c1d40c3c0344c04c64521448002a000d4030003140d0002c1902c241d080e110f1015204210fa008c54200201c07074840308003030f120f40b0f4046d80c03009946061240700a0301000c114107a074100c0758019070060034040c00b540e0660282000801040400c1002d00850741c843c00c0581c242c01c004203410300310016144c20703e13807400c110b00001003500805922091200100040101000d412a070b000800083c030b515500c4006829440369130300208861082c0c0060100f484142c0d0301c0300d40500c0c2c4903192a6407a00440741105000e00e401c4800c600051000c0c4052608604c1171001158064440d84003a45003060650009044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 820192634 1250 820191384 820191409
    0xb0a0e04051302040e060403050307080709030f0b160906020c040b06160605061f050723030d05220b1501120912020c030606031902060712050a020c0f0d0b060a0302 72
    0x100010b854000d066052503c55407520240600151216207441d032409003061101901d4001000171841c0042d003014440d484680185034401c02002d80c00d1000d04094012001c1601c0e05e481440303410742e002d11b4190041c13042d5421900c1302c0c1c000d00b400e20381039010880289803106100c1d810501c20085458404442040bd04405101c1c480c001001c0c00c09800f80448416006c7d04401036248203203078002c00f203400500f5659103503400288414402104152143c1390741c91107800b1943d500c030100c3c060074611046c1e0011841529203040851448050102520044481c80e00240041c12a8400b1400300c500d807099101c10240103051400000011580c1c100c1281da0250003500c9580154565805040e03040c03002a1403c60304078000c00150070540c0c002030710748500340150714400103508400011521076030240c40500c0c2c0c0100c0b02c0c5c1003d4030611006000303580003081c0342005029861021f2410710701141c0b0781101d038802902a691a207904e90b81c4d141200d10140c0b884e5801055000c00000594078005038402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 820193884 1250 820192634 820192651
    0x612080714121e0405090609060409080c03090118060503010b030a180308070f080f0105060a0201091203060f090603031b051e0304091512030804030c0501060608100611070b0a0e0405 80
    0x15030f854106220b8048201220302411071420030001000746513549004203401100488070110582c44e0580020002c2c11303500d100500c1048003142c0301c04020b4012000e4442c400080c1c0340d82150780060101c400d80d010707045c00740394080b03802400180110700d001000b8542c8115920000520100385142c00400b4807403905003200092800c500300402d65902c01d0f01000c85580a0074034080905186079070941040301409150b004850100340a410140300350001c3c0701494008811806500c00080014082c3c0030500484000c0c5440c5980051b1020292142004480c0c041c0c2d50410554141c071200c81d00d4402e0142c0a840c00e204200043d81c0072003003440219003286c0c1000c02181d40b40d240036158000d5a56001c0c2104010b51020030801400c070100b5150f00556a05150042c002c2d07880e07143c1a514000c000001500541c0303820700100b41c603900101d50500030403880e2205000c441d529a003c9031002e00c0303041c82c01d82c0c5400c010800c01c91021260040d20340d100050811209000e000004034040b101c085500c040f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 820195134 1250 820193884 820193887
    0xb030406090c050f010210020901020304120606030b0c0c0703060c14190f0203070203100f0e07180506120c010c031e021b09041e05010209060712080604061208071412 73
    0x20104090280b040004040603119481d03c0803903080040d403100501800340f110307541c0010352448146c0c400e00844010701b0019030540c09901241c14910000d1080d400211400c01088002c03d1100d4020001e9800e810700803401070003010300b1966104080d00f100300f00300c02404917a0b0151161030700c1d03200103003c400e0301c3c4241c078681c00c1403035550041c009031404009100f0343d0400c109880240e1800f0070716050810f100034022481c1d00d0600c42281c01403071508101c0c2c1403401000c001284000704201086000c03010040140043c0c0c84907020070001445000035040302c0c0d40501d140500d55401028200340e601c0c060f04100da04499001d804582e0000307070000f00401600150195000112030004020b230b11030050b103100210340303415501d0200b031000700c1002e44280704404204204020094045480803000031340b10984941c0e06d454158042c0302001c000c0310100d03410350b00041c103604040c480c0001725003e1154490f040001b40d15112002e0b880b100041ea6100a013480100070324504018031a4900c48502205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 820196384 1250 820195134 820195151
    0x306090e0d02070e09030d051b0f032d0a05151e011b050c01050f161a2a070804090606170709080a03120209100503010f0509160807090b030406 63
    0x83c18550180c000310b014400f10f40a100c00c00e217001007900c06440c8017842c005070503114000b4600300290415407071844490002110080c0c0003450740a9070184420700c41c0741c0302c200f591292408401000018041911192500040c5803c00c60380140d50003400b6034908152042282001c5070030010f0f8510b46030541400107030800300d00c1d40d01c803408610041a5604ea180048425580c0546410100d40c407a030400001003074951071000781d42d0445041c40051141c0c2e1840d10b40a1a200520b40070f024407030b8065954000004100c0d009040034000804107601156944c2c0710a503151042580100d102600c100200380000700c2c62080510905001d0b20380d645032840124066403010001100040c495810041180c1c0e081142b2600003401e166460f0f41402c01806030140038850304001d00416807010341c4a060f03418800a8603400800079030590701400d480d485143c2e155402c0c40302c80301041d9080d10541d180344404684aa1103900403640040c0b191810111040d9102d4041c034090f0000d540c141e40c0181d560120 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 820197634 1250 820196384 820196387
    0xd1a151305030a050a0b18060a1d0307050a06150509010f05040b18060616061404050c181801021204050f010b01030903050901031e061412120f0a0306090e0d 69
    0x20300300101001c03001040484500c0d51200d0f15008036003001000001801c1c0441e10010904c1142e03283c183c0300804860207880c004a0b02c401400c1c83d0030391441044000340c0c00030900355002c4201d9031000d400c01d008000c02c4072a640c0780c00042c21591014864054011000305480c1d0f60190b07024000c001d04c00030256920300340000c000c11a40c0445200b84500e03401d401601540c0102c0c2c84180d40048100c0d08503845070320548501740c40510754200102400c0c60100400b00c3c910580a080380075500030000c69041000c000240685400032103100c1c152404200006070312902a0240c80350500156070000d410250102010900b40308265003c40303c642010a43c1000848244924402c5820918050107200382944001e80743e482206880f40c1010b403690a1402c246056a444034000300522030b0030000555035007003682c0a424075070300351407042e00111440b11a607880050300c0303820007504c9544945001d00340304114175030350f100c0c400c0c4105054607001c002503851018410f000c50b48220001800c200400541c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 820198884 1250 820197634 820197667
    0x7030c050105070f06050601030b0402071406090d2a0515040311010b1008060a210c080601050a180612080c061303020607200601120b0108010507050d1a15 68
    0x140c0c0c104001444101c001c696003002d1101016005a80000c458585500403400390044825580d04140005821340801c003541c4a1010400360090a484c0a5152000056122044907016000140b074411a191101c3c070011a401e01780c581d0203201a050310400e07070ba140d0914042060b0325842d100b81000700402c1c147c22a9004e00300030046c074001c00c20103c91000258000e080000744800300400c3e000000c10f141c482c00c0110002d00300301d005403074624140180c1c0c45012150520122440c4218901c00141014002801781c1030302c400600c0c040c0c250307082c001d5500140c03842c0c085814403151100300002d03945070591902c004903030048211503900c0d261070ba2100c3c600703800584610002040e4000303c0d404a58089070098103c2241d2928110720102c0f015030300f0f014020380c1181c55280c00b407580001074034101401d000f0708203441400c0344011680e03210744081c02c07554110fa007000403800402089005144036403045806c40c56580d60540340d0000c40c2c0c04258181994014140c083c24001001c0d412440600c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 820200134 1250 820198884 820198889
    0x51203090406080705122103060f090405100f020702181b0301180e030307170a0b18181b0402130905040c140a030c0b0703020a35070302060403111c0207030c 69
    0x1c01480894580840740c4d0042250b0515244403036000308c0810200c1d80d80206940d01d0160080002140d818581003480d00e4140d0031000400350f510385100300c038114000303009548a02e0340041c510b1a00081c4a03040c40c043c1c500051001e61885551550000c8011401c00034601811288000e900032180c420003400450b01c00480082143d407083c8104a00ad60b4031144103081144180b99007142607c0c0e615002000e007401c06451a0300c143e6958450503001d01000003144503032080d111000711011036581041e01c1d141003100321111441a940910b95508158008010414170041c2e86150240e84800392001c80b241900d04a41012240d4400c1010040781e500324544641308890511509103107aa411500c03400707074415500d2080003c91003800340f5000303212800c0c60740c3e04628201e06021700d0644060b121010640c03440002e140d4806c103a08402c44042c20b440034594141c008041648440d1825542d07496020011644c901ca4860003000700028508242c0103d100794001349150703807e501e00240318000b0398 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 820201384 1250 820200134 820200169
    0x3211e0207050906063105120a060518060f0919030503060301050a0e0a1b0b07081209010605011205181c0e03010b03070b0c160b07120e010207051203090406080705 72
    0x10700070940b1128501107840018855940910071072a80c1d01d4440181d0100d91f07000a81c45071015000ea5248a00458540c41c01c5214500400c40c0799168403070400c409913090940303034450380500c0029003000d080d03001c40c0750070010407011110a408141003c085484610170210009a404402d201160509000302071b080b842e204e0060001d408001c243e00e51320340900704080c02c0c201c01080c504644030303401c840c103401504d114111181c0e120322038102b205440c0d00c0390b13b041d20089069030004d5203184041c030424007542c1e81603498200101e0b144001101030718014010a202040481028510101c2000a98019a503504e9054410b42501001074080d190480503540264188048210507950125907c41581e40c41c03c07085842e001d035000254602000d1401e03036004080300c04408105a0103800241400910801c40070011200c840d0045900503218040c1300c6c05640300e42001d00c0300c1d103410320400104c010a0811030b03007083c90f0b07000080c041c3d031159880700d401a0007000081c082400c0c50b1010031000030b110f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 820202634 1250 820201384 820201387
    0x50a0212090c01081306060e0c03100f05030304090e100e0c010e0f06030403080702191b12030909020d020f0313032a03080613090510060f03211e020705090606 70
    0x4900c006448624014041d0b055964010100000c010887c0e104070040c00d003102000c2c07031914000100d0301c030503481a68920000b082c02440011241090144002074400c040c002c1d5040c24501002000030700310f078010140d214014106150000127881c0b203481e00000300d000040118200a8001418456074242aa0300510381c12031101440e072030f2101241c4d0000d13070600d88002c0c0c0e0f596980080f03041000f504007540c030452424080c1401c1c0202c00711803034003aa07075200781441440d60307034803214640f0f9140142c02030108125500130880c030200317030380613202c1c40700c0034a0f0143c544000e0442c0f600196004803070914044000c41d06800a150780510102d10b0401e98482a015182c0e803240740d00d411205a00004040009010020300c0c541c03221891881e1101c40f52000b07114015503403034071b1900e440c0b2034002914100d141100020344410396100902c1281e4000c1907180400412641300221980019900340900c2002c581504803807a003814048034500281e40a031240387c1c108400c0104454024007400d214210 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 820203884 1250 820202634 820202653
    0xa0306140402090a0b0d0207200102010f020a0804021207120602030a05070903030219030e090a09062a03020c0a0209010b030123090720010e0c0406050d0f0f0c030204050a021209 78
    0x40e4844d201080c2d45001c40c00039150441564188060b1042030340040041c05149914800b40c4104a1100b042075003d03002406016058a51302341280600310041740010f80c1100800c0141c1000c3c5000103c07002000b0940b100b03a0b84440312115a840c040b2011205079500208119442c1214840d15400400ca8504010b20500c1c503240213580c0c50804034a0b02c0c141c0c0308a0f00c94030400d8050301c1d01e0003420401600c1d410329442c0484200c00180710514098501c1800c3c21318450803010f03504103c080644002020102c0b1010000c4118000d40020b0018600c600c2006258405a65612222030081803900c1c12983c0d25070400044d440701185542d80200e02c03c10b0458107c020395180e9504580c000000d00c0e01c100880d844400c188501a0380803a00d2205519001c28409904408a1800504034041d1800d10800e5560801d01c00c000182c4080078041010105040380090302c21691103445500a42012942684030b0f0002030844a0540307071207440540c006009070443c141c5d075100940c400a0f81010703100007003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 820205134 1250 820203884 820203889
    0x11010b0d020f0111010902100309061428110708130603180b0c070f11030d09051806030304031a041101170117010e0106142404091509020a030614040209 67
    0x440540b00c681440646404403c0c41d20707007503000154440e002404186a501003130b6016004024445043d13800c581003642c104500c0c008900154001c50290f001c070359180c46903c5a650300c27200d03c007010081c0a85c0300c11702240c1945005000d0140240620a89607490031842c003e050300040c0c5510207410f16080181d44541d5611400007205100d42004d01c1d08515905c25180741843c0c4260000140f6803208440c16000780f042c5000c0700c50a001094044690400c2880c0d029214403550b0301c02d841d4040310b60940090011100c1d4400303a003221003c0e080744d007015100e03900c0702d07085025040d4005030088401e00f04018050b0f041c020307503040f440a08020500d8403201c0c60550406605002d04c03505541c40c1480d12241c42000d5000d4014000e41c407000304032040e00e84250120801108069921401c02c0300218540e00d0750303442d03404000ca0418480940b8162401e8103a101800b404107607688803002d0700a0000b4007242c940010811350130151340014420341868035801c0409209000c41d070207588180709a6100d078 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 820206384 1250 820205134 820205149
    0x30c0510021209270a090b06040b06031501020703022706090103021e0a17030405030d0503090d0c0320010f0e0c03030409091712012d0e0603160611010b0d02 69
    0x28403da69043c10144440301c081103804614020100c100444130411403030600551240300380c02e10661008520391955070402081c3d842c136a04a0382e116800300041140785254900d035120602d01070042d01c9100360740e500000c80b140645190800d103a000d47c1c0b81070034550703403140b80186d00600c22142e081d980d50564001c21010f027600b0407281501c0c80124400c2d4400c1c7c2d64010804002c0010107003c1c0790801000d40341e1600c13074220b40302e0705d8005e100314141003d950b4020f006a80c42800500005c0090240403801103410090103e025418404600954220b1060854090890f41c00620011900d11a0440321404031024079220418a411104032804150f6000c030440303045411000000c10110100c3c04d090440c141c41c240415803003c400a09461300b0076050500904030341881d04000100c0311510402d444049954000702034004000c9028450f801106282c03e0300018054202d400204032a540b0101c4c80c20140c005d100403a6000f485165010024002c41d054020141c88140e810b006645c08904d04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 820207634 1250 820206384 820206397
    0x30105060304150c020c2b230a1a1308181507030309150b06190e03060a0501080d14042603040f0512030901081b04050901030c05100212 60
    0x115000070200702409203100740d8440d0384901800800180c3d4000d00080d6546084220032070080400c071004001e03011095240414061500b510f078150f402c541d03a207401200500342200c115105180e80c5400000d2000c004140070248240024081d402000c20f054440541c01400250040780e10f00d80c00d0000760f444400d4442204a962541c0403002c44080007401154074245807000d400804100707034080c07550582101da10340c2e0084580703024500d4460102030076103040d0030485410480803c401d0204800c10788048940c611641740c05407010401100007401c262040e14604009516440180b142c00c0c40ad00c07400418952a0500c0340381400c11001d505030600541c030503c3e100840740720031101d405100c0c1c2c191110006020058070354440d11206650803d038a01e014280c00f91b0700007015208005000030803500b4040058441030504d81d01c1c5e41c0d000d0351101c2000c0c50001c050382c0c1440b0001e61911200040c5001e1849180d56440050801c4203112408140190f5002190300c0018044110a004003c44a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 820208884 1250 820207634 820207639
    0x180c0f03010b033406090302010509010302090405090105060906061630121107030e0d03090504092f100c05120309010b0120030f030603151f0806010b030105 69
    0x500000000d0041602e1928a070f01402012411240c04180040c40c1c49582050390002c40c1042030b4480b40165440d80740100c801099080c04188007541c0654060200c0d041d05140151604e5020404034056441c25200d000c1242c1d141c0090000c2d918003120002e900000c180e8000d0704051007000084900c03803012030064200d040000d4680081c429401c110780d0400522403203404c10f240c08c042c0080039825191206022186040d54401c0c0150084d01181c90094040d075440f078400584800708105602074960440511224890002e200d4a5502618440c40c1c05100300240c00c915400d441c1402c611220452582e13580301d80c3e0f501000b555420200c2c1810865864108850364031460414035280e044461280a40c401000f00300c0a540305404c040e4081c0c8082c2d03100e40d40454030490721012881c4100340c4141ca504188000c111184801000c0c581c005401130841d00c49240d6140001d04094055892440058400c0c03003100d0380700f031b4880000740100f11040040c403444d890400c0130740050006018a51 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 820210134 1250 820208884 820208899
    0x5070e04020702030f0624030a03091e0503010c02010626031c1103130320061902040b070809210a0f2108070906031803050a021006120b180c 62
    0x20354408004c403a1741c420090381200c40b6410694441403414041c0c0112000801140c0b4900340141004107556210540c1a19030408a500b0181d8220a0105421403255000414400018950ba09000d03030386010880390000104603080c032600c15070b09a84003503d0105071100c611184e1001200108440c5011500d140f44001d00000054002c043c1040c1882540d190101206000044460342c0d4030382c01701c510030307140e401c01c3d00c9280c0c0302415201e034804280c06e9a90460750000d0b901108140c0d44182c8412010b00052415407103080340682d0340c1000310309448040012612219906103200074031100708400c1c070904010701c100d41d01d80d542d56085400051400c43d1403203101080244a00350300c8500c80854900403513908041c10300604994013154000c0000300000400640135000f8400c03091507401c40766001c03480e641d5a4609807a03d5000c46450011413140180101004445124940141c14502014402c007010307410704609001028003600740300c49401c00c00c3c8007078000001d21104103090548012 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 820211384 1250 820210134 820210147
    0x2040311060f070b100e01060804020307031403040504060b120105060f2a060a0e0d03020a020a020f1210020a02010614030619060f0905060a06030c1209050309120307060606020105070e0402 83
    0x6120f002d4030b02d0044c51441c0c00760920007150710200c1480166840000b2912442e070762400b003100e04503000c0e60046c0d050741050030b041c004a500d0410381c141d5442440103e0b40303440d98500c081000c403845135115030448000401d401e0080700c0c010020900500044440605004003000150385a100b40a1310248220202c50110f0294200510081d07403120080143d41040c503040342e4120160402140700a0a40a00d04400050343d000c0d01c00e40f22600c0c802d50040000c03005a03428482c0c140102814141d01006c0e900254101240400107808175003122030b40036850354004003019007502d030b894016950b4203603c01409601501c00044135940b1194803003980c0c100f20f010400e400000e18040d005005140c00c0d24001040d40340481d0051809103030b06907401d50300d1540d80c03481182111a0320010000045540c8042c07688112180c200c1c030340080c0210252490001c0ba80c1c00070750790080c06440c10089410120300c0a0611980e44130b000d00403d500d0000b0b102d58a820400100707010803a02c0440e04c2aa4046501c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 820212634 1250 820211384 820211407
    0x30d02160603180602040905040624050d0503090303071209050d1a0403030b1509010e030705010c08070c12030f0f090e0714070b0403050915070302280f14010b040204031106 76
    0xa080f0b4564010000319696520f8100e6280a482c04403400e4410364142410290000406040184c500c5c00c60b0f43da0000050a0404100480080ca0400d81701480140140031140d80d06200505103030b440f480000d054946008406400400c9540c071140c03283d034042103042c0200d0014121011260b20401c0f181159aa89280c181c0c001e00c4003a6903a60003000240b202c81c0c40341803910080c15014402d803100319002190404055942c0024000c240c0000d00144840000400c0c541c00390084070701c14007420310341944542540b0b000191060040e80015071410f10300d50b0598115030b880010707104900d4076081160826005020302e00000d020300040107a141d008900d071421840946020075407201280c5080e041c10b080080c030b242c1080700f419200d042c100409103c00d000c0342c2d0441c0c8006a054000d000c81c6590300c807060406080403114108049440c1034100300080e042c0f801d070215103110780a03451002c488200c0d003e08507050f21070414010b510400080c03001c590700418024035590101c4d50030343c2d55940141c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 820213884 1250 820212634 820212671
    0x80a021008190e030903191208190f0902040b040c0f050c010e0609030d0b0109081018150e1e1c0e1903030806151801031e0605030d02160603 62
    0x111402c11070301d05815031503580c10100040c402403c0413022108198500e4620607030028117080000c00c82c88031100c5110a540c0154001071303006005500c0701c0c89403c079100c030840039030312a44183d4a06c181e444140c5811450a40700707000d450718050710100300c0fa05800e40d0203091100c00500140070312101148900100909401080d0050004000e0740c009041042d4919a41e0300000b0f44451428102101403006510402141040f24000001000c550702c1040744000103200b43d010015080c2881840d140115442304481c0e00d85107052140000c00341e5aa10001e4100220104034200c4000c2002d41180e00000006110105503c0814a540c41d48205142582e146142d5041190000303c0d5280007945440030000c050102e0780a0f456541856a5280c00c005084402c02181031100105020f20703411142c5841e01c0b03000003881811700240940185650240741042000030a8400781c68220070b008900341401903030001c40c124002015440000d600042c203c2016000700000c1580d40c070300002c20600b0051 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 820215134 1250 820213884 820213921
    0x7020103050a0b0d0f2d0506090d050a051c051e0115050f0306041518060906060804061a0402040b040f1208031617070807031a0a0b0703050f030f10080a021008 70
    0x36403084821b4484010700114100b1000755040d00586000400c800404144140c80481c0d685d2072514064090750180c400da0031142c90b9500c640c1c450701000c0c800c0d024070302c186c03030080031203650080d41004803843c000c10f00324051308080408110344483d0740b5405d8001007a188140126080c4646070b41d078400201d8014114808451408280c4080006051b4a03030150221321103007052050042c140c07103620542c141c528611a4100040700d00c800507020803050b60142201c0703020070401c0c01d186145200041e05980150304001042100041d08110070000c051b160402072030b11100224507442d035900c1d01509030000600e43c400c0021908201d050851107007604001c01d004846a54841c0d041c07000c4002e06620080b0f03881008a464001114002d4144461440300b500c2e0042550100c0c07070400c41b4400c1c003a00692411021700c502070044056261055000d140b046e840340c140c0369101d00c0d005207000460070b030310f0703200311040d400007054180075861f40c408040c6d212031241410b540c95221074184810305c1a091 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 820216384 1250 820215134 820215173
    0x1713031404030b070f05090102150c1c02030117060c0405060c07081207020a0e06030a030f1b081206091311010c080c010b0405060a080601092f07020103050a0b0d0f 72
    0x80c01008003d0408822400b4201d00d95640b00c1c010030140095036240300c0d00c64a40e001d64003104e01a00d4114103c20420340c064942e5541031300f0722800c0b0429041609050241c0b03000280c004c401803202640b042c0d004820325001000074049828848010141d82c401c0b40111030040d00e0014190341c140c0300401c0014002c14040048840c2e40f202c90b904d40d4401c0c0c02480c0201d00c81c2c5074804c2c00003a03072504a6901401101c00802506915005a505a81e110402e00c40b05050081c5d200080070441c94a2400d01030b0180586d41c55592400c4a031128142144020301852140c0344201c2030000c0c0194450403c080705a2040901c262542d00a0041c1c0b0441580301004048a43c0002d0780304400c00103421a050310392090780c0070b1007985c50349010070000310454000c60060740d20080c01002003004c15042400c0b1202001d00c03030081e00a009105561401d07181d4a5040860b800007514011542d06105859022000d41404c0000000341c10000b0151070030658044c3c801042440701d5024000d1070016480d901006 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 820217634 1250 820216384 820216387
    0x305070507060f2d18051206013303090314211602030702040209150f0301140312160303060918020f030102090604170c06040906140117130314 63
    0x2600340c01081c8811002002c8002440048002003041d01d800407101c103100d4608001546484e000703000c07100d00c00c03074034002c108040584600040c076803540503403415880d420b44041c1c0402d604100c007404030640030006d1903500e03144482581d051021805c40070b1078000d4032403030007161b04610350408542c010100007500e1a03540740003442c0b4265285450030341b180707101038450b02c114564a5000203d0420786d420010000b41e0400c000e120300501e07180c0d0082c600484c000f03000d1403c50804e81003501003500300c600d44441408002005001182c506814400d04000440007009440b4482050018500900010044184004e044001054004d0300001e001c1d10490350100030701824007902da4a4500110001d030300400c1c03c02030030041e500b0180200c4400c403402900713403850b00386445051788402650100d50b15150181400c000e0321a650036004000514599001080d4541481a0388142800300b094450522015124440030006460001d9a03c04407000003c01500854101503070b030340e40040511149881c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 820218884 1250 820217634 820217639
    0x1101050703020a0e0906030c1c080d050f090106060c080d1e0209190f050613080a050109021c02010807140c030c07081204031a0402041103310b01120305070507 70
    0x20726501400465919658402c918500c1600348040014203450150b0960001a10700d492400c10b032003203864101ca0000e031800c05072070540b00ca0b1a541c01c10103032841d201d5100d41c280561510000111a08805404001c104591074910041e10408401c14010101c81000c259080502c1060340300b89094442c590a58007141503100d4440000e40c030164040c1c1c451030003496500310700c0c22120150340c10740781c080c844861042d04040410600b5044001c010030b0440312908049281c1d44144a11034505206200124503c615481004011800501000b0040e00140003903070160780e024800c0e41d04450340d07041c480310741000385511403001d01c5003c0d00303191a44130006403400750440008442080f15000420340d4020342500701d02c044944520300c8081c0002804c02e90f210450f09a055015401500c02440024220000c08200c03103140c10842d04000240303046408014400103000c403000410340065101c41642c556903075584921f0806024a000800c047c44517982018016012107220940140c21215460b6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 820220134 1250 820218884 820218887
    0x40f03150219120606180b0c1c03050a1a09041202120403080418020418020901030f11270a0323070f06022b050304170d0204060e0a030c0b070311010507 67
    0x8412018070745101c1d103001d2002032141d1042d0841b100e151842c5070300d400a01d15110b0864040c2d00314000d00d02e514080c1a00c00c411180b00b501582c00c071425261004241444c00e0780d40e001c2101d00d100c5080c82402d0070b21824071800e9440036003869100764451607a51041c008004202e2070304e09110700890300d00100080c044107000d8010046c0c000c13210340160b0307840100d1850295406a002d1761003590302603103507004569008010364000c2d000819040c03400048800101c981101901c2c2140f1000390751080015058421440314105c0d91112050b40c7e080aa10080c0900401c0401c6900c3c88064406400010070b100301c1d6891400b04440058248100e404094651110408940652040070f000d80304031004d40604400160b04000d1030441c4540c03e217910301c5031f8807050303e4070350000303008a8428002c0c2c0300d00d108101500001d08030300c5104800058885e03041034405029100b00c03940d80c4d886404480b1041000510680152056585940b44907445640514094840c0b0059011070842d55007040c0c200a81103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 820221384 1250 820220134 820220147
    0x15030207051b030a02090705130603020a030f050c030a0c270509010e13110103231909050318401506030c0c06140703060506040f03150219 61
    0x103030080c01039030380c003007104228407040802d00810590160401841d04025141034040658000881c0c100246440d01c40000d54406480c2a040301001c01d40c0403a1560b02c0d9941841a0403c031040c0c41410080d40c01c04040c0100c45000007402000000d443c0c040d06d0800300d114080c2401103116010001044150020410b0b0a4a80d03c0c00b540380070740090340c000580350408550304d80c0240c2500d0303032080f02d9804d261580c45440607804000c40c10300d1307140e4003407036202e10000e607240c5031014410f5113814290800d000c20981114964400c0100907040051440209401000312580a50000b503030310543e40510300420216082109101c00b0500d5081aa130310a003840481d10442d144805001c1c1815581101032004a8904441e11040c1c0802000c1c140b108900950005100c40d0603410700c4040d11000d5565002a0340d243d0341c1c8410b20458260904c44040c1e058001e00c00030f13100c1164400c2c24241802c0302b01000754001d00c4050550300e4441d40420600f5046da040f154600f103900510600f01c41407240203002c1c2e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 820222634 1250 820221384 820221397
    0x10c05010204170d050f070f29090f0d0207051306050a0e07080c0f0901030b190b12010611030a2f03190509030a0b1803121803030403091e150302 64
    0xb0b40122804901342c00c0c070801c01c44101505084006041c03001721f4440001850302400100c81102034002c010848107860540080c1000c4407024a1107140303403a00b0070b40d0404c4044191030181d0790100c0c0c1d108900503000318120302035803400c5d101418070700d91701401c45c8060140c0743c0c0300c01d8020380100408104100300030000b503c540002c0d22a4050b42e15203403005080c6101d00d1b905048000d1003809010b009601c6078014002400c401000c1120140480b50a82400e0360f19a000c090b10040c000340221844034212600d50041c001c2d0300f822191b280401c04001d40304d2242d801e0700410080c1c1c403014850b107041e900c5854a6443c489000407030b6582c5401c0c0c030466403944446002e8040c142410313881a400d910810031680e920300003030007914a007445a0303110720a43c000903211000e040034803680042c8500c030401c0034020365109640c90720240c0c1071500242c030503a07075501c80f00c1078285c004104220119402621442c2100d072841d500b002c100a00302d942c09512482c0ea00000100d41440c00f048032025499000b400d50f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 820223884 1250 820222634 820222679
    0x50702070911030411060a02070e090c01030509060f16020a050715030b0d0c14040b1003051009150b090609030105010b0405010e09150d1e08030406060e150f010c05010204 75
    0x5025241e400b68103040c04202c4000b0301030340302072580c58010300303040000d0310703403040c0900460b04c8143d00c401944040030422104112180d201040002c005e6905000311b0b030f0800b849502800290600c0a03400a200d58000c1608a8807000e24055900c0d0701c0c0b0030400303856010381140680d0039551315074003080c100c9080e100744400005c0c181400d030240c41c036044200704d000b56401030002003c1407810b03100050300410800c82e1a805551140091180c0d00c543d00c0c02c05848a0545e000611740c0741100300c0c0d10038481c440e0011203030381e0f15048103002c041c6800e01850301500c2d50424606e40b10b00c042c4000402d24826080d5068155013402c2c0001000c95031000500262502600c580780803014040c240700900104541c2520b650101f0114101c2ca420011548140a40911545c0412030f03c4900712189600b80303c0000c0754500e40c00403c0005210b5070780310b0040604036080221090b41808000070540a000541e01d40c03094440701c8014220341c0c003d0341130180c90b9034010002d548403a0707518800402941aa400c041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 820225134 1250 820223884 820223891
    0x2161a01150305060d020906010201090c081e0303070c0f0c0801090c080f0c0f04050c07050604050a05010506100e09070203370804050a030c02030102040504021204110306090d0c150507020709 84
    0x64114000c0c0107103441090045e0600c5800d02c25a000c000b0400070241c02141555650454400498010000c01010701031510080161510041c040310300c001c0b80032518001a0014014441d4a6902c84070701c1c0c2140342c07c0060020200307a40c0c10207400c240001e601100d000e40c43c0c040c4213000c00c5180708448040f5031407130342603900280c2e203411707602d032654004082e1991004841c401114103140c6a8843c0390000340c2400b51509000e843c4c1c2c0d445103400c0003900c09551303a6101e052606e080050900401e9801423080d114070701000040c4201908500c40540c095204410301c1d00041d601a2080003556481030700e09900808581055080d0382c580c03241c3c650080481000c045102000e5030017204121b0140f64402d005002c02d02c226282103a010100039404c0317a15540801c00080c25950343d0010700540ca03411b040d010001e040520b4000444841280d40e81d001e03400100402100701d8010800705401c1c00d8a04002c0032100403450301900403901e62405403039803894a0203102d500d550024159098a940340c4080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 820226384 1250 820225134 820225169
    0x1060c030c060203280f06290d0207120206040c09060e0103020f130f1a03030f0405060c010b0405040c090f060e060f0409060e0c10020c0a06120209090f0910090f0602161a01 76
    0xc000d0158410080f00c050124030407260b501c801d41001042703100f89a140060500c031942d62407402d410811810240164840414001030044001a000061440321030801c209458a012905070410502c00a8480e480b414445a0152940b00144480750702d00c0d1000c1000755030504225000b40110240c2254007101a81e020140d0700340001224145c0b0074418890b0309282c64207003003146030743c032407607030311070300f0754881c04940d80d1074031180140c0b0b0045108200f990790301d0f410704480381c0889201c450071a18846c2061020004000128511900000f050f02d43e00e040035030310008580500f08024008000c41c1c03031f100d80304072800c5020030316040004086611f100300c8030205200302e0384c0b884180c0000e94821140c5004100b8280190303015514412219005410459000c001038200720040302e2003211640441c0c1004101c8034207010303001a145034801c04116000854070388900c840031144009000ba0780c0016003035840607010074104c0f8000d81c0002a003050840d815402040c1d16800e100e000f107044410740c410b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 820227634 1250 820226384 820226399
    0x50907090c110a110307090f02091003090c05091b0d0e010509160b1308060f0a0b120a061a09191b12050a06080106090e0601060c030c060203280f06 65
    0x440301c0b841e014000600310280c0310b880f41000400c5911007241e00d0300c50300d08002482d04d11070044210118502c040141c81c1c0b5052014014246130b150a100e00b00742c90001440c000400c058407010556a003640c080080e07650300300303603005107256070541151204c80220358041c001c403c0e0b801512251020f040248210344803403610780c1c2d45e031200c1c00681c0f0b0342046010051044900d04130140040d10748528884141d5030383c40340144d0500c9001c0d9195004906c51008103c0c0700045401441940c40c0b06448040000d60300c00f0009465101c91400207250b5074480307500002c2a09900344146200c880140800c07004e0500c0401030710703249403480c04050043d0810400c0ba820380c41040f00542d4035145502e89a5a280c100110a0000d02005011102c456035032000031030012400d00c2814090208000300164000c20302d94424a049016403150080250017001580001e0340800c648c1c2500b60f005001503202e4075000110398410006120704c2000501d80d5400c501c00d13007069086900c1d074224094040000e691100030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 820228884 1250 820227634 820227647
    0x1703010803160f020a1e0b0a2c041b080f0402090604020d2c0f03040b04183b070b2205060c0604030f0c1101050d0906050907090c 57
    0x25a0403150024006005941204024824090701c240400c1c400e42245500260b1640c0b0b0702d41101c01007109840080660319103080d04000a05001c00c00d05041250000004100390b1110754000c0081c45c0020074800e0400500100341440e900007070060203880390031b00c1c412010b40a0552004002801170003c580da811101c0034007402160040e040181c190b4074181404069444040d001c0d8103199940310103030200c0c0c4850440e055141040794029000c0200446851502000c4420349007550001c100c2008141c40b58401c480488030540c00341d5a00445440144008040700d04030b1640781802c0b800d2002d500b00303a810301e1442107488051140c0342401000b403107a540761464080d07004001c504016003400d1103a220841103000d51942d1031055126103e1b0041250340e000924086a40d42c0050103100400d0b41044800c07114051900e0082d5212185417986c8060407015101c56040c080000742c208089107031600507000c0c039a049141840541001c5100b1a03581d0b80e184140f030710b1507143c40301204080d4130850 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 820230134 1250 820228884 820228889
    0xa1d031506011b030f0e010c38060a060e03030d11040303030e190b0606090406080a03081303080a050a0b091f0902040302210a12020303040507060e010206150102011e0207170301 78
    0x80c0d900f1702c01001418141c40c000f03040d0b03502905200c003c9801c0c0300000e84001079035204500009020400c0060800c440c0c0c07480304410a0800d8401e0035404000c11900d5001003502141d42c585030043c420740f84000420309500c0b031341d01c0ba0000242804040d100710340007400188112032080ea410004480c40460298642100820035200d0f1024580c3c13400c0425000c544568126070010074152420701c040300050100c804542c080c41e6160040c01d545024150044e40c40380d80a20710101c030007800700700350707030000e04182d402800000016961300210308000707070560010000c3c181c041c2c441c40480c05d0005145150f110700d44100041411010300c0824070100a0003514116640a44681b00050301c450311003100c0313415005041214412420807001041611602808511007a000f4641c0c13414542841030404809402c6003040c82801ca4568051b80d07800a00ea43d4800c801103013411142c449800100c4c0904098588990400d0b820140d641071054568002e10305c55200e40b000084220501e1506050b0380001d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 820231384 1250 820230134 820230137
    0x100807080a090309050402130f1401170910050f041506320a0f0801050a0203060607032d0f0324050114040302090c07030305090f030a1d031506011b03 66
    0x203008246080225005a9200742c4a0f0420408064803903000c113080b81c01808107141d101110010030080038419146076000340c100504002000c00c4020006040c001080164844010b00b00000513805001404101c0700300c80710321414401c1741412403c1040c00501541c040c0c178190f90030a0388102101c411f10401d011030f0103200e0801011001d07a0301e100c041e0001c42050048081441400240f00d9960003d00310290540c4030300c01c0e0800382003208060844a0003414a52600c0c8100b050026694441050720b28690303140c5464000324940011140c0700081c0c1c00d801c100450750b9400b81104880e00308802c3d4403005201d51302000884a10b0030fa00c51040a00c1918801c103a45681090181d540324450010141409054080c9480c0d40c90340854440300b02181d074000503410101e680d10801d039140c05003a8000d20000c004000c01c02030101290340700d1103031125006c140600300484641440240d10882d8445a005050354541102d0f4401800040c2c41154070500040c0c96507400300c5244d0340807160382c0303006406 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 820232634 1250 820231384 820231397
    0x7120f240807181d01091a01061202030a021309240b09011815021b01080f0604050703060302060d02031f0e07030507200c10050f1606090206040e06100807 68
    0x41100d962039610781d8105041126498134041603146881129071400f01415000001d90008641041c0c1d9081c90515000f812140010004001950b1b003c048500c60481c11000140e0b42e888020910000340301d500080000e04007900c100064408059000d01138002c02c400301141401900701c05a0120940e42c02200740c40740302407010790a5540309401203d2074420f0002000d5040740c4481011300c115011803503103401644843c0c4041c101420340d5101e0441c54800382002c02590800306030006035a080101824080c95550000441c402e00c03031b8002e00011600500429a1a00f21b1080d5102a51080f5800b1010941d4610382000c0303203603800d04240c2103130040001c100403602e17440e00c218050032000d0001c00c2044500c0010003a10b4000f40081c030a0541c0d07400091003400820401d10004d00b254608810500106001c84940390305041c00702c1d030001084090710400c10072180351220040004c0c00f0003a402440c003003400f007291881014407500804044510f03110008900c0d030126201c002c11100c65001452 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 820233884 1250 820232634 820232639
    0x903021c021509060d11040e0903040504060e01120f061b08040204060f05060d02031510050c0c1504030b130b010b04080f371506141503040b07120f240807 68
    0x5c0e9500141c041034a281e4120314056079100c8141c8140410740340d00425400003d001c03c0985868811100102640300003a0f0040d8034201e44030b02c07400d82c0b4100241c5500707060103000c806c00495902422034410003e003840007882104c1390003004108115022030165181c0070003c1030861058500c40100c9174000c0c1801e2905900344040f00c003a400c0940482d2001785c00200003007280d9a620005620380700340c1d903107880d00d4240700c84042d403609130b07070085145c0500c1006e8015910800c012003100d00340d90700480780c0034071034031019000059549400406483c521510740040740c0001c0c82002442103c605070b00711010915441d61540d141c1c1e0034202981c861003505160001c8003402180f80f01c8040358070350744200c2070f241d0b0364a0b0320180380310150028400c83d644101c1489840203a060b03c10021405540d0034000e0741c103820355451241720280c805080c0036003c01c0004d41d001c0c030074012110482c2450105000308100d1200c00e0018050491401c900902078006201400c00c0d80503218044508090003490000c0c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 820235134 1250 820233884 820233907
    0x5060313050a02150703080a06031101110f010203100f0e070c020f060c010f02030702010e07080a170d1802040501051212030601050702120a033c0903021c02150906 72
    0x114903080490340360140a9214002d0381e140f011242c4c1c688082082d16030750f015140f030300901404000786042040e030316249050021842041882d1340341d0a003800c4c4001d40800c50714040c2d190100981003070316990300000030095503005405131507080f0b0301800c124107815a2918150310b00070108481580028142c6408803015241c1100a60f200c0100a880d032480d116101c82c80c1402e582c10410f0b103042d120380000034840c1243c0d0900c5000d01480010300035100c00c60410440b030b6150300e100400581085241449400304000110480c0c07031080780c50204100e000103100350104a806800800c0c2d106078130380400002c85040a0001e0702064040101500740c0da84c20040768801c54001401d0039040080c00c4c00888016111306590300301c03004519000f02616100340c54000c15031b003209210b000c3c00e03055001e01d1340c58100b02e59002e10111036411040c02c5200c0b800c81001c0360441c0c4613600280d80020400c4059042110002024030f140f0f00940b5958a030203080300e80c00c0c22508c14418030b01e802c550104410340d8003c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 820236384 1250 820235134 820235161
    0x1110718110706090c030b090c090f040c05030d0c0c061b140c04020c0303090712120c032f1204360603120e09070801051002070f0605180604050603 65
    0x280007a91509050049948440c41281c500740000c482c5144603c4c418820f0041b07414050342c0c40f0161000803d41059001c0100e509007134064640e081c0441c2250109041082c0318034010060000541100d0b0003800a840041003a0381032602610102c030074050204080788680380380400c000d001405e201c0c010300c3d00e40e03c0c2c1e00c80896108404116000e0b020284c074080d41d41d4001410f42508060007941c40342480c1c1c46041c02c107941c1e98040f000c035810060f0101c00052801c1c24904854807a4102059107241c3d9040c01e651014400c5280c82d00c0300104400285980560880040e11940d89d000321540040f880241d14407901c0785005200004000c41c0044040000344d589000c050803031414840d83c850480501c14081c1c8100d07030411036140d40c0d01500c1600f4260301076400ca980900450300f0540700e0805040103440f01c0010301481d0b02031184072103420390090007004214001c022a4920302d02450340d0f000020583d0308210a01d59200d02c1110a2070700b40d190a5080d07406640c001803801d03140d600c0f0031025642a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 820237634 1250 820236384 820236401
    0x30f02010b040513031b17031b0d050403031d1b0102012009090f1303030e2d0c0105070c060c03110105010905060906040c020c0f040204031407030201110718 69
    0x4540d01c880c4940c246481c1c902901c0e00480c2d007043c07440c002240f01e14024040000000b1401d492101c00354100002c941a007103120301d4091642c0d0400d41e83d03280c04686040c114246041c031180b0000002d24106000c410f58402c9114070b0003550304106a0303182c4011075003054100402d01c00e055101084e1681008010980307034840e410140000141c04621202c000f4103418480600040c140e40411580380302d06041c0140c40c5e0001d10318078400403030b190070320350110407036824034000e401c150b640c0c004900162400c02a00b11390140020107906154012401c0116015080c0768021040c080c2c1d0340d8005040d400b480075940b54641c4203500c0c0c000c0700c2c107000c0c04540b149220341e02a01003100710080d0303514444080c0b00b014040d1071040c2e030104581c03034401305000c0d10700d0015098502440c907102509424130f5000c901c601205004850f415803081402e000200607000d40d42024080100080c13500d802c42c100082c83da000c0342c0c400c0c0c8500060000d90317012562220120310540e00b0110f218031902c4e840012940c4103084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 820238884 1250 820237634 820237637
    0x1020d0518090f010911070314030c04170d120b010504050d02060f03010810050606042706170a0b0c13030b04060920030c03032508070b070c0605060d0b04030f 70
    0x184101d100041d894030000d4a581000300300d03c1c0c00601145070039000e2081602c5540003031600d00f11050303500402160580040300c100e01d07070210200d840b03811103000b250001c010030011082c40513052070300207440c0d048a03141c50000c1030118054103070b12003845c014070840c48016110607007840e203050188101402020b0f01244c2c04a4204580703015685420041c50280020b40c00900301000c04065000460314090002441244140410014144082c005100b010313803607440d4031400058114803c002c1c1c0710341c0d0000e800103c080884202128000140d80c5490360240030003201d10703111004291100d100700740801400000004080c030115007030900d001c0d08141b041c1c04c005645004c64880c448a0400001e0f0160524000409521289010000c401c1481000c84c003842c81c02640462a0f52446108610b21745001c44a4405c1c205002810f0b054444480d004046074010780742c80d210041404c6500b030411601c1c06d1622001c42c500782855510041c1d1960f0140721507259803510346040c1e5220f42231052010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 820240134 1250 820238884 820238917
    0x50909060d0605040308100803041a0d0e031b0601090e2d03180907210f02070c030503220f030825030f0f02030c060114010c1208010513090201020d05 66
    0x140091a10300c00c0f030344514000d030749442080c20b1640c0200d95660b803a5110f030419620900081c4a42c808440092401c10070340c540c21aa64403410441c41c0103401d020711000b1940c040814545122030840403202140c2d500c001c1038596aa0321550003008848801030801c031194052008240b04004440d50980c010441411140d684048a10482d240d0345c00b4442070202c1c0200b51100000380c0c10729007040d6400a6940c10444c4d1701c64007034949401100c529010142510f512882e0007808100540d0448090035003020810f4582520707401c1081d643e0340142124100b450075100d08048410342c5c004a501034865a0008022491a540702c1542d10381010103070340302d0407480c4070000d00380b41440c001c03516186120341c80e11400415040406421819410050001e41d04108a040b406000205909042d50380042401045000142c0101c4e0709031000c800050038080c40c1c0c0e200c0c450041d080b449141c100d0320704898142003400903c42280a6a0041e100280940d12440c040340640e0f0050014001543e80e040c03415 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 820241384 1250 820240134 820240159
    0x408030a0f021f06050a0905040506040321060902040e070212070b040c05040e011b09142832061803011e1a03060405060103140c0d05030a02010507080705090906 71
    0xa0041c00903a60f1485100da59100d0803c05401e29842e5100100a0b210040050b8038041c1c840340c0d1542d01c0203000404200c41e801c00000c0000800e280400309180d440c104100c00c544be107440b00000c3d8001d0145000900d50600051206407000444800700484c542d030803810050140d8954900302005001100c0080c0e0015000c140c94407107210761b804481c0250004a043c181003c0c0c041246040500c1004c20806180d4040c440415060040045800191100c584810700c031005500000300881282030100108007000859620400b40845890304504c540824121560b000710078005105021030b400607003c5c026841c1c0c242040a1040d0b0301d036805030002c01d00200700c481e48181c15480c1000342c4405580e40c0d540c148040f6190a5071024068203030001d103040c1c00c0c1511281d64030601480008c1003c5042582e006c40c1401c20300c42c01c1358500011f4004100780035140f801646980020040300f0041d840d01c40090781031131144030344a01034403c50b1605885c1218200900c172400c0c00060265412040c6207401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 820242634 1250 820241384 820241413
    0x21b0c0d08030c190e21030405060c0c09090f07060f0806040b0a0e09011508062206060f06090305160e07120b1504261e0f10061a0408030a0f02 63
    0x55180a44e642d10070140d2210b45080010380e212003007001c107011a0307075100d0f0000f940b000011642500c03011903030140c8800120428034501b05030103103000e802044002c00d1054194002a100d000007542c08180c4410b903869120403a13031110400040c8000894000200d5882c1c1819446010319071009041142148d840d00c0b14003440c10829104601569503c04014003440402d020300c00180000c04060301ca07a09003c2c4502c0c4119488040384525400700070b20f10342c200200b80d44058001c0020400a000f5140d0380d0401410103600c521042d100d0b40a100038500080080b4198041070700c0006030703500e41c0751320781c81021a4a07064141b050051165141a1002d0302e80d00c43d04440c0600f803884129a95403807c0c0001d6100c4200d034604805100c0900380a0951078490101e80e61b010695424030820031012000e00c52450141c00e501d610010b400b520280ca140b01203603400c003030191190406e0001c0e80702c00b1605040443c2c80740b072003008001d03001442009011441002141400032081c070480b50005401141d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 820243884 1250 820242634 820242667
    0x60315040818010e100522120b07020a170f1c1a0d05120f120708061e0d1202030f031009050a06060c1518030201021b0c0d08030c 57
    0x5003a1541038002c64030360b110704141d40406400303480c2807808000480b040c2c030104100a450580000034000042480741004130894a161003601c19000d44007036580d50341040800320900c4081c140c0310005501d0010b0a007034000100f4080349540200366040000b1501e407070900a40001000911548080003480a101c03c00703040d000d100c040c2c10710b00103010740d40384022403c00c5821800d00f600615000c520031012540c00b003020100310502c804403d680f5184c250111842d8481d4000c0b000302c00025100740046298040340d1248202c8095a11241c0c5440323030032030007148000c40d110310340c1c0c01082c0d51004400102c83c000904c0603414180102e03414214940801011904219990050349441200c10403204050b4002d0581212840c5810000c80f4141000201249100035014010105c1a501d03824821030940c410601005140c2142d94000402c0c0340080c080d50280031030348201d03070304500e180c5080c0c0d001141e20140c40c0c42c024511000c03000c50350340b1010075401c0280001d9240744103200e00c2005004008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 820245134 1250 820243884 820243891
    0x7031d031b090f0f070e04060509090c0918030403020607060e060f090114010b07020415050a061101050f090c09040f0c030f03030510050604050103021c020403060903020f0f06010509060315 83
    0x5004003407054511081c031810890080c0b01020f0040c1c03110502c00ca50038a41d104d50b0b00040c282c64103004480041000c180582215844613070040c40c000c04020820700d020070f2502410f941164420f4150b00d41a90303000300b0390304580d005400e9420801c81007006140142c010100309101d40d20200740085090066402d260040381c411250780c1101080000000c428410034986c0e00780c49403c8070035541031000098480c01241c40c028015503079414070810740000c0e141104028080144140b1007075803603690040101e1a00400940950300700760200d4900c107200c6101500c44e4a0742002040001001d03c10480d5040b409041a0380e070741c040791908004508940c90701d8010703500130011818801d85034603000301142d07001845103003102c0c1405005c0c0800da449a085408a500910303003d615401c0500b40a0525038003204640501480003070b001041050a810107401c0e94029000c1c0c0384107040c640b4003541c689081031060201a085100140024a06200b9503904490b010f000c4400d20003010f40301e00c0c00a401074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 820246384 1250 820245134 820245163
    0xa0503030f03041b0311100c0b07030e07050a0b09041d010515090105010318061d01020c010c03060f24050c011509151805070e190906060c0807031d03 66
    0x100003d20211105848001a031344021300e003810f1071a260b10b03195102c640540c500c1003c04216107002a48103140c400c10050300000c101b101d90500c034502400504520054400a0003a12030018861501b50421011561020f4109240040c20002c02c801001e03000400702e08007a004072081c0110301d0900c9650701c2020003468805208181c1d00400050388816808281010b041c0341d40307111203620001110400075400302010805071030701d51100b003100e8046102480d10b58030118614400f442d05400498444d10316807410003203030340c8609441d6031103407150080c50401c0c3e41042002400a4118100c02006043d51400f81d040602c103074441d900b940c0c1d0005545030204203a440a000d820494810111501c401400f0300250501e480c0000004401070070300301c29501d95a00020b4095401000c46001202004041849110004400d800310b41030501038600200c4c5064404030b64903010f42c20040b80207800040d5a800e050640da0121076000c07920041080320a00d1403610b8525460070043c450340c00741c40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 820247634 1250 820246384 820246387
    0x150a06090905060a080f15010905270f010903050d270f0c05060f0304110102010c17060a120c03052119030605060301080a0b0a0b0105030f1e010303030b090a060b0306010c020a0503030f 81
    0x242e103001c47c80300060b042011510700e01414041042203e082904d1080310109010607680c4032840401d046c0b16103c2d00703007a400d50800c40720008040d03200e4001c00c20007621020820410145440d243c00002c0444404201c401c080e643c0c80c004982d60071000307441c00d441000300301c0b001a29100481c107550841d4044644154010003444108003a03e142030303c03450b03400e2000704180d8000080052824901407407620030a042c3c0000700d4100e071210450342002c2c2080c03401d81c03d4822540d261400c0d030300317440b80320984130b90040d895506e1803e280c01c0074410499a1031445503080000340d1341c00403c551003594080061603134450000a2a49a010295000740141405820500b0860034010614240203042d03516251030b25031108101c3c6c3c1c005040d20b8000b484001a00d01c1c507543d44507490b925a20610501a03002c480000000402d035160700425031f0140c0c1641d40b0800d41c2c50b400007407400e4a004e40280d0795032103003c0c40000c1c02548244405039081c0c0c0001d180312071ba140e8550103c2c2c2150300041040d55154070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 820248884 1250 820247634 820247653
    0x180a0f021c0e0a0506072304030f120306081203090c12010608151e040f060f061409040c15030b040f020a022a0618030102030f150a06090905060a080f 66
    0x101c0c85440c0b150200b4078041c1c070a86105650f010303298103009128905100482d02c5440510440c11040e0320340f940442c030b82d42d599940302e0070b1210380f0f80c4120104540c0726501c41d800a590710303c213003d10022140307800300600c61070740080c14400c3c0c1500001c3c1007500318030807a061481c480d0340390f881d03251007113840310000981603003030152031030034503600b00305000c43c4040c0d004c01d102442000441101504000343e202003219215841c20f5500d01c141d03888094901c5042600015402c0078590200088800540c4c01501c1d07090a50705108903200101e6010303124811640c4200608407001c044503c071400b480c9400151002e46400140c101d400c0000303034600055002c00da40d90902d07010403144c621690003104011080080719502050030842c03003200d0307000d41ea001c11108901c102404c213190409400500a54580c501990919801d60003100d084403c0c00804030698207900304001e0700d030203940c1da603501c90114904050101e009090050b0a864000800150020b05903409101c0c90400c0d41450f80540703004031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 820250134 1250 820248884 820248937
    0x308070207060e0108150a080d05030f13080304020d110d031e0e030d030c0509090f04060b01080601020a1415010305030d200304021c050105010929180a0f02 69
    0x4441c0d0304030005108940c021558180e070400c8850303501103450185014005140707070104030a00c44035408500035100b4141e168401a03001409184500c05200c2e050030301d40c0d140064640709004186018000c01010004500942020010140c2e03450103200c1d081c0300310030140040b5941e0310000e00305500080494500741500003040d04010301c403641c1c0b4034002894046c49000207481ea92221a500180366a40d4280005280540155002050001e10030382d8140391000c0d45914880085404546162030051000e001d580110707042802200c045e8000c0100c500142d80d0400c07140400010b0351840c2c40740200d6071003c5851040040e019511031405140c40701d82e240f00c0401030b10300c00b0140000940b03d40c00f10045910680007980e900640450b8201402081c101031803042c2d452800d000307805542050008980010b29411000b038881290800340104a0400c891030791414113600d215030b11065402000503400114598540c024821103c0043da240c0e051040720102e0f480004a031126041a451314000f89 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 820251384 1250 820250134 820250143
    0x31e030603010e0d1812020a27021603080f2707050904050d1106010e07050f090d030206090d0c0809060a112515020c01050f040f0b0d050c040e060103020706090b0403080702 76
    0xc090050340d285403501b0a6001803c01ca02070301401600081c126102140304400e5000d4401ca8800b0103400c65403001618101c03422000204825804a00100c0100d00007025041940388902c90303c29215008110611301558521441c1500030341d580304d082004039243da81c18125600843c4624018003d100d50414041c10f2440c070ba05005209404c08030040290601191405070b100c801443d0296580600e01c030f12041900038181640d03000352203260100c080540010b10036024030390941c01c03601002184101150b040447c88401002400c00780020130360b5052400c00707007000c461642461940310a00c0c922883c607029006c0c01c0115007020150701c05202e540703a0000440607044407000800b0040b081c0b41c02071b507100300301340c001810448000348603110011010103079005410303003a0201003415031301c88115440307800100c0189901c914140110700b504a0304000c403402c5905148600880e42d0f00c940054000b07403c00007041e25465200d100d208001411500018490b80c800e895405840c1807003880280740 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 820252634 1250 820251384 820251389
    0x3160e010323030d05060111100905011d0703020616170712080906161b0b1b13030303020a0c02130c021002091c0611040807090e031e030603010e0d18 66
    0x50403070590b00755000300048210346100008403c003160585600d00104d8960b0200036000c0c00b1030141280040380f00d0b011360448803140d4081c9000703200161040000074a10009001c000380b05501ca00c808000600b00036006d0040002d4900c0c10382e100302425200d80d000c50194090354654098001162010400b6a00e450780070703d40c1d01d2820303040e60329103c004c85549000c050201c80c0d010075603408103a603a501c03913007480f40d0b811400000e80c1c8042c038803450460a0b01c07a06607405105c3c403c000994031a0505010b0944100341302010001c4801c3c0d246440036802580a04150000c00000003000c1c0056211116485080c03482e8200000d40703400c07042d0300281044603d80180c40d0450041050074966541d650f25454240340030641d122884006290a01c02005244c02d4404002ea01042c000b51880c00864401c040f141030f14000d100390040c02920030745070b00c503000e028051188440c1c00c007240d40c4100b034091948a03601400004441c034031281010324000380800d030b050018180498000503002c4001c00c0000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 820253884 1250 820252634 820252673
    0x503070b07050a0c0206030a0e10020c0613021012090501060b0a0e040905101814060106020f011e0e01020d380d0f0219030b0601030516091403160e0103 67
    0x10001c003d20010841c101c0c0d050042c2c4100004404503044001a9014000c200c5195003141c0c104034040d02108c011b900143c0c136281031805941c001400c0602c40740f155103040e41d402080e108407205440d03425513454a1401c04814025901c000b42d600140302441004003604582081d142c0720800740100500b907945816003203000d18200190b25001a0000801d4a20140180340c0429200c0c2401401c181490380054003800341074650401c00340d550004918075041c3c592036030a443c55001e20050585c01d88841c0000c400300380d41e6421601c1c10300280b940c813802e28110b210303002601e082c400c0100d031002d40d02c800402091810500d102e1403040f410105102d042d1402c1e040c8801145c410002c005101c0340e1540001034111680d22101c041150b80340c411035500450744091100c046038990800e02c84074101101c07141e000c0780c030308008074a40748281d005410040e1481d60310008550f042104c40312890313144072117032509485010603030882204d030010080041d02980480c1c038095072550400e0319001e280e4070060700c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 820255134 1250 820253884 820253887
    0x51206030f0d03020307020a0b1807050d030503010909081b06010f09140105040203060a120501050717010311310203091c050406050f12040807020a050103051e09120301030503070b0705 81
    0x7010301808108042c030020107040060300c9030341e1500240c1c14045400c00c0100b40c65408010001d20664040c042d500c002c2d042001c841109403618203205e4004103100c80540481e000b0720041202d08103907001910000d200d65445824410903c0050304036410700b51450b030454006c0070042c0003000c4802e2140c0010040300c3c40900001203070b13034a110800700b018018940910340005c005419929281c00450080c01c10302c0c4034032198415428032900800c42941c44078005072852402020030b1805119260581b50441f400c0c10000006104000440c0c5880200d881c1d604601d1055605060021102d4010b0200c0c0d51000341e56860100c964508141407035042d100003101400d0b03034038880740d40401998240d07121420025a11030440321030030068014140c0322101070703450800f000100112030014201a034401c1d2004c00c2e609448800540607100d003150100c01c07004400c0112a03503905035002c1141c011103c070059070307130503160451107400550090300b007a1201d40c000106101009031b1072450316440101032030501d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 820256384 1250 820255134 820255153
    0xc01092f0102031c0f02070c0b0a1b0b01140103091e02010e030102040b0f03070e03010203192a180f061701060e0307090f38060c100507110a0305120603 67
    0x50a07464031071150f403032591701c02c1005010190307541203480140c0c202e10100c041e02d55501d0076034420340c0080c440ca0001040c0d040c903e4050082c010203102d10302e600002d0380080e682001c0344003044110b004402810540c440c0d4403280410001b01c4503600c00c144262040500c07014a0002422825110140368066803040100b0407040407500151400c4031038411188c0d5480d04c403940221010140c109030190305510010605c80301051512940b08a1144040e09108851503184080b070f0340304440c0160224400e121012682d910f20654003800a0111030444c296000d858619203070120105030030004c042001c001c096551142940d1100d070040c0028602600c503400d022011030780343d18951040d1071506031a5000d106030705105401c1100c025001d015445c000d0210051000950b04403150704280c0d50300b13080542090350500c8002c444e13410307800c4002003402c880118040001004010440800c002080e0706d5188004418402030b41c14038040da0302c1c1511603461400c0306800c5400030b061148268040402d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 820257634 1250 820256384 820256407
    0x7120209010905042310060b07030c061d030f0d2f1b010e010507030c0201141306090f03050d060e0f13030318150b0102070501140c01092f010203 64
    0x145810b54800b140c000c00c0d40c0c0c64918007901500c2d140142081700489883c09640484400101c201c0050780c203503001d0101d955603d01c0b000252150307180290000d01c4007030040000c1100d541003034400c9903404c0006401d205070301101703a003950014490200c1c6008001481800c0c0103250003100f1500a8142c0407403800043c41414004001c0d1100c10072032400c80200f203ca0003140002c299014a1042000901007030a100e40c4a90003464100c03110404607250040c0ca4001920520a0544404944140d03518548a0600c00090f0300480142100c00c1912500e500000686401d850110b5601c02e443d920b03240c8600c10380d154107903030071a0000380d2010341d80c604000d00603034400003894010321071b8800030301c0c07403421400c0460203006120100c0c090103c41000302ea0030042140b40e10749030f11510000c10001d03c10041c004a031201340d2445441d0004501301c103980580c0300b100000b0030b86d115807503000080350012035581c0d00c1d004210701540c0602d126200c42010081c0e0321540185580c80c403d2014501e0000380c00305 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 820258884 1250 820257634 820257649
    0x10908030105030709060f141503090c0132160204020a02060703060b0702010e10111617120a110f070e040b0703060b0a1803020613180207020f090903130b0c071202 72
    0x90b00382e00547d2310402c110780d522080803024000103100e8070303560b491401903030096880031071341d0000b40000c2c4185240700300c600520f080c1d0403000c0390440c0c0100c4680111910b0850340d810030a070180303100124203500303001656503200418481c0f1103a0003074111460a0703140581144ca0b264070850740c00c1d030100101d40c010703030b0303c8524203e0301c131011074200c1811070300003031704880c403000e44034880b0000c1c800c1e40c6450808404030f600400c1120311200711480d00c1004114459102d28111843d03214403e010704c00300d03c00501600c0744008400408084820b00303150407000504e0904641e0250f518000324105210034030102102442d4043c1840c1824855986021035503032591140300591000c004005803182c180913101d9585100554008040503111000051354145161251068110717480c40603840900843d514001e43d00255001000d0007090014001408882d460040c0032a90b2404100324030440d05020380003100203440c0c80b02503c1d4442040c5038410b45800d00d00e421070700144441611000041c0e540d500e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 820260134 1250 820258884 820258889
    0x1701150e06070602070c03150c1106010501111002030c0706060501110606132012070206040809040f11070302070501080903090a030f020103060e0f160e0d060b12010908030105030709060f 82
    0x980003507542c03440741410802801980001466000750001c000144000301265401600000c07000300315481001c8000c0d1040c0d00381559010040d04482c0040100b0340c0902410b4100c01852002e0ba4180300c410000d02c812640215400c0282c0d41002c6840f00c103020192141c6000f803d0282400c4400c08519696103a0720746e0b000344054441c0c5281c00e08840507000542040031200d8540081c030724002184800b1070000c2c0c101000d00c0f10180d02090006408a10008940f40210b800800040c070303111560f0103000c040c05074905020304442c0c5409910800303030045030040c0583c1d806503000e010b0f05170800000416413800500250345d071368400d200d05401c0399106280001182c0d802614599100d52510050300640181c2e8003603030130100e0710820414a01d202c0d98800e03100d00303203200703a0300788680c0d1240064605000c605041c0340c008050680060008140d98018100400e0007854011100501130015080d105000c00407161003030088010040c500342045a800901842d1405002079402c0c40e05001c144003ea2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 820261384 1250 820260134 820260139
    0xc15100617091606022a0607060b010c0b0c07052e090c15120f05041a060f03190c050a030302030f0d02040e0f0105100f1e020f0703031701150e 63
    0xc201040b101d00b0104000c4203100050301c100340101e50340d24800794480ca080440c03030040780c19290981185551003001300704000380082030341342000c0035610b4100007002c00c000954144a440c417a1800416907003010107109586010741c590780d403000c5203041403c160302c4008991000c221102d81c01e1566104901c0301c6a101d003403010000d0000200d0802c03c010f006194003071240350400b110882c0c0790940c0701101c1c031550240c00d10240011050740b07068200301c4808548c044c0014003c030f69801000040034184a4118000800400d003090b002c0c1c0c0001e062001280300001c003100152481d03802c000d0051000402003504a800261b45807850324060340724480d0450400386501c00140240e440381450341503802508140003254864640300481c0c60501d003081c09864030402e245c007070744034100c0c1c4540344000e61400d01d81e03100e16009460341c104130741c0a40d09101840541c00360520201d03003d0300401c210b40c011030107540d48240c0072030380f000c00021070301041e004607422950b651095a24250844100120070006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 820262634 1250 820261384 820261427
    0x160c1e0609060507030e16030215070501024302090f0c0d05070507020432060a0b070501060f060804030f05090d120e040b0a050a030b0405120c151006 66
    0x26803401000030544050300a201615081c10f21110540c964403440303040703100300b086640b8040490242c3d8030b001d04074403000354010009514280c44a140c0409003e145124000141c117000449217400464103500d8403031401881035291012a080c49409040030818045500d44e105c100c4980104a21420040000c041c0251850101d80c17822103500c200d85c6142c5600d0b00401c480e04083c403000300f00d0790010300168880d5090801d485c44100144001c1d50602c01c603440c9a050500c40b039030742a01d0b0b040001b003c4541c050781006d0005a0340351b0100051088a1151000003122401c240d08020524101e801050170020320000700310009800100c4101008503d00704580c43d5500c420008002d2200140d000300b04040c0f81c521014520b401c500740e01900203085809202c84008402442042c007460300c901c80e402091108100003003034200d104a074010b805201925075404074546000b240e80e001c1034490b4601d900c50032911300400140200c00380c120140342c4c00f001d400303480e0007002800c41d400c401110020180 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 820263884 1250 820262634 820262693
    0xf050405090f0a08070302010609060501050304060b1c0b0414030a080a0f1b0215251d09160201050f0f0106110c0306070e0103060f1215020903070e160c 67
    0x10030400d442040c03401c84210341e1102c5003440c00e080c0d5178010f00d90480c059030a018001c6039140503809600161181a52480d055643d00d03200d00f000303000c0f4003d20b03541009101c4034154000f84031440070111180501400c1c1c0c00c6042c07502e42100f600c01140d07a280221713001404580307641540820b8080e0020040603001c03c019841483e401c0003000070000b0380050004c2d410300441c442e034012030300207450312126450740b1066607140b000c108d450030441c901c400304164844591042e580294181241c0120002036214820409030204032800c0c016a01600c03006201303800380103407940c240207243d132024003008040702600300703034107071000c044010701a1205000607000070540c42c0100704141d101c6513070b000741201c81504001101510019182415900003803c0c0440440c0203c83c083d01c010031250080c40c054003000396911020708034140c0b001c4101209400f044004c0244e13030104025400b800644520035180c1c1010303181c82460303582000c0303a001030040b00c154076000300d1710814010343c0c00c0b81201260a140c04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 820265134 1250 820263884 820263901
    0xb0309070902120a0c030b090a02130b13080601090603080301051201021c0209100503060d0305160c0807051c02030a03110a02090f04050607050c03190311120712060f050405 76
    0x1241d0304041c00480c030216045032180d461041d042d000312038411040000c465400c0007281034492036500b5640006c0003501144007480158018002100e51040e800d000c42d484540c04070856200e500289400c80740020140000c6509010b55070060100c3c05c0c04200003841c65580c09154001481790610548829a4076017a0000a40450320854a0840d107055880100c2c01d85400940141e208107010b0906460110350090050048a0080c48018200e41c1e005806943c201d400340c0c010444c0ca8070740610242040b001841255221024100c10720292038203030300744020301048000c481024a10340e110022040c0150f10040340c1040119012300d0a07408011564a85500d4200c141717400a410040380010000090800d5600710b006d280710380706845140d04d40400865643c003d8480c0007d003a0400c11a5154000c81c02201e01d1000c030303040c1004078030f0902d00c3d40501e0064104e81d05014081c0a030701d08201e007495000c10713500d52030041a81d08221541c103140303c1d03543c234101a000390b500030341c0c0e5000401c0c18407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 820266384 1250 820265134 820265143
    0x20d0518031e07060309051b01110a0807151e0b150403050a11100801170c06071a0c27150a02070303080c04061e180b0c0f0a0b010b0309 60
    0x110001d0304840006110703008211140c4612480c0d07003000c1c01110004105580700b4020380c01550780000040c0354101c02a07001d400080e0380150442d042c09002040907020400034000c12a045018102c21500e8450718180003c0801252000d0615149003004154087d844811052100305540340001100c584180c0422032001c5101030700554440c000c5000010010000340f071745000b0b0310600032880d03142890302c20301041c0c0625500742408600e03120014800c51207285501c1501308021003c40b1100040305c808038009a010440c25503140004e4a00c0254072221590019004803000e82c400d0b281c0a100c400c1608060346107075240c910840c1d6450845015900c100e88400c1e55500c00060b41da4070303c4410b101950ba034245210840114501d00c0015940d1969981a1030440e01e464595903144100441c15011f04446580ba00c024000d2181080802140251400010303100000c2400c1d0346159440d00c81d1710b0000c000d000114554004820303440041d10039240c507070445082c43e4025450380c60304080581070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 820267634 1250 820266384 820266427
    0x40c090515040e0631020409031106090a020102120d0e030409060e070306030f081605250e01080c0d1a070302040603110315010e04090506180607020d020d05 69
    0x141424002030205026041c495859028000c4404000001d241c0b040d050302c514040f5080200b00c0810744000001d00481c9000c5240300349810140713292881240d000900310f600380301c02a400200000039002c0703003240802840c0d070080d580c0781c010304200e96260700023503451030540600b100c07185000c100c44031041e985410200740c0c220900140c81d1100d4454880303200801e05072107414115010000440c014900a00c1400c0079072ba00010141190f089945540c000e5901c000200700c1c04900210111000c1481031090b00b02102451411080780624030f820301d000c0c5e43c09504501c0c40000420010010340800045040d10210103681c100c440c001c45047c4131403450b092559440005210000304a02c99615a000b00141c0b120f0f42c800308000401c403582100103000803a0250b0700e10074201f01040080d030041d0300d600c40350342e40140049810340199550a0800c2410340b1442d09070310074108000424001442869440302c020f10041c202c40d1842e410083d070b121811f400980a00000103821030340005401c4501ca030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 820268884 1250 820267634 820267649
    0x302271f180e06131101230c06010302030c031207021005070f06050712090503030a1505060a1706240703020a140c0a080607020a0b09340905040807060203040c 70
    0xc801410791507150240c20480e0503a19103015500000e00c01c2c65007000c01d40015900044e800b090030410500545e5020307a503802655407040715002070810f001e070105c001c00c0f0034000300018021552540c81070510305101515058401d4200c18447c601940003a02a12049030301103803004c41128a288040c1c5092150350b1004e0312034090400440c06101003900301034056a0941da0305544880c98119410440d40d01060082160700b0400100710001d8650300440101d84104150100490b81ca0300000c0c5a42c1c041003c400120307000e51315040c201074026001551003201601c00000040040030605011640181d001c3d000341e40108109040c503100b0080403016136401a503040b105075104a00316a038180760340500e03105441c0d041c0049405a404200d49000d200907400804a801c0640d540046c1301c1c0e0001c000001901c81d0f180032020f25450440c0a04002207420150b440c480b0703251200e4025030740c0c2c9400c00607601b41080d0034800007030b141c1d00440b01519007011006807240c0f96460281c24203042e0b81e00465 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 820270134 1250 820268884 820268909
    0x11a0d0b0d0506071106091c20070f1a07172b1d0d050a26070305040308091c050703020313080f0f010501050a060509030304090c0305010302271f 64
    0x110340c54100c08003284058030361080b501c0c46c7d03441019055940400300ca03500c81d504600c0048a0080d40aa58007140e14107aa070809002048541d00451030101240e10582e881d1083c80010010102024641905d4040c0403c9240c940241a00c844031b240d440c04410a18200300040e1801401500c201202d0254441c4050341d030080d11100c00b403d019068a039030b4816641c4e5a00b515861202e40082c203e10f40e01c84548602e420207405901c00e4030784c0d012000184941c0c400a00c0010941d0885e070201510850307482d1000155410b0a080040641034000c1c1110900da112041200d042d045100d01d82c509441e5920305141d80e00c0040c50228254091a00707000080d980c0020080707a2440301103044501c2c1211401221359054070b01041a090711000c0c03160a4001e0143b5905001c0e81d0f22443c014288400050b00f12483c296464000d41e040344c0c4441074170400280d4803c014811441d21100c0c2242c445100005400702c500e80c20803109800c440a00328020204140b4800c20b490280c44c2c84980041840b4149070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 820271384 1250 820270134 820270141
    0x160b091f02240f0105010215010e0601050c100c0f1713030905030105040b0708060f0906120718020a0f030905100b040605030312090106060c03080f07030f020f12011a0d0b0d0506 78
    0x12810b8090b5107034410101d00c01e0000c03c0369440010710148800480310034030400d9183c0a2a40c1180e0409400541000010059803054085c10000411803000340080000c1c000e02d800002009045400e0742c172000c00542c1040e1034849003010507c160000c1c109000024207141c03925066444002a500c1a030300765082504002c05d2001c030403042d41c4104015100c8420340c0e9607800c00c0100d4004c04401c19613015100b8000304000e410b081d00340300c00080101040b214801d8984900b00600c1c0400455102400e4000070300020813030b40300c44240b4400215081c2400040030690300c164981c29003900d0783c945036070b461040010035601c6800000c01020f000e010380e03541344002c1180010140c0300301c032070249560811100140443c89041030b5a542c64141d038860081703440d540c01c440c941d80c03006440c01c3d04041c0c03035400300c201025881c4000e000c3c100c0001e112507030301c904002e60441203503c140c1c403080b4460803070400310904910348400c4651140c803410380020200303810360008040c2031480b04041d01e13510440080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 820272634 1250 820271384 820271443
    0x315010201060909080315090c0f0f07050115080f0106060e0f031c170c07170d140f04031d010f03020c0106152703020f040903031b02160b091f02 64
    0x314007500c7c01640d851003880c0d43c801072007901c1c4800d460b00701d1510b0003040582115403803800500052040104040c0c6450156210030313007561a0460400090000804104031254040081c2550000004000d121151400a01402c01d1010400d214020b14450b80c0b01071840c0d0741030280015210b40c0050094010b80821b5008104040a88002c14480100b101203040d0064400c241c0305400e40c80031041061075000354400c0c0c0720b50407041c03109000c552903510010a9400c601f50140c803c0c10141010031461800c0c2c20010300014800d203a104c440c4000000348034044e684040d11000380e4503a0304026a6804010001e28010141036000c103030040088100d441655900102211103102603c264204000b00c0380b000d0805644c0340d01c0000e41c491003240c1c41d0482810641c1006540c98000d04000031700940711840d00100a81c0d0b0901580140c00040040e00c00007031144000c4090910b4614072401d0161380e0b80402c030b440700001840704040140c4101c4031001e510810804886a280c1881c20f440d01d01d03403644 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 820273884 1250 820272634 820272637
    0x50a05010c05091002010204050306041713090218060c070311030a081606110310180204210501061208070209091630020112050406020904020c0c04060506030705031501020106090908 80
    0x2c1c148139a6000400c50012881402550b044c0e0b64001c003d00550744807030391003043c0300340c8280070307400c1c000003e00045400e50310400c40003008200012015a80360003001070071910308600105103104141c140f20b4041c24120000d807070016280d0011117000b00e1608100064175040c00d49000510104002074211000f18404600700d4800780310b070300140140020000c07401c82501007100c0d890000510020100010504031005112040c2e6501c00145841d032144541041d4a011541c24034403064040d040c4010030a091145074002c0520306080c0480000ca0794a03c070182c89003640c082d11031024000403c400b030006128440c1241c11107030100010395901d000d0400c0c4805800c2e8a119106910044000c540d0080314007176680d1703a4140d4030b00800d00c0324031440000424000d002518056070a002c200c1c007984440c8020410f040c1540018403a40701d00c0c008202c25107003107400150081c0e40500500045903004015280c02a0552042c0c000c0c516122300102d005080f02c2d40a07111450800c180c000c00d0141080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 820275134 1250 820273884 820273897
    0x60f010e031e0706020d0815010c020409060b0a05030102270a170708010f0510090f0f0501060e0a0801020f09010c0f08040308030f090d140705010f05160215060609010c050a05010c05 80
    0x400381c2c0c40c540c0c4d4940084e81c442c1300441442c00812403210004066024100302c01e041801c05040c003012082243d000700c1c00710381045000b00c81c00b0307644046696003860041d4084008000032402580f40088803515049050300b0380c80c4a00001860b00c0c20b0403640d503070303e441800103001d01c0c0c42c10180c0344122100083d5106910310890301c10f54a0540c500140101d64025148958072801625807450314082d240703070042580c16034103444146c0e02c854006000705103014080c001c200641d0381303408000380306040001d4180182d020984980c4104420840c03d480741007518110407003420400b1202c41d090802289000c80c4807401010180005008030800c42e180002e580030303200c244000b180c070782d452540c030b2030b0b49141806400003c120001001081d407000c07071006203a614422000400e48072031f40c070041001d8172819100000e03107a20107030000d28829410000d4603820468036008010038140500071519600ca4014410304121404880c00b050050800001c2103240e4003c0c001c00501031300c08001030841c0c000300c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 820276384 1250 820275134 820275193
    0xa05130e012f120103030503062e0306050a030f030507080c10091101020c01090e092b0206060604030f060b1219021c0203120a02010b0d08030a15030b060f010e03 71
    0x1210b507108001098410720001d01c450648180d00b0340e201660103410080015a00030b0042904030300c0140d08901c0c0c1455402c03500b102c1d5032402c640e540090300f6201c0c2a004540645403080c010000724a442c00071004807a01800c003941c1d01d102c03500b05100584a212441c00a500c13035041c0c41d2409444d0b83d2300882c15140102500d040c0504045c0049889290000340c560005440a006000a0b5a00c2d43e6451708aa030301c0080b141d4203e5045204032100c8205240c140c400031180c01004201601070021075803140d412582949071600b941d40702510501090b1014080b50781d0341070f1030502c640b0385085000e02c1d840e40346c08880b4000019400425500c1d40b201d0224040c402c03110611564544011011410039030007006040d600f01c0b8082803881d00e8101044000840d900c07200b42180c55194a106581c1c5540205e03192641c0c0d1401100c500140d403c00d0b01540031204040d9010004104120189600860111405115040000300490b5030303d10902406074140244420111700103040750f0320658050b4403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 820277634 1250 820276384 820276451
    0x613090206131e081e10111c020306060403063602120f031c060b1b07060f0f03020a0c20011e0504060f09090609060806060f0a05130e01 60
    0x1030000c0104154200d2041c202a94812261a90900d50302842400c0c1e00c0d40500880341c080c03135240461b2064039481e0504003502c0f1000a6100c644c0d8820a90212058201c1c000170341c6142401800b0603c0d82c0b18510015241595400b00c0c0c2c150702d1000c1628101660b004c44104048a0800858041505040308202d1180e1102c4626031106040800c0c048000c0c002c030405581020200580041a03074054244041002d07a110004070314130284c50007820200e40561100c01401a0102e882860304006411000511100403446054603511281038141c6c0422481c025880d1810844195460b101d1004028404160160420381d005417460503d006500c0c00d0b07803034002c00e40c944031400e11007803502c0c1c001500180c0c0800007403100718000c404c00d040b4042246005400240e0710309040d822240544c0040803240c1e1105070030450210104805c41e04140225908500407811000107080204e0342d00c10240141c1000042c0c0c80d49200d26486440c84144240007407000b0041c01c003c5050402c202401540c10250 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 820278884 1250 820277634 820277669
    0x30906080c040f451e060308090315040c0302010f031803020d090b120f10080f0d030c11150709081221010b07020105030c0d0f061517061309020613 65
    0x407030380b1070440d1419071205200c007005025441080688046544404801d61807403400f040da171240e00c2610011809550010307211002c0c00101418031030005030104030480c801d000c0c800881c1c522001030f02203940c2401c004202001c0d00005802500c1d01116010306c60201c07980000500d6004524400500d25a60340c03101c3c160303280c42c080c030303103034019800384900542d0710400164172481881c6015800c1941d5a445189440c1c0d40c529551600c07070400c045800582190450003a22509802002a40300960518030034060340651540d40c4c428147c0141003080584a0220b19200e000c3c1c0c594030050000001901c04585400b07451080c503611140c0d1010780c1c0001001203d003c0a55100c0e168181c505500c0d40d07524040e03e940045610350030182410001400421603420080c005207d244070410604c2d002090700da141c408040000d1540491a206010904d00e6081406030f81e0180107901c01c400b29054000b141100b09103100a14003908025000440000c001c800d600960600074110303500d0208100c4c1522 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 820280134 1250 820278884 820278959
    0xc0206040b0c0a0c060207050a05030f0d0f0203150d0201110a0503030405061602070b070302070f1d070509061b120c06010e090a0f020105090103200909060a03030906080c040f 77
    0x716107000600011902404c1100007045a00242245030050301140c6d10b5801c50f40341c031410755120440680e80c0302c0e00042e221340014550701600c000c41000300021820f52405580e0302c0b10150140c20300d24482c8481400b81000c582c001c511402016809604490045900345043c5940c0d074401e03503090321144982800101d0041d41490a405040c0240d40a0030102e442c0124008050304142821000d50141a0010900552102144004121400030b401000c002d00d8201c0c850140050600010032808103ccc242640d204c000407140800f0100c84c07072100b10301485411600780086190f0a82c0003a000050065001c000010312506980800c400c13402240c84080200e030360352005180040c0002602e07038202c4099802074010340030458041c1804a020101c10341d0010007003404051a000d2050f01040b8046141841c400c1d11f6405003054860010650458401501c80303007181c410401000301e100c0015801d0b4410000340e40080000c010703044055600c0c1c91548031291210500b039103286442c1007640715440c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 820281384 1250 820280134 820280137
    0x309230c0a240f0201110a0306140405061c0201030219020d091d160c120203130605030f01030b25090e0c0333180a050c0a0207150908010c0206040b0c 66
    0x7050140c04121002c00180d5081e241c8101000b40b04041d950780c2c22043d1420203000f40101283c2c2910350380003e041d810300d41e0701441c101054200754016031604040151035146c4902611b101c81440390304000128035807004a001e1310540c4401d0611010004d03d001d442600041c2050072944241c8501100759142d0f20260b04580141a4000440741c0000110b00c00ca4040c0c19610400703006460040c0d50f5207001e80f03401c807520000515140c0181d00000340107015080d5405004041c000b245051403a50400c01b10194926806001c003610003501013020400d800303480c075007140c421019506001d02d02c4400e017070b01030301da14601c4c072610f490141d499001400160150f41120320030140f00000e00c1084800180c0c000501d55407600d80d484890300d15070b60300e9403980c070384420415000300040039409624007c0b0840b81601c401a00003400d02105000316842c450300800c2d107805641031000c0e518861604200c00b140d00d0a050341c001c41c5503510305068102d40c01e901041d010320840c00f4400300d060603100d880317010005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 820282634 1250 820281384 820281419
    0x50a170d0e0406120b0108060a02040605040306024006111504050c0a140a0801090f0803040f06060b0703020c01091508040c030b0c07050c040603030f0309230c0a 71
    0x10341080d84580c45541c080c0a20111040c400361002600303544881014082c0c0d0852142664420000c0c0010451000200706840d4800905681507040c14a0585c028220780164000180015008900c41440720412440e00321105819004080c0407110315880e005001640c04010703800818203040410300394044ca002010321810b000c010f02959000e003100300000710707020b003007102e1901850301c0f88603143c1e440d000b007a40030348207140111030b850454030100a903081c050390050605034101800e803800305000345402d107001c0740c1040b0055642c0d40d0f60700d0140da01081c50700c0010941440e10f4008a0a20488409420100e20a800322001d1050380001928051003a00c00c42111000c08111201d0580c800c1d000c3c40c0e0028803c40820900d10346a81c2e840311142803c90b40c0d60303a4440045580707402c3c0842044049040c1e141901d08220b01070a6880003080f580e0000000828540c5842d221000c000b1404052407d4221041c44003141c4010303c0d0343c15440b90880180306100d015500c0300411a1451a042040c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 820283884 1250 820282634 820282679
    0xb010311070602030a062601051617180703030c020f0409110f01020a0c1e090e07050111030d052409010803030a050c130b0d060b090f040209040e0703060204050a 71
    0x40c205241d4950b0701070350005040400036a00e6142c009803401c80380f49441d03540e501c5440c42c800e452210510650031100d0051008242181c40301a80c50a04d801640500c52461800300100040d0340b0b00301181d5104c241d6006046003403242d40c0000040c1540407010303441581c82200c40701400c011250030002039a0203d00e01070030803042210220075618204001030044c40c810b005441c1c6030406034131080148030243d4010196202c000240c0f05411a0342c4103c603018015141003000080b600c1c0020700e40d907025034000d450500901401629980d64104103440724000146418006840d140340c03003000c084d1003c104002e291002600303100052901c00c20107410780e4641c00043d400c5a0700d80300828064800607120564001c0104400328085000001100c01b03848180300d0696922000a2803604480c202c1d4022550102c0c2409207400300d40e80c40d04908604641140c0160b120510000081c0c0204008500c2e0b0056124052001081041c1d5030050811100c0484019110507a180910510300340520b40150 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 820285134 1250 820283884 820283887
    0x60819020723010b0402033402102d0e0712030c110609121b0d050a140708070f0510030c020303010603020d0612050604210e0105030a020c060412030b010311 69
    0x805001541c0801c0781e08010b0400003050221100c004182207903c01e45000e0880b01e03021110340c4071401d090840300f111464600e0301503950404414003d403255074802c0c060144988801a81c00036860800c1603216034070307404c000421440841d0711500c00a0950700d000c3e6031240130f0a8000a00008060b80c5809450f403d03440e00003804c0300940e509080c4001c0b5512482c0d005405000818190f11003089403030a1001d41002007245083c0940440303401417110390714030300ca594049050b00c0010004100a81c43c246d00ca002000d09030900c3c4652420864640c018002034899007030006071205d190003071941101c20582d0381e402e40b041303041000c4003070359803103501c1e08056071040004100b41c80c480da0041031050104000059025110404180340381c600302016074031a403148080c01f050102d094180c0000c10746041440034100ca82160241c031007250148005c3c184800800010700800b40307034044901e4503189000707451007440c00c2d1410b212071041e5116440000780c038201d04202c07103502a2240201300c08043c09143e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 820286384 1250 820285134 820285163
    0x1b04050303071b0b0f04330305040311010507031e090c0e100803072a0509010b130806010b070b07080106021c1701061e0c020f10090308040608190207 66
    0x10301c10684807400b0140602d81500c000401c1e10b1a02c1c058180c8040e0f00d00007940d140d103050704002c1302c0c0451601c7c441c0e4080705c01d02020120b110860f00c00142d1078142c00d000c40c440d90303141030a6401c41510425850b481d400c103020010b03a6176069002400e0303208942040320502807a995820200d03413036000b00500d407a000480c140f11700b0603038103413195200e6500060b1020650302c03009035034255000000c04441c0580195160031104080029981d40c4284210081250b146880005550240c040c400c049518000203030342802c61541c064a2800342100c0c004445565039202d91190099101c80e0059414007411408903950300e204200c414103d800b6070f4000d1449506e01043d14a0460513210400107100714415000707982d2070300070400b03402096a51184000400d151200d1048004c0c08228941000441e03052040141e66503000319031004001d980c0c20800d01c0c0302c030074183d40b103d450740c0000d4041180424001100c3e80d008070540d10609400242a10405502c2550002d81c01800c0c0001c0a0349001c0ba140c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 820287634 1250 820286384 820286393
    0x1b180e0316020604033c020a050f0103200414030604050c100c060c0f0e030111040b0c2a0307120809010333031a0712090f0215031b0405030307 63
    0x940700c181d000410300e91803c1d0b030f00d540b004196000301001c0e040c0e10003912241d00d511006090540c08406410595601140c000d5001071000b01d00d0f8084c1c1c511803102c14a595000c0c1c0d01c01d40c48400400701008941704120341e54000038046030400c1c451005203074228101810541804230740e0601030fa5100c0010f1842c0c559600410040c2800403003403604104100c8810008550103001340e0344040c0d2207031141011110413010040220f1010341c20280260b0410101d40000d030051000c940454002600d80b0b91911803150701e86080c1002c0e006a0749051030070344400c3c2c282c041c00465403415441300310226480c4568030014030204030480741c3c01802031201403041e0b54140d4003030380242c01d0900d03032440705100043e80079100b0210311400000d8070071050b20103013090040049034550560745070040d0351b6040091034910001801c0c9004031106540440c1c03079484907802c0008100b1000a640c1d4020034a0714126008610045241c004441d480d100c0d64051602030030349014a801c039816179038013501651030a01141c44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 820288884 1250 820287634 820287667
    0x6080d0c0615060f020c030304080c190803040f140406030804030305130305010e07030611040b0304120509030102030a1a0a0812070c03020a0b0403261903091b180e03 73
    0x14191000750b11031103a28000350076056a5000b40519807101c003d0600f0104009203803900c00d0403e98080e601c100000d01403e41c00140340110401c2c1210240c0343c035004a00101c048591070342c81101c2510000c02c0c0403914001340c881c13841c01d41c3d500400442c04840c4c0542000281c3d182480054400e00c410003090010900c50380c028011030328919124144a0355a6132900c1c219000c41e04041c0464124010034410001e550044000c4000446800348c00c3c2824400700086034030003e04014072001000404070101c502a4003a40d1411f00000d008645904e401890078010b098820809801c41001c045292030524001c0034000503614144003c280d800b0346d030302c00d030b20302517012110540b890f81d848003000005070f80728880c84001d0702140d55100e07140da25601e4010845403040290764941c031030765207034500850340710010b59407042640c078102d118403852403100358000c0525080c003a011850801ba003c844803403045804003181d0a11100f000b14101410b40c0e80b0459000a81962040d00700700002d000840c5101c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 820290134 1250 820288884 820288907
    0x20403020105030a0f15030303050615180609031501080313120c0513150305150601320f0705010c0810030c030212070503100c02071d04170c01060806090c0406080d 72
    0x90041e14648100388851b04d903034030480002e0307120820440c0b00c0c02c110002440d18041050032505000b143c42e43c14a950b07144040b264064500403801e42d04c1c903a010001c0b88025003c1208a1103196121445143c482c1c0c0150000800090750718400580c000404803048001ea4007d103030200a0b500b000104901c0c0f40e05011101c0034252140c1149210000b260340c4d00c03004501c184024161041150010b5280703203c020401410b00100caa00c1d0f4250b00d032580000c68500c0200e11158003807105010301e00100d401070562014018801003005030030400f05500003444684070781c5505241c1e42d01d801041540c5402800b0082001c02c11820030001403c00d4841112400c0c080390036120001d80b9600440d14240d0f14001c107464a0b5290046c003d0625018440080940105039554000c5509605161603080d0080c000401400f040c9942503504684081903402c2500d2040c001e1190540c0c07054410f503907840548240c030050003a00000032107445c107886070800304da620310301034042500700003802c1d0b85580b5400d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 820291384 1250 820290134 820290161
    0x41a0127050912120613290406120f020a0b0901050409110c0d12061401080403050a022803020f01150e0703090206070c08100908090d03020a060e010c0f03020403020105030a 76
    0x3046411090750303480d00500002000704804d500d1600e405e900301b2050800e00410911494071f02808a11403281d601d1500145c21403854241007100542000b0800a08541d03003c40d01c0c0d0380704c014000c0c0c20400914900001180200c1d40c648403940c40e220003000074441c1036003441c0807440410042048070350a40210410168030750380c0c1c1c0d0030242c6840b1010b0814101010020005400102c40c0c5100d00b100c0c42004050007071401212800103250300060010007000d0005802e00030701103040c1f20388610811820340701c089018510184149110500c02c020004441c0890240c0611150034881c0301d4140b02d400d208019040c40c8046803072800709100f0105201030001c0b006c264a6214250241c0c036490020080c20348208101c04c08240783c02c0e20542005040c44410700303918104001c0c0c40201d000c04055580d110030031140a00c0203001440e0903481d1103403200300101183c0c189080d0302c42c0c5540651000561410f20f449210b003084080100710200c0c81540002408130b10f051000c11841c1c0d03d6503124000c000c01c1c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 820292634 1250 820291384 820291393
    0x6012102010c0506071107060c02062703010c0f0f0e06070609150513120206060a050f06041a0a0908070b030109051b0c010903020d050403050a150212041a01270509 72
    0x1a1070f81d505001d02102d216010940000c09003440050820440b00203203011319101c104c400c66640014414402c410301c50742d00d00441d5401102c4030064080030108010010000c02c01c00640100107000b04240c9102d50021400100c01c0380402800303027204080e4090010082442c04456541c1c4500070300d10300500340c1d01c1400340200141d54814500c6528090601c03210b41419404852500c0446170540c000c6031400c54005505203c02c03078851088020079100101c0300003940807070a00c04510a40101d41c401c0142c0468003948080107100700c4010806040e0315507615000d10b407203a040c6030b40c44c0b60510818202c0b4000708010003142c04154091a0040c0b50203000440504030480c000010703401c020300c2c100d4180d659a01403020140c041200c0c0e00804143d041590034107146171101c07612282902c034060f00c0c00002510365645000725a040300c0046004940414940c00d013030030310413202803115003030180c40c06010001064100c2004901400c082d050003030403041204014459004e0103004e410815a03204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 820293884 1250 820292634 820292657
    0x1f030b0a060c06090317040b091002090319021c03050c010e0d08160c1401021902060106050f03151206040b0f0f13150221010f1406180d03080402040c020601210201 72
    0x40c0c6c003c55030041c1e0003a401960542043c0c02050700703100701d503110b1602040c41040780c005280c4000c03894000302d210b030440c85140802680040b0701007107011a40c0c182100310228a2034201a081801790000000c61030003080700d48002c606881c2c3e500c1c407c0840c03501046034000000c3c1c1814a030844681600c400e441c2980303841c40c05654012070050424003005150b50042804824101d5402c412591100c961000308070740d5140c100d000c3d000d8400c1130f002d642c100f1000400511081c03402004d900c080840503010f012480900280c0a44681050300c3c00c0711429403201c0451007400d01c8880c098082c0103d4003505000c0d1b10340c0c6400481301600618210340101420b0b14400000544d44040c10890030000c01664095110401d10601c0d80e105811000328280020002e00c8000d000e10201002d5480076540340e555030b030702204101a0405a00141a884040051017400301648540d0041c0558402d46052003a0481c2d02c7c0283e0f1100d2090140030702444180160326030002d503103030700c008071a4011b041c440320015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 820295134 1250 820293884 820293917
    0x906090a021306120e070e01090e1e0f0714210f010c05030603010b010c0804090b01180f09060b0309061902070204020304060903082404050402040204051f030b0a060c060903 76
    0x10090f40b201000c02d0482070b028410724071038000c4240b04a90040a070000c03500304500704000041c107000b20a685035981c0b40134445913004015040d00e8400c2e41024031417280c10342d15596a5101c0d40790354000ca42c00707180c1001980124035000c440403004018031000f1130b90881c055520108500081c2c0c1e00d900c0c4995000010400c00a2003882400c0040350f68040d40c0c1d20b0140107050944031407a0b0028100305e0402400e401042c50401175505440320900e000c110f2088202c01280c103ea081d010389502070f4094840080c070308044890140c12902d00700d40500455540741a15003203800201c0350702da850b801c00400140319140003203421035007251503d0018213180c4690003260498208640480e0900e544103031400501d0f030000c1515521080c1c800f41920241504408081e4400302c101e0024015a1904c001c80c0071992980c050320013030407001d070041000900c0699a010a117811035450b0011a10b08003100d142c500b0010400000c0e01c525403900c280f4040603684210042451420640c104800382d244c007601031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 820296384 1250 820295134 820295167
    0x90206031e15010203090609010c02100306061b030219080d0e1605060306101d09040812010b1806130f1517010f030b0601020708030d020a020f0601050906090a02 71
    0x40d1408840304841c4030455030301c055140c00c080c0100404809203000404140e9000084460354807040d51445e407905280001a42e805c00c41d02e400940c0300c00d90307110541c00958141c0c802030485900d652021110341da0f02020b500d14603010140500140c1002244690701d411810b0407460061242c0700b034600e418190140d1508884603000b5208107074102d4140301c4100c005451440e0041c1008031b560501c0c40c100a000504013490000c0b512040c00860400703011a007000b80d41c41d06117041d0242681d5020314048c9441c1c80150300c00140e100e800c2a2000c0003007074000c440f0b03043d04d44402d940b007952524091004e040240d56004501c0541902c661610b004c01c42550002403900103103501071840c0d40c80d03038089a01038085524101020703146c80c0480010800740603580130034001c403a0444080ca0640c2c1311080100d0603c7d410343c010a8084c44001448140c09405074002d1030403402c4d9909480500f54031a0103e900c42d0000e103d115404182140420a0307490b000f0082904210b60010052502d81840d8840008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 820297634 1250 820296384 820296391
    0xb031b0a0c03030b040c0801031e0f0f06050f01050303030a0e07120507061d03031c090c080d09050108040b0610120e0109110603100b03100f0b090a0e10140409020603 73
    0x41c491a0004081503094092102e40d0482143c0c148900000114004c01714481403001504080c1041843c909440d12106486c240c25000301c4040798100890a00a403485000a822255289800c000580341841e07042d4150580d00e0003000b80d03182d9200c1c0ca4094000d0040402501440e024031800004c500060344c01d60b802c070901c0740019052003498164090443c000c0d0300402591070025880d124100e80d00030044484103808503841108002040620100501851900916a01038101c0c0403074030407800103a2844080d001c4d520740d220b940d1902c004450580c420b43d00101728050240221b4030b945049103103001006c495191a40c0500420041e2400b0354060b001c41ca203050350744c0c084080900ca2540b0030a880030006a030140d195082c8508c624600419034880d0041c075003c04000300f00d81403501e40b40d4200404903000c0c0302082c2d030b40f640600503c0ea0300c03669802d441030201180c002000305124640034410382c01032503c030300c2c0c2e00c2c40e012400c0d206481c4260320725401a0340b498031600580d102c002a502 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 820298884 1250 820297634 820297637
    0x4061d060f0106170903092416060b060903070918050d12050a020705100504030918020903010506030f150403170a050a06140f040e0c03070e09160308040b031b0a 71
    0x203095141c800050100b6a0040403078a0040c8404c04021180c0c000100301c6807210810b54103001002e034020943d8003012202151009001c400080000b4107800700001c03130000750b01036801040320761107540802003544205c4a02641640040c42e00300103554081c0d0100703e45c00100a5880700c803d030340d0340c3e03800d00380000c1185130400309a00c241509040c0143d8825150f0000340c0c40c40031031410f019511042d65a00800686a80302ca80390400503080510a040f19001040070160156001465413800e1003c0d402002d101802586844c001451510300050341c4444d500c0c3c402c0107001e6100001c503201480000041050f410300899480d0141110000b04a5074441e8000f80000101c07828410100001c1d10890361040c03000402c0350031900c486a541c03a000b01c0014200312030010702e0004d07030004113060200c170b0005254140100c0b0800a1141c0d00d48e50154801c03034100301a280510150388642e00d90b003615010145c229201070005211802e001401035810600d60195218854000305040c5290b9101034400b00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 820300134 1250 820298884 820298911
    0x2041407080f04030507120e03010e0102180a05090f070e032e050108030a03090c08030a05031f06050f090103090c0f15080114010c0201090b210708060904061d06 71
    0x90559844010990840b07110340310300c50355003041e8800801900903800060920b0100544004c2003900503c3c407850701c545c01038000d0003a2001809258003c2d00482c50600788201074147e4484a4600101194107507100105280e54a03250400800c0c0a103d004100d1014421b41668848460340d007000300c580b40710040f9540301e000c40f02e501c880025825040c2c0d6070710101820400140041c00700881950440d04091a0004407110181485406d075015944040d4084c000020700c40e0b140d9034417100441c410701c0d6142460304610320100b40100d10795040d209120001d881886440d0011040c6001060f10b4030b4149000f05a001d4291200c0a4170741c40d80d4002c402e081d040010800440701000982400d206d56428030036510362428141c26a030004844000d4100030b0880c0c0c140c402c688c000c0d10700d00050000d06400c86e407101912a8030140c0d003c12180607040d400c17001d0000139482c0b48100c40d514840ca9010300384005a496968440c4041c00d15800214031040c43c8100b14905880c042001e280302c1c06d030380d02014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 820301384 1250 820300134 820300141
    0xd0b060616050601030c080d080a111b030910020a1109060109080d02010b030c01020f1203060a0e0906040c230108060310181103060c0703120f020d1a01030501120803060409020414 79
    0x1401070b1b069101c120583c0180510003066500007948a80c0701c000b201c808245c140499000c08050f12603e440d8000e071081403c40022502400000791445010542e1000352448120500b680d590b4546100200302c402c103642c0d080034600300110801e810180c10304040000540340d42e0594200038405030060010303175481c41709001e280b37000c10a4454000c42800580f0f00d511000c24203d8907194540c50b860381c0454000080340c00c68454090f100014045079405501600304051907503110707a000d40d02611461010380011550000415103d88040110300c0e0004e510b00d1110019281240000e10580e410700666607510941e070610f0086245c019000582c1d21106491840c0401d000c230707940d001007802135200e4810040072003101ca0444240c0b07601400c00001401005090b900508565000314030050b0001c19002103041054205900403400d000d2a04001c41111300114201d40c42480740007402260803030902c020a010a00a513000200a0004031f181001d9401290a0712007034140c1c10072950084080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 820302634 1250 820301384 820301393
    0x30203060a0237020601140609041d010c08010f090204320307140a0f05090718031e0204050714030112020402070203010603080304020a06020309060d05090c030601082107020d0b06061605060103 85
    0x5007409482990b428810b0340650307c0114a10303020340e0400c140519a03c2e80480e080a902140c40c200c401c1d1f0b104000e00c40c8041b00d8400a20800081c490282c0c0003001120114000c0018020ba0307003034500d0701c00042c2e0450310084c41c0b1302c40d004c1d501181040075a43c8016170003440e1403d10514001c1c00c1c00c013140c48414040c3d0343c24890780408507800092103001d0301c2c0003400140d8440d0342d07d58001c086441c04401c0210140c0e801c440c031918940c0003d207441260880700816580c0025442001c47c02150200700c40c0e551000c060b100800380070030349a0354500070001445030b1388070207684400b60390010313000504002c40b03540880e0845540d0707041500c0c91300000c010401145400404600a8a15880994100544240440d84500603148031000c0640c4680008581c0c02c000c000584200c50010121940c0b0f50b075440b08aa00c0300030011400e800c03174900c0302d000404a01d0b59000c84841c03a5010300310444081503900d81040c40500917201d00c2c1d01c001c00700100e605140f03080814010407800380020302000d5155240 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 820303884 1250 820302634 820302643
    0x120c0306080c0a150c0201140c0705010807110607080a110f1801020706080c1803010f1d07050f0d030e030714031b01081308090d05060105041104030203060a023702 72
    0xa40f0485026500307000d001051220702d0241c10850401c1c645460851005031904c5944d900000d5019602281024a04a00040200445000380c881c100030382c0f10514119042d000058040c90072342c2c09500440c5032144100601d0740d1119103900000355540c8241311410955001e401c11440700c40011038003003400100c0040742e43c18201c00340000d02040b440c120b0302070500d900081000b082008041003142d003404e004000c801051400500821058595660395001881400316041c04c64a202000725003244001604c0c0701a80c500030107512500140e54204030800d49040340803401c1003a0304500010a80f030800002d4046d10b0894107601c80f4190703c406240c540100d040302c111101494104010a5903002611103410111170301a12139031150303e0400508a2049416091704600300b02030680170f000010489a043e650200e4081c0914400c6500d1104640114000a54150040c102040003500035500034032003880310700340c41e480200e030108400307241035203e281c0d44407001c003800f0100506990512 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 820305134 1250 820303884 820303903
    0x92203080f10030b0109022109100e120d11071205030a05071b141609060302040e061b0c1204060801080d020106180b03011d0102131a071101120c030608 67
    0x40808524955180c0c004541340c10310582200030340c000307101c0340803114881e101c42c1501030b1003515801c90701f481f09455569803151b11507400d840e45002008069131300c0204100000c0c00b510410203040a22140b883d00c0144000c84200c52180030800590b40003030410707070b1600713822101500d07003580307900d080351000050795001040d400030400c0c00b81c10754035109064008d0780703003058002c000045c12403c0005a00d10304540c2100e210300a0340c90300360000e861001500494241e81c400e40301440b204030380c0109a17a07600e10954020707003849901401d0505071841207025044c06021903040b10300d90300c10141d040c4240e40c81908940b0010303c803400113105030310040006402c0640c15100822070075190800004020501201c51890542c4032841030790603075000d402c01c2034105908101c8400000c00526283e000f50b00c003a60080c0034103030b00400042c3c100c3c00700d10818000c00040040910f041c0b456580e000c0c400c1d1100044c18184030f071880d07110600f13000030b2040c10381e008100e40f000a52103050600c550314201555 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 820306384 1250 820305134 820305151
    0xa0207021903050718020d052511190c03150207031706090714040803030901150f0b0409020310031e0c050324060d0f06060303030605040203090c092203080f 69
    0x201c1d0810002c3d030001000070449034450700a42e020004461104c0c0030340311f402c400200c0d2138105400c0c0598006088914244075030f080ca440740605132101015a2002d840c00c620140365000300490060710300409004030460781c442c491032000705840c0c1c0e851302046203000004000761580030403070004044e0019503424045030031180d040000d01d04200001c0d4003410003400b6404111103000c0c030480d545101d50554000e000e074803050b01d40381d1402280807402000e418071a020418155100000c14130b014101d068250b411640c0c00130302c2d141c24003031000c0103075002410480f04200318034000804510710300000040a0703520403010800b24858201103504075400d4025511907000002c283c80948814042616220034044504106644a00c0061034803031049901030300c81c8210f040c100d8200310440d4007000035244241c4040220a0b12170b0144000c074081241c80303104560022050075190702d003503000148c0c4910080348113401c2603075501c100b55000b101d041c002c0b404900404240001851165a901c0c0d001244 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 820307634 1250 820306384 820306429
    0x192001091e080315040f14041704050319020a03020d03050910050406021e0a0b010e0f0c0928090f0218030604050309010c03021c20010902060316050903060a020702 72
    0x5078603482800e10000d4004c0040702c10349145414030380c440350800301096000e000100301d41d500904002c1c000510480307044414019445224492a00035401d54003501d201074001e00280048050502200c840704005a034001e69003140040181d03107402c0710707000c2c4612039591985c03a40300560911500030301c101072020a026040c082440010350016102154100c2d641001c40f20002150700103082801421700508040071070800880d00f40c80c047e81240c040c0e190446601e200d07685500041034240a1910170550040c40640d08180011190a940501c4061088281d442542e81c41c42c2800b15403480c103942005035000300d01c50300d03001420034185100440542c0a00024a42661002d0f204e1140c8401541441041c2ca0701c3d005240c403c006011800c40454580c1445601801018000c0d4480301c51300e0400070805c01000200040c10700074901104e9002d0321083c207603160041d089201303203d814842030404c9410302c807451890703608001490040c14003141c0140e403540280148002c0200c1170102c004440314 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 820308884 1250 820307634 820307693
    0x305011a030d0315050604061115070206010b0a170a23041104020f0d090609212c15031f0e04320105060a150519200109 53
    0x103020540450b00505031070b0000e09989410f50700010b500c000e800446d000403011401051f00c43d00094186203400103d000c441e4174419489100c0f00d660001c039640c030010713004000100034100c1034101505d0352043c01e06103609590540d2000d51000b00d01190722942881e00c46940100c0500e0071403921443c00414082c01241d07241c65250803102e00d5019100c14011035000031070000c1d440740002911041c0d80c00b0003040c0714003c0a070038000054001008180c0e03400c00342202d0b0f03403c184100010303250118000c0d19042c084d084403104405101c202e001f40540318894030020340040e9a51b040c01403a0314100e0810395500c9043c00131400c910031310f10844144414521940c1404100010561103070b205500020400b88180031000042c00f0580302085112414008100c8005034001034018a200c2c1c002030b00e000220507924043c07101444907521195000c242d013040001e4400d144d05402820706240e5060010700008070301c40c0320020307a03c0644600c2159545e00d01c3c0901304103000440c20b501d501d5a40451000f5075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 820310134 1250 820308884 820308889
    0x2010b010206190204050d2103050621010b150403110d020d0b0c12091b0102031812030f0304080a09050301060b040e070c140c01110105150d08040308030106090305011a 74
    0x8030180200c40c201d205004104880f07800c07501150094100130300100c2168495140c580540346400d440722590510001030009128424410144a441d005000c04c08032418518440048100c200188041e5504c0c8c2c0c07410314440e2940000c41d1164130358442101d60300c9195041c80c2001c036801e85400352191400780e0750400503960310002c0405903034006074001c03c0754440e80c80550b414420300e02e00caa200781c0c00004100a992020a80c20030309000c25404240d50000380f4012038803441810403a03035840100400c031400e141070005144a1065514040301d01d0600c0d1069502820b4000315401c032010400096000395260740040e460000f02010341c000e0103641c1c109901c2e07000f07030b0086001c0d600d120381c0e0500000c1c1d6400e20a02c4c0c202c880030341105282e0301410684c140c00340c8230700c0c071307020404e0200e511a203044075113000505ca02e92050151100e900103a0f0303d0310081054001143c1d60684ac940c20074400800440c4d0928019402448103440d444066450b601d04203080d44d880700c80e6003101c5600c40581c1e40b100e8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 820311384 1250 820310134 820310143
    0x17010e0a050604330e0c09062d0618190302060708091306060807021209090103020f01140d09142a0a0f260f070e0406020d090506040201030c02010b0102 67
    0x16801200001880200401580c490071380c01c5403030304403058110030100301c80070750352025148100714426107820125074014007080c980c0c19550a83c0080c50b03020003240c00d071061010000b074a02e000c200303010600c1c103480000b202900f122050711080000099400c0007490702c0e41c081145e84d00103130200214140781d900060400c1c0900300f40601130080029901200e036070b548991b00b1000600d110100800b58503180002c005440484224001d0f02c6000205020404c140013950300d010740c010030302c42c0039a08660074800d095540d01f548905211620560021081d940e81c080d1425104548000034018000d0501d801c1d99540c2c10030107400398012820f601c51661001510070546000c41800030f04035071070752020818071841903024500342041a000881c00c0e042c4001d004504000549200403042c40c2c0200403501c46924000c0200c0e10b03070004000b0041e040c1e55078851035216000364001401d2090b507007013800949200382c0e02200c003900028201300466030144500040701c1e610340b0007004035281550010750359 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 820312634 1250 820311384 820311391
    0x71d06010c0204090f0c0e0c07081804140a050a0c050309062707060504140f0a030f02240d0c02030a14030429150118030f061517010e0a0506 62
    0x401402014400a5403244c0d08005801d0307034400d074480d4000f0400d0801c07544d145054001e11b48181c0d596804219010040800d5840068001050301e05d004014034400d442c070104400c8054200342c41c1d101c03080f0b141501032909803103120038480110340c1d850030040c1101160440038207142401814000d2000d14480002d8555000501000000007100303c03501d0b02c400710216800c1c8007554401c042000c10116400405401100c01d15030720803d4000c9004100000900007040094011110749020000728128540600d000d50028000c0b04021000110404c1616691046225030040c0000c1e2a032030801c441c0304001c5803480c5031019605240040768010301502c42c8c0070115407007000200c0860700b40b00300900030081032a01c1d045a0110800030880303131041c80c40d0440f81174a0710b0b52100c464440d254010b5880320811000000c0d9805200c0c1140c1e0f81c0320441c00c44200c00d50b00c155403603070320741c1d0180e121140c900d002d00300c060b204803250000d914840d402c3d200240c0450f04182c214110314000550006120f540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 820313884 1250 820312634 820312637
    0x1309021e07050f06090c01110601050d03080c16080a26060f13020a091a070302031911150a1d060105010c0812130b0106030e060a020a05040b0d050108071d0601 70
    0x3a1030707081e81042440c000030600740c492103010301010701c030300c560001401483c001c0702a02c80100e0186107044082d1104024400c068005105100784c00000b44501c1180e5805404081076508010a0080c444407e40310003800f1a4003560020b10754a109400a03620141d00e41c00114448100510200c42e007402007001d45201c0c0140c0c1c580c24601c0b50340d511107103003440380b1481a0086469606c800c43c014121403940c480d60341c0c031051914803190201c42450445000a4143e002149850806101c035100321030440d81c0d040c10032241448010100c0000e01ca50281000c0805954405003440080c04080b54101c0c0100c3c1280408180e1020501c06c010414074115402401c0c0500a04a0f82c104101544a802141185024200d00300400046e2210a1300b070b009014104038051030386c035290180c045174100100810b40d940100b0010314011070a07001411100c0b91303441d18508281d6100700511031600301500c2d40005607100c1d0014030200d44d00304018001450804014155000003070900425100041c24290 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 820315134 1250 820313884 820313887
    0x807030b06070302371b0b0a1d010c0503070b090601150c02040207080c06010b210f1902130b0306030d0201020909070507051906020309061b2212081309021e 69
    0x10202c03680d401d0031002910603905c40c1a103000d140c038001103441c180c00700e185c00f41d80e0000c0020900980071415585a10b60589401c0111200d0803108100c031100892824100548645808009002070014040140c80b0b0021040303e4206203520701e003040c4c81600000903141942c0d01200708280d011210b14502c0350103a80050b80d410090502031024231501003604958403609000182c24840c45006050501c1900d000c0c01d0102c1484240d074421000589022241c510410042020044841d00c0c50125540c0c6100061400005003403080000100b540141c1c03d28a000c420040c0d036040a101084071503d1707c0c8000c51810741a10006480c403980a40180d00b00040828402c00b000420081154000c41e000c0c0c0800301e030b0740c4a1828501030760007116101464011000843c10030800c0398000c403a90466040307514100b900c2c0c0300c200c03040c9042207500340e803111400c200001604400c0401c8200800d010f42419552084803030340700402c8844503801580282d104002c0c030b0700b145d9615240021100c0b038040e40305 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 820316384 1250 820315134 820315183
    0x703030e061f1707030c08060703050f0f0103060c110601290c0d0f0201140c0405040b0a0e19240501170f1816180f021e091f0807030b06070302 63
    0x80b4138210054000030280d48100030080380c201c200061580c810360142e941489240d4400304a07910520060792542400040000140009503080e080181c00e05018580b518001a00200d01880e00f00b00b0303442030071040914056100b45140740c10000b442c49104102c07941c50600c0204a00d669101e214841c2c2d0201701d035600e40780c1c0307400b8800e401008004c40566061540c0d401c005000c3c1041e580a44100744c4258075182d0000c010f803d000181004440b42c00500d42c107641d4902c51319029504084000004095607508410004031400e2205600341560b191100015814070780050402884e00c00d91110425a401c200aa200c0e24007804a41c030500483c0c1031103458400d07500c4a46000010410354000408280001c1680704800c1c0c00f14510061006e0240700d03411400024008030b04c61840300845d10031040140c4102c2d840004020190944060b00b07120708031070b1900303800c605021181d4442e000500f005080c0300000703506010f540039000b03088404031700d000c2d9584d0340a55a6010004504003001084806 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 820317634 1250 820316384 820316429
    0xe1207030b18010c02010c1116061209020604080c040c020a24060b030f0610090819080c0d0210051501020a0b0411060705014106150703030e061f 64
    0x2152800e2001c00002d201104050138040d0180c42030f00c0703c510005400b0204d9022290000801c030b0f98201071415110042400c0c00030403110580300b4880010100d465a03100380060701c1e61002030008110a4020b44210300d03440c0b08200035545252060011580004201c40115482e00000d102890014130909606d00c0c650711454041c2010798041078001c0004410464010031070804035110340c90841d05200a0710742104262600d14035406400640c0e848402d400c8000904150b560540c5400303800300c1e905008204d03140b00c2c0f4140b1406103040041e0029505c09003c102b080c01226001400c0c604000701003000200003c3d0794429022014043c0d0b54041c01140601140e08018483c40c2009000d00d0390341d01e95420b0030750280c100c81c180c0070010040c0100ca00c687c0030704104c0350703554401113003440600070048499180d402c4a001c0c0c4000d81c441c40101c6483c1d00018080020300650740b1031b48000c01c6042e51607103a0790a00b140103000400303411081096030b40744c04050313000c00243c5803603008070721074120043c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 820318884 1250 820317634 820317661
    0x80703080c160e070e012f062505180904030518030d050a080601091a040305060f010503031903180f1b0605033105031e0f2b1b0e1207030b 61
    0x30019441010084a01011070b81050059001c401020480f81aa100c0d49d051500895408140107a80000e15081050242c07040004022480e224481e0f40001000c65002625030300d4160f0701240880e6000030180c0800588250001c0001030445c051310400c0907113800503100c1d2040d40341840400c50940c00041143e030082916402801c6140f140341c682c0b50240044030300540c03150000713a030b19214020026507881725124855045e81c0014002e1410460040300d41211080052100e205043c0c513840303558000c4ca1184a00c00b10030340980c01210480d1040d00740f9007850f90100e2840300400f503405e82d062081d5500b20084039001171405c1c0c44690710f49084400d104680755107400e41005559407002d40018004000b0107000c20b4440420b82c1d142002d55400541410f05c180d210411620406000c0403600c00c021643c880381e40c0003102d01e281608092458040e0440b90800d510b0118181d0391071503c24601e034040c0450455a90035100c01e0142030a500c0015a21502c0384002403403440c10340e0006051008810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 820320134 1250 820318884 820318907
    0xf3207080a200a0e240c12030a09030f020303070206010506090f091806060a151812050d0e0f0906060901030e100b09060d2406080703080c160e070e01 66
    0xc024150100d40200c0c420307942d0300c44a83e00b0001004008074a03000d21703080256403101660b032000070824482e040e130b80c0798180e04440b00da00d01c14000c0c141083c901e415800d00540c41901c1164002451264916002d024011005c030081e00315441071041101c2c29800140c030505480c0220b42041d15140704500040b589290303803a000b60030048a0041c402091000154884031480c07910564541c0c0d40c0f039505000c2c1c50f450910070f0b10800070300c1581c003e1103a40030b1200c01d010010801c0e05410403540b04d1403a04040384030100119110341c04415007070a141da1110018003201001c032102c00070206003100003000c1c000c0c060504c83c402e500c0051250401e80c065030090b0100807049066641c950310b11004440100003105019019041450000c1c00d14a800701c940111a5070220221a01c2ca82015280281034885a5054656691214007103071503242000f080c0015403046002d43e0f41d44c0000380341642008042010036024904030030082c00862003a60b0610b51120481c034080900d07880e001c0040310f400340580c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 820321384 1250 820320134 820320161
    0x121a0103050d0f0c050627100f0609150b0d0209100e0307061806051602031203040507092a0c0212030a0306050406030507060f050f0409050108190809041805010f3207080a 75
    0xe811940191100349c02c5103280c0b0444030000c1003210f43d00c007484402c0e5404294800e040c443c0c0c01d00f083c081000d04401910100e000e00600500300301004011a01143c201c08225001c40d203240c110300c000d443c0801c1803001605881c90414580d050070400c5100307110190140c500bd00c100400e81408458541c055881051380003400c94100035200c00e1000751710351090b44d0668a40c0a00000803031060040c0c050764940c06c24000d80443c41c592034540707038070442c918561030314200a403178140380c0c015035a034000c030ba924400f8100c05569030300c0d0a081e028044400f594060f900550502c8401c002107100401c540c01160040d042c03015205040300d03421256441080f958000c40c20b004240803403246d4165001c181a1200368080f02d45049816000ca0154005800003c1c660802000f84605a081c0b81c4c000d10900700032210b0a071000541a500c0d203094170846000d007030202d0369849941c00000e400c6091102c04a00081d0840ca81c10f0541101442c0c3ca03000130030ba0f42c07c0c0104000801c2010015a00030101c0c0c03a0342 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 820322634 1250 820321384 820321393
    0x10f02030f0f04030c0909050c0609130606031b020111030708100e100306180c090b0319051b091303030209010c20091f121a0103050d0f0c050627 64
    0x1002c4100240c0003400191040c540507000403950b10350501c5074200e4079130050b004008400c804001c01c68990702141c5282e40201440d11040702000e05405040090007480d20f0220392408419849215003022450410440e81170690315041f0f805070908480e00403c4924000030103548007191204c0300031075a4810862450300100300520680320300c1d10041a28070450081c8179413a140142c42c913055102d004082d0031241001010420310000394006031310810058243c4440b205200c10f0170b07a0241d0035500c1900c180c1c100c05100a00c44c05a0341e01100c1c2560101d443e0295030500341e4105050081c0d180009040c15030004820000b030780540c0b544803042d60701c00203c0c4070728a81c0c12144065040048541401030048501192003000710031115600001105482007071507180c00400802021154000e0b0f54007c1026080d6100300541803101d4043c50141d00204424001d2260003000411440440c1c010041d2120a84000610100d4120b4210002040380a0904880c0c00c2501000044000c000501c0c442d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 820323741 1107 820322634 820322647
    0xb0619020601091104261f09020405070809150a0603080c0d0306050f0f1504320301020a09440105060d050712030e090109050906060d030e010f02030f 66
    0x500001102d142c00e03201f1441d041c0c0c0184207000405a6a2038148140c15420705014403a08440c061500036203d00d020340d00140c4804000381180c804480120100fa851f105c1a00181c002c0c68102e8070107035496070307030814a0b40e440545035104d201207410b0040004051600030500381440002400c0002801590301c2000801d0079225041c2c03128580620011841c03009403401045d1080400a10800b88403031084000c421000994041d4800e03801004404c49480c0d1025510007103d1140c03840c0c0c00100701c03002101ca451180c441c0c0f10404403a000e06580d08008510694400024041008005a0300d1701c0c000c1c000c44140b80b00c805441f55011035400c0200002001c81e00d040703c1e0003481c0c40500c0c8004a00000c43c51042a4840c8002540382e100388014500240301e4541c01240c211855a005e034078958000e13200170b07032690855050125059601c10030900900c2198042084030b0300c103070355416 = true := by decide +kernel

theorem cover : BRFrame.Cov 820143884 820323741 := by
  have h0 := BRFrame.cov_init 820143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 820143884 ≤ n) (h2 : n < 820323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
