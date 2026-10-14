-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3572
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:03:17.933277+00:00
-- url     : https://prove2.me/submissions/42be44a9-6649-4f6a-9a67-6ad08e291eb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 642266187 ≤ n < 642446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 642267437 1250 642266187 642266227
    0x61903120306150c050c010302030a060302150c0f0604210504030b0f010e0105060f1801091806031703040f020120150402120f1506181306050609010602030d02 70
    0x4180300c0400c810845030380d49580141e0503a255200c41c002202c4803094181d42c0300940002c000e01ea40e11814115807254460f8000e542c000e01500c2c004035900d601d82e4002400304c02c040c0c3e002031342c0c0003000c44c240c540004d0410070340184c464600f0146c0002d04007510f40319820144451103940002c003010010342828410f0b0102c60055401a44065084c100b900050790215400e00c40d400984030702c04008525847c0610844202180c8407951902d81002c1c1c070280d03c160401403042c42c0c1441024000040c14610780d804940d468103940000242841c11460030707150054141d401d00700000020b0003000b00190401c0758450710640c090902030407905600007026000100031181045901980b8045140200c0e0100514061803086546043d425950600c3c00d5440c030400c1d10301c4035203074054002113000d9102040040e41110003e00841e100e15481c00d01400d9144054841079104401e0441d020248002d80c8102c0303070002d41c00ca0318140c5552405000a650740901c07903049404c1940040c0040d4100c4a400401c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 642268687 1250 642267437 642267443
    0xf0702010e1201090308160903060b210a060612080322060c020f0c150a1107080102040303170f0403051c0b031b090901050f070c0f20150301030b061903 67
    0x28041d440c2d03001201c0c00303003402100c12808207201d0804228070550503c904207403110b02c0d54410501910b9602d5000140240c645403035085501403c0040e11900c0c0798883c01c3c440b6120800a000c0c0c0007142c5080400c4406e140c1c0004040c161002c40e0304c00140c8508100c0b034000d031030400005083e0044940500c181402540020000c902c0d08018140c8250003144010655200c4000c0e5207025411100340f12210304050449070000400308410445d1a02401d421104404038804a403225030702c1e4201907089910070b070815008a42c0d894510103100b80f20b85c4510f035002c3d40008048a0a06103a075014003a0b000b6503848a185111604101e000410703158404102d681006080b1a03141c0043c1c100c151414059580344e40c06403880b00e0010340004814055a4003e131042c1c95410313143d81c3d90a008071100343c0501012240a404250f03200d02055590f00200860742c02c04115481c50300c00e200c1004426410848401c1888006000402c04140080801d85d4404000d440f0090800a8400b400440880c250802 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 642269937 1250 642268687 642268699
    0x1e0e0a0f0e0d170903190203042d0815011a09041506020c0306093a2007050102150405031207020102030f0a0515040c02070b0403060b0301050a09080f0702010e 70
    0x6560704400003141c0050300d89070749030b030700d01042e85000000031100204c80404990b80100080803040500d103c0040424440b403054a0074641c80350015038050b400d00f0104242c00d0072011a0140440c00f102030800146507010040c0214109103a96401e001814030800c6500001c070001d800c01109020111450003500400800c5404c005a84c0c3d606110301e180901801842000410590303410001802ea0051501100800040c83c19505100746508260308204583d1100717030280720701825501026007004400e840d8154400840740c000e14407050760034800c1c21142d00c010401c0025036000300b100703640190f40700300f81c1307040b035540742801c0340303580704a400200140c1d4082c42084031080e41135001d54000c0c1412080e400081d140c00d40c01b0010b8940607990b0702c842c624080108402031030254040010b90341744d401a00c2059550729591407071900141c0c0242c8013603441d04004102c5160a1151561110300795404000c02030842d11800d08a00030759552003d034083c0007810500356801503444620707101004200e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 642271187 1250 642269937 642269951
    0x6030c0406060c12110307080901200a03110d0f080912070b0109050f0712180615060323010b0a0e030607031413021c110910030c1e0e0a0f 61
    0x40104100c24421007039504d1039588071003000032849038200244107103802d13000394180620b50312001c0950b805504180c0c14007000c980c03030301079201c00344c0444182098194082c0041e0455814060403100f40e04a00f001705070480c140d1948269000406400015030f5031034800165952104420324040c0ea5003442440210013183c05420003044440c01816210f6248081c44941c42d04000d041d8111416124000802c100c0207450400c81e002d03500146a000120300c00d5098070090341c46080c1141c408015841c2c030800ca00d07505000e220b826006046200b02980283d440304040014030064941060041070145480010705007201841043c0d01921142d009055075614108a1000f80047c4900840081130884190003d04240004601503080503000341500c85050300c400f0480d46003101243c02200d50000700d036140c00c0d654544800c0548034081358120034950f80c0c21403c0c4032240c605c09a11040369032003814148d046c0e1001c0100d0781421140841320040c81a1900303c909030140040d81840030825141c034903 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 642272437 1250 642271187 642271199
    0x618050a0905071112120705071211150f012106020c0703110607050607031503170c0f061612020c030c10050105100e0603130b07030209012d0806030c0406 68
    0x200c40c40c0509226103500381c00484d41070000352548803442900b44040010f100603030758111074240c40ca601c840320b1714103580791152607643d2030303003041c1403481d8500080c400f6040b10694400c01c01c8424502c02d10542c92440c1031401e082d00011002c0140a1941c0381d81d110400c114410080c4144001880c0d031103c4c082d91100146100320365034080c188000d80350a0903082114403c2d06019084600164120001d00415503034070400740c010300000741d48943c0e041510600080407500884507800e01c06c80c20010260380b011003d81c102e00c3d103c1001184640c0d07421584c1404880e451900c09200c2c0f001c014204140d00484522640c002030040c9801c0b03040c140000140f94410303400104150640d84212001000107036203e0381800b00c401d01d801c0c2e41c20041510701402440a02e444806103921200b001082c580074105960b550b041c4071402d9890001107900458024520368000d203840e0012061411040321420001c0e000420003034001088034140292040440d40b291018041401d1a12004d030040c0801c0e81d840c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 642273687 1250 642272437 642272441
    0x20d1703070c021009031a040c0f0303021605030105010509160504051f0215071d060904110d050912090f18090312060f010906050a0309020a1203020f010b0a0618050a09 74
    0x2e00c224801d0604005000c005030243d0390000c1074a82120001030700658143e46030407510000741c015070f01115103103c0000c062624000500c00f0b135220783c3c007404429207140d4800c00322041542006220380d04000c014400c81e2942c480c3c1580c49151881140e44810b10f15000792101d100d5900140e0700550b01504d031a1140002c04440f07400411154210f0f08912003104844c080040300381c41980000e9080002001c210201e5102c4400b1504000c1c5041d01c1c0a0782c0e031000030112030b01080307100b01c24000482c02100b080b80500c1000d40c01050030002e0202040041d01500003403083c103807007601c104003000303444000c0d8503001d00d400c22000552454400306d0401d00240c80d40c03a04550303030103020a080400003a041d8241300140043d800b5068580d00c0c6440e0070840166055000040b09d18201544c4c1c05410f000b5035103411030b4600920741e40c0701901d45011170b0f00740241801c0080e000405282e04042c8110029118054800c007103444914084400c03442c9440f00c000a205240d002652181442c08045050301142e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 642274937 1250 642273687 642273707
    0x4032d0e03060a060807061101110c011e061a031302090124090f06050f0f030408070606060c150203150d0804151b0303020d110c0106150306030f020d170307 69
    0x88045444550f41c00320100183c131a98003404000740c218450410000e80a51148042240403a0003c289401e89174400c0e4480d820440c90303405969190308400da07041c1d109002d02443c00c254080180b090505091001c0b0020300c0c3d00d43c003000314940004c0056a01c022400042d40c6c020b80c000c1081d040c5507964040c2900788a40c0704440d522091031109203881041c06092060110340136103030040342c01c9180000548440d00b000c2500c4400c1401040322800d9508080c0c01584184c1c82074404540302c40d182d08082d402c844550f00301800384100c080300c0c0c801050700c0f4081da01512001030780c09030b07995454070790051401611054164004030b1544542e401c010380384002c0c0003560003150040d01c000c2428002101d000e450403912114050403141c41c01c0c0031034820340051072100c454003004100c0307043d00c603040101c9602c078240c0d40c000c50355165406d01101d949010381c00f10000c00d5140501246003192140844002032040c0203114003800c150103001c0000c6603101641c44c0300101c1c0d0007030b03e030314005102070300f40c52034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 642276187 1250 642274937 642274939
    0x1b0c09060303040e0610110a0308070909060608060d0516090b030c010203040320031c05030a0e241b122d0103021c050709140a06050904032d0e 63
    0x61400010541d003000419a0111244580102d50b2500c90409020414410a2462080148503c91100612020041810312900c02d0707841c45420301d490500200b0030400358020342842d50410104200266001140f507402550840740102d000c0c02c64601145040c100c1d0300d80059101f5004400152a0607a500410400c182a826240074501d08001240c8034400c80c0001010200088010500d5400440c03140702805809012076110340c10b0f280c60300d4218840d500750800010400020010100018002e811504894000903e440740b10003420520070701c15603004011402840b0001000b03a080420380308505000d44100c1940c41c003640024281024003110f403c603142910851100c80039100300c03901019040d825820a80607400c55080018404020140000c8031b0b28216090010402c14802030004101c0e442c0c0c0044c180158a8990b50085002448070300040e00d050010032040e15080c000300d50184d81031500500b0b19007914414120f0714840041d8400603000090191007198014803c400d03840d0b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 642277437 1250 642276187 642276199
    0x901230d1b060210090203070e18100b03100501030506012c070504081c050403080a1e030c0e01140421120309060f05041709040e030c010c080c070b0105010509061b0c 73
    0x1681d003030104c01d0b0383d1840710007034065108032400c00c0f421a0110070290061a292141015100080300d03180c502403080141c0000036545107100c10341441c00b00f16035164980c1168090089602d5a12290344910341403003900d280c50704440c90516080c1603070034160f4415204040f101090300b0403460081560f045801418020722860481d000d0030101041d905100e40c1880d03441c87c1c030301400e65480d454036800400310801407050b265130f50134004088600d110310204886e60f000607403110301c030002001c2c0542080d096040c40710b072401e01441003140600f15020b9806484d003a0004032500c603600b460035442108040e0060045011000300715901da040002da007030081754207004121011141404803103099500074540d2982ea0030030070310742c100e0a0240280c50f4004000242c03ca0f40c1100c0d01c1e003594481d482c410107603590307004202d00711900039001c2600034000480c010308011480d901c0b40814031041c0645414803601140c4102c0703e59a1404440d02d00301400d04000141d003003044400d40d11424006083c0c4030304 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 642278687 1250 642277437 642277453
    0x601030b01151b03030228031e0c0518030a051c020705010e010c2a0902040932100b070b0f06011d0118030b090601140901230d1b0602 59
    0x1500c1040503504600c018555010000000da44c154025448240004440020f602d1011420a13a800e507080c20500151004100c0100341860002184201c004082686182c40040d21000303604c80e00f9940049040c1102d0003001e54094000b07403030541c0c0d20900070300d548102d41d800d0311259000700044520504d66005ca91210391508015954241c0010000c2d00141d00d40301400042245101e02c94003840d1008040540f40d0300c14140141e012007560000688142c0006080184084500c01c0704100508012100d151400302d00080d03140d944031580518956100602050b07440c1c001d1030f08c020080100800c1c1c1d030355520052608000007072044900300f0300c1000c000c000449a50284010100b554031681c001e1448002c00c10045d52802c40029140305146070106010001500560b0b107140a111210000c0415624001c2e10000020504e0082d034050500100108000c0243da85100e80300d89251036000d03207560b9803402045180743d10400c050551621503070125004503034132420030299101036080d80c2201c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 642279937 1250 642278687 642278729
    0x409111017070c0b0705030a0e0313030c14060405130e010903080f0f01060f0f0c050a060b100c0506070507020d02090718120506071103041509052d01110f0601030b01 73
    0x20b0300d00f41c4000303000745414000080602d8446c10003542c1c8000b106000046074411508040d00d107070403117072500c1144041103409105010309001f40c54004c200c2251207003402150342011030400d00031340c0f04140c09202089920b2181e5900d0707030007445000400e203008000c004201e0400500403070040c2e404104140810f4041425542400714403030580316262143e00c1d819415a00c100e44080d07445011801300401d0690b000000b82046c8030b01c8041034010300340803500480140400c034241500350a10300130300c0310b03241c000300020301c020400d29405000c50501c41c0d100c0c0f01c18004174044117003002e0020f500c8103c0c40c04008001b5040000750f10b11411206110f6022912071884c103901c00c118410191040d8400313400600c0084c8100e03090340381c40d04000b0071340742007994607030380141443c6402d0000b80120b0764102c802e02c900d007030620f074200450b80d504282818510002d85d0700c0c0f8410156982c1241000740744e008122080b4400c00210744c03441c403c01c003107900310f613074a081450300c9a000b0b003c1c0d00c00d0301031803111142c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 642281187 1250 642279937 642279947
    0x50f1201090c030e0622081b28120306050909010f0b01110703060510081b01030f0212130204060f081507170705070201020a0b01140406080d0509040911101707 70
    0x4103142013000300807a482d82c0300c21000000e82440641031003008002c540c00080c1c041c0d4080d103040120b00851280e0003207009400c50a080204603445400303502460b40c00c1c150103103036100e090354a4204d444000440000c140c2140a0a010f40000f60000e44d800c09011009105600c00f040361120303a03804201c2440440c00440d8080310038614802e8907400a88240085011036006a8000d01105499803405594494890900982c440548407152008a14071a5941c244c0641e0440d158940345c114036040d01602c040f071030b0200284c04420346414010380001103480780c1c3d005c9800780664101d954000c580d540f00e0103640303080ca0344000c0460f2050f880801e04d014040c401c3c1c1460002800e180d20410740e02d0f008211102e800a44044c2d045224103c40b00300450b20b0030162a000c0d0110101003031091a01c0402d000640b0000d03400809180d01c44441090615402030540749058411076000c0b98440e26070414180304038846103003942c860201250444203603007010500440c0a18008004140e41d40d0750340640b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 642282437 1250 642281187 642281201
    0x20301060c032703021e040c0c0c0b040b070b09012d0f0614100201110712022103010b0d0906020c0a03111203010509040807050d0905010216180c050f1201090c03 71
    0x29005204034018401454010040d08003640106e10b2010200b41d000c000030141e45118038103c0100320180c0c90f5105003d14252000050b2000030314080c84c261903c10340c03a29610420300c000d481e02c0e00e030001240b004c0000707420280c00d4100b10814402c0c00b00700c1c0d19801d0080203661401c100c0051800a00701d0385280b59000d09001c990640c0c04203841c0340c000b0350910890341c175038400c04001c656a41921024071030940001e84491801031200304404031100a0280c9051020411902e20180034407508c1030038003011080300c0c1519000103041da120006008240050880c04100511084c000b0070740d582140302c00200740e400e0034007030f0750342c60340c2e0044001d203003510340e8181c403281094100708100500290400d8010359401078451000790307280240c191912810b1101c50310303118001903c1204108641d40c0c1c1089800ea596041d040310344800361400c00d90004020086070000e044507260040200c2c032601a00950311070042c100c1800d9a95003160790850141c0200b40114445076260a207428500d42c4a0f2013019 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 642283687 1250 642282437 642282497
    0x120607030606020d1103180310020f0403030e0d02090621100c14070b0f0402120d030b0f1008040b0402030a14060105101115061c0f020f150703050319020301060c03 72
    0x40c40c02c1f890200001c1c4100000051641510907a92000c0800f0003a03c0148120031400549030385960440c98028003002d805112144114804066980541d6a01c140590010000c894502401c0a10400c15081403162461001e19002c1c2c003082c07603c2c004854010700040c03005651480300404503d2600451070203032810141c02e0b045510000b0300050070004031300381c0050006001e20542a80c0c0700c00d1501d009030319000f400000351200ca08084904180e50f80c8150400110341c22600350711070000046c14000010405450282103030085000c1d9241406a8143c05400c15a9803071a2a41c51003501d69684080c81424041c02800ca402d04c0000d201d081040106d103030001c0607222241d9040000c00c0c0e0104080c05c41da500c00c0040e0400d460401030b4070324888826200320700c011100b40c1a4010804c1644010309101d000d00c2044825140047c19502140d0712154541400c0f912a1507d030101c41c020b10418480d01c460700d20000c0003046090708241e9001409101c0c0d039486000c0c0c1308001e49090f0120310b40d1906 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 642284937 1250 642283687 642283693
    0x50f030601030807080a0e041b140f0702010507020f04050f041e08040e04020a05060d200c070612090f350d0c020307050d090e01060503070206070509120607030606020d11 75
    0x1790040e03004100c0c0e000149002c0b414072503528009801c65082d403c24140c01c42c0719002180d4859000328500710902c141408190415080c07200c1d121407031107804402810400c00040c4030f021551400111160180060401c1016142041141040102c26101503a01908403034110801d0510b11092480403a4800388260510b80780c1040400c5c03403107010740102d0f03103c51250808242526007901a00f075280b40c6282c00308000a0000d40b10b405528648140240358104111700840480300243d444100c91507860306400310f44903007644000418100c2d5005048a070a030b03900100b4050061161f10101401e0100d0000f0311040150281c500d005040c1e80d04c1d0400300c180420020b00c4110b0f031080d8407421250050700e2400714180c0c2c2d510309000c50b0209180c0410f00550080c080256482145d5000d00032904081749141080d00c406941d6000042030031042280001e02d0b01003540b221500001001c0c0700508a80300e0341400803010300645011b004d0345c0d005104049482d50360070710503c0098000ea0a14001d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 642286187 1250 642284937 642284947
    0xe07090b37120309090c020a15020414041811011101090308160804020d02010806010203040b0c0f0d0212040b0904110d0b01020d030614041505031603020f0f061b0c03030a09050f0306010308 83
    0x80000781c42d10114040030350023a9402c0e800490080d4912800352480c501005a86a003403544103000000c800308801c2c0a540f820070201078040b82006485043c03a00044c528045040c8500106c0302d1801c0901043e0003075080c04100b00405410100450085e41d280b100e15103410b00c1c26004480041e8125800b03940b201144000307801650151107025000345043c4196071a02da02d0307084c89041540648698401075220040714010500b0a0102a140442900c003403d950700e20f05a120031180101d00800803801400100001079a40c2c030727480340240c000216040d58942072003001070360051851282c110f025008403d498007199100344101c0b001e8800040030441034655040c1400002d101c0c1e52200c1e801c42c050204040390551b42000404503c00f1030b4010070030b0140c114810300c0202440c0c0c10351240524030005c00b0400700d643d00402d40364500d2041e0041d0002c4140400c40c24a04241441d50680600002070710b454460b034041ca03c2019200103840c2c96500c1e420034418140d80d0202484007401014042c40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 642287437 1250 642286187 642286199
    0xb03030706091e0c030506010503062802040e0106050702040b090601120915060807060201061d1f0b0f09040510030305121005190e06040e07090b37120309 68
    0x40320640403030050702030300100c40c0d0b83d02941450450f0303128152800d01512000f0010420100320f40740c09820f0075030280010341040083c030302100302c0304140300c1440a04030301d000d035801041d517040e05c00506094104403003d50303450101070002d0348030000c182d00440c185140d94499003810081ca501610060759250f20894520704e2280013450013010441d490f0541030f603401d0b0140c1503405404003170186c200150244c01c0c030f0444007908441540c0c0c00141020b04001004d0090310f844c0e02403680c84610544038000300a40790305000c101c000103402100c5010004a211845014020003400356103009940800c0583c850710012004035602e4440140041c1c02089444408040741c101d40d50010031a00d0030744800303515100001c0d11003d20b03905400e55000035038400c203c030300e2000740d071319412007010765080101080500885480e1a46400ac5e403000b5a118407450010ba152200565038206000181900c2c2c07100b41c544508151103010a45004516510303800f1507640c2c8a03d45e074450166040c1c42c1c058246140c54 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 642288687 1250 642287437 642287441
    0x1e020d090b07060905010515030607020105012403090b0a06092301170a0b01080a060b040b01120c0203040b072102030f03040b0402040216030c02030f030f0d1a0d150f0b03030706 78
    0x80000c440507a1a00186000179909001d554041d0b44a80d40403641c0d00800c0082c580781400c014078038401c581c1800b00400444c801c49560304a50300030b41c0d1620303a501c0c120364000d074081d007000f480007081c50190702d04029807010144d2004098580c8518244800090000e0200014000c000d9012002e0100e60040001c064448a201042168502602c030524126102c122004000341c0c01845943c00c00106d8804102c60f51150320540074080301c08120681062000a0480300040840c0719107580e100000000700340204280d0740140404400107503601c00614002c0c2e994984c0d2404040e1800d0501031401c145400401517441040040c1842403c60f9078507100c9031184407001d0400d90304903608000d0904030310b1042410b606424069140c0e400d14040b14418503207400b44142c461485a0400d0058030b400b407007581c0c00c60301c0c0c03940c01ca000419000c1c249030308a50320608005011703902010b050401410421003002c01031008210903c20081405254580420345108481c02c6606802c20440000050210b03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 642289937 1250 642288687 642288697
    0x512040608190b09090d030b0a0605070b07050c1212010e06012c0a0b0c0d0302040503101508031b0f030a0c08030403090924080a08040317191e020d090b 67
    0x502d20120306a501e030008100361103000d0300c102c0450740045c20f0b207020b0a505802642103503003080c0c0342d401000e80380c000c000700380d4081d20710010b005d0070701c00d00420911072080050302d200d9000803054030010244800c440c480c40d40581070700d020a18030030000041110391504103610408041e1104000880000c45180b0500c0c0b000000c0c08545000b190340000544038550745401a210000015903240d040c00c0280345405811082c54080500400c8240040d440221340080c00c242103000c04109044d81c2d01003802044c140d904068a5480b0102c8c0540500300741c500442d112110040a880090380813910003516441005070720b80202d103003d000340c00020b410000650340306002c0e01d41007000c0c80d00c034941c032019940d0100030301c4c0c0305001c615100380b851070303408041c0030041090b03400808002000d03a40383d1540d80607a01c0060543ca100000c0c079504c1d07070f151408075082c0a207a40741d0380300c40d500050340c00b901c421043c1d0304620041042c103003070400d0f00d80005440030401c2c145480d080902441d18031410362607404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 642291187 1250 642289937 642289981
    0xe0913030c060213090b120a08090d0c09020f0a09080d050405060325021006060203090f0402090105190801090b030606010801090b040e010e03040602010507090b03010e042306040512040608 83
    0x420418004881c1004c0c8010016050b440c0300419102c0e220300810180b01d0300c030740c00c0e108139401444020000901000480300c0b690029502d4030903281050800d00d4010025510201e41e9a00003e414070000f42c00c0340090100040d9911262001c0742c4038200b050751140e100d1041d201150b000c00050000d441d0401c044d690061030498500c203429025204080020240138040c0007590100200c0c40244119025410203402c191009608024401d00084d20030250214124017076580040c5d103a2143e4400d800720380401c3c80c2814005d18000c0c40c140014402442482049002c0740340440b400001d10300401c25500503901656200c08590901c0300c1040107060481d002a0300c5562000500c40343e8201b8015034004134140005140c070340385003020103030a40f04010401803c05c0584a02481141412003d0741d040d105201d414903180d60b140d00d0805042000c90060a4407100a041d0f0303400c44000c001031030741c403c40c0b0400503141c154000c019411082c0c0618002c1c2004110840c00250f00450400042802c600e2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 642292437 1250 642291187 642291191
    0x10030c0902070f05011406100e0108010515091809010b0105070b04060515120604110406050d080705070b1611030f0309012105040c15090b070204020a1812030e0913030c06 75
    0x9903a503e421600004601802110325200b00300c400e14240c82191295120327070030040b440480fa0000240a900140580da104151940300c011680c2d14120a990320140f01604080c29410826180c1030824422182c180b6290308041d44000954442c0d8181c99401d6403110409180c0d84460761000080d000c001c0076800c07040c40100351089965a41c08464004150140160485041c14105400405100c00140740a2802c10804120765203032603d1024086400c00070071a1106d18a29000d0b082200507071007009800408200c049400390030840e29040140301e0766010700d41040385014103480d07001001c4500c08507041407000200c03d5008000f0400018100b521144142150b1340b0800700719070013503c05843e00001104280071341c030900300d1080304400e8241048000e845c1b8007403401003113114240000340101d03004180c59000c0c40c000c0842c05007980403070342004070603600c41c85910090040110207400064a108540d031040c00c00507038041c000d040d41c01000100c090180c07000d0303502400262080720096 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 642293687 1250 642292437 642292463
    0xf0903030c0516120b090c010c020603220c140103142701050a020901020f0c03100b030a02280905041e0302030c0a11010915020601060e0a030605090d030510030c090207 74
    0x6022000408090807240c1c528044001d16810170003403207035000b06102042d6000688440c026a008041d1101041c0d044030507641e030307659007144c0e0303190b1940c007940190a0f0024134002388104020b203001d600c141c0300c002c035428981d211900d00440540f10170005040ba48090f510200b88000d0700b0300c041403840902d4070452220811076a928608485040f0780c134101c7e059011510080310340e810712011103883c481400518224030324000094503140c08508014042d0f0760303000b030b400564500380b0040405071740040100e0608955103002e15215a00c03403120396523001ea0042c0101e8100501d1150380c6c01241c00c03516401c81d446480244d00e4025551407000d078254401401b250820b410200014562140700341031100407050f0b1640054000070554214024500c020403011090030782c00510276045030031614083c980701d600c140110307511a0007600082c4c0b4003800c1c8410001c1d24880011620010b8585940c2040203560381c01c842c43c08250980402082d80803428001c0011a1a07038000d811000c0c060030103880b400b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 642294937 1250 642293687 642293713
    0x170a0e030f22060503010e13020a030210030519020f1b010204030206180310020702030d2007030302030315060a0828091112010219052a060405010c0f0903030c05 71
    0x10740100d444080b8121520096010b5901411400b030b00806660400c42d0940d41811607800c69004000c0c80505d01484030282042507581d1180440300071500a000140840c5100034001c01800045462040c0340000d50b8000b0300301103a038070848a6040c2000036090078920510007480210f4107400000003a59028440071001d17039951001072007800f4540c042c940303030405d08206050900444011600d00300348103002c21400358401041c034030594034107894072504400d2607408680031400003602040c154442c103540842056000002940a041c0d240014140c0d01150010845c3c98130480ba11000040d603007001148001760680f014440b0a0b14000840350300e15440441c3d542221141a401e40741d1a03030700d588441c0303142040024a022102d94400a5140c40c0384041d4209144c0548126401001030000350182c1810186401280c0a482c01c0b283d95040d90350701c002150b07035030400e4a094940303510f4480302100d5140103850701c82c1108402c2e00d600302001d185481c00d48400030841d805443c1c0d40603c44540c080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 642296187 1250 642294937 642294967
    0xb2206020a0c0801020304080906031e09010e0c030d1709010f1104031a0114010c080d060f051201020c061314060106200f0307060b010c060e0715170a0e03 68
    0x2a002a5000300001d00e00e9003411440701c0e10360303030050a00341d00c10070602020682c444100c80c2107441c2070366907941c1da449454203a840300301001e5412540c641c1500031b120b1740d0351040d00840181c0f6142022030301d10340882e40406031035003c09201000461000d00d2103c021091141200364081c46000000602c00d000c08115401d44a0b002c1010001200002d418420042c8000c1617207145a0342c0d0f00c40304c0c031940c100142d50490179070490465040c841c003851000f081044401c1255140315a1290900a107940d8031203a82c078108550003001e20502e248a03031045503000501c00d440d0140c0e01031000740025199a41c0d54003800840b0f00c000c1ea02c4685050004c504102e04001d850300030011a65403901c1c80380700711a8101c1c031050410403200c19400400300e0420031440041650306c401d4200b00c000400440c5400140c603c16a58100280500e060600b0b1002e402030226440301242c0c41800d8004250030100c0c812034164048815000c3c01c0074607034002c601103c0013544103031401e4132100b044030702d041e416a5041c07032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 642297437 1250 642296187 642296189
    0x20d08040b19181e03020a0306020301080d0206070504140f0603150a0803070c0311011707020d0806040c1d152d0a0906050d06030b010b0c011b090b22 66
    0x1c400072000030600d00081c5440341c07031486051945403807010540964030000030295244a400904504a0341804080d03076003200b2840150350060624005c507a40c1d00d4130802940003481540014000d01c0c0ca013082150011071420f101d8841541e400c5e20301410406010300c4514100e0b1016003203109403903188a1500c4290045028241d0322600c036840c401040100004130503250004985500140300b80c1c2c0025075460854015a80e000003510030400f50040101c2e80301c01c40c500c80030300501d0540d06016019401040390384440300e0b6962103180c20342d80c200c103010a49002461410018108140c8180c1c0d83c080400070170803d000041401091790018400b000e50307070300005c0f0b80124034942d00c01c800c60880c0f200d103078800e519245118036506000c03144002410b1540c0e90b04c81c0e03005001c03000401c4541d5000540c8030f07101450348082071070f2443d43c50740340444040c3c0001c06152000e42c80d041083c0310b07010462400306c069110641d55480c1850810103040c1c01504400444040c25203003040c00e0441280000c0950 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 642298687 1250 642297437 642297449
    0x30f09120f07020f0a05180c0f1b151003081e0c07081507020c100203070506010b040524090f130504141209010914060c0d1805030712020d020d0804 65
    0x5840c0e04443c010800c0044495070540d2044140742d030300b0411625648a00d4903560107a01c00d0b04117a40d00c2d10081c070098881c81c5c009441c03c500014160f80d00007e9101da4054100d085000c40c0c00b06142440c140b200d109050354a800b0000401c801000081d0401e0020000b5011007000b100c02c4041101b0480225005502244d01a4210740014450460300304003904450b5020302d02c2031010308000c040a500d85010007000c0d402200c402d141c03540b1445c000c10071500650380c004c044401969486040b0b85141e04203001c1d052041c400f40c0d01f8110700c03002c07401c110203201c90069045490700c100707081041045050000301580102400042c0d079219121442020b100b24040c1c0042c403c5055000d004500340101c03800040b22503a000c1c010312020340d1740a0003481c03e85002034070400c2110b0040c000207145005242c007540e0140b2030000d10798021544028250054400c188000070095184c0b401c040e200d038494068020f200301180c08100c0540303004083c00101600241c003080340c420113515008110350142d0026 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 642299937 1250 642298687 642298717
    0x171501030c0510140301030201180b071109010512060a0b0415030c151106071803051c020d0e1c06020c06010909110d2a181b05030408030f0912 63
    0x8000c0c070308100089040d1030b072152a1038132000344001c03043e0049000600000e410090400010b4414610701280d01c0007070102144001c0d201c0340245841c10101100500c0d0740d0040c4a984000502d505081c01440c007032401d880080c100320b0b500d043c1c040300244000840070341c2c020744a0b0009074801038980c142174041d50058001d007183c2030514112452580e1818031800400500403080501c5c0c0201107040b5400c50014070700341003242c000c13640110640d00c0580002e455801103001c440510b01c0c54a1614015458035002d03201c0c000380d05142980ca4003503c10f40b540d00031402c003012032615600316400e044843d100b810014100041840707250300c1d1400c06d0f001801803659400d441400d00c0b040c050890300100c001c407075140c40703424580e440c110490038003800b9400400b080c80d585210300e003206141ca40502020800114180211040c240181230b0b0300f00086110a07061905801c544d108204591146410402c21031554076076407a07840e1000d0000305007540307601480680f8a00c80c044000140711404c2c0350300391 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 642301187 1250 642299937 642299939
    0xa0302090405011e0b0a050706021603090509090706050912190b060f361906090b030307080a090807092405220e1207051204030c171501030c 62
    0x901c0304603501a0010152511440ca40756100c08580360710780b0590317000c042d40c1c80e2600124401643c0d07500524000400103400400e081382030b1103090b0245140c2d140203644008140d6071394418030241c20410340300080d46810000b41030021030b004000a10204001a100c0da6181c4641e41030719042c01540e02c010a00008410340c1c017408e00540d01e5015402c10412203143d83d002080c0e0ac0011076000118081103200c4d40c04290750780c000200e150264009804480f080030141c50002400490048850081c01c4003904d807603004105507489110b00701580c180a0010362070700610f51100300c06500148105001c001c0300c15004508103c0601c403c4000780016000421034a0210100c060401d003404549021400d03420800c0105603503440881500441e1401d400c400c0c01e009a00f8140905090f4440800c24071030400c40c020480d0180d001482594041da05840110141c500c0301d034107512a510018244080c940020300850306200700803501d104040c0229480800842030828041609900c150f82074032500c44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 642302437 1250 642301187 642301189
    0x111010f1407020d020303010e040305070f080c190b0f10030501020412020a090b03060f061813020102010501060c110112020d091101080105030c15090402040503030c0102030618040f0b09120a030209 87
    0x42020b82000141c00500307800030000500030f613039010521079441c50724401e8010409140c042c0c001c5a0000d40c0203c861280c61005013042801e44c2c0c0640404145842102152440080303003000341440e00c1c0d48800303540120b8070f41d8803d409201c40050180b400c100c804050010014038244002d000031720720307040b980c040079129004008800d0200d42c04490b8550a11300c04050f60b50300810721a500c80d182002c143e0040c0c031120040340c0c07508501500f0b031244191500c14080040022000004040e1003680203120303980c0c0310802200d01440c0124000c040c2560052014415030280c03601d1030501848810040c01d04c210000c0a40a40f540e4460680c2d400307206a20f582c2081d41d0010805002d171200303070000d2101c404c0c2d050120b88132a40d110165078070035402203090540d40d80c803501124024034004003103c0d1205040d4040d80c8c000e40c03065591500c1071228100340200080c0c4441541c1c811500f00c00b501601d100c00f0b441d19074451000a0111015000d132908004285241e5070240110b22a603960068440500748 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 642303687 1250 642302437 642302471
    0x1806070908100c20030c03070305030a05131a07032009090705030c071b03080427090b130c050a0612140c0708070c03020a03060225050c0f0111010f 65
    0x42c001d08201d50030080c40340d1015410505821080289a00b9540420030341e0852500754010040d01c820303036000005034101490703400b0b0042c60203014503200c1088a0b03200d104809065000a04004000010072070314000c19034848258039074800c00340c3c2400300e03002c007034120f04041c01d4a500c0300a0380382c0d040104841350142884520550712200c035040c00c503e5810100c142503401d0161000c01010001e50350913501c104072500c1c80510041d40e1142089898075290201f03032401d981d80700c2501503402e803101540150f401450191100080e00700e2000503181d00c1e10b403100c0e441d01d49140c10a0720745a1130140c0c0000d8903100d41c1440c800800c010354400601c01800104682661500c00040e04040041014400c0b8008040100c3c0c048613400380b07509503100414600721600d01c60f9036001a520040c10440001400000d4000740300d5202c07825048026600007900c456100503c0e606c0244c086d601012503031240b81081e11140b420088141030400e400d5502c1b140e8a070030b407400c5034410303007a071078940d18034a840201d44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 642304937 1250 642303687 642303703
    0xa0b032a0a030f030e0a0e131b090207031704020f040b1f0206060a060305040b07031e06080d0323010512070e040f0b060a0b0304030f050d0c0f080604060305070e1806070908 76
    0x454203030b07144500d4100134078500306008d40329032102c56240b03034502304002d20300010015410087e00e816a61301c0d42c84640c00e0094011070411740124078601c0300900b80128289441e441039034000c0c80c600412190030b06000007810f45221b11500303d8140081d107010503203019900717400408164001c1ca46842c000042c80f406101c680d11039803c3c5810001404006070300c1c280320591207556403400085402d4054400302d441c4559004814441e80380001c0480c0b803d40101d043d02d0028140e441c28000c100504280c03e01c400203907e4030300c80c036260403801400949000710900d24620b0b10502210807094071010300c10741c00c941c00c1c2c40071140210441c03600b004101c92001c030a580900c00311140c10f11603103460043c2d042c602c001000101000014140d4040c1240248199111050300314804c0107000b58120b00500420000103070a80070640040002d98a884c0c07034000e15040c0c991000180641c03038a00002d184000c5005081300381740030104000c10141c880d04000680c0300780565610108d03e1882c00800908280395 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 642306187 1250 642304937 642304939
    0x9050a0c1406160201031410030501060611030304140f030f0310050604030f06090c0e01080a05060906070507140a02120d080f040309060e011e030209090a0b032a0a030f030e 76
    0x1881c090a078950303428095440c03c0b01c2c002480f00b440c0c402d501c0100c000b042c1c00070f1400307044003005050291a44c250198501981d200e140204042c0791030300000c1e50f18203880316120015074000c00005000454544090340b03e03618443c1211050808a003c482c03c0d80c0040343ca61105c443c4c013000304141c40d00181c00c440d0003405c055134002c1c5440d06503102d0954119101102030301c001d44030340e0b200c0c04100010a008008200e003804401507540c403011000d80786c01100400351020f10484003ca43d10103404203500d4025092500c0f4035140402e903035595442880d02e2643c100407401000004400350f110326020007041030304000039040c4d401801c5006018480043c11203c5522507076010040040d03048481c01c0f0907a00c1d58107100b0b05c05543e0000480305102000c942220051100c0342403420356806402409000a0441d0502c0c1c0d50364424043d24211084003111503030581c00040c004410300084030401c0007504d201c810181e10545040302244406240f54412904a04080d90000c285a4844d4081c062000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 642307437 1250 642306187 642306209
    0x11a040603030504060503100302060403060509100501050907030c02030d1b090e0606091c061b170c1e2b0b010305090d0f03020d150302030c03030703050f0a05090409050a0c 76
    0x801c54070300500a0185000c1c030810311900201083c0c080e0548a185002582e006205a9989441e45024030141c5004c0e1030886640c8641030240f030a200700c1d401014113a64003e440300c1c10583c3c40d400d003100035140c1c00c1c03090f1003580010403804503080d0305401603040019410640c8090b07a8803c0f00002c2c10805542e10801e0f88064034020b01005607195012a0040c40c4102d0780c3c1207880150104901c0c0048508000030700540c40c100c41900c03541d0083d01c0910303500c1029181e900c503c110310201c5d401504012103100a85210402c400007920540c0c2c808107002c100050400317130a22a200751110a1500708009000b0455025a540c103d000ca25000d10301c0c9424082c41e0034131007030a00350440b0b0381c0e0b80000c03040842808105200c01e000e00d8840c2e419100e04c03160300340d41400340f560b000c40d1032006510300b40016802402881c0d50703901c060400004540401d54966a454a0480645404003161304004556420000100808201075549000d1821114003880190a40118600e0184c0e28035102da445010050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 642308687 1250 642307437 642307439
    0x40516020a150608121201080316034b020a031b03020f03040905090613080a03050601020c13020d0605010f0917031314030f0c0d060b0a12080a2d0e010c14011a0406 72
    0x2200545210142541801c1c042c281c04a515480160a5030500048201c850700300202445070600c2c0c046036003301000d0000e00700c9030b41100c000704c1e101c05914030040d0205e00c05244c0031240100703000601c14024041c2c4141c030200c0102c2c4040300e05580c01984500c4e034098480090083c00c000c14003411ba0400c40500c80403c0c2c0d00303a25656600c09008401c0d0350b03c02c0c199102c0c001001030740244140c40780c1400050807082c10842c2c5881e000025003003810794801d854039000004c03c06501130040006019260340301c4100340380c41c15102c51651951824050341b180018403912a10103061041030380580310076003012010080349004d040c80c013920054150490350244079440540d444240528101c3c540203503021400c11040c1021506c9210307940d0222141038a44108041800340c000c000d40f02d409010f07a5801c4010704401000e602c02c3c1c5540c4400d1010410841004410b540030300e4541d0003492040c18554552002c40c0c950300e00d40c0708501b0303154019175151b40811124030b440f545207803041801160100945 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 642309937 1250 642308687 642308707
    0x307051501060c0209071224050a03080f0c070e0705040914101502030408030d02040f0609050907030203070216030c0f0b030f1314030414040516020a1506081212010803 74
    0x481080c882c068050003114010600481c4243c42000e10b0701031000e0180481403003101c60b40c100040e230001d050084100c1550100d81c2d0b14090802e2000c40350048a440e04084c480e81c200451584548143c505900c2100800503080e200800414880c007400d0b00e92684852810358400292201d080c450211004480c00b0014104503e401d05400e46d01340d4080c1c041104d1400c4070903469446540c004e001035200115121f08105002c1d0006c0c81500e10000c0d030743c80703555600d100076203c04005014041d40144900c000070340c558801e60195a00c40c1c014411a000406d00ca150a4458030013608180c40084124109102043c00800007000900c03600c00e043c0d00c2d504d00008001c002d21406081c20104440c20350118043c840289118003464001c0802c0e640c2d1983d8030349404d10040d0b08111014012400c1a0008241c0c804c1e02200829402482d00500418000d554658140d5014130012030801a5518404500920304003c0d503a030b9039160f0313042c0c03542da004100210405000141d00c82181c2d584200810502 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 642311187 1250 642309937 642309947
    0x30501050f1c0308060312031003121d0603060406032901170705150f0d062306072409051f05091203040c0b031609050f03033009030705150106 63
    0x180c0b94040c58a046182c03a2400024200010301613607921034100481480a000107004295080b02d1040c45100d2051f800240c5c00d8481da6000c2c10a400080501a6071003007504000004640c09500103100281d031907280e07070f82d50180190408810000c00d0041c280c110301e8149101c0303150301410000b42c940000703124076080190b5540407405001e001b1070700c440341c00c00e00711080b1003039800203a0391080060f100c8c1021440f00c0300400c000c1c80b0f000310924648020b412080076403003006c8a0400044d003800c2c902200c1e42c03150b003010341e0101510f000d000e09944032001c2000440c818440110311030000341c400c00040c401c9c000d45603940c6100e44818130f481e1034203002e204813000941c1018030100e2103a442c7c50b503845090140480155600440d50a00700100b0000750380300007103140c5071030038050300c51032081901c48091260f00115451303a81c2c3c05620411030350749803442c1c3e42c0d242d0107071444540215100c074040c010300c00d0801d202900c1c00c1d071003a4400300d2103008100043c40864000c050155102e0b4041d8540795000700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 642312437 1250 642311187 642311239
    0x902090a09090501090203120315190e07120c1106101410050903010603030c02190b1813020c010b0a1509090507020309030105151305010b07062307030501050f 70
    0x403003a5070b01c8118008001c1e003034100494164000301580c2d4500c4100b8000c100f654070407036080c080303008000c2180506213081c2c88140740e04072010070100d40607420030002e1006c0f594007801d04024044490381c00050f0002c1801881c00000b00c0c0d541c1e03aa150040c005201e8580440030301f00b800d480800c01020700c01c143c00704142c1d0607581401c81c1d1045a4115400040e11036104014061b038055007008000f02c1415000300c50301c010304c0d100faa14000d404000301d0454400040501801c042503104101e040c0030b0301e02d054041502ca1000500c41da102d4001a05400700703e0b40403c580e00d020740d440d61103255452070005c20702c5000f800318090000701c0803605107005000c61614051285417a56810200d1030882c403c10542e107180b40058002c00c00d0b401d202c0d802c2c020900458065074441c107000101b40c40343e1032190203114101c03081c40404c14240225a070710f92001e820b068140c3d83c0340b844001820008c80c841d08030200c6c040c00c43c540740007925505200500428a402c4111303c1d0003a804007045512407001d8001c064 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 642313687 1250 642312437 642312449
    0x303061508061315030c1d090d080a111b0c04050702070e040201030f1b120e0d2f03030708040201030b0a030b1b04121a0702160909060b090117070902090a 68
    0x221004054154440088a45c00c00b5203071001d070220200340f41c6000f1000c030b07084c005581010005580c8181e601647c8940b0750802200180b0000081944030129400c200c0303611003005040340c244004001c900351240b17905140c80b600740e4400da001410a040074401c01e80c000c107143c0301400050f0305068a12001043c007030700003410160380b504140361110241d44520031a010703140c07440044900200006002401c00784075050213070701d001c3c6d0f0700c54030b0100060b2501c8030f110545c40c0c0400f4808285010f154a11188648a414607812307424003030801c600b40b000f5403040c030301900e8200e994182400014201c40501c0e410328001c0b814047c040c0003151400d10b095520900d01344c0b41a041c0c0205c011000c7c600d016542c0b0000740201c40300d625008205034000c400041c10404100354509035181801240d40b5500038903018003e07203843d101402144210380001d03400302d000c0c26020401700d141d0004180126400d0f40b100502a23100c07070034078040306d4081c000f0800404190f101035041460724000900d8814640c8a80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 642314937 1250 642313687 642313691
    0x1207030210080a0618050702060a0213060818060708010e06010815041802060d06090f06060c080d2a2613020102010e0303010303030b030d020d050d09030e0d03030615080613 76
    0x2c1c9030a4295088200a483d800c5440c00c441c0c4100703c0340f5170243c0380036195003000d40a240001995050325100b6204007840b20034043c129545400025541d00744003030f200604000407444102441c0c0320400003c0d002e0310b825a25504d00b5890300744800194500030f4503090401100001b0320908103034944200d52145000c0314001a0b41d144101c003103052469020700290030103008150b0114881044e40708000303c1e80d5411044c04640c00d030360022802ca41c4240148404101306180788000b1071040006040b024160040002e40c2d900c0688980945420310503000011880c441d40208410f82d0ac0a203010100800c1542d40c5030030a0100f4030000314100007020303210100d4035202d0f10700c1503a200350442c6021807541019039581b547c490030010060890741c008240248682c5044503030031480002d04400c651426138803d0700740b028001c052000b8048036541601000196480f0401c03c0e55480c0c6400c407280d04c82c0d200090920b18240d15052000100c15500c0140080b20f0b04211094681c00d02c041c074503540640b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 642316187 1250 642314937 642314941
    0x906140a0305090a0c090f1a060301030b1801060b0a0f020a02011709120309030405030c0102060906010303081b2a070308070206071e1b0905190c0504150905120703021008 75
    0x70a13440c0400d001c502500d40e10840301d0000e42507101340e0002d10202451181801541070807540003450010b040700f15074214200f08010000b14121203015a000400d80c01c0003036482161020072420341d80d180d0460340c03a80030300041c580c5406820455585248500340080e0060091a03000600405403450703000c3e20046030100060706a110910078a51a01c009600701078603401d003946842c3c1ea980050240a000348151321400305103600000d00e00b80304034000d0300104003581c00d55a0845003044068a440e500406807044025842083c3c00940322010265002c140b400855918140a201808500c3c0b04113401904c41400861600390460700d0040e0140c540b2680d480552801e914184420b0740c94070181d821380d421050807c50010708d004030000a070360310045915281e03c21b1404a074815158103600c200002e02124054115030003450070300202d41891401d05603184480058160401e510f00000303920480140114500035110319501035540c4010f12110742507901290074031079007001740307020b200580c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 642317437 1250 642316187 642316201
    0x1200607031a1819020c0609160e0106030905010902060a0c02151903020c070e0c0310090203010509190b0604120606150c02130605030a03030c27120507050a1202010906140a0305 78
    0x401c00814a84c2c01c0002c6541d51200804c041c1c49100680d811106070103000100c84001d4191080b10341038421270000c83d505039190081c01c0d00148410340d0215029504d518241c0096501c060143c16a0344141c0c564200c590400d20400025070480c891860062406000307224001c0d00c00b40c02c1c00c22a1a1134180142d42d1030b0903202081ca0000e941e801000d10042400c10414090303020001346002d002d40f501c41e2441113440d0305c10081a40401d00606403c1540360340014810b030299110402d61140c08880082c084a5800203d120369100b9004414800c10103400c203410019144200700003031000307604001800c424400c0050003040d0710280a84501c00310a0100003001e0168411744c0180002821140458520b107000f6010b0301000c241c03034000c00c800080302c800741c3c10f6084032250004902c00000107800c2c03c0c10103c042d00e103030703800c41a213544c8522030000c1025101c042245e40a010708841c0100a42090310004200620380e070405401c00c82840c0c200900140600140e2f5038010f441c2c01c000c2402c1d03036840c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 642318687 1250 642317437 642317461
    0x50c1c020409060207230a08090607060e06270d050f0c060a05040b0105030d09061404050607110a05060a05090603040f0b0f09010518060f0601200607031a18 69
    0x901035400351070007048208000c3c1c3e640c014244144142c5052000e40000000030f0300001d07800c5640c6200343c022a00100016028000802d00c940006009508011640d180c240c00c840c1d014040c0300499108034180300c8405040c0418000768441150701520744c120018580780c980c0c04d020483c90030304c44041180c03c90981c004c415507071141130540480d2820300c0c4c11250400540800e07202501d0b003843c2c1c2000810b1508011070340412075811504c070300ba442840c0c21002c0311850901e011107003141800f80004203103035503410014151280120b00381042400594204244445140d01980c800c2c0303020881e03643e11a40000640e01d01480403584070781c43c1c0c1e03140e041c410041d07860b2100090401c0707031080420100c00b21411016010b51800c100820003950703890390000300740d031500318894000d0707004800168003041d6007110144d01c084103140c4040c6c02c211000001c03184442c070103d040c1090300701d03004010280f541072048115034a00c20003201010031600001c242d001404e90899840d0400040010303002c1c0c4048 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 642319937 1250 642318687 642318739
    0x80405150c060a02070b330f0d0302070e01090e1e01140f150f03030714190302061506031b09010e061b0c0d02100c030e1009050108060d050c 62
    0x240142e540034500901e1607402548940022070f50402c3c8480030800040e905d80b094642000d0010112420f84550301000c4446026038602c0c944c0503c003061010704a0b142c014501501d144a42c004042660425220003154607058100940c61450700c548003e5001c0700164103400c4092043e00010035080320350440e03024245450704e85220b01400c0cc203000c01e01c420500001d03c50340a80d55030000d55030300036041040003800c0c0e080391541640148000c4000c00c210509094601c500e240443e103003c46110188081d2410900e02039000d40c00c54810020b081d0500c2c4602c1a402c2800c0f51601e00c2c52070192400540c07070244561401c00d0282c04200008180d0046810350080007000f41f210340c9420380c00b0318960615400d01980b101a002d101503405441c1000341c205400c5507070003840d80003000f40021040f20041c006070400e60410100e51200e01d4247c442c40d038030103441c4006607612040d03641004005441c115016152030700400e481c600d43c2011030743c049144815000100d0790140012100d6071106000f410ba = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 642321187 1250 642319937 642319957
    0xf2512061403010b0901061d0607050f010b01021006050102072319060f0c0f08030408070f06050109060e070807030e010b04410106030903030e06090d09080a08040515 73
    0x1415101080a0000c1034191004210840090140c4210304c418445190420320402e008100351070b020420320042081d002d031001e900a44407600380980c80e02c915142030f65984040d407130b0b030f5905d0880c40da26582c10701c00001006008401400010300c0c00300000c0d81d03141d0307074450390020120103240301e050f44107820206441e07007500910b850010030144aa090101c0c40ca84200b201103080702c0300e510101e600841e0103400c450340008186408003039903242c00280b54001441164069000c21801c1c0010b080d0400c0e6141003405550001003a6041c11152000c070b41254200c25121400740d4100700ca002d9001440b154081030718a40810649a0075040d036000d801c0d885003841c1e00c17900b0400310315680c0350b4080140780c15110701c9188503501c0b071408001041c4e06140000c0c038040e40c07851100500c040350094105483d594070a142c00210100703040302c500c0c100b100130343d041d003840e4012080216541d030b4012003540190000c140907000c2d4034000d9407515600d1040d0312a281c001c1b029910512070b081c0c0024107403000d24503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 642322437 1250 642321187 642321191
    0x408010c090503161214150c0409110702103207060606034b09120f0c02090613050f010e0709050d150e0f0709050f2512 53
    0x84824040e00100980c0182c5029200b54203604182c5540e0400c000c086440d0040c0580c2c680701c03107450b45420404040d004111600c255130155540b00c40c1e4a0910b445046010300443c0c6540c1042c03201410f8030a4121030b0140503030140110701c0581d8036a51a285840214180151301003001e090400d03140f0144c1e140d8005c0a07505900c25464205c501c001886100d210740700030898591264005d030102d66200300c45003081c05040d80c1d08000305030041094540000111081f4081000301044052008184c140b804203944d241ca441e9810410860300d52446c0098030304149041c0012200003d1070251001c201034442c40307800000ca6459202c1d18183c0c04411388810003840300c1d103403200c04d80074245403e1044507115540d200019a88078460040c0d5030030790344010701d07900d03a051903511000301080c01d044205034030941d20007041c0d01c01e80003046034007020064100500307819464110300c001118801403040760f06048140c05c001504005e0b4150349580266128062844500000d00310f0f0345449811115001c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 642323687 1250 642322437 642322451
    0x90b0307080d0f030b030604120c0314030705040303080a0522030309020d0b0402011106090a080d0b03100507021b030d0c23010914160b09130204030b0a050606280302040801 76
    0x240c1e00c81903e440701501c075141803000707000040a065490000701c0d00038144c03020f002615188a0301c204801702c1c1040c000d28040c444001001c070800f100f0f52003554203e0201d500014200b080580200c0f14980c41441c42c039040045103407810092415401081345006500b0304408050100341c00780e0b000301701c451340251a80045a800d4a060440380794240e07000d81c0801d502e0851002d000000084e4a40b00f000050043c120940b001c0d6240f0013035810091104221030340b11002c03018151400c011011109085600c041001d0030104e2010381070440c41d25101e503a0001c201d1481c10642c41c002807281c2070000c50302c1d0030400f10038141083c4890020b003a90f40401403a25a100312110901504080d409501603556100101e0142c0e43c07840d601d00c4030710b144200e0180a980300304081a4541e02408004801030110340041c4001d010310030403a400b90f001120495151000e01882c25030034821181c2c4074406480359880c22070032400082d0700c001d003802083d0408000b185050003040c840e405450043c41d000000340466 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 642324937 1250 642323687 642323713
    0x130c09150909240f270e0f0a0b0603010207050703120302042102031912080414030c030c0606010c03021207021804060b01140315060c070305060129030f01090b030708 73
    0x5110420703d48180504960310100d8041005560941100c114041600d4103003034541a0700b904c1c8850300f17800c020f0559250f40c0c0d540e59120501c40e84c2c6200d6184000341082103001c2c0707002c103035890f00a01098000c1e88140203540000c5c030300150480035a034000c243c11401f11200d100440c06403040d500306506001c12031540d484444616000745040350f10031815200c6082e0208102d0100120b01c040203045402c203444a600810f002e00101500503026003500d15641c103040c044107107183e102504c1305a0541c00050300d00e0944000740316a42e0004400d10382220a95000d0b1402507039148068220340c0446400985141155502c4c400e810108050072a00310382440c250519500501401d03039403e02144403000118040f00034482201d104084a0814014500308901404000d80041c6803070f061610940001001040003080301e81d0007485100c50181d510400921000040c4442c1526050301039420320a020071510352600503415200840300018007001130100080c940f041503800510075004091000000d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 642326187 1250 642324937 642324971
    0x20c0f030406020d02061e0c09010c052a100203030106050a111005071b0512071b08250810020d02070f0b01050a050a030209060603060307080d090302130c09150909 72
    0x151140c0d800341c44481c1d94002181200701c40211641c7c3c1210790100001d01e854006402071b1140302010b00d02084a039241d40d5030b052500e00b00e8010759044820080c0e0807040014a1605940c1200040d903101051065450002e542d9002c103003d101c06003e000300c0d02c044181d11680480044034845002c41e0440c06000c140c8a00800c415149180080c204000100d40501c10034421074080703a0280007445441d2003488108000c0e0451030045a034420411000c1000b0f01103050104007510254014294107405509501024070100f2540303440140b024504000e10700000c6101861940c0a80000d0382d500c004410040c000c0c03040f110010002c2e0100c1c41280207000e001c250142c1a114260342c919040d40e261420015101d0789888001e40c40b40300c8000151403818504040c40c2c102a0140841d1080d07500c6510f0039091010807010080001d80590040055103400c0f100600b50304c07204e90342003205410700280100704514900494260000c690040c4c95500d00c80d1036010000d01c6042400c00c09030034a441080301c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 642327437 1250 642326187 642326203
    0x60f03150f0a140402221d061024080705040312021c020f030d0902010c0f03030903021e0d080402061c0b03070e0705120c092707080105030d03020c0f03040602 70
    0x402d07880d0802c40307081071502a00b81130040360000e100c40320035104201049411682110398aa003243c6900c5409240c400004c01501e94a001c0300142c41d8078505000d10300e021002c4c1d5840465107042c55450444401c66507400c00c0700c0c0d4542440c01034144d0f650041e00b96514840c03540003c0002040302c04004801380d02103803140031403141d981b48183c03035558400101e90b00d400814040600b030304200280d00155140b60b100c2c103104c0344103042804180d40d2545440c0356070840d03484140c0129855000850826030b052290182040c0020150707504440784e40360b61a030f240040c2041d10700380b0250101040640d954442603c1034982c0c1c645400b44203400b444503800280c4119400b0070b00902c5882400308600380c081c001c092188101d0780d1814108074543e0604c1c11050381c0508413590350a0204000c40701910340707a842018001011040c5102420036540500c200c0800801140c100022400103009659010036a07524460141c40c0158560369410425804c042080350200300a11000500040c0f550300403507104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 642328687 1250 642327437 642327451
    0x40c080412051e180108061e0d0203070312142502041409011d031206100903121d041a040e0705041a010908030a2a200f0f09060f03150f 60
    0x12400b0540300103489204041e1f600740d40c0180c0701c508451020113640c032544041d0000a082032680340383c43c1c0100f4184a0300e0b80040d9503005220900278186a0807985c0500d46101450392a1b25124501040070700c0920b105d800b88412515864005017503550715003103a440c103004c4c0340480100d07040c000c00e50350003050386030101400300c0084060b94000713030130100a0b242c030580075000190141ea1a00100301030507a22040d40000e021009501101181030340b80d413400b150041c0c1c4c842a0350f80e2020900301136100c00e6100120710890900e540c0a03443d031000704007001e51400c140d9000c03403402046001c56040080c541c00c0b0a410628145640c0d030001c04030580120300810a807a05150b03186c480c1211a00c9220300944000840c590201c200b889a0342c005055a0407020b041d041810301c4450354809001d0300303000e0b1000c15541c5413114812100d1804400104506a040382c003a81400550000b1444c11000100040d10510030a04910703880d0300c042c84290100b58403c8018102458601d2003a03501d0003055a40c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 642329937 1250 642328687 642328717
    0x2031e0304060f0527010c0b04150f0911060f0c01020c0c0405090706080c0a0521150301090b04110316030b0a06090603031e09150c0b06040c080412051e 67
    0x11042d40200121401e005c0f095220303405c000c2c107445804207130414a1403101c0c10800181140e002060810880c00c0c05644a000b426000c011400c2100c4240c843c01a078a00c0080d180c0718280340081d02143c00c0291803e4280c50860f116044a030111100c1e00501640303040c0380d4000120040780c0301c40403a0300805100121010012900c404600710380e1400203021342c001003400e04002c6a05403100f000038002c0342406143c05031406041010440380036102003540038400c810442840b4508402c450b00d4224090150020806500c00e91175600010a0140010f0007445480400d1a002d440030f0100b04246402e002c90030444660b2407824590380042102d0f01d07000c403860f24801142d2211540114130880380c059980e0400000c50796040410441001010018050606000211003c50b50195100b010705a01d03a001d000b502400d06003402c04004200d14800c9140801c007004031500001120f4203d90420114403d504603036006840d0341c420008001d2004441722080d1401c00c000390002c1008880701298 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 642331187 1250 642329937 642329957
    0x10b090c0403050303240a150e011d010809033001050a0b0301050609030f1b030f210a05130f05040c02060708070f02071511060c03090304030f02031e030406 69
    0x64800c1d024502005000e074004102084120480020f0f110154444405d845040e0f0007010003e111003909a01004400100c1300c0304200d21034000000400800f001e007046004000002e0705040910150202e560620550a0116103080d2041064a00c0e0a009011084140c0c0c00d051301c0012218003c00b108601c45980c2d0000706a074100005003400b103c45c00c10300035040d6406c20082000c80e401018050741c0506c5030320301e0086507440c01c110210b2040c460f0310315990f9124005013450300b0046512840c2d0f255611035107032000c0300080d2010104640ca03003605526240c1205038030445071485400c540e9000b8004a00011a5800c8000c841000f112002c4808000040100405913117a5100301c524102059607200003500c40da0003041005411041441560080e6071a5018150000700070f890700790016003071a010b481103010402c8507036084514008450304500d8121180c41c0d60740705500000748660041c00c188011503c0030044186218141411551011101040c42da966040391080000040c89004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 642332437 1250 642331187 642331201
    0x131e080703020d020609010507151e0b030706050703050705010e0102031e0411211209010801051203220e0a0b03010c090501080112050f0303070509010306060e0102060403081b0408010b09 82
    0x15410100e9a000c0c20b032500f4401c041d020801240c01c45d241c42814840300b0403210002079031030900303480c511070107440000d12408070701043ca200070003010150090516200b0319040039540001e002d81216440e103000c40c0c0d04d03691850216468051124020310075801d181e90044102c00640195110300c101c00c840c58250b02140d01031928000e010340e40507284c40d86c11105041c040c00d000320130005451102c062404c0300c1a4100d032a502d030004600c4c0880001c04041800c00256a014502c0d80c0104012200a40c2000d0541100b03500d0340704138070541c0300c1003c4480d20706039007110540340003009244840c081c41d100d1408080fa90017401c504038400d03219500e00003401e00340d14050400202030300c2042c4e684081982c01c0400060400c110000c0c256680e204210301c80980c0c40081004500c0348000d69a81912015940005410b907641c540088051101d44616400c05980c0040c455a1198052130a8001e40d10b0340c00c201d580300303c5043c0088070341d1000010301284005054005102d07440d0140e0304408140c0e1405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 642333687 1250 642332437 642332443
    0x10e060f1e010303053f01170d02060f0a15030b061302031006180302060406110c030142092403030203070f1a0f06040506012111131e08 60
    0x40002800700d00184114041c1c03c4c10440301d12003817080782d490b0703001c000143c402c500c650051070080d1041b41400c1c503005200e9103080145660b11444090000d02d20004071004c003a440e410b00914481908080b0000514000c10903002902c016403454128100103483e400c008090314805c0b54124011021600f800c2c810510b54421648110340080c1e1178100d842c20818203c038142c0620455905c5001610004005a070302c0030000d00080801d912808506045070198604000c0700d8a10b00c0d20030b0f40350444000c031504440c00b02c20310307443c0440000040c030030b110102107a121207407182d0f003c0901c4d495180480c0e40c01140d8800b000d00c039a4900d06032014020081218141c01c601d0000030016001400000000385d0f200030300c076540c0d51144002050540702e00ca404000c0903402c0722000c0f030b56110b42d0705114041c24a4851250020400e191501210500340005c2e1206040704020020195880003214004c2c0e000405a0b07942081514070403256a5440c1c038118691072424040d100250310002c80000c00711800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 642334937 1250 642333687 642333689
    0x1080708070e04021e190203340b0106020f160807052209150b060702151c091406010e0112060506010c021305011a1606090203010e060f1e01 62
    0x5566280c810790340e854003100c80c0c40e21508880e80240c1c003804200d51000e810b04864000c1035200168680703454005400c05044000520107805542041001c60b01700100708041d42d282803084221000084182100000b80055114002c0c1c90500900e0010038629402719481c0a0461848211541c129580c98400701e9401144603050706540804400c0165043c0101c03a04401e007400102030381c280710408010340544d14114400c442e98049080c05801d01c8a091046000140b4291465030a03c4241e43c040390200c800d94101007078060000c99500d84452141c0d100c0c0300808141201440980340e5807070181042d500c5400031030180c0c0514800801e00c1c003d002e24640c12600003000318140c44000341c49950003400701401c0345040280c0c425041000d070320b60300c41c444119040c564000442d58501000c01e250120025042c1c049070008001d50300100500c041d4a2000b203400400c0007909111920001c5d00501904902c042980920002c1003031034910050054400e50100e41c01000e9905082440c0610f1032003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 642336187 1250 642334937 642334951
    0x213091a1e151206090c03070603060605093615091b07050a140d0216142b08030f01050102120d0939300611120402030c0108 55
    0x6088002620628074404200440802900002206018500e604e0818600711250412540070a4107141d06040811040b00200441d103000c0241301d04010005003584903440704103124042c200e40d002d800700744007200c3c20b41442400081c04444e1086841242d0301001c02c0300e00f0802d4180b103004804950515840e06031044d54001e00c10059801581540e000d40d0308080d20940706071082c6a200d10000b1104002c4269007513990005023a5032024040003490400c00c2c10a00c910341000541c10040000c0203910720502d45d00c1145c01980e0fa803040802c225440922090700c1803180ca542ca165000e120492000318000c500f649000325007a82ca9000580e5030700d0b0010b410040c002010840100c0d08011540401035082c0b1891080307801d81c0d1030303070b01e44d020f00d50840d200c00906290060f400e54604203401c0521005041c0c0c442035144e480a21700d0301013100007091362814018540544002c080000342e40c80509010100c862503611580d8402000030650000c8400701c1c020710402c995902258040c1c0c40711449806 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 642337437 1250 642336187 642336241
    0x50601080426041403010e010c020d050a030f0f0902010219021503070e130203010501020c030c06030115090f060503040b010918031425021804050d05070213091a 71
    0x715a41e0b940d100300191402e6844074125042640c4030035600034000c000074628034204004095001040600b158501d111581c07150b85080380c01c0c0d040507000320707002c40019014100940c4035908004140d0103007108802c02ca0005141010079180c070b406503449120418001c0e801c03140d00305030b041d484410312146070384041e6100e003228841c40c0c0c0c8200c441c00210390001d1a4130307001d1209d0408a003c80c100092192040076440d402000500113964100800c520480f4110010301e594042c49010907101d20041c01505030b8000c0c04c0c900482c145e401448800c009107003d1907020401d17a03a032000202650000d60f400c43d05032101d20000078000c00c032409155821199110039a0b40104a40c2d400d0340c40d2554011400c51100082c01041214400d04240318501c6041c0405080c0d005464410050a0316100c500783c40f5521454080c40081040000e04542d85035180c00d0455581d034a5000107641791124451944d2058100f000756010030900c45a40c0c540c5080b813005041c4552201c0001c203884041d01ca41040d0001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 642338687 1250 642337437 642337441
    0x50a06110307091505090415170c13180c090f0b0105040303120902030c0a0807030605010b0a05031620010c09050f03031c2414010305060108070507061b12060905060108 74
    0x9031048403a404c000ca035030a00382d00e0844000c003c82d084d60750440c04907100740c009080c100b003003281602e90505c1140e159000740c286040c1e01d9000504032800c5940109006171b98901d0022400d89410741c5131402c2e908886c500d510700d5510310112014003444414404000d003041c2c8010702030350041003980d040d20351544070800f500319200c001000411625405a1f07152142e145015107030780700c0800e4903001d803200340050728035207045082680a80c0c1e8107030f01901e920b4108020306181154410b007903d8020307098034802c0b64507038142c40044444003140c2ca911001a600983c2000050005511102d6203c55079150300791102d40d641c0400c0400c81c2581e905a4040d00200089080303d050842d61012804240a001581c80d62110302c0c05c407011015040900d08141016051094042c001c1c100c501140c000d01e4240300f1840c219000034501040540fa0b80c0c01c0c0140482e903141040920b4224030745028a565001608015541e0f0007880c0e400b07060902c41d1554508507010030400840c0c06040c1c0314030030603116a2803d0b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 642339937 1250 642338687 642338699
    0x7030e060613090c0b1303021207030c1703041a0a0809060f0a0f0e070b040f0b04150318050d03150902070c0501050306030a060c02010203040b090d080c030c0706050103050a0611030709 81
    0x1810183c03100301e0304842600804504c81116402506a280312541d00403000341c114030500850060942c501c2e55503034802c134010400a0188041c1c241940c00c1110700c69580240c803882d080ca140295008444c0c10040c0310080b04501050f40003034801c0c421103a40700740c40341e160134013001e44a00703080c3ca0001014140000181005e11607803c00081400300050000d8005500b107040d030f05200c01c94004196545000400700811090b102c9004082c2080314115032902c2c1c9061101d07000052041c1c60403050648901d80064050300c03281110039250b403c442581c4262900c5800100201100ca00f0900c03c0d0f881c0c0000802c036000c05109442240ea48026010394035400d18005550a400040000d9454450080204005000c60140c42242c0009400260710380c1090701e01501080e10080442e095507200e074102003070785a44134144da50810640103129542e0303100c044090103103104064015049504010000040102c0050307804c0c4400d015000401a01c6074030400881c0501c401c2c3c40d410005680c590f028455 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 642341187 1250 642339937 642339941
    0x70305090a1410050a0903020d0c060e10021c050d0203040c050405090c030c041d120a0f05072f030d09090f05010608040b060a17010b04060f150c02190e07030e060613 73
    0x64404607061100c41b00b0fa59500140f4000d01c0524221144814a10100802134202c414400e018108454240740f2123031a600c003d554560303809511400801f818a8442c0440c0550211100d15401c407500f590740b4909411700400c10460742c0305080c062071400300001c070f000d24081980044600c0c024054014919160200400392520030131600d8030803400c12514440e54410004100b10046003214240c4641c50064041c2c41700354003c611400f803150030000740c800525104104480e0300b49624010f80f81e010a0216541020070507448203030584100c401d6802066000303640c1004035881c404d02072244042c40c013428001e4400030f120305004101d401001c02c1c005010195504d0344114060f0820070096683d088005903048803219010560f5940c0c68003c20a041c2400781c003003d0300b496210250300307500d03150150310044090f01740101080a08a503500442d0b4404c10348801003031007050074801054440380c000c0d1030b9800030b543c4000807034542004002d49003c0412414070a50300181194020726001070f01e040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 642342437 1250 642341187 642341197
    0xd05070615050916020c061327060b04090b060f030403120b04050411121b0d0302101b08150603070e0418030806010f0809100917070305090a141005 65
    0x1d919568504003041c5615881080d520840b00c0c146007040400300000041d042c5034444526502882d4200050354000a04941da4000c4803604c2e1000a0640c042a400b4402c0c841b0f40c03052000750a041c00750000300303008041c01400680e0501e0300e04010007485c450810140303103d03415038000c1d028004c1c000640480d01664001c0303040c280010002c90b1900c0d10130000f404641d1304940440e030148011441100c079041070b0503006c8070500d00a00034000c5007495002d03070001032806129903200b62a11540c0d4400c051007442141d011040f42d01080c0000090880c003003202d40d41a0544600003511719000602000f00d0079082d540f81003014007400c0c656142c980381100c0c083ca000080d603820039100c0100508003241d0f5416100440d02a582c0d507030650814600040550900740341ca801040b06000c18844250340114203085e18030805003000030300340341e50306d09200c0103002c0320b900a0703180c080401c10400345a0000020100d00c801110344544039901c1e4500740c01404e00e02d0200980020302c2044840384180208010300d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 642343687 1250 642342437 642342461
    0x1203030506060d0509010906110a0c1e02060c1506100509060a0c1505090f0c0f0603091c0503060a1205030901180f06030e0f0a0305070f060b04110c0606030d050706 72
    0x1d2401201c05035a40984e001500d526141c3d07036460401806024061084400187c4420b07966490001030500040c8400045070000d030000101c03015031328045100d0682035808650181030b2640f030b03201004042e07881394089a662401c0204040000341c030f0386840c40c040c4d421080c0b03d80700c942c00c2117181d4040c00204d130851544607050000e030100c0c11700861041c14075946043ca14081c04500b03841e001c2101824038044072a810055441414a640180d8400d80c10500305101510703001d0303c913034420b6003280c0b41c443c941c0d040803603403c1ea0784031404805610000852144000355545040e0656070b0b4994010f00310400703000307400e982050013452015807040402c070f9000020401d0f801c90451725640d0044902c20305e54480d5005c01d42e6020075000d0543c06000b81480d045c800030181c00f03070120584010300103106031180204194401c944840402c0740c0c1f603020f2028540090000c00060200818107121613000c501707036010f40d12803c0002152443c000400c0080314060381e403194105603d540c0c42c03002502e80d0a40305 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 642344937 1250 642343687 642343699
    0x9030910141e090307050901081e5b0519051f0801110a0807030212010e010305011d210c06040317090304150e03160b040815011203030506 61
    0x9003a030468500031180b1050507682d150396100400381c2018034000056110b28029000721004110040d00030491000415080c55003950044140400c182403c05101540c05030b00031b00e8014400007414146078018008009005403e0940040030f51401c00209030007a01d05040d26000700d80d40152507410440c3c220324140c031004120f08500d20b1040998030102c400b26101810b601d520b40ba0803000032400401040600c008005107030200046903554814591108107105040012414441c441c3e4101e46110480c94098521540c48180c0c00400741d00038881541c2130b41c201203410807000b1882e041c40c800d100215000b401c212844400d21480c41c4140c042e040300d09030080c052441c03290700038080a1700c11b034071170383c0c80c13203403183c142c0c0c988140e2b0403000b07061400150301c10301040c40943e510a00c2c204407003a4a04082c509628480c000030314100309843d0845005a0140002600d0940140540706607654502035400b5000018100329258209102c0e04c01d0f110701580e100c0300400e010303038403944d0032440240c05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 642346187 1250 642344937 642344947
    0x601062a0221011103100501090e0a0510080307050109030e0105131e0305060c0a03060b0c0a020603040611120a0e0c09040212070b0c1c081e060307080a0c0306050903091014 76
    0x9942144c00c2640381108000e0000b081100500541007440003600e42420000010342c10145ca100b075aa40040c400c585450b61103011440856202e00c4410003080c00d1001c8070394854a038074107107010300380310f0200b00c010605110400c2c02540c0501d041d203622100d603034000e0413203918003030000c1d00b03020910400140c004013502000c0081038060200178030032103000d0001c598034040b080c4000d00b15000c0e035000540e5880c007405007a0002c000440e1190005404842c1c440e00d03620349013420303c020101014018404500080e45038039282404000d1445410512003c1100f691150100368036050140d040d241d01205900014005290508251a20707803240411110301a03180d80ca400c1c000c0c1d00600040b44190b000c1600720501003030902c0302c2c0d10400418078084507107041803000b14241c80064954503074a8802400001c0b0280c80400020004103404402c990103065107043c10125036041c1c1c041940c00714142000185001e0000040f0384806d00084d0200094440300d4504980421b40b800007103180b0001040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 642347437 1250 642346187 642346249
    0x6050f011413020d0f05011404020406021c0e10021005060f03031b1608031309290114160c1d040f0c05060714010b01080103020f010e0301020d020c0601062a02 70
    0x1710b560301c034528a0100095550400c01940188540c1c9801688203900400040c000d46501081074600caa0b0703414a003028100c203002055884400084046402072041150005042e80c00501c803011004d82403010003ea40304c0405008065500ca9102d54059001f040100c104c12404030364000d8901e15007040c4c03032a54a06082c0d010000a01c1da02003400c540c0045082161103d202e003109004011501e400c0110780d404034030140e1004403020380315240d0b0500c0f0a040d9056406401580b011820700c0d0f004a55900310710743d0072100d1003298501603a00c20300c0c510010032600700402d849085014551441c090702d83c0c940d5a1010310b9410000112903c03148a240041c81c1d1720b41c0c001800025100305041440010309520b07081c211140c0c82a007a041107240001007015840c2d61000a05221003881d000c44815102404030f80039101c2e46241c41401440040e107910110004a44141641c000d40c1c2d6030b0243c4c1c3c0b00c100500d0503194011511300d50940c500c044580c01440e010390442141805560382c4844409404 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 642348687 1250 642347437 642347441
    0x10c060605090f040203190c05010c2103020a11060c04090203040f0804090f0e0d173705070804030e0d0c0e04030921050a060506150c03040306050f011413020d 70
    0x80c503c1880c51000384280811031a0a01c80e0105440041e120300f03098140540318044110028400e1038180401c8401140611541160b2030815003c1d501d119121103440300070080c003e40c800c015400000c3c2d4405070800e004080854198040d80c500038500381024184030005009500203442200e5002507204c7d883c0021341d000014100038840000001200c0a100340e0b610141c5200c403150400d150003500c0d030120400c0d0000d1070125000803802d241040740d91140254107845c032141580260f2141e10320740c034003003a01c22210035007400305500360b0070310003500c81e000140e58181040d280100420000300e4031a4880c202070760803040c2240146000c400c02a607425081e0f40519050724180d000604402c81441a40d02d20010001c0d00b05405284816095603a11140d45a40009100802c0c254503040403e01eaa65845109000c21503004160f070b40d18100a0b142590300d500c503100403207500d403c0a0005240c1c5448041b0207040321100a14180310008001c10015042d06ca02c1030030500581c2400089006200380c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 642349937 1250 642348687 642348691
    0xf030a15030506010330021902010905150d0609020301050a1512050117160b0f070c0506280e1018090203130b0f04080a110c040203190f0e0309010c06060509 69
    0x8446807402c145403c4c01c2541b20440c2c2d42e08050f111501d4030711941c146c0741d00007124490741075800c0e5030f02072100c030610040315881c2e12540065030090401c005000e524241c4001000d52050b01c0c401005001d945140d2002a4002441410784c013030f202031000c0103407a0310000040700a4040b072811003021894521105d0484070281c21010810b01c1501030380c0c000450800100c8620b001600d55681c00602d4041012824843c2c000d410a134031ba400b052190400429040010143c007000f09155111160303803148420410b0500c98483e1100c41c040d6413154a0f81c020070b1841c3c410000036080c0458143e03020800e40d4107144070b0f166032240e42c815480001d401070403031000d54016008044141d03041001402c2a1030740560103050011312924100038080003a03400c90403102681003038207254085000000c1550300b0070460b098101d8109000104000c0c4034010b0801da5406080101e104004002164481d00211841c2010005060307008008055141d8020010350840900c02e4401180c015200c2c03000c9a600141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 642351187 1250 642349937 642349943
    0x5150c0403260306010e0d0203030c01150e070806060307051306021c020105010e012705040f0b010803070c0306020327010c02060f0f0103080304020d050303040f0c0b0f030a150305060103 82
    0x102203400c1c0200180100c024825140440800c00e040000316000c02442c8400780c20641405030b801c80d075118584a00306100d1456070010241c80c2c82d032030b0503001980a00000000c0c4c120f02c1c0c0b01c62001003845103902601c0ca00410300d581d42c9071050b6031544107102e441d0f41f02408603018440f0031311100795002d01c0b00b140f04001d0070142c0c0c041c2c03501c41c0800d0000d0200108c8417043c101517906007001030102030300809a0380d04486582c1800440304400b400103a01030004240b1072225241090b0401c0700b8400c961400044040c0b01e18035454450b81da0701203482d180d004a060003002c2140c080400c202080c00c070740185401501e8031f01c15002c60406405900c900d440b070341c1841c07203d6335114400040d8076a01480201d80c040600000b40116240403102c0d411041c2050000a103950400f00204081d51503035518002d000d9802001c80e5a45d08042c1000d81c2e030b900794a601210705401d0681c02246031040e44045d82c5a920510015500f50340312147c251010b8840720081e00100503500e8070000104108000c4c00e802540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 642352437 1250 642351187 642351211
    0x10021828090c05180607150e060a140601030c031d1b04020901140a030207020d050c09011e060333090b030325111e18070206040f0515 59
    0x100144990241103807a4030084085290100c0ea10000e40c02c5022180401c00c1070081d1816060004000f407054010442d018040103500c2132808410002c3d80e00c58818202d1040484009540741d00c4010180d1f036201190203450b98004001c1110f950180c1c12080f150340840c20041035106440c2c0c00b04020a8880510f00000e9001112114070212003044001078200150740c150700c1c0c080c0c504000303040400403048518507118006144211544a40d043d40d9905034004c250030000740e40d5040c4941e4410620088604c10040c0744000070304040444010140c403100c91001c03091092a02a00768014428810442c84010000000040f40c0c10040ea00400000034000803042c4641850550b004a48c6030f060114006d9004000302d100740700e00d051b1600e1043d41804000d4903a04c450340382a02410400c222210380181221101c0364101000072400290500281c41000500d194042c220100b20025125480560448404600070500c0032140c403500d94018021100b4217041180074101891048038004910310b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 642353687 1250 642352437 642352489
    0x20f0306090115050909031b03040e1e090105070905060a0e1203130b07053a0306050418170a0203070503040e0601080f15010e01021609020a110609100218 68
    0x880c0b0202e00034080e04040e42c01c2803003860085001540c7e2301c00c60601c0030310300b40d10078500d00030a001013040364043c1604914030302150410700041d4416400d0350307204d42c2514100b0000120320311014032400d44a85215a03505240380e25003414441584c1c41000c0e00c0702005141401e074403d5480c0c242840c54901c01480055a91719080300703070742000f09442c0d040094283c00400c400070102c3c4c00000c69641716910a03d501c02041c002844458034900504820591035070401c1140c001ca075010b6000b5400c81300240d40a00c01c0403c1c582121104c03050000c8014024000901c884a000540c440a00711640c41801201c0c607044994561502d160003645c041c060000c114810410156030080c081031f04400780c0003140310703581001b03010f202c6029141f0714400d0422020b001c010655038401c00c4800030b01c961075090350308a5034803201500301942c0041c40b6000407900b0300da042070301c4800c006000340c4190410f0024040300031036001a00080c0d4230107424046401c003a1012030690b943c880a50884a51134800308800d08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 642354937 1250 642353687 642353711
    0x30605060301123e0f120f0708240408040506130503070b270310061d09070e07030902040605040e03030f0c160b060310051f080d0c02010507020f03060901 68
    0x464800d041d1020b10946400c14801c0144020707100d8480641000c9460454983d01040c18417030081091644140f180d901c0b0505407001107400c002003070017078090780d01490300d8100d01c1d5540c1d401c0c110b000d440c4404566080b44a011603003030382e9070014404c195140c903084e0b031780c4c0029103160041d644000c0300b4103280e8000c21040c51f0412907640202400783c1d20500f080030251150307880e603810300ca0500300e518030304440011b5941c0511040d000b82e2220305080003055160075014a0080b101e801d05440c12420038046201903d0006400c000c13240d01c0c50507452566510502200034001d244400c981050b11208003003403a50382c9006e9060301040c40801180c0f2071505098505060741c1c041c280301c800340e504210311400103040070341268a07a60000c913135071595203a46002c40d140419a0000e911024602020310003030702d00c102c81d00105070500301c420014032a19030b800c160312080985525004109080c0007400154011070191044500042113121075a0b0300d00081707814040c04030351441150350344031108940 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 642356187 1250 642354937 642354953
    0x1112091b0411191707030c020c0f1f1119050d090b0d020c0f0a0309030302120a050412060b0d060606090e09070b131d04060501090203060f1003060506030112 69
    0xa560310880d018420001e0859000403103101d991500f282115200482180160107080022000454a58074010314545003200600a040201004005000d065581c03a21443d240003603d6031180010041c900c3d030601d2642d090f1110840741c1c824014000c0c110708040d242041401111a1041c00c0081c020300c0540341d240c15414111013074444000d21407038a805005403450f00c81503400300510304400594030300c00f03801207903c0c082c6e8508205440c0d1148070914820154880342600459100f42c085030600e815210380e81d800c501508038900d0011300103010030014500000710014283c2d000d8400003450142c51000304581444c66907060303a150f03885150801025910099160050805184881050030301d00c00c1300c0d440710701a02c24a900701d4004212081d5038603403425014000c150348494842d901081841c0c20300000710850b000e84403070b8544800068105030070f00840b403242400403c10400d03140c3c00d200b00101810340c0807d0504050ba074003000316494407400e004601034040521002d40c17281084c075000c48 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 642357437 1250 642356187 642356233
    0x9030f2406030615040c0903081309050105010c03080403030b0a030503121f06051602010e060408011e05040b1b0d0f06030501060501030207020310020d02131d10080a06111209 77
    0x301030380c004401c00c004014019071501580d24100c40206e4181c2d0307441d60440e042c40d91900050300780d450000310b400c000d1220913442d50442e145440144016a078810041d115903020f40c3c005000301c0d90030b50004000034800d600200812000410405003140c4075158280b4681244804600300380c440b400b40041040b00d200f41c0c2e0407282000c500010041d08100300101540910704428500301a20240c06086a0080218400b0040041e02e69038555507101c4440b806840c21040c6404117106034459078080c0c480b2401014407540d00f0100b5441d41751038a00707010803d82000c50f86640301000c18088c94181613603d01824880b0750942d10041861415410320508560311940100d051500c10840c0000585001c80c1007801075030078850042c2c5614000324a403029214010034a404030301e007140089a6175040740c41d006484102c03000c40300722a40d9170b102000015411070189402c0c950000045000041e03003504000c00103501d01c030300c2c02e003860b1440c0f5001c0450b2500f941c2c903204540103191131420044050007605 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 642358687 1250 642357437 642357439
    0x12030302030907050a0f0303120609020c07030b010b09100807120e0a0203100c0e01080a02090411180306010311061804060f03120815060c190c15030e100209030f2406 73
    0x10070240c60081800411003481c1f00c002d080c40002c0405102074501c41e171000000701800003040d90380c0e5012004c51919840701e40030445800d141540049440344141065071092440680001d6075614944801c0d6000da030300810354010403003400c204c00300002040c041d440d01c0c1d400d58801031125500030301c1018140014207400e040058640b04003401d10aa00c202e40450701002800d0500c904c0d1900c140c8a0042d101e81c0229581060402c030728100340c040bd60b030042c0486040c0b03070301c1c2c400401441c00c10140c07a61f4081c0320281c441c011100049205141a90007005042080ba0401d0701004400c030100d42035039041d92010354110382c012400c206100c0381d1030b080508000c0d6454a45624500040720400b1805806c1c6c0d01030003004046180c800c0340d10200410003c0c803500d0300c10a00c50030110f284c81040d100c040e0085280c01c80e040401c04038914000d000300c1030780554002c060090291040300301002074102e00c0010350305114010941c40150030500081540300e03200300b45203085105650714192003400180c00c00b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 642359937 1250 642358687 642358699
    0x3070906170f07140309070509010803090a09020d020c0105090a110306090d12021c09020f030c0d140a02060c0c010207142101270507151202131203030203090705 71
    0x1000c2a00201c40e08940c8807882c8607400030035441d407400880e9046043c000c0c90300750320000010b000d42000c00064200450324110349406980e030700c8100f225101d006501106070803e19a1703c040c07007011410380260040c031800000050a25000c3d228031400d4031001c4e00d00500c00c3d04828403c0e0b0600c411005d04154002094005021a0410b070b241c50f80d482c0c11021510007003041102400046004940403a104580c1c40d40240c1e6074034160f4001180101000c00c01244501d117029142c491600f80030540412030100140700524139540c5450b00402d069010140c0c003090b0180701080380041e0b507040043c050b00e0503c2001000540303c2500064500507c1d50000748095034000c0d0150020713580c00c041007052054480c00324600701ca1513030519015203200400100f03560324008000b08114281260309a045000e1000c0383e0949544038407103146402e03080b10200000d41c2e00c1242d15034143d1903400400c5103004d6804131043e8290b03180e4a01c5403c2c00490741c1100000d400009202408108001c808003a05040b155 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 642361187 1250 642359937 642359957
    0xf0a1b030e190f03050a03090b0708070908010c021009020310020703050304150203060a0302040902120d0e0406140d021014031302041a370807080d0914012703050303070906 76
    0xc3c100c0d54102c0746001000c2020004100000c280300e5040b0712010341e4400c1020f811410301400140041c402207403628001003010b40d0024610300305008102d0810500e4001e0b0504041c3c040c8084003030414441c081e601407091104c43e58002000384000c1402030b00aa507030300c0d120705061400004a850401e058101e03917005205018690b51600303001030490740c2c103c0d00001c8541d03a920104200c507405a8207101a8003c1c03038240013007107420914542502600f185d040048940b0b0728040c860190300c10081e2500301100c2025038005081c2442e60413500e0502e41003c3c1c04001203801c0200b0f40d0781c002c40c2c4100142c43c00c40c61900850400d4050114900ea80000040200c00d40c90013003030042102d8180c0780d43c401c100d0800c1b04d0700300c000300d142201495403074100b44d01d1081e02c1c0c0c242d5076a6213040e44501059441114104401c5d5403003180d00c03a05441e20344080d01140c00400004480d156424081001c442240704040e0120b004940d03284401107200e000551f4580c9001d40000e0304001581e4801403e001c00020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 642362437 1250 642361187 642361193
    0xf0a060305090d02030a050906031305060f0106110a0f12050d0c09090b120607050f090618030f0715080a0b030d020c010e0a030c03080a02190c030b100b030f0a1b030e19 74
    0x1d640948d03a003554a0340d182e1b501c900221404030b4040c7e401602c107001d0340d414000341060701e05105050300c1207074892141e0355000c180303120750782c0c84d103a0800750196054840704800034440c091140c08013180f0f4a4002e00340022100c0d1a800c0f078030184190800714040d04000c020440c0507008400c2882c4040f03036164009070b01d43c444039444640080c1210100300d00000c2d21007290500405032226000d000d040d05480e140040300500c00d26105d90ba44903c0380c8100100c0609000000920800356442024100152046105c0035200d049000d05a041e5a43d190038640c0015201040100009110b0b0f6000300403403034140d03001501d010584188180500346c1d44c14140049103401a020045030751000c00340355503081c0d0740d600b242440780000300102004110079044042c007030701c00c80050549029500140054035140610301c002c10041c413520301d00b07160600010715400060142641d0261a0342004200b004414040312041031003a03004d02c0100340c1c2c545042c1c07241d00c010003018403c00c10140c00900b082480b80c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 642363687 1250 642362437 642362447
    0x201150905220c0b07050c130b0d0618140c18062101060e07050304050709090b0604090f08030c0a030509010e1c170c0901020f150112020f0a060305090d02030a 70
    0x14500c511400308140303000410400151003801404450442511703001545801c50311030010324600e40c82844840000f5024002c0f5100d8603948110040c85008100032641d100006080760300758031036040c1d070f00030a1400800c4801004103018007001c0060071685d50383e202041a4285140403030010802e000702000410b46030040c190503440b90b4002c0205d061251031904501410303058101548403041a0700344400c40f5004805107004034859400e40b03084644516803042240c10b4072601800e03d81000010880701d0a003940202d00c0240034050183c0c4a60b00c98403254001c0c2c1c000c3d40d02501310702c400103801c2e5826500d8460305801c95070b40c01c02400030001c0b899506964004822040d007030515071075060100305014640c0030280784079094140045140c600044102a08040030503405400754880000c1030b604085840034a8040c0740c464441c0690809103034003a400306402c01240c02031440e1188840030765686150200034a02660045164542010001e040500d2065a601598418040c0220043d000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 642364937 1250 642363687 642363721
    0x180b010206070c0f0c081e010c0f11030c0106030503032205030703081009061d01140a03110301020405031b03070f230a050409060b090c120606090612070201150905 72
    0x103203440f000c160002c1c1400d01c03000d02c4c000d10003454070744032002c006407403400031558503c0c0d0b40e08502503800300e0340c18410311b50071b8503246120040000d044007001c61080d8040d200d140e511f1400d080807203042c98051080070307084500b140c00c1581c10364000300802005500c801c04001012009100104020915541e190399a00905130002c1c2444203910001c1d04481d254800c0c33400901144c04140020390740c1d046680031283d044000000300c940400e002042c00010455044014200902810646891038481144001c0c07001c05c0c855065400f0400010107650402c1003903804888240f02003501015541050300c4c1c9500c581c484c4046c0c40d04d2034400c00952001d512100a90f02d010042ca410f100884c10000d12111280c2d000a5440313850071000380300303120b5603500c10302901005031107641390b5864104200d078260165054032044041c03400005401c0341000320180ca00003001810480c00c0002c170008218035860f0484003000107070756800c00301c082c0c0e03030030014020001d02e81940108124102100c200080101d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 642366187 1250 642364937 642364951
    0x2041a12010c090b0901020313030b0106031407050a0f03061d06041406130203040501060e040303150e0108070b0c0102070c03080307090b0310032010050418150608040804030b070504180b010206 85
    0x20114030145c0d264000e100310b40c0e00e0025407520440241d01ca10300714070400400c1c0181d00000c3d2400500d00b00c03180314284114001d080c552505418090450011100103860a0141003003603122000024007006102e070980c460514070921a0152604c1800d1104403544001d85022800141060110035114a10030102d16590007034090b9507540c03a801d000d805003005900180e407145a490400043c594503610000c0710000c0e00c90080d81c8a035a807440d00f802070400303020300a51030b000110104221007540f80188070340c003c020005800c248041e01c42e10808021a03100340c1d1205000000c0007030540d40f100100c5d024100c0c00c010141182480a4a4540f914050000074546080c540c0042524561582d400106010003041e4272032035086051f0040140d0880d200d00c0c0a0b0442c10381203100e180c2c40d42e01030024440d2840003102c0002e8981041140d40a5003e00161f420007801c00c80400415142045603106540a8072074a58440c904030305a070382d40700a2600c0315101d07807800b000c40032581e90208007035401c01c00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 642367437 1250 642366187 642366209
    0x90b2703250609170910032d06080307080a2c040903050c01050c0a03060e0108030a1b060c050a080a2912060a050f1f0b0f040302041a12010c09 63
    0x4051070000c0040850101c0540000c401070303004e41c8a0040300300107181495041c3d8100078402015030007681601d403062072500c42d502c1040542d0500300c842400c16811403500c55004a015503607012441e040d43d000650940340c84000142c180c12280c1c0050740d040c03c525000c2c07090000d890245003000390050700303003020b42d1046407294454400c0c5842038054410300182000200502c1c10682c0d000d9415030310481056000c603042c48400a4401d103544040d504071050358014600d4064042003c0741c0320440c0801010030100c0c60312940e000300d0702ca407003003a245001940311141e48460b054005024544001c0481b0012802c0920708840c3c000c03074440d060288042c1000c004030703001201e000180a5040410000d185210760020032401c210650056805401c229010381099107030360101c1c1078500c102c008100c09010722411b007000001d18102c010508841040c52480c10f050f260380c00036040c0c60458860010142d00444160740502e800111186c0c40d140183c0200090215100d006e000380440e0311410b14001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 642368687 1250 642367437 642367507
    0x9030c1011040510110c030a020603060f180403050a03050c07030c170d0227010e0102030307080910050703050a06060e0a060810090e1c0c0c1404090b2703 68
    0x2100c078016180034140080c225034042e400d0207002030680c5134016034451544113501700d00d011410007140349040039030094500d500d159942814072048002081c03025401c14811415211404000b11495015074480e5845568030100860020305543e80a8201d2400807004c00005000940000141211552106e28610740c80011140080365014454250000c507000245141d100c0e01c00540d042c0ba4110b007204c0086c99000d88000440d800c15420004a0140c0d01c1003020403070381d40c0110000b03940007450038100e4040c98503158548090f15404d0366000c0100340c40d00305010022255004410203040a1f00d0300e110b12042003000a004213901c0c0c1708101c14484100042038200c0c5000c1100c4000c0c002c04e4505100f45e205400751142d5030030348406501103910402c0c044130032a81c46010841390158012810362052410004142c4404001c0741c50070f0b41c0700c0d0350f501904001402c004040c500c00c00380070200103072440c54a0600310040c2600c1040640300d400c200400465465041851484545102e0f2101004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 642369937 1250 642368687 642368711
    0x6090302070b0c01060503210301031e050d0305010801140c03150118030b010501020d0e180702030d0e07050f1801060c0203030708040e061503040b0103030e01022a010809030c10 78
    0x1000d466004459880400544000e802c241508058200c546c19000c03a8042c1c0b00007510309910b812000705c00c0303020102c2000100041030300c40c2c8040c070708010011414a6000420742d15103250040c99098140400e45900041046410a1081000c206d5404000120614213080d0f404001d1200510050b6110b45445d41500540d02c6240340740a1160f885800d0b402e4a5100d06044c58100300900c2400d005104488101200500c0356802d806c08503c041e042501044d040100903803000340040482c8210710050001d03ea000c00a8002c20790214039040141484030b082500b031003a80844400e0590142ca00741240a10b80764480425604603982441e10f48048d400300e1000904510482d00080d112920100d400310340d82e01604200c5c0d0240c0710407154120b246c0006400c4003001e0104a40107840d4440100040020070f000c1e00800e070300c03100148103507014003060062100c243e01a508041032450800c1000e9040f95811149403a040030584000314140031758050860340d44c0003c40e210031105621070410480ca = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 642371187 1250 642369937 642369943
    0x712120b060301030b0a15142205102108192003032205060402091503032107021c0e042a1202030606070b10030215030412091206090302 60
    0x25954000c06003070b03507560341c0d04103000500001c1d515800024940452059500c0c080e42400f811640341c140901d40303110840040115030140349a42c0400700c003940b0a5100c003440310384680c92142841d011240b003001d003006144002b620162160b14981c0512884180105500d0015074001c012903090601d000c10304480202c0350000540c410a40b0b11620161030112204044050361050044200c101c110b202c0e4401d5002160004c81000b82c0940c100101180150600d9010150b201142c4406001c00c01c0b940300100349941d01c5040403520105190170300d081380d004e0325004a60406414030041a90ac8034412b94600e0004100804500784518101c1880ca691210b8200d51006108186d110060030f000320704038600c40c6078140303034000010b02d0138091804400e141d00c02c1e41e020b01c801408203820a0300559540a000d41c020300300700c100003103005d400801642c480302208032110401120307948038181840c01801220409034030409011088409011840d034032060000e01391307000076022a07a21428141681 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 642372437 1250 642371187 642371201
    0x3010320041a0d020a090c0203041d0112110d020a17010b04061a03040f330903090501050f0c06040c0f0f06080c0702040e01050403020304150e0f041e020304060f11071212 75
    0x40b02d41c2451f65580000390048043c01c00c0320803052000b07101c0da480420340d0802d04000d0107004064154040380d400030a001c071040e0041c1e01c40c040c0026039021526000a10071a00381d601000180c510404040a0310600380513510741458291030910100c0c0c10045c9555800d004020b0040384040084001814400603c1003000000d1b044034001c1c007040450241480e40e080000c200c640d101024071255440401d442c442c540500d6015681c88004a0a00c00111a2030b80044070140c803900023400440100c500a1050f03a01503440b480b07402d44107502c0c110309520b6404140e8460000d1400c852010004280c00100d0550722203c505d014640c0c0384603c2c8002401400603a030740c1a1a58a000c04200400d9000002041a9846044003405102d011a001c0351249a000080c9812240c114200009824540c02082d20000aa03c030383c4100010019454101c0e0012103080d90102c1e12404407203000c14040c801e03001411070b002040c5246c500e80340c540c550f84c000d030001000e04006541c0c10000b02000143d120304 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 642373687 1250 642372437 642372449
    0xb09090c0906240403030906110c012003040b0a0f0504180504020111100b010206060f0f102109150501210206040801020f030a0515010206131703010320041a0d020a 72
    0x3e81640108100000c0d250080d0004401080e109100401c295004481c03440041a51400030800d010040d401103030340701c103c08000703800d13071140040c07030b418001091020700040d00c1b40c1001e254488001070001090074005a0750301050010810040c030030110080100440710b85182c40104840c1c980d071004030740a20b00820110a64040c08443d800100204c1d0896425500e09a007180d5490301c0f40300c02c001c018a2881c00080d0f01c04903002c090040c5003451042294030f2429400c104400c50b003c00041e1134000000c001d00c0d9102940c9c4c101c25010800c8114800480c5044036008200645c10040c1c0c80d51035000d6440684007511016142c54119a108001c440150040703030020742d01c0b11121b40c00388106400917148506480d00f040c5c006511540c1003008135411490580c0180143d44804a5207003805424000960708400e02d1080f100c03607003407400c000314001c0d0322801d07445081445500d29281859800340d2302a210390f092040340d20501c5844459600c1c03c0780e0889001142c0c400910010350080081d900203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 642374937 1250 642373687 642373729
    0x912030712060b0d050a23090109021c17210414010e030706060b090a0e1005090711010e120d0c0306080a080403120c02011b05010e07080f010b09090c0906 68
    0x1241983c030200140807100403510081c07245881d500c16030803d0b00c83d88140e0b4100400c1c58100100c02480d00131009400111401c0002182080c9802040340b16084c00071102030518012003840401c00c03084080c0c103104400340034603420300418045c8850180f0380136803010287d0482c2c03004241800f00080f43c0469101e40304000700440c00601071110b483e9000f4850a0704d070f0034a0b0020000c2d0741441a8201e810440d0020961301074a41130203a61260500081e0071210514035460380820680c46401000d8001c00640d00c0e400d26800f41c0340480ca0a580464050b0380d40780e04982c0c000020034000e07c084c0d5100580d03200c404a60309076400070403002410994480003c4cc411240e01c1410301107141d000300240da004c1d0b50140704c1e860009030143d07041011080c00034000f80164408155241030031042c03003c1035105500205010340c40ca0074403454654141c00283c02e43d0030039100000c0c0418248034000e1000f40546512029240ca00e032215181e9401180c52401102d2820020307816540e5000b2138030349075008400c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 642376187 1250 642374937 642374939
    0x5010306050601021209060a0311190e0f0103180b062d0f121510050d030f0206060a030f150e0f070e01061416030203091309020414091203071206 64
    0x3180000d02000d4031000d0141c0202c070301c0d041d0710350f9191080700c0020801400b1185003e5038884110001d24074483d0f040603560040c8000060000840f0180005000640d00c1d4001d00507044200308468040d10750302c5051501d441c0f842c5000407078030080307a0304e0150813003c455038070383d80d6401140d03204169840340b07032091110b02c00030741440d41d42c4020600840425154070901e801c030b04060001c07010074103091041039409002101d20007040c0c2d030002c075401040f00ba01c905849503214003085810004c9102180880e0305c2c5541003521079030401c40c5580c016001c4a500d45018a1601d6601004422039005001c21803403100b00400682d5a800080c91003602d03104a035040307140002003a441b50400c0c0200030f50300a41c8400015141c0c49109840e020078103c3c0229071600000720407a000c203d41a120480550006100d0280300e640d80c0440e50140d0198070f03c005c0f840d9403103441007004031420306581c1d03c201c46013502405a481c00020b0f541d96184013052800b5601d0b2200101615492512201061640d0074018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 642377437 1250 642376187 642376193
    0x108040213110f0a2006090709110d1b14040510050708070b04030f080106080c030115021c0e0a080109031b050708070b1809070f0e0a05060c0106080d2f0c04050103 72
    0x390b00c02c007252010240c1110300c00c412102c90344404060b1406807e42d8010301c1c00780210006a80301c128030000615140d490004080f090805544600c2c1000b030880e05000d03400b8880e150080301580a1a1034051481d00e06404c01d00054010310445510504100002c145201080390400c00c641d80c15410103d40300107840c05180013050704000c103607200c00084c0102c0000400138007400c040d90003080620445421603003042c0b80d0700c41c0c28402803048030442c868082002c0070241e5402c428070241b007030307a9a0140150900c10500028110395801050242c1c5040c41e0040440da0007208406a00541c8181461880042c14903510f0106503400101c2107010700070340064004000c9004007010aa2051100031445d290b00c10840c03840d204864040c04034410070042c0140c0e40c460b11000700e003d074004114100061304e44002ca10305030808207030381c03520740c0d075814090083c643e0801001c07006804070328041c13134503030790701c00b0304000f05241210998100d42c0fa650b100c80143c28280114019414040c00412031907a40341 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 642378687 1250 642377437 642377447
    0x151c0203040c18020414060d0207060e030d0e030304020607030503090a120806090603010506031c030e030415030e1f110c25050102070e0c0d091b030b060108040213110f0a 75
    0x111502e650025192021036482c0743c64000d80b0201e5040402c020824914041404145d90020350300741e24840d800c010060004000e8411050400702040c000c43c2c0ba241b2030b22034441210702124000050368814400c000040c0e891404850701d083e4549040d5031603403240301000703150043c00780000300441801d06040100c0c40c1c0c02040c2611906003200d80d0045601c2c2d407020f05080b503509030380c1703950941c001c0c150040005001061202d01a16545000a80e110203411076600b160040c2e0401d00c1e101e0310302031304210a292b05010707040700442200080c01828400041400d0b40088030380003043d2543e21550710140318241102034840310b00b0410259405441d078040010855602e4480300d0015504d1700c103001c211544009480c070280e41c921880c0c2c01994441b50b42d2502079800c6401500601c030b488004076000545003032181c0b490f040d9581644007000d4214500842c07032040c01054981000a0b200400016940300c00b612a80e410040d40300040030310800c1d010a91074071600c21219101c03d4005580600180c0c40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 642379937 1250 642378687 642378689
    0x310503070e0f010e1e04020f041505270103061e020403030c0b180316051c2a020f042003100602010b030307020a0519080d050408061302151c0203040c 66
    0x34200c0041680c81d120b01c004d0484054031040305803201100700d011994059515650442c0c0010254210b005108001805a814139210080170308240b8908204d0740c01c01c800000e0180584080c40814000841100c3c013002105100280082e0b4491049143e81c0d41c60742000001440e100074203540d42d50710b030b0802500c9001004070888401903008000340c098030781032091600c94031091021354503090604841d11406541104251110301440c032520801c06000e0203540c0d0340c10103686410284443c119407100b4040740320300c072880000e9558883ca10060380e42036441000507034116000500c10200048400c860070300009001e11440000083c00002d4010340e60600450f94a80d000380054152041030580b01d024001d03009410040180c410320451030400904000000c4402c120440155519003052030200d402c419100802e0001a043c0702d0740b0310500003560b00c007203c0c40c200d40c1041119070104030300440070307102604215000305030303001c603680c41d4582c0403100301060409641368206401d11044490301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 642381187 1250 642379937 642379951
    0x804091109010e09061005072409030207061b14030d1d0111180d1406040303200a120510030c080609210301180f0516020c030102310503070e 62
    0xa0000e0503d14641030721068850382e0003500f0b960074600c0c468016103081c1c00841c0c040310782d00c03100c0400b9080c0011001152160500c407640118104d141340c02d002e42411a10303005003040040580c08180034408480035034820f240e0140404c0d035142e603240c41d0743d4203500030304484801507800d0102410b000340c3c0100f5040303110f00d9000300030410b01915094440040c030070880d1541c1c00c02c1710454400000e240464204406500804a4202c12140c4207021810140101e4088020aa0705c0000340400e4500c2c2c1c0510303240b40c00348019189024054400506115240860180e01e40d841c1c00004e0298118440f4420040d035000119205154440356255180c800c11904400070f8400c030303d40010002075502464590b420400c03881c2d49544d003051382c40d040c00038590b00d403c44103d1301d5590b600210000c0744202807148d0300c0304100907010200050020300340360700070160520a0b80180103990000c0444542501000d9060401300d40441c2540b1590344810342c254132440c1e040c041c01d1400110111598001441500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 642382437 1250 642381187 642381197
    0x170a020a090606090312090503030318060f040302060a050a061203170f1b130333020906090d02180910060b0f0307030504210c060f27080409110901 65
    0x1448040040842c1c00500c20700707001038100c050400200b8030308190b2080300702e41c0e442c100701c0481d00c40b00420314541c01030b603138800c085005c13010072180c1c0b41c1c0510106802035414450303c1103509003074034000d65600d0082c0001c08811755513004103581c3c80041e4010001410044c00f00b41083c0b0407800c01a01e002115180e02c010400000b000400705000030003a90302c5140038105c01c1c072000c032a0394414109a00440e81c51920048001030100100d4000803402440b0603008034803000324103401d80a1404604540c80110b080c1c1c0c018040700c1916a81c0005840e02094165440c1500c0e0600d80005601035181c000442d9a1800702018002411808244000106003400c3c0512080d41e6a070309694903841202d0041d11001c400f40045501e0b14460340016400c81c2c05101d480800051500710580c104071913283ca00c0c041420405160100800e074022106800c41a4000b00008641c03a003030258039103040e40400108805003c1e8072010000c0d03030802d88018224800f001c000059a41c280c6001c81c1c1e00901700c1310702142c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 642383687 1250 642382437 642382439
    0x4060b0a020c0f150f0d1a0315040b0615120c03010608010b040501050403060c20010e0c040504080712021c0c02090f090d03050a0209040f050109061d040318170a020a 73
    0x3c1081030020f0500c01029145540c490300040c8624200d40201a0050001d907081004d801c00480a0050300b648246594110100f09040c000305440c02d00d01e550106590b45500301000041002c00c40342c15480b600030341304480b41084041c17210400d44656007266080708000824400008a0304000e141039451a455907500d603601c0d0546030704d45028500c00d079400180100f200f0300024035130381c100c00740e00c2c2241d06100e20801d10080c5030070003060703a00111004582d50f4500174008a44200020b143c000e4047e18104001c5c20300c0d484402d00351180c4080603100f406504640c42d0841d00c03c003d40c0303640d610002c2c501c8075400f10392000100070780804c403400c1e0b05c034044900c007081c0031501d988041c078090b41000f801030141c0820041d080d00980703030040843c40016424003104403280c807507004d0703441392542c0e04000044a6062080e039004079181500b0030b800c0107080c407040144059241421071b4100d80c0506000702c0b00440780c0310070741014125800a110800b42c00f450b0704903804c0e001403200030862007260304103aa2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 642384937 1250 642383687 642383689
    0x10305070b16060b4b13020f1b0312071110110f07050715030e030d1104050d0510240e0a06082b051c0f0b04060b0a020c 53
    0x180c00b6000020702c104003100168000542950b115203400c0c0400380240c0f84c08445000d0000008943c9845100d1040191103590319a0042c407000b4506001900b00746100c03d44e414002c5004d01001030110031601d90b0000e80c20807051412000d85029845604c02284101041c0c588a40ca80c1c01400742d036000241010701040b03840b805820b402014125940c000c0c10000c8a500340103001c4d219500c0f580706007010030030955030000c013110020b002250081c0001c0400510700034254a92520888034802003514190605012410200890f4818074400501107440a442c03030903981c0780d118a43c13005500030f00e0303002c181d810448080b4808034201604c4a0402030310a661041005c00c010505554659101054041c0701500740d0030035542e08a1001c01d000285103890308400781c600700804814850b42400303c2030b00404e10a2282c050400520280707450f0703041114426039541c80581c0805011761140e04c2d003001c0c0040740325961110544481c000e20501406e45c0e6085a5980350f80800720850060107020540245 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 642386187 1250 642384937 642384959
    0xf1210150504030b160306030615031406010302030a080319020a0801050f01030605100f0e06030a050603070b0c0303010e0603190b07030b03071404020906130b04061106060f040216060203040b01030507 88
    0x21030b13420400d00d0701d8a03510071590222910a078410f01c410b055039031101101041451040800000d41400c581208a00314144245880303003051584032241d102e00010710042e02c1c042400d480c1c00c2e9000000075100d4440f55982081e000648500010251001c0f03003110060351302400641c100d61040d102101103440480045081d100c940c061160007500c0710b0034016603940319001d0b102c455070103842c01d82c4683c203070040014403a0f0b0041d03814905941d01c8e541071180601d001c0c01a171005000c0f8814540c5070a2070703003409580b640014450a01c02c103c00400040250300c0030311074a40304403101c030540c160001d4545412440c2e41020385512002a15020035000c450800148400c2602e05d421654504401c0c2441008041d600282035660018805d001a015200c1c01d000444041c200310241c0325111401c01c90028054103a5104840e07050340302d0001c0c802251510100f6600204040c2d8015a6070769284003094400120084020314680c400004c010510100100c1141a03902c0394003030b02c0300e459030f40300b113019 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 642387437 1250 642386187 642386189
    0xc02030f0604061505100e010815090a090b0f130b07170403031b050414040f0e06010f08010515100c03230c120301150c050c0909010203180706090b0f1210150504 71
    0x40820070691001c00387e90301030002503501c0301000103c143e0340c2500ca40800e003c8a415900c003680b440e15000c03600c00b001000501c1c1a440141980340492030314100116a000b40380b0458003600d0418a00045003642e4400d01d2680d582c0c051000c0e11458505003498001c0081035084020104c0383d15000140a04070703c00c8040350110b500000a02c400003000c0c60030000203101c0c10010700c0c0141c1d07599000810100c400d000c0107000345800300c000f9204a00c1c080301582036450007410685203d0046414110580c5e40d9060780c00c0c00502c0e03182401580315903140981390f040c284101d460814240d41c1141401c0c544020007049280d01c04170a41e01380c0080c2d100da02245000c20301030102d01c6044050040340e001d118070680701000c2d0003078045440107c00c54000c41c000240035500d034a1265000010401014080032540f481446910000c0030701524021009148242a0051010340d0300009404414822004203840000005846078403407400c2c1880098084070081c8070324107190024003000340d2050700800a942c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 642388687 1250 642387437 642387469
    0x30306030304060311040906080a0b010e0606071e0219031506080304170c04020f1206030a020f0d0203010204080f0a1217070e040e060103030e0307050a150c02030f0604061505 77
    0x1400c1c6814540e0603805081062170b40012003000303210004500407c0e015030030041c440c0c04060030310543c2c10b08003410040c3c416004060f03001c1d981070510445813034001c00c484d5105d81120000419400c000f0b00100f10100c90107001e035028068402280b19500f0959441c8102d034402d1100c50303409041caa013040c040d544240b0903d0001d4105000400084101d000390002c02035999050740e00820302100098101e802c8008001010200452503020409507118495000001240141601c52842d40000e03640e01c0510f0b1074a016103002440d0b1404c54070250140c5000c1d04469041e688100c0002800c66515941e121084c0d0310300e408004003a1402d4021036241c0c0f0020000102006190707900e081c00d482a90030b2805d0603030042d6880300ca8590089090150602031352003035442c044800240001c2601e031021b140c109074402c5d045150104040030001c00780d600c5c848a542001625031119000107420620800ca0911083c0561000c2008010250388070f1141001380d2000c688059440d60203115901c21010310030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 642389937 1250 642388687 642388693
    0xe030304050f0607121e17041217090a12080114060304020109090e060402190b0702040510241206060f180b04031505010e070813080f0304030c060e03030603 69
    0x1c0c092428003041081c0c0300d41000e850240742c035401c2c0d0340b00c40c951003038401c0400000b907029818040c0d071140c000240813282c0051134461006220701a0b1b440313191902a100401c00c007480300501910750700030701c4403402140b030f11220640c151500085d550b440708103240c01254800400e00b10f0b0708040b40940b0755141a542607501d4246990090401d00c400c40d44060001d034148041200c001884410600460340c810310418042d1441d41410b1062111401011002f0603040604d40e4042c0809102c01c01a90841030f0100ca0210b199141c0c801c0f815108000740d041882e040d500e000c1550303c00d00c504915400d441d0400e0751440385030080f9940c1d020813600389008010001ba101010000300910500600421640b4080b075001c4260781c540d81524582c4c00341c1e00480e02403c581940d105560300f503200322401001c501511420340d10301958000e03c1508010112003500310b83c40c4882e400c0c40414000e4454404c4252521580c90415040142000b494040210303070b16828280035030442000401500c0c0a402c0c05402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 642391187 1250 642389937 642389939
    0x20907030e060f150d1103121e0d0207320706050909040c0e101703040f151106070302043213090515040b0a02161712180c010e030304 59
    0x8086402c1601a00ca04c4021583da145043c00d9030700c00207482050751041c0c085038010100305082c141084c00c584042c49051005002c0c0c00c0c0341c001641141c80003002c014404a54aa4849188070b00a000c0c3c0b00c000340c441c0d0207066106c02a546030686110005440c0040c0410007445004441d56405a5014080002c1d000703020807844c4e82040c0c144d05030420700c01c564160301e407511001004914801180e030310b040710200310002c114011040303140354401213010014501c3c045c104048086110000c0c4100f0340e99a032811a014a584e01ca0b0442d11000b00a000585241d8240103c000b0060b41150240740740703444d000e0350a1000181440340d8800740d40680001c00f10a560324a0400c092600b400480c00841c50312500d40314000b8405211045e129107040c0344516007070800d41410703006000c0013403040342034601c100100c2d00d10402c2544c20504640d071010f04a005181e5155424895000d2040140010050340050054280003a506031200b10360f2102207d4103a007941c001140c0712042e034404a5019002048 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 642392437 1250 642391187 642391201
    0x62a030f092106050606070f050606040e1506011407140c01030e240901060302131a0306010b030a0c0908160810140f04050f030f090418121227020907030e06 69
    0x10059005c40001d0000b803c090107911a03111006880e64125459080b0400300a060b2415100c0c91080f40e04402c0101001d10007010b0b0880011000741819060240c0c2e540c9111400041e00200c42489500c601982810f24103918410b9039012862109400301c2d0a141002e603852100040f50007800c071011241044031070b600c076080d004021002e85a481c00e95210360021000d07131502e403c410440c0701500d0000641112000c081c58100301200241d6200743c00004c010009502904150380d0080c40320280042c00b104900001e03561460366620403c070718010318500c204401d48410300c650446481d48140d420411861080104030f80583c2ca4001034299143d01042d5018070b41720040c0e922034410411940c0000514803540e1551708061900744c040900010340a00a00705401290b0300382c2001d44480a00b40702c0c541da00e155241c10100a00704006c84084807590305409a0002c500301810210345544001100f84448920120150141c0c0204151004140110f1180c4104081d00c25901d003e403100d03403a585 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 642393687 1250 642392437 642392441
    0xf05060307020c01320d0f050712020c031b03031603060605040b16061518180308060103090c0b0409060e04080f0a0c0b0a050109051e01062a030f092106 67
    0x5481c0c1902080c62960140c06003407110a10079110a60f0b02d0811b8a44903c42103032420341ea46200d58080036401c010500440320380160141494a40001002d6203070014035030b40d14035500560542c80080c0c00440003032240e8560100c01507000d20f000324900e0070900820fa41c264143d0b030300c6100e800c0004904100801050302c101d4058080f404c80701c00c00d8000c0d04110f0300c4420a50303611701c035001e24121080e2400c000524080c030321808120321a0405100d0b4803241c100f04052094024405014003a8006c00a072050703100f0340c03014980355802130b05031508a0b1074a0040245401a006005101d407401d0000308100003034500251180394031040040c9400040305103044140c0207030f04040305003d400c5510000140d96100c0081c4180003413440000c0c15032403c1c524500352503010300420308000011802d40c03204045002081c0c107541172802d020750400e54046c04070724840b0014044c40139010000d6005020154084486001c10140b41d403006143e0f5210b0300401d4000340008001c240b6142070300e0310000011416 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 642394937 1250 642393687 642393707
    0x120a050f070c33020c0c1801050913020f1809240402010c051603060b09160e040e0709090c08060c040e04030e040f0f142406071e03090f05060307020c01 67
    0x340401400d00b0030b16490540685e0403110000c6840d030000c8a0880303030381c101521101076228806038800b5a551501002c1800403801030700d1158400c81403002c1c00203540700ca5006940090002e0050f426884c8401e400420803801520702c64164000c200069032a100380350035411080140c50b00c00c84860320380c0e03401503c0032410074030f080b504c0c1d01858210268444203e60840000d5000b16030100e2145940380c100040c0d40700040c05a414400e0300395002116a0344031005444a080558000826081d0410564a0400940e100902d8035080030321820401000441d620116100c030000c07949161681e0030000222f0003140501003a004a10000901280c410070f10102c402d0800307000098200f200380032003025104103c103030002407a02c480d055282080b10131f40f040e0b400910090300d918140c16480c04594084a02040340707100e0200442c0c0e00d000e1013241c403028150014682c40010051a103407901900101c01c0c0c3c8102d6a00020445d00003441d070601000f100d10507003c2d0340c0986112200c080c0103650a200d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 642396187 1250 642394937 642395003
    0xb011206031a150a1205010623040908190e0f040c140d060e0103050607020d0306150806040b0a030c06090b0a0504060f020f070f090e010204080c090a02120a050f070c 73
    0x800f00a10551a1100404068042240e540c01d08210509016081d0340031984206e2113000305c198002c0705990f000d2050b183c0e40d441140c0c00706001e14103052204450183c81c41c40f04030102042101c4940d00d4000001040d01c3c1c2c019a20050038120100800003100e2600c84c9010101c0d0303010020544a2085900401c00b0180041d000561b6949459800d441c0904c240c00860305a800a0284035a0640402c011060001107140038070100d030410080c040d5442c0002840c10602440340c003c10300558880d080110907103405060030f5040c82d5070b82405000c02c659845a0303000b06003041b002180b881c03442000c40ba030307401c0c081d103640d4a414070302802100c50140c5a800a0b0841c018014540c08854041c08898000c04070005500303060f50030044c0000840c0c4900203481c110340c1c0b04100c00c00c07092501180b072041d142003c8034a000c003903448540e960041c2c41034104040b1820f9600080195032006584102e0251581c03865210059603045d4050307649000100001c0c014001c07001e4200c820a401c1308006a06820b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 642397437 1250 642396187 642396211
    0x6091206090512071b032303041a0a1101061d0910051f08031306051b0109030302120f060a0311011101090f050d0807051206040207080d0b011206031a 66
    0x1d003612802d00704184001d01541d00c000016048083c401a100220b46040300000c09800c0c45145035a5202100407041201911102d449030102d0300c4d29081c4180c0300180718500842248400026140400b40d00100b028408604402c200220a440511901060b00c070f101031004c0d075144200e20038030a65840102000c00c14818882d00d0f00d81075040d8001c46020300514085406880e000740c904d07800c00741450700701060980c0709120f03040f11041c526007000200c0d13400741092991481900382c05944c04080c610702e0030305517017080e02d48400c15600d6401000c148200140039072143d21125040d1800355025148103900034103030442072000c11140c61408503091414100b0550010b181c034001c40c20754441040954000407580c00305014440705005041c81c3d00500c0c50a0202c07481c04c0b41c0060040c0c0140078205030390a1a00d8002015900e0756411076846a800c034052a842e80600300582d030203440c031808184c0c0001c5101c0c4180000700081d00480701587d900861200140c0103115401110350002804131041038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 642398687 1250 642397437 642397451
    0x31020409020d03120501080102180f0a03050d021c0e030d0e01020c0a0e09060c0c0a140a081210061e12060f0e041119030803130b0a090203120406091206 67
    0x1a441c8070034240c81034070940341e4444c6000280259002c5410584c891030b5264010480b42044034100e903072a800c42c00c01201c000314070f00c0440000c6409450160801032062054684042d665600012500009410212100c01d025104c4000312038103074040036042e030994004c0c1040c1040341d010b030400d144a69810301c1296024102d8900203186e4407642d50184e40ca10107031009100701317100180078180d4040760424201e80303403030b2107802c840790350380500400a01540c403417916100ca104c0040c4403811310603812100316601c41d01d9001aa201c588001e13601d00001451102002035140e0185480e0a518502c0d0300030a40b02c168405403c0d9440742c8510b01407031440ba683d500129190803030cc10b0000c00b800ca4220383d28a185450f00d03180c95400030b022403aa107d80c10803002101d6580042c2c0b5400140c80e4002001d9450382c45054164401c0c0c401740000074400d00441c402c00c040042181e1081e868503008804958004601101c101c1e5a0712aa006050000381c500205200d0b03400c0b5083c140c134190b0b1046034000781207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 642399937 1250 642398687 642398689
    0xb06120f0714040e120f0d060305060f06190b0d0b0d050712020a0b0304080d09060b031b1305011a0c070e040609020405091501090b0105091203030a053102040902 71
    0x104290401d80c141030356642c500d41182050310541484502000c0100720b411000364401840d405004040c412000300081c04041484a94101c6402194403400301c441506105076aa05060022900d035402160141d90840d0560301100005c5d08581101c0401460410b1101c03074040540317503070103035250070601c02c1c0783d141d0000d6020080440244028101400172558901c100031810500f44e001c08105c11003031051002149020302280c0e005426910005034041d264500f039006800116105980f600441c41803280c84d4165680004010404440543c6070396140c0003003030122442070241c0980b41e500e083c03504c400daa800d1401803030384250030011501c4555039405120b41c00a0101d804a40b1a078079015194218240f0307004103034200c44014087c0020246401c4022907522051042016080c0c07596a144d446074058422500c8281d03025003008290303011010300950300e600c240c0741400024a06070000d00ca10000d80c800103001d041260001c441c10312201c860310040300c40d554017646c0c000c2e0384420700001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 642401187 1250 642399937 642399943
    0x2010e030c01140f160c1104021902010f02070b01030f080403020d0c0503063706051c141c0f0504091d1b03030703050d06050d051c0c0b06120f 63
    0x1000340e0708800801c1c0c01c50ba9030540360700d00710003804e6078020b007800f44103001c4551441c00e0000d00503041c4d86041c0e070500c0703094281100c42c8100b100c0c245070840d00c002000c40e00701c8070300400110034180326002400111924103009003240300308040a000301c0100710060002811000394955500e004019035814a600c94000035208000180c08030b0340009240e10820081c141440142d610089400455100703c040002d100c8400894090039180c1c03510490709000e1008165000c403028040151a0316242c2c4043e0300400600a4510400e842400103540700c0c0b03080c103070006000c001c06051840c40c4032941c440d9108c1a02d440c00a8403014090101c1444041005040f9101c0c05103003682030240744c07009104082a50f0f0614000740e1084055200710003030351141351000021680d089a2500d040fa95600c071401d81a401080160003039940b200c1c80380b802a05004001400e0440340e103071030f60f569140001d01c02e001d40b1036019050004100c6400003002401d14584403417480c00b0614501c0596051654440c0c0c1182 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 642402437 1250 642401187 642401197
    0x7051c081005090c0409050a06180c12050103050c090c0708030403031b022107050c1801030201090e0714070f02090c191d040b0a09050f010e0705090108060f0102010e03 74
    0x1001030a40303000c221101c40007142000c000c28041d2681d5034a0704040743d1103c2d06100324001c3c20195921030020409108541e4460401000c00004401c20a100c1810301c074050305103682c010002900c03c0001810740700e130303600c82d05040300e41c004001e00440202d441030002c0380c140104114800e030002e02c82c0c980854010341c0210320840c82540c2c001800000c0c0182c1040c2c85210750740342011540601c645074110306590a44800740c6140d07121054031a4618a4003034604030030b010b04250003642042164901c52240050141a0b03031003620f9244003a902d800070340314140d01c22600a80002c80c02e034070030504109010000d200746401805481802d0900d0340101e558007030141e50b1a183d8a00000e0f841040d5480e41d00361500707034403592038240d4101c81c0900e04403005420b01070410b44213517a41d003040b00481e40c0b140010002010030040620942c0742110008140c143c09100740700894000000241504d8401c108a41203031505071180300c00750300c5020602c1444404456254190341d613402c80701c5450390003080a01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 642403687 1250 642402437 642402493
    0xc02160602011b09150c05070918150b0f1c06021b0105070f020c0108060f0916030513050c090a02071e0615080d0809010209211006080a0303090c0f08150601020706140705 75
    0x10031102038507c0c005c0f002104bd40b120807200c901c0d1030290480d0755580320480404490448855050302d85940e18221881000c0b0001404144000b440089540040103454804901c0d10001c01096070b40140030340790424198000c00050b00080c9a1010544c020000c081d00844c001d004404001e6034480402c41100003a100c40c1d0400110b9841201c1441d41406010b42c40048020700101e44582c0e40d4034256103142080c011480b07620340c080000c00b0004554160340201e80c000502209040400c0303401d0002403040001681c2903402c1c4881140f2020b1000300c0c41080b0307210f040041500c021401c0c070403564444046d02e9202155002c0000c246e0350350f0703088152440180e9592078900d80034540c13001c0900c1d140d14007146021540c1042030401581c000800c056a003242c040c140451601d00516041c81607510302d130082d8000030004080070501d443d000500b40c040103e190281c2c0031a850784030069035509054841c02002580160901030018101405841c9040c411811036144d881e83c01c038400c01e000030100340a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 642404937 1250 642403687 642403721
    0x1060c03021c1209061a0f1003180605041a0108031207050a030b060d0f0e06070f08040804030b15090708060312070f06091406010909020f01030c02160602011b09150c050709 76
    0x20014507040c40110803611b1034100e07811000700440d0f00108144220500611003459614030440004040340e801a9007031a40c003c1013000141f400d443c1c4864050003242d40b170154001400000300740c0c140c0010468200c011440000e0199a840c1e00b0100d0380e50340602a40410551a00204001511848083e103081c010354600410400580740700b110890f4000008603295501c0350040c4016503400c0940190310044902d00124999120700300750b00f0b58410303035000030824559201081903083c1402503c0c685039004551011164039107580c100d60011094500a0341a044225401c0c0810803000040c6034440c4106074500d02007039540c5480041b10300200f4140e03803900d410381d09120b1286003400b0722400340c180200c04104007030306900411250301c4600d14203814543e480358071480705c0e402004100e0101d142440403200e16911180c0c020b002e010b8102c41880c0300b501d070a010003162801131050350140c41171003201020784804035904951441106c101902d0b50300030a5008078030075400b80200c60b1428815010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 642406187 1250 642404937 642404951
    0xc0204060e0a111606180506010612050903070c060e011403180d02070b030609132001091a0d0c031821050a082404090605010e01060c03021c120906 65
    0x2c0340c0c003501c00f041401c0910820402c5540a01a403046007807201c150401030010b40c5000324502c203508115540c901803c6803080d200002020741e40031031a0320184070410380920040e1070707940002d07590b030040f40740c010326040002d4000e0200c0c0703100f4503050350100414500282c0c00c144640c1c10610a5000780c0b00b40c040306000c3c0e010340b012841f040080340c403603080507c02081828500304071000d80e4000a0011441030407400045000f0581c10740b001e0720110340080901071360303480b8001d01c0021004190307405030204602038000205c0c407402c1c0d01060001c03040390031400c0c905451a80108001d180d14030901d028103940301c0d404100540c0c800c0800348441e21482e010010454000407203c04086012070071005c205042000f445030580c0000b040342c2014441700524081000c6503010764a1040030f04171150401d01d061a10028000d160300054100c80c10301d640703007242c1c2e600c840c8100d03282c001c4200c2c0074001d41d1103214241d4103a40e41000c0c0000305410351805180c14800584403209440003043e05880c840d4403904 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 642407437 1250 642406187 642406201
    0x7030e010507050364080a050a02130602030706050c0a020a02090c1b160f0b0a0e0a0305010f1409060c070219030804090509190c06050a180b0c07141f0c0204060e 71
    0x400c0256017401c01c1d2142d00086140380006240840061150a04a86580104501342c40c107030141e4a1402d016860f00b1401d54803113500a5807504106419503916003050301003689543c0601c120360514105034041e080401c500d40901c03000e030300080d00d1040c1d02c040810003881c00d4070441c00e40703602102e105805000305c1e09580400d101e105849400a8000c000132000800c541d03042c6004075100e010050611011659030500007945075109584080c0c03803542482100302c0c1030310103a4805c0340b8214004891020a8594246603965034008443d8000304030401c100d0350016190002103150800303003540c50a8012034490740ca041043e0004c3d4802c0c5280d640b20024800c400340f043c0242084500360300b0003103040e1110394490510782102071007001c0031b0200009a07908101e200b0149800064112202089440c1d642e06034550303281d00600c2288428000c0400119054140c2c10102c010210000e0105035201c280805200000c549aa8030300c3c00e12100d4071200c00141c0751406440014040328481d00540e14000c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 642408687 1250 642407437 642407587
    0x204020706050103151a010e060c0f010f060e0f0601030915020708090406080a02130e0115031406160503010923040f050c010504050a090b030703140307030e0105070503 74
    0x2046121076042ca100103041803050490f41c06c05803c00d02e4103000a0040102144091040341c00f05c0080e0b0054040d07803207282e01c0540010741c00c0250080b0400290b42e4401c07486c50686002e50300d1821194411000c220f1540c400d07008140494060301242e010f00d40c401c03e0074422139009003801c40c0e0050002c40ea00d017552809104400c01084504042c225003200c039030005155100140503d0015a40d031181c1c82d0340c2c03104c05d501143c1056603848203036094946030700740344c40403900d14400e00d4a54481e000c0018901182a0b020101880e999112142140d00f4280b8090280c080c1e508899008000020303102102c00b0017240150082d4022204e4010320982c0741032a60410010880c0203040c05400c110400054903075100700030031512240c00001e10104450006410401507601c0500303540d0240c0303400c40b8580e06c044010501c0e507210b61503c074940d07030002d00155490f010348100501300d90018442c03205442104503007881a035007400181c40082145203810840d04001c030742ca0614207120610642d580315191 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 642409937 1250 642408687 642408713
    0x30c09032a0a06020a020405070504051c0c1509030f06090215070605010603021908091c120b0a180902012003040f0503010b240c030703030e0c100909180204020706050103 75
    0x6607108002d990401c1c0b00659121400c4800074003403562580060f44061080095a026000040c440000800d91070071070260610a00b505481140d513041d0700284500d00c41440b20340900c40c54460855181c6180caa14140c500c20f003200303403921b43c1c588071900010f0341c40909400750200308810003074580c0c025081800880b4016000b12050620410a0a4840903083c81c450201182c40c580305109a80703541540d4102040300002e240c2c841600000103924030780102c4800c24076560000200000d41040d406c10481d0002c6225550248080411181000d2403680001c3c6150340103041c01400c070034072060550b075030102c5c0c43c3e0000b2023034101240500c880d46060f0003031402081d0881c001e001010410300000c0d4408110285d5292255410b02c0d03d407031070b0b00c400090314240802d01d01900d48407149810050702074013805805540030f0180402481710b61901c0ca101341e8440c40103036168481241403854420042c4409445d0184000c034440c2d6140c0140da4500003041407034400c0307a0108095240d45440d040d28558 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 642411187 1250 642409937 642409939
    0x15060915021501051315080c130902150f090306090705040605010306050f120a06050907050a0803161401090501022d281b0302070314011e02030c09032a 67
    0x8450b2100c1150744410341c4050640718111110900111044501801050030005110f503824141400080c030910125000da12080250341088104a00084150849611140081d40080f407403030030003007003105000a400a403480b030921500e02200c1031f0003c0e291600845204060f0f030300001080c02181058000c140092000b801e0a11040341841c00044510303999052960044488001003c0008000c1026808590704510f082000703050140c0300030303101d00c81406504d024452030000050385c80c81c00421500030840b407542000c6121466582c1c00ac0105220354030803029034036401000702058082c030060890003030207000c007182a0365041e04602958611408240104d400f803041c14200c00c141c1342d0035007070310100c030210700c040c48503a04c000d8403160110350a800340c0c0b008a10003401019000a492001d03a401158101c1c3c0b480c10300b104c82070a0b213540810750011f041d23013644c240d5002c00443d00039540008002000505001701035020a1a108540801c0d00c40024140148074090080307920401000030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 642412437 1250 642411187 642411193
    0x9060a1a0307050d0201031b0302030f070e060d0c0918020c0f0c130e0102120a02090906191208041502061f0617042111011802010e010c061506091502 66
    0x910400103500c07540d4612501c4c0c002c0c903d80c10040d045a01c25480b190500b403c01b000c008044800c10b4000b40217400883d0804684039981d03020807691401030745000342101c0005e00031071600d4103003c10540542030b12150351003800441c3d0030101d0380c4520b81c00b02c0511054007004c010307255511903120600d1700e40142d600c41800d400c00100c485880d00c44010003082c050b10781d100031904045801c15a4020311403032000da07140504030700074462150001c3d0020722000c1804c27580790f2602c0e204e2808105000d40c03002c001c0310366040c1c045002c000510598a50a01450094001c00d09003542e40c9002015010f1400b454001a0030035000c200302d6550b60b18010300c100c21403440606a0f1307418104003601006c100100c1807001d200d014006001c2002c0500d0021003032049001d48003404210013800b804050798041110344650070114880351a001e8008050301064050b5035142d0850000300054896034441c01054030600c1d150888962980026040d0301c006000300d9690141741c80c5400a12a2078003112003175013003150 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 642413687 1250 642412437 642412481
    0x6090f010f14010e090c060307050a02060a0506131508030708040e0c090904060b12100516030b0a0303080603100c17010b120a0506010c1e06060b1c0b01051209060a 72
    0x441480c0d06055034040700d0a001d854175503d03002c51520100c80e0b080340e8815000810040c2e01c0f40d2081c0942005d5480e5021542036480702c0041e601a0752044030300a07000340000820106e02803983c0c0200001041055606c8500d94440d042d080c11031344180703401c0d248030000060400080e0161100190f0201e1040c4c10760307041c20080380000f0b2015901030030280000c5e445550000701695507100b003d040706210f40480b4440c945140d540f00c0588400c0781c081c80d00d210340b00081d14542d40a4081c2e00d214040081c61682180c3c07c40c1d909403041d21025001940500c0b5030702c801c0b10b00407a944030b410290340d850317100c4181034040c0100305081d00310305030030100c0c81c0700040c803e003035160014401194115403d5503000c91607998010040b00c8205210300003904025000aa502035000100d0380908554003501c01484450b071079805010041c0715044513800500c50090f80756200c514107521284030f090b0140f401c2490b2043e20381282046800646880710a508280140080c0c00d549200d1a03050f00f990660f00d02900c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 642414937 1250 642413687 642413711
    0x80702101b02040213210b06040e10020f222105030327100204080d030207080406120b090a0f0c0816050726070611030f0a09020a050306090f010f 64
    0x90408420700a00840d0080b81040a5a80c95078440001e46000c001900d0482100907a010340000d04c40c00c265003818413240451034604050107441d003c03400140050841c00412207481e8000d42c0407010000e00010144012001803038400080c000000301c015200c81090706111100c02c5401c1c00600303202c070b0114100074081c00210702005495000002540d03000c8681c001d56050700b1061070f45a10f40741e0b540100e0010f02d6205030a82e01401c1542da25108031400e2002c0c01070240e08038814010040c15400301071000704030092240000f1120060300c0500483e40c4441200800c0700700d8000d482c9602602e4031035003051440e03100d62040c20180702072894100121b04111b2600300d92811150340483c1045000182c05040c4005c1c02200003007284401d0182600400d10355202ca6035800c042c90807503070079051110304c011441181085e0785c09248240100c0c0c85030b4540d0200c1000800404808980105030102c000685580901c08144034100000c0948241411440d080e42146d40100c4614117030341ca80b0440d0006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 642416187 1250 642414937 642414977
    0x703030f15090c200a0303060b0a02060c0d0608010c030b030c0406050a12030e0904060c0f08100b031302030a2a030803041211010e2b140a05041208070210 68
    0x100c07001e1640c0003560a0f425001265000710252880e10518421400c080311342c0400141102020b01947d41005402d48816001d940741c400d041c10a40107030700c490081401e04480c07a000b01a0407044140c00141c02e95503890300c0d425641388240b8280402e40c1c07a11100044d080501c6a07102584044404014185c1054000740942255011790161840d18015107020140580101c1c2c03010700005202503880c1c607052a00708080c000010308880081c1e09551700c0105c940c02180042c0c090001c03000719401c20b43c24440441211b40001b0010716601d03c2c41480a0090b031021701880d0210f60003021001401102860158114038040f0703480070381c00e2419107007080412505800d407034110750300244501513910618021640d10245800c8107000d1751a001c5c003640b8510000500387e0303030258511382c54803500248003880030442c003074001043c000c83c04858140280c1c2841c2c03002041181d0031402e00f14189500c03035040e600c800340d03020411182030400240f010150301c2e201c2681841d0010710303d0150a0318500b102d10140d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 642417437 1250 642416187 642416189
    0xa2a0b060108042d0c030c2606060405041509051e0c0d0b040c030b01090506041404120c02121006030c0806091f020424030c0212040e2205030703030f15 67
    0x15100c544c80460800ca00c41507a81040708580140d030000420382c40381081d00d17082009100f503440040d0003411000324510225801d22910030071a000d00115501e441c04d00000c0c000080046a0441e00e6001c50311142201c4d2181c2c000d000d00410082c02aa03105c480350a6488a003185826003682c41500c024201d40d8030700e500c400e1540d9021650a580e915a0f00d44810041d501d90802400b51003240300215200c40241d002a22400007200c0078044a102c0d070191081901050703070050103030f000c00401032840a0207868040481c62003c1d203040c42d240813041c4c040303052031003100b92035440c29220354081090003400b206600241260001608180c101550015075a1050440e03141c80310004059041095031242e056900400f0a80c4c62845410000500750140704041403044000c40d142243c0e20b10078610001c1c00349a600203c4800e1440c190500404883d1208001d0050452900010500343c06e00d007804001100385225800440c0c8034405890050181e80084883c048400c0c94142d03106140076804007030b10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 642418687 1250 642417437 642417473
    0x1060e24060d09050a0302060a090c050913060e010b090604020a02030909090a05010f05071709060a1a12070312051c0908221502010209030c060a2a0b06010804 70
    0x19008085400861028040d041090242e01e1802c01c201061101c0440c800203120300c00e42c03d9070340d581c0c1c4184942c0100c900080c000303807452201401c03d01a40c02e0950280340c02c0b40740460140a060381c503580318000d43c2c085140c0d070020781e51903160f281842d0420002550f0420300803a41503091803030b044070084d5240a003040e46440307800da1401181452000b070240300481d641010080c008072849841070009800265a0f40d00041c100072171920304844840b02e014080c8020130080e04d12910f8081d600d5015096150950300700502c50420144c09070b5902c401c618100c000320300a81901d600c1c50800014600d44001d00605020042200340e0214046032480307483e60350650000501d650f2141881c0c4810700480c4d02e0401440c0600407000c10f41c8115032510000ca6000c2050392103807101c8030404030700340e02500c15801c1c1c0550180c55408840d16000000d004424264504595011041d00700303a4024490b1001030781154080340e483e0024450805080340d48603600b82400049420190317220000c04d28413250300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 642419937 1250 642418687 642418741
    0x121006030e15130c23090106030b0d0303020a0e120703050d02030c0c090a3306111902360f06090a0509120a03020414040603080403080d0b060c01050901060e 69
    0x7000c1044401e9034200040c000001c000c0c10303075003482000c00042017500f9041c82c0c07007010018000901c1030f02c2405102c00c00d250250070302e04095a660740030750117500030700c1102080c40900505c0014075150301c00a0111f000c000701c010100311b80f80d4100b507420490138032102c0301103400812910081a10019411607007000a03602000203030b56200749980140149003080000c0303000c1c00118160600f2280b4080c0084124a026000c041e0f550001615500205582c2d00b525420001c3e201c58402c0c0300c070b4150310b40e2a0000d002c000c148244d5022850325848061424101c6c50190102c0e4250a150041c40c590701080d00034542c0c1d80317400c2810001d85254002005420000e48a4000400941040c040000b180b002440243d0b01c501c00b40c00050040d4105020301050306503210544011454203004c0d00341101d801034145172605040d5240ca1900d40c0c03000300908206900c80101300550348480000341800089580001703424140901c1080c00c0d00d4075580105401c4808405212043d0070300810300d0803d078102851 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 642421187 1250 642419937 642419971
    0xd1809021e0a02191406070201021e070f020405010e150a0614131a0909090303060d080705030c07090609420315020a080c0a0c120203121006030e15 65
    0x32481d11009200c101d003c01d180700710130030400c100c4c8040307291011110003e03905caa660b01c0c50100d08074003c803d0f14018003a00d02da0128000c5010318001c00e1041d004440400718a8810f4000c18280c450a900c41040c3e40d079904c2c1001a001d2000b130304071034919012110440b4203803030886c00401c100038401200c0042e01001515216050750626200d00030301c1103019101d941050342d50360844a4000366121030050810000040e0483c1c1c01004581c0700d8600105401001a40340e155003a0b40d03009644100ca46220800c1030503c0c940c000c0040c54001c0c1001500891140d0420102c1c00a0380c01c008031160421440304400c2d20083c480230f8031928800380e1030100804502040034030f1004000a584040e009800c0c90955070b8003c42c0b160000c00f900c112645500c8003a803141c403c20722861184800000c001011001144002074810310420445c0320b961044909144419200710440e10040c0c40305000c0800e100010050103815001d4064840818805400d08009104411213005c4009201585104d130f0146 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 642422437 1250 642421187 642421207
    0x2120a0e011b0c0b0d09140c03010c0206250c0c0f060f0c0309050603090312090105180a03020a062003070c0312060b070b1012060605090f07021b04020c0d1809021e 72
    0x30004001b0f6802001c141907074030f40500460348418441032254081d500f48010b1a05003400056020300919080030031a03c10000f140503026865802405034041000502d03102000c00c4082c03600f10082d040501c1a002e016160000c06080d02c0309201980c4140181d000f64100840d81061203d03003102e0090310841d543e5600c00321a241184942e400c6804804c5404040c400a00300540c041c500c10001204105034000c0d81400d4181c2d00d0140036401030042e17014200aa001540541108564551000602c00c000300e01d02ca403400aa0003c80d0040001844480d04400b0701d607100000072031500e0449800c011843c18000984454451000302402c110300480c0800d0411030000c0b80300f0014008540031103154030003841d001000c1e102e02d100c0c0c0b234070039072804010400e4450000489070082c0f105800070b14044210801f07004110780b004020301e50080d401e00241107070340d205000800402c401555001c03859030f02010340d29484003d0342c1194028038070501106400d030400b05460342010f410240d026884801500c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 642423687 1250 642422437 642422441
    0x80f040203030c190212010209030706030207020301060e042603071b0219030c030c0e0c1207021501091508060402060912100f050a140f0a0c02120a0e011b0c0b0d 71
    0x2c0d000c1845104012604c0e1008a41d4035220030010300c00c40c1d80c0300d07600800c107114900381c0c0198854035901d500025000c00a42d800b982c01846a00c1c405800411030f10303951200d030700f1030620445083e2146d04440e0014090314550110b20b10300340380c0018069046003011407004020418400094001c420402104015907950201b2049140404140c61003455201d291407210301e5094030089444000340a03020524a829421313035480703141c43c807658034140b100d9000d18226070400a0045c100b98000c038030300180b204540c000c04074041c0c0341d19070b4040380b0b1104245110489082c950b02c01146900104144001640d882080300c02500b4203d84c0d402981a0b003500107820003c00c607941086182c5450f240f44c0c600039054001038811580d00c00b0400001480841000f1800300c12611185601c40d0440040c26003400355021482c02d081c1c0d803040754410a41d0407454406039222183c802c0100f410045546581d69002900121008403020030142e05c0300d10b41c2d0b074400d00c19000e009400d0390b900b011442d41e25821140d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 642424937 1250 642423687 642423697
    0x30a08032e1e0b1812030c0a11120109060e0f01060b1e0f0a02010b010f020303040b0109020d090b041a090d0f050a11240c040b030109020f0c10050906010501030903080f04020303 78
    0x40ca40720383d9113a16104808401d0090740e040103003d4540016100c0c8044030210556041c1150b0001526080e0681c0d600c005841030300c00034041e40030883c5c91340c03442c2e4035209124808541e0b100da08002107044030700c40c10310b180c06050681c00c01140c0c104081072041d002d002042e41c0c0423400c561070550f203401486a10500b9800703441418000c9100204101e07118a5054000c807800e10000c1c0c0740c1058440c2500e00481c1c0364030040354007a000c54000001009810300e5540100500d0b030030410000740d0300c860359035400500c01c010340c0e05443c0604d080ba414043c0a46606000f504210010020300ea81c05a10300b010304460380c80f81d09403041c41808101d250155004034240003e030000c800c280c0d511110b400100d964140504584082190302040002d00b2202e000f8048034152801910004c4c103513840c1c80361203070107948040615800301030248403c0c01402d004225407416080034038008280c61511182e008d01d01941640328170b04142c00c11041201080d00000c4882d040050b05806070b03080d50b190f001091451143c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 642426187 1250 642424937 642424949
    0x909090507170a0c031e1a07140a0f0c060f110706050c03090613290702010c08011d060301060b0c070303030b0f181e090d120c1e0c02030a08032e1e 65
    0x10f005d07603800380c51618511071f501c2030046864410030104038401200440c0a90750044001c100368030090980680214194034030309110f0b034030200e03015a000529209a818001e101007001501140e2001080104e014071035009425400c600e0440c41d0143d40f140e40c800c0040c0a030980e040c900b0317043e0010300040010403011040b140e10b40410a0700c10320544c00003540102da00d070006519082035000c010748034013030850413100d4031000c0344980c000d54400303151040e4010300340c03d926658400000601030302c810080c1c201c0f070140c0f4019100141c41c5007000307000e0316000300303400388070f8200007000c20702c6d80e80c680b4820400c8810403c0104000d9582540c040ca040e0450141803018168600400c459403800282009c01d04c040303950b0348121000185d08000540302a031084da00412440e44a111000c03d918440300c1c03042c080307440d00e0800701300c9030740119090681304802591403138400400c12007088030448018605503022900c1d01c00c1c1c901144a2110803500e180510344a03100340b40391008401240c801103401402d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 642427437 1250 642426187 642426203
    0x120b0a12140d0c0302011409100f0b12071502030906120901020c100204050a05010809072916031704050a020609030102070c2903070f05030402010909090507170a0c031e 74
    0x140310b0054490524004110010740c2420662481c3d04081d2140b40d0164040c3d070028031804c10f040c0003100c050412801e41502440e91881c204000da17981000d005880a00f0303002500646040c043c4601d4945020000c0d4000d648c010014111551280f400b110700d540511421007070381d51a200d031107a01a00c900079102c20302d44170344c8442c00c80441040c0d0050003150005c60300c00d001582c1c1c1d84015a050700003261801050f401520082003c0551000e00741600d40e24403090149082100c443c0045a0300030a150700c040350907290100003015001221155203a065240781c0e1034600c0c16036601a650314100400078050040880c0c40c2e00782d91400d405844040354000501011161590380c02d1441045402e02e00f29820600030340d10403e60b403490111380c041c40f196598000c040b1801041982c03c2e0f800684201c0c1080404070740041d820041d0311400f84c0a510820203010369910b003020010303d11204042c40c502c00d0b0032503000400014100c1640742d0413a90321802e2a000c41c50240340c5545a1548403074058207110b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 642428687 1250 642427437 642427453
    0xf0c16020d031101050a06140f010e12060a0c08130f1e08090414070c120e0904080c0106061107180e01140403080c04061403040f170406120b0a1214 65
    0x1a0800c912042503501c3c0d4001300b00b640d84919843c400c4d00c256100742c1486411412810305207043c00d2501c401881c0060502032000001e10300425100e07a01500039844a40080040c002c1c445032a0069440402903403a04000604007540d02041116400b80010861041500b003003041107480f44940710f003052040c0101d00006607a0620110301c1c2e10110081d446513103080d0185400d65411007006000300c103260341e4201c50f1503460ba80c03d0114000e0029100600c10700a107014051303554400c15070321451141d207203140c440c00300306007280c2543c506400000038001a0011602040c0c40080c128044038032019202a803481c001590000030181c03050380754105e508040039a0060a02d124040d070203248030303541d081d185644840441320240200d0080d500007940f14080c3c049640040f20145412a000e40c01da41122074241c0c0d240c2c0445607501485000c40300c0042410064647c0214441a2444e14880244449840a000180d003c801405200d000c041c0040071681404a0b0400400c204400c03501110014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 642429937 1250 642428687 642428693
    0x100b04290307090303090806010e062b03050417120a050a0e19060206010b040b0d021c0c081e010b030f040c0312020102030f0c0c070506031305011503050708060f0c16020d 75
    0x801c1a13000580c04140ca05a00203400702c0d00160840c1200d01c20052808543c50b03010412844400c00c031407100541c1c0c803c1f81ca1510304100503032051181840b1343c86180d950b528085800e0034241d00c11000c40104e03081484050150741d85101111040101d030300e042035442c2050b020030b6517007a280d00726440e004a4140c00346040020401d00a00070b48109400b102e0701e9a03038649620b0064400c81c0200041c20b44180041c400011181d009004c00286540490f4400440114801e04403200004400000303520941406550302c07101c0c0c85401903801418403108198144503420b000c1c1e10000d040030306040c0200307000400348100c0c42202405154032203000780300c800000e20000e010b0341044d2001c4000e055079201003146c951a450442e1889038004019044003032518041040c3d94000901ba00698061021810f0010b6003c0c4202c2a5601c0d0a108585100b4214201540350011075041401154491018014940c80b0294030030361040a403551141e4441030000782c905c400950303c070002d4002c0d40c045591010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 642431187 1250 642429937 642429947
    0x412020f03161b030f021e120a060c17040f0302030f0d05070201060501210c050f0c010603150507090b0a03090b010e04140c0a0302040f090b1806100b04290307 70
    0x11042c025080c01d004858801620031500200b072100178201c507641000c503001420003211050000c014004c108083d9143c65001c02c07241090340c0441003582e04401c55000800c01c1504c40c0c0c4400729081d15054039a440c03520855816000d000d88040c00c440740c10807500c810107101304125000c14080c030f22000e40700c0c0e49441402c005458142c400001550a140000c5501d501c20030360b8240d4203c0100d0b1300c81e0142d4045503000700a01c403080b8031b0070410504000141240c5440c00060043c0c00300e0600001d541451409d04901650b003040341202e000f0f0804d0b051014990380b00405906035044151541d039200301400040e0300621a6900c000c00c2d1074006c200000d98440d010f0b00c030030704c01c81c06251002d1103e040d50206136142ca8844031b2481d4072820000091000d030400d0b90100c1c5054100303001c001085c011980b2202c5114408641460291048050420403030b0421301c000c6400003034034045245203600b4443c0b405114021409017508a148081120002d2001419403584c80b00b000c44200355282411080108 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 642432437 1250 642431187 642431227
    0x1120f0609020c0f1902090106050d090203010204062f1f020d060e07081303020316030318050a14070509061302070b270c06092404140a0605030702060412020f03 71
    0x4441d00990765005c0d10700890b214402d110700e500a0900308030740c3c03c0810a0b1696003191b03451010580e501c81c0c0c4140103031070901c010006080162244140308411507001d0000302006c81144278040c5101c51212116880060034003145078019125948c0f0750b51454010009000c1d25100701510360600400046100007583c005d80100c0b0203071348101c000e5607102003800220001841c01001a4000c00401c0810480e42a4845103d072103407401140c0010000840d07540c007501078506540c41d402502000040200034030b801000a01c0c004d0103006100e11300f10020b01200c1d4014061802400c11005c44070f44a074940d4100c51655500c03440720045428980c0c040c5540707105108100140034411200320740713802e0300042ca500e01118000c00262411170700000f40540d98801481c0f940d600c50788083c250803804940c1000e44003800035001404040301031a4100080d00240fa0b1011090080c1001400307002c075400f00b01c02d81d201e504100c640581c008032040032032820b0b10b8520341c0f240c0c84c040440e01425007212224005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 642433687 1250 642432437 642432463
    0x2031014011401020607270803070c0e1f03111c0302060103030806062505030415030c170906040f080903071202040b12060a050c0904020301080d090b0901120f0609020c 74
    0x12208080d0306005aa480b034040d0382c03140104440700070340c01554440c48840100c0c0001074451405d1641d8440341b2520311713009190102c901807010356091241800070b010031503003780c0c0045500403484003215107a00f019031034000039184021246400c461500c80c140e60400c2c0025031740e007008103640c2905000391035800a000441c00515191702282c16441c00c00166001e11002c61907039086403d0702104400f0940b04444c0172541e42c001804002509445000d1050280342103880204a82d00c40d914000d00c00f0b01402041c0440005440a200c14200c001414a602030381c03040d031031000510036003484401d9005481d54503600d803190003000b14010700885c140526103442540c080c4102e8a110042107503488026408044540c00b03003001540091584d000310f500001c035954514074180c0740c0303804501a6442604003541c140d00c42d540701711182d80c4c014031400c0140701100d0200c0c20050f41900082981c0f1414011702034141c0c5401215803135485560000e402030014003002c45d500e800c03004405481c0e04003020301c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 642434937 1250 642433687 642433709
    0x20106050906060a08040501090206030f04030912031e09051002150a060815070c0f0807050615030c060903030909042604050303122707080d0c05030702010c0203101401 74
    0x26850500c0718905014034001000c0c41d007042c3c1c5104044a8040c1c0080c020707510b035900c5044400161f2690030065004410307442d402c01c104c1c44c00e818090b02d4501280d22140d0401101e080e65008640d000d070070704c00e6199000f0a548100400b0302d10446003000380740c20040d0300c410700c0214040c07100e40006240e00d582a05840361640395a800700c0160072100c55215000c500d401000d860609000c50b500c11603440010f60401c0d54020031139031690100c021050350215141074000030b003c414050f081004a40c440b862401c245500e542e00004203032a40c0310400c0e00c5000b9040070590800ca641c060081d04d004000c003400d8903410b0714241c1440740301c400c90b0340414070764500c90401c1c401c000c102040403582070341c1d170146c021890100c80d0341a00700c4406004101d401c12903040140000c14045a110703166001000600402400342401c00382800c00d41107005c40000e010303802b038200700020350100903100c2c0340d42c0909003d80500c00600200b81400300c1d142d0303454481403800346884400c0c41034019940c1618100460 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 642436187 1250 642434937 642434939
    0x10f18060305070b030613060e0f091b01080921070606060503010e0712021c0b010f0c020a03290a0c0311030f0a0504140307150c0203040e01060327050d020106 70
    0x4090120380103800041c210f0781144a0a03c4481d100c40c0046412420140207061820404a0000c00302e0b200c0e600041b4a0032389607020b2080c00c03c0050f281540001010014181441c100106801c25020102c0520f0501400d0310028850b49030521400e41904a6540901c800e100c502c0003ca10130703448007000700c2ea6540342c4400410300c02d1040040e039041c0c403110030480100740c40300e0405485086808400b50074083c1c00b00591844084901c0300c24140c03003100c4801103540080000007410110b070071240c0404100c00980742074056660849070b13104481d041b044d43c00441903280d4911480000340200b1001b00008482440121041c9600c20403441680da5020052625000c038180310b20310003030b1400000e500c035100200b600c070106d607409035402c0340c4956014180d003244024407a0442d003160302e0558101c012604030100112950041080804a504c00f840c0340500b488205009540180101000c040d614041c2c00c05103140010101c0c000b031001002c00b480c1c000e06107403c95072041c03107061000055003483c00c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 642437437 1250 642436187 642436229
    0x110a0804020907051306030b1512240a03081b070f080d0219030e18070914090708040b150d0c080c040603120507020a18021207020303161b0605010f 65
    0x400c4e0b40300184170a910305592458010101c000c1c1c800741400700e6004e81d003040d510001c0d0070443e0007082c0036804072513030304850300e09402414900c200902c80f6282035241408008007556034070940c1e2007a254451100c58880c2642800390f905c081080002d0001e51040b0640854440480c1c0600b4007225003d10480d2100015507004a80740d0b000c06007201c2001c0b44550080c40045d0154001c0c0502c000050550101e54554190503049404191016804144004024003004109824001d43c41c0400d40f040310807802c00c2803004100352001403000e06403448000124601c9a2440b444081e82080244903598102c02c504084459200c40d200d101114883c551454006042601071501100c0d000540702071101d54080d800d0790141d1203a01d0407a070102019002056410b00400c2d4500d0704070700c100c001600e9556000d2a03000c00d520280c41c00b001d640c010301c100450080000b8120703110038828900300c3c080f05609010212480c580d51740c0101101e05003000410000e4100e042e070740031548540102a00312a100c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 642438687 1250 642437437 642437447
    0x6030f241806082d010c02150910061401020c01051e22090209040501060216030303110903010608070e1003080403020f0a05060705060f010f050d0b0c07050708070914010506070b0406110a0804020907 87
    0x501c1c1c4007d6013112070181c00191342c1c101041c0d8029025400c0e1030074a0b107689003580881e5400c0c0c00c101c584006186200303684d0f50f81002040c0c400442828803600c1c20902d11124001210080d1089401d07c3c00024403059007140c042c1a0f00034001c01150348022107440d4280c02010b50000d0340403d00482c07500e0000101d2074030003e41d100d80304410144550b015410354504801034122a148101d022030104403105807500c091040c940280708150151480358244140c10311100d030060603000804250ba1000d201085124040ba82169411150711000050040c04110883c6469010030352108021480d103040c040081903440c46828080803e0850b03030f80350070800121081c240281d50300007092180d4003001401c0d0486441c4c010020501e0705051000f165200d600e001c440750440d0101d07400203a0108504e401c94002d1940c84225454958059810580400d41e640110707203000d048102804045810701007213030b000b981051800d580480e03580c000b40d0806450310340d054800724092011000001d521034450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 642439937 1250 642438687 642438701
    0x12040513022508130b0304170a090b090d06020d02091201062102040e060711010c0305061f0309080d0b01120c020d0f02150106030f241806082d01 64
    0x18041401c5403018502c0c0c50208044458086404500402240300100e0824202100410004902039a20300d000d1800000c04c0588125481f4076407400e02c1a80e500b0b0760000c3c009001d40384800c55250300e0300004000985c40c01d0625030090506440068030810b10f00d044c0e00201004081503c3c1c1078500400910700d00c0c00c03160a03201d9603000c071300e100b14004242d00b107103940c82c0c480c140002d0002c1604503040c2011400d0a100b95140f0022641c1c0300111300300340341d0a000305c0081d107040b418108580e24181002ca0a1850b040701c506d9058800001802105030013544603002054112000035107031247d10260340b004008806030240800d90300090324003405101c0c000c1d070140c202c10b41d002c0c1030101d030038001c1515181c58207640c103029802400b0000c900c03907103034400c2c0c5402010075981c007090101b039818020088500c1c80c0c0000c01c429800107601143c40c40b01112010407100040d500b80c01004d11401c02d517005108640041006004a1a4550803100103083c84641d40c1d0303040791840070a0b074104128a00301c0d07100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 642441187 1250 642439937 642439957
    0x6020d08280605102d0206040f06021c0f06050a0321050d09080405010806090402210c0d0f0c0b03040f08070212102406080c18031204051302 62
    0xc400c40101c1514100340207416100c0c0d400000c5041070710f9100092007480720410690002d52440415004643d500098001d40514104440e100ca0740f400341c0213407903103001080a030a4012400014042098036811151884c1c0700e980f1100040300c80c80c1e002409498031019a81c0d100e802d00340c0207d46454003c1844080701e602c0b08140701d03043c10042a02001c03000001c160003d02c0410300c8100700403141c90103488503041c030804415683c0c50901c00003410000740074042d00d016011003000c1100580b00d090360088080d1039034441340c0032121041005403410b500141000d8201c07060603001d80820100e44034072242d05109201880d0090340340d1040010714001128042c2001108410880c085249800106000350010b81344501511300302403c00d181011202c0e40d26019039891410150788010780503201c6400e0355121445040038507060008048850203400d1103031048000440c4110401c890080300000d800103026600800c41c50340b9aa0788682242c403603503016065007210b000345030405d80700300c48031451 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 642442437 1250 642441187 642441211
    0x8060615070b0a05011e030809130b060a0c110d031e0c0b010b07060506060a052502090705130914040b060a0305060a0e0c0405010807060507052506020d08 68
    0x6210410462512080390820419110400410011800088440f0712840309003c02048a502d02a2600340e4001c0c0ea050070605001c82c007200344005001d6038115110f000b4211480007107204018001d500030172401c00c80300d5000d078001683c082c115030042c52038030040b800385d10740e0044220f280d400c0c0041d580c80d800300103001900e01d808899002c0a0510036144d10011440c10032040c1a85a465880d0250b00780c0200703140040c00b003410010081f00340129a8800d0040d140036040c00840701011300035002c0c4e80701c0040380800000754460524038042d0342054040d0001c0003102d2a0070b145902605a071702540c0480015121064003048040d218082c000981850340107290f07481d0340e80e4a038003004000150000390b00c6041d5030300001c0401c1d8100314060091400ca2000604480c460301014035080b100c0e01c081d40954140030042001520200700441116003d042c0349503100f4291030168100400034011220101c5102c00560342055600b14180613900c0940885901d10a4880305403a803040c22148000e07211 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 642443687 1250 642442437 642442441
    0x100f060f080f1e090304050a0306060302090a140a0e0309060d020c0601061b0312090c03080301210b06090c16063c022a0114011a03060d0309050d0b090111040806 71
    0x121900136409030b226001c0d83d041ca516840040d0380402194020b69110b622103170244190302c2c0900d1100c0d004000c0c0352041158400140c0d80700b0720303143d00400e210300d030650f00c90f41442102c0f400e104841600c0c10041295640d00032464598000b5080300ca40c900484c8034447c0042100360196054000c60310310020884444070f001d071b070111103000c240c0c010040c00c20b807a825400c00244505000401840c4100d0b0003640340d604280001e003c01116040c50740c1035661107244100411503c0300b03007a4201e0030940d036026080d40e03005408241480f0303100443c2094402103030349200784841940305000702c40301e0b40540c00705c0054040d201d1100d000ba18442410b09030040d05a40f407032000a40c0285820800200072103803e80c5c103401514003050441d0300604d1665100c03950840307550707070400903540075043c02d003a00001851405201030f0507000007004107004840c1022000d0605002d030703440c40d004220041100c0201103071440e0a9580210950b070381c003147d40c01d0003124800c4078000410399041d901450001c100175 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 642444937 1250 642443687 642443731
    0xd051b041d060d122304062a0212070306050109020a1b0507050409080306040506030d09150e0405070f030c08130f0204150807081603030f0305100f060f080f 69
    0x7090251041d94000d400a40d10301c00109130001c401c41c10725a544030110703a020002107291800740c1010303c00c0d50314002080103100c102e030040c80c8045448403911030406082c07d805401c20b401c1e0003410010f0f520240d0f40042d58801d60340050000162446854188107a9a0b24681c54059003c2c0300c038100c02180119004c1740300c010320281c5010045000c0c078200c420035a0788101003412101444416142a07500004000b0241418028140c2100041c0e00401004204010041081403940540e8a490300041030302080366126008030b5650540041c401c01c16030400030b01c050030344070705280d4000100782000b80300b440160107a041948904801e05070000c0c1c044466507a0b0118295030034041360b01a588403d880c0480c440848000050724110008000c01d5040200151525400b070400e040820380f41c40003030000941c0102040d44600d510f05001c00c0c1c40c1c59118101c031100e007d6800c28805e240d16024002500da0740462111402c980c41c5d00c40c170341a41c6402c2010144454200c2d610b40c0e010443c00c5040f02d003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 642446043 1106 642444937 642444989
    0xc0b07120f0b091501020a080a09030219140f090105120109050109050607090b0408031813320c300108030a08150d260d051b04 56
    0x1040703c2900002d6840c04101c10041c00c5074804a00010740c540904410741c0950350080081c401c5c2ca84006c0900030040321441088900c4c0b3b581e20701c0d44d02c0e5040450b40701280301c07009051744406a0070602806401c1020491413162076613520407e00c0451030a00c1540c00f090b01c124081c20242c00c150744024071800c041d4100018484042004100e80310380002100d204086050f8106416020f40d0001140310015501c645410b90404400010300044603200182c5170000300c0c1001207030b08018100054400c402c44200d00702c0501000700351221344000100040c0c11101204050580e014150800e142a100b80e0110384203070320204000c4c00d80380e000f0380e1190380104910b54018640d0f005400061030a119803602404903948100d0300202c0145070042045682d20000281c5c4d82c603014036502d40010301c01115180c0c4048040a00000c131140008202c8007251401c026030040d940360044140b40b = true := by decide +kernel

theorem cover : BRFrame.Cov 642266187 642446043 := by
  have h0 := BRFrame.cov_init 642266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 642266187 ≤ n) (h2 : n < 642446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
