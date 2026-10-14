-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0926
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:59:59.031085+00:00
-- url     : https://prove2.me/submissions/897e9e99-f6dd-4a05-86e0-616d9d25b01c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 166366906 ≤ n < 166546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 166368156 1250 166366906 166366919
    0x1a04020a0203070b0f0a0506010c050622020324090d0f211b020c03190209090106031203020d0c05090d170c07140414041e03051204061401050910030b10 67
    0x10340b035024844904658069186c406849002d032180240620304014503140c03400002034000a1490700040d8801d10301e10964200c40c1c0e00840e4880800780651302d4410351803420052102304a804000100c001c0d440843d5036280900305a940945200d00070010700780d0400060414891541c8030a90070f901c0b10209000b1003c28072907026907600034420814120300d210303c14286a0100408113120070290050616001c001a150f40c2000344120040c2c05100b003200020b08903d800c3d030003400503540c421103141c2c000400920040080d0007403003000103001e240c07402400c1c0460058040d0340d031444e40104040b90b8020701d0b03500d0f440740303154101011403805414003030301d000e1400901c12100644115550340c0c9030f60310004100710658207a2140c4503a801c14200c10b000c08a40d900c1c8000396101501101ea80d885006840c0c1144c1d079220384000d00800300648020b120802c400da400c01481e03c1c2075580742d1b094591301e0b08200560800d040c0c1d00c00d140d1026142e400c10011307982d5034900340c1c440b8642d61501d11a0f0b81e50413 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 166369406 1250 166368156 166368173
    0x3060616050c031b030a03080916080601080c0103111603090302041a010912020d02091f0e040212011e1d01062904030506180a0203121306031a04020a020307 69
    0x100d040300c242c2c000c045400c0b1682810807125031500d010a40764510b0403031040110703488032413070140941006188030004051040402980040c10a0b244c112840507954402c00c0b40c0310748080c001e0714180d003d51814801c841d031090043e04850005484150b280208541c44080040c0d20711000702c00344040100c0020260351070307101e6141c0405200130300a441510100c001815103000d5000100008140d24420001d07031100540741500940c142c84c0c0c502c0c00d45400700d03108040c1400d00322030005840fa001e00450800c150a243c030f80120301c01d03104004440c115850302400e0b5440001740c5210810090214070303080350140c00580c4e1301a01d10341922a0320014920260940d1002c3e0083c040a080300b8801e210a96090a500318114001c0c1c9222428241140c0e211500c0e03460190100b030462107054800e034107084040c0015a4030726401400c807945005a00c0710700b2102d41208000b2000d040d005100092443d02a008c0c42c0300202c02414038603e074065082c100700080d00007040c100114881030024500190842 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 166370656 1250 166369406 166369447
    0xf0f020a0b0f101205070302040902120609101407020c0f15040f062a080306060f071104051602071203090810020408100605010503130203031c0902040c14040308030606 74
    0x84034429071519051100749483c00b2a07074419a0340002d07402c1c10901064011840d103056039030407540441c00c11030350f000003840148a500602c416002d40801e10040384070000f41000b19030240343c07084c410ba42c400740b24003400000c1101d46802680040040b500c1501d8902c4146108120050030322940c0004004000070325001600702e07904224085c07200f400500e403c8900c800d440140502283c2c07200542104010a0b40d8019000030110000071020030900d54803a819583c0009030a0030643d255809402d0801c005058210498080e510700340104118503490420400704203c9900242070a5107808003060b030b51340d00203000b60b081100007800460f1002042c03003040c407045580c2d130340540c0b5542000340c1d071424a0b004982110410380381c05010030941c1d801c607041d65440b03000c005200303000f00c0d020f0001c80c2c2540316150124600c82003020b00c140c402c110756484480003e000f51002c00c810300c1d00030010380d42d0085200c003194252034140002c1000610810044d58042c0024081a00b8102a9400500040602c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 166371906 1250 166370656 166370671
    0xa080c0d021201030209090a230c04180605090106080a080906070209130c06030501062a02040510080609012309010b0a0b0a0215100b07110a03050c0109060e010f0f020a0b 75
    0x2c0390010019444c015203140c0c1c2007441100a484020b90640d6420790b290310001c200c0c0898882d280550882c1c1e0000e01c140c2c8603aa1020707205205d881040c500c0200b40c0700c807100c81241c00518000c003062041005100d072405a8264000520784140d0030303201c0343c020340c00040503e980300d60100040c0005031a42c1c80c04601036201c3e0f543d0b0000100843c0f41030911500c003600180209031401d80100b0443d98002c920341e48250100c42560402d085a01289030040342c0f0020107500f15080c101131010031504134068204444555064960a4032500700307050a03a58a00002c041500642d041c20401070b100100054101c0002d20000440114280200d038100b40254441d100e4868041408181c0781d405100d0710170f104a03a0080c2010303510f00103400d0244042c00d80509402c0182c041059801c1060703a00b900101194014410741003680d4038500b80ba42d03112500000d5000815100c00080c187d40541c1c400c0c0500d010584a03088014001c0300100d031582c0b444104081144500601000071401002040f13000d106c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 166373156 1250 166371906 166371937
    0x702061b01020a020f1617010212180d030b21030409050c03060f0f0a0306020c01021c0c1701031e030c0609030e0f01110604080a050f0a090609050f03030a080c0d02 72
    0x104100f0290414169900458440c4c0001e09411890182403c02e4005da4422503200b000f182c411440d07185c028010b0503a00801c4524042c01d0142240711030303000b80050101c0074210340036040c0c2580b0840a03100302400c455040301003149005202124202551015900f207011a0305043d661440c0a05807078091b601a00200c82c0003051021905002290342c1030680291228034103489075001003000c090340b500c409061240d0108000301c0c840000c3d0100c80d1800a004201d4281e00320180c40341c1c0041401003240404a102c80d04007030b20400300a1603260403aa04402a400140e605004100044180d0f1504504002003039a0090008046102d0550703054000e40e40c404260f0411001d004a1004000799503041c0720101080340941e07100058110783c00342c0c0c06658030703454240302241580d80d4001c48100103404440491804011588540050704440350355a0fa0042c10f542c5100740100c0e4042c3d142c9407a0140c00c10048030300c0242c010800c15411928030319140b0701d8900000e441d00104e801031034035100b1016 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 166374406 1250 166373156 166373167
    0xd020c070f090b12031602040b0a0f15080601090306020703050f040608060406050a12061a0603040b09010f060308040302060c070b370206040f0809040504060b01081e06060702061b0102 81
    0x814418031100d65801e80e01c1881c0354140c141030355502e0042e20001b40d600c8982c0c40c003080c119180c940002c06041006000032051940300d0101c1c9240240307500641070740418001c0603440f00c034031584c8410f008040603118a4010b03402d40e00c400000e940082400d4052040c10843c0c408001c03030380b00040c00140381a80c2c540003241850003c0006907242c1d9440144540c07880d000074800f040303102c1d0318003200940c001400141c4204901001e064007054081003035119401100b0002032000d5144101e2240d0f0000c80200b16260070015048201c520364007014090180501c82072006081000c010546020726004881000b035407040c0341c0c0e55651014002c91203d281710b000e05000e0324a05c0548a04881446d0300c1426080500040250340d82c40082001d05410284201c000500620740101c07400024064014043c614060038480c024003941088036001404000c0003681510313000802c209075924180c00101d05440f08020028160003000d000d0760b0140d0200f1520210809031600e141901c0c00d050005600e64 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 166375656 1250 166374406 166374419
    0x60e010e0115031a221d0f0d0c02090a15030c060e010804080d2a02150c07020a060f020709090c0816080303040206030403030e0118350d020c070f 64
    0x2c1d00110800c41c14541804400310012011080301d03000c180c2d0030398098062010072000303414001c03044031101681070b03c2d004030702c2d04c040592412040f0208141003103031102e142400744540c1c0d0702d070700c042d4440014030805260001450004c90346500541580000b081c4007a030741c05a030400c04000d60080f555204008070812006402407400c0b420b41209007414031140c540b40e1191411841403100482c042d540e01c19541c981c08003a142e0f5540e881c081082c14810b010024007003e0b642d4991000c10a200307030454400a042c00840d0421241446d0313020f4540d4000e241b0f070400c16034a031030340c515191080d80501000032615583d141f0071040802d01541d00c10707403d2454184244d00b015075001c0d601105c010030300300a0240003000421a03800c20f0381900c1090b81c039922420110010401040320b0300855084c03a5101041100034900380d0f907101d0103074007994103520254203804001d10342c100301e0350300e10051032403210042c4401801401c61002034101c054a009440700d002801d001321900b081c0710760120741c001403001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 166376906 1250 166375656 166375679
    0x50702100c05090a03020d020312041202031c020d12060b070516050a0f031101051b03090f061c05090c03030703020313080c0901050d03030906020408030c0c09011208030406060e010e01 81
    0x100c03030981442c5280601140200fa290151408047e0281894441c1142191401c215104103e408420020b40f03541c0c80c1d0f584c54258413003c0340164845c1c400e0b48201c0b441c01e0803801c100c007200240c680062541006000302951000003040f016100c66655480020720328050400402031704c0e2140b005010a40d503d036031481c05480c2a40c010f02d01070560004240003410f501c41c81d610550ba0000c8103006001c0900740126990300c160640c20001004820b00c0c0c0d203c94a000020f8000c4a800b00c41c040c0c0401a04c07070500403a8080c400003452288005241e2040083c5039620042e0041620020f07541d60240d00b002092450f4003402d82240142d0001640c01400411620501c010f0200c04000d0f02800032a6400030f0360014040c06160302c115080044041058001c2d07202c0903600b81d01c40c400707544542d6501c01081c1c8a802001c1c0d034034010301400d095a0030300d1410000d0b66040e106140104405001c2c142c03100940342d08010021103906070ba03480d0108401c0c241e041c1b500d00a05454001101a6042a02c94080c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 166378156 1250 166376906 166376921
    0xf15020a021e1903050f251101030c051803070302030105070809070f1a0901020c100203180904020a0e0c120a05060a091a06031003140303010f080d091e0302030105070210 75
    0x30b050704254814026803e00405100703800c0e0f09450a10303240c41d80448420b62030300c03908a041c9207034075016050815110850340300311111800780d280c2c1e0303210007039110040d0140d0b0b90b00501d040014004100c1840c507c50f440300040080d5001030125044951203a020070708480003a40d0010100d4000d000300500307060108903480103051001092482c091810f48124501c010042010001c8440440d0313240b02d69100704154100307100010a668802e8500b003401075204d038465200700069000402802885081c9648450300440d07010300807030181850007000b03600d4818041c0c084407110b44200300c426070b0000c0060b0b9141c02403030300840c002180c1c00d00000304210801d0035445028150b0a00c4103689500c0110750b5034032120034096031620382c0c135910f40f01ea0301c1d8a00318581008144051003034400f203c03400000065410703901c0200032035003801d843c0c2c0c0c0001c0c2e40303071000c4500100240d100101072020503202180d140080c00e2528818141546a0740041e0940308125070003801a84200101c8900312400e020b03001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 166379406 1250 166378156 166378213
    0x418050105060c1f090f0c06030e0c0a0909050106050901030b0a0b09070e101803060518150703090c0302060f1801080105011b050f16030501060905060901030f15020a02 74
    0x24076140006001603120315000191140581c100300c070161039421250005c07100158440c0300e84400005a250803050666140100790000340341ca02c010040120000720341d0038880008010078001c40ca80a1303614054054282c045405548480b40043c80d0380b52402603902a500c1000450034524004090300101c941010120748203c03003000c1441491908940302404014040d103d08016420500e4113968401400f07203601424105004000305010701644030074018600060260810601710700070503a501e00e040c0904260b0300c400b40100340d0150003680003040603441a0329050116540c0e400196031360308001030b00d0340300e0789000880c900d0405442442c21b0120340c090070722440f10350425000130070081d00c500c812081e08010744000e00c01c2c02400c000c14603030130380c41d07204441c40d0b11115003041c601481d50348000c8640350b00b030440110b00c091060107114880e0101516a040d568030716140e840301100c0d82c1905540000440c641001c03400b8040c001481000102c0d0020610805206801e0803a820031041c5803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 166380656 1250 166379406 166379419
    0x1902060a0203010609031e051b040506090702280f080301030b07140d0c030905030309010b120f0d05090423060f041107030804050312161e02060720030418050105 71
    0x140503080d04140c0f0f220546c2d8105044810305c2c0b03800130001c0501091940f01070111b1181c500101c0f128092521101d050701001d42d814069601c9048c00d2194007401074500c400942c12072485500100c062003c6008081c0100c00d801c10350301915290848400344801081c4e5240c070b8004014001e0141f10f481958100701036240a2220119200c1d800070b081c00f0b003810580b0000c0d254905000c0262090304a8944950020b040c1d0750b86c2e04001c51010300906141c3e56050280e400300084034542100071600100340004036019180c9540c1e860350445030380c1c2c0034001a50748030ba9a4a40076034107030032052852400b07010301540e03800a030034142708010b91007000d1140c292080f4184140c0501241002080d1000301d0340c1414802860344035441c1a86c1180180010040305034610410440780304503a104501000c125074031000c800c00f21091074560201d2414400d000135a0140e404903603035a100d5640340384650100b01c200c09200e01000d464501f540c0c0140c1c0302200403924000f1981c00c4640c940705071030042c802116031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 166381906 1250 166380656 166380659
    0xb0105010e100f0215010b04060816092c040506010905010b0705030702040f020405030312071701060e100908011425170408132c101a0405061902060a020301 69
    0x5400440001d401000c000b0048034504440f0f008204100802440701c5000170b056031224084022078006100380c1c030005078070402161441c0e02d0402d00c0308801040b030b503c1100c21401d000f507441c852281092001c1b4280c5602c141c1c100109049003849028038400c00140c400341d4503004000041c1e40c4c3c107801944200c0e00030000c1400143c400011551415815540494011100640c401c005e01a550016816010000d5015032620402e0b000c40d20901540d01c0d90031210403180100c001c00c140c03d001c0e0340042010f81802100a203022400c400d643c015070b1620380041a1610038035801d4400001c0070000c20703a007460601c551640318084070b5081c06030020581800291080004000c0b40b0401c22810a44141320089028448000100c400324441004c465803401d54440f501c044148003848408441000420318080820689010500490207452814a6103062140d44800341e05c03030581e01d5520860030400080d85888040181560400464606000d0182600d0280c1000c90041240e450030380704200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 166383156 1250 166381906 166381909
    0x30b03010c02030c0d11010902030d08040b0112020d0807020d0507080a0515090705090a090204020a0c062d020c010221010e010602060f1306091b090e0601050328080a05070b0105010e 80
    0xc9170445d180751442e01c40c01e0000329a2040b80103054285020303405000300c031180c01881c2c0e000440540030f18030800c0c0001e140e03070340c0d00320b800d5508410510003540b00080780d804d07001055149000d009200d000800c120b8855034603580b00c501c4c01d49154000c000c0c07900010040c0c41804030502c1600b0400028941c05040c030b18000a0454030303007046003d003e20032541d4030041980221240d0101e09040d80c060700441d82c2d94803034600604102c5000000701c81842c1458801000311484140312882c0d0701644415952100300d8200e00d50180d005504900c1e1159401c2c0844800101c5511521203a0b810745a416203155040c181c805107a854140c020005540c0100141f1003059a410001e99000b042d0214001947d4218600342c4007403c3c501c1c078054002c000c1e44520041800340c114141080f103409503410480d41000319011911400300344035060303068012200b90545464402d60300007400801040300340d20b0890300c2c1d882284580081c2a01c00000384040380c56020440306a903010702400007402c0c420144070f0fa080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 166384406 1250 166383156 166383163
    0x50f0405040221030f04030c260706051624050609010f031b03060c020105090d030c02030909060a0e04030203090a1205030a120209040c1112090604141c03030b03010c02030c 76
    0xd221101042042083c0d046052090f1071124402441c125900d680e00d0500880300440c5010740380049001d1800204122221071080210001940103410300e141f40c4401540c030784d080305103250540780c0c41c01c1d04940003d078240e0301030905280001030100b0038a040c01d5090111003000300424000c5410000500ca0103062128240440340e00489494031116100c08140c0d813001c03161f000422450401600e00304442d019041039209010041c100c5080002d03c040850603584c1103171480c00560000c000d22410b40c1001c0c4801c5911003800303040140140c0da202280e18a0a804860540040c2c20125045455280c4414003000030f12140089040300d034400c1d00c4040d10b034429481450140080380c2e69441000542d42c0695105250081040000200510020b04441c40080c0140b149000384030381000005003030404e0b2014420080e103024207060070052800402920445030700c1c3d002160040440560851650000001744659008100d400c5c5450605003550184124070065400500c1010103000000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 166385656 1250 166384406 166384429
    0x609061b0123011715090604020f01031109060304080403021002160902090a090203040303090b09070e091c200703080904200a030c110a050601080d0c02030703110609090a06050f04050402 82
    0x144d03118a4a00140740ca181d140404683c1c0603c0e4410200303003000122a408118644180e00a07101c3c10388000c801401103045802e00403044c0e142d244140440b281070b081a1000e1070303025114145592800d0b8a0760002100707106406500360060707001442e060201c255001d01d00c40180b0b0801006d505205034003000448821950280c1044154003000003810700d48260007000340f0940040e10358106003030060980ba16854140030f162200e05182000c5940c1e1903000a00001450b00d480d0111000e01042e41c04a03103001081306400811070130284003101010f428814400111b01c60103c141d42e80d4090f1041c131040d17030303000b810001c080641e070010300200c2c000b640100c0d0246081450300080d0031084200684050007030082d0b5190910400101008009001038803a041c0c4d0281412900000102e49080303c40506900707000350107400142c400c10000300f040c1e05501038124010515800d180b548004515200b0007260300c00202a1213980c10850303400c01141c3c000c6003400c280e8092000d0f181c142c000c02d0540804 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 166386906 1250 166385656 166385669
    0x5030403030b0406090518030315091e0702030703120e1b0406080703440315060c0706090b0406080c0c0109020303220b0301050306150609061b012301 66
    0x10009040601c25404282d40d840024001c0120989490004000303000440b4038140c40c00c0130352414130020b00000192489407a5841c04240040c3c02340c8280490140044c105054101b1511304907680807a072250250311441e00340d0700440e00c640341410002e08220150164074409450440f26020f0108007107009080c070b20f51070881c0c0c84130f602060089002441e540d80241200d000f1100040208200d10b0308440e090b0031081c04100100a444096640003001c0892009824141110001c031500c0303224040d590040d51002e01081600340c8001046060b40a0419420140c21018050102c19000403c80028010441c002410700313040c00750203403140f00c01811580541101240400200c4001d40203a065a030380901641c0d1907224550b01810808a109513404400d0301002d0301241840310201540d0407a10300500510aa480e080c01c0c2240c550003c1100a4100c90200034000d25034940d40000d100d00f407a82083e130765a10700c001805a0844440c1030315240d0000441d0a0101030500000c04181541d21 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 166388156 1250 166386906 166386917
    0x90a03080c0406020c04240e0103110303090a060e0a092309010509101509090b04120206040b0c070c050a060207180e071e090f05010501080906220203070b0708040f15050901 76
    0x300071100b0032410300d0300d82d04529002d81207c003285600b501024a030403280700c0da541141001018080503120b000d52030401f508034408400420540d0300c00e4600b00301e05800604503540240d10744000e40b091f111030b40401c000c100284848095a040800382d4035030312102c0c010081005007031400c0001d88560300d00300303070fa4026030300c40b9a078240d891003201c8004010310005004121a400620706003c1c1301104a40a440c60101e0500107690079001041c0703140300382c0d40802d01d012143c0d10b41f004090700d13401c6600d040e1a014440c40d00441c2d03c3d190101c46c074002e410b41d03030001d2189a14001400d54100f5500400002c824201501d246141a0015124054980442020140500042d04103e007140c040d40a209a182094508181d208603540034a05803042030380d0b540d580d995101c4005075510001d81e241d0100e0210001d00302191030021940d660f44910040a40f070b282a0b44013007070042e9400a46c4d0642d00140005001c216100601c08a000288183d090303c90000d0030811016129005c1d0a1000c1e05115 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 166389406 1250 166388156 166388171
    0x70204060b0307080115021b011d03010f02091c020907031d06070e01120b0a0b090604030506180d08070203030a020f09030307110907031107140114090a03080c0406020c04 75
    0x598681000015049001d1120707103d00d001d0728001c000c4442072250707103002d0026a440303003a1a4800300f00300c160085141e502c2081800c000d00111004605441d440c031000e200004806916a000e02880c3c82002e6004009a2181815820041e420b1fa00b041072240c07840c0502a0302006843c3d41075203540c0102075090026244880c941c18070440c505c0d110045516008031001c1100440c0c10600961030f914081e80c038001080165103c01e4121007918a4956000008210810140004600501c065400600300500b0035590342d40e02842c0200540301c040300820300c002c1c2c0400d0a041009107000360401468560a2400c103001d000c1d440b88805003982c141181c0005440241c48154070440b43e00c003801800316580c8440d03a080c0710301c600344e10a0300280b0a45100010076000c82c13190040b00c05400501d00c0f05480c007119540c4040d04a00c060352919115501e5498403056401285103041c450440038028113101011071400070f01c0e5040040071820000702c11700042c40301e9a800105001c05a070241c40014400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 166390656 1250 166389406 166389409
    0x30c090c0703020c030604081c0209030c0f030709060e01080f010506011b2909010b03010203010609180609090b0106030e0d09060f0e0307080304090b04020a020a240203010f05011d03060c0702 84
    0x4c0280c600050b018801c5000b440104890000204130071056220030b0300a4165140e41d600aa1180c07040b00e640c540e01a121040c55482c1030004107400410007801c4903420750b603690b102c070f003075030440c1e44041c1c181080c5d800100a0030006000d190b00440310440200120b10788400003800011443c41e0a261442c400300c038000c1040000c14101002d491600b00107840b403400c196011070054000c40d4a500c555080414003c070745d083c14000c0d079040e5210fa88600350a02e040c4039591442a0030940b01107001603ca4000140710304180c030a4051841c05840004841e605080f0080c4c01d0310351040d0304c00407a900c090a0000b10365402010715003526620314000c48030001250088640100040000f0b9040c0500c110025240700000010300c201c402203001400907071809400c10049004204407040940c00c2400d15000041c3c0c0e0180310501403000c0d940c20118482e0100024080b80c0090308000d1510001684c284020760700007100e042040208842c03418240c0703c05021a856040280c80107900780800b03d986002c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 166391906 1250 166390656 166390663
    0xa1802040e0a1a010206010305060c07241d0304060504030b06010201021c02030907050603041502030705070615061b020f09060d30050705030307140d050703051005030c090c070302 79
    0xa015100c0100381c0740c00d1804180009008800d16118a10043c585055142d400490980c0c1241d03048006000715550b404202000340d48100c208507100040c2691041000e1000341c10442a0012201e0003e40400042040d40f03000031450f9419115a0003400104026a480300884050700d070b0001114a05071603200c0184d0180c021096055003520b949411106000103507400b0314418071740c4204403181155a10240a0301d44015140500481100200c964080c10350b50000e50b00010039140503441c1018507126101260003129400d10308000300030301049030b02e0b8808a030811400d003501d034242141c0e02c180d0001c0c15103016441d80d00d000d0015440051140c1c0d841400d1941c8581e0864801d0100a07403580340b2244002c56940c81011072000c3e862244078940c4110140c515041c3d02900840c5581c0701c0c0740c0d05a0f19007140902d624050f110070040148420940e0207614081e10b90703900c3c0894242070109c0007114542d810380016000b5031140581042c50b40d600038445801482074100c203030741c49d000e13810101e04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 166393156 1250 166391906 166391909
    0x30c07020f0f0d1127160c0510090b070e0609010c0501110f072010080402030c04061502010506010201020903072c10061103090108011503090c06050a0201060b0304020a180204 77
    0x40c03162891241000b84250107440342d01544003110100d4000e44140140008101c036180f10149100c07001000034880c00c5120100c2c010340c0e0b81c1c0d00340b0121f140510f42c5c030240340c5100c409802c110244c0391114007041003120301c4000d030020140d00703016005010000124a00740030b0f01c0f4040f8100100781e810b40051002c02c1d40f103102003035040080d030b42e590a01c0b4402210280e001941c11201040c1b42001c1801c40780c0558040014860001c2c80e10f0800d05071094100d410340d401510582e454010304019681999552117010b0050103400710b00d25544020100283c21140e000b45803e0540e40108941d01c087da80109003101500c502e02004142d040040004408641c1301d6081146c00d04010342c1404241c02180324080111900c035600c0c1e0342800846140c282d201e00030072101d540416100e80041c06140317041d14825001918074a800111041140ca50300c910510591290010450004007030a035a582070007440d01400b55982071900d1428a90b0118001b43c145100e040c480341041548040c802005070101d60 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 166394406 1250 166393156 166393159
    0x210051e04084008010c050415020102090402070b01150c0209180309041a21070308030601110d080702100e031602011107060521061513030506010308030103021005030c07020f0f 78
    0x901e010b80002848003030061a40b0f07445103400240740042e0302d4a050150025080b001e988042c20a80ba0182d001014418100c0381415950240100074250312140b0190140c0c034000c0034209000d501d030410420554420b0306000c0c00b00102c2201050142c2c44250f0b4aa8120b1000f03000510150020a00c040c10b41c040c1c5050f4039403040c01c2028207402c40716001c3d107401800780c00302c82888200164462511608502c0312904100740c10660003000890400d501840c0d01c4081030500c0070307012180c4030341c00781803070f442f2400c480c0400e4411092180c1c0e40e6041000400d00c00b8010300401261032501d0413190f60340207003007070966800840c00f8080c0440e4800e034a50b03100000d101080307030301e0b1580310340002c1c00c90f0300040d01c84c41046002a400d40c408190341140f450050a0260180192070340400344100c440d804044010360303048000800000041c020882d190085015020107501c075411403040000d580c52032030401003009024030a22103904001000c0711801641150b230a140c0202c42404682601090f0a20344d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 166395656 1250 166394406 166394467
    0x30b0d030e030a230f0f190303061206060f140d11190905010801110a0804020409030509100809150906180a14031b010606120b040f0504030210051e0408 67
    0x10601c405407041244d201c2c2640509641e2006000041c4a6588600401440c41036001c8091840c41043d5840e2240b44940686004a20a511120384850b40c0c0d1512808940c19540c030307001000501003d00c80140500410b83c141c1544203618000180d030f40103c0e1401605000307080200421701d0b501c4d101440d056680c0c0180403060745584101090007800c0900c070f4072010b9402c0c69440c0300c0c0b0b00040c100726862150240c44100450302e490b003d0100610300e2103401c80912004000e189a15501c1c1030403080f10300d40c1d55640004034508005e141e2704100015801c990161902e00c180700c41e03002c02103850369005514419060b018803428a07024548549202d002d01180110b8542c0c44204101000400784400450b11120510300160145c03400c035507062040e80c002411103620600002a10f401000c0c0c0140000c00125805020304840c0f8111001501c003180503a028a4501825041c0b0f8000e06034032003071070f803d015201c0c07007034407009584050b00078030091082c2c82c001180d400314040305026860144441040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 166396906 1250 166395656 166395683
    0xe060d020702270601090e0a0203150301062304272a0806070816030c141305090a02070804061b050708030a09090e030406230a030902040507030b0d030e030a 69
    0x44980d2904001001e4603060f0103007000030059401032585d202121003a2500825030790b06e26110000039000a0210204059640c48c0c02000342e400340500b8019148140646040ca01c0c0c1103113000000d910444458040c034202840c01d80c54100c04800b00c0061120f0f40303400c0402c5182c3d85010205146003080c80c1c85803680801404803901e45984201003a1040301f0101d5059071034a40094410190440e41803003119080c460300031995110783c1092440001500300802490301d098a500180c0d040f500401880100079981080185416000c0710381000e4900303811071401c9055122141d45101e00c0c040c510034011a500c001400781d0510800011007070704207060324074090300c0c1c007426a03d07070f44207800340e84c00109140d4001c1001495881010b08181c6050001e500d4540307421801d50b041c0c403054005120100342c0c1580454100700c05001084084c4142e80c3c0095584260320400c03088541c040c0003401054039043c002d089036100c0d000802502038060070a0a054a4000000f07850107912440c02030003c01941c69 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 166398156 1250 166396906 166396939
    0x9080f03042a060e01030207020307060f020a0624060f05030c0306010908030304030207180c0e0d02041407020309010212090d03200106060e030105010915090f020d180c05030d0e060d020702 83
    0xa4005071030303d40d0b450f00e040020620044040c2e0042a1012354980c02509081011700d018206003142c020366401602c4140f030b05625036104032144400c20685c40b9010000c10920312590f42400000303002d50307090a00918441c2c841c000e04600004100d0b010f807840000102d86142e0048045600602840c0201e9549151501d002901c41415104171444103c6c11107038404004890b0042e581d02050310358a103d00050b810b020000002200981a60069510380508040144020209d4811002c0d80c00550381c403080b01c4002840d004d4241442c0302c0c5404207100c030714226501c02d50484503150f01450000050703800140c1c0b6031544408945041000c1d032a1075000500150000128074900c103084008201903aa22120881907030620b5001261107842810244030390b81c02035006400044403600d0040c2030000c0c0d407100504032150580503200880d06401c000c0100461f01007082c0180409070301800ca081041c0502600343c614a80c5c1240c407400c0c020070341c40e0428009905403044590000d04800c00481c0161 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 166399406 1250 166398156 166398233
    0x901060b040801142401120905032709040c06030b01031e09060e060405070303050307031407090302030f0705060901031a030a0b19090b0a05071106010314010e0109080f0304 76
    0x204c119442001200080301d0402c0e0031034140303c002031260544542540c2c1c0004552020901c0f00c0c040036140d4908103036010510401c0a0450800b0189101c4100c1e131503d1503840b445503241c00498820060b4004120000360141030907400c40b0090700b004a4072181050040c0c024003070022481c0000c441c41490001c080c0d9686d048055010300858003003001d50304c8050040c0c0c50710402c40340602280d00800040000030300c01c20055610244901c0d00088400036943c0203104a0710035079031000000ca4100c0240258034081c001d8240442d28503000388486450440420300e180606407915041c19522111680c07044208000c5601c100d02c001c3c21384050310b101d03141c40d15294800352074480030300410001c100c9813442d042c4030341c00d1066040854401a540c2d03000c80c00000d0030b8001c0525041010380a0281074800040004074083c40c402c0075000312010f0410a02800c40307901140f414482d1381401600c8012884403001c071180800742401040d52540c55080601032445845408076048d090391110640c03200814 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 166400656 1250 166399406 166399421
    0x150c0a080a1803080a0503041505100e06030309010206180f010204240503010303050409090f0203030c0d02010e161a04050603161206030209060904020a05060c030706060602030301060212030901060b040801 90
    0x7519621100ea8521100d619461a030f400020a007400401c0449105409040030f5076000b8441c50940d00490110040003080d503009030740c191040c2e2070a0340248030b03440700c0c049400d0f40488164015414507074810300003950303000c0c050311005200f07890480300605030f0001e0100f018518043c130025940c03030b41c0d56003100000d00c00004003400c2e0146440503c500030303481402180c1c100d940680d98a410582072130030450040003008402c6911541d09481200182ca083c005401da41812201078100136944a0020f401c2d500105e004c641103070400420200c094102c07141000c00c0d1141d0010707200d911181d629500f08075106039040640d12181c0031041044120120b40710100c9102c065441401140c0c948020310180c40c03550000a40c0542d680700002c0d22402e000d01d945900500042022140741d9680300403400c10760245580c400c0355000010b511090041d2401500010708452005519562600a0003512103c4102010700204e06c0007010a854040942250b4058451240ca85590356030f80c09845000b01400d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 166401906 1250 166400656 166400677
    0x1519030b090105010305030307050322050303060f0307050a180212010806011805151e060313021914060c01091b081605060a05090316030609150911150c0a08 69
    0x50800090a548043c0a400c1c100c3c0da1010007503045480f824000d07901a00014031811198451290b140c0800c6d9440c48111885800745029641da800d2040c240651320042e039420f00e009500001c8100240d4840422400480c3c1040c04c00020000c4180326100180c07007810781c403035503408002c5c00101e141000030070401d040320100d050703500c0303c0400a0b1600055030b1048581c00c08803c0c0120310442203003031409940014a8111403601da2034030f40c001c00106c8503042a501c0342c1c00017002c0d190034070440c00c0c41101003640d0078516884103603261a15001083d450342c2c8084041c080d25010030074040400c8250040c005280c0c1c080300044608900541003894001c2c54406d41006204140d81c0141040004404100345d81c000f0b82401d00d01440c50034203071543d6020300c000d0307500340c0f03e5180c2d03261a0155400004001e18860200840d01950300e0802c5901005405c80e0f40c0ca1451030071940c0c1c40000c5800201502c290815250b0040100f0a0814500540501e066040850140c02118410041d004d4001c00000c0c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 166403156 1250 166401906 166401923
    0x4030e01021605010206011208122706060904081b03070303021c1e021c050408070204141003020f041b020d14090114090a030203030f09010305070804050d08151903 72
    0x200001402c425038900c00c89025030441d50041c800e181c0e143c003031603160600643c20b0030b05d0410402e0310504014030450b030000035403002d0240840020000c5101440c5c070310805005003901c1c142800025401c800140c40100f00361320004031100820068482400440e0b482001d90351560782c0c504000e0040d5005a0205003500058001000c80c0007991062403015600c41150115440e54240503900a520480b0180c1902c1503585841000070300c00d01031988214400c0300025250025441031000f81c801d0000d200c10140b00301c0301004401000ea5074400c0c00c8a8045401090407a814004076004100c4100d0801e04c801c0030346414560290001012440c10026554801406d00c01c50b01440d9140603015000b400206102050840c4034251b01c090000641c004000c0b02c8034564950000b890b60703001d007101c0d54080f540856400d401d1341e094415035510000a0820100c6031800741d9400d900d0f000303091800d0301440006d13400302d454502c0c40c15034070303541170313170240140d03240b090703c441d81840901062008491485 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 166404406 1250 166403156 166403173
    0x90a03080609040b040b04110a030507051206060916050403020d0803191b03021e04080601090e0111071e0c0f0e01050301020c0a0b15061315020c03030f0a031404030e0102 75
    0x3010002c5912941c0c200743ca02e405621140d41d8070101c148081d1041e50200c4151f40703100d00350f0340d606041c14021031052004180051802d01800156095004042260b03023040f820441282c0300c200d45e6643c41000005006490002c607001030b174190007543c1019402c08545401081041a41001036000e00318000640203040010941303003040e5024003540704c025800b1110501d000c00d01a401078240789030400e0b007045880040b41071000c1c280d045544500c4482c1e0141e0300421289000703200703692100d24031800030b00c09244c01c0801c2424621542a0081c44480b5681003409110003100b11241140c2d401703600040b48030b907a51412014404c07940900c40500305035400018041c0742c1403088402a403c1c0d030b406410150900e071160041850002c010103881e480500c100b640350b9407808003c20800345c03040010501107040508003c8039041112000d070640d40070b1f44820103035590002c2540c0301c4c48208050144d5035020342400300d010380b0210b9040c50130f0180c0c2e1418401019084020003489500c207a0854078542e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 166405656 1250 166404406 166404409
    0x1109040b1203040504020c0c1c03111204060c0809090c09040c090f090b060417030304231002090d050703290408031605071a0609181b0f09090a030806 66
    0x1224004400701075034020042001503041c15005400e08100c10415650505000c0000c502004451b0752001c000200c6103426804154010350464007002004004040004001e4075045070f511450280b8000c3c000401d048008000c1810110b5003842806071124095040244209181d0341220100768451802c0100341150548100b40e481d045078469000e01c07000e1407410384043c1c01480240c0d40396402400411020030104481c00703040c04d0413181e09004650300d1811342044400400384078049410342c0108251a405110000b41e908080c1d80354501c010ba03960200c500050911180c814001c046015101d800420f0100e4480d04c040b0403150951840002015640b06400c0d6071800c80c2d00500e0981f0074008034403002207080502d843c0c02c01b5420128900740c10341d01c41e00810b0301d0b074102c0804442000810442913007800c040c25504000040300800c0c1400002002c2511900002c081c000241043c00c01d07a0007a81c0c8000d000c4103450000f8121103e941041031980351076441740c2c44240c0c0030400d03000101d0000e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 166406906 1250 166405656 166405669
    0x50106020c060304110316060905150a1d030c0d03020f010b0607030c06090303020d02070f03020705150702090c13080709150321110d030903020c0604030317191109040b 74
    0x280700040c0590314640d81c2d903072800c2c030807a80440242e415106a40340039210301c44504483c0302428464907090502032500040201a6920000c1460304800c00d0260242c4241c0003510300c0d19203030751240300000d07404c01c10020903c0c1000d810601d680c0842c0340076414080c540c003c5640424101404002d02020501605000440c411000010009800509000003007000c070b0780700c1101d0070b02c20311f0054a00a400c500700d1040c0e802150382520001703000143e07402050740401c840c8000b000155100e10748161007055030000c6d0f01642d10082d0062030b48000061025004104440e0191601c104954400c1d44483e2400e0760f43c0b000c0c3c080e8100c06850007080314045401201c0355000c80381d001482144a0325909200c400340030304086d81c541404000041d0750343c0c00109001034940f0445d156000604e05e005030500a192100716801079000c1e0307100f0842070001c03a601060000b014620166024120f0b10350709005125000a404605d484520300700074045074940480c01488001d4040f1000e000203110503042004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 166408156 1250 166406906 166406923
    0x804051618140c03040f06060510120c090506041a040801020a020a030f02060105100525140c01030504120509011403010806041202010e1c0201060f08062a03040209040609050a0b0a05010602 83
    0x10112000d1002400192440411b42c1c4c209201c0c0310301203199039445010030315000d181610800411816000c0d0f00d03100203035114a40503d00c4c14682040001d16060100c0c1c590f208a014212007036100401e050500fa2400381110000c10449000b15504c410f1000000c0d03c17484107001c110001000005501c86081c4001400c5050350801066084c68588200043d10f40d580030389400d0a1401034560030558102640c82d501c456103009122849010306540c0c7c5060400d0301c0d90400c241414542814440400c0c0c65184046c41000303141445541c4100340d1005071070415403c4000105003d000001244240b400301c1c1c140d0103140710b44008105010070302e10a03030903512454141740481c0d00580c0340c0c80032081c600b42d100c62040303501e0000041c9140c80342e070002014003030394101d610144e02c10014010509003200c04056605c2c0f150640e0505c152000d906589203200c083c0000c0d01c1155454045001d111055200580e029407040803601302c0e04242c40c01c00d40f134101c200d4070080d030540380c580000b0307080c1d002107102072 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 166409406 1250 166408156 166408171
    0x3030f0904050a0605131b02030a020c0d020604030c080102090301050a091a100906140312041a0307120204030f02030d03050601200f0304080f010b1504030201080405161814 76
    0x90a00380624107200c02000d0040071140c00ba0f0304d40ca400101a10794481000740f07503045c400003081c1c50045528201000e250400d264046600c10003c3c403141d90750115014900007022241c01c15008100d0000540310300075904064072b41340d40380000040000c81513000b004544401d4009000d942e85600b0700d001110860000903044d588017a482c0c1c4500c1c12146803240e4402c02d0455010307000da49a01142d07048401a41003a4103401d030303a0300442c1e00c1c0c0c0b030701b0064000c0909400030750f5490242030548140403110010707a0351003042d01c0030000c01c2035503010300700702119216204000c5454941c0ca0400d01c01c038241c0e0b810142d0003401552060480d0610900540e80b1424041e151541c801c0c2ca8810700c0701c05448958204d000a0062401c0f956a01405000030001002a040200205001d021955085980000740c1c6031046107000111a840003001d8142c030110394090038140c0e038640d00e41c01d2a0341000f1801c050741c0305440d0039120101e11700034100c0518910036400d0720204601703c1900c4ea4116600740c103a6008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 166410656 1250 166409406 166409437
    0x20106050a03060528020705010b060c0d0503090106090903050901030f0e031e070203030a030606110d09212111010b0a0e060a090905030a171501120b0316030c050303 73
    0x2e1020400a81110303405c00c0305031200c480000131708614650b07010180f42880f00c031207070002100410302000340039002c1c2e9841c04035846803820b490312140c1c0303950b62100a0210203110000c00060141c04082d84960003c1840762010b0007000041e1034001d0030b07584101782d600e020038a064000907440e003207442158400e402c1c042c001e40c5402101c00038800d001000300c000403506101006444016102480640b080002949004c03c00c1420314001a0001b00d2029000715540d10001e41c0340d224035032118040741101c008002c021402e00c6464206501044001809803161040341e0f0394103290031a04564040b0840c0b20743d5507000714903c6013003a9003a60441d00009600c010a10010300101c01020311303a43d00104010511029513a1341c1340301c030050711070494055443c0c0d000030a0b14807811f1703003105403c0800c1e0742c01080e070b800a10b4030f0305c142601c2400100720a130401202045010542041e6804400300102c018100c9400d22405840351841d80043c0c00121900c400c1a040000c042c02c002050300d02c08501321881 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 166411906 1250 166410656 166410659
    0x1006051804020f1e04060f0c031e3605031212100e0708190e0d080a11120a0b0103090b0a0e0a15020a0801080705060403021207170307050c01020106050a 67
    0x820001e90810a11440728600400c000c0030700000b00c02c1e01342c094040c00032056849900e4114044d0103c00008400030610a4005402001a5001041c0000e200301c1e1521504915480c010454804102c0852070080d44855901000720540010405c4024039224004d03042e180e03102c3d81450f8461030187c0c0c229044000c20302582d030341c640d108a00c80341d110600900c55001c40d56903034684040340409668800c0491111028004010341e0300c20300103075907111400c05114040e010700002e039079610203070b50310f05c1003015010100d1039406158001003103020030303400c0c1c080c3c82303429044108a0a00050700c240ca1103501d0400702001e154064041d483c0410b0300013000c10081d40e14100004050b0140c03800300c482a000740451040000c220040e00b000c1c2e5040b203200162107105148002d4510f40c41130300085115400010100110756548080b141500d5040d9201e0681c007280880d803e00d01201504088950a120b85a08080701c0300003000c0c181e040c0c080c208544002c1c031950016401c89403030b400b50541041d2401c1c030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 166413156 1250 166411906 166411909
    0x51b1c0e0d031b06020f0c060a09022b0c1d0a0903050a05180d08030105180f060418120c150212011502030c06010b03011502060105280b0a020610060518 67
    0xb0b80010f80070060810641c1419030741c0c0c1c80701244d001d00742c1e44114203400b00d20420401c1741005003641c00043d03524100090344654000611420300484103c01d00c469602c603014a003040c056240107440c1c2d0140c41125030680303600428024201d03030582e604007060f0107000140210395500481c154a40c064490274030b4034506640440706680001240090342032041600e0445403280c01c0c00d205814007070041e85407254140010012a1040700102d1000c1c400c4074403d110201480d14030160700110b040710b00003403420920070541c03160070103050b0190201d82085601c6121940021400e440d082c032840711203c0044100c03c0202c224011071419500f8400e03448014400130701e5240c981440c0c00c19a004903420026041911494034200340c100b01a09800400100b2070689840d80c80d0065160724000349c605034ac10b04001c141042480c007040351280c1ca40c0403444858809150000000d0104003000c1c6030b64100320352000c1e42da03040541b41c82483d02c042035800190544150142c40265510100c84124100c2260 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 166414406 1250 166413156 166413167
    0x3090f030c0507030506010605121f050f040b0315010518090a022101020d060906080c03100203060a031202060f01150503161101020406090806010602010207020a0b0a051b1c0e0d03 79
    0x7007141ea600c00c85a0100110307100b0440b95000380007659807903994a02d16103200c5c3d40340101501350a035482880d101d0031882c031012202e030400c3d0790055480c8184001080001000f400000b03000582502a10007603843e41c0500c0b0394500e060b40c10a86200941c050130840510381048111882e1900b42c0051145c0001440c0c0024000c3c0c550410f0844041101502c11080b801caa00901d01100c01c59a1030720100a41c6040e4016000180140310141c0303007900f00100840c2e1911a162001d40e031880e4008009034a5079590910302010b5034011941050405081a01075a50783c8141c86480f411001c40b800011800380981d00d12408003201d9403000e095440d51030042000d007214404007000d000c888811755460203003d10141000784400c1d0384d02040c0c0c42c60140b80e1410031206030400e1003164010091400540c0742c0001440c01c55069025441c0d41c0c06074884110f0712030251501244440e0058902c244250000142a040304d050880c405032802c1c64461080d14400001004560408103101410001c80e0184 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 166415656 1250 166414406 166414427
    0xd0c080904050112020f0a0605180604080109050619060b040311040605091e09011107021909110301090c02070303021c0c050a140d0201061d060d060509030901030b0103090f03 77
    0x105165030400803035034006416603009801c1070301e01e44041e100e003605510700303000d2034108400b051311001045420810004d10902c40d44408803180031000e0040c552a80715402143c000346000002044064110b181142c3c65080a8842000030f80d01a084500342c40e0f4544200d6080b26002011940341c1859591a1000600c0342160254456079522000031a40c8445038243e1060081034008001200e820842d0314220304080d1201c400c0780c2c58032000034440e24503003048401c1c09030101d401d0b4a040070002030310440074103581c20030031a50f401d003120340d0035a8442e80e0145050341d11607242809400b50480080303954414901c809001a408a5038106550f0451340418203140b040703150a04400c20503072522460075141c0c0306d0841d0788c1d14424501d900044170600c0000321201c4030740300078800300d8980886094100d508010382ca00b540d440a021a4141d612942003401c0d85502813024000c0345804081a62640c00280c2010b0100382420358686696201c1d10810180070341c0101140040c00d00d0351400c44500c01c92 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 166416906 1250 166415656 166415663
    0x6060c01060605190206060a060503060d05030f04060908150403080c07080c28030c06051504090c090f111606060308030a09020a050d12210e010e0705120d0c 69
    0x20000111401000e0040380054003082c3c40d4107070b60350211014000303500c0b484a9581c003150011800e0000655030310013560110741c114500252281c039030000007184602d003031300010068840003685540110090026000b03c0d9000e0b221a681e241e624004640c459100d041c2e81c04000c0c03142400180064007600c4420340041419450500b0441e1980e50310049034022440581541d01480e1741a1110307108500c030344c40340d44080c00020200050781d5005000c005000300003c000f80d486a00261f41017101c042480a02440140203110480d0982895189a4107902035660418188540413402901c180a001d60082c1210b003d50728042051a01c80843c4015500849290703898070f4000001c101040080d40c000c0020702c2e80004c40f98001d104000d5440c2c0c1da5407200380910600384a240100324528070800300380300a0705040280c140c2c0006180c000107020394084e00414a005400104100150b1040005110080c22548069218001c02c0b800b8410b0840060307191303105460f108034252103410400b408510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 166418156 1250 166416906 166416919
    0x9060608010f06050406090b1c0204020904061508010801020406020a03031d0610080609070308030a020a11030406050714030316050f071e02030d0c03020601170a050303100501120e1506 81
    0x889040c0c05007035034988010000b1490725440c06201600d403a00ca44002030070340348000c0000407041004120750001032000c7d01010941080d8480954440350112000aa80140100070f143d444040c0070b0403441c0d0103175030a030000b9800400480d07020814800c0f0b4054480540080c41e04406950b0101c020308410314054088a044035041403840000b0400d00d801a4040c01001c0103940c2080141494079038001c0c20a4010b50100c0e408001081f0b411040b03d8000d00c0c141c0b805a03407110310b15025180d1102e2282c03540102e120004e000514190f0107005010014410bd5100b00310b402c4031154195280400d80340002c66180141c40b01d2002c500803002803a1800645642c1d0341041c10030386482c4010b0004511014400404d81e5041c011490180b02d2020701600a050203c608102514000e54480c014003807050036108500500409030010804500fa84c1d60180440e540ca10744644100e0342a111446481d01107242601e500540302c044d400343c11000c2400000510244005108418449402501c0b5503042103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 166419406 1250 166418156 166418159
    0xc0e2a0a05040b03010e0115080c0405090a0209100327170307120510172d01090f060c090b030108031c1803111b1305090111071a011a0d090606 63
    0x1c0005016600800344240c0100c0d6641c500235000c8030440034500c400c410060b1201c10852130380c06074810380341a40c01c2941d401e88a640c554a1580080c4102250303203a11645010060350705070f0703045e0416110a00500c100c00042c550403988034008000c1d10100a01d941120841c2c200c0c032440c5003001d1940260f042c50700000d0990760804400445005556054520124a0007800008440c9840140b5400b1000080c140042e00340318440c8400e0310120312040750400b4007140421441300750440381d008d5400c034001d050080050321700b0100800015607083c010441c0d40f01d000902c16180c0c4140c030304907078000c8080c6203007021486a400c590710300709000745461641c03100419030703403804281c02da004140302e5240c48610790840c0701c0c0c907850485600b00040d2880d20498502c01c543d1503c400303c1c0e810351101c540119840e00c030030410301d002d00511400a034218002142c00810b0107800c10340055014850a0f8607101642c0310707d00b0704148030100200e07110245040202c0005040d031139200540c0c1a018500005440c1d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 166420656 1250 166419406 166419419
    0x406140112020f1317120405010203071b08100603120906020a14240f0a05070905010c230604030e04050f1303020a050d0e011b1113180c0e2a0a0504 65
    0x51303426004107610480910002c032060404201d8902c4403001c43c4c800c05d040c2132400d00003d550740700340b1000900309852802c005860403c00e20520010740055411360751456405410200140400c2c802030303c01c84030010264690743e0250744600300360707a9254040d0800740c999448980040501d46e9481d141446100780f800700343d00009030400c1074120780440b810030303c1c281002e082c85650000750034034144910306002d00c08041e4000c4504012210282440c3d413440c0414200808050b2000c0340075001e801076891800d50070000413078000d01c56407194664000e503400503410b100486004131000d030044890940410307100c01c191850b1014540c403e104441001c0c060740c0d11300303042c403503260780740c070040350003003101043d2582c110910030212038036450760b40505200c54590140500c10f46401501804c0318107012412117070140c114265100c8040c50f415103012062902110b60743d82c03440b07891a00c1561030003141c1c0c410f2080b860301c1462600e00300851f400303420301c0344c1c00005544010b0404003401020440003522 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 166421906 1250 166420656 166420687
    0x92106020f09040506010809060a111309090b0912030402040b21010c03060611030d05070507080a0903150b0a05010e28060216080613020604030b0a0b0406140112020f 73
    0x80c1840d40e00841e440702142d5007404151100a003215041c40071400402c05e00f40303000940d040e4000300144022a10070000c8503829150321800c40c04810284003448003055500c0030781c0100902903c02e080344000f83c1e884080064841d1070a00748481101e1040011070050319064010102040004020307080609000b80718507c580306400400340503035102d40c5090342d102d406101d00d50003000113040c400306c000e07201400245c403885402440913080b940e420110700d03900c0c40b680607600003d500c504146d6444491000140101d04203200031502c03074125102009500c01c20340144801c00b40081c014502480c10140152094080305000e83d41050f042d54203010070f0340301c90300902c1200702d001d40c610300440c0c01c10740004d040204104106040c005412810089108009000c5034410207028211004102910000d2081e200d2640040c03c0c20114905010740c58140360701c45c00810b5001c880421110365641240011400d4483d06c6601040003402020500403207900180307241c1d01440b03165031801440280240c0c2c0e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 166423156 1250 166421906 166421917
    0x504180f180b0a0207050307060f18060e0d0903050c09061311130b0a02030706090c0b0309030c06070908120d061502061b070b0118090804080f0c0901050109210602 72
    0x603076a44181d581e0090021148072560400c110450640c90214281c032202c0c0c2c0c0e0700c04c0c110018025035845098091648a9a010700500e0703a1580301c2804461050030715030301500003200c0d4100640034a14030840c0c203e0051261500300d070b80c04800703450008508010011039003402000d80348c0000952111001c200d0840c03281071800040c02600b9502e5410002400c1c000c8100c03078001c0542c48804008218ad415000820780b6180e580c400380124480107036142011f01090180d111a42030748011050107070441c80030000d0407000e10745808440b101d949414080320b620fa040d00c03c03075041ea040000701e0040c0003c89030081401c00c91005000c40c1269941490321500c2c0c243d41d41440058000b1001d0000842d09411700607007030a8200f1526041c00c1300d82c2c40300700714580188a10414000d07003e41e5005015007a030000c001c0c840d005044941c0711580c402d4020b407910001e032202101405a5084c5210914240160906888060352007072640350a001e499004102841920348503091365120880c00254140020407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 166424406 1250 166423156 166423181
    0x301090c0201110708090909031c060303030b090403050a11010b0307030605010302030d050405210c1201060f050904080a030903090b0a02010f06080d0c0b07050403020301060b0c0f07060504180f 85
    0x6101008140020300712000740544540c0f03a20104002000308984c841a107501c0c20303007200c05400702c0c0ca4140700d051035881500c944010b00e50f800700305821000103030341c8080c0450b40203850600420318000200070b500c2c4411030b4002c010940c00e000158020303204044c56851a00da039000007030f8040100000030310b000c500b0780c02250303510380394001842103085c10f0107104080550350511074241402e08e03000a10707102d6403008a84003204c0107441200707100c80c01c00444001d000003070210218104030a40c19400b800c1c0b03034094024560480e080c00074282c01c002415501c40ca07002a40b00e820038142c0c2808502a108101d829020007610340008600126120004e0040c102282c000040e9080a4030611040d55000d50007072980b5040081e5001080760040520f111165204184650540e1031100c103031028080c1e504040d40640c60104c0c0482c28480280091008110034000c43d404045460340040da158002c1c0681d00000c5e5040c0300c00c014000c101a142c00c100b044441011034203040d050b40e610120380c165038019 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 166425656 1250 166424406 166424411
    0xa0908070e0702011d0c0105070305040b0c0f01050105010e01080f04020d020a0e010608180c010f03150902040305010b04020c3a050316180e0a142d070c1401060b030109 74
    0x400350b1038092107404400301000d0381d260f030038111802e03189413900004440c1034180440015071500f003512a204440107001c5030340c2e5a0342c0301d000f0400903554031016000004002e40c0380c4000070800b036014040b0308540c100160f4802c400c44e50ba246420100d11805041260042582500344005a407907110308030113403c62a010314010f6240c410014182c2001604080300c2c0c2a140a02e80301500b008074095407000750a0805130024614458114000c20480882d155101000380000c50748200940050086902500c005d00c060390515042204030300c501c0107210b015500030a0189813486080900901006528010408100d00741c0510300c00220403564003c00110000304220100c000c1068442d0286c01078500311025400ca11102c14507600d482c06150038550902000403541195a044075180d0010001740541e00d0070300030410b0390150440b582e4a14007480c80d03150701c9010b025003500a803142c3d9040d0398506540a0646681286290310403d010055403540700c0414007882d80c0000f54020300348500300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 166426906 1250 166425656 166425661
    0xc06070503092806020313240f060f0501080901091505040b0a0c080606250b0103021804050c0603040204091a100906080616110a0b0a0b03010504020d080a0908070e 72
    0x5181c00c2002d01d00c44030500f52880120301d0b600c103000325414068954040001603694580400c2006601c8007011300404107070703000e0000740c0d11708001c8602139603601c4003020a02600d188006484290340c21402402040100d41104100030740c411911203800c24000c0c0000100803895440d80c100c02c4581c960455520398460040c40104000d02001a50000100d00d08020403c09400d009010b0310014002e00d02c94240400c07107200104003c40d512950481c1c0b010580f100740f1a52510b031045070801d11050307102c1c2213030a1404004a44418101e88100c0d40f000140a60b907040904102550300013500590b041955026100f0002c0c0507141405502c50342c01e14002910f14182440844c0702c55140c012403851401c0c0039041180381d50000702d1507001180b0808044040000348001c503480c02c041c05034025248036031544c0c001030003541ca02190007508090020301c0200e00daa4241402e80301d0541c3c0081d085100e448161010816801c00360003807182d946082501c040d91480c1042c031f4040c1c03a400009114004406 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 166428156 1250 166426906 166426921
    0x4080c010e01020d0801170304050a030606090b0303120a090305040b0a0804060c02010b150a2a020126061509030a1a06040b060406050c03090418020405060103060f0302150c06070503 80
    0x7070016851400744001c24442c202a00010200d100c10700c1054000e8000c0714002580300014000e0760003070900905803140c60381e52814490084d080c28452101d029107001342110f424140441242c0403400c3c00140b81c5240d441d400c452200808039000b040d020400103000200c5c040300280010009203540703036117180319424a402c01c0390440300c004000f1341c25a85090084401032f150b10100c00718106440b280380d9128000c00c04181e4004100a00141c0e058005442d5811400317070800920300c83d28000c1c1d96402082d010440c5c520707142450240504030030008040040c601d450181c01e11441e144c0065109030815109074042450300e039125800f2500044c3c1c4d00030389018401e010103090f620503400c941c240590a1100c022030124440c50003128100b00e400203007110790300400c01c00c55402c140040c0040041034503900d020328001005140c124070039400c21020512940c400d020b130800381c41181c018010f0b0680f80d41d003004040f007864a00c20030318100500441d080242c040c021140300707401d5500c41e107a80385000c28 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 166429406 1250 166428156 166428167
    0x201090902090f060304060f0203010303090614070b130302010b09090a0308090102070308070503041103070e040317010f060c0f020301020a050c1c0e09090f0609030a0f0c120c02130204080c01 84
    0xc00405a1a10620200400d9501c1d115241c2c10000103803250342e542d0b00c2d00c0c100903002e45000801621090f000100010406910000881c100c820950315403021209000d900d81592003030000240035100a10049501c11f046a52144411846800001005298100070071001c09085a03850b1a07504070120f81000e154004182586c03042201c4000c41c50401581d801410010016104c8810000003000003800c000f0241410140060010220707a482d0740d030f6803203001c01c40300c088808a0003d1220351340b500d05200c42e84e4049042e02e03c21703404282d40031b040080450381989800300694095600385421005a1820b10080c00d2000c001c0d500c00d5070301d181d2040f446103002440400c034100c01c1c01500c1c1c451480750b8000740e0a040e510301260b41c00d1003904c0e0300c0e54403460550b600c024a00e01c1d00410045c05403002c4004000c000b01d456035202d90840a404400c1034689100c0c104001c1c0003501c107860b0601080e41b040703900c481114802000c02ca910039090154404982240e041200143d2100443c2412036030440e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 166430656 1250 166429406 166429409
    0x3122303100902131215090803160e1e060d06080303040c05031504020405330a060c05120c011104061710050d0b070908030a03020909090613031107050418020109 71
    0x42406519105034144c114a91808a119415405003010742c03001c00c02040305408080d08001c03010030701840c170072814481c0c4e42d40e1080e00ca03603500c0f02e00400080c810302d008000514070b640e03004000b0084081c01092480044400841d500e0303100c4d8041148117010a4640b1072f0324060100f120007035840c0c0c0b4042ca0b0900c08480250851352080d4008012840300c40404021194070980c151004521522400010100c5481c910003a80080c0002c00308500100f810f4054004408412285045115903903036040c0c4001e60007c00c0602540c0100c0074039000e121070384000300388424080d400011300795643c1d08003080a4000390071910010350711a521408218445030807580021140b8071244407640b0b45000a0b54450900e20010703d0007040f4000251203a010760f617900024503d02041d41d0b6564040700e030090095100e4203190f4480c2d26400082440b5140005172140300f03000d02c0d022000d020780607407800e4030310440d603565001d128490145e0105140c0c851f402120050b0300300462440c60300305a8070014103040241e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 166431906 1250 166430656 166430669
    0xa0c05090d0c1403121905090402031603060f0501020d0302090a0302090103050d030c1b030c050f070612051b0a12230a0b030604020114070204090807050d1403060105040312230310 79
    0x1020182a01c0d42d511703011100d240a50107811448149480c40036900c60042034075041c4c2c010310120800030510014083c1c0102082c003a50308101040e1500580c070a00c0e00140103003030050b440a448100f015020303500074400040f00802d071503003080d980d500086460800760800c0710b040c1c000f66034a43c0e0281d00b50240525680c5541000c441090090142454854070008003808101440e8102814010140201c01c0d21482c00e2003070380e000a031a124003511701e1312000300c2008200e15100000301da11010000c0d200e20003101800c100d26081c400d95085880007208041030b05510341d10351003404e820b44807404100c2c85031b00c00301c0d0200d15881d100900004075240c2d0b0a284e8000d40001e410080180c0c0d1200d4540c119500390304a00391a002c50703002103801044661001020070800181141c00e1010000329001c05021702c1d40c0f00400034480000c050b03041e00058840394017003801448280002211801120944040d61401c00c10340796081c1807000c0400100780701c41f25114000801c0c000310101000c0410060b000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 166433156 1250 166431906 166431913
    0xa180303091703031312120608010b0a0801140606071e0b061807121d060903090a08150c0717031009150b04090b060906120a05060f03060a0c05090d0c1403 68
    0xc10b46101c0481085e0030340028090000c05442d407100324003860746000c0400c00c2603020445542c6549400f030003454801803103441120900c100180d00b405c14082c44000d1740c03080b2003403c165200e08041c0f10f0103030404030b8201c415110640c042c0d42501ca00c01842a01c0d1401000c200100c0e08000c1d0602c200c00f42e608040201d04d10603d810032002541255070907060740e540c0c480000300f1540c40802c00c02100000601c461080c06503c081c0880104004090090311f1001c651000d8520341d143c40c0182c0e608808040b0900c00b40a103030008a0b1840c0c000090440700d40030305843c101a00f00403400710402d80c01101c4444000810400c280141105032050327101c10100c8420188900b4280307640070a0a0060b445020142e90b160380980c000f40c2c803000c0945807804005007625441c2d00120b59510450b039001c03107148130f28a1900340000c0070b44c54071103054191803030080d014040989504007030001078902c500004060190401c451400317900c4460304070541a000c0d40808045a080c48084148080384048041c401d52 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 166434406 1250 166433156 166433161
    0x2010f140105011b080d0608060105030706170c0702060904060303080a0c110c28030f1b060c122003120105041416090b03040b01080d031103010b0a18030309170303 72
    0x342c00501201c12480b0903000d41c00f01c08013610303200403544205581c050702107041040c0052402c40002d840ea051303500840c16645030986800e001c90b003000c0c004412181d190b00c0f00012810000d40c0400400c000303400940014580024100840d0a40d800c0758000c800044102d01000101fa116210b106414000d5290034408841580c1c15141d4810640541a10401d108060b411100c050004c0303522039442006880000b081d81c3c1e0812000c02410070704162401c040700381140e0341c0029414a28810b4881ca501e035090440d81c1c540790402c3c540303469901b200510041c3c2d0302c2c0702c81d0154180e03040b40000c00110011a601c440650f050001204107910660255013130004440300780c2280d042d81580420800782041640d4100708017228240704947c0080d00c016400001d210900580c1c0341424140d44100044448100c88804120100c400c003002800c0100340a000511081c0c3d840c000516100e6528640b030505c0340c00202c032a0021100036441240400c0c21400c4c2003241140441504a940b22410051400c51 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 166435656 1250 166434406 166434409
    0x6070c08030f0c010f06080c0f0a0509160f03050c0f220315150b070809180702010903080c030906070f050723071e030303050c0d1b0915090509130506040302010f140105 74
    0x40308c09030090780c41012049900c44047d203c0c10410001448010444c0307a9a080c10310f07032603441c207021485000005600110700070440d40640502406078181c0d1460314500002000d070104c0b41e8000e049a130401011455114211065229003c8040c5000d003419604000c030340da086200721044500746a007500428902000101000f03070554609a4203c41a43e544010420001d444504e03001d0080c07001490600c2403209142d0305500020750603100b9103641819454240700c0070814003085849c6616544458000748040d4450b000c201c10341c1482d41801410314590343c0c0d035003581114075407641d0f803656a5184030b5041210100144001400107000c1d805481d107041500c0d00c007111050002405242c1c984010500300400d25080702ca4005561f101044200f20650313070705907164200c3c400c1d04005000482c0c080303801080d40282503454400c6840d00950b1038a4a0300b4040301c90001040c4410901880052002040b41803000d58400c510030b500001d107a0591080c0f20341214002d500e0745500040450051105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 166436906 1250 166435656 166435663
    0x9010c09061b020105070203070308120a090b070e0f0d050109120801081b0f0913030e06030702070e151009061b02060a05070606031e02090903031506070c08030f0c010f0608 76
    0x809060085002c0c40c4260b0006076070034030038264000e4041c03141d51000418032003080042c06941500c110800b00303e07240c0b5401c0e41c050b0303109210060000429030020407040c500039040c4280c0041702800d60038907880d00c40e00054407529018810340c0c4a9442e401100e04000703c2c505500201000d42c20102860350400303c8403130342d681c06244c1404420300c2c3c400000b031407941c401d1605060504000e0000ee080d00e0301010032030800050003001c0300800c514a400210500c0d040e0705807445401c00c0d078001c1044a140014880407014083d0101020050b000041c00c0662501503078000c2440b03598542c04515031519000401003c40110582c0184449102354001681d8803c120388000c8400e180954640d441414148000c240d0381d4402000b000c180007100420700030b80c1e0302c450001402258200300c2580d0700580342d0380720305c001c0b100588482d019180440311407400502406d0380328004c0c8040840540c440c26901d1560344464400c4503a0320021a038445244e0382406484444800703c0310501c009803030100610340c4e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 166438156 1250 166436906 166436927
    0xc0f0d0308010e040302121306022413020f0409080307080108060103150515030d1d0910050103091703040b0414030c0c061b0616230a0c02010e1809010c0906 69
    0x2010400f40000c00c0605100700134401d41c00c080d00f0f99442e603444c640e14005032090154071a20002d805509005450b503605140404458044482001c0c260340d1104d1034641200e03520a0200e1b880290406041159180c42c40f0b1440103a01c9500072a80d03d0600701000382c41d43d00d051740001659402680140001100c016600e91031014409002c02c0646810b0b01c2e00844d00f5804c21000d400d8850b0014a9100e503520407541c9000f25009180031000210751014000b04040455060900700e031f84010400a0307512a9100b00046030107200c1011039503009d41d50300d4a41c0d90050b00d09540340c1e0601c1040c0400c0c406040000e1041710348003401107240408034070040b13440301e082c1d03110307507108200c0450900b00609a00384200d809103290400cae2001883c0c41801210324064080c940c10010700c034800f80311484980e2a02090308113103003120003810150152011a0003c2034004128100a54105101820b03101c800031035401c00c45c071150b80744881c58180905421181200c1d841e40c10460039140030040c003030f0401c03030218 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 166439406 1250 166438156 166438169
    0x60f030307050a110d02030313030b060d0804350f0114060f04091b0906090509030901020312070302091c020102010c1821120807030b01050a050a031e020301080c0f0d030801 76
    0x281821507440007a51148091401131f4060000040107420a07003410082000e50f03100c2c1d11070780c0241d20f07100f00b0b10004629a120080c000403007040140b0001e9901d0824801c9070706c400003c0082034032000c1f079200401040104503040c41c0c0c070403945651617240a00400d040c040391510348000928080000a050100c2c80d80c4107030085035502400401e1041c1d00054a1401e40078000745010181e035007950b900108981e224800100d031420012861840010088584241e0141e000f1070a2141d13406820040c010b0241c005814164200007034640c03900d803005800c0c00451200c645020b06d80280c0006402d40e1680c40b0b11404000d00501c80c241505214414a010742d241070721088014907402d000c22034444640c84003d00303500306626141824070b9000140078030889061384d0074440d0708401001511036006201c030341c00101c1c50038460030140d41d100e0f40c828000f44103100e4483d84c503d1401d0300c20030300703c0c0c0c403e80284080360001c2e00c200780700e0300300842c45c4064031301b0948080c0658015901d0051000d2018040c92 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 166440656 1250 166439406 166439423
    0x70602030604090b07180b09180a0b1011061503030a0c110402030f190501030b0c0a030b0a03030509120303040c0e09100501150908190210170f060f030307050a 70
    0x79426071a030b40d01c602142c0e83e11040a96150a042c1400307000642c21046030b040e60460903401240000548040d540206005040c1d110200038018803031041d118003d00d44a062036985501c0c080d50303500d134281e006504807951600c440b0003070600780381401c00c4402481460400700d140103240d1103480000c12104100050726100001c07065510f040030040e003c1440c00d5501c00d0000c420b12510061622001703009080d1b80045410040e01c1b9031a44044c0c0343e007484050700d900c1c000b00014407140540c078024a2200298500091000241c5001038060340340c980041d400518049880300c0b0318200414030210020038070004605529003075440940442003400307046144980c0c50086400c90b982080322202d0901d01c0d403c02c2c00b296071600818211000900c1d0418000340384500c000480b6400410260b1003c2c100780c4244040324019001d001410325125151782c10040000b03105054210f403a10044d010b5400e05650850f1820000200040746241440d250b100350010000000014000505036410030b41c0310349003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 166441906 1250 166440656 166440661
    0x30402100f03150905090c010c050607030b0609040e011a0604050a2d090207020312070b0402010c0c080d021e01050c0a140f040b030405101b120204090e0313090506010507060203 78
    0x110050140356185800e080002000400d40309801c0c0c110321b200720360420881d4001c140d0b1030011204030307840c40b10103400358000ea804101958030070341010a00c0b107400341500c1d1524009801080c12541c140306204d0185e55150440e40234407442d49e51145000f80b0441d903150611342000001034955100d4400c4d009402e40c4014114003110307503800345140c0341c51545807820050f507540880c0c002a60110000300e220f40240384c00b18aa20300144196200036030060065820341c2e8950340151070444021030241c9000c9100c2d540024601070410100720720790315540c0070b000d5122000c070b01d5001203400d4402e000c045034102001c0240c0c01800380151602600145000da00984103450f0380c3c0c4c000c0c45412030100d44c04100040204076240410001c50045d03115100711010104807608060490f199444401d00c07000f02040c1002145125000c171071302002c445440145030540e1144030f0000c8030340c4018615442c1d08007150035404189008680d0008090081c8180907900d031400c0000e100c1e1268500042000d50301001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 166443156 1250 166441906 166441937
    0x1a0709120b04122c0d0f050d0f030203010e27060702070303020f03040b030619050d290108060106031e090f020108010b0309031b011b0905030c15030402121f0c08060603040210 77
    0x607640717040e9001001c4003622440790500e10307103c10010301c60b4804500505540800383d8400c0c17003200e0403039000c503030b407615035496480c0030080305c00300082c1480041c80401c0c00011101c40c28070889000b005907800800d1124a5890044d0808600c000c031001d80d034105000402c0300010380400c481d40300310b0444031105805922881c001c0745080c0d5410184d040702800080c1c1040045c0301041c40d0303810406051000e01400d0f0000002c1c0700002c2400360403640c0e04120010440c0f50300a80200b080b01800d8002c80c01251010070004046802c91b41c426540000c150304001d0540d40c20080d0140980f8204401c240b0b9440c0c0002000d0380d910400944180b488003c0300c2c90036840b0020342c007580c10104000701d0100d55025402d13000b06040607038010070f482806040c809100c240362800e4850b50b50301600390b00900b155180d8013086120307129881906068012070058034007040701d042d507040005880d01d5001580482110008140c010700520341c074007410b010008d020260382c50300303644000e022040c80c082030700c90420030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 166444406 1250 166443156 166443169
    0x30115020a02030c010e031906060509090c0a14060c1f0c080702070302100302041502010b0301060801090c05090a14010e041203060303020a0b0709090204090915091a0709120b04122c 80
    0xc48c0c0031300c0006a40b4010400100ea04003c08580040b51640c2240c0c42d01c0d15a1a180e8950006d0280c0c020b984090810803d002c040c1310b00501c0b5070080c0b1301e03414190300a07020360801d090b0011207a031443c1c0180c11b94845200ca0720840076a610946002d17035141c600b16801a40d41c10b840d0001a128052105402403814440d80480d0042c1c000c0300c9002e001458000c40113070180031202c1c40c841c401d508014020800d050148184c40720542c01035080341c0418608004e1105110340589950040d54840740c000100c2a11103405500801c89084140c8140c6000c0c288460005c40080000003010305229040010035400120b044076603400c00c0450010f522000000c1d5600320f1a0f82c0802c00e13842c004074000650300300e42c0d403100311005e001d41280d004203081d10720180121003030458010038900c00356140d607041c2819140e000341d00901609099400540360a9a62000d82400300c08891034007010b000c00007040030007102804102458213041e00980041801240c25000a22031102c11303515500921002da6281c2c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 166445656 1250 166444406 166444423
    0x3010608191d060c0307091703090301021c0b0607030e100c050607050a03051e041407030c030c05040b030a11100912080c0d08150607050a020a0b030115020a02030c010e03 75
    0x140030045040001e21000100c0d0407015a05424040c21002404107203800c4e0440380306803810f0b80c1d401600340c2800c0c0300300c4c01c08040c41d01c1019280702c24807000b4440d840910007815040c240301c084400c4c1e544010403040c2621417880b00c19004141c14009000000c0e04002a00d09540e02290b860310b660504020403075100741a4030016140d440b51106005109822600912040c0d4065606100030f9a5014014483d01c00d41561400e00b143d0410001d804a42c7c088050f500b6034800d174050b2411a50781c0d4481c4101d0343c20542051b90300c494480d908000c0d600e840d00c80c68082201c00c1e0301400402030305403282400e804913440003a000d45010180000307503510840c1c04601a20031151910030400e005e0901c002c140c0c00c150220402c910580035075110080c0640c0016108107244102c02980410380400e000319600b000d40c0c1203816200701140000169111000c1401901141100716200d6240046d030300e81e0458140303850703000d54100046400143c0c40104a6812510007070a04c000850403140100e85041d260 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 166446906 1250 166445656 166445701
    0x90c0e0405010b0414030309030c090705120c0d061707060e040603140609070e010b0301031b0e04120806010306031a070e1009080601060f02100b0102030c0a0f05010c110303010608 79
    0x1070034008641c3e208801c002d8419610261140203104410740700303165980c4078000e0b000b903244e8011440f0310198a081d0440d035600c48a6842c0c0103050120700040112105020b440c0c9100d49000842c2c0c0401035100c0c1e200d088001c1140c0203111044480f00144940c694503d806402c08010110b107441c400380e00d0781d401620065503c408502c184902c40b04140f61608400d85415138980120b0900140040e01759460b81d050710100401c05107982d02c1c40d40c03030598401d0050190180400d464100041c045070205d0641c1c4981e000b800704100f4400442c000422444004181906040c03070141c090000c208150700c0c401115440b032400008641303e506042d10414003680c1c0440d80001e030200310300585e99000308518120b41c9400c0440750181d0300c43c103040e03616a10344900040143d00c5800900c034654560b400580d5220010300540e450b04540516590401c0085141616241b60030554102000424450900742e1905d900e424002000c0540d1016220720061103000100420303007000c01c003032a80510005048100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 166448156 1250 166446906 166446911
    0x305031920030105041a0102030331050f0d110c01050f0405060f040806010e0705090405061504080f1207030c022b0609060f0e101a030307051f02070309090c0e04 71
    0x400035075003001a842400380c2801607040c28840050445041c0300d014403c6070580183d07013156030329500c107440d444011307a400010504140700078161900c00424903950354003a1010b80000031807000a60f1030f01c4a0b40011100f0082690358803917030414086200aa06034007480c105540d02e94003800a403441c00b9076009036500035000902005944290030084c01215081e606440203a0f0361101e03000c0c081c44c0c0807075150340813500402c040601d900c0c0c10780c0200d44c002070041a4550301505a84c240a00c2d0700301e0703001a212130b8084003402c45070303a03c01c0148102c2c0e01841c5c8d001914081503031b907004000f21810b06000340607242c80143e80320703413080240040501c042082c15000341800142444000781044c42c10544401c1d1400d880f50942d10b4080c002d0000c00b50506004249075180392031428020240c9a8070a16070512203000c5c079445540070310080c2200740c01400200364424110844100d60340185001104036481000241c3c0080d410003600c0089aa0b4404000350b038040051055a0f020001c401f2268050f1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 166449406 1250 166448156 166448201
    0x120901140a0e12191707060606030507022a04110d150e090c01080606031909050c043801030608150403080106030608030708090303090a0909020f09010303050319 71
    0xe40c0061249000302c0d084480740e840000c03006580f03490718805121020b421010150003004103a5a11102d001180c0300401da034944111500ca88080b43c80a400138800203850f0400d21020543c10040760310782034208000310810f130510000e40036510b404d031400d00f0f025a4070745091002d032791020350603507452141c100c100f44542c501d05d1580ba11400024003c200d05180c00d900850309506c03000844501c40d41c8180c40f803008540300c1d030b010028950802007001c210b03050082808a002156030044018152245008010040e411401c20003036a4885804946500300381e0300006008484100c0c08440d000c1c0000d00740c40342e080388401200540600c0d00842035501c11140b800000f490305441952166000356241445644c0b80c031421070580d0058440d030b400390b510921014010641c543c000b41501d28005003140d03d0810410041120b0400f145d01c16841c0550b640040401d6007402c10b80a0160401210100c0f070325030440d6800ba045000c041e1110001031211070700d000b28200d09512410400604088041004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 166450656 1250 166449406 166449427
    0x103060b1c0c26060a0f0609021803060106110d03020717040b07030e01020c0d1e061506020705060310120c0305011505190302060a05070305160f03020c030c010212090114 75
    0x901261003400091140b0364010443c240c15551030b90100901c82c005840181c4481c190311002d0444101c1d4002215a00d01d00020300742000d10003808241402802c0208040c0014100350400c3c1d0140d01a009120044d00c001e06181808110140d84842c0e40c04c0c0180c66042c21b0400c540e030848182050450200c00003000301781c02030208041d141061080d03880408041c022401203072504d0080310003070b42028401003c800001c240c08140041c030504181460070207e042d03224241618200094100760445c4020305024407581884402c02810040e030300d01d0720b0b60806190041c8039201d07034400c40b0310003050701c4107140401c001c440d8254019a000402403050703104961080d000040184a4207208807001464001030b020b40356048022207400030010f9003003003124201651035601c0550200e0812204100114458200058007002c50b8010044800d03800010718029190121070054548030358001c0456807410303a80014450105000c00b440c940d1251070a000607a0b80c031003062990700b41e140011410f04040e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 166451906 1250 166450656 166450673
    0xe060904080c06180c0d0b0105010c1a0c0403020901143111090a080a26040b0a02060105150c07050111010209060c0d021504050c0108040f05031204060509070506030103060b1c 77
    0x40b1030101040d14070304090302c800c01241c906c80d108010080c2c0b241400401071580200c80442409008030b000380240359509207400400c000846c1c1c05128044085000e00550425014041c0580030324010b041c2402003a031300151030b048270150031030400c9040451101103e03442c403c42d1190b51030740c0c1e031050094030280020342c1303980c4e0000c1054600503007000303000081c10040000d072080460f400215800840d203400840394561000707515841c0401000300000a198000c103070062060503883d50180c03999504100401004801042203200d410000380010300120704049903c5040312000d080901c8400e00045150740a0f000351201c0c01e0748054003280c945550035000c01c1c600348101c03181d420754092044104022010020507200500076900031410040310f940503100b2a6002b900484404001070050fa803114510b600a550a000d816000405d002c01c0004500880d0b40002c03055024210f61414070002c02c0781400140b2020706200e4949440c0781c12525405018041d001500c82156542da2103410000f08 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 166453156 1250 166451906 166451941
    0x11041b09030b0903120a020a02010b03031b011808160302011e0b0a0803031909080d0204080f07170a150b0402160b1302090736050f06040e060904080c06 67
    0x550182c0c400005016060120840c0d022002160303500285889040102000350000c1d9261070540d0340e1520142c0c03280d42c0c104041c11800681c034901034000b12140368160301b503c050812111085d07913009440d1002612a07000e4441281b0402c3c11000003180c40d0500328090304c03c10f00800841c0c1480503022100e240e4542000910b04000c0c0d410a000a90f12a8036542d02d12040314108102004402e10410000c1c2642062000c103000343c0041c0e0501400744000710480c6d00a50056081d039129941390ba803001e030103100140040500c1001e010260700c00d07003805500c0751400d00009110004a501140d0b030240164000d507902c40d0301503c21903c0f58808442a6958140001d085e1022000c130400907a60300140e00c6100d4603d54054106115a00c80d00016252040360340c0c4001c00f2208007141c44009000600400700041e08000070f19209145040b0922840780000c950250242104010038402d0100420659030805000d80700700010350303540d0070840c580f4064100044054002c10003403140b4441c8401040c81e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 166454406 1250 166453156 166453163
    0x30903021c05090d0c0801020315030f0f07090c120e060603060a02041503090302100510050f03030403170702060d0203010b0406030e0105060307180f1401080f030c03040311041b0903 80
    0x81034900001c036400420a0300a0985000420401800e105410401d01520070544100040c8810f280c4031102c95007681c00072500e11245184902254403c5d03d4100101994011044060030209804211160702c0d03a02c98047c92000c01e846240d00f80d50603120b80002801c640721400200010b00204c940103443c0c18007031342d245201c0d11611000c9041c0300c07194800c90f402c65030101c075041010340c4a00c409501802d9408030a13419800780d81306600c44402d40f402040c7c4217000310b0b070328102d84900b072104106d44517081103ca03034000d620904c02400004c1501c0c10203c1015000c10304281c0729143c81c4001031103441100710303c5030f40500100002917a031611a01810a030390a503181441003902c43c6403001e089400c215407417540f540c4480c5040200918036040d44120a64180340410104103182160040d20300c40d072014280300c45540010050b51a0601c01000350601c564060361420a00320322956987c003650001400d80740e403500c0081c401e0f41d51030f442032006604a100c0c48082104250000d404208544001c0c2c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 166455656 1250 166454406 166454413
    0x10c0801050a180c0504120605040201021c08060f0a030f05030309011b0f030f0e01020a080402120706140306041509050417040810021c1409011406010801050d15020a03090302 77
    0x4569880d00c1105041a2192000ca0b100751049041c2420b0140c04c1e4000f0080c1400410400803907d030000f00030003c001c0c1c1c02180e000c100d504252000a03d01a01c00103500168032051409107001030b80665141c0d005201180c244644144180002d07a9000c1c02e80d000815a0070a005240300700700012025610400c0108001c0146800001c840310b048441c3c90200340000765450415081140a9130240a0740ea0b0002000100740145410320340c00ca80c081c000510114004004100841c90700d515001c0a0329024405011264500790f000390a150000160401140002c00010000e0311030b43d0100743e41650071341d42c2041e501e40d02d0341444c006000a69040e2172290541030802e19245690049608441040c0700801c405c01e078280354400203410882241540001103803068810f0503042c0180c1d588844071201041a509009000c942100d015200e15807c02d4005c400b0040542c0c0c1003007640703044a000b9035402c01c1c03400040c501295011020f03403ca83c0d00500c04110603c0302540740d071008150301c0c0700380c00310b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 166456906 1250 166455656 166455659
    0x10207120e150406050a110d0c061a0901030305071103030703170609040b01060c020a08030409060f080105270c12031e09031207140d0831060203130c08010c0801 71
    0xa202d8800649850702c880360000300002c00049105000420610310549070200c42c102c1c0240c0d195003803903030010701d1030001506500f40034240030340391149449080c1082e040c2c400ba20289008642e10303c805101c040d00384400800c0100500c81c09140c00d0101708001801c0d6603403a151480c02404003e40e074602400385098140008689040c500c110500894211040e680d45038a000012035603c00c4410040341c100a102c580003800120402c06030000e006aa07101207800d9092081107001c401c007603408a0701c02c1c0e04007000c2c00402c031003a1300c03010000303002000d4a10300c000c00809a68070b0440003a00040e040202140c580307500e000048007170080310000b42910030645a80c40801d900300d00414121a42c903401407000b6516011401d001421120302c555100140b1401d072540d410b00380305030f8901100c0411500400c1184010502401000e841502d482840224030034180c50a0b00000c0224000d040c0d690000118040c026001c1c04450300c0c0e580034055112160b00c0302103482c0a00502408403001c510344100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 166458156 1250 166456906 166456909
    0xa0803040b0a2304021e0607120201050919020409020a05030a0b07030b010201020a02070e1305120c0c040203010e04020f060d18120813060c0909060621060b04050918010207120e 78
    0x300c41c9580c0c0b6038280501042d49130341c2c00b0000c40398170315803c0b900b581c0e10384c148100f001e0f22650040c0c0120760003040c4d40c5c092159103c0380607094640040110b8a143c10109a101c98035001d512002221501038500150080355480414a510754a070400c69161203490311640030080100582440f501483d40d05001d11002c0c40016403d130300609240001603009a0000e03c02c080d0000307002035004174008410000040c1035252641061580079542246120000300d07500000420442c5040c0410309450451456141151504082030060002407045d108a620301a003540d8400c00d4589a24409004020840010082c4680f0101f4594112508052000fa8032602401141c00c940f04809050900d41c0d00e06490b91050000c02612008400340300c2c080300042007180c0340d44140005484151200d564000c40800c18540b0102c01404003081c4608200f014808013141c1c02c10b443c00c862003070710700070b4454444a46240360701080440c0e00140350b00c040342200510110b80f662000c40709d0640c55000308060b5000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 166459406 1250 166458156 166458191
    0x504030311041a03060d02060a090e090307030512090c0406060f14030f0403080a06120b07020f120901120608160f080d02060f04050a140303100e090d050a020a0803040b0a 75
    0x124400e082860030b030303540d00303804101001181d10105c02000041060300070f500140d003e0700541c5038140040c0070000140301c0359842c6a41583c108084030019801c120242d50000c01d40d12810b82c1300780380b10035081d0100701130755010001813180c81c100600602001c2d07154400240300b8181242c0140000d501d803803040c9400c07042e40f03040382c1c056103180080d240c940c4d80302d07141500c0043d000752000034200e580e1031000401e0f03506e40d1101b000b040c2c0300b085500c8050070a20802840d005840072402141d40041c81d600c0501c16a1104842103140d00703007445106401103620725002401e90380d00151160050310b42140f10100c1508200040d90707611940d480d0119280d0400713a54441c401000a000344c0e01c07100c081112422405440f6501520a50071109008050340d5403041c00e0111001546890f0300200c00c2c0110640009110383c080c001d50740315030301103182c0002e80559400104010703800344100000e408031818800d000b040e0b5460381141d0115981e0407c1e1500602540c02101c1070420340e4513000c00c01c88600c03d0030707 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 166460656 1250 166459406 166459409
    0x1909021c0212070c030504090920010201020c07210b010906170610090b060702270601020f030306090709050303030705040302090106030b061207020f12220501020a030503070c0c0801050403031104 86
    0x503507400342c5603036100340689150324038180a40074468288030000d440a018022540003500c03e802c215895001a0741d42c070402c22100c21101d0659006020b2000701c2040000d14804450002480030290f0030300c060305007030a080c0740001402c3d0002e42000440e09420750b41100046441844c6005841b0b026026516281d0301e05030303108080180c0d1078604101e041255004100350244c020641841e20f503a42d4009103050600310004800328515015840048030400e4096612030310030700140252512a400f915108d01c0010002440360441c1ca01185407030b841500306601912000d030031290760f42085480984183c00c1440300f24855001d980001c07841911900031170410b410b000e0b01c0b079414070294079248400043c6c02001c860451007503c0ba0705943c0e4204000449040610f10001d0f40d8400003d1001c0741d05445c4080c40c11205900088100840d0f40e0006100d9900390300740c680702c1d4407921840000c45850380541000b0300012039410010034103003c194031144c01648241c5040090b0801003e00740b1080c082c2307 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 166461906 1250 166460656 166460677
    0x90606041505180d06050f0a050c0406051312050609100614060d0f050a020409060e09030909150307030b1906050616050c090c090123181909021c02 65
    0x2110605201c90740100090000c041070303c071850500020081c041016114050702c213980144c2c5a100340322000d8800071034160003260341d1006001e5454030007080000c03849980708030700c1003003c0052510b008040e61525000a8000f213002d503111040701d41010740e0b0710041541d1030f40c03039401003481590880c80c15100304412221010100c003500380e000b4081020039000700c0500c2503000d480311841c00b5a489107100d0103104021700131005803101d0a04113850125440c0b5000f07030b4080501e81d0107108002c54008107803103100100320b03903090103550340054802c02250840241f40e0503201e2440b0200c10082c205038950b20582c000d0140c48080700500031440180d400c184956604280c04008d0185006402044181c03d5405602110035801c08600801c1c40ca020885000c00c40100110b0381c0001513038018103003001c00b50032400142d0503a00103020800c041c450360b0030003182c1403591115003c4544441003010001140d10030a4000940e84240143c003070760101442d080000c0d044128031895184901c20f13140c02e20030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 166463156 1250 166461906 166461929
    0x7111603020d1101050d050108010e010f0513020f0607080408100c0c030903061104051201020d0c05030c0f0d0b09150907050c030315030106031403070209010906290d06060e09060604 80
    0x4652100303580c032590300f040e140c104075007044824032448181c000c41c0e000b400540c0c0006010581400502d007100e107100c1400c003c0070b0402c420300a1030901d54020001c0203030121400c000302140d08001801c3c0d880f540030300500c41c0d030020400183d04000405c000310105514902070142881e80c400480750340c41c51440003004100b05500c14000725880c0e40c800150000700641e01881c0c140c442d00001c0d407000200308506256900000c20540c05080c0740100920401e45003002c9040d410301600e100404d001c0c421680c52200c4d07001c01c1441ca240802d8101703414030350001c2c0440c1843c4c14041e6036110300300720000009003e0340f0080081425030b03103d28111141465084007560950310707040c01e50844c0d41c0e400c0107400e50664903248080085a841c3d181c210189202000440e03484a8a2062040c207400523440028600d10381102001010011203900442000007541e0103994a2070754110402401380c0710a41d80694a4003602086d01604800b900f003a80504039202c21440da02d100402c0081d1155006031030381c2c0a07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 166464406 1250 166463156 166463179
    0x30201180b03040f051e070305012412030c06022701141c0603080318010e030f0409020a020a150605030106080f0c1519030203070f031a0f060903060711160302 70
    0x109100c040c0150346114109590090444907031b032855043d082281d1065541000d081001081024410001200c000000502c0000c0100510386001503e6114220003e0510311100041610078030f400d01400e6808001103440b101d030b6038410194404c034a69101c0180d8429a80d4030103540c05101f5120808600c04c0e9034030b180500140001040468941042d180310303464110200c0000e4550016510454185925040103008641c1d0030342501d10f0104c0780c88154004003d8180d40c20912001c0f901070301d080310f00260b94bd5070101012841d007600d0b410041e006440000d11082404015001a021900210024050940c80700240713904c0d040c0c64040110b081d1f1207181e5154030b074101a015101035003000701c000c03410000720034207000880712708401c0c0c0d0002035400070405c007205801c0000e0000403001da01c0d04012000880108aa0343d4402481062103101031740c0b00809542d461008491124001906441c41d6040c211806000c031030440e4a50b00c284c0c082c49050781c0040c1ca040c0b003c40f046940040c03250711b040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 166465656 1250 166464406 166464413
    0x9040c09021b010603052a0a0603020f0d0e01061715040f0c03080304050606040507020607121505040e01020306150c03040501031107051506030d0201021206100302090a08010501030201180b0304 85
    0x20b5004801d01021810107201030000b504007803007600001c5001c0d40151200c0340410000c1089044014a4a1810140c40e0002c0701c06840e90050b81080d50b01504006079280c80040c90320000340511402052407508080410045500c1904103004540da2120f40900307540145201d10f07101d03c210050755214052200c00603010410074448555031074080d0850035051612511024001c0d40110340a9071154011003d1000b1707400c1030b02c6400e03070001d90781c400717000e01c0e04020f40300519055240001c4c0c0707645a00c0c0d042c80c40301441e45801c00ea0040034003c0c0100079006241e4001c40c00f035042100d043c0c1c031a028040b180154100369038101e07003160035004003451901d420403005400030449450440354100050011500050ac100030031417061f101040d41c6034a81c80e0400c10985000b60290704c840444e4018003050703a0740400001104e420030f074200c1c0c0d000a000c1340c20344210000e008901c1599070124010000141d00340040d48039074186e038001c2e6030392034480d03400010b05074142da440d01c02c04550880070000500403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 166466906 1250 166465656 166465661
    0x210020c03071511070303200703080a0506011e080103050c03190b0a0b13020d0b100c02011115180607140913090602040801020405011107030302060f091018030e09040c09 75
    0xc01d1000f21000a00030640705804803541c00941041700802d40e0350680e4551064102035240c5044014022245000c0131030f503008145910241146040d42c0c0c07143e0210ba150380c001c286135403480e0200a0714400544041d040200b1308042032000744e800d4000e80440e20369508020482a001c4550050070160170720b03107541e5000203550001c00740c041d000c0e580e00b9052101d0f6201020b84c070090a5820016850710403103601d020894140300c200500c910552428030600c2034010710000030035502400c141007841440f0850074181049503134018040c84250007080b10441040400103500702c4d00d00119052a40d031800c003668120300f5204450300790345c0c06100700d03292458003400d41494507030001400b0800904581d108400e0342c0050700700d05a1650041014401940d02c03144c0c0d5000c0c006c401004003941482c6460103901d4540c0a0140c0c48454210300c005002000100700b402d10b4082c00c1c8804124400b04040514800c40e9045011400242c0781c1c030b8031240700e14200361310324055500f128202c940d9520700640d0700300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 166468156 1250 166466906 166466933
    0x12060412020f0102070c030b0f06090a0c020c060309030c0d020a0503031b09030d030506030c090615070201050f030124030203070915020a0f0501141f0501120b031902010210020c0307 80
    0x8501c100300030b1000c1210203001601d4000c1c8204401c05800d0300b145000c5812910003400c0c1e0390600341910400c0201c3d82d409002940012a021000901c86d05100c0209d007800c640c00c01054000100000740140460300000500324440030310207030b844880c40760b03c0407a1280190140030b401e5a20500220b090354090001c0301031400d6041c0ca039245010303210000b00e420640c4c0918408080399982d0100441400c0c107001801c0700f0001154100f54910b014000101031030756214010070040342c04100301045902400803180b0083e20303032591640780d40c4d50380c5022945400d0781071941080d2000a014605603070080c000e403809102c2d1500c070408614144001d240b070218401c103510046114030ba02e1343c00403036101d0f03e6490078140204004550220203540b40004010054440d140079080c00540030b2585401e00b604d001030f140c09107000524445900007a501405941901690501901c0c181b081e01001001280e00114030070303000c1e500000107005a503000c070b0250402e29451a04108524000942d40003104103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 166469406 1250 166468156 166468193
    0x210503070f1713050f010e03070b04060626100b06120603160b12010f061d0f04050903090102160f210605011211030d0516050a02060c03090906120604 66
    0x240304285800d40d10801200b900c116104501c3c80120100340310301808140c4d0562a9040280301042c001044a56a442800800381206010102007401c00129800035002002c1314160340c2650010590a010691049040f020051064010401040c01e550060024552000b00306505015403c0400c070101c00c8002c000660500401c41c1c808056071206e08424094480d04e0201e035240d4014980d802411101038102501c0c82c00041401c005103580224002d5484980f80085038034509194003040c0b4044100d66030781e602c0f505007410008000000406482d001c88260700702c50300050301071b12030700640c04d40d80205003d83c41442c800b03200c1a40048000510002600074651552072591100b201b00c650a070089210f8141d07a0410005024510389914100340084018103008804400060302074401c070240c050642450401c014140702007440001080c0d60041d00c80c81d625400c0a0480781c40c2e5000e0b0900e01d20440c0c8034000324501e1300785006004401c4094000820142c0c03526111714070000e044c0310007034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 166470656 1250 166469406 166469417
    0xc040e0a09080d0603060b030303010b0a050c0705060d050a0c0c0c120201020a1208040311151501020a05070905061914011107150807080903090d06020f0f03040b04210503070f 77
    0x19000140c560000f040910700c20040010381e603086107802003e8174820358071030303100351302c107000520500303449100711912110141000ca54032240c81c03071741c07074101200c2d07070722039075120501081281c000711a58210901c00d02c0240800c21000100c104244c1e1190011075000e461101004000c0c841406503850f55680a40140100c4541044554841c0078a16040042100240c501818841015000100502c0113043c09000d004204070348181d0040180b00200103070401014102c019010341d0081c0501d40356950031070300352241581c8803a4241c0c00360606890341809080038920520903134205012050541e00e4100c410032802031641d0044413034603203495040301e50f802120000191820310560180400005840d049070b289080c0301c02800fa110018068032030354000b0004030a66940d528100840300794448001610f0b80170545404400d03002c0c0b02c1301d04031141c40000c1400f040c00004036000340708030701c540040e0003044502c1d98006001484440490082a028408200650f02804003500e000c0c1c0c007850f18 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 166471906 1250 166470656 166470671
    0xb0303032a0906130e0603060f04030c0c0305060a0b13090b0610030b0603010909061b0c030c0303110c0304080115030c09112713060b0409050408040806160206010e0c040e0a 76
    0x52403c1e404030714051040c1e00301000801200c5e055400d0180d004c81e04401414144c0340c000410703030507004020001002c0169158140c4100040380c03c80401442e0828200c409901e01004d1010007003616072205486800018002014200a4050826a907030310030f810082e1512030606000c1d601c0340403c0e40d8000c1c141c407075641081c5520349401039802010080004142c816407424008208c48400d07210020030701402982c100303516081208a1001640751403d02c25070348607403d0403801480c4210003044440707000185440c00900001c060001d450600c0d000b00100c0e0100218242660441d03c0000c0c45103030000d404000151050344a18504032404207194941a5805d80f545461044008401030061200c4140d80341410003034400e500c1d00388a21300800485003402d042140c98015485100019621100050700700801c0406a40c001d1414004891450908104803c00c40c0208c020503001441070100010b603885114201318001e900d42d40d2014500380c280020a000c04000603c0303200600c0c1c03075800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 166473156 1250 166471906 166471909
    0x110402040302060c03070c1a09091e0a0e0c03071a0309010207020d03050304060b0a2301030f0e030c0f06010e151c2004290d080a020601090b0303032a09 67
    0x10030795038480300d001d1603984406107021946201290080c3e418416604800d4075114060b40441301b09e0001250000200da4600c1c0c00100b521401e1000000e1000102c024000118980e4024405513403d0805403503103101140c00b45a51822580710b03c2021008203020403e000e14840010764118410000140c40e1180b25004511071008141045000590001c100000d10880307116022910f541101e0040c0800d14003000541d000e002d040f8100c0b03080d41c9802c118603d0387e009038420445d0090568092007100701c140a455125000020307440300380d015060740c00b0710b0f50300007149a0307042c0c480325118101651607140007200d8041c001d114aa400c0800c2203100a881852250b40040380e0344103002d801010300818210240c124101e8580c1070046003004030451614210404000003440e64500350b0f50f500e0b1110b40022071100031050050403410307000560442e01d507404124a81079a41490050000340c605c001456640c2c44102c1d114004582c120000900031040d40521403070703861240c1e03143c5080504800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 166474406 1250 166473156 166473169
    0x80603190c0b0c0601050109060302130501030f060e04080408010b0a06090b0d240807120f15090b1302030c0f0603240a0605040f1d13021f110c060306060403110402040302 75
    0x22554401d60f0044c4010401580d2000f42c0d44050910342c9003d50922042a9003403402d1501c5015030703810315490742c068440c6022140d11400040420800b0083d0500301030900311915400740c00342040039402c0071802c0085007454005d0201725801c564039062018035000324010036402030b0000300c0a00d41c441034002d603951041841d0380c10401c4280c080301c0c280d52400e00003618100c80395001c3e410030070400740810045401003980c900d6258000c003405440d415000008402805d000c0b1000b0200e100f560184041144400c0c603a01c4414420780860b1842c2c3c00103003c0225808d000100b80307034040070401c0021860f101e58a80c0c040400c48901520800d0035840300040c0e010325403900190005031000c102003201d219030f2841e80303004003085000038581c051881648980701600a15800c130140700c40346060b0031034440c8000102c400414210aa40c06440080003d284011000c04144070b4801d421042c1080e00d84039040700c0c0140380003402145003074510740c1d44218400d140c40240e43e005030709100005c05602c44d82c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 166475656 1250 166474406 166474417
    0x3070b0402041533050d09080f0307050403060506032e0e0106080309130b011e0918051f1413060302090406020a020d0203040b0417032a0c01080603190c0b 68
    0x100d10740504c414544507140c024044000840d8480038490701c0c8504540e41113400c88115a0000c440401c001c00a0305040200788070703010002d0341d000700002c10004840e81c000d01410503a8460300040c46245c984200301940e528511410480a078284503410850814040415100440147e0b0200e0305610017481035003115031540c0603140540002502c4517081c50a520707041d6030300031080c50410901c085c0c1d100007006001101d42465920082000b02140b290007800c00c04001d00c00b5800c0515280c0da541081005400c00b40c501200115029228602800303192541c1d600390b900b8094044d169803000810420381d00c0e60400c4654001e5540c03607001c80503031a14400d8070701c180d00601000d40e45240d8160003e18000a20510300b003150820f110030f2180300c00b118100c5040b92182c85004107000300948186007580304800d184180c4c4c465410304c00481007055041c0b0048072000d8001d40f507e6000a800540d0303860700c1200d1f144c2d416003200031300741200d0f4072541081445030b0081c05280a11519070300c400e0101e6100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 166476906 1250 166475656 166475669
    0x2d07030b060105071e1401110c0607050f040e091605010203091003021317030316080f010603050a060521010f0b0105030f091207030203040f0f120308150604030819030603020303070b04020415 84
    0x280c1c07a454402c81b03400d0003000c00c80111541802d1410200c2e01915031140f201800750360070080001620350344020840e0030f48016003d014103420039030a01d1082c85582c0d2040b81c03024030f895142d081000420b9070003c0241c03030022034045c0520000000301a030480080d03006e103070b075003201c0d8000020101c0e885c2c8658080301050b000a000659803420404907424035142201000d1b810450001c0400070030003c003031403c90464002c3e04000c2030036104c0760298030140202d07420140e080b00d0300032403401c4422070004642110408030380081100010360702c8200291003200200c240403c0040010030792401d00d24400c16881990b150548460744100410061250f111000c2640107a01c046030510142d4404104c80c402018a5862000e80ca4a00540d54105940e4528041c003404100c5000a4030207040c0d0144075131150b8028501650785d0f0310703407600d090203801004030340d1030b000203c8410a1034a40284100e00550390000c0080d42400481c1e5141074a0002c014030880e04242ca9044d1105a40f003c103c40c40040e009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 166478156 1250 166476906 166476923
    0x9080d090e01050301020a12020c01020714150f090a1b05030d1701090603030f030504140304060906181a0f09150a030e0c06040501031107052d07030b060105071e 71
    0x5080454248094103030403651090748104100524260800b424123845461600302507210828003140600a0207031880190515601544130790f10342d000400e0b42c180200d41b52090f107940f51100aa00828428200c65184a55000480003804949240148401218001281890503854002107170814004c0c4405501181f1fa00600c005c0540c51080c0da180502071200042000b640f179510002c000b44a00d40903001410b6642000c81c0900c20050400700650a00408070b980e10b9550380c40c010542c140b24070901000610108904d01c0d5184461003210856603500c14181441c0c1d240383c00b400b403d030b01c581c056040105040120040d507840f021031140c02d00320641c01003034441c82d041c8800340a0b100303c6200c00480350003400a0b4081c6079541000c1c2c409803403080c6000a4071104c0890903980c2445001c4000c1e04903c5404100b030403440c1a040c01402c407a581c1012400d011660f4000c1960303071903080c0001048d4003203500000c1c01c1c1e54030640103440d482d40140d80c000350842e06401c40e8485c1c446400420b952200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 166479406 1250 166478156 166478159
    0x61c0c06020f0f01180b0a0b0301050108101404050705060307050408060415050f07080a020a02030d090f1e03020a060c090302042405060f040e040609080c01091a0103050c040504020109080d09 84
    0x8000c0c0542d040e03664043e0000d0004034480c0814102c805602c0700018104d00000b40411132102c01548115451840500208101d5840b094040e0340d032410aa41300184a050500b0800243c4c400303855940129030000040000c00c1c203210400c04550802404241000014000001c22040c02c0184e00d0045010340310f039052300a2216560015640010800c070f40610014007480f412035404403c041c0c0c07000c0034200040e25a90b41c4903040313003144541c40402ca1198188000c500a12041c41101d07a101c3e0700c107810740c06110f1401050854000210b001c082c1c05038012101400124006422010a000051400301d882a4980d8005000c940000e190508040882c42c0764583c00e8280901c410040c040844101b4249800300280c100603100302d00400d04400740b200040707400c105441e00088a040c0e4401c0350162610349402d1f44030700801c04004199401030060f2001408a901050f4042c1600d03007203c064510040340c0030620000d050b019204904100e00f90350001071800f001e1010b68001d0442d50b6131110820b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 166480656 1250 166479406 166479433
    0x70c0308030403020d080708040f291503060103030c0f020307030206030103031817030927130b0a0b0109050126070302090405010b04080a02010c0303090501051017070509061c0c0602 80
    0x100141c907503081070020046c28005180e40110182e039020f54848000c1d00702000c94a410110840124402611440c045460360100010091000d1265003070b5030100146003070f103404140e40c500d001e02c4003070003081f050b10820703000c0f03040c00044840d00ca002030100d8079015500c0d80030076203580c802d90066001810701ca110385503e600f80000714005001c01601d510704482850102504c07480380210b20703846080d042d814100d810081c000048142d0200304680903031494004820b040304c80c500c1004442c9245120000340140c02c0500c2003140ba41d1061351410b0100c1e00b41001512950801d40c0c44241e52084c01001100492088086610540300c1d5035015807201071250521040d1041030b0805143d2110a1000380048180000d4042c40c140d024038119021382014101a4001c00754004040c01a5003403200304030a46100b0040b58007110700c5614030345280c0c82808025034075031646000740c0d071384030b40d185001c62164a80101d01c0440c4000a101540c403c402d039a803900601c41080e88100701507000f903100d10b01403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 166481906 1250 166480656 166480663
    0x7060209090a1a0402070302070e040602040602070f1a0c1926030402100315120309051c240b030a060506090106020f060f0a110304050105060a080d090e040602070c030803040302 78
    0x105a42010500604500c4900080514200f840d554041c42d800714040b4140b610800400703004100c0209100300700e0905041c0040a0f5015014100242c0b15a9400003440e148401d41d40044846030113200c0c543c0c00d0340042d448034661100304101d010344510203155254200c4550303070f60399a51040c190b6421540540c0b207050500c0389480d40c44054004107004000141e1110009030022515902e00090340c8200c05036900d420790095003110ba20000900d00c404205600f00c4007460943d84211401c5012164000c40740c03c64800c2010000c000310344c4004c0008240b1080040304a104007480303c040381c0078610001203803500e4001d4000391001030711401405a54180300343d01c540584070724030290032442d018400081d9500800b0b019215460105400a060b6644682c04114504008e54101d035130781c1064102240a00380c252800b40c41500108400100d40c480020a120f40c1c0c0c0d00c9440b020000e40c64188203000b0158024019581e140d020058680080d942127642c4000d5445185101e07124200350900030318 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 166483156 1250 166481906 166481911
    0x6150301060f05180a140f0405060609040809100917070312141608040306020c0d020723060306120307050307061a0913060f060b1c05060603040b04050708030706020909 74
    0x1103060b401c03010310141c0c5801c0c0000b0b403031004400342c0c4007158440420b01401030481c000510300d145081014803007038800c520300c003d0245000300100e032965180c1004001c046001594002c2c07035070904014071005404e040d00c2c103031040c500034141803c903d0782d1210b00a405000145000b185034001178424020010130304598030314000c892415512085000142805500c6080c3c201d121252540c05800300b00250700c030840e405594010010744d1201c1000040c103942d00ca4a50b100d07005801400d0022480b40c4900e41d0200005e0f06100031560b900740c0c07035400d000c426031004c0d2005410800c1e0b1004441000f070200000c064040c80742d4021550740d0407600b00042151004205811402e049228150b429a10300f105103402111000b0301c0d1810841501d40080100308078101d0b5504d550821500055038244440500340120200104840503000030030444102ca00480b5190351040301400802c01142d0300650fa1940144101c040f5468251502901072458000910442c1c686d90006030103000c41c100700340d6154 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 166484406 1250 166483156 166483169
    0x3050609010203012105030702060a05040501020616080115020f0115230303040303080c07022e090315020a092103171b030c07021e09011e15110615030106 68
    0x10f0555040a00302240c10302d0f0b49407034030b14030301000c1e00340f8041c0300301407048510503907000740910f5490400103000341580e0003921a041c0075014a00000e0406602c0c88240d1280c000d42c1d9569480981c01c1071100c0101d15484415441180f0661001001464007449003291000c1ca1507213103d13800e8940785019230100d07003102040307401c900d1040000d4038944001040d01d041e01d9041c10455455a1803901c0240305e8002d2a070065400303281d000415084c0115a984460b05084100c04a8521803128009680c120700c1071000a25443e8082502c007c40c1801e0743c054410031840389000e680030fa070b42c0d000150009580c1042d22200e0810440d8a008150b00140c070740d0480c10007120441400d20340035081c80000134844100e00003004000001a4440324041c003202e81007036000302045600c1814904a0203403e603c40380c11406660b03c43c0010a80e82a079070700b80e104003004440002115414a90759001803160115860184500d181c81404002d606002e0391344941440c00124500301015010582550455030014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 166485656 1250 166484406 166484411
    0x71805070f020d14280815060714070b04081f0c080412050f0703030e1b0a0611031c050406110901090e1f060809070602060f04020103050a0b12070305060901 69
    0x1d507101d40c0c0100f02c40314504591300700298040b484c0529410544524480920713110103015580c900601c410100311a81000c655a1811683c0d8503000051903c2d030b10901103a01078003d0020400041e10581c101a601920078182d4982c180ea52030050b00d01d40160300308100359001560480030b030000c040d80e041d060b00c6145c40c0c01d2041207407a4001500d481030140010b01000d4030782d44160704880c01601142e0700700b80c002d543d40340d4603402c0b0f09008000380402d12411080d40070b443d40035182420100708210588070700500f101c500c00d00d00031003514145140504440103020501401014800b00052003090b025110401305091400303280c0078085480c41f441c1508411000c0c8030140c4542d074024480301c29692a42e43c42049034075140e000407201d9800c02824480701c43c40b9207000c00c81a901182c0240511001c4044910703194840c00140c1c0c8a000491b040008070407048001005903102e82c2000d600710060480009644080d8800300c0c2c500e814450303d0807200c3d40700705410001c010080000b2640060100000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 166486906 1250 166485656 166485677
    0x501032309010b10020703051b010915090810020421020916020f030301060309110103060f090207021302031003020a0e040b0f07050c07061107081923011e0b040207020114180307180507 81
    0xc0c2c2f00f0710300c500954642c107010440303040303e039800b40040002030b100d400e00311010362052001c00c42c0607501c54060700c0380320404c14640021780310150100b6205030764014010501d07656107000840760b06140e000240114070030384117115908401030000f9400380280d55400f00c0d010625081c030404020007500251b0415250a6007007102c882112907040550701c5e0013078090703502d00180c00040c441c00c2d41748459a00b524130000c14000c05018807981482141d10980300880364a560b410a01050b41044401424804c81100050203118010444a6018800d82400b50400c0318070510507250080c550403513808980c0b100c4000c03244003400c0111800409408001740410406144403100b8000c44800c000c0c084500030b5816034003040801c5c554180c4207044802000000c64807220010710021140c0c100f091316251020903081418170380200c0f9070098040c0c41c0c041c50803c4565450b0b0007580004804400285880d000c0441c81d83d06000e003a009105503001e2494595015114004840c0b000e06000b041c0b240c0a41e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 166488156 1250 166486906 166486909
    0x602090a120506010509190501140f0a0b070807030306080a03080403030b2d0d050d03050103110103060302010c021210020a030f060f0e07050c161e0501032309010b10020703051b 78
    0x403440e040d560140e50006181c0c451901c3c1e00c11f813642001460028034100000030a0f810100c802c0301024400440c0c88142030201c01c4140640f8048a029424800f1400c0244001140180009066091291900060301076940c24400d0819550000460001d0442400e00080c590316005606401a0488042000d440e0034002c04560f41e0020300c484200300300d9100d5116480c6c0e90125961603181d00074080e135208502c2440c0080060509000c01c81d200c0801501da11f2041d48a8401c910a480e410303114400d504242d5000c10032402d8410511b442d261045d80b4604414100c107002400841140303440214800a400d05050141c8846400076081020780d08410020349207662200d51b081043d03824640c0d40c440f40d0380146404c181c20440c00088d1900902000620182c00d4800e519946180908020714162594011070944070322003a2180803c192104464009070041c8000e60012041c0c1c0000441c44100404510015401c5000c080940c21000d010001d001d028000340c0f101c0000140320090002c20b190 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 166489406 1250 166488156 166488163
    0x601090b03092d01150f06020a0b01061b050f100509010209060405010518310618020f071208041401050402010f050a03140a0203090f010b030a02010309021c0602090a1205 75
    0x102842c0203e45480c2480400d410700301200038009081c1c02800058800780c04181417811030302c9416807040d0f164000258030f41c070100300c003d14503900002412140c0d01e040e81c1200d038420043c2c040c00c2d000d00c64904940c000ba10400450b011260320102603d065081d0b00380341c008843d4014545092a4010800c0550650303a40301180c055034001d003800358940b0480c2d03021040007004103007496001100e550ad22991a0400b90201b141818000c82e030a6040c642442a075060300c00c24466041581c12581d00030140c0b4881d900640181c2e141240040d080031402c2e00c46c0520300441c4100c100c0441c0c42c620074003091100002c83d105c103040f02e0800038040c1c0d0400341c0c00208200081c11104040250108400c100c0e44d2107600042031120700f0944842c00f500b02090044001c0d40140c03881a218403075a151504c0701481030080d00803c220080280c080601190015805070001d08000c903400002404040c0c0b54021140d00020400e0080300016219003c210900241511a40182c02c2c0600b09544407000224000b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 166490656 1250 166489406 166489423
    0x50a0e07080c0f040602010501240801051c0b0a020405010216030302030a0804150c020f010e01090b010b07140a06060503010c0806130c05091e03120c030d021e070b0601090b0309 78
    0x203241a0110b542c401240e05440c0c0140e8082c0c8941ca41c000a0001711258150003041c1a00d0003882000824242101b13a1141d00c2414000d0b4400b142c00d080c0100403514060200d9812442d145c4404604080c0e1617841c0b007000182100c4081b075095001c50b041c001940d042040c5e01074942c081000ca100c060550314041e65074082c07490701c2c004008a0000040420108100b2401d03074040703061081c4a40b070441c1c100692121400801a20203619180303845140c0c250500448180a82003008000540d0a194041c03450340c3c03003c2c8066840300d01098500e0281e02c000c1000c2c5500d9030050b400016294181010103082d560b42403009010407600e01d0920419541d0841d16601c41060f080340003034132401151050702c0302e00640791580da1000d601445400d20420a840710204480c0071016110703480c0880300340522900a03402e5599240d4000d100080915a90740d0090030550309441e0100030600411031098010f07400403204503101411941480b040b540c11615903409081c11030700d19401c510700080341c90b9844044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 166491906 1250 166490656 166490671
    0x30d0e010212010909060e0c0d06050a09020a060c031211030c0901030f18060f02030705071b050a0303110d020a050c190b07060902012003040510110a05010510050a0e 73
    0x6404905444820035030441d808a840491510220360350b90202500074091074006a8041d42020401e140345000400c05010042d0000d0030700e80e41e01e4254a4200c01440c0052542c13603c10f80e100c180c40056640c2000f0b000052059a850705c10300c0e072084c80c0044c40d5421960224084900f080312603d000a40001501c0d17000500d156641e458040d0b61004034040d00301c403c0ca66800070329000e0a0f102241c46400d0030354201e8010b88003030001c200d140d02042c040788022614a40040d43c20b002c0708000420f0510311000c140e200c0011a00c90946460004100c2d442651044005c9200341000942d600810700c0b006008030b80500141c070402e9041c0e111280ca900f4a0007d040c4605c00c41c1180180740c0c42c868445202034070540c0300700c507104c50851400e840146891507050f030204019132aa8900d0544100c0306403100c1e200700c80954141881e150900034040d00000215080c441158003050480314200a6403081e00c0c0918000f160030304004612442c0c0174200c3d0055030054218141c02d100d981e5112070466044400d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 166493156 1250 166491906 166491911
    0x10c021902040906110d0c020f0304050103090c030506010914010501031b0f0306082401050603010f0e04060207060903020c010801050a06140c032208120304110405060f060703170702030705030d 85
    0x6041c0700060040c01e070318500900e0a0700d800f844420707a085903030103421181d0350504104440e17100725074140e03031b640305c007600c0c6c0d40480d40100802e00040d48250003c0020038030841403116459126920b0341c0c02c000c003d80102c0d144a945902000c5519681649580102401c1c242000041c1c21803c440c0c15041c48030b201a0140300c40403400c0402c00340300354070500041c10381e10f003070f02c4542e00b0760740c030300d0480035851038041100148a00010600d45422003c40e8101c41103c41075000d194601504410542c0000780700b0780b003540d402d01c050800725a441c056109004d110fa40030b804403816078030000d0444070041e0800340c02584014020300540703400c550140c80d240c002203400da0321418081a5070707186220f0700110a01e9490303c2114072358541d01c46030000701030700d028805490746124407107840c0c0814003040328003418144103800c03440c0e0340303092075440603401c60000743c00003c03501201d074081880c03980b00401c1140000d456040f0940c81c4d0040c0d000d59134001a13288091850551a07498540e03032400340e08107042055a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 166494406 1250 166493156 166493203
    0x30a0209190e1f0501120f020a21050105010f050631080601090c081e060307050402030c0901080c0c150c0d0603030809010e120307030c03020c07080a1202010c02 71
    0xc6000707100d10451041d080c40031050407078400c0e841d501009821100304000122070b0310b09181c0f60151a041c0e4100c0d02000220403c00d4a4000035482d15081c00d070b81100e181000404c010340f04543e4031451101e02c00d49c42240d244075252883c03c4070016401803041000840b414882903540404840f10b01000b2040381c0002001001c0c074100c03900032021140040e034031049001a0b801400719155049034898001040b00c4005aa41a82c0140c002c480800d2500342c030b4550242c0380507061440a07003081002c0c0c210741c005a101c1020070200d910640303c0240006000c1241d0b941c642e4072030044c561000075800c0b101c0c102110090103d5031000e18510403140f8014840004001d48909001c3c0c0c1c000076607600c018040c40b0782c0c0b400c01030001581034803501d01c1542810a01c95034240300003044040d2003144100a0714507547c91404500812842d1500b208068007004140d14551082014101400101002d84900c0d14a40341551041841c0440142076905124600d9100c07600480c4149008140140304003030702 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 166495656 1250 166494406 166494421
    0x5030f070501140106200106051008070215040501020417070f120524040606080c220908070b090d080112020607031106040303060602061003050c0411090a08010207021e030a0209 78
    0x10200c19451001c1d003000c0c07000004000742d10541c00c290134014074100550701c50360740306c2080c240c850714040c0d15080394402d4402d4a42e41e203d440440d40c060719601c140d81c0841c030000e114500e4200190760566990b90003090078042d0741e070400c055000044c1004002c05006180107108840e08010340301d10000d90b40d2180503d818000144119609109007903d0388a290854007140c122060040c2d40c25110189446404504100f000880c0899003000408024503d00c40400d144010f522581d50080819225002d10002541e40c1c0c02800d01c1503c2001410103518005c0d006078503040c106140c210401110000400c404144035000c8142c1a8041d1490b90360303002c86080950b48450f0903603110744c0a20851003000700381507040e4825000d84400741c0c20f03102031352140b0040f03a00250480c00054140c0d040755000354058501a07101131183c1001d607030410700749071035940010309201103640004d4499400144040440c94000101c002c18003841c0c450007410044040440c1d0b60b1103510310001c0c010319070035000c58580c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 166496906 1250 166495656 166495661
    0xa08180c03060c0409061a0d0e0705121b0402040b040312020102120c0a080c0903070909020f041104090b0a14100e1c020108060906030604120c0c090606120905030f070501 75
    0x800c0c00140440d100b82c02d203d1400d025551042c81401601403600d40046403507202e80c45809a0100844403650412000101c100003c1198912100c3c591003124000142500c0c1d5880340740404410718003600b0f441d0b00c01d2038004445d072442d0300315a11076441080140842e08078032003070707909891b00035a00d06054040f4500503402881002080c00108001c00c04201d192076461005214425066982020382e842d06154240103020300300303507135030b040d0460a42880340b071425903c101415400184080e030716000311030200d003c0719004e0709000100d41c0c0002c0c091080d07507082e004440701100151403a444031840d00b550b59080d03441201e6007a214445181400b00402e2007124542000d00008140000c4400f903600422552160484201c0c045841d00002900c1c0d45428041e440c4901800f5015129640d42d90f515031030030190600c0e20b00103003c003150303001c0d010612400700c0102402a51400045881c240703c40a0050b41d14200750140c2241410055000210044151814190b24020391a00d50320300e454020702 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 166498156 1250 166496906 166496923
    0x60f050c100204031401180809100302040b0c150f040f12050c100614060301030b010905071106010e190504051209010306080604050a02090105060a0815010c02120c0310020a0818 78
    0x75403070000ca404001d2101c0d10213640c000707502d42c4008118200f1001d001c540b88150f130364000781c00750105004003c1c0b5810300341c0030f0500415a9140042c60240c40300b070502695041540d90208070f9005501b0302100203400785105030403419a01131901103140a9450b0a002a080e5034001e20040d03080040c455011b002c0c2065545000c9600c0660b05842d43c11461003005080c2d134030444003000b0a41407080c5071400d000c806c4906807030b0044648046a0300b403401d4200079100c041d0900e020404206158905040c003400368602a010550b0041200d04016811280310044ca02025410342e00e0441444002200000d4016180c0c0c0701004072a2101240801a002030040368025001401984200401c002001c0380c081e00e071a05c2214858510f0341c0328410f0209901401c40c0a60203e41c00001041c400e040384500081030440504d0140004403c50b8041529030f942c4c04c0200940354019440c040c1549024412805003031004201141030103a1010700811408000d094001c010510505072401d0781400c0c40000c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 166499406 1250 166498156 166498183
    0x30f09080703030f06050418020607080403020d0b0f071412060a081605030d1107210819030e0606011d0a090606090602150c040306150305060a0c030f06060f050c 71
    0x20303252200c6080c00b4020700307400001350f00150300d00300c0c0c080740c41d291602c40e124505c0b11030501100361070125400c0c00650390101c0310913035165505210000042c0e41d100c9150b56039038400d681521040c184036081d046040c502501407024481c0001015400c0005442503034021100702c1580075075a107620020456182890b0020343c45401207000655018070540b050340100c4400703900722040d90a1402d8222525000d1100209554101080c02c00030740074000d00d41d003c0703885908014041c04580c3c3e42d40014a40c0022200025810f601911440064052152504a03c09440607204038030308100020210540d0500092010a22510000351515000d4030480074003100402007140b1038850307001800c1e0601030702c51803005114000c11984c41400c2811a1030090141000741800e00f401c0d6a5250007034241d080d000356a411203420004003146c0b0402c1840d00030380601000103000b1200d000024183c0310050140110f003400c05200b004001e5000e80e00c58000c1c9600d01d8081d446e001c45400107401d000c404d00608 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 166500656 1250 166499406 166499423
    0xd02090a090c020a02120c01050406110102090303040608060f0108010b090120191e03090513090b01090507110c0315101a090414100b0c010603171207110d030f09 71
    0x1d034155000520242c0c0b0703900846036034203050a5400801c4e0f580154041f0031307000550512007080340c280502c18012001046c8000503041208440c00b0a2654016034400c0000411f507400380019420032620004e50803100f842d013006158100802e0b007205118101a1904000d40e1541c103410701c10b0441d1001070424840c03800d41c0c074840d00d21201000b000b41c0002e829101610fa80f0f890010820051400072a40c950644030000164a07010405c5038814002c46c0030031a05403140041c1000403c620000c174040d0420f03035000a02810f00c050000c01c514500400b0100580c40b0108100481d500081e540c12038100c000c40d903603050b07070340c05400d848803815951244060701008205642e402d51410050072205c581a82c00b000b076006c00d00c14056030306e0410707200710003490b20702d0383d0070b016060381d00000300045d000038000480e0321503480d0b45281651980c043d0340c68030180041542d4070541c4030b1520440c1c000d442494400380070030003011000c0d19000100c40b110145a0b55103540590a1055000405c03480d4000d01c02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 166501906 1250 166500656 166500671
    0x908030a2c040603050318030d0903030c080715050709050109030305072d080918220311030a0801080114040201020d0c0f080406020c030607030501081e070509040f0605070203040501050d02090a09 86
    0x5031b498018401e21001c0c5a12190200f509080002d814020700d0120b6452201051854400b80d50604000324261404007040000c038000c207210001e04200f031008100300107024030b0100c10007003c00c3c3c0340380c20045c100481d0040c2040407a6218040e1a0341c00c2d003002a907180c03185800c03030300d030316920441d40021010100341d8940c4e0107014071940602412041600d1100d000c4036000d25008180d00216601d01010400310050048800b42c0003840030090b2090420115000f944000c161468000c03100c032000003081040180304040707007801010050401048140e50b182803990010313464042c0841104104480303000c020781440f40c0c000800040700c1c0c211009659460302d07848002e40b20300009101d41e000788506000304000d02e12901c90541282c0c1c2d030102601d020264011440307510110001e40c51b15500c595840410540e4420840d50301a40c401c41400c10303041d1407860810b0507200010042400d54000f030000304070590300300c4100c80d072050140e0001a6110814000601c40c26a15000b504100340303003000b07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 166503156 1250 166501906 166501913
    0xd140705010e0a06051005060a080702010902031b1c050303190207060c0302040311030a03050d020d02120c071202031903090201020a12050d060e010302061909150f0908030a2c040603 80
    0x241c40b411030b40110028416071b5500039100519012911680b50844000c2280154441c0700c1c80459070441034a10010440301640c0d00002d01d480d406000000450064800386e6a06240c00002d1030140541100d41e10088a0a40c03181d0761280002820b003840550450750310401199290704450301543c0c044070800c070b4908403010040003500a40012940e40c1c0000c04d12105510b00000c00030106541561414580702070040b080000c1c0d002000036888040e0207101d602850702d101c7c07280324405e4040300049034840059042c0fa801c102165000340c81550010803039071003101071f10f0302440ca600449050102e400696032004070306e082c0c042000070b00842e05414114825690040050103003001004083c00140e07101e04800000c04800c0c0300c02580328034104881a48400a006080004010b506000c03101075512100c54045c03682c5000c061300010350540c14402000d8008031881c0251000d5001541007003217418001d44580f2860781d00300540a0281500c101d51400710720303412042000a881804419641d15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 166504406 1250 166503156 166503163
    0x41a100306060303050307120207200a08060103060c17090d1b14060402100201020903060a050c0c190c0e0112020409080c03130806070224090c04020307020d090608090d140705010e 79
    0x225401c002507005c42808c035450703085000b40e4104a42201d0300d00c4000d00380d5003104566801c690a002c0e001501c4020000e400d04007030241a0095001d0240400c10543c2d58034024107601d41101165100c3c0c28003001e008007598000b1700c52102d0764960070004201d00e580000d0b20f17090300b40420014a0340600702603999400c10080b80703c9000300e2007074a00180a40b840c04050f82030b80100400560103500100004ac0d201a0386c0d045250002c45581c0010b1802c1c1c001e083d040d041048105104021f01c010382c081d00204201e80411100a00114038040b0759941888900380b80e095198001074030503900d400722002032081007000c68a10661b880e040f695120480418080d040d44a881115414081c82c00050384c10b0b030011a241c400240e0180c144802080c01c48a800c2c160307600503056001c0c600c201d00c13410281e43c45070f100440c0902c0b0f80c3d400521400007810001490061580c215504101d41503083c0810a10001000c0340b0350120750070684894001c0d5140c000d80790103a401c2c0030317003150f09000310490070318000b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 166505656 1250 166504406 166504411
    0x40290d1e0c050307150c08120702060f06030105010f050607060b091305121e0d02040e0403050304050d021f0207020d080301091b0302040f09020703051b060702010c0305041a1003060603030503 84
    0x19a0740c0c0440c50340c0c8808043d21940503206000c07140324071801c00c0301d034107208080c0980c1052240050500703041214990009140c1c08940d000c0c0036a1018061109c104d44906003142e012004030000d20443d030400c207a048602c038051051174000c170740100383c1c4020042070741c2001d102d440c400380c030418803450086480104030141000c2a1554021000c3c0c211056403244229010440742c2d01c41d4620040081080c483e29902801000622641c02c1c400414006502c030192401907010340c0c0d4003602c0e070806080080c02c0c28410505841958005080da0441519044014070103452050b0011b031189201d00201308207040260008002820000000c12021281e91104040345080c4240420071104d0020a0b0224816806441e882d60341d400c40422081c10190001c09101d403103481d040e811b043d081641100c04841112103245150030540422508a5092007182401c0880d46030030301040c20641c03035403070788410004c03029105012240001540c1b0140c200c2c1c230310011980310300d00300407455490034001c01c6500103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 166506906 1250 166505656 166505663
    0xb040e0601061403010e010308071a07120b1008150303070b010314011d0601050603100509070906020c0402070c050f15070311060106050c061540290d1e 67
    0x60421031210a0140b0903603040c6d4909002c402c1107642140c90f000c01940000b001103403500914602d07403210014040b4900c1c01120b84e625031005a003c0c0c0b90300034066a000b1300c1c106025050f10010b4200f2241d11a01c1607800c0000d04e20803200c1c00030b40b14007080c114032480601500c000c14801c000402c1210100601c0720000d10403008200c00d0101810403500440000d0704800c1c40da0000006100c1031030f2480086070800e900c2010718074002d40e200d0204055190444044003c07416107503040165076010710105279018000c0350210315040c07055640300f43c1c141443c0500c9014807221003034010b440e150003810141c666103030140c854999a03180380050105080c21300c112803901030302c000001c50074090000da4404450780c5c000740c0300c2c40d82d03402403404070205c1800c40c403036105071169142c0702001803140e81003280a580d106a242000186100440b10b0b041144c0c92202031864441c42d0038001d03030703180351140b111241990004002043c070000508805200b00c0c000d40714a4840c01a1813814142d60281100e9038403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 166508156 1250 166506906 166506917
    0x70311040f05070215060112320108070b210f180111090415152d05070803040507031509030305090d0504050f0109090e030421080a030f0b040e060106 66
    0x640080340c01a2001500d1103000341e48178005030a0030910707000c41650702010600d850b00217211110192400d0311240c07564004031070051440480d64800c480035030b080400d03101c08a1415035141509940e41c40080c0e05c101681000d0109050350800480c072000e0500d0403c4140080c031606021000f240345280c10381d1101700c0a04642002c1110100c18041e403c0e002d0001025641041c00400603c0064800c000701105940302034031000c88c200c3c004203c401601501070750b441c030f038850b0350784018111903402c1c03d141107030020015188042c141e480300856581e19484001c07e0380b82d440d9854944c1c80c00b48aa00001d214070710074540c0c1510030740503510440010780030b960309000c00d8403100301e0f540e202c01e6490740103800038800300024040d50400c00d1100e4500141031501514060780d40741ea40c0d04407050200e070b5180b10b4100081c10084001031160140200960950b004e030000380b96505c905082c40740d120040141500e0340400d01c900b40040d40400d6a04c0c00c050400e00142c18101015521814240200e101182 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 166509406 1250 166508156 166508171
    0xc03111605120c01050f0c010f0c030f06060201110f21040302030a1412041424060916020303070e0103091a040b151804020d02060403050a020a170606091807031104 72
    0x603000a2034143d21081a100c440c0307014001c02441c42a03501071652201c0c95921200c03968100903051045505d0100346540000d203c0031651030300801d9906503800082107a0419a218074602c50070780407103201c020100855681c890070001c40d201e0000824100507c03840c820810002450b4000c402803008001a54607a80c0d072005880841c2aa4000c685c030b003010080e60100050300060812900f00b0f01e0546001c11503c0f070000c0ea0024031140080c2e560000c0368040c0d41d0090008a040a54490750890700f29285c0c400b0307250403031078000d503a40001050075080050925012032547d0095105c114036a0b0400c00b05100300c040900070341c03e039090684048418509040000b8026401c4061284000358009c011200300302031840003d070601800352090f41d009100c4001d140060b501d0200400042d03200340042c0609910a00400845641070791000b50b03102100c103104c040c20f80000c00c0465205004440441c46515100040e07a07017160400142d402910030907801005014482c014044410421201031140301e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 166510656 1250 166509406 166509439
    0x80105450714030601110111130801110c03030a020d060e0421030605010f050d060e1e13020604090e0a12050c0c030d090e0403170109091a06100c03111605 68
    0x191072071544100c0300c2c2d07003072000c200e46612035441480090000800860003500c4521101101e6000c00800b90400301041c000300701c0185c081c09103205990120000030b06000001c3c0390141c8a200007070403c5140da40c001441d1040b03132003a03441400607180c50030030316060385002d203070a04600e000100905011a00200c090742250320a00a034010f842d0107035a6542400d10340326040d1042d40003145810301d140e46034100071a0f036081c0d96450381d1082e40d0118004090b081c00340c088200c88032026000c4041e00a50841110160311030508032001c03a03898140014203d201480d070b80342003040c5448001c0482503011503100801e0390104c06031124145d1002039820cc07262801c1056030741c52000b400d410104400d000100b01d4111120000342e4800c0c0a41007600054542841d00350700d58009801c1081115a1034204405109002121010b0701c007103210312100c1800c09000040e14201d0041540c0104001c02c002c0302c0406119113021400c00e10710703000319807451240c0100580084280c0c01050300450701010030610300c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 166511906 1250 166510656 166510667
    0x81905060303090d030201110d0b1212070212010b101808060405100b06040b0f13050613050907170907050906060a0f0509151620010801054507 63
    0x1514009000b18900b0b022103080c000b054403040c10030380555588600722001c200c9800010014050078030000660b150016041007803a06007900503910079417001d21742d480f60b4a2088201c0b85120780498941c50308110304207040e805048020066a00181c0313000340030718490781201042001907200080380b42c845031500245a070340d0300d0864001e0002da00034810903059603000e40c040301d01024043c1a061074140c69a0914000c0d5024102100b910500043c2c0000d21160340b00040e80a0b01d1b00b00c5d4114907044011086d20821b01c3d042c05524422001c80300880c00150007403002e40b950311540b070110041807030300c0314000d610742030180b0495010707103095400030302c2d90301e4280e040f1801b071141a21401ea001079103401c200c9145e04a040c9082c0c10502503c5420b0242d1283c001a000c025a580040e4405028600d030220344050034440d500c400030301c220807482560f030300108013906440c41236440111918070094030b10ba035140821106072100c3c2541c0307855082640005001400000d10341c003040590f44695008644 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 166513156 1250 166511906 166511911
    0xe0306040803180703050303070201110702010c03080703020d09111201090b07140909010306020306030c0301020f040608100e01031406130209010308030a060306060b0c0f0d050328050106081905 85
    0x1416001000003400054050740a903400030140003182d01c0c050b101241e840d1418072542c20036200c41c2c5c070100030000c1e480d42c24028400800081d0001c5420031010303030300181001803420401420701c0511030004030b40b54801c4e4180c0d0082a060f1105010030b01c0d09061901d0141d07a9106028080e0202030103004141e401405440012135100e4600115641c070803404503440b08040c0c22005112604001006160f9146000113018600486005940c0d0401d103081502c0c05040d06240c0340aa4014401c1c60054114542a2030441d4124108000c0a68411540700e4507403245802200580c1c030394800110521204280d04940d210800040707030680e48407911000440343c01d4160095000c01c030140123200080c00ca001031754002c034030b00310040740b082d403a0740d10481a10344981004800080118502d10311a0042010b200c1810b0301c032010b007020124403000200103100080c40c0860302c00c2e00340401d184440d000c07181e99501d542401800c00c81561102c200030009a016a60740e030300206070307801000071885544039460 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 166514406 1250 166513156 166513159
    0x90b010909051b0c0705090f09060609010806190609090506040b010905010503061501020a140f0c0420070515070c020a0801020c062d0f06011e0903030509040605060706050906070e 79
    0x143c5401a80701c42d00d4040e0700030004501d0750b01500100180d1502e81e41d540500400c0d030042d10071018901120480c0c54410010320040c42001d0745001001060400310700b44d50841780c2c44140d00041180354100c280a0202c0b135108003a240d00e0005040203101002c1512400384d88280c1043c4400e981e0b9441030020344000380501d40d81038002c40040b510705003080c00b2100e802401801620481d10842c0ca030b4924895820420801c941c21403202007550603001c1c40b50700c0c000f0b03c04440401c0750000e100c610300d810b8404090120b0059800003135440c20b00c0010084c1e40380401040803d044035141411340180305030f1404c54203e0103004004404541c407441802030317800e80340c5244010060f569a131412590030050340402541003101000c440c00030b8020403014103204032031906014007982028030006207400c1d0184901c0d220b00729410440f414440d8020700d2401100d4051921549815040c00020014846035020076803081d00020388500708601074221a00c1400b0003029200a951000c00a6075101288040d26 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 166515656 1250 166514406 166514431
    0x6010f2003071e1109070306090509010f0605120303040f05070302150a031512120908070902090906010516080f040b0a0c050d030e030a0c0501020c0102043305070201030203090c0901090b01090905 86
    0x411040c2003605c00c50342e03c12200d2401080c11036403000803c0859078156101c07601e59440e052440003001040c0140801050140c0e242c442c0c17031241000c8a6107900014000410400c0090038841c02e00ca010444980919002000722110980b01004003025030712075403584001c40d09000d031004950615000c400102c8a9000f01c9628099465441604121002c085070003030204481010407643c0c000c1000001034980c0000c01030b902c269010030841d400340e004182c0c81c1040300030041500350000c05407000c058150301c03611542d100c005131400795105010700d420880c03004902042000c074196201300b21010b20340c0290151403e41561007012025100b00c2c14000d00b031039004008044580384100420407009024400060809590354256426a48642d101442c120f4090350801021203041c0c0f40c51140303004184804a41c0c00000c034010300b16000c1c00c000a410b040d408000910411000c0c4034080c6c4900c4020402101981c44034000d03030080a0f2811901d000035a4168003113001d040c01c0c4502800380c80c480d07a08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 166516906 1250 166515656 166515683
    0x105010605070c140102070f080f06060f0a0e040303020712080411040606090b0d0204050307030503030105131e0b060702030a03020d0f020f0705040902060d0204060518010507030806010f2003071e 86
    0x884c10341c0694201c90b141148035044000500700b054100040180c00007a010300a09199100d00601d414000f402091040c50086012401d9941e2042c480f42103c0381412030781701550b00c03410254000d010f482000340000140200060826510030140b81c480c2e441203800084240801c018081190700302e014540100d103914030280508040400505024414041c016150a843c8c2011908144040d80b040754560310100060106143c404807956101a041008005500007000c0850b945d68017030b0f00f8200f07190398680c0c85030815154501100c205a8010b4100d034000f070702c00e02c0c009549464880e0000009002500050342240c4045690303481d11060380d00802c0000c2c04d00341044010491070804aa010804005024040d242800a00011700103900c40c1c0d9150400d01401100c40076114903060b041040821a1000003900304222540100c400c2c0382400658407144001c3d00c4410f21100301d03001d1085e26404420002c50300000400175203100308580c00c100018907030101c0444040000081031302035007640 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 166518156 1250 166516906 166516919
    0x120c081506070c030503030f160c02100504031b09150302011e031b03050403030c05120a0e0705040e0307020f03070b0a030c0e060a020d030605060a0c1e02091003050105010605070c 79
    0xc2010465600510807440c21a1640e03031056216070b6a842115250004410000d80e10381070f0034455030208804000486026004000030455a00d0b550001d205140041e42001c0c041d100c0d40c1907601860744036111000c1c0b01c0c3d0b1a2041900c10f001c501c0b90801090030300e440755010390307003d100c3c1808403036041c1c48092038049241103402e004103c41640390109a5100b21060146c0510034562145000f41d07140040d031403d00e4203000b829240c0003002ea00a01c0810071044055807a8084000d50140c0081400203e904c8511301c41c50800440da030105074850b0400e02a200f018001000919449200f1a51041640e103428181505c0d40124401c910389002c060250950a80c003a03000040012284d1138a00c043c070709444000b58403a004a03d1410059001d40b4440c208560148141c002a0000b1220a41410400384000700b81100b01d4034000c0032651001c00004003962040b0640000e50b41c02800ca00300d5180c55000301c80c41458a100585003036080100008a29020300110b898035900103400380b601505107403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 166519406 1250 166518156 166518181
    0xf06010905030c1302070602070c080601051503060909070503010203010609050a0905100e0711010603110316050325091805150603030d0902010c0b04030f0f020318091306021801120c08 81
    0xc018804c2c0740c080089100042d070314401400c400f84112176045501c0c0c217282c00076103000d0381600107a0048079100c50000e25440e203030080d65072250301100d90301559518211014104507095019076095800031001042443c0c0100c2d83c2c206940013a00e04400c000d41e2075217440c0a8410a582c044c051200c1400184085490f00c25040d5000d010f504003058003101c0012242c6c211030312544140c80c403804203564804c0c03c0ca07040c41801680d451a1400f0a0070354109800a915810190440c01c0d994950b401038001e03840706081070200030324200c0c4c01000740407410344240e514880c410b83e080301c0c00d0144819031032124240c102c1700ba0241070003074021400c0c0301010080a005040f8610700340c0c10701c00b001c0c40f9100014540300085119601c42d96804503901200da20140c500000c410007401503410502542c4c05084418400201026049561701485d4a4100650043d03a50869010f400e4900002e184100d0920450101c030075104281d80b04140e0381d500e410680b003151807880712000002e2481c0041110072038401c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 166520656 1250 166519406 166519429
    0x6030705071e0602180405071d030106080708030301030203070b04080a06181401090212010605011205070e0d06061505070b04020405040816061a0105040e0117120406080f06010905030c 81
    0x422102d0884811508110140800040210b8209400148000444840403116404810259418401d40c1800b15019040540d42c1e1400c520f84020303403180d0041d0355401d40240009180083c03e031440709454904041d00d9030f0090005900030310a254002070f000030300ca000c503030884500e2400b07840100c00780c0c0e40b0301001d8410131030310016080640d00150041780d180015100010b4110000041e000f207244103100815072151501000741c1d161031802c01213a600b10440450b201c850050009140e90303010707015201401107441903604402400d5480c41045a00d51101045d10111204c2c09007508540c04225200c1c4110a8020083e0f10342c04046801801e064100540092051030b5850904075900344291516a2180e01a20043d844000c07105845c06d420b241d0070301d00c06003841c000b46403600780340c0140e04c02d01042c8200e080b820307001d80105949480030300000303203840382103506559655540c680091440400356a1600c1010080020495640c00348040e80c045680281c09010201000c4080105d0030840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 166521906 1250 166520656 166520663
    0x1b230a21090b19080f0105030d0503061804122a2003030a03060e060d120c170d0204080d0804050c04020708130b04030b01152a020a151103090603070507 67
    0x81c1040402c24200d100041c001c685001c1003d4040c10070030190041c41040054440c1101458500040c8100d85020820500308169800c100c0e42c1ca48591021440f0f0742e540d41c100c0300000c0c00100038041044940240090903e0003581c43d03c0e144e001e0744402083c00102158043c24a03034000d2000c000199030b000f0310003000c40403540054143d40c2010003281c2142d000810100003c0e980300011b0045428282c07456401c0f50013903c01c15403540242c0c1c3c5103920038080445800900c20810030610400030003150500346d84a11a070702c1d5860301840300052029400502820545008410a000b041da100d64401442540c10800400002084a080c0070003507000010640f40d201c8100101c03540318800c070503114010100c008040ba1780368a9810f007000a2041030700038171340c040036007281c8100050f802440c4181120804c04884030300d07290b800c445402810032000080d082072a07131000158088594441070b48402c0c06446040e01202c0741d50040e51640316280016174071113418000305449520a00140020f18031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 166523156 1250 166521906 166521917
    0x41104090b09010f06060c0203070603020306030703050114040209060906210f0303090a1205070803040615080105070315080d0503040809040921030b0a05090f071b230a21 75
    0x100703807148507000308110344910b03450303444110b4a43d18800d103200b068024641883c1011400c4015800179840b5071451103000704160b008000304074155420310841000750b5000000f0084011202110452480c084605038450403c0e20001101c504040c03c00d43d2040310002e100981002c943d019905500500c000c810b000c030b02c03c2c4070303102e000501e0401c0110301a02c162001441c2503c403924080901c210019070500402500340303d030340001800c0c141a21b4200d070348140d0200b11003034048280e00e60010b055020a50319820401030000326030301030748080c26843d040c1d4482114a5156641203540d00380240080340054400c00c006000300389464044e01d18910000c0011030f06400b5510780000008c01c0e91094541c3c01651200f1504003a0144070312040c0c01004d0340e81d100460700e08400a6494800104500011840d640c00100c0b0503102e448000220f0400c0c42c3d20b000703041c03180d041c000ba010200120107075205103070702c0442d40c0030800010b07032154103644244522075130f69044111240c0c0610980c0c0a409108 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 166524406 1250 166523156 166523171
    0x71b140706090302100203090306071b02100e0306070f0f031d0a05030a0e0d020a09230118060b09090105190b0f0a030b0a030803060d030509120304051f0206041104 72
    0x2241401003100400d920350b11070303510a00b18010800581c1c10000c100c019940300b040300c180a52404a140390b40320f003407800e00b0034541005501c00750b006810260300a510000301e40103804600c0d00403042d58507031081902264101e50350309005640300a81900441c0110b45503103402e00015121760000d40c84034403090341c94010000c0a000d65440c00c0003000c82200c180e007002c1600c5000c1741d4420508128004101d036041000e154540104410040902508000f03a0b1100180340d0021184407240c4050748403c0c0d02100c8030340e503400e43c64105c590030394842401c413800c11714000b0f0040b452071b060b100501402402c91030071340d18150402044d0f80300b030038502c0e001c03041030280003401844443c00381a220650700011561070031201d0004040380d528074061031080c0003100d405c0c00030582032000da075400182550a074040750654201592903014241c00142d0103800c00c4420410343c10040082d0088800070380e903c4a00101d80e03035076564101000000c89006901501c0003070049110175501d0656000c001d040041e115 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 166525656 1250 166524406 166524443
    0xc1315051b0a111504030b01031211010506092d01180e030f0d15090e0312090a0f060f02070c080d090609140904030c080705070e3301090e011203080f071b 68
    0x5902741e2013907414130803c2030202c5403076800c114a80140c2c03401c00700070840c51500c000041c0c21024040c10101010309950301029a001d07840c0340210181100f4041e052456a4603082e80c0607104844220444c0d242c1441c81e8244541000000e40303007030403201c114550170311a800170282c00505074100300100c04c80e80300100103080307841881032480000041c4e01844e44c81820078490410404050040307805584050b0540c00880c011680942e0b819038881000708040c00800d0311351001e40182c04010700121f10346240002c26510024090500d1285600c07102c040b50b075184400d4981603814401c44880f1410210b68074654a443c0c580d140e4400d210341840c428181040e2501d4849801002c4103c4199116101c140000803110708400d03070045944a501e41c0d090719407403001c035103170000c1c0b1081d001201103441c143d280b0323a01585165001e4841c80b00701c440c156944081c050000a07007000107070003040401e008509400040d50340c46101c0c484a81340c5038845000d000580e200c1c6403400200f680c84040c03003295103842 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 166526906 1250 166525656 166525673
    0x21c09030209011202030d050408060a090236010501020726031303051e01380301020c07090621030806040906050c041701050108060c1315051b0a11150403 68
    0x40c000046101d108013200d40b040c1403405001020401c1405400d100800ca1124000b5016510034203044001c80c40412901c08107144000034110000c5600c0042c003001d462440c12600440ca95441c0b007130b401d0161341e03031780e0059844460b0340c080c0d49a00700150003403036821008140e0010500381d040046900d40741c0c0b16140040b0122840e00225925001103142c2081d11140d0043c02141c069408003c0202c68504000c6902c441001e8000703180c1036580340c0510007140340c1d001083c0001070b0090001e41d0340c1d04003d82c00319280c80c030b540108910a03142c000046980e818078803038580c101c0502c4011254441d07168405842e1008001d103e694080d4407aa8000b0002d401405000d01983c021001251280d0074800910000c015401401d00140e1405004010302600002e00b40d40048402051541e01d4508881c181e0503640150028009000c0007200d02c01040d40c00b80040c40322030302c41c821200f05100140050394603011400f4010700b04500804007203080d0f1510100c0d80944048843d01107142a66075500e8295 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 166528156 1250 166526906 166526909
    0xc0e010b0a02160b04120f0203030705010903080702060709063b150306060a03110f12040c05030607120e010f06090207030806030303010e011e05211606021c0903020901 74
    0x800403001c20020000da80401510140040e205004203a803030411544016a015a00c200314213092030440c0340d82840b20f001c0749000c030203801400fa80d60350320311410203901030700c1400e00403800540c19a0005e0840303031001c500e10b401001e140d0795a80040346001405c40302800586966100009244c40c08003c088071a900003070781d4405101404036000040d400c00204000300030710104803180400402500b980e071002150301d81086030800042c0100d54006001c4140620424213480203400654840c1026020640d41d02c110302c10700e0441d0b21140ca0340141519108192001c4007c120301e40305c1c0304405034458004604105e884000000c90031403082100013921100e03400180c0c2207038001000000e040e803100610f82c1c045811303070003146154980758600c031a50005214081d01008400c0a044206811149400003000024030107000400045d007503c08000e620301400c02248508c0c26010403401104204400311200f84c0c01038540d00e2030000da4466040c151610300410800030f14008401640d8075140b113030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 166529406 1250 166528156 166528169
    0x6040311010b120c0d061409010203040501060603231b13150c0201120507091a030a05060a0602070501050903150f090c03060103020d0201030f06080607030c090e040b01060c0c0e01 79
    0x40c5102454415084031039511003207005800603400060f000d18005954a02d114065178411082451810800c00402c01c1d84609003aa81c500b5090080288054000d14000d6010307000800c01e03941e079100290220ba1800b503001840300300540800c4440751028850581c440c41d00b40c00c000102e11412a45959980079003211031080c2103440c4288504202540400d242c2001030610241d00d000e280c0003e04032115900c8002186602c5200080c0764a1007034a4400050440040803076000f0951100381c815600220b94000496140ca00058680c3c5494401801240c502e030300078100190404004407004d41c042c0583d240c1506c00e41d200c1c10080000606d40601c0703515408200301c000d00f8402865814081004543c920030361181c030040c40582c3ea142008090f50340c0c242000604500312414040c042d0402d0382c800c404c18014070007080091fa403d6007002844101d16030b02d0303c45140d12170741204403070903041e038014010004140051100c50b00800111340c40a0140d41c40350410390ba15020307030444000076004007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 166530656 1250 166529406 166529417
    0x609030209090f031606052a2809080c0a152f011b0c03020709020a03090f0506011403070e0a02070c0f0b270904080d0f0203040c050901121a04020f03060403 69
    0x50110a11400c2d403c01523295916180001c01c8154100803220800d05c400914000651100d11804000c0191140e040c10070f1510340f1100c4001c0d02a019580e948583e50603401008004201072038580900801e5490400c002c24216451503011620704190404421a1440d1401c0003804e680102030044d104c07507614800411181b01110b0280daa4404d008a040b0a0154604c0c10500281c1c0228851084e10099032005071203090340b040c228080e040c11400079007012401503040043c41000b151b92410788a159a03d4141210880140742daa00014071410003410844d4001c07d1019280e6001846514042c030200482e8680740e4181c03103404410759010035028440040c059100700001c2c40c03402c0018140d8040c1c0c0743c0043d0000d01190b06020001e00c01040001d00080c0c25410344c41e20b5100354640901000119100e04c2d091820f20b640078409c0c00ba02d8440c80c1714000028007050345030030740300c45d46510244505d10450300740064017503c2d10240c0100c0c0e000700d410280346035548003080400c1c4120300075500c0307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 166531906 1250 166530656 166530697
    0x303070f110a0501050f07030c1106180306070509090103170f0a03050115030b3d0302090312070812150d0302010212090705010903080c010e03032a040609030209090f03 74
    0x700b050114982e80404c0c10300c282408805a10031001003601c40403a0142801016001036107440280c1c0740081c4200c80d481440803a401c0950311180d4076081d9800c0068080340c6164580002c02c0c2e9107401450b240c143e0004200b401400000c50118041007400980c90506040c20060b846085054200301d000800007540c51004100a01c090710150700c42c1c42c26418108280c00b205400701da2911100f803c1c1255003088505002c5600c0421719160049801c1d0090407a14484141c034014060343c0481d880500c030f44500c85651521014020880304d07229400300c80c3d01c0c50002d44483d800c1d40c0b01030013810704400309a480e20408141d1103444400304041e120360300059071418400203428110302e018103101090780c00148103104a07604030b640101504e420800d0309071903d00607100325014120725480070140d800080f0902c403102c90003142c0380100c004503401c281c07011441500400000e00030b500c41d04000581e240010030140c204000d41a8100d0780c0c00041d602d001d0120070f0b680e451039200341821194406014007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 166533156 1250 166531906 166531909
    0x60b0c10060905040c060804030e03010216140d0503190b03103306050d090204060e090f030a050f0d020d05042d0203100b03070f090204090b010e0a03060b0303070f11 73
    0xc1c5009854014810440ba080c25101c080720725042d8000c2500b4008018081010325004000380030002400a00941d03603520585960201d001410714122008a010200c60801000210b05000b40d81580d5842c00d007180d865038013910100742141e40c505810b66489401030225141840082c120001046000c1200c180c0d08011441e19420b100c41e2a5030521404540c0205aa821184000311591441d21540396100034164400410101600941c0310b468104c1c00182c1c4544210320b079114000c1501a42c07240368440303070351039100d118429440000a100300061600030008001510341c001d01d0340700050808411048910031120196025100300017021030020310300b01040702c2c030700b40d012043d51005046074995010940d00c100d4044442e0166880e5546000652030800140004010030002003803036030b0b958007071400254800c0c044e50b403a0078240302c1c5006655025142681c500303000078203070615051842c0c95250080c4901c007200b40d4940410030980d8086400100003014090280c0081490003100f01e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 166534406 1250 166533156 166533161
    0x180f0712022b150311011407060c141806130305150a0c03061a0708090607030305150f030c040509011506030e06070311040902031b03040303020d1d030403031101060b0c10 75
    0x9680945034140200090083c800c026034904681e4000f0030414040c000c0001a02c1422480c00b074030b0060752000c940c14080c0682e503086102e036035810f91103504004c604100e807a003461040d00749620761681009416000c6081980c010002e601001070010320060b100e40e1000e0a08040640b0086034810b40f509020741c006462041e030900113480d0900f041078901c0c00c0494020078020410b000d112640110384a02884403000031120010002003e0300e5480145280180081400f5520701540798010103801c1250f041c44400c41d0312707041c2c2c010001c1004620084c104009004018400c00c500d540361072042c00d0884415240c40e024102c1a00c1c045520140311580d2071a0600c003e005100b054200b103c102000c442c00e404850076559030380c001580d030b0b68070807407520403030840001d031070545071400010042450341c59070140c081044841d01c140131030003540d8051046954000801409504200070800002c0d0191400d109089885400403590319682e03810019950805941c2c0d4510b6084101581001d040b980b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 166535656 1250 166534406 166534477
    0x20a150f0305010f0e060f03010c080709050d0809060c01140108070503062a0c0a081804050714090f0f03030a09080f03040303020319052a010b180f071202 68
    0x920303007088551314000240003055030034401d817401071107064041100d9880e8030103e1004208060000c2c0034a40f541d000c01803510350201e52a500041d448500407581d89003600031044210703040b041d954180b002c414100304282c0e1240f12420603e659031403098802101561a6900a0007808081e15806141800f458104400240f0031074180135004511a20f8007801031402d5940d1200021250300c840d000c4510038540200384c400a03061000104124501d02000d554082c600c0741300f178505201540f83c6070f03400e4038040340c2e448004d0401c84060054490764103000c08151610f810060400280c40b100201007802c41d801906284000b5020f00d2013441040410071502c8849880790300190b00d4903166440080d182c0c040d01600e00711080046c90300c200c3c014454400c0da014001c0d00908142d1010070f0000c1d4040485102003081499420320b151002145452501c0e45510305006505045540c0c0c1d0751007407603800c00014184002d200d0411a00324010344079101400c000c1c0ea241c1c074804d68041d1140d003040342e001c0f10f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 166536906 1250 166535656 166535687
    0x80c040c09080a03050306010210051501030606050c071e0932070e09070908030a0905030c040209210f03070807050715052a0a0507030b0c07050d0c0807020a15 70
    0x101d09040148000006008060540515000c1c0d2203440f1100100e050880d0803185800c805e082074240a036030704040e40c0c407000081d0247c904100c407683d246010354140c06517201402c1c40b0b0b00200c4080143c042000d00d240d8000d103a900f4820300f955142d068100c01c42c1c0054a01c001c1c26120010420b511544801d5000c6a01d2003441000c00e092a003040010b008680c41000d0501401030320b40071030b44403800781100c400a09111002c2d00d803a80f146060080035140380d40b146a229120b0040010f0140c2040d2003120350140c0003901001c0c0b840400320580c800c000009954110521a130f50381922014030030710180c01040e108480585c3e4a10190074880d10340500c1d5080072b403402e400095002e07002a041011500c840c0701ea0840741c00c0c50142074030103044013072540d03403500710134000c05204004000c008203940054074030a02c0341d081c1c107403038041e0f84000c00d01590f4001001507000b00d104101780350060304416406403040c00468600b087c15030201e000848158040041904481d1044031803580042000180880 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 166538156 1250 166536906 166536917
    0xa0e0414040209011a120403050703171506090d120809010501050406150806191206050a02070c0b0c121303060f0905030316120203010e101a030a050a0e0106080c040c 73
    0xc2a400007401003c040c0310391810300d901080c9081040b0020026034040790321803440c00e40c0603e005e04014180e5400b10f80d0840010f00b4018503014041e80d4081898020700040c401400609000e1040c030000741d0104522991101c9012800d0780080d680d0408a2000034296691000074240043c02d2801d580b01078110300d2080b4149001800003528440c0b180342a040c0a1900070b8181e25100c0103c0c40300041500030043c0c12042a801103198003c21902c4155070340714a004005079654482404101c2c003c0751802480302540210401025980401810341d0350740030340c00d54800d2455072818103856130001103100b8511080c24020030911849208554140030110380620407840f00c0c1c0c0e03449482e071000400d032021a0710240131106644c0c0c861003400080040001c001c55980d40c5980d200b41150a00300c5820044550f107110100d0b8050184081c03003500040144c4450640c0ca4440c4441c015020003810300a00750f0f036400424000c1002400344200910400c0c0242038483d407440240300654103005500c506124 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 166539406 1250 166538156 166538161
    0x1315080102092d0f0d150515180105012d0c060c020109150507020309040e0c0f150a050318190b060d1109040201050f04030c05030c0919051009020a0e0414 68
    0x1404683d00641000c01203481a00741d208800005826503105003020b040301510900301008094a0741c80280125603100103846000340c0c40c4100300000d64a4071034050030f0713207191004204950080b815050882c540b09600504400720107018800801c60f8202030380000c810000640c14003c880c850b0701c0d4060202d10080c4415031058841c5960f043d11450a22501303691440013a0700d0700e200344290341d541e030801071040c4001c14132520078596581800d401da43c8140342d010b01c00005c0e49407c1e8840c05200d03800702e610b2401e016510000b0b80e0541c00080c04440c07003404540011001e041c0c10b00079200e42c900030100c0145140060f080c8142500c1c00100414011403640c25100d006c0b5940c115103107468001159152030f103540700e10048410380108008120603650205010080043c4c00b00101c0c103030350007a811607647c82103080401c184840166403240e4401d030303082201e46a503142600000d070311010340c5030720040150382d03003c8034012030344000800800100450b007000301a00e0140122401114180100510350 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 166540656 1250 166539406 166539469
    0x30506090601181a0d0302010f0c030213052b051f021e1e1608031314010b01090302040c1808010b01121b1209120806030f0703050c131508010209 64
    0x5688201c00e031045c0141401842018800d40040044010b030110a02207030310381c5500a4042c1d00002040e03034540d80703c510082141d0610b10144072010480204100400f0980c5800980c2a19510000c0e03a042c0103002a0030048807242d801e442402401e0741c4d00595450701c0a5200b29070711428404c001801d03a0403c20f400d01e100e0b1040c00b10101d4103030028103030794540c0011100c141200000200074805507004c03040000d910f200c0842550f80711b0190b6198007080140100c00c0e402c030b81c3c090ba0007031f010580035801800035050590020668000300c4c20306991048403100300e0300f0f0440103035100043c3c5a444039000c41305940d00c0345140c1c0d40813500b50000d00c00034001d40321704d08000c030810061400304442110100f50780700e800c1d00010881500203040c02c01088002c0300050030140101e500ca402486090100c0424450010704081103039044000390010445010030007844408043c8513400d02038803512100010000743c9a011b0061181d500016500c000c403009100001d0484ca502c03030f248550b414a040c422 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 166541906 1250 166540656 166540691
    0x9030203070519050a030302030a11070e0a09020f0d06020306120c0a090b0a0f06030204052707140c0105100e0708042612040302060a05090c0d170403050609060118 72
    0x54030001c44043c4540b01d040c5014071400d800e243c0c002d50f40030703c000f48008241900400200b1042020703a8500502210700d06159549081c20300c2449150b1a098001500d82c280581c0204040c501c020701c4000106022000694860f41641e019202142d001050010510301980030350008181103000d0300c001c00e61100011507510291080c0d441c155203070428441d290780c5110305480030b09444d58070322500d5501c5540080007900036000d0706000f5098450203c20480820345282d13108489520000300b00c0d5601340086070b00700f100f01c01200548100380441e91401c4000e00030036110351004021148060701c1c0088542c00d200303000c3e00c50410700081c401408082901c101022180c00b1801c149807501c0c146403a146038240c80380b1502c0703803981c174800400d000406602040142c040e10701e04c00d0a1115441d5084000e4442c01a00c0e4166844580d1aa40800040c600d440f59025618481081403c01369070b503c400d03081000c101e5a001c642c0c0c1010300103102d4071498018030b06142c1c07001101049100c0a54010291 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 166543156 1250 166541906 166541909
    0x10c0302120a0908060a02040e0a090203031914040e0f0a180f020310230c0c03040504110903010606120e070617040203120a03090c0504050f010b030c0c24070903020307 74
    0x80c00c1100003503102e0042d0049003040000c2c007060045a41519050140300c00a400c18050b03a00d0800c4401e01141620b00c4034043e0b12139403900100654a0201c60888424040340110048403d101c088894500b1990060015100600c030080320400030b8500b81c0c0c02120044e8008018059962138042c0c0071116404080c400503000d80c3c4808286220003840c00007034982400341000d800e09038240000040034062110142c2038182c841600130b51140c0b0b507803200c00801c0c0601800401241e0003480204021714064000c455108002d05113140b500e1520008682565010340142c008910180760512004269200341241c0c00322030409010170320b08061001780740300c080103802d140300d0702c84201260555400380002c200201125040d25568803e104015014200c000001d4038032080b100c0c40000c1c1c42c00c007806458401e0140c068202038680c00c288040280d50030140200c000184140000000004200400b0220074490203032541d0414859400f20300e109001004c1a04100c000d40c0c0420060701e00103003000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 166544406 1250 166543156 166543183
    0x11030406090b0c0f0d030b030d020601060f1409060c03190e03060a1a03100c26011e0b07050a02040e01021809070309170702040e0f030f130504090b1005010c0302 71
    0x40d580ca500410071403610364881e00d002c1ca135000b06441e01c505140c25500004c00080c080c0e082d10701000264405a0321400c09101d000046860700345110382c15489150b15a5011114240340340c203240c0c50308042420781e0016903406145603c00180c0804900ca8210041803483c19407612000808156010a0311000058035149941c0d03120760380d00c4a8494906051010040c01170212412890020352003c0038103803280190300440c3d01042008460b00000c080303100e09451031504003409918094030308030494400381d030000d81030b540c4078008201224090010440715001e07000902c5040c01e81e004110403a020140e42d8809a8410085001c000744060f4111000e21004c0b83c5070f00c2c0e41d80e242c90b03043e0040c00b81d01c40020880209079450b0407070041e40310081d0213014000c0d034081040c0c20581e46003e1380c0d00e205a010070b825902c00d00a0302d504902e0f5100800c00714648c00607410f80c40c0d98071000f150644401040803284409030f01c040000b880c0402c0c0919001744000d203880c91100440b910080e40f1011000e40c00d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 166545656 1250 166544406 166544429
    0x31805150403260411030c1e061204050f0105010506190e0f060a03050a0f090f080306040f0c02010b12030f040303030203130c0e0411030a120815120d1103040609 71
    0x603007454002d40c3c0c80d0340c01e04000341800d01824211046502e40c1001210701300c03442d064110011045080004007819002c101410b0070400c0c0142d5015929007403c04400389a10000030404c95554100300c1248501440c03081000b4040d0314000346006003515416004140180014446114030b21040d46c0d0309000e1012a040480c01400c00a01050000b81d02100c07480e0030900000300030003615403662049205001144081000082c1c0520354410307184521001307045c0300c8800954502184001e0000c41d0000c200900002e000d001c18110306042e5210482440c1c0540d540300311481190500b81a40100940014040d52801da548028004c060145020240816a01100040500400064040000d0f40055642100c2a0360f01840e81c00803004441c21580d40b842c0c080b40c031086041c0002e40c2d2410580c0507511f1010391480240460702c2140080190b00c0c283c01801c0703055043d80f2955841e01c85d03182020702400303914038892400b1b081d902103407021a860350720401040080c80d5110260006903213003948507 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 166546762 1106 166545656 166545661
    0x6060c060513080909130b04060501240f0c02040e010f020a14031003060b0409061104150e03030306210706050d05010602030c0a081303050703060c03180515 69
    0xc010f0381c1d060002d080c0c83c3c90400100d560240b405600403884000c26219025001e40c281c40a440726507076080141b1808107d40d0541d50618001caa600001c420030003001821a0005c200309020880e00d210404115900c5400849000e05e490b4002d0142c024441c070520000c0d4440902813010544102c214120741071460150382c4900c04d000f0034200c00c0341c5182c403000081c02d0307405400e90780300380c1e5080510000703100e0703200d51031991180d04041e030340741c6040050084415810424800902008000f83d140c25a0000304590340140b06a13400340211030310012410751560f00d0720242d401401441d10104005030301101415181e00540c406010990b40d0350000d03a00d0f07100300c4903001034076008007a40201180d10345004206203070201c4a400019584ca80744d0038108502ca8104480d0303551202040d0f9105ea5050107075041c042e09030721004481c02c00365910103588140d80101010ba101d00e5000 = true := by decide +kernel

theorem cover : BRFrame.Cov 166366906 166546762 := by
  have h0 := BRFrame.cov_init 166366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 166366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 166366906 ≤ n) (h2 : n < 166546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
