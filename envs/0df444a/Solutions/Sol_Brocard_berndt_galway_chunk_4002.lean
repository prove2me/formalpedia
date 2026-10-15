-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4002
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:18:11.759181+00:00
-- url     : https://prove2.me/submissions/4fa85277-94fc-4c51-87c7-d1ae94ecd99b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 719604316 ≤ n < 719784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 719605566 1250 719604316 719604367
    0xf0b090a231612121b02090c09180f01120203150619080d080601090b0901050f210901180c14030a060f0b1e0901051212030f090c01090602060604020a05 67
    0x4243d51602d00320318503480142440003413100d00e4064502c0003070783e4074800c0389498042c1c90800c1c0c01c0d52140c1004125102d07900000d640000c004d00340203e03188400002520034240340c2e0441c505642c03164860141101041d400039416444011813408031b03041c82c43c0c090781018010b024240f805961f60080340034100c00741c100162a51240b4010603030164441c24182c2c005200f03003041d00c0302c641042c100d00d4652040c0d4440324141300001a144450002c04822654140c03643e0400320082001349440c02e03028402038640396190743c00c01c66919854810702848440444c0e0080c54030311054034210801c095005c1d0707410700541c140a45054040466034034006c1044640d47e00380c0004941180c4810403042a40c2048103c40500001055550b11f44458a1003419140b046600c5194500c03442c011602c0c200303017181c000380160b0001c4148101c10403c80d04c854060881d036400c0c1e80032060407000440d0401101d00c038601c010b0b030110011814900f0903600401941c00c041c5840c1c0d103001850011104000040082003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 719606816 1250 719605566 719605589
    0x8190c06091101170c04060f09030804031407090e15130c091b050315040b030f0106030605010302010e270a0906060803070303050f07120c0e04090f0b090a2316 70
    0x1c9050361340810032035005940041115118200300425960900590044a0030f0282e8904840e0075a401084214011584800d0165440340c80b0701e402d8518074040e6800e2240751207280004900340146001d0362402c0c001510041244411901036058460030141001c40e543c14401d4055010840c09159400079281c0240c000c114101c00341c1e0051988000741144804014040c018400714170362446488801100c21200400e408800b040020304200010001a4007076191250002c2004541d410641c1264000d88500c03100100f00740511000c10400c07841d42c04e040140e10b0318061410047d0040d187c012450080009400c1c42036584c0508071005500240c0c0c20380e10104540003090f6040c0181e83e440b5180200c0200b0604140b6000703045881e14440441c03005c5c0e11448000b180c0d5106243e11170500c00002e04c140812011400e20030300508203c94141c0304100741c070300040d030350110001e48400d00e203034400c0d4401c0401d400075107c4030081c2c280500b040241c1c0074508080c3c210f0784091031514043c1c00c009201 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 719608066 1250 719606816 719606843
    0x60f0405091c03090201020c0f120a0c0812071a07030213030311100e15060402070b0a0b0109060905030a110d120206070e0d0803061210020f0a1101020708190c0609 72
    0x1d40e1110381c410001c907080500713020340c0e40c0060760301240c00114003a081d5110390400302d941c0001003ea0804041c1011350380300d00340c5100240003040d0040012151602c0c00c1d00c0e480204c42100031418441d5031400340c003601100c1e0207181075051140d0142c0d40010f061400604200796503130004000c06003a402a1f000034081c40760041a89028010016810369002040250f008000203441c0c5a07210302c91040340310214000010b070262150f404460300d441e4059020308103442c001d4001c40050001c0040a0300180c140b50300810424010403080b401e880000b002424021400c0e0b44201c140403000504541000035400c02000085580306da14403600c8040d0082c1c542490700c0c032401031605c41154000f610560200001c040469800070440344c0020b8140e0f00051020045058949001c3d03200a562001c2071000032840c41c2504030304080e000c0314060b5a12040d101510450050a038041c025000d01062410820350411511140b8409062050350401c2d800c800c640381c031844129440d0a000765080d81c80e00ca003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 719609316 1250 719608066 719608093
    0x81207261c140f13051f06030b060d1e0611070515090a02060d0506030307230d030608060a0b011205100e0601170f060f060309030c0f190308060f040509 67
    0x4111040010211030b460703034a8018448410040080c1c80c02c0d80ba9401c16581a05200f03051186482c01c1d5000c4003500e241c504018078240041c8030510041d602d0a81036008a801481d04410307443c5003541049080501e0481500480180240b018049503101e90f03038880c4154600c19200581001c07802100035200d141d200c40b0383c031030311518010024031641d00316980701401a074a0800740d690041c034070b603000592a81c0b4080441d01c2c500c03860402500c50780103144402842040b26a00102c0c0105950541d0038440d80301d5825000d8230001c2c0584903860304010001650300e102540415035580b01450b110580b04400d44035902202e40a481c0d45035110a250380070700400005000868105a0a18140d8551003513401d250030003042c040c02040e02031001201103a15507071800c010003401480208965500c1c01c01d50200d9969034814411503980d8007501210285515000c180342c0c81c081c0e5005c02074250f546103581d0484203024000c0c00e03554003034480b81000200da11580705d16485011a807009003c0148240e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 719610566 1250 719609316 719609321
    0x2031506010e1207060e0d020d0609030e2409010c0b1510050306220605040c0c0c0e010b0a030f0f050a090318050a05120c06030f070801081207261c 65
    0x401143c000d500c0880c6209240324001407010450f843e45c80e2690901103a40002045520820350180d0300401d000513030002d2007040e60214081038425144c8480c00c0303c515042c8491110715911080191510300c0300c080031960420020001490705140c000341c01120359455420107081510700f9407180300034012068590500560b511840105414454203518004001402607602000690040071400c181c1c0001e036901c3d500000043e000040c030030b120004d141c5500815400c0001e9064030102100c2000040c0c40f0b0f20b0200d0311b03040e01d103c02525481d0030440142980581498410715500343e558010031101d2070b04034414903010340e094405c00300705c0200324180140307140d010184801c14000520020401550f50401d41411600b0070b85060401c1013a1703101c07650034a20f02107803460304580e00000b040f504c980c624a00c07a109201a0300c0c0e804099072112140781d610141d5541c2d03131070101406c00060000c0707200d0000020880703a020381c81c580814000a01044243c00501056522002141c50710541580e00d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 719611816 1250 719610566 719610587
    0x11401030b07080a020f1c0603021e0f040e060606071a0c07060f0c021e0a0204141b0301050618031e07090605041b0302090d0b090601090609020a0f080907030203150601 74
    0x105021740c00c00241e80300400722071040c546481146040121455102821600082c00454004100300c600c1580b030300e40b040142004038441031054046084a41c81072409119100d45103074030f0341c02810569940c8050003455440b543c41991410b10f4114415580704445040a108100300c0e000c2c1501c030000d0b0300e0050b05031101181814129400c0000c2c0002d8140d000a105911010a00c410314402804000d60b904041801c440a50450700300341820f01d072016803014081c000d6040540d4003541d0200c80001c184c3c580000c2c003c0c2d5902403401c0000900390341070100745048900e401015100030305c00700200344800b0b440036003006030307145c02c40c0d00c003000318000d240f040d00c000f81030a40f01800311130b50500001c484400c8107403010050503400b0420581030344034929109082035110220540d141080150035503540401d01c5103001190828002040240c10780c000e440346030720551615203130345065540070748400400422040d25071041007000030150b50200856903450418281904450402c60001400230045 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 719613066 1250 719611816 719611831
    0x60605090603061b130b040801021e0301060c02041d06090d03180503070b100512070906050f0f240d1d061b0a0c120503090c0f03070b0705011401030b0708 68
    0x19004120f60424080d000e01c80003131001e01c2142d51a01201d100606211140d005440314103000708002c1502c000550003465402403407a4426154018504214124442409000c000506000c1540014101600071400d40e9442502404151803404216403038480220b600113007690041444841040d010701c6103c58052242000f00001c411940310a9035910800400600d00040040001c480f17040303d4410790301800c0c0042c105642e6605130a00d03507a80d5105070244408042c07030314000081e0762070308902808441c00068200c0640300c009c40200300c200e18562209840c03420480c01c8800740b50f0755400040421040c012030000782da42c0311442607441002907030040300c1242e0140c0140034001d20151303034004086150540040d80e031011441d00300c69100c81d100c030003050000c0c1c6400504840e50054003851150000d007003161841e2011b50100709014250103852a01900144403c0c442c0c010084002d2a0850152001040900c4004609400c10703000341e00c1903442002090900810903882800140c0007001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 719614316 1250 719613066 719613073
    0x9041d0a0c0503120a080a0902040509030a09090b2224090f060e190b030307061b0f050906250f120e18060f09010e1503070e0c03070c060504060605090603 68
    0x442200e0130055125210030b40051081c1500025500895500011b1890f82d000d0f006005e2410304511259498001d03813103a50128502d8180825a11400d1050032800c1c04010300260290514030b489060010050f2491180c1039100c01c4a078003080d460070705228501c080340d26200c084034600489074086410301032134003240504000f8200102651414200e0b0421a02101c4840d00c2c1c4000c8183c0009014805010b505800086000814440240d12041c0409500420b544288ae03003504c08907282140040d26030b001c141c091140559a04104025102c2540700c0305490140302c0c03c508414000c81c1c510b02c421a1210703001c420003001c012011b89003490800c20343c10703d95120141d183c0040e9a150b8515a10040c0c180c1510008009a032406428080710304050003415865844008a46030f10f041120a20f5510308000034841c00c504000442c1000c9038681d0740c241c0da880d03d90429010f00340d84054401d60800104d60510700100f076080c86543c1c082d611a11000524918240a1006802000789554030039003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 719615566 1250 719614316 719614333
    0xb160c0f051903021e0a080604030e0a1d070810050a12020103150b031501140a0801050f0d0206040915081902030105010b1204060b010311160b0117100209041d0a0c0503 74
    0x72a085ca0a203ea01c0c1c41c44110a00e622030a408640c40f00c201c4d0344000041d100303c1c0180001c4c180c00c581d0b05490038405554125000303460b0346240303100d081c018100011034054540081ca020744110b4029401001003901d0304507240d5520700003200304c01650800071034180003c40d094215038062041007000340d5042c44650466107802c00c2011240002403000c07042c0f448a82422070582c1c401c4110b2880c110903c0b1015896a803800c000030111002401407602490003d12086241d00d4840081c00805a00600e42490700d4105904000a0300e0741e400c0c1407017600660b000100c0c41d58402c2c44082c01d00c0f203000d45146c03041003050040500b55001a44209030b040b400b08044400d04407010358081d4050380003000881c0040c482030048004280c0c45a65503200303103010030417040c010503080b1035039105e0340141603221250b40c07541203110400c2802d40c01b004465202014840503041e680e005042000030003000003603030b00714501c40c2c1c800300c51010301c940515130044804002003210501d40c000290000750b00502000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 719616816 1250 719615566 719615569
    0xf0c080c010e07170606031002161e0b0a0204052209050a05030c070b07080d0e0a0b09010c02120901050a08191a01031b0806150d09030206042009010b160c0f05190302 73
    0x3d902000480300c62303940014440e4605983d503868081003030f51000302840714841032082c070b6a100c075152000310707000c01ea07000c0400c00c084d6590094809450000b031054076000b40b09520002074862400100a000d0349032007500000c118140005c1d07a050f80907a01441c0d842c1c880c0b82d40c660504000c0d40110301413001c148000400720790710700300b903c6400103d0440090000c40c00b0f11601e19260300404000e2031000303081d007040380403901908034558a6055408403440380c0122464a1800e0141e8030225000441c284070904030a40300342080d60b0420344061407502c001484075000b9042c0d848030f13040d407102004903a03c0102c00796890300c070b43c50290b4880003800160003e04a002050710f080501060f11a0b640c900001d40c424000320700300c6000c400003403400c00007034046141c069114241150103a516021216040701c40c42020001c2d415500001001c10304940e080064004c0507400840c011000c0c0d495025040b00050340600380400605582b40c00310640310f240104000c00d80c10f070b808800e5051a010a001c00c0103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 719618066 1250 719616816 719616823
    0xf06180721080c01050c04090b0a03020d06090201050d11030f011e031202030c0f0c0a061818090209090f0c0d0b160525020405010b0a0f0c080c010e0717060603 70
    0x10162046120016039058101000280079030083c2202e15441c0205202141c04500010000c07250828418001e18000000f080b014460320b10020b504500421101000241264050018580b05040150924226400c1d4100b280c0b003070914071102c40c1d400810f120802182e64140c500402e418481c03c030071010103200c00305034800544401060f000300587d0403440c0600a00680e54003c4444045440d05200322201c00c1d920b113001c0001ca8002c050f00c060100d0b0542c4907000c0b4044c03d00340070f00d00c2c1c0f0155191004c44000e1250544002c030210381d840d4426001a5100c0c00320702c0c00344003000024880d0000a541c0141842d50400e56144210251520303000000c000a00695210341701042105141081c81c00940780f0348036100e803001400108000d0310701e8011030b001106c803d9030f0003a0f808010b03a03070301c8081950840c420031b8190340104100e225402c101c2d52254031030155891140e4190b0381402034500c042402d41e03032484218111500b00d031005100c050300303d844405102e210000180907504005022903207 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 719619316 1250 719618066 719618099
    0x40c081b0d030e1f051c111b0111040b1c020c0c2b0308070210060f090c090503010510030302010b06042103020307051209030c03011e0f0e0f061807 65
    0xe00c4843d1521560590f10750361113500c2c011821129280e100328200c0014507130fa12814056000c00d80d1031b070000310403000b80d10030600300600c8956068901611010042d01102c04a41041a950f40b00c410760f448080103600a040200700040449807101d4030140c0d481c0c042c01050b600c4082c0b051042c0805035000c08006038442d0529010b03501500b00c0980d10f02084061445188100d003040400f810b80c2017010b5000040903c00d240d16400d4035900501c400c0328070181e42d607621510940c2e2140a02c180309020726a40101c0900d400c1d402c08081e01c0d580c0c0d00120b030130f6410807624900300403c22a0204180f41c2c080c0240d00d000003040713600754945404d0000e080d02d4008100d40c920550380004800c18201402003049612041d00b100440e00c214030014003003001d030350181200c3c0e406030081591800580c1414055031100c074100240180040c41c5020f82080145021000c14808641301e0501030040142409451440c0959802602041c58825180b2600012201d201d0080d076218050410041d41d40300c03803421 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 719620566 1250 719619316 719619323
    0xf041e03020c0d051507091206021c0f0b0a0504020f03010b090d082d070c1a04030605010308030612060c030613091a010f0f081b011403040c081b0d 65
    0x200500a04040703207044400000180c229148004100900c1800103404100703e44c20310604906030b8030f880c0221518011486045804004040c00344d0000d1040d4000d44060700450703480c54428079000210909459034000c42e41d9240380d030748080030843c0c00c01c21015400f921040d1425403400d0300004040109110500c0b40c00800d11002c10b03c8e4032940d0384d0050010030a904081c4058a4404e01044030340312202058941c00308620310b07102c2514682502040e900c50903005421440c150b80f408104008142007003141142e2800100008000989144038081c060b6000300c0b00e4948900e40302041c010b601101440e2841580d002c42e04102800e1003036011a54415800d43d01141e10340b024500d244040d24107104024442d0200b1100240d1034003c02e0005412114030000d40c4502650311540b1a1001031140201960368100200b8a01550345020341d400c82140189031004185000180c0d425580d041500e00320342e030100d0f0710800c02002c0d00401080c1070f070b041ca42200c0741c0e01c02e1042c800901c0c1c1510710507008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 719621816 1250 719620566 719620613
    0xa050909090307020d11040c08060d26040b040e0105040b090a09030e1c050c040605311d0106060f0504030f0516121509050c15041806030b0f04 63
    0x28108603002e20940310110382c0a8440384201c0641d280c0101c2e60742c03c940c40603010b2031510303003c00c00b41e601c1650b11074014500900305440504003a280e50103c00b1801815242c001d104415082d44420300c0d200a0005090b1130160507217490500041d580c9aa0042c4e1003d4416810300c081d002c1d00d90744000c041c0f90408202c0c00c000074150901e00d01515001c1031401c8040d071100008103001140513601044241051190050b507012031300050800045070550700649820810078044001c200e494042084e40c0d0214030400d0b0307170b08040101115000e44000c41c0b03401c0da040e5907201d110140c04c4024000d000103000282003103007080c04c0f2003800401c14001c511003e840010003040107001c0c03007820f01044440c551076490700301003903844980d000d0441c1c2642d54221040e4030b2501a1000f0f036013042c4118003a00368400048e041c8240620304001801c40b04150002c8805010440000c10100180181146140d04000451810301d1400d081c0c8440707600a220800c0302d02c000041000040000b4290341c01040300c0c4602 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 719623066 1250 719621816 719621821
    0x114101218060902091e0a0b0402070f0c0509010e0103051506040209090c030711031306080603070f060c020103050708062206030203070e15030304060203031311060a090314030a050909 81
    0x6030050075910403007402014408040105100310394001d005014002c1e14906a29111900c03490300d0703803100350400c510f1013004001042510080d80c204c0200c03800300520140c20403403140c9032001480d5202c8012079412048c00e07810026401c2141d0b4040c0108054400303001698519224203480d907811001d07601c410030040d000906255200c0d4103442020b4000f51202150b40390646070201698010380d09003001c2059070b0816080081c0002c00c560500400103172414115160000988104034054622503060081e80404140f00352600700da9001850340e503039080f03601021400054119803000d13151904010040c010840e584c1c680090501d00303094000d0845180c903188001600042085409c025494040d03020700003140d10314445600d00400349492040703003181090042543c1d907c1248104809a0030038000a10600005038a0540040c002e801f00f089980144002803015030003454290302280c028031050003840250120840701c903c0c0030b4015031404d10a03520192160103111000c07132140400000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 719624316 1250 719623066 719623097
    0x1140a030b0a0608010e0102040617060a08030c030301320d05030f0a020f010b24090d0f031d03010c020c060f0409111e09010512090a1e0308011410 65
    0xa00401036422400c0003070603060424040016040610401030290b00740210040d48410601c00c0320304466294590004848000c622150fa03510010100755004280500009030b083d014002403000d0710044000d5a903d40c105590100c40440b101d0100d001640c003c0121700b10f041804503200c0a100b003c8641100100d441d240441c0f85100e0402441d00720705010680702d00a40c1c00051f1001031441e030701c00070700c103031421803041c0b208021106c2c00c0d06100c000141686989105004000c1c28107040180808815503401d071200340441c602c450085001482429141900125080c0c103110200d60440091000c0b48120500a6032150017030364281c481c2e400000c40381c080807920401c440081c060180c0c10300003082050b11010b04d9410010aa01c400c20184502e14000c0c5010f004541d00100140c40d120709150307101324800320006004084d0001d5104d60040f032404030f019080060900c440d410031452009040c0d140c01011020706904c00d003800400046500c0295072903000c03481245909140442d0340100509 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 719625566 1250 719624316 719624329
    0x6041b030c0b0c010b060a09170111030f0c0d0204121a010302060901140909070c0507060f09171009061a0105040518270d1103091305100e010915060206070203030114 73
    0x6845c80c3d0700400000705c0804942c4c0150300d5404403510381e2840500018000c502c0c07402e940500c400388070440c20400000d8203c41050070a641c00100d040d000c0c81c10602c80545100890740070343c01c60000c1d16130382d62180c0308000d0b0a004521065107500d4440c1e03250751451f404595a0b0043c54090381c18400c103500f04c0c4400c0004001560040384d0002e003107407660b080c0040081c0c150b010514003a112800780c40c8020231428080d9080c82000d000035504d9150161600380c00552141e00b15555200902580c84014000001e40c010302040034010346000902101d030b1641c05100300404036503c3e05005091200b00007a13138621107000d100e041c1c0810b01c3c550641e10401c00b011035041041e401c070307412405404c4055140f00d00042c4801380106d00e4480c07540084c50a19040d0b9603008201c641e0b50b004130300300360303031401b240c0b00340c001d203411242c210000c13000c150301ca043e04250321800360821061a070f5183c070780c0c0440c0d400c40660003004104a0003d080c081c00e0041000303449120502840c1010b200300e0171b6051080d100c12 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 719626816 1250 719625566 719625581
    0x3020d0f0f0506190303140307031d010614030115090510032406141c080d33061b0f0b040809090106091d06120d0206041b030c0b0c01 59
    0x40d401005890400d0404038010101a1802405599400580035410410640b25015242c240d110742c0f8035200d55030740e5154031303500c018001d000705a120a003101e07445c80c040e0b030011814641e0f040046003040c20080100500c0041d5a03400e4402c2e03042c035102462000400f04010191911083c011031240d41d1102c04040d2042580c1c0b000700743c17006002e140301588914140045040d407004009100080d5100f0180c40c88a0034840305035402440242000c11300744100407024003c038030030481242001c01c0544900d04076400400042041c0d04903107104540c1c09030400000c80940d2081103035001e5181000d0f0010800981c0002c0c2d2903070246c44840040c140f1104c03101890120f98426804e44882c0341070300d40805540c2080c011140184104070011500c1e5006000032005d0741d542e10414122424009040e490710803014008942041000d003044120305d80a000010002e80d103600204882d0074240341002240103c845a01e4960b40300356002c0c40065080101c00044402c02945a622489400d08050040602 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 719628066 1250 719626816 719626841
    0x7030503030f1005060306060f090d0605010f05010923130b060703050405040b03060613021e07060519090210050307020c0d0b07020f03030c0d240b04170a050a0303020d 74
    0x3000300b00005052481051190440d200703a002030f40d5840c0140b20550009607070f802e9101c1d00a00c030580ca012103e1015200301c038402801030100341e04a403200ca04980f002e0b045986400c00f020320522095801c100e0b0200106054030050400341c64803040085a40f5140355070510405c082501100c07015070750740140782030910042c10f040d519681c500d40a01a64030920880340201c0c2805c807410035501e000b0170620f00c2400003610030100707101c0301d03000301c4001d5015004452002a01c00c0c2c4888000034440003501601d845154002401e09060700c5800c1c05180342003915880342e0516502c0340060301c1d8019214541e1f409030034002c1d01c0782c860500603428000448c0180740c2040c03981c0c1140c0e06001c5e150310700d035026022540a0342c1e026070034080e065032a4401110805e003110010041d50307262040b16841031811b00e0035013003489021003400034030400d00c0c1d02c0750b4003d114881300801c05101941d003400780c051484060301c0050140300d1240d522030340c480c2d041c408040d0503d40e0201c0e50101e861040e82004172040746 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 719629316 1250 719628066 719628073
    0x11010203090102030709060305091e031b060703050105030714130204050402030910062909030a080313050616020a031409030d092115050601020109141b01020111120405070305 77
    0x1800c0c01c4041c000d4100311030000c0040c5c0103050000d802400b0380b14a034068034404010b4102070107860441c011155030b16440d1101d03480100055a0051281c0d015000401c0090780640414107007603100400344c0724181c1195100f81c000c1c1c1c4080008403003c500070900c07410305031041480343c020803400100038000c9600a58200307000204008030b8560206500c0300460869404102d40c84c1c0700c01c10140da20340000d500c6115080407041c41d1200c0c08070315010306045c5a00404640c0c045800780c1c1e0700240c0380c00c150342980205098540321010130805015081e4001e0305980b000ca2030400f00b8500170756030707003c005000c3c0901510b13480604650401c2000c4400910f0050100c0b1030101c000c0c0001440da065600c104200c80854010340001c1c0462105124052508090f0b07401e000c18000060b100204405800d06040d503603201c0c40c440001da803c406000c0006c030344c2e502030000c0c00e00e140c550b00740842c0c11320111030442e45005c21500100814000790b0f102450b02d00b180d580c0699030b600d48985415115000a01b00d4417 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 719630566 1250 719629316 719629321
    0xe0c090c090111120409020f04031211010c050a120b040e07060c15180305031e2d06010207060c020315042a1d1e010b0901020c030f06060d020111010203 67
    0x500034006101d5140c0c2a0b9521161403070a41e02c941d21503102d1850003040c030104010030861003074160041d14180c500100c50914207a41ca03500d500060810400b41b9012a00f0441c42c1d0b65040c1c800c0c401e000c01d4001c541041451710503901401004544d01060301e80d00150b0b0b422101200341c440f036028003410010030301244c1c080c03911480043c140014820085074603110485134050205003030b009925925890740e04082841c806903805903902e401c010000001e02c0074684a58442d000c2c60ac0d0064002c00c4035402c6040280304420143d180f40c0201d059013115068000240840f59078001804400c032000c0d464404941c081d10310020381080700e00c0014001d0845120f081c081032003c14aa07100d55030409240043d940703182d84a14035a0302c1201d1007466441e446000c05203100302c80085030b040c2d105080382907145d8010107d4440d000801001e03004030040000106d02c080013543c04000c3c0344a00841100284000760f002d14200d0740c0da03400240442d0041442c00102c00031640076030300207040001200300135502c03071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 719631816 1250 719630566 719630581
    0x3020708120414061f0503012007140a0c09050c070f08090d06110306010e030f0a03050f04231c020307090209060c1903080a020f03070e010e1801180204060c060e0c09 73
    0xc4101c11790740050403e82e4000541450148204031520849801d403c4184107501c412065903004218281e4188000900c00c0703200c1882403102142c0300b80704216801c2c040c3c1c10440c40e1401c841c0e004000358240740c000c020550114070101025035000354005e050992310540900451468494100020801400c022a42c1181c4048138003942c85800f0a81c0c0d02000e540700d900405a684202120480180d0018001040860712810090041c0f01e0300c4519686001d130740308050212540d43c1110580c900b691412051428a050807400781c00300c444080784007810360280c00180d00c0e940c1c20721401414a90001d50a14075440d44030036900821901c41c00c4e20320044411300b00715500942d0840441c0052034a000244003641144251219103d07899983c0313040d6031301c0c0c0c501510203411242e2114103002800c90311042d5980c440e13144100302c07858085d0089595142498003a0b03c400d0783c1d0124903d190051205110743c1e075129510a81c442d03040407011407510825560715007442c50510b01e0344e4002848104101c141e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 719633066 1250 719631816 719631841
    0x3010b040f0e0f011811010c0b011e060302210915090f010b031b0108090c0909070905180a0f060905060703060303110d0906121d0606010207060302070812041406 71
    0xa0482c01030a0700c0407212082580b500f2201802c1a00c08a41e8a1651280c0416600c865600041e001810004420985515002d800c100c00342e21850b070038001a01003544860050059000030000c909083d400c5c1101e003124542040380c07001600c1912140c1000141039400c003081281d44801c0411850050b40c100700c16a075443d454612841d1001d50b00b0803904c50347c5810001480d8121400840604440e00e546c0c200466070840003500c000f5841c4198007451015070355110782e00c1d0140c60308400400c00307103180c407000030241d480082c00400c0c80d25100908142030000480ca28803100c3c1e020711108140c000fa440c000c2c00929120380c2c0030300144940350070400d80540661100080d02e0103a2103800740380019180c41c4c0d80d5210240347c1800010740e1258104800b90144c2007240003149501300105420b01c181c0300081c00d0021011501c407155000c9418403506c3d50301403280c4405045a440c0c02e6190400c0798036040080d00c5100c51400040b0142030004041c4881a84600203a244400903a0854200324103450344 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 719634316 1250 719633066 719633081
    0xc0e0402180a29030709030b090c030f01060515090a0605030c0d0f020403022803032105090a03081003030203030f04080906070f0c0b3103021909290f03010b040f 71
    0x74450a100c030f5215000c120740940e4400c050380e0390303441205400c680d20489601c00250903a9401d20815003900c0896400380b20300e41c10481200000554240b03031a08010f20113110f0260001c95203410000007005842d000720040c165125410603503525190301d200318005102e03c0d40d003d00014a0040c90850981842e0010b20072280225010075409060811441c1c6020000c0c4a901d100142c040003040024011b4804c0800c143d602280050192580710b009421b80e03404584040080c0c0119540100300764100359500e4008408220070140c9900b19540650707280320240c900303000041c001c0001800c01c4861011190340860180805440f61039900e050300307040c41502000c803412000c030036000c15200642d0081d90322800d040f0414050405034100c0d2100c0d00581c40700f03548021804030760f0210158503581c2144013000240394a4150340e61030700350804200d440d83c1010440c44605685c4000f41c40c01d1014003403640703c00441e45274202c0051076000030700409080740361541050030080d4802c02c28040b82e2007401e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 719635566 1250 719634316 719634359
    0x2120c030a05103606020d0216051b01023c0115051c030e040b030303011d160903030f120507090815060d14010207060f0905100c0e0402180a 62
    0x849038074900c601d00381440d0400710b140b420f5050a040d85139480700121489812078095040185006040d0f15140e059a0111042204044070360039490100101003003000036680d6241900001a410800000d440340588810041e0b12080d02c01001d1810b81c0709070395400c7c40c448101134148190a0455164040c2541d440403009041c070710b030000030f0310381429130b1580c100e0b24100e1034505200c411036409031400010404440d40095a50fa030103c80742c0c408200031400303032469402c020005401201c4e4080c01c00b800412601d20071031f8000c1f00851403604054410309032641400d00076101043c8620880340308005d40e0802d2800e60422040c0604203800c0380d001b205440c0700c0010340d4041c082081c9a0b000e4408140d50440d004003100d0b0f07a603000300e003140c5050004c8039618000545005090303104c10040d100038159103940665030ba1101c2d000c0140c1000408802201d0b040305000710125400064240010089424000e540005450191242d0401070b075a01350340060030781c0200c42d01e035001c81c1c00c0f4803030310300c49078 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 719636816 1250 719635566 719635571
    0x9100801090c051e300a03030509062202040c050c0105040b07090e15040c05130b090f09090a02060307020f0f03090108101a0a09080d1205010605041202120c030a0510 73
    0x144000b90003205900c02000001d0030708403480a40c030b41741681001c5185c0d185921400c03983e0350102e68080501a1000003406075031b02040506000a9940c100640078110040f00c40754040314a44252240c40950754160301120002140d5407941c50940e03080c4140200c0e030b0001e5203050304000030805810081401814150703a2040c116844410f208541c010540f100d00010124940d00e4255141c0340e040f8030721460261a10130704110000080b98034081050f049842e0300c0402252100842c280440b000041a108842ca910301e030914540746525081c0c084400b90141c9000000103c0460080004084220207142110301c29400c0c5aa1180c90340c21008a4500064504010030104002410081705031040701d100340d40c940c1e511400144071644044012010b0140c803a8000030304880500508101c0e10103074943c1501140c030010711504540c0d05030083c0c420301c90305104c148502c1e641d02032581c240ad40d058802c1881025141ca030b0303a1400c501d10341805d9251044000c4903042280115039582074141c0500305 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 719638066 1250 719636816 719636839
    0xf0b0603043c0f0203070302120102042c04030e060c0d02011a030105100e0421020f0c030f030406110703060e1b010e0d080a09150509090a14040209100801090c05 71
    0x1060092540d2203100c5940d603550481d00002c00c50740d03020803c0c0144010102d484150b40c0764040381c4091443c5400f00e11507540420100300e00030a103407035815180e40d42005000d030464000c0c5641361010000c0c10107400c01c01d082c8500d0a20380c6948080f21440803001c81203400210151138000c0c06000c003075030038250710920704a411890b401c05000b66800341e10499008400d2900300042d40400c850001c3c0190307880c3e08014016042100c201807150420031030b075806800d201c2d940c05c8100d0324004103942414000d51107101c402c1c58002c0d02000303131829109680780040e000038641c14a241f038281e0b00d82026240520f0030607001041540094810700b00c4c014001c03101700c1e407010303c070042d14ac001503200284c0d048404401c2803000a882c050062101c1603540c1020b52401e030310354440c03c04942c9080307070800100d030000420301410f1a0145110f54070042002060210070b47c0090192112180607200030301400000b13010803031810460b000c500117080d002000b004007208904140444188500c2041d000d240101c44 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 719639316 1250 719638066 719638133
    0x30a0b101d040917041d0121030c0227090609060a1104080609160801020c370c0609080f030a030209061606020414010201020a0e010f0306050d05010f0b0a0312030f0b060304 76
    0x15047e04070b50728124000700c40307a0031010f400142200014102d0800c43c003040a503006a507401001640b4102c0c080c080f0740711b11640740b224030290f81c0152902190f944a801002040c0d6000219280d10042c0590b001c50541f01c0c00002410034040c5401005003401540100881100d002613080e41040203860420445681c4406880c00c0744501510402c142e0040600b4200b2494070bc038120001c2d0070b401000030880300d45001c0e540c11741c0030918011100c100300018200709aa0b400305040010f041c140000d030160840d0425003d03543e200b162041d009260300403407203a000ba0755450544603002c0c400d0852070700d0a4400c1c0381541c0254014001d203903040c3d01c0410011650351051003070b00d101c0c54103919500d4166110070019107103040d0180e9503500700341d15a8004074541d200c110080c0d10261203540041442d036081180c203415070b803040e02c9480c002c2c0d103818020000b04031024640364400001d4100040c3c13032254026290701074064070314001e400072800020300041210716024207031506183d00d2941c1c81c8882d403a1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 719640566 1250 719639316 719639369
    0x303032410020c06031302180106110d0801050f0d12020f1c0e0d021309051f050601080c1e030112050106080c130b03071a030a0b101d04091704 63
    0x80072001030740003121020b6a81081001540c100004005c10760001050b0782c0024000d030009840b0340c000542010042207101d8014402e811468410760107031111410403600180200014810a44600681105503441d916a03089503845282c010380c07070018042c0302582c060f50300d003000701c1d032400148142005214080c0424820341041c030300e03542d1440c071a401600300f000114242204141d902012001032086d42c0ea50703510034048881e22601c060001085a07001d10101400d00004042100e0300f403200700300090b80d01032050390307004058659054580856a000080c05c00d03009240314030300080000003241da80682c40e100c0d2000ca21581c000c3c00140e8580060781e0b100d4000c821050b400c02a100c00f1401501171a8220900070350014045509a0740d84444030420040000c041300e2100d8000000c0c86121106405805503005064564000b144003e0500030410b8a1106140702203181c5042c0f00c00e0315940703942041f41190341112281d141c00d4020300c1901d0312640244220007802000d251b05144194090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 719641816 1250 719640566 719640589
    0x40317070504150c0203011506030b09060303031b0307020a05120405092a0a120c0309150603031209020316030b3306030c04031406040c05010309050715020304030203030324 76
    0x35980f82284414007a202003408550885e8103540b1008035070310264200801e078000b40200d42d40400c404484200744005a0000341c9518040d801c104200712880d10148144292410012000d43c0d881da24541c007241420000d0320014158040c900c02d5480b0140d18034054020b03900b00700c684914545642c588191006446c0e030050507a0082031107c00340805c00c05001c0c208004d1142040802c0c1d080181c00d038401c6502c0b00c0b9124010a940780f01100078000c0c0b004224083c038413040d90802c00e003410f6448c0036090382c018529007000c8a4841c20101c00715107041c0000382c03c021a03d152010020748034500b003000000101c4042c200c1100100c4d51400c9160400c6814a00000903106c1c0c001c0300d05540b0521207664401049021541408c0000000148900d40b840303065080b1100508000e0800d480e10f400303400031a501c000d040608155104000c10800304002080350410140b17444052001042a81076010700e610280d41030201000304001502d0040100502c3d1000e110310004e06104501000502c1c0e02c0e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 719643066 1250 719641816 719641829
    0x140c0103230105060901020106091d012004030209040c090516021603020d081e0304121e1b142d060c0d020a030612030f0215010b160614040317070504 66
    0x4881c01001941403920041c00c0d01601880041002515031410f40705948125481403c0d80d541800200f0a841081c803401400500e6001c050814202070311041d07213076010303d01010740710303411002c0807070304001c5005c2503070005110b540400c1c44140381013003a030720035402254020b0015000b14400b40002c3d1300060009815250300400030403544525840b21950346d00b00d2a0095401c4403800c50503450151110007462041d8414070f40402c0444081700c000304440d04461403400055484500c3c01c403610340007488102c07030440180b030180402c1c13441e04042c0810864036000203181d01034050b980c1d80304140c4000d23040040340b0f1003d107002035001c03480100c0d5603500b00710b4400c0f40c808d0040c400061600e0f8150000c0030b81c04020b20707010031203070b03180c40c41c5440030710f4003138000c80c041210014007620494052003c0c42d8920151a20392009615120420f03015226244440c410008170588403020001c0700e91203111000040080005103103401d02d00a080040980040d10248081e080000c103a2440b070000c8405940e503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 719644316 1250 719643066 719643131
    0x7020a14010e010518070f0e0105010e0a0e0c0409060b040614070512031305010b0d08040b0f0403080f0a1d030d0f12090b011a0405061e07140c0103 65
    0x94545030020580000580100107540380da0020520460900907a030003411a40201c051064040c85100c4c640900c40d403140d02801158102008043d0013242c0301ca0456a080c201411003c01d03500c0001d000340710329004230700140061030902964a8020001c0d005641450008200303003600c030148509030380103902c1810300048031110000300300b40a520140004034402d0044a441e60380d00c290000300794004070741e000161142c1191171800c1c45024051200e0405040e00c440200380a20b446000c01482640203440c0c3c81c2c44000740024040c8401400c80d0015078210441a0711400c404103285100e03400440301000007450027007620a041c460903c0d80f400c1000060007800340d90505401561039000900118040c00040701981503400440e0040c3c03000c191090f40f1040303544d070400031254640c86c0c0034200b0920b8071200f03120512940d210201101c0300780980421054061b03444c020301c03081e20321920000070018400c01c0718038260b0000016403c03120031801d072014801c02e0300071500304400c180e0510039600d182d90b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 719645566 1250 719644316 719644333
    0xb06030c090607170a03021305010c05070603020a020f10060f1a09090a1d0d09080304030b010b09030a02031e0607140912010f140f070504080303010b03060d1e0b06090702 75
    0x20b02000203207109846400e000341e180310303003181d0a103140e00840e0700b40c030119400055000320070088aa20358054542424514aa840c2c161180b0f0341e104083e00516041c0350303000440c40010750017000103e55181c18802216280b10306001c0d600081c1005104007020101000808640d10211181d50b044000c102c64419007400040341c108460000082d181e0b940d0b6035510800d003100040c3d41d40289000c420f0450081c1000102e42e403005045c03a180d80d0282c040b070780090000f0300000310044c1042e4115100d800402e5210200d500c00030f0300b083e40000c0000d40c5840361001c00340c4804406043d03084002500406e50b001d5a54801054401880b0303c1e103120b441c0311040020170703004d10300710040c07002403090311000140e100010400c0300b045440b40d1441b00a05171814041100703290041841c03507800b01240c80e00398103040c03504031956500c1c0810b0160400500000c4005020794071108000072103030750004640035420010140e4000003207a01c10054450348000400244a030524503051400b03401154000e00340070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 719646816 1250 719645566 719645569
    0x503090a030315090f02030f01090c0c2a0f03060f0b0a090e010920030c04110403030804050c0a090e0616080714090306010906060f0e0306041401020d110d0b06030c09 73
    0x3c05810106049103a01ca02000c42c00841314402c1059484240c00d0050b628108103d002c00c1e1098143d0282c80118100030100504590202511981030b910150b805c1c415100c075512510b4400030f44107100b00700d9801110014685007007800c8a02241c0c0507035005c106e84c02800d25294140e030580f00066801140102c410031203540240e02c82c10145581500010340705e00c856640c100e64068a09422b03d0b0841113007040d105a20303041c000c070030381d0600465007045203400a8015049900807844003500740000d00000805100e000d04c41854002d0b40144200035854031504d004004040c9c401c4445013601c1500d00040c254103c4140303940408940c0d89503104a1340e509002294528001d1850035250381c41804550b000d52000c1180074040c0420000210380682021402000c0b641422800e0040011552807602141c9020503c00d41058100e00710100e840c8501003078602920a801900c81000e2030005003800078084800509148010800107000529a02041245602090300c1d4002c4081e0b0070007500b0b0f5035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 719648066 1250 719646816 719646821
    0x120215010312110f0102040617060a030b130b04080409061e0b0901051e09040c17060f1503150a05010918051003020a0602060a060506040b0901120e010606020a0507060503090a0303 79
    0x60460503c2d00110001205180300c1c00c04188074070410701a90003140902200360801d415100058441c0d154507a10300c0c040c00042e014003c2ea110243c5503000304e801141318129100000641c1d107410000e9008682081d01c1d1210070350313120344204410903181950100c2e520310700c5110020548404001d41c4005414691002003691114900e01d061003020004851052101c4042d5520f0704c016034402078481d04604117001c141e850300c0d2142420442c1c001c2444078075603c2116040e8120b0010399840d505a03a5420204070150500c0000c026030740c03008001c10106120103004011401c41c180d4284401d070760f0750130040d00d0000701c0740034103040c0c0c2002c10100b09442d00c165011652200c150001c0c0810709075a500810701c00c205907006400180c01c003404000d0070502130b010300c0340144000e0343c0451400745400f590514070300034060030904201b03c2246070b10940089070801340300c240005008000c099525000a95075003c044011186e5014140c8002906409107007528415000c000c0900512411039404400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 719649316 1250 719648066 719648093
    0x10b1c03080a0618051006020c0102100b030705040204080d0f0513140f060715051b0405040203061201020c01060302010e030105010f0308030c190923010203090f0a03060c03091202150103 82
    0x4103980f5071000840004240c0810a10300c44520005010b00b024841c11501020a8022006641c031111a280040c0d81c00500c84140040d41c200002d110740003000005d0a11140c1d5002c0303680a8000325000c21341c01d40105201c48101c015440d0751144404015040e00c6074041e032202c4d180c111404e52130030002e241080f1440301201320b0040543d0301020140707001071030350b8101a83c1a40c1940001c9016a1030741d41c1845501d40081042074003503920802008000c0d510311441c00b40070b006a40201c0450441e0319070305102113284490b00029505c580340c140010380240001d10007a800150b4500c80c03604c0030306040c07007004e050701d18040d2807030005421078642601640c0040c07c1524050010400652502c2002d01841e401096596401c03410510300804100001a00004030304d0619480304600e0b0b03580c3e0000300322500c400040d100803018003074080024054010643c0041c14003420100381102c81507040e4415200b89200d00e81c00c03d030885070703031000701d90380e554074035203d09402806001400403e2000c2403030392 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 719650566 1250 719649316 719649331
    0x12030905030105090303011e15110109020d0501020a0f08060f0103200a020a0c080f0d110705040203130303060f0308090d2f01140f07080a021518010b1c0308 69
    0x295996442000ca400c40c0c0e0b044610100c6504084010310210718a00101c0c000c000540054101d524244058801c4011000361407006114840f0072085598030700390004050160001c1500310040c1990074290701030741c05a1030001c005511340c20003d200c0b50040d80c0550150300060034905844042c080154010001c41c1074068881e00320b0200340c0f05c070258078001400781c218564043c082010141c0f500610344013a94000c441241c00c61940340d01c2102c8000b0f4050546005880c1801140d80119a00c500f40000340e0070107034000d800007080102d61000d4800850825209039000c1024603660707100408800503e0000910b4802c040201c4142868821400c48400303000c3d440a10480b00903401c2403101e21601100742001d00b43d00301c010361840d13070400c603103680301809080c20b0b40c545840003001103194418802c008041d88004641d01164610030000f4022002c0c5000030f04005051240c54000c0c1c1c01d6075a201c1005070340c00c129900000e410003841371500b100d01d5407035008a8072004e40e02603829450003003035070303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 719651816 1250 719650566 719650577
    0x4030f08090a1a07030801060302120402040525110606030c011b0804051c05010b011812080c1501091a0f0d05010b090c090306010504090503030c0a0306050a090c02010f1103011203 79
    0x4140d410080c0c2c1c0310308035241c400403080e84d151400e18010344070281c142d00c2501858410310907040d03646200020a0f600a0341120000b9042d0b9070480c3c480b855926080840c01181c03020390300b41040580044200725640c0029040b03030b40716580d290405a4640410100a00007030407040d1264949206240701c0c0811403140d010f081c1020f85400104981d12809032000c2c80020101d00340c1d1091040a104a08034200c3c28644052000034511aa00300d44246225440f051000c00c40018207000203042030782d400c007500005030f80c40d651070400b40070110035080c051004010724115451a46110300c55245900c200041c05203d04a0807070310402c07100c1d009854050300c1a54890a07006e0710755a9030a0b459100b0303c9242040d41e2075401d918189454850160021400f03980360070a2007001c52000800d0340e602c150602004d9130f6611550303804401420f80351344100d0f000010310f400451440040d41080c4040007803a4000c01ca50440303500640d0036940e020b1040b45101004100500070031100a48240350503000b824036 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 719653066 1250 719651816 719651819
    0x31a0108033709180e0618030d0c0e03060c0703021506060d0608101112040209041506060233061306030c0905041b06020c01081005030a03021005060604030f08090a 72
    0x458216050001e19000040034072105020a800046584c3d070070484020081280010a40604d5540d13400948a0080300b60703085041c00103803508208440840d0b03400d1105215a064112340605010b51455480744203000c1c13500082c1d0300c101101d081e01e482f15099802007142c000350040e0810600320180080d50015420090000c541229005120007820003900030180849446140740c01c6900940c00e801300c02d001001440000c4803460310309a0082d4048844050311303191454404100010301c81034914103800c0000000e0b4927a00442d81158160300c0d203901101c51000162000b000c00b000603848002c2145007004520306047c03003c1d20070501d0035030800004285880c1d449107425003c00d58004642d20b0380301d800b00310401800d0001000c020b010052210701490034444080d4480c1c1030f0018690420801d9800200007002101d04240200400b400341c1e036140d0100d05000b034403081c0000d101c403612828040815401e041c910f0440d000c40317420132801c034211007203950b9224159010741000f6502c030845050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 719654316 1250 719653066 719653147
    0x6080a02030613051b211c0e090a02030705040e1e0a0c27080f1006080309131a091f0e0601051b0c030316120201021201030b190510031a010803 63
    0xb08001b420001e9008040d00c034007002c24400d001c40050880c00c2000721941c155107180e00c5500c40141c021103c80e0004d40c60342da80080403030382030085a101c0040041c1c4001800b40060242008201180211028107096030f25601100305a58607556044005071008060080511100503c1d25180300300805409400da500e000462a10840301d42c85d80464000b08000f489004181c459100100070880c061411b0100340d10000380004509a440d00e80c0640302d0501c03000172800d8201114213003400401840e001d041031410100201c0e0407002d0401c024040d0003010a180c0e0501800c0c1303205282c142d484d1440c244041400e0341140e1001c002c030384081c1c07141c0b401e030780308540d820320103040080a20781ca0341c20130385031500f001042c0c007400014003815a4410442c042603100c048601c0c9054a03088203002080b5128101c1c00202138a50010450b40146800706000e5000b900c1411031003280e000301d410140c1c1c51002d60107003240850071700c80d00440340e1081003075048094121040d41412801c001c40c031488000c600380c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 719655566 1250 719654316 719654359
    0xa0e030d0207080606090403021207080f0a0c060b0f10031d0607050705070e0106080a02091f0e2119030c05060f0f010e060f010810050406080a02030613051b 69
    0x2110040560410b00d010700c80800204149984031070b0884007041a41403030b80f006500c1c2e0300c0d41440740548940c00034000044c0700c83c2c071003140c01c1c068200e01c1e00e85e40c4409101e0010305a10b00b2820880702c00c0d04243da072500030715000c5803c4100e0dc0e4010030b417480d01042c808064008002070103404c03042e1a00f807981c42494580a000030752280da03881d00c0340341d51340300d15140260401030141c214001480c0c003c8010302150398000080ca03444112080016610640700c1e0004145904001c1c0d80c810320034468484c0c2001d241c0c400000c48075030b4800d482c400c1107008101d5544101200710001d22696078045801e9201210f001d012028005000703042c07140c02119692985818000300f00c5110b804002580c05101c220b240e03c80d505d85c01884207900b00440c03418054009540000c1021071207041101e03810204002c0c02164100780020b0000410400040390344e08030f0140c40310b1000e0000e9100340100380000300b0f212501c0260700308455022010b071003191200c054501d9412801c203000c80d08141c65001181502c180c42 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 719656816 1250 719655566 719655583
    0x70509010903061d25140109080318130c020a0f02041e02030702160501050904050a0b04090f1406070903120c0602070308060301110a050f090607060c0804111c0204020a0e03 76
    0x81e901c8100c01c078181440c4d032500c0704180c0a0007050060840325101d032180c001c0080e003610341c0c03035038030007445100d8000403111501c403030300500d1803400006140011005c0200013140c0c14402581e20b54a0840c2d50a01503040710303090746990700542c111002c800006800006440b98441c801000000c04241d2001c01c018403c518865941d031855000091080042d01000100c82c1000e0740042d0542c81ca0608000802501071441c2c0203025580714004205140700c41d0300000b0702c0c598040c1081102d4107081c00c00c00c15404014400f80c0e903030000300b50711940c000c170b01048240c4540701d5a142c5c612258610350380c0c1c80140c200c4c004240100520b4132030610010300c40e0300003071012074020760b213000c10307030400104050844544800240c0040001c0015440c1d00303402000351213540c8030342e41c420350f101c403408404104248a0424010303c0d40e80707080c0e4805c0d41c281d00710345064082c5010302c200f2500d0142c41c10a200d810f42e0042d41c296200980461204c0c0103150036002031460752090b00e0320100b42c03d0001e002c43d28103644d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 719658066 1250 719656816 719656841
    0x50103080a1205010b040905100512030a030e0616260708152b060905070f030b01090203010b040302060702043b190b090a14010b100309050607050901090306 69
    0x1d0520061a480301c04034403160240030080009501d0720728084110711440c0703d800d640e5510b0f800085e074008000032a0300300030310024094281d4464803080f50381e280d902c20018040860315102444000450001d10203106035400d540c1744003040e43d0014150b40b0507109100b074004030340300c4001801044041c140650b000c0c45050f12140716904180b200c01c0300078918aa6003900070200c1161055803920b4540c0c51460400d84004001d2180806050034009041130072405030070341c880d02800003050500c4034068030440c2d000d450040010303607d601e1010180d100070321410045850500c01840546030403001003c44074401030000520914400c11003014012860820868200041850311009200001c4241800e052005000100404062040403844c0e0b0240a80005841000107403200010092400c1403a0050a00180c0e10003440895028003000b080700750240c0d074000030707421a66019000d80000d06602c80d001d000d89a8031180d044072507400507592241041450395000010417801d10603034a08028 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 719659316 1250 719658066 719658083
    0x912031603030c0302120f1305120a080912030703110405040911030105010b070305071b0b0f0c190203031b011503050303090d0507022409210724120f050103 69
    0x190074007030110350031060342ea414180100804005420302000d110390103086c00c100401f0b20340715007005201000100d40000c00c2403081405510603040d07102c0243c0200d01c455590329020340d4500c900d8607110707180446641204c600c24004102c0c140d010b41c100d03100812101c41c845050940d5003000400740c420149003901c85002c103038143c4c0410308080c045c0c18090000a00118588099680c0c001c010b48940302028241321520020307000c0442002d0503010040c64840348458807580b0203081c0c176245038044a101341d081e02c60028032107808041c11042282141c4c004000d1418013610034601d500005000b01e441c81a95619201c1e44140745d0705694240255001d00019922440e00d603056034503101c0c0c01006641480b20a00200f401070340c480000c4d40c0217000c0054a01103042c503150703804115006112032140c1c0900c041d0303000283d9004040414003d0a80c003c07c1f55400c5a4500d0f8441c0c444400d0f403602600c12000313002400072607009640d0f118411914210015140300b25804050440c1c1c400c1e0011105541b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 719660566 1250 719659316 719659357
    0x605040b0a0c0503010f030213020d0603030504090c0f12050a0921110c062b09060207052a240c0d0807050a36030302251208091203 58
    0x420b8410290060b04a00f4014915418402ca001502c10035103c002c2c402c00090240c24600c020540641e0498010004c003840034036180c0c13801170100d810030300401580324900138160391b040b8801c11125661a0240d250310310a005001030381c10140200414484017291111494030000d91402116003407100aa02c840780d0307040d428070005141d05d8151804000aa11000c2e10b91296510002220b03455503060002002040030045e4220030030b90300221403800f10746011111420300085400809c05284a03005441501000303500e440c0300e02070013011a10124402c800b2070411030a005c0c0c0711030303d107120700040301000803e64001d0740c2031513010240c15944c2c0c0c0c2003a0801c1c164942c0091a61f608480b03d41016070504185a200414240001c04c01a175009018128405451081304e0141d00a09110344080401c80d00c174103000e17540703180f1307001030290080811580c84c110b8610941c412064994502150301c110456440d014240d8201c1c403a4260300c0707054103842e07001c852000c1005005640c03d040d60070309000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 719661816 1250 719660566 719660581
    0x30901020f07050a050121050109090b16080c1e1902071d0705031305030c0c0f01090b1801050f160b01050922060e01020d060f080c01170703090605040b 67
    0xc0700250028099510154003484030b990390304612401d481c001e10700f4006841c0c010003081c01070368030104003c0c0c1017441c150002ca99030700c858010001c0103000b01e041884d240c0b40d5000c01c40e4000b4400c0c03d40c0d0000380298022880840d000ca008064503480c0c401a50b40c0280c041e031001c2419400f0308616084c00a03640511140c203a010b114210007001442c0c1044204800204035001e000e41c018100410480300100140c000e00c444201d051603d900a41207030b80341d501030020983d4030341c0515100e0307100e039204248116503503100e03409250944030000421418162a40e00500460550304191070610805001958020503100050b1600c00c01e900846465045241000c610350380c0c06800c0b6a010342c11341c10411200f008800b14200041c2d00500040200d5411030402c80014094400000c546e0b50000a1040ca000c1d01504803505503014070f1384400d41d50340d81e1030300c0c01c1e030b101107262a407408180164010b04021200e03442c0198414141c0c00e010a07404003da07500d17000c80f1822139045030385441100601800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 719663066 1250 719661816 719661823
    0x40603060807080127032105040c05040c02030a050304020f0910061d0d0b06130509160816050105030703180f05101401140102100212090d030c05090112180503090102 73
    0x502d03503840204000e4640d400745d02079000303c0400d610b40014043c00741c407041611803025404840a20030030841e422503a41d550700e020b403c007a6002d488417a078840e40440c9502d450b215840c0b400c0c00d290015031402c52001c0341503a0580000f40b0a0b40d0041c00d140f030701401030311030021291007255101c2c00c003032a5608108016021020300c04c03680e0902000070803c0c15094440d0840d040c00980c02c0020101c00d82d40d07650003e0140041101003c9a1504040611600d0348000820154030801c000850103141e03202e454283d03640040300c50964a500e82180c080225501a000560708544a45404a0507a001011a50075203c005070215a25407000d020765040c00424015425044514102070000c0c4a400c1260355440e201802004c80708580c4080b4500b0030780c0204079180c1304060021042d900c400400c403e0a40b4035604039011071081c0904544540032910902c500c110584440c1c40d000d0801c5c26120044a5100d21a134070042c41aa1f074007030300e07030f84174020100d8180c54610890045941e40f0040000905 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 719664316 1250 719663066 719663069
    0x30d050903300604090501020d0911010e0f060d1515050a030b01210b191202010906050a05250501020d0b120f0703060c0201140c0d1401050907111002040603060807 72
    0x42d4540403910109424882002c80354015808480129160302c450800a009106a1800e40d41e068504a00041003040f03504010000301400d0301c0746003680d045001446003442030400941c0d031050b001c0015540c4404142d0002e5108102110306802c441d8071983c51803110360758515642d01040300480e5042000380d2500569524030300a2800011900c100082c0c04134207003418200302e59241c0c0f030b01c02041c0700d5102d420a807044030f408046140e544941e03c1c8100484441404001e9000442c25040421135a0158048a031030388025910203182c24004601034620140a000e00400742c00c5ea241c500c40440e5007400540a58a0760500c0010b45440310703030030041c45116020310001c043e0051361075610400d0021540500312a0080c6000c641a114448101d0040090411f40081071034001e05010050300b40e00e0140c0745401429800300070040c250300c030100050100b44070f09980450104001149944504c2e110a0303407100702e404941280c441c0b284001d0503608139401c40d030300195582000300404e0104009000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 719665566 1250 719664316 719664367
    0xb03070603020304331a15130e0c07030f0e062a070b0d0b1c0b07032a0f11010c210c0e090c12040f120e130e030d050903 53
    0x1c02c808810040000200780b1030302d42d601c170641e0703850101000c80c03c020748040e00c3d11401000c1c80e1008481e8202d400d956081103406d5502c004005001144001e10441900e0244004124440c01c4c41c010b55401c6510100c08142081007040d519059500c0d6180c01000c2c2180e8200500e07105100c2c0340c4d030f0754100101288a512454546d0140104000c055040c070b080701c0000c6c941400108001c2e0b941c0020415520340450454000d4141000031414403114406071406a2642e1746c1c148800241341b2102d84143d01305011866003c3c2c0d1030b055102d8040d015401400b0900102d00700300c1c400e881d070070716602e0840e140032100300c0206101c03c1150036030102c0e0140c182d5400480c0c0c00b040285e407840c41e40003481140024150303402104042c2c00f14005001c00c1e01519400004804107015505e4540361004680c028000c084810350080c17400185290f0040d50201c2d400c2601600c1c201c040c40f502c80185019020816142c2840e0100700403800e04901c99020b214030a07140d1800a658490310040d40c0e401c48000d251891 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 719666816 1250 719665566 719665613
    0x409021309051f1404110708030103031805130207060f140907050d1a091906020915120a020d0b1207170708030901231803060702010c020c10030b03070603020304 71
    0xd05a255941440f4054a81c840348501e00300c95039002260003000903124441e40e903a0081070402c00c016802d401035040ea031280e40c4815240c803114403000003441150281c50340c404005442c1090191403a4084d24506011b00c5010030000c64001081c0c00b01c40040004044200ea2a010046418070401001d801014151010001000355071504c03003181c500c2445400c480002d69002c030fa004803042244e101c03a1a00090440340144048c03900d08000d510100826019003844000052001219030540b1403100b1030b01da030280705a43d1618000300945c002042400740c80d07914500c00419031640c2d00800e02840c124401040c000e400c006140c018008500a000e2984c2e1080006005485021050b00c400301000c0c00c0c441030440c5c0880c1e0694100c242403c0380003000c00007040d400c42c03050300d4031050400360340c05801b55070381030b1a0010201d081c0c031003100d50400036034060403c0d01072908200d50b9510020409240020301095400c0000782400c1c1e0130307401000004c0d008010b10080c8042c401440400048003043c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 719668066 1250 719666816 719666851
    0x4110d0c03021513031103120309060714040308030402010c140a080405040e01022104020102011d0d030b0415031106280f180611211201080703030509060f040902130905 74
    0x74484813030311a0100802c00407a00c500c510040d1030411004500510841c0e102d5203915003801c0c1142e841900f2a41c840008100301c201c240700d45424030864056030f411540c040c0c40c60341e80382c005440480203c0c80807251090070341a10449000240300f40c2c031506200b252070350342d11480d0904000c03e45010a0036074840303910401c2454110800d140c100100c0700501c2010700480c1d512400141d004005501d400301d440e5584048140148401044100842e07005850402074210b4103414001201c040e801e86c05a0355540780d1050000c2030641c0e0300c941076514010426450320352030045828801c0310350b05004001001c01622454210b802000310b0b500742500e0314221241d201c0b61102584d8a400900c61002841007081444094220600c41d0200364400d40d900546141d050082e41d011340ea01c400030364180b0b400e00c18008281d564010990808482e0140e80340d9040000c581c1c200261540043e417800340ca01c100704400039030741e0054009800560403d014140d07000345000d25020a81d1306c010030140c20074042011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 719669316 1250 719668066 719668087
    0x80411101707181241030c16080607031e09020a09060605040527010506031e01061107090b0a03230109060f18170d0902030627070b1204110d0c030215 66
    0x3c4841800d41c1c0300e040e8002c10ba510f840c1041c03c5104642240d89a405404075074030800c1034047c61001200c10303e20407a0b003a0b552f0711030110101c61005152004001c0039420f40b4003454103641101685078002001c0030f04031a50748021508a60460f84580301107400807a00700150b1804400c070312159980b0703504080c0e90440102d50405140e505005407032082202002207840355041c0d18240210780800b0600c407011b03585910000d484d003100c841c00c910b900c3c4104100440c140d10140201e15407003401806e8016298110394134101d05d908212802c18148807941202d00f80410b09010ba00c0c400d030700401d0001041d034405000e00c020703580f1409081d28646070f5030880c1c800207850f801e66012140c00ca14800da403230300203813440300001d001108006175044c45140c0034041d84000303180b105035101004908103a008601a040c82e03880310003d11072255150001d01070313480d481c11003010455001c1d1040031030303d1020242c0310009981110880781510410a00041841141048000c074501100c680c008103040008180c0e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 719670566 1250 719669316 719669393
    0x5191505030a060905040c09050c130e0a200a020709020909040b04060b03010e15090a05030a030203090724020c030c0d020d1505070804111017071812 66
    0xa660042100000002e601d080310b552168001c2c2c9400300c8288814141070600c0c940304455402032400035071404000c1102170060100312402003454600203400303103140c60329000001c2030086c5510045501c1344c00000401424201c3c492803081003040140d21a41020740003440c04006400020391144100000035955a580140e19481a07200d0b40c4822195580d10300070002c0c10914100380d400d076013072401c5c8507880400400d0b102c80b55080313280414081e80c1c42400b040e60318001c011024220350400c00c440500070f072081d001503502440c841304442e550b41d500c0007100003250030407031006250018480ca41c0951941405565200007088004081d468035000020311400007540000780f00e611000060010031044201d00c0034000030b00c0f4420425413609441c06002c00d03008403400c9544514882c3c401090340fa285030398034441c40d419600c041c500109182201d4040c1405402e034803d05c1000c0450303803c0010448034010141c4400350004a40e101685080c440314813810010455050740340b401442c0111800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 719671816 1250 719670566 719670599
    0xf0e131b080c040c1e180f05010810030c0308220605030106030c0305160309020d020d08030115112a0a0305030c101b0f050f040305060f0f09060106030b010e0405010f0519 75
    0x41c405d8683c0f442402c4000d60b44440e540083c3d45c1900c11113034001501441d000d081100b244e0080c0c8815078070703039901e09020091442901000b0601c14100c001407003c583c80402501c81c000120241b054640340c0e0080e0408851f40c3e552025001403400001400384d02d9040c0105850100141014041c40c20024410340040c0300141040041550b600c040d00309540c0c62004000880740c003d0501048580c0b281020844c0c1d9100340296880c83c07004038103142046202c1d060940b00340315201c0241c5150b079582c50350140088031207614000000c90281c100402d581e41d4015030320046204000075541d440c0b1880342903050416040c010000340d842d01c1905607410321035a035a483c01d0324451800c2c3e40440381800090b5218040c203442054131550100d8040108580003507041e01800c0c1c03124000c110365036610b00b900701200d41113594004940209004100031402500b00798100d200c141880c1c20010514008201111001d03403048080d2a0116006c00c2242428000a15000590b002200c43c09040030502c1c101a0f41d003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 719673066 1250 719671816 719671847
    0x80f0405100c0f02061c0204121202120301140a030206030f190b0d02040c020f03041d0f040f110a051008150303030103020901180603150b040c05040f0e131b080c040c 73
    0x783c01d10b401c080c146c0c8032450000d03451604540700d03500c4000812100c901c0d410112034034041d607142c0c07a1855000054031a40348003002852441d5030b00340842595203204200710320741c1098100d0030100050b0f440398050352082800c060b039981d661510040c0340c202c410741c00c5440240149400044c0d00030340c171105d1800d00d40319010740c1d01242d54000300908a14100030312440c2c50380e80c0030106000c500700c0e202240c0c110000c001d82c114403c0945038084101d96104080d100105044400c80e142400655100000001c0e283c0c02802098401e50740c1d4040b074042061003641400150044080082e02029064072041d10503041d4011400c540c111750100c3c0310b051060041450a07080e5030302011b020407490f00180065548040f914030042c2c24440c90401401d04180e40318800da003001c150700c11300c0d84560300b034500312003c04040303400051519982010021014020b000100e03c0182507002040b00340600a0701b10100e1030b201c80c0303120b2400d5200ea00704100e030003002d80304030f0404152109080d070045110624084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 719674316 1250 719673066 719673079
    0xa180509280e0705011116030b1f140d060b13060e090a1a13020a0b0406081510110307080403050606091602071a0903120a020c060913110403080f0405100c0f02 70
    0x240d06c5c0f06441d2002d14400c42500b1071001d107001c03003044243c100d8980641d11546180103c61035405050140c02c14a000f1241d404031094030880d01c03440c0250200c01001c0c05244009500790b40341001c038280001c1a2400c40e00c40344c6440f030030444004191a81a13000d1707107000203021048055900c03594880c2c01d544404072a10b82d0040400d09540c0d440307020301e1903564003c200740d0361241c0d603082007070306a003041c07003110045414103001500c11040b4403d95804440000c04118480c40c00200aa82201201c545048580301c1405902d002641000007000a1401480248030625010081288082000300809030b00e00001e400365075802e400044000a5072000c4000a00c1c180080041110500954200c2c903414071501c580e0151881020004080c251003990a440c0c0c4081c00e54140403d42c4506500302d5003160320381602030f601014070340c0000060682188410704e0300703950b41c84070352040c5c101d440082145240098100640d16201201031814025410705d80140003107500da105e50040c100c0f0000e40aa43d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 719675566 1250 719674316 719674337
    0x7021f021c110c0304060e090a090b060405070302130306060e072307030e030d0c14030702010c26071104140c0d050402120d020f120f0a180509280e070501 68
    0xe010b20585280c00344035002c40303071204d988040040c0071350b143c405002e0007440940c012a20045d4a400749070705c010b400450b07601241d1540800c1c40003d080051410b401c0603801e1003121881620035030020300940c041c0300082511401d21055500c4078501030301c0d090501008000f405046820148071138904149624400d4980c000b03410141d5042411500300c1d03605014500410441c2500240500102401044100c4c80401c4100441d43d807840340d040040e0102e00300812070b074000703490450350070200c07041202c2c08541c03032030262400442030704204421a040300150709242031905107481a240801c11a4002c1143d0303092000004001e845144ea07240b003800e0b02d8400042c255120300104c1d0744500102d40c00ca400001c4488402906d0f441a190300d4401742c011300482c0201c00080c0025120f011140517880342c82c0c50300c40c00301aa0070300700c034485000a003429104005400d80d04c26152a20401d00309504075030009181c001100007a41140540710b40510303100345a0b244000008860f01560020f003041071030326 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 719676816 1250 719675566 719675591
    0x71119020303090604091a04061a0c0a0c1706070e060a051305131505100f080411030a06061712030c09040b090a1b0c02030a0f02130507021f021c 64
    0x10f120700c00303250341c00c144000307000101e5024540c440f265256040c00601d040301c00708003c2009a80452060b0400c2d0142003101c21803a01c84d0710002c1070b660490034116030180c5030a94804183e0380360b0350b001c011080d040410303030a20b803442802059400740d020324100d40c882150f82c00255985c0070350160300040007804900c1c003160030034490311072015000003031101041480300c50b00300015010340c412100c80300b40300601c000340a0402100039044220305440340103645401910403590000000c1041d0b400c0d241d46403111101d41ca041c08030324400c6018100c0840c405080400e204210140040c040b2401c0d840308409012020215094a41140341070908690b550600400100a84420700c8d8043e448000a01441442c408a40c40103040c004d8210503100000603544059071016407181c40031303400d6007101200d42d0008003408000c0640a100500480c2d1130700c0e03140040d1080f86c03411244440941d2003041c4203000b4800749800c852503003581483c19031521001c07150140301c99040084001c801c544624142c4460b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 719678066 1250 719676816 719676823
    0xf0b0307080718031209050105034f0c0b210a1d060609010509010f062d0201051b040b09040c0509031006060e120a020d05210c060711190203 62
    0x1c002e0f840c40c010283c10b031a810a90b03034102c01c1072010400701d0403100c0c00040d40d50050040d64400c000c146035403880e4a0324000e44e041400302500090550303084007511542c448a00c2120116207034011b04004e0700d440c81900d4004044440f94011041ca0f402c21700804c40521040d484510420305590301d9260341d500c808441d0b402074009001e080400e21040d281e1518a4030f40003643d54420b260840b08040e059a1f1007050064148003030040d0080c90340c2141003445820301030690348540072851010f8038503009904c1d49460021581e601301c080183d444074203200c001c3c00c0040700406100092a2550b2600389090340c140110712851404500403516140c100c600030b0f000e002075581c00c0300050151003400560b0004400202014050b031402304480b12981d00f0541011088038007080000b90040140c0c8000b038003080090044488110786502c103982c00640480381182840303006c0003000c0f420702c0d00c031400f00b110705042c040000c2c9084100211208824101240002c04030b00c00110320050008240141c00403a0a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 719679316 1250 719678066 719678087
    0x2040e2703040e10150917100212040309080339072702070f030e0f061b06090d020c0904050102041a030604150302030606040f0b1c0506010f0b03070807 67
    0x25400041000501c0b10303c3d507400c20348145450001c006910351940d0aa075810142d020b80c0400091495100740050b4002d40a980320f42e803004000c0301e503801f503006a40d02c2a40d01400860510308009014031080641006100c400351692002031820007040f0500c5c2c03040d12500c5d810020a07581c4081c1f000012103280c0341c041505400050941c0d0038142c43e07440030f4605242c494882c2600000e54582d000c2c14658602c00d864180e617012103050380c4481c10f0386003100c942d01180c001940c05400002d072222246e030744030014401c2e40c0329a41c906850010b1003550341d041100092145507a500001580080c1d1030780807a07015042c0d401201d803a40070341c665040050080c004d51308043d40d510150000d43c490307010410051445040102e800b40705415442d0440789102c001c510009401d0b60181c0003240c036600c0e0a401064006005803c001040e46080c1c00154501005007484e404050031119a24240041032007001d0140500c0030450510174a801540d040920009012904000300031012900e520f1240000c80e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 719680566 1250 719679316 719679391
    0x4050a0519020a0c1209080f030304020a0608060f0d061a0609030303070809030f030103030c0c0611120a030f091514041101030903111e0601151409040b030703060b1302040e 76
    0x1c00d540d8528000e0301d1100385000b0304195104004c0182307140d100010850780700c2c941c00790000105920788842580c0c0000042d017203a5020180c00520f028a4a40041000c060b5010f15008038402e191916101c1c400e2078032440030781c010b4400f0804140c0a8500008403070304080c40c5c2c64039003503590344d4814003801d50041200c08113180400000000c14140e101780c0c5080464003601300000b05d030f940c07903605440050041106800a400094005050030071002c040d205042090801194200c0e807925841c04658011204a41c106505404a0104400c1c0c0c414201e40c03010303000d10b820003410140c48410701500040c103694105074803040098205846803040c09144100c1c1d41c00c55400b03a140500c8111070b6140751100d5000b91180350700014002c05200c141401689140d1219280d54880d2104c800380c036030011010310b40142c1c4541d02d402280c0c40c10065200103501032070340010828a010100701d07003a9100d80072840c40034010300091200c80003444003103421290080719070038000078640e60b54280c180e4504424 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 719681816 1250 719680566 719680583
    0x90607020a2c0109050f0a0e0f03040905010e0108030c0a0f030e0d030c15060f060c0819050a020f060103030e04051512010c030b0901030b0115181404050a0519020a0c 73
    0x4819520030703801080c080445100c01010b8907a2192620400c44900729020f5010922000204820b0f10b01903010380740d42c145040694509100920000c0d00c3c42d40036500006030f1a5650004020f080b400c4482030b4090207680c8051454805449885655003021000c0035040400340728619040501070010341219400c050070200da4a100c81c1000f40480d00f8496050b12207801c01e0712803124184c1180b25a0041c0e920484050341041e09201045855910a540440c0c000c54108908034031070a81d456010008211555030541d540301111000f41445d0382c9040301803039075110074010b00000360046403c0c42c80020a460000c1d5079a50440d260740d00701c07601c0c0141504665000e40c4550044410b40010521103801d403428031210240c0700601c00e141c5024800074002e00854801404001040c003a00700840f6801d1405a000c11403004c0c1964405c07200394050400f40c050300d80c0444907401d00b4069a64440c2c00000200507078030742601d42d01c40402000e110700c2e22680e4000780b02ea944038041c045d90540c003074010303018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 719683066 1250 719681816 719681849
    0x40305180a15030b040e1c1403100303020d1d06070f0212070906080a08030406020f0c060f06130b01021b060715021206101209030e06070c14030c0303090607020a 71
    0x207258103440c0d202c00380006810420b0301544c40c20b150003814295a81c03c0001c010010541a86105500b0785600a004000aa1030404c500b072040d0809140111081000c01e16141c0c41d40c54040c1c0b0f0082400060f00074440c540d49a0314039900c4d43d010181e010740e416912140d0320481480c052088031402030000354040c0c101e40c41040440e0340042c1c883c082d43d09425040120a841c3d0040c2d559840b07003404000d11000c070410019002138440d40103020141c0c0400000c0c0d00f401441203020f400c001080710880a4400301c0810030a0a181c414008000440300ba00c0801842401400007900e900e0408440d000701c400c8902c0d021000d0b2240800c5850054229000d80195010702c9110300c069030012090750a03040404020804901d0840724140c4e00d400b031f80d11041031b103641c900340d450040e0408000036000d012400341d5003903640d00d078000181546446407110340c4641d030030b0171300000340d641c01184440e019500c03215042d070044e280041102c01603a02107440d151140902d00c000703898030026030007010380d40c0700182c1c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 719684316 1250 719683066 719683079
    0x11030a030305090106050d150c090f06020307020312030720120f0301150315032406030809092202041a0301060602071a0a090915052206080d08040305180a 68
    0xb14050b030100c100a010365940d039810414103190520b03028140d110841c54130810220168401d405442590510f106582d584160a2070071003525480840541c1002a0400c11450305001c0684a100b0000c60641181000351004108070400b0524981c02c41c10030741d803810009410040108040a41101295101d80f035410344412900207114000801c5600014504024040d010b0702d401c4400c01e00514040604e1921a5000c810703003001c040d8001c60301380061180f51003a500420018502400006950f600300000340846250003d081a07a424692030101d441403403113940780a103c0f03404880c007060081c894034980c2d05034100d92451680c035605e02040041d0341900441c0710412100d6448841c180009042080d5486100360485c12002441941051103081c00c190320a181d4105008840401503881d030012680c001c0c10619156203240103c403180d644042107010700d02c0506803c001400c24241010400360040101800c024117001e00400c1218151300d40303605145401c48010072040e0b0440d41c911 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 719685566 1250 719684316 719684321
    0xb07030902270a0501080c010c030c120c02120705091302060408070e0402100f0f1407060c030209030c0607050307020d1a01090f0605121507031d010f0506220911030a0303 75
    0x20540c0b100c0440040019030400903a10030681203481260160180015580045401c201440300c00c500344004681000003007407813900c0c82b190090503510360a0000c0203034010042c1c0c0c00340050441a80341e03c00c1e881440f9036203c0154842d0004040700b440641400307180700040d502d00613500309580900c95075030005059080c070307040701e0b010728003d480640952101c103400311640c5202c0c4410001250307200c9880d04050b0f02c01d11100c660429248889803c16a03155510800e4818144001e000070fa004100803103c4c0c5170910401407980004c480d22460580c1c00c0d5500754580c040c010000e4070440410300b0031014000c514695002c00a4850010040340da10f6010740350003821410000c050b01403134a480820141003140c140d2100a11407002440640d8a4003d10b401d8681c0c000d11040416403240703d0384105807101d208400700301107050300118541e203040b108a400c541001b002d06125503a01740d240c034000800d11964074180d0303c628502041c21285401c10180d0820421080f036014450201048145585507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 719686816 1250 719685566 719685619
    0x3021b06090c040c0c0f1101030615230405010813060204260d14121510020307050d020a0f060e031b21030105011202090411042714040b07030902 64
    0x48908002c0134249800c1104d014810000044c03c07010418900d2000c50345089045428003014500864001e4641508231011a02052464040f66140e9040410410b420004100e4048624105402c203460000000c040d0030001d003110440d02c0409000c503040c081541c0498000c1c0c2100710881240d280140c000c000d40302215518565a409401c82481d103662140e80104855001203c030715061102810040000000245c0465500343c1600c2089240391034011110744054403e4019603159211424120306111341da202003411074010005180015508680e404041074210070009407210004149038030303521842080c03100b030150056100000000000350307500110a803032454800e08001c3c000d40b045502003805500c1c0850f0140c1c0e40302e2251401603010b0304203030400802c003107081e110048101642d94003e4006640c42c0d00e1003081001202165080950b034171140744401c11141c5149042d000c0b036507601400c0204840c014001240003244260811403003d900200701e140c080300b40071662885807010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 719688066 1250 719686816 719686819
    0x2090c031005030613060c031b2106060507080a023c0706080a020c1204030c0f0f063609060510030504020d030f09090c030f060b090a0603021b06090c 66
    0xe801c00720b0282404101140581141c001c2c245070341d15281d6501300a030940035002401c2503501c004000c0f00d83c00d20402011000c4031901d030a50304464810011848004009a5400072420f0403010014940e00c482110305841d004100203464003000d44049040c9100d05100a0403100110300d55001c0200d10295180003481018030708002c40300280a998581c2800c3c0700c1d030804616501c001410a6070150000e000c401c110310140c0340d0607014104d418100e500301c0d4105407405003400b401440140d4095826001600f007450501038602d14001c00104819595a80e0b620a901100428210030707036040007007030568011030000156030351101d14601c010100b5110740381c0710320f2070741c02ca8222007406803007a03d0080e41c0181c07442c0700540c03007a141501e9500c41d2840d05401c0150b118000145c101307441c401c203071600b44103030b0700410f0b106c51402a21098960303a42102d200716404010b28400c0b81e0707580b403c09084070018140583c0314221079903004005030780440c04160f40d016a00c10841204004205a800c0250 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 719689316 1250 719688066 719688091
    0x141201060918090f1e1e0303050714090d03031b030c1e08041b030f050a020a1505071709040216060f060803070b04020303160b07020d020622060902090c03 68
    0x580003070303010507a40441c0010f03080004d031400c020041480341042d84041c0000b100140d01c1d85c01c0359514524072144864002c1769006003002c000c0101503141c010746801000c1803401c07000700c0c0326000081300c29125030039805110b8030701841d030081014026000310910904040e070f0700a00141702c09019014200740901d21002800030356001e050010945a03128541d501e40d9500b00e400e5a555071010711610107a55010302070740440c4000000500d05004007248503200300c014151401e41c40c030500020701880c1e0001e0300c2c0440c148200d4220103034002d050710000d0383c00c26511405a03a0300c1c80c8070350a911400301c0c0d5903003003400040c0b003034074030404110101d556070b01ca10300401c40900c500d400002107640c58042c507141c9030020020000841c644c0f840d02c91b003150004081d20b04e00081d00035450305a03044d00c20100d13095100d1004029569805103c5001604241d0015001724508484010302045510320602207518145454100f030109a030701c01082950301410031901800c01c128610129001100e02070482078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 719690566 1250 719689316 719689349
    0x61401081c050a09090209030705150d0c03200313210206090610050d0309050d0b04150b0901120503090a0308090a09020a080a0903030b04050c04060f02031201061412010609 76
    0xd02c10401c8411510741a9a000401810202000c000c1e500a2400e0307907152160303800210b840d86c0d0344400c07440013504100d0345030766540c03d4241d0b800c141c520030050641814070b0071800410041c00700c100c01c9041d15600e59203070f60720354500e41c01c41d0202600060140c1010504031604030300c1d0200071001010700d413413a0211403041d80c0d5055a141c0e40e0000300c0307040c00012070b040e0040003d8100f90002c02d05003482410306400942d21400800c208203202c4c103003580c040080307100f40810b0200101901c0364000d18840144142290400410082c032010310480c0740102d00e544039036041c08800e00a580103031500806282c1d42690307905001c82182c000c144c02c0b9200d24000100050030310024800c440f1600030645900c51070b82e6a0710740110060203114070a605043d2600715041841e6107a2103030501c00e41d083d6031250740320380c24090000d1021f0310b071858035402e40d48200030380c809103985900018112400b601c1d043c0c14940603020075100f2030251100c0d4001040d05500041820360b04107104500f0759500000050510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 719691816 1250 719690566 719690623
    0xa050c0406050a0311150c01020c030702040b030a0f0b1008030f040602010c0908060a0c210507030b0f130b0f09040303050f060d11010f050f0c07050a05030d170406140108 75
    0x101007480024400c51170041810b8660a00000d036402c0e10000d1034001c0d0506280c05c07060790a99101d0a2403806607040091290111b01d02442900d90320b0000b83e0061034400110394a03070000c0214030700042e20345074088000400404041e848840500001c800350303600c8100911000e100c5400501404016508148104031024442c01c1820222124a0000d114130340304ca500d8000207010300d500c00000c1214851710620032084484074040704044000303002480745011310300201102c0c0b94800c0c0600c00c10288007001000d5a4182131203006480c139840c000f40307080c046000604050720310f00a003500a84041304000902d50103a0045105003041c0b001d00c03105958035020440d8081303240400503d218003456507546294421007014000030120f092484c42c1160751880747c80c0f2170700a00500402503201c2c10051102d401c0011401000744010b038024088103030303040000390481c1100d018005416264100103014042160032600d407121008800311001d50710341c061540c0310654002ca038203100148281000c0c0d01c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 719693066 1250 719691816 719691829
    0x2004090603021e06030c070c2408010509090304060e041d0f010b010516060e0c131d0d08011806050d06060602012405060706110a0903210e090402120a050c040605 71
    0x100c3c000810309890b55450b400d204402d0740102400b07031071400c0b40300c03000700c0c000705409400031615045030346981e89107030076110040054030705070002c40c002c070360728018812210f500005a40070f075202400c0440e06200e142002c58001d00480c1c400101000c91800204032b145004a40003548068800007401003446a200554840c4140c0400f040840000400300d00412042d5011060341140e89060350720080e0040001180c554601d451603035002e545d0f40700c890201030b05420708240182250040c205841c0c8024010780b018405100c2c4901c0300351454100e007044903966000e080500746c010301100c000076442c04e01c04010180c03801404090341c80d01d41c5c0451042103a828210b10074100745a0048841e04200c240400c079000000b003100d0043c1c0301c41d40c452035040c40c54040d02143c5a95543c4207030711481c5050400385400c4c4c40685221340418005101841a400803010000ca10141c0d00c0081c030351070318030100b09080001d10407465180a01e000a804115000c2109880c00c14121010710003183c5a1007007100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 719694316 1250 719693066 719693119
    0x316050f01060e0a0504020102150f06030106060c0f03230409060e0f10060e120f0a020a0605072d050118200102060a1d06010602060105240706200409060302 69
    0xf030285407003000501655081e0051a486481881a180010016401c02543c0340701540c2101c40318941c081000845e040c24407404008011502e0243c982c030415031501b170181c481030721010781000541404012034000311300011828503080c500303040da1582d580000f200202010f00819501115903c04107058102d500802400740c1011601130780038900d450401e0303840041c45a03115030003614000c28016014814016603076140455805442103003040c2c0f0400c0f0340030007180c11907806e00c101800b10304081000f101c81c01511441c45d4195288800508071078419981403c0c4c8010020740c00e00c40640e29501c031200a01d60510300ca0f00042c04a02c0c0d12691a03400340352080b1499005900c800300061104c00c50750400d03032a400c54071190740c48028000000d142000e00982040c00540c1c421001007003d410102d02c0c13030f4101040b1288000080c02015008c0c1290f00c07500f100501425244d492001c5005950405070030500e00740402107580f15070ba1050100903001d80e120983c802c0160003c03070f00001800200ca80c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 719695566 1250 719694316 719694329
    0x60c050a08041103161509230f010e04110c01060e160e060d1a0102010b0307050607031407020a060f08130f082a0c13020a05030103022b151803140c030c0316050f0106 73
    0x42d100c008d0307035040c04030840042c40c00e981002020000d060042c1ca5901c0f440d13064041e41c0d80000d680c0c4058403203960a55070207a008101e40fa20032800c00c400110940c1811103020038a18000a0000000c0006111030080540280040c0d1030300d204010205181405a50200000c6e0002e2000003810010140c0b2140c052003501e03004001000348400182c403800e07640c18696803c094090030061a40c01144042c039468000c1c50201c0d01501500c0d032401c0d04040d9803680800b130f1045080f1003107075555424102d4846204002c0100301c0c0821008003202c0440380c400071905680ca40e80e0b522030030380c1702c945980b0f80b109007140e40108031088000c03070030309a58000c84000c207000f0348640c0d18607403a40c2e092018500802051502200c0e501e204d05d8000500040184041c90047d0040c0001d0100c8030044e40440c0d41e400560780701800044004800070350002d8661341800d000c080d4494a4070b42941d102070440c0b0883c02c18858070b010020740205074070b0b40c4404850011b40a841180c0c4044400c0600600301d6249000f0321 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 719696816 1250 719695566 719695619
    0x41d060601080c19140412020a17030904021606141b03010e0714040305030307020d08011d04020609040b0312040609081f090303180f060c050a08041103161509 70
    0x9070350b000c07030444c030a10050b00340c1c82e0140c84503901980003541c60b0020703040802d10b000585009419803a10282d2080030f002d28948050b00c2003407241800c1c0e50381c0b003000ca9a86c00b0343d4001c10004000b2008144030002d40d13030000d10502c9071800d00c0d0900da19468088503c030142c18588401200c100700704005a90690b80714918441e499200c521003a1411103041c581200115420080480080d01c00d101840c0075086640061003110b0340b028010301110230581020f194510222012010f020350602c625030400c0d01a25425661803229010501a01318603d82542520030f04442c1c0d00b645801c0d00092044503511341d10703040000e803074004079603c1d0107189000c84036a0140d103100d4540c1040c6640031180307a51003400c0015022158042c4002d48200c004001d545804800c040c0e00d05020480c0100922aa2546809172030038600c1040035000960141000c0e00104a410a044650710200701c03107982d0315201c3c0c00100c0340c00c0c2e0701c00c4490040803080109100089402e000003420200d01103e0640402d58039140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 719698066 1250 719696816 719696827
    0x10b1210050a3e13210503070812130203210f0c0309090601110d0f02031c0b0a0603020405011407060e03071b05031203010e07031e1a090103080f03090a02041d060601080c 75
    0x201c1c00c0382045d03000d0600c500304040180d200020410401001042d1056212544403000384894195401b4004c04829010800c072050300c1c01070f42c000c5440c1c00b00040340c8002c4800694410702002d07540c0600c040d42c80b401480001c0442c0445000805420182d07402c450490481d601c0c1c40045403404003a03070f80d040f032a9004149604415024004036003081e85c81c1d104480c103042c403241c8152010680d0514a4940d941c0c0c03800c46c01b4440c00c00800f0078000c0c101c6410709502e090b24180000703000c001460b100311900d05020038bc07142000210303008406451200c0c4100c80c5c403035003a4100209182034008412488041c1c0d0400014181804103c0c0b0040e041001aa00e086038644000e401e100740c0020248820140e07207681d407085074013000c40d0031458006000000141c1c6820305841c9059044040c004030700c6180c00030010000600a002124603404140d120561a40c50700c416040c0340100340300c00294054200000241000540750700d81101a1f22034044540e0b68451400550700300c60152810f000e90340d8100b14 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 719699316 1250 719698066 719698079
    0x2070f0506120126031318061a1b030f0a09081603060e0f010c050d0e1204050f010c050106030f1a070f0522090c02010b1210050a3e13 59
    0x50415a00a6544070038071180c01c0030f510f0901716070000d0040040c3c441c04900a0140008005503c0c041c3c003800501041520306004c2c980d141d03003001c00030801130101c00045401031a1240786640150400460072281c4406000d0b60804a0350069550000041d000c02d030700081742b03403000404180b01c1d0341d01008405403506540f00c1002801017001003107628811515140c1306642c0910848048061907500d4a41314001c141d08031045d00d410004504040c1c0c004426281c84415100031030301107810480d122903001d58040c0041e074a004c4044000382140d4600700002081c080f842c0350306100e6a11541c0003050055800c034000003690000e80721000040c0a4490301c483d018050401801c10110348082414486d420342c0d0303e02c0d074841694111585068441c1005c4000d01e8090013102604001191248000b4a12009499440464007040c1004036120b40100c1c03815000c0e940548008105e4400340c000100c0841d415080e8050003010300b00b415900401070f104810054420756008415200320500081d10f40071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 719700566 1250 719699316 719699339
    0x10c02030a121d0d0c350c010e0312160c080a0e150d1e110a21020307050c1203011206021b0303090a05061501170709031202070f05061201 61
    0xd02010109440207000c200190403c01e0809849807a902c601720003140c1d14000620035440a402480d0803508182625100700d0700310721145c800c458072a86030b20f84250001180c00b604101c0001081030000248010820881c007403814072407656509800311801c10301008554070a41325602030440581840240f482030b22452004191907001803000c100d29006c4100d074081c5900c0381c00300d88003040e0303103c02040c100709050301c940c030500c3d1a00c2000c11058181c603d100c0002d1003401c40600c10000d4400d072810344c0e40801c1e900c280210740405c40c11910780c07918000141c51035000c42c4088140b40f29613a03403d941c2c0240c4504481c10f86002076480408915555191000707500543c980740904412140c120220340403c1010f10f03c1400c2c00d80051110381d680c2c0c2841400c3c00805041007039a02c242c0110140da6903001a100d103243c010550b0309500076a40c00001321100104c0f5000101100c84803017603030350000d500003402c1040d81e10740d4030f0400b08190744104100044c80b0b418042c0b0700006017000104908104030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 719701816 1250 719700566 719700581
    0x906030c06040602030a030609020406020d200106060503040201111f0f02070f0803060a0e0c070209040f021504080f0c0f100c0b040614011d010e150d06060503010c02030a12 76
    0x240403500003191a1002440582007508044016800840c19114155250140c400100b40f403510852609081c03050003074480301812444000d00c500422102015075011009816040505008000040c0c654130014800d6005440070b80c000703040c082400d0b181900204900c1002c00d10044012691845000c04002425035054803004035030f802d11547c00800c03010410110500d100b211030343e42d40c1c540202004100300f041e070003009164a00004104d401d07071101d400c58030703102c0c1c045a00c0c418554441c40c01080c0403400d0540250401d02c80d01400e0202c40710700e8098400e0351400c00c10b68032119008540c02d9910644c140140f50302032012082d6007140d081900c01e0000f200ca007883c1c501d0004040c1d440d408000c0300d003034508603191a5224009407030030180b581224050200100380b20f4101d400040200c10024040c005c03411010304c40c4020414070564001505404003014203d6080c000450a141004000305d105050003035007841486d1820601c0402110711000035500c0b20b4504c00c8420381c5050042428 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 719703066 1250 719701816 719701819
    0x20309010207031205130e010303030612050349050141060408150f0708180c031b03010e0c0a14060d0e0d17011d040f0b07111204060e0906 61
    0x10406c1d03914840041044c28003600c0c04040e4640e041d4550301d80101140d54aa02c03081d002002d04d502c840c0098800300031208540307003074913041449141404078201c46c00091010900c03003a4446124501001c90740c42801c10300003e5107030411041c3e80e106141d005601c0c03a007031500408041000100c40803800e4041d000341849000c07000c03804a00411001c611294420b03000000c1c680d008960002d04001d0240b1500d0344421080301a40b0107043c01c090240500c034001d0410070103010710502800e004107040140601503e80102241e01d0080300000c2826001160344059010f5428036071040410440000c4506180e00d0180203044154501040c1074001440240b9499114000700800340500140b4041c205000700c8140180c604032004031000707410b6400b1005610b140c07512240041103184042010342240310300d5104c4165041d40c8074500b00c000c180e51302c0402884200300d8414010340d95804505452029856421100c11107240205e1207452301681c80340310700258600c0450011401e045a405402140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 719704316 1250 719703066 719703077
    0xe0a0f050c0421020a0e01090e0c0f120a02090112060b0a060e0108101a030106030b01090506160510060b030412020a08090d050a1a070e04180206031b04030f120203090102070312 78
    0x21540d000454640b121b900400aa1280000600c500166841590484150003008008002c0408086016050300500040c455248400340744002c0d08140700341c0d006140c0c0240f14990640c1c50f9583c400141c4508a002c0d15a40c0c078218809090b414045211015101310761502c20440c0103103c011184124020030320f080002c1c10060018526521082c090454000b05400302e03200d60504100400711040e25118038108000309004100d1038940d01d04560035000340351101e107400895070410701c2c6814600c0c0111081d26181040005c0d0004414010714055803203088038943d0241c400000300e030b43d518184805005190100456082031400d4005050101e120f4806c6c0c580c804019151100c5454030740e0f02c4050184000310030012015440128580b1000d000c41e403c015001d08039905031020400048000d005060001c00305280890304460040032042200c5019a502e4592510700324048040c4000c07138501d480070031641122030000c41556a49601a4007d24005107035032140340c05d01b117046032804280722 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 719705566 1250 719704316 719704379
    0x50126030706140613090309061409060c10200f0d0609020a0f0e0307060518031e0c0a09060305210910030b090702031318150e0a0f050c04 61
    0x1070041c0543c000304040003410100314580a0140052428041940c07416240380c2502900085c1c1c01c821020f06903403481c40c040e1030f50094803180408522034245240d038001c1d13000c40c8440b0982c800098002c50142c800c03a007841030000110f5480803890390b0441040808506020180411904101401085805841c045840c03540e40c1ca010702207034000a103000014003103581e01c07101550002c95201e050582035004110315454038000821500545021a01001d01c03d18029103543d01080000c090b45c65143c020001c400304100602d41c0d6581e800c3c0c0460040c4241d900010302c001d400d104600c00c0faa040300180c580c4105103200c0030f481c8040d40d80c0c503070700300c4100303000050007500c03100640e42101d0380c96140054403c0501e020850090001000e91046600820070001d4410040103d442112100310840910a842001010244c1045100d945401c407110320f0020305804c281e18440d020300d894910800c8444410350030501076500841d82052082c200704030811454050005101014841442242640 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 719706816 1250 719705566 719705573
    0x9060904050a0905010e0f0d0507060e1609060b13120204060306060f0f0503030705070e0403020f011a19060806010f0e0a0605030618070801030b0901021e0d0c030501260307 76
    0x1181c05075146489070703030f03180103c00810400744103040b04252a20b00400007014040304c0240c0d11600348203844108080807803050b01308185c0b5044401416008010385900841140c0d401100361628402d16580a081c0750000622440c203100b1a089021088200c400d1a428030704c400219100411040341c1003a511003000000c40c030345100d03074400b502c0b014030034400c418a807180c074404954094018078401d030800c20071880003510010300941159810040c04d89503542c1c80c10180e080403082184007010b0f500340313119000c6050b0004040f501c5620200c9900707503452135000101800705800e01949000c91b10440100c1c14660203142c1d11580d160517441c290710789501000101e070985480380e00c0640420000f000b8041189404410b40342d40ca855140076041e14500704074000c1080c030045c4000350080121002155441034290100e90292413455880e00c0c44e52105103103070b02c80c3e034410698480480e2030440084070080c46402070604882c2d90a05020400da810126420701045454a01d08940310403c50384000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 719708066 1250 719706816 719706821
    0xa121b03050904060509060d120903060203070c0314120a051f0305060f0106110303060d03050f07050d11151602030405270604051e090f010e060402041a0306040809060904 75
    0x41a100e581c0349600c0b040c800c1d0038003056400b6034029a11078040542005415207501009007069500f0200020300704001180994480440c0d80002d081d141c00001001040d5401c40b40c0804c0e118403d80d103031000c40e0888508445580141c0700107040c10b90180c030120300c081403103400c44c0303420002801800401800420085503000b12540c011680d5401500421a000301408407503070040c1105d040564204032420401922031100401091141928030200d400345441281600e0300c1c1400352a80c90b58490190a14559902c180ca421000080d01240300441141e804a903003080300c2802d690540c41a04c0301010f4908903540d2081000c214401403200051a903514801d0302091742c040070442d4180301e00740902c090320784001480c1c41e00a034201011b11040c5620f024068804466100c10f100340e40d11400511420060040c5240200751f0030f00344c10700d540050116045004a100725010440306540c050140c031003c442954007035142d0480170000e4041800750300104010200280041e00c0e1189041c0040c04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 719709316 1250 719708066 719708117
    0x50a0b0307230303040b040e0c07170702130e030a0e060909010605120106031b05030612101e0b031c0903050706030b03010b04050f0703020c0a08040305030a0215090a12 74
    0x180c5040d41d0020380b107169048101103050030401d8000d907140a0400170300c250603100b01e20411110620b07040004500c0c00c005025070781c501d82e1008408e101c0711404004040a038001410681c810440150004034010702d0303120b160301e0f42c01d280c0c0295040011071001a110001032003486078008908115542d459915001200c4c06000151034054a0303000c1d0060680651905805c040241482d000d41004517004905405c2003a06103490000e9880d942d102c0805c502c1341c1541045416841918800240c140243d000a0100c292402d48142031541c0c4a400c07605940204190640580008184900c04001c80c0d40c80c0703003800b82a0900761615a030f41e076152031509060350300c500c0010782c0d103440c0d1111b05d150038041c44442590458041c040f9080c00c0420b00140c140c043c090a051680c001441c41030503030309112001c1c01c036070010240744d180c40e501e00300552030341d000020400043c01030210900d440d6810941d0b05026608810080c40b0b07020381595558641c24003903001c0c8007840b0304d1100da605002c0c00049000c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 719710566 1250 719709316 719709329
    0x11406011d0d1a010e0f040c1a09130204050316050a060c050a0b04060b010807050703270306181a01030c090b120616082206090222151406030a050a0b0307 68
    0x142c962420380c0155180b40086d00210201c2441d03030501010130320600300d14017070b182c0d81d818090b0000f403864441802442001c0d840e03034010213074120703848040030542e0240c02183c1c020b0701030382c40b8408481d60910b078040d280d00809900c48041c20051000c51700c22028080c00600c10800c864658089880704050b003441204e04480d000e8458140c00d4595900142c03440c4c210308541040d0381807a00ca82e8014021045200424414003240004500c4080c61000303003000941d00080c0c10031032443c146154800c1c10175105020703940140199412911a00100d004904a0707411030301c0c24011f80e0802e02041d0142c559004919480b04404419000d0f01106010340350050100340b100d14001c4542c00c001512103140248480711042c6001d100b000d114102c5449459090360040d400641c2d14880c5c40000c0307205a80c01c9401d80744071600500e81c92084625440233039000c0b1481c0c03401509a039510200c10303000e41d180400541001c414000f00b0000c0c8031640250f5000348480c5c0000c2100488100860700d05035041d4081c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 719711816 1250 719710566 719710613
    0x6081216150c0f0509180601120905280804030f06111c111e0c2524050f03130501240801050106210209040203010f08011406011d0d 58
    0x2180c1082e00001c1c5580f05024600300366003400c100000042c0f01e5214a4002103c1500b0000003500c942e120304c003006550034516204000d00196828095512040000e44001916020f0404c400e04117145070b03a602c03000e501c001603918160840da20b402c201c00c0c4420003155540c1d2501c003000b004003070880c064103a068042610f0b0b000040c0440c20603050391240c0c0040a0313900810172035290503003c107004020341040e03424016590761040e4503034146019408150b02d4507455204409213007004202d80018200d5088518001003141003010121403041d88900340800b007041080000f8407a4480c4010303640c07090b9059480890380846032503450a4034038041102101c00d9000b500c0c00103496201c8400f03000307809010020800c56040a0b0082d01c410f21341303140c0d2040e40721080901c60385141140c04072898140050000c0d03469594541d08051140d0b000d018024442d420505083d0061303440c55141071040405030b44551003001c9a0010040c540b49500725140c200d101c2c049404041806a00580400f401c40b4000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 719713066 1250 719711816 719711831
    0x120d020a02060a0b1f020c06040807050306072f0f07270e07030803100f0f0303030c11060703320103050708060112080a17090a11040608121615 63
    0x7410094002c0070000a03a10740b106203250740c0c40c1c44218044508501c80501408442907501b80c2c074001d10b8010056000c00d00180208001d80e005c5001c004840c4d040d4101c54803515a8501942c1c16040c3c555005918540362540c003a80d6039030300401c441c0040070b2100340d03240c04234200c0c2060b0520310140c00c8455400c0381d51440341c40601e5103c1502081a550300f800708443c1068000542d107601e06844041c00c0c0d4030000c40450100101034413010010075001805040b400e50781d40f00c0c54018509480182c0c00300745407044420120740104401d043c91140700300680f6003a91203510980081c261140000c074022100e60201e03100700c290841006900c480d0b01c0021500c0d61551a1151a058207500003080075084000108a03101521080c1c621099204130b46075250b400009084904011001118140d55070502c01c0c044035075070104036001174500545c510402c80d06038006000030348034030380704822065206407450040030b143e030005054442411002000119204e8856101b104410550105507507502c01c04c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 719714316 1250 719713066 719713087
    0xc030e0f0307170d0203090115050109060e042307020c1504050d030c082a0c030705030a031425060509062205030f07030f030605011404120c05061303050c03030426120d02 75
    0x80b0327103004020074644502814100f10000f400c2160310110700303000c0e503140d418003008101c0d80503914510506045c4086510b24003c01c00a5458520480840c040c4070483c0003689210411411034013a11030141c003c4105486030340e41107070080c0c3c040d02c0503610035406111404030404900722280009540403496202c0e020f41d40302c604c1c20904154600d030301c00ea0210710204038584010902d0514030b0340600b03060001800d5180c0e900e80c1032081482d06450f0f01c004861900c100654003a402c1c00c0903015860800056503151b90107a41d4800a44241c81c0141d4034050314065076015100d545d10300e074410300980f802c101c01c440e003610264008290880119070b242d0707800100740d0b034141304100003000c091820f10311101c484c802130703030091080d0300a60741c000498010700401e000003107180800410000d09125a104100d078441c4c1c0d482c14241c00219128014040d00145510b0f000003030700e0942d1a15118283e6410101c0084031211500c1c14145882e4010a9018a4030282c0e8102426035074201c0f6002581d621609030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 719715566 1250 719714316 719714351
    0x190507020f10020c19050309030a06021b0c01090519030f03110d143c090a08010501051005130b0f12010b0a0e09060418060c030e0f0307170d02030901 66
    0x1d00c02038443d2040c0501c01d80100005054801d03401001041803140415041c800d0079441040215609803044944103420095294010f18505000c0700301c5481c0d0284100c0100e0311051265251800100181d406010900d000c9000314060300c0a010414040c40d030342c2e501c025208029803025400700d10800640d00f03c5080600003000710100601e0400c01c41d0384502007400184c01881c2c902a9140c0d400745e00c000c01c418814501110050380d50f01c5044000000565503445035101840c5c650041041d2040000d00c03030414000c503030503128010319812003500801c104641a410074000c8450b042c625010003c1c0c2c0b00364070402015081810b000f299581d00126490801081040c3d01102502000304071301d03010158070002c0c92800c2003046070140807a44541002030040c02c1d00d04842d48103036103060403101c1044601e5002c10200b2140782c9092024017100d2181648410304000350100030340082040c3c400044604403d90817000045107030500b0260700801c040308982080b544408981e6441c600c034443e81c0102c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 719716816 1250 719715566 719715583
    0x81b03030406170c1c06051221031b0703020a05060f0405060f101a070b0c0405090a0b060409240803090a061803061112070e0f09190507020f 62
    0x690040d450035140040041108400c0b0869810590341800031581c1c003001c05089554502495500b0310350301c51070300d09020042106215031032045010840700d403508100425500c002c10410001c1c00030750b22100d1541412a0b00090409980329900e4078801301c02d1118601500d80c840c06a0300501c0c00d4242890000c2c42c0180191041040c1c118030403c10000400006440b80c0c041c180c1060743ca0191108603046a165070f1980240c00300c00d003503201d5100100074400141554900400222a6988843c228244244903e002d665001841000014031329015600800d60555015186070314181d42da03c01c0d4400c45040042c4141c070fa250140080c0e039558a14400d041c00341070160055407900e102403000520a4074076206500c14000c4005803800c4441805180400640e0004014420703186600c110005940c00400944c14a144440200703940612030844503003500390241880018440600400005003030042c8224070340c0008106101703000c891405054000d244a800070000070f42d855550600700b6420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 719718066 1250 719716816 719716819
    0x120f190308090102120604230915011505090114090d0807020306060102070503060a0902040b060403081e0301051c110a0e07030606080c090103050c1e0306010905270705090406081b 79
    0x50110303017042c0c5d400300504d50300b082044400190b143c42580034185203000f41201c11418418007000c1003141000440c1224801000d01e01c02c041a82c1c86280c407428003400b5030041d0002440c00d0041c85100d501410000a446045800381400c01c42400300282c030703003410107100b21040c00004c07440ca01103003001c01c41c86030406002d00107040500d05040200382e5404d8000c184a040c540c40341450003c2d0346881d030080500f283c010f0540ba41c1c4644038123154035554480c518880c0d2000f00d485c004041411410190f83c141e9400410044c4405900181c20350051320032031b010395003040300304078004065a40c4841d80c00100804244070900c0d2800400180840c0d14542c413072401d01c1f084a0030440007402001c100c500180b003d080001d080d80300c2c841e00c0d10302401101c15124032080b05043d0b1904a08416000e10700c61034090740c50300f0603d034480f003e1249082101004140ea46020b003c2c60306896140b090f03207a8040b09a1610609006a2100041c10b0350081da024800d180c014045901100e52180141010540b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 719719316 1250 719718066 719718071
    0xa080105070c110414011d070f0503040305030c0f1801030e010903050405120c2701061b0b15040c050c0d090b0a0f03090c03112d120f1903080901 64
    0x61480020304001403941000740444000307101c00030f8541d9507511079014140c0c00003040d40690303181c150114890103c800c0481e12030544c0c00c00188080d00c201c10803000016660359035419510340c0d50341030b20190400340c5038404a00052103011460302d558006881036290100c9420101800702002501301c6003406080549a410030300880c2c086034002c1c0c200c404503003060300c0d81c1109a1460315100d0400d07495800c4240c1c050454840b0f20401d080d0344100c100d040801c50640c2d101c0780d03650301041e2002c0c2044402064544007002071640429509414582e000c02012050310b541504030000404603003000c264040403a001003800f19180a081004a0701501c0a04040d01c2590900e102c00c200c50260024100402010280320031400344a40c00c1355020681c0003030074212254880c500100208410404640503646034440b00c5600030070b04d480c01c07001c506078040f020042c580c460240142903002c1e05082c0c4451050340d03c28000b500c13003001009254101341e00f003030036408001c0ca4000c1200402414801c0c1c1e0340e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 719720566 1250 719719316 719719321
    0x6090a020a230d0203100312020303070e010503060f09010602030c011b0e06030903040f0b072f10020c090a0c0f1103030a090204180c050103110c06040b060105040b04060302090a080105 81
    0x190040c24103210003a003100700c4440c0090320320200b04548100e000c0302003602e001209000640c41010b07009001e40f4426507100c60048076000b41280d90b07010484001001500350b803110050b81d4001d800660f0060300c00381000d8519600c40d03020514140080c0e000c140144d00001340041400401e200d10344800d030182c0030185000319040d5009100340ca054500d9403040c0b90000200c0c207400342c10811540240460842005819921801111079030081034003500c01c01e890400074409000cac0c0b1400e0503400e4589130011004804141c05020681c10074034810011f40c85080d04140a603559503100d144252010a00455a00c0900304020040341241d1062400e00c1032801d40e800069902200f41d82c0c3c8280d4170785001500400d50300006000d049450348911002d021423282c5800c0c000b00700f2041050301c03401e0300c00b803140502800f11701c07105224650100d2202e800c081c000c82c0002d1a1150b045810850500d020303424203894441d6840bd0f940b0a80c0400701082e0700043c030000a0808815803001000004000c01003032 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 719721816 1250 719720566 719720587
    0xa080a02090a02030c22090e06101a0c0313140d12080c07150506040c0908100e0a0203190c0512030a230408060f0a05040309060c03030b1806090a02 65
    0x41c58042e00b14031420f900840060b0410034031030243c50b825007101c02e4290038070030310401400c50200139008040610b8200a0b00210101c0d0026405000e0602c0c0c00300c101155250107450413029403502003098941004200305603c4110070406081d24078685902010304074581070009018003507025096014080125480001c03c0440c0c7c4903105040082c01e00c1a00e03aa11841c6146980c801c00710014820b01103990511200e0b5510342c0300c1c41c032401c41940e0411002c4c5803c441603440410307500c912a1990300489140c02d288059410184907000d0301000c540c00c00001d580000d0820701040d400e442c2002c1540d0448040c40799035006070b0300802082d1401d0921249108100c0d40700d218882e90318003071154600da0390499010142c084411101000755580d00c440d00c401d138058490506440c140c40a0007100c0109400038403d11030b82e8040c2d581501c544072024a0a41e06548079044c0d80c3d03050b01819034400030034405031100340c646160a806001d011055141c21000c200400b80050300d0000664814840c46121 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 719723066 1250 719721816 719721829
    0x1060501140306010c0f0605070210060506090f03210c0106120c0509070c0b0106030c09140f130902030307060b0405090114060d060207230d02030a050a05070f0b150a080a02 76
    0x808214110070756a58440f00180e8842c400400e00405142454042c4014000c01da0700c0140508426401d44200424045511040e19503a0141991042040154003160724000d1000c071100c15014080c1e0302c00b244010a046460090b05803100c010b00d00006808030344c0b010030302c5070340050010a0700b109400041a100c1d0325907075149020381401350300c0040100d40c000380544813101d0aa03500034205400c0e0340e15110010050000c0030400004234503a00d002250b5004404c076421042000a040300601d001c0c07040400494124061211b16540d41d1540e8000140c1c400340001c00d03220380282804109130200406110885000425042240e450305a1070903003484003220698105200303c407448080b082c1410558000c0c4a2880010444011a0400c00c00a00384001c11048407444009403580550200c8042c0c0c4c692052000f00c02c0040e004100441400d40204050551180504141c0042e424280da54080900c0142d81e00407240b82854030009175450701101c8200500065000740080c6402d95021a15 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 719724316 1250 719723066 719723087
    0x50d14093702060d09240b0d12050a1e0e100e0307051017041103060f1009050705070f0309090b060c07030f02030c1005041a0405090a0b0f060f030a0b0301060501 71
    0x100d0f12001810104402080e088036500315002007001c80b14182070500308500f044e9084d07466483c00e081c0a0040902d01d02601d4007104180c022070051074a0030728900459803580000740a0062000d406408a51000c039030400350504400b039165200410003000411800025480d001d00400065065600e080d840100e0707000100c41054591110250a0b818180c40b842c025000011103170f511a0100b10034001a1949000782510580030f644540e02e46c54901d5400f188100c4d08003c464007420303420070000605520099114550340741403814100c040d580c4000350300b15008160300044582d4424803002020b8410940706c0e4408880c5980b4101c401200e943c3c589215110140c0b00381c40d056280f070b05640f0305000740d0002103001082c8040101c1e00c101c0140042c1c0090003000c6190510807811903203002e086040b1025100f00501d82201941d90308003400180c40c05042d215003201d041c000b0805a5110f1901a10f229003421031040d80302c2c070f402d4140c5422510b248103498881e80c18070401700860f0341c01050180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 719725566 1250 719724316 719724319
    0x6050f0f041e11070b090102072f09090309090703020c0a030c140304061e0206071e02070b0a020d03150f0b07140706031a090601020d050d14093702 65
    0x304002034055801c80c48110307030b075401d940c24105030b0102c4004060748000c00b1618401c10307841c01c0c00e4441e02012400c03400399080c020320a0035040f00d625080d40043c10b8030000140c0c00b8040d00c0e040024040414886c180503a14401c81f5400443c1c91031252800c0c03030520754400c80706e140031818540c04007403055480c40f0080d400750600009075850810300c210035284482c100401c50883e983c80b507582c640140030703520716220b00c484418030a001300240c0d84003082e120b000e40c140f903480003421800c0c0d8614000444180c0f01e0542988030751203000622190000180a10342569005808000003240c0040d050b00c0d4020307080c050319000c07843c041c00b889141178040302c103403480d040645c0c1d102c14172072504072034000303005201030302c54030a80c0c40c005a04d5074150004006c0b440502021241421981c0030b00040b0b0310156040760141e0068540c021002e0b1050740138200814145070b021440c0641e43c4500c0c61030840075140702a0a07000481c1c0740c02e01502d100c1640c1c007004410800311f0600c0046004841c030209400c100203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 719726816 1250 719725566 719725571
    0x1403212d0c0d0612050d1215090b0d050f010c090609080d08180a0b24090601050d0b120f012009010516290709050105090405060d050f01020c0106050f0f04 68
    0x60b5000a4a07502035005004d048010903500e40850600355602d04202c0d001500140d41c1c80c46080c0d07110054051415a0f4403101c020032a141c0c1410390705000342850b05002d5401c0300640c800e602c04648101b00300702143d101980000b41405507000c00074442521030700080700b441401002045040800546100a03104a241080d25038541151026045062045040701407088840040900c008000914019208109504200030412000c48020740482590306d60002c540c0c0b00103141c9500810082410306210380000444584900024091190004010199601681003000c492100344070b84c0d400c80110102007481c0b0241d036a0044940d10030044060704000c004140090a11074103030a08001c2036100301e1104101d400c14010401d410b4016590311074250300d94012403d0540241290001c2d1034042e5030b8a803620743c1d20030501015041c00b4012030f4014100d00c001c500403030414071144454001c501c00160742e032051030f4405030a450b201d80140f40b00701e4407084030108541d2016102503003414151400b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 719728066 1250 719726816 719726827
    0xc08151311070b0a05010501030f1107020405061201090305070b0604020903120a0203040f0602030a020c06160209090a0606081b040605010c02010c1b060c0212011401031403212d0c 79
    0x489031540034051005000380602d805000b00b00070701c5d401c01d50580d402a64200039480c0600440b038181c495429035001c43c1c1d08204180409800d00d60400c50340000054244030f564401c002c0c4235030031245940e40941c0020400305284040100c48820a9007008048600f54104103010f00040e0301c3d88116102e1003400480061f21200c030074000c0c0f09840061280c90000070100e590f42c08042e40300d0340581e01c0324005010b10044d401d8a89805019a159980b4003d000f40c1e011006d542440000c02001d80386100e035120340d81c041ca00060040c0200405840c08801415800a81c0302d2030680c175501c105c8110b0b100c0e60500d40e0a02081e64807019501d0525024606511421000d0070500c9840b10031820300c2038070410f14200421000d030000104800184244e03080c010f400400e002c001c2c2241c191384601800c0601140c010004204102503114004001c4000d491600d4004a001800f10003444481004500710904105010949280f00ca199126451101c000180c01c07800d842d80c0702500130300488403000c01244 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 719729316 1250 719728066 719728091
    0x1201050915060d0902100206040809010c0c031e0b09060c0f0d0b09150a0812030105221e0b010507150509011e050f0619060804030c06020304060c081513 67
    0x4501030084000390810782d850400020580240c9100e203000e031b02500d000e0b02c40f190020700c00a0820702c200d0308409041d003081038400046a41164160b015190b03803440315408804250900c128000b41d40b4469281d100d09865890090402113000700021b403150007100030404d0301c1d48640c0c2200d0700300040003555039030707840782c0503c0000500b0700c1200b0582107070b210810130101c5035840040d0750b4040001c0310000c802581d240c14095492032019402415480e0602c0100002d081c0312441d054903d160320400107554601101000c221071700f562010034010440c00c2c48070b0300211a48141070301020213191046c40c1903480d40314402c0703103400a007010203010b5540300001c003004420f5014100da08000d126903945415585901806800140c8001443c0703215100130071158a02400c8a1044040070603250b5a0103160407401c0c0ca00c590014801d800f80b00700480100c000901d14070003184540e01c1201c0005650106020003004102c00402d10f0306401260fa800c03c600380c0e41c207044c0f0310803950416804581c0000465 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 719730566 1250 719729316 719729341
    0x80a020f040e0415050a06030c030f051f09020a14060a0e030f0d020c09060d0309030305030405010209040c0201021c020412080d0603050a03090806090705090f07030b15130b12010509 80
    0xc1c4002020310711070081c401002265884d06003034060191003488591a4440c441c42151818032000b04942080c940800000e610b541a01190074028000c0c1c901c43e8000807503c8864a010748591000d0942d100e90303010840c5840c1c01c0d80700141c00c6c03081806035205c0e0a0008510b251003500144000e0015040c441d091a503405c10480303890001200544102610004010356205c3c032004c219803007511054001180740c105180c409250325015518251a14a1a102910750f58005002a00c10b03540804c80c00c88182c60714020084000c0040d03000607a14034030380304100d800c1503842d00b29528040c01080208090344901450f0204503801080701541c41202004410003444654001061800349003160000c1c1900910141c04407039200054620540c4c41c0c004654492159018032075200301b120340891250b03e480b000580d0306c111582400108090340030009081012462400340c10300500180d100042901a88040c00508103a0102401c15030901201240c1c3c1005000350344c0103072a0880014261014813 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 719731816 1250 719730566 719730569
    0x51503010c0306090b09090d080403030e0604030915021f020a0903020307031407080a0201021c1710060e030307050709020f070c03050703140a02090105042019030c0c03080a020f04 79
    0x20000c010030400a40050042d010300e1180000751890f20103424172505040425a10411a40d80580300303d18010320140d906c440050015400c00d035a0f0485c0e5044e00d841000b440b40a01c0c0a6104c49800c1071401103156131022285441c501150043c0c001023544140010702601c0a2103800380160710342c40303245c04c11214061261300c00f030361601c0390407800001c0c0024070741100313866032141082c3c1e814240c0700e038880c50f5540c00c140d8000780164000c82d90500c00702190039433010410000d2502601024401e8800310105609540c605541d0900382002c110082d0041003000603a03500b0360240d41852895151262142c1c400c0c400d802d0035075000103001c0030b455030a0085801c0150b003d4598040542c0301d080c4281d072544640012213203a000c0c6800b00b0f50b0090005000302016a0043c03500e0885c5e070038101444042d10440d50081c00c058120445042c0d2020710710b01070264a25901404003242c03800003001410b4544810b0800300744020191440c002c00d5000c54810381c0b1170300940004d41e60760091010042680300c1c2c1e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 719733066 1250 719731816 719731819
    0x151503010e011d0c010f0206060f040603060c0f02100c0806060f090a12050c060304022d030114040204050606040b0a0f0203040b1224180604090803091f110d0515 71
    0x20310110f46034000c9045910707095124440203c0e16042c1208005581000c820746440300940c0c031003800034803c0d10b0140c001c10580000235102203003c0360759a41da003065502102a94022031504144148032a90400103800c5806a510083c8a0406142c01c00303040c030b1001400641c000e00000035081048544501100e4a103c070103861114081e0340c84501e0503500300ca10313104071803600880144080600d40003043c1c0c1e00407500107141400342c0f10741c14035100904813000703400300318001c00d028801c11641e42072244154002c90a01d00200d6442c0a10400c41114001414a44503240521044c04036104890030f4820100103410b02d44c0301d410aa280c01c0e841e50080f0350103500070141c0001c0a04801c554010703103500480080e000791140c1d404469803440030900c040f0400d9001003900c200c40c0d8556042c1e0020710b4100a000d0030014146405884440c1c1c198004c5817503444a511515401101481c0007540b199005c00d0340004000d4150307030030008a46889a50500d1700314a4450010881c009182d03880304014140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 719734316 1250 719733066 719733071
    0x6041404060b310506042003011815060c020a09050a09051c081801060e0a06151d280801091e021c05030c1516031a0108071b1a0702151503010e01 64
    0x30749803240d002341d20034002c140882d0004e5020150104882c003d0002c008a6140840c0a541c04c00300121110400781509a0780514040c1c00001e450401d482050f006017483e010114840803a03090451800540e00f07066103038207941900504d10740f6485180d2035003001a4401000d4180c1011514a0151000307402c42c1001c5010101841020b50705035201c04200d43c4d00000c031100741d44c0015000e40c0e2a1030090708560600200b80c4180f10140b5200300e2030025860350540382031241000d4042800c4d4800035030070002c5180c0d55000341b4418043d032a24a070441480e6589816614002039011400000c01a030681e1044800580b141d0708100d004e0040e06ca004880b070040b2100000746016030307100100150350705c44a5400e60000c44542d248a4003850001912400b1086c1c60003c000004581081006280394104290400c60319891207036448003048890080c0395030102d119402102074500400941031100350340c808110360801c0510340904a42c003c0700c544e201d50400a601022901412660b14060081e51 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 719735566 1250 719734316 719734361
    0x9020303041505090f040506151c0f0b01141c090303091506030b0702240702031309050106122c0316030305010e01080d1706041404060b31050604 64
    0x3c0d88040500131070300044402d800241d2045c02030004844007501d149030803042c5e010503a180c004d0080000d00e42c9240d48003104003e52103e9130903004854007040402413070b03519010401100d69010004c0c0c040300c10b40e030034954a0181c4002c0e80d104003511240031000e100c1e44685660080c075000c2d50244a45580020340f8030400e00035440744400515030350100700d400f850341901240f0a24400115041204615080300217844403020000d0240000140700c00210310082005111801c81e0750010002003000807070104555051100180001c448400c0d406103440c58a800610314a0f01d900720314482c10300c0c1c800395440540316119510300318402c10810783c04400b0303051051402c050341a48014100d444254104070075076206c95200d0340b00c000710f0b410800042c008800a060030229550310326003040c0000c10004004400003a5a19440303000c0b20141c0396030b41d88403003654403070502110071622107040311a01040c0000014003c00e500030100c0103580007a558400040342602e443c0c0c0501c0449a0044040c181507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 719736816 1250 719735566 719735609
    0xf031209080c010e07150c0c170610090507121a04051003020f060901020d0f0c020312221a091206090a14030c1207060f0c081e010305100902030304 65
    0x10b500814103094030303600c0c1102e80712138407401103180c030701703860500c4079807080001100d4040381c42c07940d200c0d4260350011071060b0006002c03030300082c00315410043c800944818608800d00c01205007450f40140a1035080508010400c0d90107405084120b11403480040e090442c100c1c80182400c0c0101c4140d001450101030003000d040c00e581403030803248200e0310f80300070a80890a05c603150082a40e0b55015a100498042e807450107049030003194503061414884440351600020303d0700c40c0c3c400e4049038401c400a41030444580031590081e401c12180000862a458058440700070441810524207044c0c01003200b07542d40d5680c405803210008420100e404605003503054075115050040c044883c0b5100e080f495842036004019074141d4140d4a0191100105940041041c0c3d130140404480c5195108252501c0c000c0ba403041d01c12500d601d940b20f03d06440e0505010502c1060603242e1140320513094010000188002602c0303200c0d80c0007031008a181c0c6514404249103009903045014403e038030b80a4070140c2d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 719738066 1250 719736816 719736833
    0x510050c010219030f0b040207082b020f040302011412150604030507141008010e0109050c0906071b09060e010504020a031e0902012c0108060111121909060203070f031209 75
    0x121341360b50304101c5001d4071001c0104274402c101d40142284c400b440f203807030321040254408559410107028041151600743c6034904990205010828200000c00c040c415968008506840c903d5180380c268a030200680700d021170040000d000b810703898090328400300302e030300d130101650003c2d98403d01b20b8086503180d8803c110145100c50015008004010544a0441c4200d50a074105c034a0345c540b860030381c0d0030f060310a8003901c0000c2c903140146208021045050b16000c0003440c1003805200d10710140158903800455014050384007001c4d003401c14a0520842281410a41c11030f24100c40c01030f500c20200d0360617800b60011804e01141d014003a52074100e41051a000714051074800d98590b030354142d610b80048400e5141c00e48c6038226646400c56076005500400b4199040901410180d82c05c80c440360b8100e10b0681402ca031740a004c0d402140d03c0c1c410320306404207a9284040c50070042c001c01d00340003000b50b072801143c001802d010408084035040c1070180510a54002c0e40d814184460411820442c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 719739316 1250 719738066 719738081
    0x8180406080d05030115080103030c06050606161103010e010b030d0318080f0d0b190605091503130b061008061903050114090d030b01120902060c060a0c0906090510050c01021903 78
    0x401d40c0b986c0c103d40e85084c3c0701c0c0c1e600c103041c1d0b541602c0f240e0003403c0580b44c101c0100001800ea40e0400c1c802c00055205495100c41c0140092060041d9030800003081c05160035101c40500515142c4e0511410885a607000707d540b02c1d000216140001c4c02c5640b062000f520b0000594020b00701e40d0740014070482c080c2c0aa4010050710302030314428442044002d043c0160501c084098091815880e41c0600941d4070400c0204070141004102600c08800d813603034043e040c1c0c010795903520041000340a140400210801444e403180c41260307800b0090080140151250074000c0c1071510034011030005200702c010800510002d140c200c0001c0082c03a40204120302d50300c405461031015441032a4007000145d209014041c0a2001a528140e4055035840041d02400504508981c80300051012107007401c820000ca610134501c500011401902100010380001c81581013101000322080003070080740c0780c0d1030a84600b143e542c58465a0713141944066802070088011400080030481c070076503c060b90640081c1d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 719740566 1250 719739316 719739329
    0x315010c06020a030e1e0d0e06070c060906141e0702012109031b0c1a27150408030a180e070801090f1a0f04060f0e0a0606090308180406080d050301 65
    0x741c1c00c1140d0003141b8641000c0300d46100c0349500054026240e01e01c1000303003465251020b40071a0904030259035009406105403ca07800081b4a040c0070480389900182c2d00f80b420f04501a05c078a090602002c0142e503000d030301242d0007040e130009500821a442590100411820060010490041480010086c0054170030039800a100e410f103000c4d03103040d002002800316502c8192218014540b80c1a0011a803104085001202d402c2c003031340c518060161070410112a07100391180c10900300204100120085107150f5028084c180703c24000004004112055075000e410440b0b995241c014141c200e11700b15400a502c0241c0c86010f0007110b44d0010410b90607590310400520003003e03d05034050880b50b1110654120300440303039482002d800d005404680b8140041d2011880585075440100e9001c04da03448048080055420040d05007060703c5910090f2450f842c2c2404401d155403a004813900915905043c032002d450741c81181e550740d59015400134071101094884194075450003801c035410901c10720 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 719741816 1250 719740566 719740573
    0x4050c0909041b0e091b060d11090415120f11100c2109050108040516080a0303140105151606110703030605030f0a2a1211090106050315010c06020a030e 67
    0x4503000c1a0015a18450402c010042034100340c034212448004054040307407504801f04215004100d03086000da00d00860980b002141c1c3c410341442404200c0e50040f002400c1150102d20500524028507031545c112a0009105c480340a101d04054040c11110b4031902c1d803100e001c4115540003500410f0010703016004900854070340100c0482c00c030115950803500b00001e0180c150138001d542c010b074070145e04540170360300721080c80304007041c00c4004c040c803500142282d51100c40c00f18201070b894060394254011a20380b007a015454080815074108951a440c61164000f086030000c82b8402d80c0b1003a0429000340e0300303000880e043c0341c001a0343d600440b001d80c0002c0c2806008502800c00050482080b4003a000070460030f005511451010700000c2c0f04081003036030319a0311044038507101800601501451054603011021864000b0002d241c1d0000c5c0f0b4014200c1da80100102500001921380c440c0032034115a40003045600101c034107403070b42c01e4005c000520100340c1703000321a89a8405070807a60316a084 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 719743066 1250 719741816 719741819
    0xa0606030209130203070b071103010203010f030b102303010b0d2d08030a1107050607020d03060603050f040602160807060f110708030c0703110d030e060709030305070204050c0909041b 81
    0x4800c0400b0a140e406501644400b41c10440040f1f400010205d05000c0e160003903003041080000b07800c1e03a00070b070b005125101034a501031040c01001044141c00040f8120300d002c41c0b80ca01411100c50f84903003292a01c8515140200c0095070f142034025804015004218208242e0720340b078004500180c20900c0300c2d592031409041031294401130284100140c00070784d01c600f156155070b5002e0261412800041200c2001d0020900041003044000e024040381c0c2c01500c01d10b02403010040032078401d5444102094186410721002000340713201140c11a422031340150391042c0300c840ca881080c2c01e00310f009041350000155401403015a0380300e02d4080740c0800e400c0c0013030b04038104041002d00950b540a400c00d181000401c11092241c4010424203229050802030300c080e60318000c4c01c2a004020b06000311f51101c00340400c10320140304082d844100d43c01c228441d1070642c0c40c000c040380640a0024080c1c0d44d06c030040f40e8050309980c01e81c1d4840b07038004c0907000d040c942440c0c0b812622892040f48013142c000c4040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 719744316 1250 719743066 719743081
    0x20d20011b021c050405090703110408060a0c0c020f0d03030e030a21022511180403020606041505060d020f1903152d081209031507081f080a0606030209 67
    0x703200c074101496913134881c10301d41403c0c01c00c8842500a810102416a9110000e0103d104000a00020301c10f1101418143c0740011500040e11400020b4008128034081060010381da004075415200e4019204905100020314007a8001c020301075005400b440080781c1050ad10340c0c480c0948840300180e60008070491a42c20520081c0e0003400b1004c00540d1229184000d5142041c1e410358205016820b512224003404021903401c84d07025a40e0344020940b80108420702d034041200300e41050080e1001c010651602426010b607010301e028071072262100107040320710740b00550181c69110f100c1c0203440360742d0744040001c0402d400341c030941c4402281c100b000303100c400c1c4010902d100888002c5943d660050101e14091141a41c8004140540c04030003130780802c440004010000b2807048030503101e0356549040b410180781c04145412000e5070400e400070062040d03403103500603400004009258080d03036101c41030494001000d0b00090708522520620340706010f2150003000450340281c0343c0d600592520078 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 719745566 1250 719744316 719744353
    0x2060d1505030f1504081e04030201180e0a1d1605091510030902010519050903101b0f09150518120a1103121305030c10020d20011b02 59
    0x10034003c00350800201c900d6000e00700d116803a4001d00c2215514900001c0105034600c03d09070041d156810100454107000715600600c4280c1d5003002040c030306240a01c0c0c85c100000750240104105800350301c0304000c40c044c03e0000040854003600310b0903a04c2e0032621400388140e4580600c542841042d4582c041020744040000c44c0c00341d042c01038600c080703111801e0000c1e00507280d003901c1241080710400c40c10614a200d041d40764003800c82d0b6036a2076610384000041603d08054201900c0205160595515980c0c1e0401d22100304442030382065480340d05000c101340c0c5c030300c00254001580030a100302055405548030005081640c0d1260351401c0054034001409a10606901400310f00d80c0100740d12000300c1c4000700c0c210400000241201e1000740d60751100c246030740100200610300c9c1d140d003c1c05e100a140a010b00c03240120281c03452000100307131400003550785854251f20000d000f40c0720362200201410081c08004035150318024800c01d0f120703160030303c01c901c540307800440140a026450120541d100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 719746816 1250 719745566 719745583
    0x210c0d0302121e0315040e010e031e04030b0c0706050a06051c051f0b10020a08030a020d0f0c0507050705090c071b050a031a060405040c030303020702040902060d150503 74
    0x103a000b040c50108408001105074042202e10081901907402c01d20a00c0c000402548100400c610507100da4400005000507a440003040b46110303410403c50440790000003082c0c0d0480c501a8120740040e4030300e81507070203052107260000b80602c041c44c020060147d0b8510000c0203020300c162402c201c540d480d031506204440c1c10340500d951004000840da800300300b01168400800d405a01a070301894980101d11101d011304004640c0c02a88031044542d003450b02507510b00824034680080c244410307860380c940c01a444000d121760901a404245407008000b65840180b146010a00030014514100c03005442900000e008440780d04c078020380802c2600303000e49400e0140b400903540e01c0c14513000395220b4920716100c02c03060b40e248104600004040d901c2c010050000c501400e11800c030880d005400c0c07014010000c0019000314140000e010010702c000030300f01d00f200d41526005840d40414030008003d40074881000c1c1d48548007143d42e541e4400304c0e5020351480e24801071140c1400d940da106054403455803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 719748066 1250 719746816 719746823
    0xa031413030320191506050108010320030a0c05040f0c02060703020a0c080304030f090902030405030906160606080129030705090705070b0a0501050a0b0c07060f0e210c0d 75
    0x1114010400240151000300620904404848a00c0725031000d45240504c48001032030300d03101c2550403206101e58990104401404007005200050074100040d12031b02061000500300301400517024210003001c00c013400342040003815220740a0241c240580e05130b070607009082c0300340c0c41c1c81940c4c040d60700319116150141100d9000717421143d0781c0d080705034002e4029000034000d00c18a8401a4000b5111100039445940300317886140d00c0342602d680003040c030b5515401c6105050700c100184808100b000095540000c0c044645d141d540c0442e0000056005160500800c06420180c1c003040c12481034100c18120021941c0d4010811602004241c81c040031805054150700540014032036418030241480d404070007814424542840746d40c8640180d0000c841004802e42d0b220018012442d20b2440350005200da4074110b800d00c01e1080d180d988801136807041c9000d028080844101041c0140882e00008100404890100e65000c00e01820360b4000d800582d064054100c3d110201d24010441c5030702c4542 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 719749316 1250 719748066 719748097
    0x3030e0d0f0503150a1205190c05061804360215300619060f1d030d020105010e0604020304210e040606111c14130e090a0314 55
    0x1c64410540315584042c058030f41c081a4480303055074030f80b141201c0d90300078403c1424451444040307052480c10103011440340c060841000c0e60000c045031800e140c0605559007101e440340c0e00c44502d651640c00108505035150014203003a4214041c0e14888000840e031840f28400e400d0800c01d00700340c4601c082110500039884810b261010321914900ba0240c100e074001000c254107074402628918462144404002001000680c01c00c0f003141820740c3c000c810010f0b07801c556044182020805000500c0070030000d010880405419246121000a091414000502a504400301080c4000c1c0030309400d0182d41d00408910380403900d83e05182c42180d01c11508105800350716a00a0007a0355040c2c50307180b0708010480b046c1c0689080c2c5c0e84a2043c1e900418094480d00b0001840e01c144a050009a20007100054050402024016000340500401d408005411580c0b000c170640d100c0510040c40d0000d81d80c7c1000803040003d003850024181010074000e4031245001002a071a800b55845a60741080c030501 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 719750566 1250 719749316 719749337
    0x1008061302250f0515010312030e011509020703031109010509011209060f021b0c0112230a0c08010b090f040f0e2d010b0901141207060201050403030e0d 67
    0x4103554003420107030410340809030308404402000380c41c4201400c425030b00100704030858002c11500308840545004640000641580345850354100b0462041ca40d0b014551110840403400200703602070081c00101040c0d0180c8151102a400001d401c4108214003007481d14003401e020041c40815141c15860581d242807a08441200444017802c218007c100b005071503611900015850b401240209890f03410b0060706d0b42c00c84843c0d080ca040490007032002d203030802180b19803a40d0784962803024a0300c6252010950704050100700141140038400d8401c401da8100600a9140040d048500c122180d540d82d5072890b42c0740c03030017001181b01c0d40d002241d000c0644032946c600307400d02e07401030900030b988e040340083c03100c160880070350a000b2040c078254695421103e00b10041e08019001c1c0a100f60200e000300800c0003640c0103c1c2c075003541800356410040082e4103c42c039681d14100310300009042d400907910400c1e620030300a40038213000e0b034044011a0506140e00750005000030803001303d2000303980d2404a81c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 719751816 1250 719750566 719750599
    0x1002011d0f07030212150a0b04050106030902010903061104030f0b010e01151d04020d1e1d070509060409050706032f0307181d060a0b0a02060a111207020c100806 71
    0x4144000300d0005d540034a42d4440d40c0d1840b00194907110b46c9121801140400d4a0340400c000c455058204030113242c0750614420151340e00001c0e42e015a680113100081c202801034585c4100c2c0119840288034103800c03210350042160104607281200c0b4a5a01045103980710250707034160009500b4000e0001c1c010205100342c21404021070300345800003400c0140b030b0071100c07100c65084e15240a807500d110308103e044107801d02213602c108c8841401d034014041d560703087c41c201241c50300302d10b00c505886000744002040803a0384551081032016403080456009940e0781601801600102e15112806c0b4050051180380089200c18080280c103004040e0b840c507134545405075040d0b0040700341420101c0c0307224000714041c404284214040720480c01440b035145808020043c4105294010800303400003440000c05043d000035074960098108103001c10051622100e0041c0d60146882100d01c9240320803c1c455800c0d000f0980091500041e41c06582c03140d650001a100f0078003c1d550250403082c00104050072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 719753066 1250 719751816 719751829
    0x8010c030e0607031a06031f0501020609100902130516030b040c090509090c090910050606070c0302100c051b0906031506100302040321261b091002011d0f070302 71
    0x91080a004281c030703110790310001c60429001203231140284401111900500500710383d142005000902c0204000d00e4000405522001298014802180c03114440b01c01c541d94900c4005041c4d221420400103803078000c00a01003540500c020401280c9426280f41c8641018001c4d05800200d0b5143c0b040100d1420050044400b00104210407030701400c20326014996420740c02500411042c0010101901042013010444101404462142100b00310100028402250000849404941d0444840c03084001034900380b42c4002c000b040f9010b40e19030764500740c2c0ea0601040312401e082d649222180e442e9014150f840741c0041401c00e9460410700080c1e202d01e8071070300c0c1c1000c5d41c560b4a0701508196480d5580403443c07510907100ca41900b002c080409a51350300000c100c0c084211901d8a12045c140310f001340464010180010a008200007100d034500302c122130403102040000b0f004403041305181c0d00004e000f40540500001c694049440120011030b00058500717246183c0c0014040480c51942002079 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 719754316 1250 719753066 719753081
    0x20906010c06090b010f05010c052508010e031804200a030f0204030b01060806011d06090a03121d040209030c09130f21090b03071206150908010c030e060703 69
    0x104001da606000000b545409840c10a034861907440044d5410401e580114800b1500b0041c10020ba040d402c0f000726100141e405496a1440c03151040c0c0303031850300481c49000300c0d508921030795801c1c5210016203510000c020041400a40c0c201c00d0912510810001920b290307804e81d1008045054060030440e03998401001c45008505000500d0007220b015901a6003242d80141d0341d60803558010411640c20201c000c1d0300138024a031040d4881ea91030540340c052411006428080d031070115080d04c5a0f01e43c2100784001e190030601c00d1b200e08882a80040500079222441c0d03141140f5a001d4449038200303802034a051100c020041c02048800c0710600161101c028000412010442003001c00314070b10b4148400c40b18098683c4000ea0004600c110b0064000065103000f0400e6040382008a010f00000740d940080d4070f0b103015840c3e000e85c082c2c048003a250383e40000900b40348031040044100d03000000302007200c0c0e1800081c0500b08401e1002da00b01d400d40c0c0401085070700501e0008207003034071070b40c0f2111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 719755566 1250 719754316 719754319
    0x9050c12190e030d0e06130f05030d09080a02010632130603030507030810050a0605090315070309050c060310032a0b0c1c14070303110c01150602030301030f020906 72
    0x4542050149200302520604202d11001d508002400d242922050142c2c08002c0c02410080c0100d06143c2d00c0401c8882c0385d018003074120f40c07607181e03540108203080c412540c40040f41581441007852a040209003907101c03891000c050361800c8d400007000e40d0384114a480714102c211804c0c040c80101d000803100d0a4010f5009503020b40d694a1202e518103142c400c0101842c001c0d034800751650042d142c0580a0b400160405002040190041105a54415585065a03d140b070400d40f1200b940740800d01c2c0000c000c0c5036801c1c1543c20310400918550592000316181c0c000c50849003035285060030300041c1e10068603118000520801c00f0b0000c5101c00c00d00c1403030606806413045c41100d960540010034842c0e50010f015103040000c040b01c20311002c1054450720344268500a10842100001030080100300c01c03124429100401e200741410302a5111040c2c10703111800c2d0320341d50302c020841d0b1402001c0540c8031441001c015007011070600c2c40001500c1c140c070380c0024010380c0e19500d40c0821414440c01001203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 719756816 1250 719755566 719755591
    0x61803240b060c1c0302030108070b0d140a1a0402130902030c0c07090c140a0c0b061206010b030a110c0a0201030f0221040507050402090d0f060902030a08030405060109050c12 77
    0x30007203501c510006100064014000d4180c1d441446444030b04d081c40604201c0800d40140014000b4440100e450400c42d00c41101940d584d130001c80a01001d002152201a00150910100101c1d0021500000034141300c0b810020203910507e01040200e001e81d101074017800c0807809080c4140010313035000b1500700f194940c9a0742015082c40c8180d1801d4115081440b00645404c1c0035141907802961451050000b103104505110044a008040000484018011500c81004150035440d1a503641c0020b124a82c1074441c1076031111402550740e802540d0700044140b81c2102011244000010f0750a00b401c0480501210340b21600110090040c5900074540203500b0042208000c3ca0041d81e07180c0c0d01d5040c0c104001c50300d0310b8100141408401ea021303c0c0141c0c010091004980d98900c100090301d0303400610041d1944590070000d0051004c03120094061040468031014092800e024510461041c01100c032144e80b00c01c0304000361941076030201604401404882182c1208461030750b07100802900300c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 719758066 1250 719756816 719756831
    0xc080f39030714040b1518010909090f020f010e03070e04080f16170a0e01080c0c0613061821030e030a051804021305100e1906180324 59
    0x41c1c00c11200f40d021825815104a010000c0d06080c040c400020500701d03000b01d03000340f00d20328480251040c05100b03401c50100e107a00d180141c0c080d003801400307001c0d80202002a01d1f900c2c40c0010420307210078030581c481c5424080c1c1913015807084040742e00400300036010b8081a894001044070400300540200d800750310a101800058130319002520b14460000c0a10780c099440e400c05030700d0080e00425070304a84404000152039182c01c280c0301c142000080c60078100ca079940304841096030042180244960007403000b03000c18404074002480c40f807030003038508204441700018100c590810201d0024402e440310900354046100740d1300c07554060313107076410041004444000503d0a56106030f00e0480410001310701d240396207501c4a48061040700c02e483c114581039025009099007034a03482007a00c5100312880541d0741178403e140e0851400c8002e08861160001106444c80311101400380d000099810403820040c0145400013804a0f50802e006110b07803098080b5085220025981c0c503490740741c85021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 719759316 1250 719758066 719758069
    0x10b1e1e040c0f110601080d0c0507050d0b07080c0c0601030f0f020406080d1d03060a0e030f071a07030902010e0105090f0306010e040b0c04060e101b0c080f39 70
    0xd2030010020b40e50382d0340300e070101c04030b001d800044900c0c40c40b10b556211000600c400c3d440001e00c00810b125505040c0c500c81810300d0b10303d20709281500604e4200b01034202c0d80d0300300000b13902c41900030141038403040110350703409001001e0b074011031080560a074024401000422030050000c07846030b00800700d125001c1c0702da0300881d05442d419404861107074494180c403503034554801da09141c021300703040844084854900c0040c0d510039003e0042080e1658541c003e240032b000400031030312484020284a40c450581d410043e0110454044121030550a0000218920311a04c64900c47d07aa05846080c68410458011034107504203800860b0410900f4030f1854640e6001c001490082c405041c41d0003d80c0b4241c0740c1704200719406040f610690100380300a2181513080701c03602c1a81d80c000d40d5140d0000f915003500715040251500001c481c81d9511004806000815200d101550b272940110b9411a400d000036030b54035008984040f145212044009142c092803c1c15903050814409948281c01050300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 719760566 1250 719759316 719759321
    0x4110402070311011821020a14070302100503010501120902040b0d06051e061c030e040218030c06030105011b050709110301030c050a050d14012c010b1e1e04 69
    0x60055012902c0f0f060302c000b03518024024002e150a915058080c10040d542c0c40d07402c5e40e241655941c0d410b1505203040c0240910810000094a070829020718108002d50509515101e0f2800180d0082c041c0d0500503035094000c00489048460607034030040d201c90701c3c01c842e0b801092001000c990142d12084004183d6940c522001705107030103038030002000d003003250400745400703d07803c0001c5942500c001040207958608103542c2c2c0e020302ca00340403021f2004a00c0c049480b414100b108652052001c140380000300c0c2030b071880710121002941250200701c404002c10089000c00d100d9503000074803030046446031f00110072051051030300c1407040782c0c3c481e91a000da0005443c0c050b0040800d420011004005102128152000600c0140d40340e4441c2c0342000b001c06e0440004000c05403a0911501d484c0c001c41c0b000b5404034201c1100a0040d49800b09640300710403407001120300511141d804d1095507115460300302004001050341d103502109210b024024031040140c030099100f0840260200c80b5455151030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 719761816 1250 719760566 719760577
    0x70305160501090e010e07050d0b09070509030610080304150c3c03020c01030c1806050414010e1305091204090603061407083c011401180e04110402 65
    0xa10203a1410800014200c0059522551000700e05500400c0107841c00880160002d80358a4015501d01c110309003240646a240c51302500702041604100041d503110015040c480812401c1e506284c584000d96440e20485002d00305403034208020400a945584100780301000c842c0c10500002034442d2100c0b0303d44605d991104842040e4108820502200c10400c080314104c0c2c48007001c16800c45c0d0f18003e50310010010158145a0359517519030240e402201c11640c013000304009071388901d440c0c1c0c000401c1c070741162060880d0030010b8060f01a80d076004200b4605d1740740e00078100420701e5103801581409040d0160289040b402480f2003026404d01c100000c002829107900c000c6103080c41c500d40402111600310400c03544032101d80500003902d910014068000403840c0b03107200c1c04015030150810000701d104040181820030404c04560881040190741210810118500c40c2c03c2c07010010f40d90602c080305074000c40124500c0034000484090942600507010320310743d100a541c101d010400303d0f80308 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 719763066 1250 719761816 719761843
    0x27010f0212011706040f030302070c05030109140610030302100914160305060c03040213270339120917030c07060e0a180e0d17010e010308030c030603070305 69
    0x41e040140070746082080c0d03d00b000310040005000610701600d440e20440c2154000604041c3c000640c1c3c0140000715030343c400503100c010001c014440a031b24049102600244c5c4100c56030281c400044c020040c502000d108403038154001c0c040301030200017000010984440b003191042c44040780c3c0154240204001c154808070114141040c0b8210b050243c07030400d0007400f14aa07880c08208110050303c1f9990150342e544042203000c2104154500280040c03540c0c0221900f010070400601c40c10b165006940d01e00304d0302150f040d26400e100c0307030098480e44601c14026980854200d0010b100141440f0903204610506143c1a5007031520b50a44c200340391034040c1305000c80c1c0c3c000300c0d045094104c144244001800d4a00f080b42d02070b902500442c070702641034403603081c030b424850b080040c40640316000056411020003e555071032040282c050a030b1103002d41541045c500c460000304040c0c10700760300c0300d041c1c98209110754156035903500305102c603500c0184015054001c221700080000c2d000c224a0090020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 719764316 1250 719763066 719763097
    0x6050108061b04051e0d0b07030f18082d0301181a0a0b0702030106030206130e0c0703050409090f0506012301020111040b0702120a0308160827010f02 66
    0x500c1a10710300206440b8803101d220702c074100010051941c450f01c00c00c4052202100d40390b031034559580011000c80c09004054211071441c42001291079144c1c1c4800b140103003200003045801c00e000c20201148600b000018004c400c10011041200301103da140303241500002d04004292a841110500780c101380c0c8180201898000c030540c80040c0340c0100030155448880c0b5021902c1a0340008081840300d10802c0f0707040c0f40c00580f03003065460a42161014540107800c1903a6a800c00b12400b4035400035201e980c902c28080b4011481588400084806aa42681e04c103814982045600d20003460b102c2411103081a038011860b0028500f40705c3e8a0082c5000a02c00408100703201341c1c0c10003556030754540b5045900d40822410700908100640e001d8444500c8007944035149440071030854084e10244c0d07007030781c81480301d48010190310142e03c0d8414040c103044c03400c40001c03912054402040640e031280c100350f070160518151005010000713102803003817400480c50150200440040781e1120000d044d0900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 719765566 1250 719764316 719764321
    0x60b0f0304050a060e101b090e090c06040308040914010f03120915020c0f01021203150a08070b0306040f0b060316051303030905030c0d1208061305130b09031c0b04090605010806 78
    0x507820f00c10380c05c0812030400300f020607c6200500500400c014040ca2000314100e03070100300d840c4000c11144050503809000540e6a41c2c5a080508130394010784200802903082c0000721040198014043d0704945000c0003900407a4116501d81c10540e08001d40001007105034240001d086d0380488400c2d00300151a009409061005d02c1804141c9a00407040c0c0d0565202c044c1107054034400c1000c80303510084107401030200c0c895110010b0710f9030072075601513900d51040b003c01194480016006502817901205c08004c002c8854420909a40100c09101c1e4410720a0000035040c02c01e02800200c0304049140a03450880e0b4a552140c51000c180c01c16000660074040134401da042c1004041380817241151085800e9440750b94005000b1094400c060401c504c0e10040b8803e80c0b030b0b032034040041030402c060a000a00d044011084503294201080d03400101c082e0100300045404812250007481e5581d83e105021a2486420060300081208a4115a6500d50a4007141452203114041c1c1104000303041c0340e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 719766816 1250 719765566 719765593
    0x230303091e0405060f0f0402071106070507060201060e040215090a030212030915120423011b030506100f14090907020105180106050d030e04020c12130801060b0f0304050a060e 77
    0x2c3c1c4009213494050140515080c220b076681d800c1d103c2495000b01d40c096523450310740c5003200780742400560700c40c2c0019010400030104200890000147e4074594000c112007070b601d81d40101001c1c42070300c001c0d4014203a503c1460690030310400400400401400348d51a050762a40490a415030100f0003094075003020403559014a0044802030074601c0000d221b5041000500142c00d0303982014000518208099810b810401503d032028010401020001c22515401d01e80e0700e49290320600300d0000180c54640028614603004001c010b81210955412504c22043c001c19507c040b00024009003d000600c6222410741d20240000d104801550022a541c20030800b0310a040d0f0b100c1c4185021a410628240320a444140c41e580c54142c06d45003c01c22054807201040080c410304118060600541c01d00044180419004082c1090400e21100ca0b0302d5441c0d034002d08aa1281c024a40122020045851807015041c081d541003402031050310b15049081c0d44803403c64190980d1720740140c011440c04800f2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 719768066 1250 719766816 719766821
    0x1030905031b2415040b220f240303030c141c050601080c03070309140f0703030206070504060518011107180b180403140408150916230303091e04 64
    0xf2104040c01c86050038280100a03c0015003101d0724012582d075480c03240240e4a040325090640e20300c244016a2030300500044016044000d85245050706080d0008600075000584403190302d00d8101820450782556021006000b030402c41d0410410f00210880b0800d003443c1c000d001d01c0070b00030494960300740217024080c26904018aa14180028002040320f040303504412030345e01031003501c0d00250080d2130785410220342d10707e840e08030b41714452400e000e982c001e4005000300590f8083c2d001c0711040d5456400c121854400e902801c000200d048c400604c502c1e1820741001c4450405060000150307403000b4400340f0b41038082e4032400a60681076400c184841241c4180c0b12010301c02c3e03410005858940c0d44444210034050300080800c468221040151880310302a50007070203501d03095807680ea554503c00c06c40e210060384c0800c03a03805550180888400e902643c0000c6a028017448907100b0f245196140340d44c43c8000d0b60342c0e01808108505412070790b886401c0001d11408140072000b614241052004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 719769316 1250 719768066 719768113
    0x110c06041a0601020a1401060f03061401091a09090f0d05030118061401120f020c010e0c04090309051302040b0a050c0d1d120304090204260c09040201030905031b 71
    0x51003040c84240020390344c2c04070b0801005a0410f0010030b9070b50038091302500624141d0300100d41d11820b06008030030007000d900940a0003120b00041002642c0742c0d24120100c1d82c0341c2114084070707444042d0844007810001009607001c080301041d030701400000d1a503c0c3c24100591401400a10000b0052040048402003180c5448055604020752828080c85410f4140b5103010030341808a410035826200d0950b400800020540c0607055498080c16810703e4068150b02e03148503400e018040c0300c1c1c003142c1403521070803800c1509643e4006210b46000244200441c803200c16081c001d408000c0032603100540d00080c44040c2c0036646d62030f0340360402100d1908000c0100544001c000d001c6035407080e042c9040c00f82d0001c4040441d40646008004005184dd611903540140500e900100d0b00046143d050110103100f16030b0020f49022b031145480c00b454840c24065400341d80b01e010b480105015501c6a03101c0210207200308212840c04009003403448030444004402e1a00d40d205e10040015240740c0c2b80040e8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 719770566 1250 719769316 719769353
    0x309120c03020709110d0c0503070207211e0f0f21170601020313150305060306040b04030309031b2411090d02030703080409020909010b04080607030c03110c0604 71
    0x2a298034950340c0080d200c0c24a03200d4120000e494028443c50840c00704200c5000c1003d01104225150300c840021748103401c100c510740054017440c40c3c0051240d4010004554000301d40d010b81104070995960141c501c07021a90000c0380444406d000d8001071090703c07802c4d00003070240d588036408000f40d1400c1180141e41c55046090007002e0707107081c40c0301d0b50032a03282241141c0000011016070368010040b80f0394003c400075103001c20031440002902070b903580204000306140d03503170911072580c5d40018169984c4080c5c0e40100070706000d000090202c1d1083d4007a0f24014424075100c2640070706001c103240c010f140000c05a42d40d00041344400e451503452a2403c04500e40784400303000061500c0380d02450382c0144450603015403101c60325181150b4007405080051039100400b2038603107131522030000003500301c2c8415034080c0850740300208000c003617901600c1c100c44110b401041141e036456000c0303000c1c128400349442816151004072844991000150088122a000078002e510340f9040c040900c124205180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 719771816 1250 719770566 719770577
    0x40b030906240108040209090f2a060f04030807031e08090d020105060307120602040b0c030d1802131505030303070507150e03031b13060e03010515011d010e03010507030912 76
    0xb0105a40c03c003c05562003501140c03040910390ba154070030307400e001c1548913040e414000c800d9644003c80c588a1500110b02c0039a107980c0152142d441409241d2082d203004d4008044244002c01c00070315200d00803d200d80c0310b0314091044c00c849001181190356003400b9000881c290b03a04001c1b003407400b0030410300000c00901c02030180313050100100707807152060300075000c032000c5042411040c0401d43d0112001400e40c010040e82e1492007030050f94880d0007203204201074500788250210811404030614a10039001000d900070900e11443c40c41c014140580320341d803946030151000805940c01d10246120300c140342c842c1d907641d0071070349840d010221110b484a2030261503d02d0340a60320200100fa240e00032108841c0300a601540f54400c2030038007824481c0f1200e5070946a010542c0c90780400888803801065000744aa80c841100040c1c51101c0c2d503450900045966095408401c0146200b0041000c181020a5a214980e000c07900b500d00c01c0b070b60000400d490700c000b102048203001025200025030b207410b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 719773066 1250 719771816 719771881
    0x60c02040524040b1f03052d0c030601031401061d0a08120c070305060403210b0d24090f0215070f06020304020f0d06150501090f1208040b030906 64
    0x42d00c0380c1a4812424040e80c1d55807404582515807900381a50210841d100110904106000130041c0c03038201c486a145d2144404600c401071594021002d0329600b1110392039460791104084503107030300f00400c60350416031101c0401250003c1300551502a0441d6520000104000842c450045c0a40c00c0824001c00750418100032112012031a08428180c08890381c0d03075200c0141025203804520741001c3c100d409400240420990400301038110750410101540032f104c04401010200c1701c14000e126007007140c010f4440300140001440e48000301c91040750f240524420b85070b072030480d100703000c1c215509040c1000c810154680285a04500d600059105103001800d98070040d070648101c4c8e0040081e500440410115601c05000036089940500005c0c0c10144506005e0042c20300000c10390a9100e0142011a66500c0b0711f9500c010744000a1505002601e003c2068030101208413041d104050240400f064964400c4000e40c00782004000409890818000d10085200f004442a031170500b000713032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 719774316 1250 719773066 719773111
    0x1e030315010543031b020406030803010e043e0a08011a03070b090120030d0e030703080a05100501050c01060504090c090b100e0409050f0627071a0f13060c020405 71
    0x205444080003684142280d85d07500d101140c0035007402c4e007000302001000b1002181024034801d030a44100d005144040240c2c40f10b059107800444a0945415400400d4841d600180702c0c4002030780300d000f800703041c60242c1a59003083ea421a80c07068820080d030040b20320700b103002d413a003000964054a98008014641001ca9001a0440e002203250b856580d40140e03443c100e09009000340c0d1320961010806002e40310000841e603480703504c0b0743c42c1100030803402d002041000d03d0910a00c2c2c4610a08a80c0c81c4000c3e04240042d120350b0012640b42d4160340d2a02808603107a220f901825918520a944103c5507904010000064a00c0d40c00900d01510844902c0e06100790b229a2543c01c148040d500014004520305045041c591251881000c0707105410a0080d100702e1034a4207004507007003191213250300500c44030f4661509103900c5510f85084a1051054051701c44000811000c071894100500c0c06201c2c10b144804030a8991002020400f500e85440650800e400b07160340c08000e002c0c0001700d003501c205 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 719775566 1250 719774316 719774327
    0x20a09051005040308122208030c1605010603240e072304060e0a0b0f03030304121110060e010e040c090c0201200a021e03031501054303 60
    0x410a0311840107041641642030048044401950b0092034003640d40c1c542c050349265119041c0d9460601c1c101820f00b0b4001030003200b00514540e40e000b40031a207191900140840c081e04503401280549a01e0346030b1200080b424403c410041d445a900754226641030007032030f562280c0100750803110360305101b40e52140030300115440091b01c803491000c01c0c00c10410304c50f030359016819488494202d8504800803c10240c09070081e8420455020b041c085d0304000f80c04d015481c103030800740780d030148d00500225001402c2c1c80c0200c4003036180d80c607201c1004014110094645500d0680728440a6078880b010f1101c51840c021881c05086a8002d108190801d9a02c00300800c21501c0751600ba03607078800e11504d120340300303400001c5a48900d0072883e0612204d50304100c15030740f0040c03035103000d44588810190700c10003820901c1000e0300c1e0300740650b04546e00c000c82d60202d04003c41243d810840d0803c01c81002c900312989011660440300d16240c00d407890a00c541c083d1280040c0c0d40b12010741842c1d40000040d5001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 719776816 1250 719775566 719775569
    0xc0f0f161409100e0f040c060504030503120604181b091b210207030306080d230304030302040902030c030723072d0b0a11040e01050607140d0c0c09020a09 68
    0x40c0d039000c401c0e540e84001c400c50302c2c3d0700740c02c0038191442e01414000601c032108443c1d0b0046002d1420005496035886007aa218420ba10000309660024815030300001c0c81f5039546036100c60040c1002c0345a000d14629090014a11803040351072081e041460300c4101402c5c100d020262401076410001e2070810085e40b440400b02042c4c1c8001c001095041c0e480300f00f02080c40040c3e4003d0103c0640d154402450094060700b02070141034014400c54400703a01040c419644070512004900e194100f1b1001085001020340c8020000d606240d020040005d02d0b60442c80250301c208040c1d0440b60f101d00b45114010010081c089410380c03a400c02c140c607001142240e4040b100d50b240e102d1520403580103071845003d4403180203050f131062441c110200030144581421500e10442c145502004408031650900080c2e00a5019084e01c94820304014081030030420000c10700e1600500d0141503510301e08801c40d2030220012452000540025030403410444003440510143c400c42109509044240000400e02c214070b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 719778066 1250 719776816 719776819
    0x120114060f030405010b1c0201030e060c041205010204081914010515010c1a04030903030f02070312210e010b040f0b1305180d02012012040201140c0f0f1614 69
    0x1203004c00c070742548003506922028101c041c07100200c406000d11a2440c03c81a804a828125002c45032480070a1280c816980052228189410007440413021103129038200c0e060766007080081480c010400518900b20104842c00181711414604007000700c50b880300c41c140b140e04200c04c2c04004aa0140040c47d81c1e1000e180070440780401c6c1c01c4c10034001c002010904904d03a508cc0a00080c140c0c004c03204010740e8020340301e10042e40c9040d10126601c000c144400741c40c2240c0b1a0000c0d09052244510001a11f2a2040d2240d482c0010342d10360121034101c49504030030f03992090741c2d10941c14280141d20034103500e020100103501202c4046440401c402c441c101c840c55540d8001500c2d404a0454224042410b60880f4141d40c5a2a170180c02001ea40c02090b0400b004418404c642d82d225604030f90b0351200040a81c0b40585603580156408541a0442081c51005001000c14004c2c10810207608849140c003c205180c1c030b1007483c504101d000382c0b0054054801c030f2418000c0d5a194041e88030440350 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 719779316 1250 719778066 719778097
    0x1704031d0d060207140d020a0309330c05160501140c12031005040506090106020a14010f0f0204030c090203041a0a091406060a0b030907060305040c09060b12011406 72
    0x25000042400c41807100041440788080b8076802802004850340d9403080da00011a07060001c1c28006036a5180500d00c01400240c0b206402c1c4401d0710f260540c4007521100302c2c4c01f44414030f2440b00b1030100288944d2488001008440344009020003007000c4100f03050541000940030b0b09140000788007a0111010b288618400102100e501604201c941c2145102d100005d44a003001e0881140703d50091054034415400d083c00310b0b00d5813030100768050480c2c1a90f0002c1078594015500d01c4849905110b001800c0e540c2c0e007101c4203221140b8010458003e0101c0c60059031681946032240a000264000b1825503205000f01300011f40c032624912440c3c4854203c5032010340c0c07440040d030013409002c60000c180346003020294000ca503000924500400d822030302840302c2e64489106103698001210508002d6100100400c100c50081c1c0c4043d4100d8060310350840900e44980070842541c1143d40080325032180010344501000c02c40d030415026003517a0f15225111500500003418901588908200400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 719780566 1250 719779316 719779367
    0xf06020d1409031204150224060f1228020120010908070803010303110604150e0f0303090f0d090503060a0b040e0f030418020403121115090607170403 66
    0x1000d610941d24002d00041c00c071106100c3c0782c0c1203c42d0b9074000d03111b414030100803000500025400422400f2404138030b00d207040d02d9290741c850880080c0078043c2500c1d80105104030b460299403a0941c000403c0310703000006108500000700007024500400200080074100342c0e00740d00c0140c5e40561500300c0d03410901c4031044111000080035005082d83d940061020300001120010041c00c1005103040743c1c02616100c01c400000e851460f2944802c5900810b0203201c81050803a840140c1e1001c8240b4181b002142c0500e461390710000d1030340d4019a03042010340e04c04404210440010401ca0020304100c6ca49840c101c0c0c42c110100340e0b1001d010b0100e06c080d0381c65040c001c40a840e26032002803203c6100081b030748a408095071103034407035000b07007c2d90241d201071200b0720588160034000c03501103d40c415480342c00800d000208036844103840e2014046402400728100048030501d100034000e0444102508240c02c0c416005030101f415501c03180500c102580400000c2a000007100140042c03070254200080f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 719781816 1250 719780566 719780597
    0xf0316090203180106120210032d0b06071a010b0c061b09040207031701050609030a06020a02010b0d03090f2c0604020d0c03021309050f0406020c07051c020103060f06020d 75
    0x107181e8203c248500d44c41d040000608170030b02021400518003d413295151409045000c400f992843c61814483e00fa064160f8600c880030940d15065101400c00c00091514141c030001c0c85c1d603070141c1c00c05d44c4c03420600c450801641e44004106401443c0c1c803d03296142c154091292608c07005d0041561102e000c00b0401800c6070800c0c00f00315103609030300601c1196144002d00d4081c20411220318060281c484040010850b070a02703c04071902040014003c0c00c10302c404e95650000f0f50300c120101c604554985c034000c65079807111100d49503010311030745801140c942402150808546540d004207001421041a0011101c107405014442680504d043d20590b99080100c0c0183c0300d900f405403241403822007416081940740e4050841d81300303190032515880d6510114501a960142d500004a00c05000810009201c1c1c0c0d0060142c03200e803000b81d900d0709968100141c4800c101e40c0c003c07403410301c02c0c6030403c00315a418461207001d03040411040c03003a142401c0300207588a4481d4080750a010041c104041007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 719783066 1250 719781816 719781841
    0xb070e06040303180e060a0311192603030c03010909170301061d1e100c08120601030c0206010303020d050703050f0f041806030203060714070b040308060f0316090203 73
    0x681000390003569540e68030b00c2c009001c0f98a188800800f5249072801140320450080c034640681c00c0286900d00580c1903032510301140209041141d44207000d240c2e14030150340b1050f4014020804d04184126004c003092007402135a00c8a01c61980c980c0040007000031105050055a066801d045400a20503100740380040020b0001d03004942d43c1c0f0004000050101e0307000c40c01301c2a41c0d4030401d0340c00c0715029003c18844d0b007220705a61216504580d20b0b0000440c242001c4d09001e250052030070001810030342d240d45040743c1c00200154002904401000030950f01401640030ba50007a2001700074641c90b5071402074603030b000d000c3e5000400200082e148281441403090703440c58001d000d8107a54030300c560704100b142c66000d8410511030903440e03050100070045600c01c290440f038002d0040c101319500c0300001c940c0c0c000007407064103000d54203008100102d103012100ca84924802e4581040c3c4d810440300f00604a40740da05001d201380c0c0810f288140c0c6450151036a41200c49030038000d40c60307894200c200c000c0c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 719784172 1106 719783066 719783087
    0xc0108010305030a0f0912030507060b091003060f020d022d2107031d010501140d0203030d0e0106080d051216230c0318040501090c08040b07 62
    0x1441c6010f51641e5042d05d08500d00f403a44580c43e4010400190f864035000c1c0e00003000422924100401c1d84071310324441208071261032035450402414901090603010050845484401003080d140d800d40640c1d8400c40b03446019501d03210300080388024200f50391840c14400303002d100c480200024900448000700384903000d03412180c5600e1007401c80048040c0912040540e120408cc0000c2075800440d070003030449900115241d407400c00d8440c100403401140c5849868200c11190040c1d50000031110307400c01c22140810b0300d1094080d82801040280e1215440380144502d42031101c0d40280146441148140c039005561100030b5440c4048680380c1008001c1025055070890301c07001c4411284071607641e02089864120301c60340782030031904003040ca08402e8004c00341304030390b0b4500f50246d540508102c0c00e04010701400c65074000d0031004080c2014094009120104045078882c105500 = true := by decide +kernel

theorem cover : BRFrame.Cov 719604316 719784172 := by
  have h0 := BRFrame.cov_init 719604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 719604316 ≤ n) (h2 : n < 719784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
