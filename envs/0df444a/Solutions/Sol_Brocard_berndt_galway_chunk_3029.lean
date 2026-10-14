-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3029
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:27:27.730854+00:00
-- url     : https://prove2.me/submissions/5cc4592c-0be1-4322-81a3-be7f4f18610d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 544604316 ≤ n < 544784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 544605566 1250 544604316 544604339
    0x12060108130f061d0a2906030a0b220c051201151809050a200306150d0305121003033e0c030618060a0b0108040209072313 54
    0x1c10003818140900e452400180300f9600800e450ba1606008000504004549500d4500160801c2d038a24030a081040d0f4904041100392014495180303c05000e8203100001c20354401c40e003440140101c106000185004507111250012400810400580c80c2c1031810030301c60780311b04c0c3c4c01000e00821404502d20300b10401400b41e0b400400f50b07a15080d0925241080e80028400c0c4075000f603101c9622288034001142e0104070940c13145028101d0036400d0f400c4640c21424450066145a000b40c020b0410841c0320b45a00340c0d1488881c10075140c00b282113040d80303004c440c2c91044400c9800304c2d9840c801072203600120b00c0d0048040e2031180c1c07203c0c2d000d034401d408100f0303c9070302e1011104a440c0c88601d6808030b540e4819501c3c01031500f03110440385104480000130f0f0400c481160300c076030305440c0c00903c0ba0103a9001c002442c0c10192042003082a02c285500007096800000c0010380901c40c3e5101054803588505000350000300414000c02072503045981021307403507211131031401402404070750110366902840f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 544606816 1250 544605566 544605601
    0xf070b06012307030e4b030a0b04080403080f070203010f0509071703040f0b03100e060d0803090a080301121401050601020706110f010c050c1908220503010212060108 73
    0x141c40506000ca2560200c900380181d400c49500894020180e44018200d00c4644104e4200c145403081032100750880e020412034580c82c0300e0791404070b414254a86c2d46001c2a480c0d01e42d9000038511030595150b0421038018855940002c02e43c180020703802c030a80d49000060200244200d009000740382490658805580c01628024116004141d04020740703a24000c441a40320324010590f81800c0d512a000b41141c030310b590080c0d044100000402101c0c040e144a510041c111003076003010182410070104504902c4010001c1c641c607800004548240400c004410b040d50380400401e941e50f0311400b40d176140d082501c03400c440d091180761554035241070600480b88118410f90060491078a00030041340d01c001d83e202d00c141d15002d0719a004400304000e0141c65403d280c1d81c0c031010350b0355102d011200d00e000b5151620440c08203030810143d00241045003180c0c440984d0045280181502c0d241c4c9129011866208942c190f1002a500b0741e50007000c040f59110350801d0304c2c0d4019981c1e81449501042120 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 544608066 1250 544606816 544606877
    0x31e0a0b030706030212370b03010c0c1401050403020d110c19050f0607080306090408040f0b270a0506250b0103050607020706120207030912030c0b07180e0402060f070b0601 76
    0x87c03000f120032002100f1800c41d001c07080918040385103140380011a08441c0040c81c0c102c0050454031400c0f01b0b010600301600d00308050b440080001c1d10300b60720000d4403982145800300c100300803a140300c141c42c40c017000025006000146500d004982c0d00c00342100c1542c00f4410b640c0141e1007041a030605241c080d040d42c03641500103070000d02d07640d038510820444c1500203100f1501f44c281800042020380c8060746d00005480c80c010059601c3c4003401501080c100c144c500d000c441c0709496640c0070141c03981c0d20342c80205d07601611615210210020115000c0e40c0000c840c07581c00c0f0100c5004001d000001d50001e040364010000c3c4c45040d141d000741262101320301c2c000e80700032071000401028444d40b1680285a094080d00d0404080c0e51245070ba41c0315000792101c2607000882a910000174004c0d01d846098006000b410070310110301d1400701c01048121103204044884404c840020159101d03042250351131100031390040d40d628941c0c03400300a45a400d0341e04a00141a203402d04010a09a08174052903025 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 544609316 1250 544608066 544608121
    0x90902010806040c090b21100518040c081906060503030906180607122f0a14030c0115030303110405010c02040e1507050901080c031e0a0b030706030212 67
    0x71142c081c0009010303050903442c1081840381c00098200c80f800007900e11000070341905402d120261509080c1050042c11480440303c1c1c200c010055603903014070405550300e910785050f50b280d5450400305030700c90543d80203000074014600d4900500d03643c00001d0307484501c1001c04208085c1c40f4402d1681d40d000c0d0064003a0411020400c031820714030005c3d20300803010310007890f46280c50515500d82403140c04072158913000c111114103844188005070101e20328221100420a8000e144444c0d1a07524401080d001d0a9540074941141603010107004950200360007000910071860074103046e540d450b04030f11054001a291a20406440d03080604031401c030394050b03545004014840c0c003040000c1c110903505028500c60490300c04181821540300c40d2040c00c10b41c85507030302e800c034040000d003220388004c08a841102c000c0040010301100f101b03000c1d5000381c080076080f106940d80180c0d60001c2401c107c0381c55040c803450b600014102d0b4107070010900413005002c1d204280e100c20031280c83e511103150000b044200d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 544610566 1250 544609316 544609321
    0x318060c030702062a21150a17010902030a1407060f0801031101170a0203060f01053907030f0303060503010b010c080c070b030c03011403060c0a1407060507110105010909020108 78
    0x600c24003050b6001000420502170a5409550001640f0500046404060741c0c60003490a0080448080e48003e8903046001e00c40407107c0051a02c9450b07025074a00700000d116505090f88095000441096025048524041d49401c110f0f213032440c40e0041e1030191180c0307480425518450f9914510300750302512414200d034219a100c2c031002c0d8401f07410b10304204460003a0904c0c0304048207100c0c0906000000140d4a0030998240040c4e54a41440710741484020030039204481c60035201034152207802c003584511400b030640c1500b0a04140f01c0d1181d068070458002005008108101581e118460340302080610b923100280742c2610004041a404200c1c4940c0050201d21124020f00807031103400b0544d62501e4071400802d00c503400c103454a44410710040010310002808c8880078101007011801003041c1d284c8007001880c14414800004200801046890310030408031007554900d551050060015240c000b030018819110344180d00550f40c00c3c01d00004a036026403040400c1c0075010b070b440607282e6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 544611816 1250 544610566 544610581
    0x62b030804030c0602131a040303080112060915051906060c060e250503211b0304051305151903080f07060c02161a03010522020318060c03070206 64
    0x824006000380c043c003844251550001e0110300c000c02245212001039506035090842070207141e086002d07508111501003100b840030a41000f0034904440e01025542d0f442001481c150b00a020600310042041030350071110001070385650020f83c032070003288041d1b420307280e6803821041c00c3d20190f114840100741c0c4040e0403000704445070028502e1040410072509101e0388201011540c203841001c014102d800c00101340882e240078007098903c6104011001ca9415005100240c50f214550940c0d8070011100712076421000140203807001000700510f2041c9042641a40c18080c01084036560076030b0019410310322291912000b440d0700e032403810751441c1040c3e045070394146184e804440c0303917082c9031010720540e800600300f401400500300c040d03405041085200034a6020300344031600503400c00d031004064410511000c805480c11200c04484104140302c1d50b61119584c1908001c41e188018000410010310a054080e40c01c1c41c2030f00b2108030750407540c0c1d00c041a4041d0005503951001600500e02040a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 544613066 1250 544611816 544611827
    0xc0905040213170a03080c0301050a1203120c0801031b14010c1a0c0c0607050406171512070f0b09030a022b110a060c05070302090c0d14062b03 63
    0x250a45a6007141d0860344641203900f0380f501ea6100c20805520500b201000c269001e5403040e0130400e64540303a401d5504040000702d01d002d003805941c0305841d104805c4010703d8414912042e8420b0800030130880c02c20000c40042040809000684e4007007883d030b03158030000410110310b500700c07111060349000c0a42280011104036020798020388130a4500c98402c821043d03510440742c000d801011030b1039034550032891030310f042c007a0061642d0f0610078180030400c002d40c0c20206103402511042d81c0c0b0741d02e554802c01c3d441c0d804501c4403038254100b224078001c075020400000d0300c20f0a4400001100c07115a80c0c0d510000c1692182100c17aa4050304154400300040c02e03d00040c1e40c0804031046461020301c1445c070180e0781100c1981081d03801e80031241c1c10103500c0c1403103003444d0041c0c641d45c90001100d4503207032245956107405100090250200800040464241e10103603442500000b00912062903003160a203102c0720107898192092600307810f44140b9554803001010089070340c1d040c2c403520851640f01980c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 544614316 1250 544613066 544613077
    0x60923040f11040b0c4e0a030b0112180b07021509030d0b0904020130020406020307050c0f1807050d020705060f0109051b09060c03121503010c09050402 67
    0x407003a480d0020341080c0781c0503801910290803c29261501e40c49000e070b1040c5000c102c58410000d80c06058003041c010f04d5080480d807403c00003e0f02c0660304040c25a0742e00000f240c0811115003415020452a0000d54150007400605009176240b80c140d000301c0300d0381c0c800c540300d0034044040302c0c41d2299804005203100c507516900c0310746130065502c1580f05400c403122403141102d84c50099000040c18004d1401648950700c41382c070080c1c5002100f4542940003034400d1b8082024056001100d01200303913000440c503a40700d05141e4480003551103c6c6e1300e19019540340c000c50f0003103c80f405001840011414501181680448000c0289410072020012442c08002c054594070820004004124001b011400108000d03031042008000518100740b088440d071006030070180b1203605140500c088094a01d03040e5003c562024801951151660005041d520603070150388803602001ca100e1400c0182514820711501c084801544401c0f818000c1500300e0b0001031442020078602c103001d0010341001c0e4050003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 544615566 1250 544614316 544614341
    0xc02072309190e06041104020d240603050a0b100c080f040f0e0610021b0105040e0702010b031b060f0706090f080a0315050904031803080c0706092304 66
    0x88424955008201d49840441c0e10107041c450031101030081e4240d92040e6250707080000b0182c006401d01ea640e26119051a04080b8071a071340101d080f040c1128641d20003890300d4031103d000a501020440c098800c00071611800011034038000020380803175001e0141d0041c06400500354800b00002540607a5030860070481921542d005001841108020b06c00a00281ca40480340b862207a2400855541d8039030010403650050307020500c00803490f9000192520b0030220280c03103500044020004903114040ca5021851801c1d4803000c1c0841550103501c803600f400c20640940d04400c8500200b081d8a5184080c0341c0d4101c1805c024040c1d0150810024140d020710803507011500c8041031f150315a07010304007001654400c100203807400510350140300d909000d072640742071003980300d02e04000a158290000c00250a0010350305072001c840c503844d15608090340d804070505032542d000403070980d82e800250090a0200b030100c2008078a901c085241c80b2100308000c1d1010200215400910003e00102d04041 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 544616816 1250 544615566 544615619
    0x140f04051213050a060203070209061c06050a14090f030403030f20010c03060504060f0506160203030a0306060f03020418090c0b120a1b1407021903081902010c0207 72
    0x103110111100041100c0d8840d084003400035803c0c03008001c00361102d60320410030366104221000040c0c0f10f243c040b41e40300a00302c0d605ea88031034501503c0b100702d0f0318038000101107510384000c0100c12032060b44102d440c04e415103901e001e184d5940c8080e55468103d1703c81004207600900040002038400c21006a441031145081c4843c6840040c00842e00741c42007800442c241d44440c0280d503913560610402005241c1103130180302e00c40c909003440c010718046008090141600065030034403041c211000c500c0c0c1503806801c0b0f95a5000d100c034001d0052045010701c00001e9809800d90340c010f4424000d490949103074001c07464442c02d106419038001d2403816000c4620700702c3c5038800502000030a0280904250f007610010040c9400582d803000c9404102400000644014408140c6640094000a800380e0003503500d941712002d000040c035184904078030210210f0f1812010040124600c00307481d010b404c03240c9508000100540603802d071119070b0800d01c01a4007406040040c0c080782d09a03400d055440901c5d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 544618066 1250 544616816 544616833
    0x3080a020307231804150b071112030d0b0607080313020109050907090609170703031d040203040303020705011d0c060a0903061a030f070503060f09010216051f140f0405 74
    0x10300f074000703040c100c0803219041e0108140c140c0c6003031410f541c001120304960400c40071480c503088800b0002c65004260704030714007082600801032100b64042c0702c524010308900d0074000c50f145007030b030703030760000e0b104071243d5040c100c0500050034103034162502c281e401580d0500f5903440702c009400030040c2e0581a81048408a40006c4035100c215840707001f031400d565103555441c181080580006915442148620000c015040350354801080c180c080da50715142040044003250b078041000d8007007107405131f4002e10000078041010341503401001c1c0325100e4130080c00044c4d261031180c44c450310038086a4540380c006803c001800d00d0310304001c2c1202e801600f0b110344071540313a484040c00c40d2026006002c2080c0c07c0d4013581178924081001d50706000390f00004140312414400800c0e00ca000c0a4950840d565140b008142d18020a40583e4034840c82e50070060329007651810100d0f644c405029012010072000d000d07002c01c0e900e150156507880f400d00c02d0391104648031143d0303828480b44014003d64450099205 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 544619316 1250 544618066 544618097
    0x3150b0409060606030e030f0a050c030d0c052713020d0905060103060c090b1806070204110a020106050411070503090603060a3b07120908090406090e0606040903080a020307 76
    0x28501c021801207000041040c20003c000c0c049902074080c0d40c01e560310600c00d0b102c1c0c0000d480110342c8600c100b03142c030384c2d100c0c85582c0c0403e1550055108050580d400c285c0c0b0110011390040c09442d5034170528484c0100340070003006080903554000b5000c0e4009003a410050300364207150f0000d220241c0503401c000754040b26512100d0a042c000e820849045403194560300c101d5500c0710b400c001600c03982c030b1045d1410f401111801c01348020242e51038050f101c04202041507640d40d50100b801005007800c010b66484100c603000b80204114020790344110702e00b200300c150294420041d2000594404029460401000d040090f1fa8100500300e941c001c02c45400899a00106031462104070b24036007460302032000d29540c143c4100e25082e081d00c1112891410003013800d5000d8015841c00b102e9180009490800341050a018411000c0c1c49030060304001c1e0014144a6551040c41480942d60031b682c625164075041100361802c815024000070042008a21070b010140e00450300301507181441d0449000010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 544620566 1250 544619316 544619321
    0xc040c02210d1109030601060e060316022e050c0406020304090f09051207060b09040b16030905031b100608030a140d050406090506070807140a050f03011712031003150b04 75
    0x5680740c0d12a800302d181070b005c0c1010032083d805030126050804c160040100030074070b6804000c000c80030861215662a01c2140288855120b2812200400c043c01c61410311621070071000703030400b0005501e0100003035001c2139000c040c2c2d01660403070740c0034510341441c00001401a21207202038040340e503581d40280300010b60801080080c03500c00820705448415500f802030494422481d503e00404030502000001221410325941c4039021492103860204850320440040c0065074000705103100000d0005480c4240c10001c19418070500c040324000002c0c4a04042611124811a0482ea109020311a403040c05039941d9080d104204541c3e500b000c0724030103038030203549007581e058503580e5540c1c024005221042c030405510800505040740c082c10703c2d210050070581c1c1c16000340c045ca0008280301d200b05103e2412154000084d03980c0545958441200504140900107001100d20406181302c0700c914034070058030302c518035076007503414000c5c913684614441814114a10038100c4d504c0841800340d64491 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 544621816 1250 544620566 544620581
    0x6010203032406071410020408120f0c0a030305011403150106140f0a0503220302060609130609110405091204050f010c0203060a05060405060d020d0f0212030703030903020c040c02210d 81
    0x88030710b05c5112002210541c100094040401002c9004220500403400009403607488520210b10503035881c2d401c82400003541c014101e4550031409803510700e0013455410340000d41a101c5e600340a034682140c0d2020195541400c030f46800d215852607004100c514002c100c00001c104650f690b052034001c015506580380d42c41407120320045003000c4148179140c681040d070303c040341d81c8240758243d5068250310b020307642c1d20b0000c140e14881c0e0006800038010b00841d8100c81c60141d8440418007400c0e080740703020141080048100c9020750701d414006505007000041d45c1c102d400f03054240074a082e0411050100789514205200c0c10300003e906000016101000640d03c105640200090035040c1081000280c85018108a2090004120000160740c1d900c524415071607104501c84000b030740920210b00b542c0a68500400d0742d010204d0340c1d00c1410340507005115884d100390709440070310307410b0010482160a4224518010307071049149042005940c0100034a03000f448208904140e180c81a140030364400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 544623066 1250 544621816 544621823
    0x50748151716090f030b010e06120a020d0305190e280b0307170906040201022e0b030a0501050403020307140111040b0c07080715030f09170708160f1a0601020303240607 74
    0x20340c0010070001d08103100c22358200c00d088403e00858901800816031700d8446400107485822100c0c101000c050060040701c0200c815002c02c0264403c0710f20700980007480c104002030280c0d11700e426040012980c400031003074648041880c46080c5007003822085803904000c140100b0702c009050b409641071a40c1e462144500c00046c02800e00f850306100081c00c059002c0803800c03070a034265410340e0002482c40d11340080c0421890000030420b60500009207842565070000d0181e5180509205c203260f4080b0003400204c0c024000c414003001020074480c203c0d20200d07070b400f20a2409000501c02982424000c250301c0d170410040b0b901c2292108811030030810030b6403203100b65041c1c008469040a41500503694100c122170410002c82149444003024440c8501c1c06600c18800010044100000b0006481900204500c00004104145000d0b01540d10780401550034640300c01d410100f20b0100f1007014414207041c3d01a50442c2c481c18005840f5005d540700340c048848840805805035141c09000e484420302 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 544624316 1250 544623066 544623083
    0x40f030f0f05100902130501030b010b0a0504170d08091504020105070303020d0615032313020d06050109050a052d060102070302030f1b01050748151716090f03 70
    0x13151040040d03540e503240c882c440c06400c18004001007141003102c141106c0d0071000d0903599104980084555110340e400c0041513501c41103404a09401c006180c01507060719450340b141e551220000e1039995424148107600c11100300c4002001940b041e000b40002074464240581009443e0b0780c20300c2a942d2580014119400121815212680c54056140140019621584080d80c100300100080200400100240c4801b507400411511000680c100551f0085e4041005503103130302c0204060001501c00c404080d0521000c2803404007592154802d000750031441858a001009680642a00042900e07056000d40070000000d81c806001204101e00001d007e00920500c801c80001e6900c050030b944c5040101c14003402000890700300200c2c2441d46083c0110f01c17103102080c504051080d100c070702d144800710751207000c2e0a410a240d12907006e43d880c0c00014810700e998280c040741d5110904082092400403880401d000c0d01a0040e10710450a6504d00702c60001d0711a9070300400f8030180d030301c00c461102 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 544625566 1250 544624316 544624331
    0xa1406251101122003280b01030606050909060906060408070305010914120d0e280b1513050405030903030708043312060f17060606040f030f0f0510 65
    0x1030b0f01c40e803081d585004030754081000380e0070301c000c090950003541e00360b40760510000045180801001d02c03c022010304080b15020703001e410740c4804081e0040c0a1030340e020a0400c1000b28441c4e000d10190b4038a0200940001100e6588a0401c07913041c0b4050910741d04400d003080045844541480000083d50040001084a0949160044600c3c5a8950404494000b40b441c401d0181c02001151500c041a04010444807203648240342484a42c04000740045003c1ea042980c0f01c0184e0300500001c0d002c3c2c0b07501c5429a41f030142a00f000d404083c004ca5004664180c000a029000e60040360030502aa040300c1c200013002c0082071859002081c261130383e03500480c040000000040c41c1c038401401c0c41c2c1c0f101010f100000e40102c43d1421009410060104004c2c100c40800c441d540038200a09610094070880c0795615801440300900071041c00140c013038400000c0e46403c1080858084600f84114100e64038038548403000d458840c2c1c041110b50b4100c00004e078001c2501005114020104440d0009038030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 544626816 1250 544625566 544625569
    0xe19030c0f0e0f072723010503070f12090f0c080102040b09040203071b080310050d050d050a170103080d06080c0a060f05040825050a14062511 63
    0xc015540010402000003100380704119500d560a9042a4030415083c515261110f0640e04070110f00c0211011400e0480800e40fa441008251800c60750542d06c03840004c8024030001110010b101c1c1c1e0f0b540468020008a14910b20544040c01142d001d03180c50b0030b480c140c4000390030a5075181782d41136510605084111060100255aa60041030074030300843ca014940701d44540603004445816100ea41d0100010f0410307030161550550412004034000116100340c0340010b100d810075120614030600a03800414113041c60148450000c1e04440140b44032800313841c00302d82035440a503807003041125002050910b01c000c0f107441400b86210707410040e11506106c1c54602142c0090313200c0c4a0662100503402280d0b254050503009031101403130224813800c000754041d2464401c90340320742d5403440b03100009660350142a64103a0012038600e00e529440d591801000448001350056008048400440d04490710304030004001e4048521752104024500c241500c4c1e0303401c06440c05803038100115210f40f00e107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 544628066 1250 544626816 544626833
    0x132604121b18110405040507020d180803090d0c0b030702030a0e10230417071502070b0d020d061502010f0c080c340c152309010e1903 59
    0x28070031215200ca46041c07500701c03014250b103428a80c8020795540c640d0714844000d000002c0b54090b020150061200f03040c0600001c0d81c5003144400c110015400e4828003032800949450942181c030803200031800e01c4880350030000c0e555954041150014950100018550545800740d44109080c1c0c003c0e41d12103200000141030404185ca09502c603010101d90840351a4202120090380d07003035512650941010518007084500c0785070410300da00201500712591451000800409032070554900d203007000c0c420041a07a032071907617000e0600301c4441030280c0c1110450302d86c05005036940c50440460305558850f00c1c0300d24040d51b01d1240c4010b035164055000b06500070f0052f0300d01c0c08041d02d0948114a00206940303c2405044010104124900081848040c0d07080d1b01d002054035211348003003011014a005c15584225101e40c40e2440d8684030b0020b4407e018805800c43d403000a5250286030100307612114a40d44034120203418441c4040007003102c0d13100c1d0704e0b11400c550380200503162800c0c29820607010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 544629316 1250 544628066 544628093
    0xe10090b2b0302060a0c0c03270f05191508040c03020a0603020d0c0e01050d111c0209120d0e0f12010e010e0115030f030e01050705060408030115030513260412 70
    0x1c1c0c0c0c60406c50028112a0302c0b18603201c1082d010700e002c40200c1c1d807142c1d0b56140c607a102c40005e80038884600012445840e40d002d075204a0300122031040c1050924003502c0842085846a06038401c44031080003c05806034032003aa00600c02e50203041d1181d12580050b841354826013000000950214001990340150703c203480c1c030403c0c941000c201605d04003000901e01d200342404043c0d000e40f66110348801da210a0103079141400181d02055000d100507165000940240000707078490320300301c1c115444c0d607403010800060944617a5601e40c03a040d01c00082c0200c2031080300d50307140c1150300c2041d0703a494903d0a00c61620b2540070b40c400401c201e030711803c80a094403264000e4920640101400300001a13603200607045095040c00e00710202c82907400141c034a401006c0b03025210340680401c000030400d405005505a40c2451581c00340d40c410074004600300c030310854602c590600c00e42c0c90700000c00c0b06000011600110a01c85904803450300d044400c16400c164070000782d4070740c101844800c12541113441c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 544630566 1250 544629316 544629331
    0x120901030c0e0901030201140c061501020c0a0b0d092a05040b010e010801180b100804150501030510091b03030e0f03160909030302121303090e10090b2b030206 70
    0x10407031202c440004002c800180700c000d05010701180d000071414034941c02d0310340084e1031100b0f6500e203107010325044550324681d0f42e0850050007020001d040510b00080c404059803003d000850904003071203209001440c01c40b074250b07072080c40000503c1c0c200a004d800030341d4003070501203050103c030719010911007030300e500005840c103102c3e14a150b0140d69902051040c1114012100b04007415035440d4140010130700010080e40141d90243d100c0d07522500040490300031442469501450042c03641802c04451b004c0c0002080d9410501c0340101100c2c217504031a141e03034080e20882d40e91510141c000c00f03114003039034012408560301c000741500d40e150031007500316140e10a4001e0580342c010b9000c808800c69540c001c02030790940d1205440f00380341c400c0d0705a5584e90580002e0204038204900c0a8088e121488421400501040c0c404240c1e0322071002080e000396442107100c1d14075401c050900d0041e0010030794035500171031500b0020004089170711456615007401490180d4030b003403604000b42803540c000e1010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 544631816 1250 544630566 544630577
    0xc02010902060f1b010b0609300a120302271306080f1203060a0e070e060a08181b01120b0405010b120906040201081603020706060801051005090f0a0b03070305120901030c 75
    0x50b01b19100c0c501190f010010480b50f82c0300710030000d10030f42e0600010404c11030414180025152562400041c0e059032a402404840100e104100e422407e038461030008640b8160b030641e004c00148035010381d140320740500400c051020750382249008211541640603101c0ca071b103d0700c4883c0544000340b150b504a0075801190615619002d0041074500d0f11502c50103c0380d8543e0b000040c620f41c443d0481c031050400052188d542c603050000300030101e090940d40b9003249008075004107501030000680c0c144914450b91241d0402440500550b98070100700c050719000f58580f1400d4259507030794416103010b0605820101e0311640d031021f0318555100b000b018060785a1040c003e00001d40c2e00969100d601c4020003010035510344007100c08034040c1c001c1ea00003c01403800d1503c08603115a06400007807090f40b60b003031354500c5d0960318020445920001e54041c0780e6450441c0100da407107502c40c0c00c07000e24007001030211840d0b0303035607580c2e00707071820845200c201c2200781c0103c1d60303010547c1c2c14083d604940240e40f030034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 544633066 1250 544631816 544631831
    0x5160e03011514210102070303060b0703144b031311040209060c0703050c0102030a05040905070c080703080f060a050112050726090106090e0601090c02010902060f1b01 74
    0x1003820072401e4002d070102c0202d10500c6462568a0040f00038284a64482c040045441c1348601c50103904005011404070742810804224071400da4162a43c45805954850000b0b42500948400303501c0000289240310700040c2c00f0014a5103949024558020b20700c02c1c2460703c003982824029a8000400051074040400070300c102d0700162864580b00c160454183c50526200000280c000c0c865407032070680000d004900980624004101002240c0c002c0e01502d0084d82c0a000498592294000d14400700324240001c0c44110f0315540301542c00189070820408481c850380740c6400e103400600048002030525000c201c820400703442d0f403031341103942680c090041d28207103800a8940c1540e072002e501526035031000242064481c40c1888081c1c03103018505060866582500c1244400450b54042c46601b84480003410341e145214450300c0c01c121001800c10f590910000c0c001405d0118034500856484407150000340e5924070040c010004480016903440030780000000d2460180810113110f42d140200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 544634316 1250 544633066 544633091
    0x203120406171803040e060d20131e0b0d02031f0b01030c120203041113090203010b0d112e080a0b0d03090b090411070b091501031e0501020c0105160e0301 68
    0x25a170540d20084160045a43c0b22030118204030240c84000e000441c0848510b40103607200028284400c070159205001d45107041d0448007500d560240e404101c11403040074403280e6910750311804004000800e8101040455000240b07403400d42e20020300160340d10202890110b6441c81440072244e001c0c00c00380480c0203c200d010b8260080043c4c195041900000050200072491500100990000301007584440c00c0b1094280200b88004080703029619001818216161003000350131099030000c0e4001c03c81009030705002030000001074240680c0c20441c40124401d0703a0b8030480e0752a04059550103841e14100600c5400d4440a941d1140240c030005c0540012070fa108480406480c0c2450002d0755420b480c9010a0003010000700c1080124404642d14003041003969a45000e00c2c6850211440e42c0d03444030301c0d0b030700f82c1c04d0a02c001440300c20080c421041c9400d250008180c00b0b40510001410321590304030843c29604111080a5541c0a1480300510789030011402150700c0c1041e4000c10290f00d8070328 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 544635566 1250 544634316 544634323
    0xe0f07060c030206010e070519080603070b190f1202031509060d1a1009020301030b1b0a172706040c080d02031b0a02060708130e07051602031204061718 67
    0x84c1b08035502c40e10340002c1c143d1b4060012540404175001080d1001c081400c0000c00d0b030801664200e120f4003401d403001407841204020348951401e240e800f05011000d42c0819513a4050310001a414003110391031a04607500203201451144c410f8030500317039621443c04c1c100a40c2c3d07036004041500c507151309021400440c0b8000c0345103e1003074003011301d4003007078441d101c581071304803207551011401500000010007040300081405000d000741030750f40d16604909503000c17400d0b406841c00040000703441103010b03107a07902c1000041e0f80020004601c5000005680800144c20301d00c280180900c0e40010140800c0100307920040c0c1c010103460002c0c00d0304c041d50680c000e40f00c0c03180e403994400c0304044868141c0c001000707000346070b602a4024100707550b076040b6141030320083d000703041764004800801134009488805c040e0181c5c4a034a080c4d941d645049200d01100044041281d000d036058031640743c42c0e2100300b054030000c00240031a84c03603451180410710b200300003886000300340c051000c0303100115166075030001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 544636816 1250 544635566 544635569
    0x2114010315380613080304081603030f050304080702130e06090102160308040203030d14070e090103030c0303090f020907020a021e102001020325020706080606070606090e0f07060c03020601 83
    0x34080384408110b8900021000c1c01041a84900110b0820001840e5840000103100301c5040600340c428440508902e010740344054440600440c01100428a400b48600002c0d41e0007440f0348080e0341000c2e419004a603015921f4001340300300c6652861002c54140003003140d0b541c8044010000e521380000704240340e0030496106402400e1040300d001050441d5000d2059407454043c88100700216030803181d120825440903540d03040030480c801c10300d48544c10442c44850603030782c040d00c0d608003954180c0d501b100104020203041c0c070341048070000d080050343c0c0c0c00195800781da4180c0c002c205610013401082541e40c19440f00300b0440504500590b507544030384201d80d2a030754443c141490702400142d0b0100f01a89200070011295200000b0004550007800f8900d00d0307041c0d0b6004219a4002d4000140e9450780f00b40501004a88000001829460002c00170081340c0c0c4590b40214149960340d00710001e40e1103010303502d812034005240400300d0740f104100c11001041c40d4503201c0788000b03468401a403640d07410b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 544638066 1250 544636816 544636901
    0x80a0501230d0203030d150801021201120212120901121e021c110d1b020715140d0906050f04080304060c11060a05010f050f012114010315 61
    0x92030307084103040c1d03103014503080c1180c0c001d03060702c1c1c5e0360841c681c41d500181807903500ea01d003041c1601000300744e4200510030385003020040c84001003940d080004680964510f04000c90380400350b4161500e1245062056203100900f0301c0b1880d4561914500140c003221000c43d06440c5a49004c4081d0418003041c18007000c043c8000c1070040c3d035a00803015503407500c00e800c010b003041c141c10221031907541803040000f044200c00083c02002900c03000c8044c0c049018044108800590140c1801d104504c4620154042c100c218141004040b10015518803035130425040b007020301d9075400d43e10050182d80d002e00b40c4d00c12043d042c01e84a84c5007130741d1210b046000c0940040c20041e940c1080c030b2410750054265406107140401203440328513040a40c680038109c01d004090105010040c0003c25081041c03000086c0c05050b12051111480611b074100101c1000081e480300d5030300c132816030100c054451612806107010b603240c0341941d6001440c84007518a0715810399041e09007003406142c0b885ca0b9411840d286001d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 544639316 1250 544638066 544638119
    0x30d0f0e0303100503010c0c02010804110a080d09080f03040503071202130204030b16030b0310050a0b0607121b020a1701060e10091a0607080309010207050a0c06080a0501 75
    0x8101540000420404112900d00d1200200703000032a581c5280c0107007141c0b0b085000b88110000c07010100c42c46140b66800902040a03c4007140010b101c0546e060b20b14000642850b5003aa5140b450a1410316003440d01c001151540c2d500f441810303828409214803040c0722000b585414500b40c04240c0d1060103110780c50000900c522507c0440da102e1000e0780101c15198000d6441725101c0c00d111019602c16180e085401403d0565851898040d00410b908007900a000d0482c0c6105241158040d0000a2900003060f0f96081800301036a21980a06009405140c605181d420403560250080381c800214101d00e0128074000e40c0181e82e050050340550304402000c091040381200b0f45400741032903811401204114004002003003d614040c0d60071912003500a0045004005003003406006964003039400c50010446407000c2980c0200440d04403a8003400146440c0c1151a00ba0500d40000011101c40f81c102408105265111411642117640c01340100001d5141a896050601e20a082c0740407110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 544640566 1250 544639316 544639331
    0xc0f0c0304080115091404033e03030f010b03150616050a03031b0c111c0b0c07200f010e03010b060304050106050120070302150403120201060f17030d 66
    0x10003402600c0061500c0d500a10000b0070209241c0c00001d244d0080701143e900c3c04409032518040c501000c6c0c0030f103400d80c072200024040021034000e0050450480000ea145a65400c100764840001ea9103403c44070b80080d42d102c0c1005045120b2012069102c4a0201d9003401400070740000c607440c050300e110040700c20650303440d22520080c000302001c100207812070040c2008030080c5601074100c6030403001e405029426201d041c00e010b03903002241841c0a80b0718003581560010a00701071514140c03461340400201c08402c11031362804060300301181d40726441400407408e0000c00c03152104100807814140302211003040e491020603200301c0000d03030103030404c094941d404803a034500394002c501c8110060003103641c1e0321b042e0070040d000e850503100d5a4001241e00c0c1c100941d5015580440d50824501d01c042c0000c41c1c0f6540030000c2c024848800c89101c01000c000c0040000c2401441d8080d501058001003003842c54072280721401803641d41318003008481640890880303140402120900c1b01211000034051 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 544641816 1250 544640566 544640587
    0x5030115050913140a1b050304110a08030d0c021b01171510020c03060108060f01030f051009060b0f0f030d030e01060330030209060409020306281a030c0f 68
    0xa43d5030840844414900b140e21030321600e0111420744a00e03810101031004580d0b211440350b10a10218041e40081c501b440401c3c0050010007203442044001481a00f0540d20f510749141568046101d0408203035883d90704c041712075010303c0303e100800b861080c14045075030002c00181c01098180b80c20480d8190040004180c125103241e03400c1c020034007030000c0880304000d401c040d5641c0c00c0c074201c0350700c248034003400043c1551000406510a810b0070f08040719507461940d0b460040b607031000080715540525903242d6440d2200c2c1c81245503460142c04040f03844130009050022070740a135010307507010341c9906007080c00d0f640300040d0349038a2200515000607138042022003a4010002a000141840c0070007405030003039a012811449605140007118004030004032041c0c08038404c01c3e0b80c0c0c940090003231004100b1512540d002d190300180c00b5103410440064601a8803104926201003615000310b54820321500d48003c0442420952105880d46103050048140510340140c3d050390719410800030700c08903013 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 544643066 1250 544641816 544641829
    0x2a0c05130e010606090f08070b07030c0302010e1b0f09010b0a2f0f120c07030f05011808031509060604090b1909020915070b011a071b09050601050301150509 69
    0x201e46000300204a00c41d181e0382d0003060700c0e00034800d5420081007001d0128101c00003043d0700e0100c421040f40103207450040d0750240c940e80c4882e1002c1c1c080d5542e403400c1403180501803010031100c03034080c0c241d0f80c5c1e089071744810030a004049102c00d0b8028103600c0300600c40703001c0441c22110200400e00340341c04000e4481e10b41c01203110740114030b900748904400028849141c0080c40c00400d40d5a038090b0340c4480c080703481d004102e00407020708072050b50010b10208049107080300900483d600a400101e8180010008400040490141285c1c0c0807000001c01c40d40020b80890711406030700031219071081d0f0600c000000c030306010300c1c0203010005a440ba1118441e5a41c0a8882c402101001441c02600c0d51448100029007054003150f00a6802c140c1c1d50388051440b201b00c5210a500110451782030b400c01030340488080500c000000f40d820100003000100b042001001580c0d5a505001508241031044c0d80d01aa00050461410300c031062006000780e080e041980d00428105260540c2c4881e80400007520 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 544644316 1250 544643066 544643081
    0x4050a090804140f01020a030207050d0c0b0a0e010216030c090509010b13050f100e0f0a02040506040810060905010e0403050703120c1707020706020d08130209072a0c0513 75
    0x110380001c0c0003c0c018030080d40480f4421044070241c004528801c016a02c51030341000040050b044400c3c02c0c0950b1410980741e581050081c580d5000c156118510420164802414000490022496003040e90ba0422220560002a54141040e2031441c2e0303130501000603501a0308801c540310400552030031025403000602410003420340782040c0c6181040401400117a680c01c04c14002580010b003011940b920501c1100d85800d882c41141d900c518048480c640081c01c200210341d02040002101e54819000d80003500203c0c01400400ea14030941e40201c441551052030b0b4181003c004010481d8234030300d21940a505810308968460042c03400f160070300382008040b1000c51400703140709501a404035503e140640714248801840d10350420681e602d0203180b00d42c0340103034400034102c040c1c00d21800f40c040e0840400c00c0c24040740300060340003854000044482000042c1c111b40400c10280342c1103a151a04c540740d82081900861544030085920810f0040e280500c41d00044084181c90f15403043c007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 544645566 1250 544644316 544644323
    0x8031c020f04030305040e06030a03080f1503060c0a111b27010914072c03030712020606010f0314040215070b09011e02030105030a110613060c0c06170604050a09 71
    0x39942c0303840303140240403600f090040901c0900760720005801814000b40c901421a00364840110381e40c1c0d5400d180d901d41200415160400307a1084071034a050300c00b000b046e8090b040c581c0502d40c499442410081c0750200c2500c003a656548405c1c40b1841d1142c0711269a03076040000d4498031110100301403200d4006001d4441403440711910000001c41090304c0e40f144180c1c0e031103048011020f8858101c101c642c0c9409001c03101d036402a005c00c5465160500051003140d042c06030550381886429202c0315003402c03400c10f41c8c0c809600040100301c810b44c3c0c02403a880795045103080070072100407941c844a05005000b800240501d50a0710320100891540050b1846164060040c03c550701d0b040b200366010704094100421141d01003100000840403130b000380c0c0c1c10f03200060002c1407141c18949882c01e415074003140190704813038104110321052941410200180101e9180d280a40030246000d4001025039402103040041034403164203c00b2051001c1500110101c6010400341c440c40480c138024000400001c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 544646816 1250 544645566 544645597
    0x60c120304030903140115090509120313020f0901061d0d060e0a0204320c0c0d0f020607030c0e0f01020c0409060f050a0501080a060203130b090a150608031c02 70
    0x1104260307004410f501a00e2003040d0300b10480c1c07145032400d420798000c04221450301807106424040c140190707200c01d42c000f01c55000c80704456800d0710b0f0300c950b41d80196041000114031645400a600302901e00b648000300507188403100350315103100144207111400c010a142540c036010454595030b1156500c0382281c0240c3c00700b00d52444d560301542c2e0f803490503108074080c604050000f18481d488004007600c0b107100840021080605003200590b0003001003251600300c4e01400007103403e1404101c148103002080d00d801d008031070421000ba00e4490001c04000c100b504041130348110f0366000c01041c1080600340c0d6110071340108600183e0030103100401503034100b89845502030900c100313038210303030100840060b080100c1c0c1c44102040003555400d008803907040d0700c003403070035000070703260b41d0007154001d03c44680b140f8000450307940e0305c0c4400c1013540c0e00881e65001c4c004241c14030030720144d0b12032040410742c8100070301440d0064850b200d0050318041650310540607002c024032542c5070100d40715891901d009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 544648066 1250 544646816 544646821
    0x230609090d052b0516020102030903070803040611130f0504051e0709150909060f080705060a030b0d08070b0f100b0c0f161e0609051e03060711250302060c1203 70
    0x43d80040204072401c0d4041d5010440360307541c1c603006100300c901814918010b50f160015030b44918205510107407085499030b0b5286d14904403c00101c011785a884980721100c201c0910303249540c585240940c000c144664070707090500c0490380701d44400784840c0c44822a4a04281c0d1007907010b50f00c1c045a41c1c403400c1500445001c1102442e8003018210540c1d41c0220100201615460109118541400b8000059000c880c09000340d14020019141555a5160100c1c2d080c1c0c00e00e02017190303502e50400c11140003201155050400c042c0c500c5050380006090110500340c680030010442604d140d200d16410300700300007504008541d050000580d05151071707085070500501c90130800d081c481c03144100500300400c0c855841066401c410a04111003d60b80c80102d4203003040700700b00782402c28058900311b0004829100c0120388044c0900740c410b0003036403101c01b440c5d00c000c060242405491a070110906101d20141c0343c003050a071b104041600d03010354900e0b440301d0340c40702841d250491440d0001c40d210303004800c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 544649316 1250 544648066 544648147
    0x303020c120304020303030109050907081209040b180c09010c2108070c030906030209040219090e060f0112180203120a02070b040e0610050904230609090d05 69
    0xc0c61503600520456103054607400740307105240815140254560420801000102003c0d004103410030381100c15074088690340d800c410b00c0c1200f460b030000340b6107070042080301591034907100309007440500b030b58211b449042c01a1000e010b00e1000b000c4100c04c00d804036501c150359104916800140e0781c020203004024844911503c0501c0d0400210800101e1050000e9a00d910980c0c00c002d240d58162100200359081403819806900101d50158006034240400204070b5450301e21000e852406842d00d41c1c032141010071001d4a010000e1805002e174a8003011180c1c6640d00055200c8243c101010010341e586541c110b4941680b40c600002e54540308008900810b2810403004104400352a004c5599660391203e840b5200c0c0a184103504c42c10791450002801b6081c4000e4010710344006280c03040c41c1c602d480c4002400c0342e0b41020008071908070302c1d900c480304000c40b105464226100321072a0000e854802e40599a456118000358100400802c00260f401030b4802514070016403403011980001e0703840c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 544650566 1250 544649316 544649321
    0x103050907090e010b040f0905060703051905041a010b0a09050f04060b190f1d01080402031216021318030c0503120109020903210306240a03090302120f1602040f090303 74
    0x1702e0368825031034003a849641024034843e16214950103001342000c1d50f07411000350300508004041c003c3c1e8042d000d403245035600291050500c070b00c0c070600600700e140040d500011940c82050300540c0e0074030700802c05480035640142d410800c0300c001b1030380d420b0b000c1d100b00d000c1070140c029680440d441b08408200b441c080c1c9401d6082440000c3c3d19920440e500050403c2203c1180180400040d00e83d061101c0c40c0041d4410b5003d2648640068200c400d0b40d240095100f0b1213070b11114059035903000d030085035411450103129007800d50b8003061041c403107000801c5004c035003066100130040a00400c3d032001020070000b403064880d6000c11180004640da541c41e01c25000c2d500ca031003140d100740603484564100070a41c5801024001501c4005810f5545000500101c0c041d16071000d1241030902c2c807010051200b0500400f0000000c4d034000c02d02610b1868003074904005091a0740181c45c080c8007a078040c00341c0000f40c0c1e14030800810f4560760700303a042c004900100f4102d40c48107006800c0c066668141034054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 544651816 1250 544650566 544650581
    0x2001050702190e310203030918070f03021201151103160c0e040f110117090c0114030112020f12060f041e03050d0209040e030d09110907020c0103050907090e01 70
    0x140100741555130b41511024135691032142409540780c08100c0c404964810500000c2c00d40d03c0507007201e2804009030000f40e203810703902e035088000402e0345040080c1568082c0102842c541a41400d5040003241c02000d00c1c44041406125446d503001d80d001a24a4801c07011454481e4054041d2540c50308012400c0030001c04018007519050300c9031700d00242c109090311007281f01e0350b0052000a00c00c005562003588192040000d60b040012a84503201005000618980100e100200034101102044000b6012403100851100506400e00041007450881e0290040548d4110f41a15501d008030000442c1c2c0464a031301d0320064030503441002111060151a20b026038001d207110201141c1441c0d0043d00d20481c1c40000740003400c11722404150164075009040782000c002c00200d000f451070100c480c51604414040d42c40261180d00e001c060000d16001010382030402d0b81c84203014a4200320281d039500410004504140c0d41d54000f485c00e000511010020704200c030070503c80a0703103000509000e007550 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 544653066 1250 544651816 544651829
    0x60307050904120f1706090a0b0a090b030f010209011403040503040b0a1d09270106030609051c030c05031317042304181e0210080103050105060d200105070219 70
    0x603c906144454007601030501d0307180000b590342e01703d40d43c1c1005015a02c000500b0640c0b0f525141c904154165540c840c103200076000301140015083d10f013208062030100c80705980c04030350748104010700300c9980c401007035043c01c20100b103031540e02d440c4c52401ea803941c1f00c0c59105640d90380f004150503003442c0c0d1080400e25a07508203516404103200c54410416040e2081e11483c401404403900281400420410202038001e24000080c01c203580f5111501514004003003200c43e5080814070025109100700e1071032040d40213180c200701400c9003400160591102500246547e07141c0c3c0a200c040001c0f000c1501440034509d0a00c540b100e9803410855603c040d014984507403240340400007e07040c182849501040791414001070f0600010380c940040a226401c4000c6456682c40303026005030b20380c44280410500f45640326000c0d503145003002800c5070400b0303020700d202d45010001500404c00100d844020f4840320111100018004001a68a807080070360081d00020941d01d0161400807045800341114074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 544654316 1250 544653066 544653077
    0x907050d1a030f1204170304150503010e0c03010302030d0507050a1b2309040303021606050126060610052508130501050f04090207030905040e010b0a06050c03090906030705090412 79
    0x25051103c1e11413100f40080024280184000c1250700140c0c0d03051403894490714262480d00b91113480000758a0001c0c0f840070040f4400000400041001855203035003d1a40810942554119400039441d0300079005d2020400c1004284603007030003020f0060160981c0e003c0341800402d8184024540303a85403501c10041d0448c64a10344610f409400400e81a5200340140f40c040d0f01c2c0e88030754054009401c01c1c10708601c0007a240a2010000f0304601c2400d000e40f010a10130700c10b1712114004035001d200f0300f04004510350820824060140c6652840d510486074500b0501e0b102c10746c11001010070154144815140060001c06000380070000000302007800500680b070b07004c0e40e1500015074140c45815070000c6102820017007040002c4c49580a061072903c82c0ca4403d8441c1d944030300287c281da2200e1f80e800c2e0340740d5440101300181d162641220004101c00d092107814070b0200064151240241c81d4000d000340741c08400108140e40a01540c6c010b840000c1841c51981410b003005010107103c8902c1c03002240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 544655566 1250 544654316 544654333
    0x312021c1e0207050c100c0803070c051e0d230d0b041808030106050a0315150f080c0405120c0613090b1f0f020c03010f02130f140907050d1a03 63
    0x201d402142c80d020f40140080086614040c1030010008808000508001a50b0026000aa40709005500808569503060ba0406890500c1c90401015a0002500131019119203d440b200850188001121070a0010030521402e0507190b611500b2102c4554485d40040c0f5500003020359409025029001d1341e08011020070703081400031501e0030210140c82510b080c40104240b80c450700c02000d11041528012820000d20f03006001d9000c007070340000712145003801e000c401035540310303c880c00404d165207009859800c18118440d032920a90141500462407500e0103c0303814404c00c0316a0898002814503580d9081c82c4607004030134441d500a9801017402c100001400303143c1070701030300c1091302d048885200241e016481521455040826a015400390250520050740d00384205045004802c1000d652280b485000030140085074101c140442c2c8024424420303c540c207444103504c00416240300c2c0098030342c81c100703403a107000701c200e14407665042c0700e00d4200005201010b4900101c05504075014030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 544656816 1250 544655566 544655621
    0x10e150c03060603040206130f0303050a0810051e06040305030f1e0405010f11010e070305031b01060b0f03040309030f0f1202030c10150e0c180d0305070312021c 71
    0x511042e01c00581c48042030011a0161403c7e00040010402c0851001c20407903440b400c0c40800c0003640d00030342c007207200858410482e60300304481c035038880c141a0210051038140400950380f189115038102c2029110b604036095074403072100715001342d6008070849840d0609840c1c248120390000b030204034030349448011342840100c2702d000e840503244140c44100c1d0700041000d0807a0b24601180740c04502c0c0d921130a00026908091003080f0156000754045d42da110340076072481401340250030040040b07038501242001500c0000d02036400802d50110040c1e41d94480d805e00711810300d580d030009064101c002b0030410422141c41e4040703400d584640d071942001c06c002582a610380c0100c55440045801c40f42e08407440c140643c1c001030310348070a0034617519225118108441d200700c0450b196081032000003100c60407840c0380b41010100c100700301e640040c0f6640d40d54000b4454001c0f04002070034031a416410b1001075810341c0650700d0304600212007069500c080c14402001d04030000160041a85121103078095 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 544658066 1250 544656816 544656841
    0xb07121b0215010e06040506040603150903031506121104080610050f060a120902132906070f11040207060207050129030a03210608060f0a020a140a0e03010e15 70
    0x100c6043e02e0400b401c0d6a105d009000240c000200300650041d0703140c0340072000070024202c1e103004400c00350f40010104140e242c040c0031a080740800115841901c0820004c0b680d1004824a041884240210b2030024842c0041311a02950300403240c1405010100059040e2200c800c3c021108100c81c8038200c0300d402020f2154502c2941d00b440d00251314020000e0345034855800c0303100704520240c000d4064810518a607012242002c0001c0d00d1000d00c68681400c0702d8030003442c02400766040b5590341c0b03400380369903903440010010796004200300d4004101c0c10301940e8070b9069a12050b0041415580c0c0c1d401480c25a000701340d04002d884040032460101030b001207000009816a100c050000c00030102d030742e10706441c04c08004125441403101e60583c5003410b1414007030031000301039600c02801c190400c41035407041304600a010003511841848900c1d11560702010a01c040058840a5681c0c1c3d02101c03c111100540c106d0b109070107608008483c034080400284c480b4181414101451361502c440c41c0d4040c2c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 544659316 1250 544658066 544658069
    0x3050c0405010f0908010f090501050c090f12010b0d12030c020609120f25050d0e09010e060d050d09050f01030605060702090c0c0109050a03030b06030402010c0b07121b021501 77
    0x46090288024841035024184004078589181030211200390303503a040a0a441d8851150006941c9803007601d81044802d018450304000300c0d841007824016041d02140c4003100c43d908030b80c8190400c556804424200398465640d80101501c014006051810002003102c1d42c8140640040d240a04103c502c520101d049130181c010f81004c0d10032801c10100d010082d401c845000107010000b00584031070040d9a03031040300051400794103010f5460490400f14208480c2440e00300c10302c8010080b042c1070382c0c0c65480d2541996455004884591a0900840c0f00d0005d00500102103100d81c0701c890800b19041801441100d00868691401d00b100000440c10354405108507600f002045c8500001403800207011680031034009000790414556144076400e59200c0305040e610b98009295060506900d80601401418162209851410103600081c0003440c025000f401c070404010102d010540b003030900c10103038101d0341018440030030785001c2040791484260b03070b08000d48144211081340317001e1180e0460 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 544660566 1250 544659316 544659331
    0x21072c09060105090a020f130501090e0106090e130203010203041b150504091a0d030801030c060302030c0306090a0b0406060207080606042003060406031403030a0f050907170f0106240305 82
    0xc0799103010240305a40501030a1035030301503000c1c80300e84a424416006081242013038a03480074210b08d40b40c000340144c030445e048004904034080040c03190980200f10801118410010901503541c0c1503220071079000c980750300941c994000002d00041c81060610f039110343c00c3c582c05008005a4404000350050b041e00340f40404103006210400c501c0007607a010f0340320803820380d80c002c15228200d00001c8000e150000d040f000f0504030b00050007402a80c0410340007801e020b003821072035030401c041c03816058000101010b1042c40765000144c04a4400e41000d01000c8000e0414400291100707406501c58080740156440c03481050b0000e001460f1178052114800d10303482000c010501c0c40b00901185c0da10003403245030006d4442c180000007910301c95403d25001c0403407028684900b0a5100342c0103848000a00c440a0790401040c071011940120307c0d03104540c104100854000c03060145142045c000c0042200d10f5403a0910000b491404641c55003100c255421852061a465440aa04850054070000b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 544661816 1250 544660566 544660573
    0x10513061d0a152015090709021c020702040f020c0c010e090c090d0309050307060e120d021f060b040e040210110d120e0f030a0905010212070221072c09 67
    0x80902600b20b0015107440046013051018003039003640d10303041501400221880b200f1007041071009082c49054060034600505500d400281c0c13000302803000001c101e005103140d000508808540e540e5100500303081c00e0410944d141c04599a00c176803540380e050304440c00b00f003007840c28180031b10708280e0051286060b400841e04240e4038034184100010014411810f000b4980c0001c2250340e41000003000422803a51581c42c540c887c80284075055180e4611689558001031500d01082c2e000320305881804188800d81c007440e41c1035031404000e030000da4005a0300100008004c01c2e05800030303520910443c02583e0352003001140840c1200d06040001103141070742c0002c00c2210307a80d48180201910ba0320000c801140800d5002800c07400d001c250244448250710004e4070f00c4015800c023101c0070040c40240050451011082c030700c5000b502c00d0200c0203114141300c4180f0b488000811413000c620100312400c40d10013580340c04e142e00c0e10b055804001d030148070044480c0c00c42016070030304d041c0c400d10115014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 544663066 1250 544661816 544661849
    0xf0c15020a0903080c010c0f050a0801090c09031a0603070e1909030e10090e011d011503090f030e0a1202130905010f0908030a052211010513061d0a 65
    0x1200941010481a040101611002000c60866005030103050f078103500000b0902a0350341d025010303045407426a07041c8101030100e100c5098002c00f803941100c006d01d5001c0707945498407004980c0005603820040034120b514901c2161405c1102e400c2e88905021703000c9440c42d54807036180049030300003100d5480d0340d01101d160000d4140c402d03410802e0581d2003804d121400c14240780014561304000400c40340058031400302003044114a0801302d00505031304591513000194054400425201402121400c00302c4040715044188284d108a20564026000940721361241c90300502c60306c502100d04c0d10a4071002c1001c034140078080c00d09404c0c02da0060002550034541000040900040c0c0750540e210b5503600020b00414106000c0e6104042c802d0444680e64a407000d0b00e403040b01c41c061f041420300e9041c41000901000788201c091022500080f0682000310a840100d91300e2013031024502c1d8004044200048080c0c00c43c0c51407107a003050b2160607403860383e8003040c0b00d08501c03030748241d13148500d24480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 544664316 1250 544663066 544663103
    0x5060f091e030d0608011401050f03030703140c030712120212060d0c05100c0203190302120706020d1a0f030a11012003030c0316020a0f060507020c1e010f0c 69
    0x10708481211680c02540d0501c00d20600407401c5a039241c1c0650540d946900c10700c0524002c4600c21405008100d45001200301030201003680c80c05041b9004003440018400031a1682d440c1c0180c07650680c0700021296a18020325018400341c115043c0706020030940d55102d4245c400310700035a0b00b100740c41401a4119500d07002003005140e03c2d0700d01500c03c0700010001144a0320703482c91000e17403500c41d5186d400d9018454410705207402c0341103401c03041c000300202840000036404aaa89001da074005d0303100740c41c2d050390706040e00203118070541200c0142c134041c41400c01c0c05d550a1401100d000480d21610151000014151605c10005004012030b010717010001d2198021881d001c000000d200703204607444201c0402d189035030b10a0301e180121400110410070075121240440c6600006840640640031f2290f0b2204c040000d000e2005011b0b41c0ca450000310f0b002e1080110416110b0010000401060090140100d03c1c02d210002400200b2421b660401607008400704880c00f580654244029125101e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 544665566 1250 544664316 544664353
    0x10219051011090a030803150d3503041b0b1c0f020c0106180501120c12020607050a030804060c030c05090609030a080f13060e0904020909120d060305060f09 69
    0x1822200480e00340314002d19510744c64103c0f00603502c21013040e540c0382040a440701d84507950007652482001100d0681d0001110038a1240f05290486200315011a000d54440f0180010111061648601200300300c00c1c000703004616900c1c50000d00141c140e0070380301c7e0344000992058040d00028003289072801e01c1c070000c85a00c4200c402c0b1541ea0010709000314022054259100c1e68801520a4240f1749591001d1034035112b12401030004643c1110b186000e5039402d81d14036441e00c40c2c01e076582102d003c80001e54581d0000c8648440d070000640385907039285d02e00a4003560080c0c4007951402d14094095010314003034803540383c054440b41c0f40e90307040c00b5640d010018613031702c1080100d4150048101490028807244060b06074a08a1624951900d042c1020128201318980c000d40403c00c0d104c0c0d48244640f501c4810940081d010b55038007895503074500f0000d00c0c2c043c000c0c0071200803020000d200c3d9041c8001c4d0740010240c91003101514015140c100c0c0740c04410b00166113140150b000100012201822007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 544666816 1250 544665566 544665581
    0xe070503040302151f140f0102032502150f0d0f0501050a030b040212010e1b010801031a0402030f0f0d0201150501081603150303030c120917090a091a0102190510 71
    0xc000d0004101126002800c4503c4107074010b8086d02902c100c48062441c012030f01c024144403e10080d41000e01e803114403200051000c1c541081e8545510f1200f081d034550b25000f455498200c180c503561480190320401c002d9000d551002801841d001c03498012100b103000715812a0030040141c6000d030305540300d107040e40130054801c986c41020b6140d000d000500c00c0c01101d145c0c0101001500c049920014a01a4008041404d40c100008040140001003040340642150480b841401d0480d90b21480807a140c070354241d501050074460310b50461241c241c002003034000b2040030b500901034040400f0303406a00c641d042c06200e0100354914001460401149400c11803680c8525000c54411030310201e0742032014041d00241d0029031255110030b01c1d40d800c98100c0b420524001c01c10000c251041c1c45100d071004850032060b201440000d18440140e0b41d0b20001000742c40c00800410515960340740e1b07018185400702c24079000d40904140700d040c0b0014080d508284c5a000f00207003000014a454001c000c0084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 544668066 1250 544666816 544666831
    0x181502010e06090a0302070909080d0902030f010f231302091e040803010938150313020a080601081213081c02010e240403030917040e07050304030215 66
    0x2118a0714000344030400c0483e005601003400b40402407803e05000b4100341d0703642c02540c1481e0a05501d8030000ea45c070300c01c48000d2085c0b00790000f050806440001c0c1007100100c0329011135800c04c00e031050007400e81d40c04a031915070b004456842054440b0f10045468500f10748060800d03001c015000054248044210350260366596240200c040d03000f0460320200c1c045d0b500780c40724640800140507012240c802c507107544014540210a03449026441c161080e00e107400d40c000c0094030341d000c00c070301e03201c210340340c1c4600c1c100304a469180c0c5404c0804050a41c5028000c0e4400c03414540b0025001201242650690b150780740588030031100d11a81150550043d15001c1150050000c0001d9510b014800d04038000d40c4403103a400700708002d2a0003400d42d00b01d0704405405030002004821801042c1c000d03c44038034100c00c04030a40380c0d1641002d500078062860003401e0384c1a000111880e80d502900144240da0017202c00e00d4080e1205e20781129603010846008015a010305080300394140c05840b601d501141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 544669316 1250 544668066 544668071
    0x4020906040302030607110d0302030114150c031c0605010908060c03090c0a1206062709050f01090305041509030305121005040e01020a080c03070c0311010f110406030c18150201 78
    0x30b032640464903140e4101d442c03400040e0030440c10110b4850a00c81c14079522060b145c10350655040400a040612000d1034145c4105104402c1c0098480b031241078410380e40c9000c056944aa1403002c00c1c0443c10512016001c40350b103407200229680d03008080d1442030b5241d2100610b410f640d000401c1c0c42640c400303009140c0c1403040942c00a8155201d0f040301000e0018004016900d5440d49410810b03078a5a8000c1e401c0c010b00f64001d20300d07640390020303c141c074001c0b401e901140880b02420314604100f0b044450326a15401e0500131000d241d0800000c00440c0c6665440c0000940c00c018100e4030340550b40801000030300d007041203041c2500c51a20190b040207120025002160703503000004c080307c0184d01d8440160350081402140c264001008550020a03a0000c9107940b40c0785100820f80803545d5001020300001000840d40400258000c6203809188d81d010080301d1103103c107412003a0854801e04c00060304210001c8945442511426a0030b41442c04140c0c0c0ba80c10211600050010300c03080204566 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 544670566 1250 544669316 544669319
    0x11030c060601120b0303130e0f09030904020a0924120b01020303010308070203030903101e050906070c17030a0617030702030d080601020c0a0f030501240312050c0a1b050315060402090604 82
    0x71750600007000d070729a00064040a00346003072180070001c440240034100004101c03040061156010040ba690743c1c0c412a00181da803850100207540030340894100a50440e10303d01c11101c517250810710343c26401038030340b6400f020340c03003401c02442078403400070800340142c0061004000081100018061542c0300900307481c1006038031004241303407170a2107104108031922007118501036640c0318880e0888a13416101484585018902c1c030355240c001804030303400c011080e404201400701c0c0c138003050940c041454040765603041407080e0130040c00403402070004240400100032a983ca0000c11180c61540c0a80a031044205220082c1c441d0100101524190f0082140b000300c50b40d194881e55000d0075154401120341742c114144142107803121068100741200d001c04100c1c109642c160b107101140e42c4200000f50303085580c031003140c45001300c107260038282c803502c4007420400820322404910040d41000d180c1c9039035516400c165075800001c2d00f03581c60910f1b010100308141003540050034400e401801c4986440e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 544671816 1250 544670566 544670569
    0xe07080c012f0a1209080a080f130e0402030c010c050a030c0510020409090b01050d02010504030b071e020d080c030601090303180302060f0c06010b04030c1503151511030c060601120b 80
    0x148503000b08050a0308042c440c1c008102d0000554100b481e45494003020b050f080c40400c5682c0c1440b1800a004c0d0000801e05849100c43d03082112540070a800620030000d940340d0440c1c2001d203060302c0813440303802820080d20302c070b5105018800605820038000c0c5600482c0d91425100c1941240007940e01d406040c4001a03031405a0000304010540c54000040c1d1005504180d150740c0e406030080c510829481420310050307a8417800750303420f0340e41002c0c9106240d156168141d5942e01c5111131112460481d0300645e040b1500450b070301d60b03201000c5d102c04c0b0069a54416005031803208030b03030103800318850800c05d0010134851917050208462001700220000e0300da8002590a03040300300c020401580000d00407803c1c4005200309401000c0c00310489003007500716501e10400120a005450700300c2d01405404209030b01c02e420201d62440340c03d9645524946940c860b0100c1444c0b200b070711000c6500300346420315891000046071000c00c242c00c080c1080f0785428004407400560840030012403a215920841107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 544673066 1250 544671816 544671887
    0x40b0417150c09010e190806090f0d210501030b151f120b091f240c020d021906090e0c0a0f050c010e0c01030b060a020742030e07080c01 60
    0x29070881ca902c29481e19002151342340c60780081c940200d0b03401206860714038010004401e1418022801c1c820302c5c074a41c00e4145800f5801203103d50304114145000042408400d100761030103001c80e40c94528010600d4400d10000c05441c000001c0a031680c0004031003603a00c541c2d2944114003241c90045041d8281600043e00200709443c1d00034030b02d082d50004011528400c070408018085020400c0d051103104000e5040014040e40320400d01c080758070003204550703c01d0184890583e0040403d261300241c0101c840303003184a40212008146028008240d0220b650401841816043c42c114a84440b080b400c441c1c003003804a001060100a00c041c083d222420300a100030902c951004140300c5d0003400005082d22007495070b650060b00204603040c812940031a5031020794640340319007042c0003880c5034550321242143e814101405d1907100b01c41c2c4140840004040152107036030b4248504d07007446540070340b15070143c8281c01c001c0d40603c140c11050750103850314800f40403e0982603d11800f2801c3c01910 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 544674316 1250 544673066 544673089
    0x403080705060703150f0b0d0b03010c11160e04170412110109060e030307060c02070815010e0f0c0315040b060a030b030609060c09012102040b0417150c09010e 70
    0x107440d000b0004000310b00b03a142c071918007540144030006810514144109404400500822070701440000b07882990350711581001940c0600034001708039143d95444010040004140d1092040c048c290342c0300d50000c904c0d1108816104c4610307010502d91141c2c3d0301d5003038940b0210105251240d0600000500d040d0304002d464005000d00b01844440c00c401d4001412079480c0c6d00300030107000107204626020745000041d0384c0b00c25032200300010100040b0109074580145c41c0e121140703d201364501d4904803940080c600e4100d0390091110101a20744003414102c41c01c0403600d00b07140190a00004007518110711400c0003141000c2c000189143c6924041100d50307000900000200342c4400174001c503810700b040749907030110301c2c0300103407009080034620424584901c180c05810840c0030360b000c0042350210184120180000b440441d40ca81c1d880144440642081c828a46038640d006003584080c0000300355295440c1892041170031550702d11003c0225500f101c40440d0411100520b03e140030b481d00c540301c3e81c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 544675566 1250 544674316 544674323
    0x10e01080c0306010e061c230705060f0a080c070b01032409030207090e100c082203050d050c070b0703051609050d1e05060708040c06030c14030c04030807 68
    0x4066051140c5245040c07480c0101c94000e900c541d004202a400010070705800c15001c440b100c80c1c0b121801c12074400e041c000c2d440a442c07250760b07410900b00c106452400304e60b40d00f9000d0030358020303e94400c01c110386405134941c003501c0c00b00104424800305120b401c1721641300c5e60001e001420103040342c4603c1c3c01214240c00840390506610245581d80f10030180c00d10200d02030702d60a002030f07081607038000d403510300e14428082c40c00e80341c00b074200301c0300000c0c8901d034450f03c9003d508004903101c000f0010858071056408d441e5030f0b003c0d154110781c10006403a00f0150a50541c0300c0a00d0030700049200001400020400003019200b8820714000440651603540503400c5540e01103a00d00b0710358800c00300d209507181844240805210200301e507440705450080c003d038002581100000002e081c90400b901e0300c642c010b040b4065a020400d00c1504885881e000b14041d003c8441803580700e490a034116074500c0b5909001c034204c4503401001103009002140c0c80b81b56a51280c0c20960760341c1d100240c0d03801c22074049 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 544676816 1250 544675566 544675589
    0x30c01110a120227030a02090a061403030705030f030a09021f180f0e0901180b041a15041a060c01020d1505090c0a02010624030c020d0525060501 64
    0x44226644002c080d01490304429046103081c0024405030904908608100b194007100000300700242c1c2c05101c80c04a840e00038005041529100c83c1c000c004103401c0c0100c1c181c3c2c2407248510b90b010b08001007940d2440394840000c611707149443c0c81001c4650402410f801c1c46070785814184005032500000341c1c846518000c5010010031920b10050090480e859000000c0d4511031420031009407610200001ca440e4060b45822913111612a64050035683c2032825900d08414110360801c40800310b000c4c400c074051034101900240342e407d0309100c0b03141a40d410a91a0401803034209038541584144007480d03201400c001c0403000c074808500141c0201c40c40040c031342d41c01f10f20141001c0090041d024419070010b0905826030512000039041d22002d0449440d5003408640c5401e400d0007540268003420806412440803600151001c641c21925074190f400241000526010b85d400040c84c4144104503444e1642070850800d04a40c4401e04020b04103c0340c0c1e04940c4130b00108089210703450280c040580350 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 544678066 1250 544676816 544676827
    0x8160611120714030624070b100807080c0604092a020c030606060903030715060b0d0504032601050d062403031e05040608060f09241e0d0302030c0111 66
    0x544040c103c01114685080104100329184c0d840001c000c100c01c0200190407070b07503a1740c103800920900894030014540303003036003043c06100b460181d03409044401c202d088605007a11005869110010500000d803c50014130041c0540859070300301c5140c010088a151844400100b401d0b01d8403980c040c40140580c00c410b07000c00b15402d0a11245900c00020b6468500c6c1130000004a641c0340f055000c050116511607150750003510302078010100400100c08020344404001d1548001000e095504401240e100c84410211601280c0c814040007050b040304012603190038140002040c4008040b0743c10307a5640001c0c8501145502c10808241101500d41e021a0440c41e0180401c800020020000c2c40b170024025500c40d40b040c121802c0d542c451800f0086900c855001c150720002d0220019171280f0105c041021503000508022405040c002e00c00d6940e02c000010f100a00551081c50740c001000050a00c1c03890415072180b01d1142e1180c4100c80c41c020701c0a104508460320501b480c0b450003000200b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 544679316 1250 544678066 544678081
    0x14032a040c020a0f240606120c030506030d120b1306030521030a0b010c05010219120b0102030f0912121309020405030607030e0111070309080f01090816061112 70
    0x4660201c102070008103010850b83c0c48803045072500c400002d1041859400c0c807190342c120200c04411100d8100c0b41801201d490760005440c0d03184c240501c4000600e8500c404200d1486805940e02404014019014240030b1a030100c2e002c04010840c164460b07114a1180015200c0040c0a10410381c845800241310b41913242c850f0501040b0b5200300000c03aa02000c02100001c040c1c100d0781c01c1201550001108040c120040e14050103810014049501c013040c142034510207103220030001c050703031780d80c410070201c0000241d41144c031404a038900503401480b61600e851214401040041e1000b8100500302c21108815840c0c04800c00c0c20040d0603202003484200c0c0034402d0041c201030000c03040154206810500800d9481c0c3c0f00906100405460380c80c075040c80c00003035110280c0e0031000144107650701894103001d40a030003507210302c0e440c0c1d100e80d000c41580c4080620403001207580c0259034500d042500c0c0400c240804c10040165030181c1d4804080703102840c080b00510f403220514403000047d141c4000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 544680566 1250 544679316 544679321
    0x123010311010305041e0f02130e06010602012d14010602071a0a1403071806050919050307030f050c1e03010b0d0302060703020c010209130905070f0e0114032a04 71
    0x301c0342e042c9410304043c440043c0d8450070114140188030a0080021079a0400701041c03000a003001c0c1d00700400ca080122030411f40d800003003e803241c0400710b420b182da070384000324200c2d10700c0404220341c21741640320740041a50448130411440c4400c600800ca1010800c40c18010041c00c2c0d1050015070300543e0104009070106100e0b00e40c1c03000d600c0e030031030401c00541ca018082000c0d2641c9a100300c400000010f004bd40140340103458806105d201c200029100e810103000d50388121151032207014254006416030308424909002d96001902401040340740d03603074000700c003640080e00321485e000f034400c1e11015460f03408101c00800d5480075400400351030041803508441180004030301800b61455040c0101c1d80029295820030450b10300140c1c1c4078107100c0c0090081c02111080c0b54130003d00f0707110240c1d005164105038001d50241040e121603542d24074800700d41a01307a1103000040b01072000100403031802e44030201201c0d00050241c0b150007641250544030108144d101c510170710240b100035040f50030b01d403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 544681816 1250 544680566 544680593
    0x1091824060905210601060e0d050d020c030c03010e2517030d18030e012708030406020127060b15030a270206030c0a09031202010903080f01120609030201230103 71
    0x442c1c864003a911030144c030a031607540c140a003405100e040046214103880e1608884105c0d40c109c1c007628190402c401c0e0007500c8002842200d8443d00c549884001d161034188211541a4480310003411120003103241c0d54080c000458489144003009000050b5120185014502c4000c01d440559661042004008101c46041c04980c0c448887ea80c1c0c038000103600991921f42c1d031007090a202e842180221030b5036004510b480340c030b1501d920745044002401c0d4400006081076420940080c0082d040c0c680303801681407500c0d008164003140800785140814420385c80126111005400840b00c1c00030b0800400c0e4075402503d800500b9541e0720060030303280b5148000b010640b0040c06200000030059000184d00d400301030040d01c80c002c000900c1c44111405020054011a4400349041e5400e20a03c1c01034028031540c103083d0301207032810740098901c40010300043d058072040368802c031a0221a495540041001103000c4040d59030711030341d42c880d0030140c1c454210ba07036941c000345500a40c19454544102d1000c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 544683066 1250 544681816 544681849
    0x6120a111309020d020409080f07060203041a0702120304022b0201030c0306080c0f0d02091905060409080f030901110301140f0f011b0f0204140a0b01091824060905 72
    0xa0101e030702c0050fa103110403842c3c420340441e80464030403140d0619801307902c81d843c4105091580061075404000c5942c0240d442213004209d02c3e080740003c00d00c00640400122070820041c1c1018292004181050000e550054005004051042c0211030218112a07241040445000015008904542c2d260049000309040c500d4144130b01c03031920248039650554010554070400914800482640310500d5001c03107540c0040c20441141024541c16118000e220744044040d42400005080c42c2001e0003554440d5a102207003900d816018101c44003035400103003411180e5502c0e21000043c8142c5007001d075000c1c0080c0c0b6075012480c000c18041111800654400318050f4601c00d650f10510b0780c119019018030360500094540c1481ca030f103007c40c284418058001c1d030140c0350890001d5000030050700b40e031040c0303d140b2080082201c0440152610301d0b03a0b1080d02c1140300d0844203001c0f51092500040b036500000100b40c02c6050740485400b9000407203402490018043c6201040350b032800c81809241c41d0f04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 544684316 1250 544683066 544683071
    0x610031b03080904091104051315021303140a0b01060207081005010503030403080f0c0303010603050604060e060d08091c0605040b060d0c030f020f0d050a060506010203160b06120a1113 81
    0x41c6035200c0701c4034041c62010038807695030303800300c1001c2c41903064004100100050007001740e46004943c8c541046011340050701d1445071102d08607140c001510807100c0e80c82020b41c0e41444289140e85210981d0484110440d40740038803140480065074045140f0302a1449401406001d814400c12a10300716111402428035401c0400400007514080f080340d05032034005003450350340d1250108a100034814620044840c1c4000000001c00c1076041d8007450184a08440a0103007d580343c2522002c0c85003603e44681c044000e000030b50001c1c020700010700c142c0e14040e041030946036a12004c003500e010804020b03a003031a00d600403c41005610540e00d81c1c04441110400340d20940c5864048288940c0d01000f0941703031004c8200400d41da111020304011460003821085800f2241c40d01316122482c105007101c0282c10000828030700e44c004002d584407850620580315800407191965180c0300405020b858002001041e50050745a05014070908030f0702030310642d600100b00405000d4810980441c1c0d000b400d2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 544685566 1250 544684316 544684319
    0xa080103110a0e160215070509031005093d0e0f060f01090203070504050d12020c030d140d0905061e060f01170601030b060c070609090203090c0112020c0610031b 71
    0x2802100d40e8000040b4200844035441100051b890181c1c000d400740d034421490340030030590651000c0248500e920a0b0113940122140643d01d5054503c00c2d25070401c25000028401504d10f414030320ba01c40880d6580f1884606519644460000003800120084068884100e490840d004001ea001d8010362403004100a182c844001c1d150900103000c1d0580380380e000404580050b03c43c0c01524041d080007480740c0708207101da103081a25000300b0901a005801114160810b6150124101d901c110343c035115820f03000c05c13140d1002040c0c1d11140000040b507960740c48000c04204e080100d144038070a0600038010482c113a020403011701d20004e241d18450b414940e01c100060340d02c4084021007404015018865440318001603002d064403d0320150040804141414007100000c2c0381e5040b02c0c941d480300c0d40070035142c0c80c0030303c1030784422549040c035680221001c0000d54419042404003000600c00141403400403105541000b03800e482c40d107404c0ba81c1e11018000d04c01e00103540174295a00344030b0000e406 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 544686816 1250 544685566 544685579
    0x509060108040f03052104032c0427060603020a0f080a08212404020405031e10020d060f06020a11012007030803010608070c0b01210204020a080103110a 67
    0x502000300300903e0403104000c1c02c402c2500510655030454040311110b040c0051100300010451000c45080d400a0101048000400300c0b0710740f901000c0d170320000b040103840044024040a402107603451402e000c501500030950380818124a400640320ba0b002140440ca1401006a800c14a421216808200c1d00040006510005038140f4aa40c0300b102c040d1038441d00140c0000740c025851440c4171074000c200070060214003e410b0b0600c905407a000d409150006c85050104a000f20f000345505a885000c4c40400030414481d44554081c10320125090b07001c095070344a0681e0020703040102015159401445151070660741000a4412403004041d19800340d150440411000b88120b410b00800035950a60040000781d1403144022220449104d0340d03a0345845051540244503080000e01810302140941e4480c810458000340c0210704180141d003070043c41900492a000da90040703040c03100540c00181c54900107001d03025029140c1021030340c0355007400300e4004820030200344100d100314414402c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 544688066 1250 544686816 544686827
    0x20a0618061407082217030417030c0d020a020307090506130905010219120c0f05040e06030a140109050625030b06090402120702120a1d04060e0703020403060605090601 74
    0x221401d500d00300d560310500916070441885041c5016011803400102c031540b6081610342821310001704261801e40e581e440214407180c03202c00105c808070f604104005c00030300a8080910340c510040780c00f03807807606261704c8415282283d4210200090780180050f04258607090108900604201805008524080c1c0004203c0303000c000310705450a03030303488444007400000d60595240e802c6140041d1202480c40c4005010107203564940c0101c00c0c00c001c200680c80c1d2086070350342460302168071000d003014202090741c5012000104607580510900320380c0e801055401c2c01c2c0920f040c40c964000204d0110354107006092100c018101501e215030b00b85c651607070481c51002d41600000f40d1a001440c0d441120028040d44921039405900074004102151291941609140540c0e078980032202c400c400f03540021694060381990101044100345030004900c40110b00c02c280500042001450903120a103142007204196403036800207030b0101d0140204003482c40b40e02d02400c0304848081e6140b82c4200001d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 544689316 1250 544688066 544688069
    0x10e070801090207030e030d180f0501170901090b0c03010905150a150e0a0b0a021c05090d1506170c030a02060d022203031e050a021e030705070e0103020a0618 70
    0xc0301d0f5030000d4240c041c10721a000711000a01c0080549003000c401c404000c01d801c2e0480c0351382c4079598200c0d1002a2520200c0f03c2d0b40c08588044c0c65401000b221605510306922000744860440e540b140c405d000040c000c5091288180310000855499505100b8400101c2d40e00406910004988800502060344d9034081a0b00f11240785620b40341d0241c030110115045644006000c1e0000281c080214a40400d02d01401c1490401c1e070031194240707a0340405108652030707070080c00d000c560304100014080c100344100c00381e614051407005403a40c070503e00c80f00c1154103035882980e20f1041c0003840240408207025410719118110300a00ea9040b0540000786280b040341b148201030380d400141c42c2ca00466107014854a129402038021040c1e582e420041d200742e0244190028503d21002c0d40074145000301c5c1920208a010342c001c107504541102030ba00300d101040b01c0c840c2a1721007030010500092082085601918500c1c2044501c3d500d10310502250311515007200b07050241c5251610b0000c42095601c0d070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 544690566 1250 544689316 544689329
    0x3030a0c110f1507030f0f090201300902010c0b0709030b010503070302060f0c010b061201060f0323070e0d032003070b0c071506090b0f0613050103020f0d0e070806010e070801 77
    0x10084c2c4c46000c0183c009110400d0042400c0b810b040c140b039005a46640105400c500030b07207a1107421031015903000704103400212101104180400031100300c1e81d00360b000710f80c19417040c1070a8003032004a896085010034220f6003440019075001c024005c210001920900414007a030080400908590000300725001e001c00c803040e1050701040032100e201e001d41200d01e1511010b003d5030380d03d000f031607413020350352302c00340181d80108484500d0048864428170526119800905c02c0714801000c0241101140340040c0201c4d0411648009030360b002d5441e440c1c044001403081c4c454034800d48000211840300300840d54501c1c8141c000740503150200c0c60300c039500d035480300d141d642b056911f00d1a45402c07000405103180c845890343c6440030115002a0a61005450a004440003072000303034103031f042000900c42c4884000800000e99001c00c8154000c2c1c01034203110311850340040c1400080c507400000c640801d91941075603071020900308142c82003480454050207a551090003103151921300a031540c41c041c41201d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 544691816 1250 544690566 544690603
    0x1905090f0d0f02090c04240f0f020a08030a090c1508010501110f031b0105060a0503030405010f0e040c201504030c06021201090c1704021c050a0503030a0c110f 70
    0x84041112841c80c4641582d802458101c15080010700c5800a4101c3d00a01035100407080318007441130340d01d101260001c7c507079541e150b084400387c91003104d80c1c6520340c104409621401c100301e0002078050002e58031600600000241e600c419040044016100b5030200c1c1141d070038011201c80c103941c011801815a40c003070801c01da007561101d00c010728280811f921091140404180604080c5a1400c1e441ca1041102d009000c3c50700c9103010450f07020258803915505500030407040045500400c8036000100c00d50400b102d14250050204083d42d04101041c00000c05590f0700c4403040810001d07035410382c85030030004c0c54094150b50101180c2c40000c0c0018040c0907400860b001004003c0d0120b0b0801c4141101c2c0003401d507903681c43d80028013240309494011910785484000001141100719100d250028040003034005031080c00e0a21080e00350043d601401000000d02c003041c4204010341c0665004040011418010340e001041d491084422426a420160a00000c040001524101035090075030340f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 544693066 1250 544691816 544691839
    0xd0f0212040206030705160b0708060f130506030703060f090209100e07030b040914011b031a060c19110f0a0602030315040213080a1203110f0c0c151905090f 69
    0x2515140102281c01f0903095030142c0040c100010740d05014007565681d2210441c64407030004005012aa10303121a400c03005407800301041c0d402c80c0e00802c1e0444c0f4041c0683d103815880b5200c0400f920112000d0010003610b0b100d000c011400c0048240ea03004071050281c036180d038140348000016900180081d001c0540702c0e121a4090b41d100d40c041c1070159403091404c2065200c0104150280809800c52a4001e0710142c000c20388034044e00036100324002a02c11005440710304401c02006401c6000300c01503500c03035240b0b440030040c1c40210315440c850042d800071003070b0080039080001c000000c00005000f0351003120204011600001078980100d5100c80502c209141c000105d0024050103440c12402c1a250000149200b804034802085501804200305010807051041c2c050b25a0a5483c210180082100e0640b50301c01801501480c3d0381c400981e810803418000080311000c1094030040704140001d82a0300541c4070301c1c107010f009109402e03e10700700281e00340001d0040282091a6005a80e440340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 544694316 1250 544693066 544693081
    0x302030c041a0d141006081009091407030b0109060501023708041205010b0307150807090305030a0906020c0d0b0a02070503160501020304031101140103080f09150d0f021204020603 79
    0x9407603d008805070104021801c42074580440242900c500e0244100c00d000460380b00d20541078a841510a214581c601034a0284000300500140c4000e880e0f0306580c2c54464607400c814004a001036018801c80806941001c200030101d5a00d076018505550140145140004184103c6800a000748040401a05408088840c0f81c01c100b03e000b4215040010041400391400b18183c2041d13029000811183d101541031680d80c80b2a40150b10f0440700700003014640703e100305400c5a02403010700d04000610350300d41c5c41c0c4d451500459603040115402c081c013401001c4d4108100031021004442038103681e0900d444003548a0405484612016000201041889030820407501076030329030001980c0001131401d25034000d40090320308500023144640400510030b0140030b144410022840b503c001c46e480c5617a0000664407210309001482d80c1445080c00039914404411207032602884c0071941ea070307200002c07442140c0e000c3d803030b4030485803040c030a0014800210302e07095805513041e5032880d56602c6494 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 544695566 1250 544694316 544694369
    0x90302010f050a0345262106150a0e36010306150e15040902100903060507091802070206130f0503070617040f1712160302030c04 57
    0x100a00784d40c01140130002103894500c09422042002020100140a0b40381d5a229640c90942d4041c20501c12140007160a90030b082041c045032000414071b600d0604140e20060030091900d01c1c508665034468100201e60600345e48003070030328140300307161032505074410070143c05034030304002c203d02a0504400840c41da200446824150301070750120207102c074020616103020f942003400200c0d10541092039007616442d49a441106543d083c204c19011684e500e40ea01c603030105407003081d692040d04d408800002d030b01c90020450f0341c1007041c0d42d242c0c00c031420b40c109441901e201030800010840011400c10800340007000302d00701c03d41082c40c05070b42e40c4454000906140900c80e61900e003103e8290001603403041c00c0409800f01d81045d00ad651080f0f999000035102c000403c2040200c0082010006000401d40d00e03400001c24420b005504040002407000c50041d00300c0c18200c1900c085450a0003101110380340c3c0a90545000c0ca000c3d0b1451070000707403110040c0620300c22103011002d01250b1864004444 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 544696816 1250 544695566 544695581
    0x12313050705121b0a06051e0409050a0504020315091b0d05030c07031a060a03020f13020406021f050610050706060506030a02070204150e01050d02010e030616020706090302010f050a03 81
    0x40c1903001d294200750f080394855200c80128100001ca242c9400d03242e04200d0031201c2100c42980303901e07080903101034055034200100e8805580d44503003000045800115841840c6c01180d0030b4500145618140c0f05140c035108031041c8800e07022128104001c040030340040c2124031007101d04202865003080c0760101e02d034032880c040c0040c0180030210f03660540d481c000a0080842e4082c0c06440c4010103000e041d4038440d0400d403020740c0c015801150620150626074010907699101910f801103007070004d000502260804d40003d00141c001c03580100310342007803000b124030701805000d00b048141030140c005000b00550740000028001c001c0b4400c0c0603c002a803252000f410007404481d030341d24007120904025403120404030712070340c607203420038140b19042c0002c0001e5550b00c40300d00107540d00380350800802503681d980490401140000c031824035142400624004c0700c1035031003020003c12091000e800c02e140d82d0031045c10801907000400150b030780021080d80110040c10016903600340b96a085001c0c0550 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 544698066 1250 544696816 544696819
    0x6040b1e041d06060a1203080601260c03010f05030304120f02012d0801080312070e031f0207140a031236060e03040303050d05070c0c0902030702012313050705 70
    0x803070b0920201403408640305108410440b588200c241c1c80d0b9000c60141c0e4005100580051042000507c2c55406640d001050705d492a030070b034403900303285940c80d88045411984508100da001c00100400c00040440d5006007a0890103913040030b0502518410440c3c0400780a0140380040b10072005590281d81910321a0a6003146540074003004411480e0442c0c1e040c10074000210040c0000a501c90080140c1701c10001c00740f0300c01265107440c6403c68a0240b4150384a525000c3c24120794824000c03100900301c550380741da1780507803940c143d81003000c0301120200011400d5004411044002584491510034a40c540c2c0c800041040320f5084261105000d00740300c400608004840c6c501c0f600403035a50840701e6114000074051900d803008581d40b00d010b20b10008000c54014000000007200d2900040d42c050624580040100701c42e0b103615a0720314450340200d2000d540007090045a9a080c020500c1c0d03810790b024405002c100385120021258402400c12401440c0b07004d00004011040c071000008020 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 544699316 1250 544698066 544698101
    0x1b02011a09100e150f54150906030a14070e271b1e0301152d0e0a0e0102030a020d06120206030c0d0906020414010806040b1e04 56
    0x44c02da070100c0c6849241e202c81442100751030304a416610705842200d0440c420070402c00300c1000e104000900300d501c2ca410b2140b00d80501e144803e001410b001701c0e48600c0100c9406804103080c4212540b02114410b50014000c0100f0f208000540d10300040c1c030b42a19038490300000c18600f503030800c1c60910003250000118010071a00b8007a0310030b40003211280904004000c00b00c2c485030074440c01e0340d5200508034141c1c0034002d4220010b041c54210008090380d200601c0c130401c0c00f494980024211007d15200c0c1c800e101e5402400d00c0400004e421f5030064880e05400c1014617484c0c041100b000c403103140b0600000b03503410701c0003071810308068004030000340030040259164141421540d000e50880d6007001070300da240c07643c000740c0a5008846500c041c0d40117030080f403030b585a90b0039800c60741e88003201c1d10804544039442000040c1452000380028010b220b5030104d94101e0800051142001824141c411824541001c40580d10240c01a04280000e5242d003000c03044c1c1e40c0170601800350b161030240b00c42e5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 544700566 1250 544699316 544699321
    0x40803070c0309051306180c082e15021c0203031603090512250b0604090c0e0112060b0f1011010b0a14042007020d1a09011b02011a09100e 61
    0x9410b5003000081d41c60b41c01c1c40c80031003461a05107d04981d18034803046d000840c09008586000204612408289503204600003c0d8001014800c420308172a40107041582c0f4500e1101c030880d90502003d4030705656051840070103070295500955a000c0641035010440084103680741c0b06020b54415041d9592100c01e1b42d921b04d015203108007040c1c008a00d01c3c5640f60b144924510300c1407403003008849a42c3d00640384481ea8a980b800d110041c4084901260004103002c0041101808103124500900328000101e103230751511b02e17014040c0e0b062000e0b9107000701c0d030088030404681e070340084103400c4a003e80b900d00303200906544528003500060010981061010030085140c501c461001c6036403203010755050010100e17041040d8090038449a00080041040c4260341c0149007407800b02c00e60a0081100c0c180d11690030300d410b003030f041081e034821030681c0d910201c081619540b034035515942a05c90000700001600548801b0320f0a0782c2500d82d900c242c4038000080c0621086009103c05400004c5520780d10340b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 544701816 1250 544700566 544700599
    0x114060717340c080c010926030c0a0c09051320061b010c02060408070f06021c0207021801230402070606080d02010b060f271c03080906040803070c030905 68
    0x480400c05450011100e00c020482c8100050514000b00c0c061f5181000103142460485951409190b00400301030101c440c1851210108094419607020401070403061085140203688101c2c60351220411504017400c00c0003080700305c5211049190072507102c9040891840c040c6441802000c1580d501020100f42c000c10862281001e69078098444004c01c01071402c800241da0380c4034111001042e250003000804001298040304241d0948250005420004c1d4180c1124041c0143d2140b03c010b16804a0f00034254601805030b40c05a20b1000203403005035060916a03e4800b076401076004403080040c440380300586555044603209a0041c4c2c0410200d40c40350346a6440d030400802440041d0700b40090385000c0d18004c0111b80901d0024084075180c8031041c0509021080104054284c0f8403582c410310300e00c0e4030380340f160303962004020107a0b10030880f06240140c40d00d44080e095a8441d8402e400700b0000034021002c5179005146400c10864444442c5001c489848113600130581120180e9002c0041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 544703066 1250 544701816 544701907
    0x11a040605090f030f210f030c13030f0605090c01090e060402211006020d020303071709011d0622050601170a0c0602070e0601031509150308070b0114060717 69
    0x50441d1010314032000c03042c10b0790010346009405031107641c86008c2020030348a10915000702240c1d024031003000300c0c0c181d41e603d802148041d821011780714151610308000c0144000e1001001034207003402c1904090703007040000000360200520850103036034001016400300b034422000d00e460407030285042409140c01e44c0d0281954209218000140c480c491494009a0010090720700c9044c1540c2c0b003090211380c2c3c507099500c2580182401516550b1004047d001c1c1a84110301c030790116400000b84100e08000241c50f40c1c211650702403a2204403c8901c400000f080440c03403a044482d808002004852014512801c1c604104c1d002050031030700c840000390041e00030a40004a86100310055220796030f0900640c1643ea0302440b00c0311103402d00e801800007030003543c081504a48102c000c1920107031039070384c0c0d205980e12914084e80c7c42d0491a0040001070501d841103580034a0549009007080c065640d05a00001a0000d4400100c408220043c03954014090140e07c0c002d0440d80c00c11800c0c422505041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 544704316 1250 544703066 544703083
    0xb1e04090e07153c020a110102070509010e25111204180c120e010e060109061d070507080313020a06080912070807022205011a040605090f030f 63
    0x107501a40030000f8511944020011403080140c89440f041c3e81c4030310741e00384960341d800441a000d200d83e400309030040340149441e02d0224825001046502e035941025140180c2c003030383c010704641c401e00080c003640d1502d016007130444211200000007504c03103c9160640085c0c40d44d19500001c207000300d1400a0303500c0340264070081181c6d01613440e80d0341d10b00c140115507c202c0c0505c032441445915041ca984080f42d21602e0f007107110703241100400d400070042c04207640007180d04944603074440e507a411061005000c21070041c560040e080108514000c200d945103903c0c0b081c0003458248810001c0c002070f004108659510380d0180301c1030f40e68503242103c0000040345100130380c0221058840856814010860640100c9504004001001d1404e940c40b45981c08480105c41c40b03d030a1048400503180c140668070071118450040192451802264080701d40503801400c0700030b9007a41c80c000c0d217281c00c1c0882d0180da50600d0590384e1650504003146401c0042d40ca0075415200320850b805060501281d50340e03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 544705566 1250 544704316 544704341
    0x1b031005041b0f0b03061009051f03054206160b1821160b01060f0903120c03032a270b03040201020f0106080102030601090b0703090b1e0409 62
    0x820064032040200c3c0080d2880c02030200c480e10800c00b1803404d14000c00741b086c070400b2602c0c0c6007038815140e402007580889901740c240c1d4030300208030601814540500545501107403002d080d2410402203100070038680002c42d104540140c0c0740b2a100310855440051083c0d1030381c060103d03170303862820301c000400b24030b40b100c0181c604034500800f0400400e041da000c004107501c1c0368000c0402c00b8802107095500310406a1b840e15000040050150700c02d080c0c0172842c1514000d0642c40e010b50b01d0010003601c9010034898a104000910b242400051000d403101344030103441e458514441103003407406800070100381144184c0f8a000c032a440880182e05c060340d000c81540d998421012030004104040801403204090000300c19219050040301d01c400f0155a11600501c111105859800500750840307650b078000e030316107035000010001c0e0b5503000300e0128024490028194074000068a004101d08143e0060325a034420003e42d103000002c198058840d2069510f085036500c43e6146a8400244007201821 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 544706816 1250 544705566 544705613
    0x320708070f06020604170322080d0e0d0503040b13020301140402040609060f0512120c0a020306060d0308130203010b0a0b03060901090204080d0c0c030c06080406110a021b03100504 79
    0x4a0b0440c40880d00a00940c0d000300260b90801d502151418945c05c0104a4004000404228003582e00440d130b220818074010341c15242d988845443c86070641d88200200940d6911060034030b08129400303011640c0c000c0d088600d11460b91655014950040000c1d400030b5499030030300420316040030395200400e018910858081010035624038250381555602e10445002c00e4050b501004942001031130206e0440604d4282ca0010901c00c0c00c0c4a61074111002c039030450760081d090081141410001e1301d81243e0115000c10310390281d40c1c0d00a0034504001d0440500440b02d0040c2d01c21500e00350414000c8503401485425002c0d15070b030550b0010b400840c3d42600c00c02c0c0b240d0001504029034400c49041d80e40960280c41e5a110500c02582d2882030010119003251008500001040c40e4290310b1002d0010795807450600e041c181083d00030f941010201e084028020090751000c1600001d02c00c45181c02000300e040d00b001c594000a0900d01103055000d00036041004004c200403000865000e02406030880 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 544708066 1250 544706816 544706819
    0x6180a0803090105150316030803040602091c0c1a04060309030905040501060302220317030c0403210e03070806060f03070801021201150305130605061c030327320708070f 75
    0x2c241d614500303040400c0d03031800600c0048c00810003800003564040d02650001d480c0020080201d07814500408090103c0c60f0b0f43d460900401c1003144502004000c00085019068460111404188a14403c103c02c0c11340e180349802c00c00d4000d00900380200401001006690307565400600603502c0300400c51291241c038503200041ca1160071311081a03c0d04203850307400c0904800042d0b0394560010306000c0041005020010005180480761a04070000b080e51070080311418030058078002d180010340380f294200301d0060007841c030001002d6501070320031100905800000008282000c466400104503540002601d00340100c03504540343c126012460740010f058400e00741102220303425101140d012020483c0b900120f080d580215401c0301001f041d001d101c80400c6411680700501090031400f094880e104002800c4e010440b02048221801d1608000c8400e07559070141f000f00380c100450300e00c203050300280c180003009816042084204089404003510340484544c2c2d1000c5104400310306119600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 544709316 1250 544708066 544708069
    0x18100504150c05071e0315230405060703050717011e0510050f09011b030309021e1302030901150f0e0a0c0c021509040c050c0c030304050306180a080309010515 70
    0x500c0001c49400001a2548a0414440e103a84c00c1e1458881c0807040088031011010801b13401e12a14103a44031500041c440c45480201da540045448d600d0281200c5041080040b440110300d0701e900c00c1c01c80ca0700041540d02c800301650040b070b5466203460320f505160b00200710340b030f2241090b20806050840382d415031540e40c020461255608409400062014084502250307460005000184414100781e43c40c204ca080c0080038060514134142c0001c1d40300e00128003503007456040381001c5609501c0d10807411500030046170550500500b0a164180c1c0000000c41c0b14100b944481c841901d2501e00300d071000d43c0c031441a84051428040c00710200920004249074481382d10414150b04002e460703014440300140c003007240c0001a0454440d1414080041035025510380c4900048480c241d240c7c56216401c04010615100451007214000e074410441880a9980000c1c070580c044600b081c0394a0f200c0403070a805080401002000340101c0002c0180010302006400c40b510401141517842c40d81c008200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 544710566 1250 544709316 544709327
    0x902070f02041d0703300201050f0a0606020a0b220312050c0901080610140a030e011b08060d05070e07051206010f1407081c0b1503010f0b1810050415 66
    0x3c00310b00c2c082d8400c2d041000020001c070031504440c1108040325003490610b2110089040c24210b5080c0143d65441c10000488100c0d0302c156008500c20204100305030805002a50b6168480406000d040c07041e030000780440c19145806003103c814180f40107401081c0c0c500074014210b0f00b001440540d0804000800000820042d5814644141e41e000500e4540100f40a04040084840420840002101000505a00c1c02800443c1c5565000520030115005c90b030700712080d0b080c221040300d0601031344802141d480340c2d40d5504813030f040f80c0c00c01d681c7c0100d1400c10f00d4075440d40d00c40e00e00c0c141003108208203643c0080107804407410855011080b5518900111044043c918400b00400c030300900061030401a1005003058912078030340140340c00783c0c00541b680c4480c91051659241900c4000ba448141041484405400e40c542151400c0d9410300c0000d110305085806000401c800c0440d14000070131081190070103081006d000e0101d0120325450091860b4050302509007001108051104420b1098 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 544711816 1250 544710566 544710611
    0x19090509070c0c090e01020c0114010f0e15060901020a1b0603050105040c0f08060112050c07021008151306030210090302030d05070215090d1406160908100f02040902070f0204 77
    0x2003c2e8100d407506002c9490010b045111074012659824054800011000d1040e03540070340c46886010320075131400d4825000046580c108081d20007021301404601c1071980c00c1010150012940e443d00c4104004c0101d04e00b5240000203007501d10511021100c120510810000303540c0c1603034080c00540e88420611040e104031180c4a00022090284090440d11500c1e180d034010318141340c4891101c0d1121049400d64401b51106040d0500c0014800114a84201c07107000492050422881f02d20701010078902420400900794000c0c4d40d442c0d048038800c40194089005154001c119515000b407241e402082d864003404200d0081c89002101c032086130044003502c1850b6401000c00115400722211498a600300080e0650885001c06c000000070380131240c2d001101005600402c41c6141c0110b0000c0060a05040340d0140b2841074030600c00c46501040c0070029036680c4101103100040c040100000740320340c0c0d008020702d070710100d81c03581001001444e00212500031507090212404070807181d000750401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 544713066 1250 544711816 544711823
    0xb190603050a15060b0d021b0706090612060e090604030909020301050d020103020f041502030a02070f06080f1008060112020f060306010e120102090415061b021003020d0219090509070c 81
    0x1500c2480003c1403042070b40189268041c0100b88035136100101070854001d2171105000703580208154824400721005051155101c0b401041150325020015200b07800034000c0b071041082c441c000e649481d0141d08000028500d107918a46203107490481140c03524002e48003103002400c1560005070b0360700e40d4025207050f18001008140c140c0c1c080d6005500a40c001e0340008081d505c00e00000405010409480c1c50008081c2c01031951a2085075009092041a4002c8000c5814001050100550150410380d1084803900b412084d512a8074802c01e5141080e0b12103252846090008205011840e01c0840b089101780c8251a401c1d5070321042200c00d0000311940d500103149002d403040e0700d00d884000c516400d2900303800185800d820f100841c05503030390030740021000d01c80031108102c801c1e40003404411407003040c441c84400c50020b42c001482404016600707800c058010400d02100c400c20b60444810f001900101401011100c2c006000c0304864800d5a214078024000110f2003405040d82c0b9042c00c0d0b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 544714316 1250 544713066 544713073
    0x816111801061220040e0c0301140909010b030f0c0a140d0305070309030602160b0c09181f0e1005101b03141b0106061b0611070c030b19060305 63
    0x24444100c0314181c100b001ca040c2c0320344500316803030044029032008020100308a103145c0c1c0c0ea420100c60014404000d020002482420001080800300c00b07070580c110354204452a010640344c0074140c9001d02096840d890303250191001003c1d480e080022614070070503040e00c82c072019555814a003140d180d046600179070841ca90202c4140083e11860040019a201c0d05000b2801a180d13141c0004a0b042a64100c0c0e5075003401e60600240700c6044201e550114020303090b1490040030709c021a4185c1700d4500e803602c0031110800825115100744804044079401d5040081034155240307802080b41c1c405032412400308140010200702401c2c00c0750328080c505542d44034442c03441c00d43d40d45075546c00d903c1003040e41048085250302c0801c0740c41c800200103121140c14600d00d016800740a0500b1502c0d2940300030144424451802400c2044090740380e6800d0700004001a001c61085070f840c80c52140000080c010400150701004000c1c812900704d00460301580c40518218181d0301c20411218a40000b511550 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 544715566 1250 544714316 544714319
    0x806030c011e0302130b030411060a1722060f0608210c030f040303030b0103050c16140a05060405030403050f0627070333180803070c0816111801 64
    0x800b22004a0520246403400528220348150440b40040090308030180c0b0740d82c00818002800031401c11031310045030403118289030a1000e5001740050b00014481003546034400000b4026500500c9181d0281840c102403903820703c01460703e04020400b00c026641d0042ca00840401c080500180f01c845c01e8078441c1d0004104a4107031207031607581d00070f890704104030303c0b08015812030021524090f000440c030a07280810703021000c5c0005415214004e00c00c100740c05007803100b105895021441000c43c0741d040310000c2105404400b40c00c2c20801040000f4085100b0342052008001001008004490054054070343d0141c03071010306074441d64260340d43c65003010702d4150010802c404650a0b00001d500108071008030350f899440c15014032035141c000e11007400564091803401049000d0b0041c100442000308024031038407030507884400c01d5440140058402200007940240603030071a4078016049460991102c0001c114222100c9450004540981402d0100c0b4800e0400094009018481507039104050707 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 544716816 1250 544715566 544715597
    0xf0d1407050c0105220308030412020c06030601050f04090c0c05060a0603110909011d0d11071211011403091e1507110c060c100e1b040504080702040f0c0806030c01 72
    0x25004540a40c030414030b8a414a0120540c101c0e1740002075216001c6203803285020708050b0085184061040c0554000c1e65400341c8540d15001225800324003401c10701d4944940c002d0a01c2140203a8102c5e20b45146440c90a1a990340c005400d061660310940c119041542e490300880181c6456100007031008100004100c0289083e010107079109003000d0002030b6900d02c0c0044280449400c5103440071036003020002e03105150740410f88000746500c3c8001000041d140004075021001e0740e01024000030484855524213a00c00c1841105030890190219180d0a01150303807511030070134600d03006000211400d84441c1d1000418140b403241485000e901a031381d0740550569038210121003000d00d41c0585010340b000d9998500180c14154440d00003800820380c00312040c0100ca171010114a900c0c0c0c450001c0303416019550880f80741000b002e03a030109254503036140582950082d084020350103403c04880d500c0ba2069030b4071064440d90300c1d0355544101c3c3c6072803042c103440e10081c0c11418000340d9144a001ca04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 544718066 1250 544716816 544716827
    0x12010b030a1b0807021006060903021504080a0c0e160512100b1809010e01051e0a090f0b0301050106030e07030f080909131505010b030112050f0f0d1407050c01 70
    0x4640e00c1180415444520041d42c81d80003090b1a020000c141d5440c03e000e0240d6040011140c41400a03200f04200d0341004805421240b040c44000d106c1c17031000450b05800886034081e240105403c07012605095218030b0020031040541c000c104035120260009440655851241c152699039525141d00d456640012400501c800030500681c0c0101c0300b00008003000848010140f0390f83c0c42d034a820041ca122401c10034460300c180e1200c82c8070707840e4200610103903864003000210803040b5004c101640200a02091503520941d00003d4442d2a20800007849030040e0046400f80004800800c016030301d4250580c00c590f03006001d881c1c05e038488041400000d000700c0280d4401c90191034064184412240010800c08080341c1e10f03e225583c91540c13504000781d50704004080042c245e4148884c2d030404659288a000500c02c0d1610350900030810800c1c03000174050148480e01000544140c00e044070485941c60703244004400009030f80181d900744064101064418003903004000d08800500b640045a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 544719316 1250 544718066 544718071
    0x103120201020a0504061b0b01060309020310020304080f0c010b0d03030504051911010f030b13290f010e1201090b07140421150510090507050c120d02041d06031212010b03 75
    0x111000c7c44540c6000c540c0c00240c0d41e0007484079540115042d84203105140c00c0030b1000c2805110140148203000000d07002c41d054131810901c41025989410203a664507000d080f44520042c0c200d2102c0520400741075164000c80c3c400c5028804541d205c1c402d03104138032403080310b1501c007a2040f101c0c0c08209095610402c9210143c1c01e02d0b01d00070529805a50000d88103034a40130480250079503e5400000003010b11428007101030717a01c1615440e0011050200c3d02108001078414100414a03528a28036504c0316090400c40750f1007002046150344a00d801d05000800382e500c0408038464112006102441c01d044800350f84010800011a401c3d0140080511032044c004694002c0c242c0d0000000404600c2943e11402c3c510101820040c584006401220809411441000410000b80d00200c1000500c14404101043c01036900d02030070742e01d440240a05d4000030701c090040080701100025200380c40e801440d0441c10741c2d4400048a403040b207984540e0324203000ba100d10344010002445568095a03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 544720566 1250 544719316 544719347
    0x6020a0c15270b0f0705060c041a0d0e0f0c0906030d02030d0b010c02030d1805180711030c0d08040507080f0d1d2d040b03031c06120b0103120201020a050406 69
    0x2d4440d15401e101e007190304100500510000041090420320408104041c0c124102005c4240f5280c18140e54090b081010040c804929034001541c0005040a91140c01100710b00011744040e20a6561000c2c1ca4004032800345200d240e00101041d401c1c50046082c0c0c50010b402d4004500d05981910441c0c0a0720700c008900341400b40b0075104c407015031400d00810005206039038610640841444400d407852940c2c0d00000d02034400480202503004401318000c0d0000000d0034989880d031111068245144124081904c035401050030800800c1d41200740d903401b40388281c00b61203c0e551100702480e030750203e4080a1409134050f40c280a070540c00f402807004980392101d09807072480b2140c40819502150440012851500b200c1c415094600e0140068141c1d00d017200c0038070200f094040003a590340100d905d012816040080a50701e000650b41c001d1000708504030003698003040900f003000da251000d12041c0d0303d030030782c0c0500151000c0c81842103541c3c480c050b131a8a824141800e1007165001b04041030203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 544721816 1250 544720566 544720637
    0x305011d0a1104150206071e0e030a0c150e0d0b13080c0d0503060f0d02010f0e06070f051c02010b09070c03030f0f0219090e06190f06020a0c15 63
    0x44840b032865400030b01c0902001d04004079072941420b8001d00d080802400b210401c08403100006000d454480080520700292500c19000300d801c038006410144190303030041c541c94441c04001244003a9444040442580d9128101c918403040240602807010345402080406041d00154030261389070b0807541d50354020310039507080002010340c003890303c0c410340c0f1440007081e00401008018509407000c41c45600c01500d540b0701c03515455001170420700c401410501400142c040c3c0d5a0181c41d101d00361505580c10401e90082c0b00407506040b40c480346481c00905c0d0210600d4101504070303005001d05521040007501c130035540e81d1824011511f2500a40040301010f488102c09540896280a1180713032602520f00160f40d001814800303100e1468070b8240300305000500e0420803445503c40380b41341d44810143d51161101615180c1484408425041200401d007040d4001c1001940011480300f5248204081000d20362035110009117041006e680c400082c080401281c1140840002c90b00820001c007006c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 544723066 1250 544721816 544721831
    0xd061104030f050c15070521161b060903050304030204021b100605030c030f060a0203060102120c070e060603010b09040c050c070303020f070608010f030807240209030c010305011d0a 80
    0x2da1a809840550a0350707aa805109894450319252280c0314401c40507034003091030031b003495030340c5a01c0d4020a45100707690303000c04a080b140c40308070104640e04c107441d455403401c03440d03024503199010b11914905150300f8580a000485c0071401001451300b900c1e04100150705162070760303007084082e42c880101d112180060f8900070039190300411084201d4048000301040050400c4145854200c402c03c12920960143c0c06480e2070038408641242c00c2a00c100340541d40b82d85490040c3d14000840072010803801d400500b6100e9400c000c04c0d080c0c10340c0c01054402000751070b190108080c5000a0149201c089410012070040303240541c000300c14085941443e0b0308241400d000c141c1403210550003640903801c580c2603500e109001740b141074060801d50030022117650400820110800090100402c0150001440710500c080c1140e0b00e84201d07560b4990010055140c40210041e400c50780640340684103407265a01c0d1503000740500c0307050b24070b02002c1c0c8014105e551600c0104c43c10203014442d1850351942d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 544724316 1250 544723066 544723073
    0x7030602180a0b07060b04020a0e0103090f020a06050a080a02040605030624030c071a0103050d0f09091503060b15090409020d020913020307090501080706210e1b010504050d06110403 80
    0xc402c0001d044602c0c0d096141c0c50681000d00039581320303c0780c8500ca64030410103c4c18140c2c0100c0c00a410602c01e190000c0c07100c600f481c01e0034a80f404c0040103503009031500000900558000c00518000c10b0642e19840359864041c0024268011401078902080d002e10001d5240d050640e1002c00d42c4c0c0e80040400004018014044215401a00d00c06a0810006460310504c2400b0b03810181e040c00241d1444500d62464035080d0305c0c2c00701c0c5003c641c1004000c502482101d881007071420060b000a050810030301001c811900c80021007440121140303420310704824041d286c0501101d60b80107801c50740600d01340d40201013000400740d4400499016201e080e100000d43c070b4804285208000070202c03411407850f41d0042524003411680214006810803005005160780070550f00110b072194204940c001e00308084801304040c3c0f0002c500000344c80c0581d0b00074800702c00100f05545030b000f002030300b00604a41c401110303284213500130941c00c003025032070040004206610400e0301ca62010307800c0707050649968 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 544725566 1250 544724316 544724329
    0x15020a0c06020615060903030313150212010528180207050303130309080d050d02030a021b06060901090e1e1906020c0706030b0108060d02120304061e050702030703060218 75
    0x10400300050f4440c070200158245050181d5208003030407a0b20300d0030710f28a030b4002544c034880181031404298100c0e84103401c101401004c150000c154842c1075482c1e074600c442e10080c055013489880d01c5822a48416104074031308042d4030500d11880c2440039506410428542d406001301201031070031076400c04c01040171480510195004044085020202d0a1b185c00c0c01001002d00b900a001c007504100c2000720001d400c4801c03601042c0c6074074009a02d03a40d840404400a0150b00e00c2c00700054404441682441004038080d449070104403440211b50342c880000d031048034204688101755600000e111003010180108030041915000110340c0c030354010200407001c0d1032001400f20750003500881d00a0310aa41449001c0c040c2c1014038040201e0711180b00001c101c6440600300c940550481182d00055469640e003030051600e5280031030740c4ea80e55407035004001c44c0e01c2c80000c2c014506e00e6590f944507544500100d0f0f0940da00100101007250131600c50718020360110050030f51511244580704242d07201e44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 544726816 1250 544725566 544725569
    0x12050f1b18271e12071101030902060403060506030127031107031b03030201060515040308070212010c0c020a150e060318010c0f080f060901091a0d0b0403090f03080415020a0c 77
    0x210040e01d10040e100d004615420b0b402c0480400e01c2e00528140e0121240f00015a0b0141d508030206c00c04c1c48000c0e41c0160000c000d8046e02079000300c00050044144802074110501840302a0002c10240c01b01c40c2010300f04002d12004102d4200e95a48a24007292280040c000c803500100151a0126a203030784203071071449140c2d40710f001a080d00304208103154080c46144020001512448140898200201468072460000610780c0e100460501d00350340700e41d002c100707036038003150000c108880d01043c01030b22500130300c00c007284601a03100707000c508026840c9201c214901d054540c10903000101c41004a01e806c0200490100238500e2201509840240108003000c242501c0c0c10b142d804c20880300802002004004844e43c40440d0103006550b105c140c541411102440c200080b0403124009401003110041843c03903114040821003814040d10300001d41c0143d120351910000709942d01ea81cec604140d690711004c3c0c00300000744070030403000d090619400100c00350707032040c0c035000e04d40f5560b5011443d800303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 544728066 1250 544726816 544726891
    0x21207090806130501150620120412080c06010b09120304030206091018060c03200d03020a05040b070c0e0603070317070201091502060f0a0e100b01020712050f1b18 72
    0xc0a0b100c108c9420100c4003103207024020191000812850070310080340720360b2182c00c000e0f001d0340988006110015050707610a00320b90701591000c0d40d6408a1182c5900140c03481d51290340c1100c002d85d1a0200081120101d9038044c00d03803030401d0078200402904005030221001401014042041220840510724000d01406d031221140305135641070040000d084500d00d03004054102c45c079074941c140c00081101483d051840c025135035021882080314240110f82c40400d4440011504408000c042d022000c00c1c2e0301d041540a105a68000406a491915210291070b5240001c00c6240080600b03000b404003500605101454565844e4942c3d08103400150003001a00128103000301c020400c82d095803c24984002130041503041146644c40d0000c02c0004502d055494010b080305034001e014510041200b2500d03600040200c1c1411600c0d150509513810650051f9804901086115480402040c073301a06500010401c1c148122030018040e0030185240d002e01c1440c4070a100c14250044030014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 544729316 1250 544728066 544728077
    0x412030915030c0e0d0c090f0f0e010c0f0302070c1d04050d1107051915020f060a1107020904060b06030a0204030218090604081612030212070908061305011506 70
    0x26042014003440039007400e12041504100180d80e043e40c0c02466003030042000c80d44c0c007000d01c1c5a03180694500701a03038480c8200e01e013410389000c4441c244c0e50004180381502c400a003e415000d203515400c0b580301d2401c40c00410503840c4071603806480380e8040c010b010f120701501030b00141c0307903082084c1c02c0003c0200960380e16912410441009005d100075448600503080c01c8200c4081500d141c0c1c1c8500450140c58007551110140c030b11000e007241403907401083e81001c46582d880858030000c0d16254076558071040303031182e08086044031000b41701d05c480802120716918140481d603420090000000781c010348203036031102040506a50742500540c0100c03503e180041e911480c6105012100024680a02111107000c0c2040080d150106006034415070000c0010703a00c16140c0d89031001c114644030041c10b129000c3d0103d00802d40c156004148136811001c014446075a500b07000c64150005015214868114401143c01c0404203c0008800c0744114004100070030055001180d007101644014002003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 544730566 1250 544729316 544729319
    0x300f0614060f010f0917030705070609050a060e06070b100f0e04211b03080a05060301020a0e0f060d02070c0e06011e080c070b0f01090f06060c150204120309 69
    0x2240c450360000003006010218989080c0000411110040084505001d6042100800548201078680c09860b0200c4244042c400d4054005d540303420014045802c1d100352800407c03040e0007500e602080b604000c1620b44800d041080480c1c900400c541c42d2034000006210000000d5841c820561241d000e641141182c5854503001c001c0c0540580d01c0700e654074046800780004a001494a501d00040d4680010702c00d00320b50b10101c80e0040c1d5070910551503101007280c0b200709a88843c0c4107004004220b000c0c0402d440ea002014200d214901c01500400e84403102a80681440b042c0000016002000141003603500f90700b860136648030000c112003166050360180a02441c03a6031880d0404c000303107410444200894001c0010510441f911401d00ca5040005003000500c0d808460300180d1100c0b06101c1420300e242084d440620a0240006c01d504004505074410300340e20619084807a25039030400703030a209849603080b00d88000c0c1d0325136140e5000c01005c50012044280d01580901c2a030341c284506 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 544731816 1250 544730566 544730573
    0x12090305100e1006080a0f05240907050a050102060a05070e040e07030614010617130f0f1a160e0a050d05060a11040b0a1101091506030c0b0310300f 65
    0x10f07061050720968030300d0543c0c10311400d08006a507074030340e030703880f003035610440d2920300f490380c900421045c00b00186045484100c80d2103888084450250341a8000c45220580318010440809090300846005038400f2002805581542c1c0145030400c03982c7c102210f07617090a0010400751500000e88841a40c00b4070f80800402ca164841c041c604003805501113115410820300405880e0750f1620714005405940218484080c0044001001540f0000f0501500024500305550b807109010685030b05270718480c4032401d400c086401e03610402028605220b65981c02c6415200a1071115000c0d8220340c00c8140411142c5805d104403204a00420060400c4d1604ac20740100762841074480c0b2400d60814802005106850010707035880c80380760b050581e403c95540154038018840c012025180c5840101040861400c5600c0b80041e02e01860a29503040c0d01c031080c2825502c4250b03510311314041030480801140300c5202c503003241c20420107121070b5030b00e440b10711201d00c0f008021426140b0740043e11030f0a041 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 544733066 1250 544731816 544731823
    0x50c090a0803280504050a0f0302040e0d050a0f020a0c030b041401020906070807050a1506050a0b181207090207030f080a0b24090a090218010c050a12090305100e 71
    0xc05265008516140140c072142c42030010020f52000c0c076050501c819141c1074040c50a07036020302800340ca08001c1030b40e50104894804200d21044c0d00035841c00440804051011800d485500d01a0320b900d464900495411544040181140300c214000c42d00c01c84005110090002c0040d401903e6288441c201703810070100001d0b820100c41132030b81c03042102c9080c45d160607090710101a082034600c0c2c1c80d503003981171a6050100c0900024440e003018010517884100d140d01620a4550170307241000c14540714041c240580c4114110b48140d552180e0400c416442c2036110805e4102d040802d03950381c9a81d40444200fa41c216480460106e2811500d108503541d0020039944d20500c001e5050108ae0714110100b105c5014010040301c000d110319910080f40e0720b50b04111070010501409101c1850355039001c0130000c0d0048032609110300c10349003c4030219071246843c0b01c2d1407600000074104010942d0342d80b80d1131152103880d510a00060800000225405110380400800d440d03d01080424101001d28103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 544734316 1250 544733066 544733069
    0x141c0518010606080103050c040906321b030a02030c09031c0315060f0806120d120506010305090d0503150406090c0806060307120b040605061306080618040602030402011101050c090a 80
    0x3000713200030040010480005081048040550300050020342600f01000601b248145010740d108840c00f4030741c4059100c1c8805410304942c02e003821126200d8107030f0094507056010483c100c1420a00110703440d00b0055004641120f6940b005528108450b00401c0c101656080301482440c500309401d41071a805000d0030b5002880c5450902c0f03082d090440c09880307039043c014100c003002245c1002403481d44411207001e450713180550487d0401650724100515490307500540c81c8031582010f001c02c01d42d500a003d614000c0c0b1450010f4008074942d4881102d55800c000c100c079212003400c2c14251000d845a01c101000384c180c598002c1185000140098108034003d00843d001c0c43c4104104a8415400600101803910342d03c00410034031b03103140c005405050a0380042c0d80c0b02000183c0e0f540304410380d00c5003904448907170321010b0392907541e0810403407041042c001000d500903100c00018000707061a80110351052050418540840440714120f0031105c08407046903000400103101401403030603071520f60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 544735566 1250 544734316 544734329
    0x30b0301230a06060801050d030c02010e0a09060617040305160302100501240c2604050301020c0d0f0507080d091407170c09010510051c110711010e01141c05180106 72
    0x5e00c0d5240c02c1c00720788100e00084003d01048401c2d1030f0141168440e04002524800c01040f00101940361101480100118400c50300451268041390700c08a41d054005441140c0607241d850820391210300ca03602c214001d0408500314050350300c102c08540303014800c0c603020340800b1380e4607118115803100c0403840b0707800d0702c4200b020b0081104101c0c0c0059407001240c03441035000466584043c1a403c004017641c01190452a815400801d10207a481c07000240305904143c9075a03944481111220140d03641e10032228040c0c03030002e0810041502602035000345c038205210358484400d003440c1c00c041a00f050710300c0c2c1080d00121550352101c00d1b8113104002c050045001242e401d11507504d00800501b1a00d10002c0c1a410f010001c64104050100c81408169907070303103002c061107040e130136010b0000c56500256040b0380c881a10050300c002135105103040e170800401030316040702c055510b07440c0c5102c54212000440001c4801490304074440180c2c0540343c0160340d11340c41024898404030b0f01c01e094820640106 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 544736816 1250 544735566 544735577
    0x1050303070b010b0a0c060e030304050601050d0b01091a0607030206060f01030618180b090a050d080730020c010f060803130312020102120c0306010f0206011203030b0301230a0606 79
    0x120301042c1c0408566045800040205035a03101003041542c11040d1440044c010b103183c003400c105e242001000543c45548100c0940d00300d41e881e00c080110020764140d015010382c01e094014001e100240d400303120780b90013000d00491440040e00009800c5e51050104400581101e8144442d03801c152030a8078803880f09080900685007402c2940c008407142401c003106040d15090301901114250100c840c9440d00311210802a161004603180c0e0703460380f258120340c0f900c104100040c08510030141c05015501980d03030000700c025034181d1996010091081b040c42040844150310f0000e0756171008010480c00500041071202014858004413450f0f031b032140b102604100101a42d11050083c14010f496000c040c504400005403c124020b000701d101d1420090301440500c4031218108010318030036402687c502e40700c1e1981000898841c0400c0c46180d10000c01418980b00090080d0026140184d01400010b0101e4a08000041c0031583c0b016400e0a6040003041c170054074864081e900180c806070800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 544738066 1250 544736816 544736827
    0x1060e030a0602460503040c03020f151902060c1908070c050a1103012a14120117100b0d080d09020d12091a0a18210b01050303 56
    0x2003500c0300e40280e801020341c1d90000f070b1520901318452103030b000c035100510381460040790215000400c0d500b007001900e56054040c1c500b40c0c0b0510900850380700d6944480145401c91650b800e0055600e10707040c0f4030398080000c804d418220401c040190580f49089410114007074a01100641800700c007270a180c62560341040200d00a03103020300041200345091810300050380d1500e00845203404500401419402114000d0003801072500710742036501c8040b0000c0041030a80d031840f1610714050400a07285002c482c40b4450018004d03e9101104481d244407035280c020040b41078079801900742c11201030594641e540c601003050030040c040e00c0954041c010041249044005546189110001404040c0c00682042d05618039080040d80c5680604000035020480c0b614546000707450150000143c001d54000850414542c03842e130130184100d802070f14004607001c046900c0b581d02c09a010708200202e02c0002c044e60003510034803072180900316900c505845440c0c003900044040c1d105c0c078400e81c014001c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 544739316 1250 544738066 544738069
    0x50a05011e080607051b0129010e2110140906090d05090d020103180501090318120f26030403090f1421150906070309080703030906090f050a0b01060e 66
    0x403c00d4024816082103600da540782403015041c0c404d020340182055082c0703049800c0d20843c0419030075002c3c031110720420344008400011245004021a0340350300224068100c80c21000180001007024106000e0760300c00100d01012000b40e640035001c8120703040c521010424484020311100c0d130042058005007010b6282d0150082c620b010710740e1003511444d000300800e400c5a000e6401602c1081707a054046000e0036807820a0340c000c1840282c01c0d00405e418070b840d4021007003034038103402c1900e101c030000301c400e04200c1c1c44200d4007032802d02c0c4c12100c00b410400c0310000341e01c2050059621680100c0c1260352854103150050035421160b001c2c6c41d4021050501380911042d80c0300d40034003c5c0058a0b100c103003810321100550b4148060310145160b020301c10a0380f110b074100c0285c652003400d01d0b200f112000e03100c2032803c41c1141e526100c054444030043c480080000d1198004101c524040c56002c01c44e4016a280c40d00c2c801d040240454a95001c40101c3d13040000e001c0085004212505059011029030030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 544740566 1250 544739316 544739323
    0x8120f06060d0e0705040606030e060108031903020912070b04080f070f030f03030f0608010207020a0815071116120302010e0a0b0a09170f12090a15020c0a06050a05011e08 75
    0x100c2182c0540b690f148004003582008903c00901c0020306c1031280681e110405401420004840402070087c0c10000c1030f1090000211a400480c050181441881011013140250445450240d00003008040220080d208002181c060040300c0003491b0b40790b1501600d00c1c070f0a00c1035010459580c2080c00200b0628851401e40000c40b60801201013840c910361030202c00030500400c622541c00c0c504200841c0c0b00905502804069100b501c040c1da03496100d40010703640e05180354800000c0340c000c1c000100c034188070b42a480385000000c000c45e561601d1040f42d0b105e0704003150300284094013032411484141a424003603803d912581f03001030082e810f202d0f00c2d00c02440c01300810b68030302191560b4107241001000149803210020149202c0c1c0c4480c580300c282d804a0780540b115852a41c200c40210b24034940208280003c41d5110403000700c2c0318005134422019401641ca04100b60041094104c0481c00318004d0f03503c24115030340300081c55810704407002660200c1030030b00d800c3c405003010180300350b04000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 544741816 1250 544740566 544740577
    0xf181803050a021902030c01050904020d0603120f02032a030c01050a02130e1501030b062b060b1303231006090c0509130504020a260601050103020c0c040b130908120f0606 75
    0xc9c03a140d55100c0f80d0030f0104010388070308a0303c6007065207000400420710803480110f0b20307c0400341d5690f40341b8101c1d1110885c2d481c00740a01d100041031002c0d00f030030913000311081c00d84030b80c091143c29a401c0621201000e421203000319015410f254001440d00b21207107801601c98080c00d444a030030351050030101000f00c12801a02120b6041c91365a000b1507401c3d03640c55094030404055000080c14007240042c00c41504440e0103402100d06062000100b02c4412000a80b0a5480340100d00b03850713a841c40d164000d100c86071030524035110090704528002c03901c00303101c002c024042c4000040750540c9850426002c50384040c0400e01044000d100d031440c2c640e61607e14542004140c100482d4940f05c1d03000046034607034540d0100350150f000260406101c0c4513451071030070380c89000c410740e20541c9c5d0300c600540c1039110301401e013800394203c103808201b645001e50203210603660140424040d800c00c107804208440340c81d041529145004100c231128040c19185180e840008000302600d141403020110340c650058 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 544743066 1250 544741816 544741819
    0x30b0f0705160b0c040b0a032301150c0807060e0105100e0610050d0b0307150906260907090e0307020901050f0f0d03030f02070b0a0c090f181803050a021902030c 71
    0x801144c1300d076070300c282610003034404200d02070755500c0601805402408590a0f82c9000301d0605481080e1040b01000e8604a5040a4411040100021003100c044266031310845070100c050041c176005c00d10318803408001c2c0545400015546c1802031400721424401d030b2007854155101020403c81e91903000d0007048112a40c1003040d1034110300800580949070210030550544039100e4001f490481d5408009002919a00c5286801d5111101100d44c0001e00d503003401a01d0068001500b41d10b00f0000f0190301c024104103556100351600d4205058a14a071300002c1a503001190110030341c07420f0701181c0e0041c407084403c410403510f80c00215001850302e14219105282c01360185080c18000d800411055108000441d9282840e140c80000010f042d55078114951400004040f19030041d03000c0d13030644034079071a85020340d80f070903041ca1100316043c10345c2c0c6584c0740c54004c3e124022441c0340390aa650351003500d84544070107504100070710780003c0d00880c42003014004082d80c09a10085001d5003560380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 544744316 1250 544743066 544743083
    0x3050d0b040906020a0c031223090c04050103080904062112021501030303020d060503011a06090f1203180a120318031e11010c030e09040f0c030b0f070516 68
    0x140c440c0010002e01d000782014046600000745020f80f543d00500c0f119403203109440b101401c3d4642c120403000c80c2c03940c820007064052041d8000351096400e04155601000280440700c0c2c0494060108059078030a030b000b110300c0d400200c2d9400844c40c0c90701441014041c00c4500103601000200044284603c4031809026072903628200d56290f4401c4c4428060461120540141035130f40c0d1400070001d511040341103400d280b81a0011807145410b009040640c0c10001e01620030340b03108003c20003103074441e01049500c09104060510703e507d81c0074035501c2120140d80078686807460011a030702c28000303200300039100d8801d0325400d003c8007006540d4004403035094a03041102410000d5800da03c1112901b01526440185460401c00d50304503e0341c1107010320902090000040050041d6000d09a5580007404a411b01000790f80e10300300b08120341d50290150b80c0c558904c80268075003040c6204588c00c241c0307a80c0341071701c2041189072030181c2c1550498002c0ca051464a0b03180f01c0c0c4031304e0600c28884010308059 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 544745566 1250 544744316 544744331
    0x1050f0d0302060f042102071a030f0601030b03030903011410080105072102040504180309080c0604030f0501110304080c0724030c0207080f030d061d0126031603021903050d 76
    0x800c03000b1800303200e103802140d0b0b0342d0002c946c24065580d10051080b10807079501f000000a5007c1010700303890140340515003241a60302d03000c00660161004992507501807005100caa0040d036030901071800d0384400700120308e038907080055010300c01b0100e541016449a0419081c003800951055181080c500d500800300310a41380c0c07120350800f03840340f03034811603002d828801040c124440300890b505840788640c070b4082e0966601c3c0300064403800141025980401c041c801040030520b1248504000381c03040c800018841441e0450f00c215402c16102901c00c0c000100740020074910421503400134001b41201b00f02e40110110081c2d11521154801c0c0c000c240c0c5030000394407154020400c8801915550050b5900105811500742e40c1e600000f99840d24141410720005006454200380307500c2112007541c0026a07824a007200d1030340307282c1a21440200c44134a10040c1820f50034409401d2131100c14002000c110220708000780382010541501101030204011000003076040030841c2e1440031006004219035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 544746816 1250 544745566 544745573
    0x501050a0503100e0708090609072303010204030609080918090604030c14060901150504050417030402031204080c04060b03131101090503011406014505030a0b01050f0d0302060f04 79
    0x1c000c0381e44510743c4c0f98001800d110381e443d08944128440c0c4854800c40b0125640d0820340e50b41c4062500c03078201d004020140f00d4040c4041a0660202c1c440040c00140c03405aa030380e958802c4031030051043d1260080410941524504100800301282d80250b03903180323908194007141e4503000003400003000d028a0b1068a01000b100d01c82c602c00f07002190080ea8841d03d07050204601911281d40e45021141883c60b01043c0c901d030901c80d06015941041d2510f9803520348a1301215941d00141050b81e061207030880c640c2c3d19426100007007000d0700405000d411803200340c101303020650340320f41c0109107200401d100b04002680380340003080040d5002011990b415922a0040c0c89010198100d59015405c04601c03465115a0240c000d020701004ea0b1102103c05110401c03005080042a642d2101da4440c500c0d2110400c203800c185c06c9400780340100001c01c50366003001a24026007044200c0d200c0075810010000c1703151007900c18280107030a0b9255003002085035402900c0b054002c1249200003002c0d004107050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 544748066 1250 544746816 544746841
    0x3010918020603040b06040b040908070b07140a09050f0603040f120e060f0415020a03080a0b040f2d05160c060b0303121b072022090b0906010501050a0503 68
    0xc2a00a01000c0d541d0926042c8282c10300d0040b83c03114000d508040b01354100d42014800c00056030b40040d81141440c005d070350369426030580541107004004c0c594101540100320f041c02000b8140654862186280c50102840400c0300700051141c40b43c0012303c100004160a43d40403c43e0544c0242240a030303110501007911001488515a90401c20106401c00201501e90043c01a1448501400828a03c04400f240d40720901e0300c00500103801e02e80803500c042582d4102d407610741001800420401400c21130203040303621480c108051030203202a480f800c0f5104880b52035400382e5064040c0520720b0701c00d521001c10844140f04c80c04024203030003c481400004d41c8840c1c1500c0c4000c060f80d9646200d45d90f042c103819015107403d2051207103d0000491a8207150849541d0f5901c10043c081480c0c0356810300d0141c02030290713210341110410300114100e101000c0c01c1e41a083c59500c0000f40e030036181c282140315900050030307407000350700c5900140142d0b0707006000d49400c4403503440e000d1350329614042c04028 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 544749316 1250 544748066 544748111
    0x207020111030409090204060b09221b090303030e28060b09040602030402100c02030601350d030b0609090103020409140f06010501081e0609090a0c080106090b090c030109 75
    0xa000100f408924020240c00101249000f140c040c04803540b5200c2401c0d56105040740039a02c10030341010022119803055413089544a42e2000246043c07141005a0306a1104120003001421b030790024001c2541602c108028941c410001348221803469040d054400040000d00b042c0d400842c540004005d12608001d15050001d03241c812107041500e4176002a400580e0100c0c4100610071507845c416106020142405030020002c00e016444c00388800d161844c05000340e0303c1c49008603110703c105c500801a0381056824a4000c0c0104400440001c1c1141c4a0f25407480c420b181c00c01a10310165100e001e41819203404540000300d1456610305500491080c2d000784c142802101e60480c3c1f100e4011416504030341c0b007030b00c41c040c0980d50164070300840040301202140d1099030340d0124007035041200d001c076030040b0520121401e4140c00c4d00c52000c8099594400e1481d41e46480c41804440054052011019000d035501300d86c0d0300b00060680e40c980030500813010096501c0b0710400f03c50950050040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 544750566 1250 544749316 544749347
    0xc06062c151f0e15030103021309020d0302100c141b2404020117010806040b04050f0307050115050907020d030507031407050a11120a08091c0807170705040902070201 73
    0x15040c00750500c07044003800300c4903420000b081c1c020300543d0309070400b80403141d01c0c148101d28940c510382c04e40c0d08020f0101c17032402c62079082590f80d00042c001070301c03859440c5075518000e400411104407440004010b445192081c1c00402500c0d000254502003810305692490002e0359001c2100c40b606005185080e03a1030350b001c0307001004031001c0b5031101c014096543c0240d000380d0b03803071880300043c484401842800b0312074000d26520060024001c11642c416540d0011310440580e6001c0c1009035070185076400ca4242601c07240d41d18000c5600c40800d00707804600405055031000100d00e4030b01c201030340307440140411509040d00c80002801044c403c0c1d1004118141c046038007880d5051000004040e40c2010750848040b0300d4640c640e0364225070001d64110f09419450f0514134000341e11900319010580603190240070300c540080c4042e5000a0b03a03d140c100f100f199210b248a1805100050080300402d8001042000740800c0c000103580c0142160180c1300e45403000b42c0e54030350b40e20040340d03400c0d0442442c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 544751816 1250 544750566 544750579
    0x906121f0b07060e0303010f1217030a0c0e0d030503130c03021306090b03070305121b012307090501020a0b0603100c091703120105040504080c030403030c06062c15 72
    0x1041c0e044000001d0100a40140800c020700c030f0030300142c26900d100a0058950740040c01c001000a1544801260411842a81c00450300b040f18100c1008540059039101c0c1381c107031101c00b00f41045510942d001d400400480e040081d036005c984001e0420301c0090203004805d05100d500e2818081c120142c00001d43e80a0042501807900e101d1213070017440c05000e003013461070510074110340300d180c0000d680d425690841c001e002c3c00e042c900000729295120007402e8540074034090503041c911101b0b10400c00507456403031801c0300c1c00721040c1001c0d0702d5420040185081c059940001d010f280da0001c1d44a040b035901074a6846075841742d8000a151408900c113020501d814400588089944800e02c1d0044440e4400c0c0081c0c1200c40314881d03030301c030700a6047c0420305865440041240b45415045960014050300c0000d00c0d0030030490303801d801d690040d0004e40c00f2071010b030006410031040303109003002050314401c41407000c9046101840380205081010444094280209900620b1a41514480c0800500c1c4c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 544753066 1250 544751816 544751819
    0x9070c0f080d0e0c0102151008010609020403050c061903020f0c0109030e0306060105041d130206030108010213050906010e120f0f0f0d03051614070f1a0105060906121f 74
    0x60801d40c1c46103114109060034911841c450712000a810380f9040c1e8160068540d502c040048411003401c004d008000d10325280c200010b950fa002c1c461a8003501c00d0303150242e910790440c2081e604e0410f41d006280e000e48810401010b0250311031581e002c0d40e01091074003580d103402e038540d040e0884c040e500a084055107030070082000c25411408000400005405540c55507481d0001503038140118454654800c2078200e03842a4002c00003222580090052170b41000d6041c1c50b004509a81c1098010354216980026014040703212000c00c0d0004002c101d6024095250010001300780c0c0225140a500a0340050032020160394107002106c0c0c074150010032106d110344804132203569018403405070f01e410b004256901007994841d0103201e2040c9040307112144000c48203001102c045100504a540d0b40c901440250000b03058041c0e4000300c14000c45461a44c80a207401030300c000107040c0d00c05845a10708000090503030700c0ba50266401c03108250402c1f12144c0e9104001e01c00c1a20b01040845c5800c4003600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 544754316 1250 544753066 544753073
    0xb0c01091406070306320a15050c1902011d0f041104050103050a1406120304082a030c090106032d02120f070801030f081c0b03100b06040509070c0f 65
    0x81c1c0603c20503140d41d082c81300c43c1d519122481904000307084030311301144c0440c142602035002d4180100020021b0520416687d45200c8414024298103011001960000d2980780113401000540b00c05110900c40c02c2246206a0000c0c014020300c4400d103181d2140800921100d0b80e8424082c030003508058410f200e03043c00b01101c460b00d90310a00549010a2500c400b054414145109404400d00d0903801c0122544904e410003200c41840300c40e000c40317884108000702e0640700a00403211404445c40c548a007504a070308411400601d8007108038000d030b11141e141802e59462030f407050304581040c00c0010740f140d5009906840f101c0c000008601808250b49501d62110f1031398014500342c14400300c0c00c011500c900701400c28604003515090005142d1030010b101044518801c5140035100d03e160a1400c107000700c40c034803801c0002c400343c540c0c25910f6501201d581014041c1c003032003040801c0304101c0c01c5c444030001030660240340541d6000702408000504064081d80b0120119904440203580d145050314 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 544755566 1250 544754316 544754323
    0x307020f070b1c091202030a321612020a21170907030f05100b030f07050f010309050a0c0512030a0c110307050334060c030c0302010b1809070b130b0c010914 69
    0x120b10000090740e941e203840001508815000c0907400460551000c15009c00c0c4003125900111001c4400707051003182200021070554446040c09856000f90a002c46c80b420300c007060345c01700d003c03412854030340480c401c40c5036a000310404156250f8480312a055240c1401880c034082803500000c10380f01e8400019024070400280c0ac000c8c2c0400d030b010510000321800d00f03050700c0304c13403132410892198070004040c07066180500c0c00450502d0f041c98000340320313083d0341c43d80c0e850054100c40944410010600a1210341001081c030100000710b000194034044681c280140707800300041e005001902d44051080c0d49035030501031000103190040c126800f0322140c0501c4501ea01145c114141c008014480110089000c9100d81c0b045603550b4941101a61140c1c5058480190581c0c080b0115542c40001c1881c03039a404074081409551114000164540018a1454107010380c0015940c5101842250320122443d00503009685041091588802403030140c140501440c0100520f080d00c9445080e0f05c412002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 544756816 1250 544755566 544755577
    0xd030909151a0f0f0711180402040c0201020a17100b0a08090c0405010303080604090c030602160303150b030612010f090f120e1516170307020f070b1c09120203 70
    0xb18441c80790700300030500c0290b541c420f455100c00c210704240130b4401480c95820160200798010849580081003080001c0c4103240c000c8081421246400140029801e1a118652200e20319000862508038a0100608000310504803058031650307520000b123080b40103003c142d0061510030340707160b211128004081e0410f00121010780e510700ca041640941460035024950480b509520358100588500d01030101400400c40181c0e13000900c00c000100069251004112119800b00d049051002ca4900201030300c0394040c1840c0300c403c10107000c2c000030440d07904407a00804102e580d403011540c403586060160802c2041140300500d046c5110050001076051828018071510041000784110301d000d0315038210304051359800c040003050804800796101d00034114801540d960500d4118140d80700200c01400062101c0c00050100038020811303010040407118a2064018002e0325042451f101d80b03c0c06400f14001c0342c1c1d83c071060390003216111507005c001a150070211070004610001c1002c0d541e540704 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 544758066 1250 544756816 544756829
    0x303080a0203010b0d090f0c0801020301050a050d0506010b0730081602070614120a0f0605030d02060402012303040f03022109090705040f080a1e020f0d03090915 71
    0x900050103409840c401c07a0705a55040ba80d03142010f2000c205940244020401100e45915032100c40002c030302801164402048100c0c009640c80d8102014001070151541c8024041c09540b802040014400719030380e419a00a4410140c80d82000d06082c00c0301d1300130742112043c0c99050310b10f04561240e040d28030060800d40cad445451003911165074124120210703848010040c0c1048405000e10343c4640c03002d0828405040b203c900704800400044c001040940e03864a099170345050080322a4111f0151034004c0004070b01800f900c5040207006901d4050082c402410494903080784919030b60f5814100001170184c0b4141501c1340380514080b03044680c2c0031820303405442965680304019031842400c00000800352800303070400009400780200144081c0915050100c1400040340004001d4014802420319900428001d001402d000f061700d1015000c1c0844414000d0884003d0380b40e000c3c042c0c02c80035041d00c103202104003078141103c44078a00c0d00001c00c80740c204000c00e40140320900c005002d94a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 544759316 1250 544758066 544758077
    0xf01030b070504030f0b0c04081002030907091107030302090a23040e16090f0e0a0326150603040f02090703020c0111090d0311010e0d030c031a090a020c01020d06030c0303 75
    0x9a03041d058031240503604c4014040040c8100800010300b0384c0800e07a400a41b418401403c1945889185081000c2c46141c00300443d40441007000141c0104640b030002c003540c0c00300b00500d19420840c503001d4482c17040050305054001403483c0e4240c92340d051210080407060b07c50304140d08240d100190624600c00719030300c41e5081440034840700a000c40c008402805945940108130302c1c005007000689160001900c0c466944ea103c2d1424403410302c905403905101e559804481111030a004840382c54503800031302c007c540e080400001d000383c491100000c8000b1140581c50359145d00c0c001d100081400c1000350003c1515007808549034050300035010382168003009018034030862140350024080c00d0a0790ba800b142c0d061403280481d025481043c0c1031b511000006c2608049010024a031081c081004000282d4681e54031951980c541308192a20242c0340248204404000c0001e5510801500c42c419040d40000d5100415000354103c40200c4a1040d091001699030b0800b000300ca030441c8815070201d03e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 544760566 1250 544759316 544759321
    0xf050106060c06150e0112060207061103180705030c0f031c0519020c030615011404030f0309060203090a060f0320030601080702060f040f0f020301020c010f0c1d04020f120f01030b 79
    0x4401134040c0701600c030124420308440c0c2c0f170114444c95507144580161640740c1d0802000d00414658007405e000341200d0346505540781000e42a10030700080c2420601595040f1660070300940d900030460440d0950200c4d400360f401408032000030b040c10a104604021070860000c00303440d2540020107081c18020a40c201d0500841002007683c803a91b00505040c0c3c1a001040000c030360701089a00c2e010452410714010340d004001c5040c140300380d40a50402c0e1100f201e0420580200750348001410040d2480e440914101003544000c1030001c00c0e00d01540060004204041507442c0c46540304840041c000b10003501c803c4a0300490744150350054a4040c001a80c0c400026480c1d030001404d9801030501440c0700c0300668a5868a8025154040341201d031079100d0030002c80582d90900203404c2114100c0d000140751075507002d1002c200c641501c168000d20039606024245040019068130181c10180c41c056514201e100d92005a480750402030180a4074100920412072401e543c1107058070710898408140381c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 544761816 1250 544760566 544760591
    0x31e0f04150e01030b01320702030a0609151107030c0305190e1206101e0e040515391b06010f091104030204020c0a05030409270515040f050106060c06 66
    0x1c51a20800c444640401c03100c6401e071207d1411080300700c111903100d0a005c2c1c15400281000720740c84065940a0b190b010a5003030240d10302da1003050410316101003000403860b180282007400742da507010f801e00400d20026010704d80568100c039410740540d80708115a440d44100039103980c4154441d54040e040c0080d00e43c08400000602c0303401841ca1070084008140b0700b070503403100700540d41001805076119000000d00540c01400e854081c43c03140000e012000350f84113180d40c034103800909085821091803411f0600c14820902c402044c510408040c00d4202c004140c0354103481000020344004400d14100b03500c00d040031611a041c0d03910505040043c5640300400b4080e5942450b00c1e60f000d0344100f0081005142503802003440d461908256400e003200c1d911618150380066210118440d04c4205118008050002c01032901041c200c80c2c48030741c589a150147d0301c5150310600740c0070b200208041428080010130113031107240e0000084c86200c1e00c1da41d00915400030a107049480a00300b88a441c0320 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 544763066 1250 544761816 544761827
    0xf060906111c0e0a021c05030406090306051605090409170a020a120207050f01030b011803060e0c0102060903070b04050a3302121914040c030212031e0f04150e01030b01 74
    0x407080f03140c010203440d07207a6000c000255920400084d0065811840d00d0001001403000d00300429985d101d070100c0920b5418088241c507001032505107001e07502040c00c0d08840e041016a401d082c41581c00160b401d5943c680704d018040b0341030190440800218112180311342c005510150248603400002c0303075200f5090166587d846500500c0d0344400382405a8419520a03445085002c5051415800b0507001001c171a5540010703400c15240c00d500c0c1d000c56a43ca1104002c0344203107a4080c4001e1803a4942102c0d065124050084014560b05c51140402d040c800d04000884401e5042950308004649010114440540c004400100c6103001c94116641207154401c0d5101c0491581002205a8030603000584a4038003c82903c50181d5443c5404001407098030310f11710842c4901c04054880d801c5004001c40c07002800711404c02a403080146031820746e0f10b00f54201d0001a68041c5079141c00d241d407054425401a40c201c2e21083c0e00d0198504141036011003038070718090082c0c030104026042e58004495 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 544764316 1250 544763066 544763081
    0x3130e040809041a09130b0106050708090d0305120f010509010b03010e040b10080a05011401050409080708070213050a051602010c320304030207061b0f0f060906111c 73
    0x11a1200303112490711810a80c214032007410018281d1070020391304000081801c44152400c0313000c03c502001803400c004808906a01400c502e08155050a03030641c1d51030300b68455507001e24040c48964240400b0103010790103407582c1c1600d8070706041c0340f460103e01c0c00c4451582403040500c940280341c00050560284c808407410ba0f90900e104001603a1603032110505e00034080e14101040c1c01c0c400c80003400c100140507a1601d244500e001181440d2155112500ba1206070409807056140c104550300040070601183d4510364000003030754442e501400001c0454406102c681310b01d40c1030004100240c034171580268030684000e50600303894006900100d0880d00c4995001c8041454030907201c1c1024210b01c0340554491b008031680f0410950341e5802801500b0a42d07080f000359011840600c030f050381014000c264100024084407482c41d840d100c40d141805d4024018083c0d230003248444060007129008900800c0c0c00c07000920548003040aa01c1054ac4a205c842d1400300c01c6110883e6012a18001c011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 544765566 1250 544764316 544764323
    0x2208090306011205060f130305130b030705040305010b0a05210c0a1202040f0c050a03150b040803031b0c03040303031a040603050c040f02130b4602011404030813050f03130e04 77
    0x1f0704044e52a03800382d41c81e910801d1010340c0c60035003200c00180042540d008600c6102c00741d803070030b8803246503290043c01d4070345030a4254465064810140310644a40c400c581ca01c02020800c450403c0030b0000306800d00742d040c0c019680006060001041090780107400f0034172240f0030343341000003c0034003c1803811070320103a1070840000c5040010b0140c1c188070b60800500e1082d021086800e155646a802c50300754820350010145401c04010010740000ca0702842c0a0000790042c5649050021760006071244500c1c0001003d0503500d00f420440d80d0382c0000e00381442d64002d40f00300003598a034100035690318944180b40c2e110341d00302046510400c0c403500a4400f010824480958664100410210f00303801411541280e4136900e94001400034040212040041c000d16500008000070400e06145400e03041403501075a04100b00300c000b01c20351004d095809501441c2520043e1189072307018007103181c030317100c060310600c20381443c5222403a0110091030003054841f51089055510854910786c400c0446015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 544766816 1250 544765566 544765591
    0x506010e0f06121303030501050111030d020a050c0d03050406061d01090525032f19110d02250b0d050903072102060108062208090306011205060f 64
    0x105010708014000c034026100041c410307410103100c1e582611440f10101d40c1c845211007002c0d01e1200b030680600c14580940400c7c6041440070000b0034a0580c2d82c4561401001c445a000450900b50361058007604e03c1c0490003802d580c14540040700050141c807043d10300347c2c0d20302d1904c0b0002645800c03076104645e140300307a00501c0000381e10f4a16032800400300100590010044085050b650070190b48505404944135103002a2010036070340302140303100e0bc2e0704101d8003a4180b00300f000c2e5110203100a0b03d02c41540c600004607030701907828044807551a652201b404500c2a020307000b00c21a000710314001400d81b200d0700204c00c420301181e81c4440100310700c0340d1004088100030b081030000c01604504e038814200d00c112460510565217106190ba108d50070020007030310f42c00e035400345294140902c600400c0070382c0c02040c15080105036981c00c6001d0000260b02c0e0f4034040c1d18081081905810341d003110b40004c054411a43e943e00203030f402c0303510082c0c04031580e010300c20009140000420a940c094040a0b601 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 544768066 1250 544766816 544766837
    0x7031d100e040506040207061103040b07020a0c050415031b1814060904110a090b040507020601050f121e0a14030a080c0f0c0f0313080109170f1204200301050601 71
    0x240401404013070f202a4005d40c0800001c03002c81d5140c0120300f02a550412900c3d0f83e450142461946c5400181190085401c1780d0700220101d84c01d160b4050030381d50b0407100002e5030460142010100c1c0a10391004200e458420f00d0100141c80064040c0111904000c2480000c2c070600b0070300007102c0c02c1c607504440c0c201111010603803c2c102009183e074000e2003018100c0c2402106400514658000c0d40180150380e00c460300740b125801d050150903000700c8240014002541000c00040309254030148403400355842c121003181c0ba103010008419102d03001521001101c80410001e41c45184bc5141038a02401c1401e0102944d0f800001f202d100000c140c1d226002c0d9260403907003a40303079881a0781000c1d1548042c031214051803c1030150a8403001c0310030040d44e98941094048200d01120341c0480816454600302c0c07004205400c0d04051340640018a50303656418417001c80349240150308401502440d00c00c1003108100405180041c60187e00100d202214030060070182610703c1207071841e0005d20315403503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 544769316 1250 544768066 544768069
    0x10e061b0906130e01050a140d150f020408060412080403020c01050901050706180c0f0605030c0a020f070b0703031103150d02010207050d0b1e0121020301060b07031d100e 75
    0x90040070800901c2030340b50a100a42d07a40d20000550003003a1044250401000b2a00e003d00c000801400b52048101c222107482c0c002074103c84040002801100c41c0394003002048506e40d02c4021890340c465021502c0c1c6032944211503407079a00702c07011500d082d421103440b28030a015030031092103550700d030b40240700240c03152004403051381214441d02e051010030b020b42e400140d25070080c41003103044100c103041291946d0800b01a02903c1d503200002c010042c006c18401710390b0050272282e01c00380d401c140d1950703034000311022441d0070175145c0444210b000e414000304208a1801c000e1580da80240d0301031241c40440c4500c540f45110549842c0b58001404000900c64204054281240b07401401501d2405541d88046075400700b58010440e11060040e08100341d981c0745015244105025202d400d03050340c10710440545081001c40c1c6601c000031070380d03c80d40442d9425000300014104100855848038500d18000c0c0c20038100340350b01d6120011000394250316041050080e02501c0c025926036105411520 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 544770566 1250 544769316 544769371
    0xe0f1c0309030513063c03180b040c06080c04060c03120905030c0708010e150f0a020c0d0f11060f0c0f090915120106050a1401020a0b0711010e06 64
    0x1e40440c1030101c00c0c4441d0072407130511400c03400144980c2c0c450916500c0c80da180e00c0c0240f041d410356011121001d5039584004502e007081c0f0040c0903018140094161404c5407000d8441ca85844014600381c2c280c0200020821030b0000d050854103180c079011403a44a85001040b58004d80c0280400140c000000b00007291044c1c44030f80c07000a003540005000c9005484150844c2e0140590700c4881d8000042004015424816080502c0003032014154142e9a0010b880584502800c0810714800103008108070079451350490302d221603240122080d82401c601e004c5d14404d400d903031a0300405d0602d04100c4a0800220f03246100f2080d0310509081d070764a450b40321015800c0741c844c3d0401e692060000804c0b540701e2070201d90040b83d01642c581c0440d5640810030040ba4a2030517880840d9041260030001911b8841c0c0070003d480151103079200c94ae24a02c0101d14144803a00b014080744010002d008034560031030000070408407600003c2c041104490356a50b90f850082d80c6d04c208a10701645080002460350 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 544771816 1250 544770566 544770581
    0x15100b03130f15050601021908030610200c0f030d140d0603061a04200a0518040212090f07050312130f03150c030608100f0b060d0e0f1c03 61
    0x45802242c1c07042640c40368028040d50560703815520b5590010310444d0b40c0c04101e0b480c0507014052a610707c04000d03689044d058003020700b041e405443c14900d92074449002d41c020a10082100030140714042d40903078043e030f40300c26401c040c070b010b103035403240701c416a0170b0204940300b800704c142e124120030300c50180d20070069501410644d190781c1d596441c08400603200740620401c941c800e10280084145a00401c400c56150f08110b411706407100c0c00000b5440040001c0d244418218108143c0740e00c0e141103251040408080001d03840380c40015260b10391b9002d1300c20300c0e019001000031600c0502198950070b968041038081d20b58503500c10480c8010301c20032200104000d203020390400400b03555032201000d40c50059041140c074103c2902c0748402071441e520031203c1c0d00e14a4030b028840103180c20380c1141c0f00c141d0708512040c81d035101d841010364840e044e08000300c2003134060038042e0741e1100182203000030800071560040304d0062119200c0103500004000e9880540b458100449031400341d0181d004081c0c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 544773066 1250 544771816 544771823
    0x130204020c0a0609120c02100806061e0a020d14161401050108030a18030308010302011d0909010e060109060b1b2b030506030604150c02030d090515100b0313 69
    0x204544100782074280100600350b0721540002c180c80c0300c5407810444401d141c0001404200700c41d21050302580e510345c00d42500129505011500e5250140819014860081c40b100c04441e91440000e003401414014943c0030141d07400c0d5460310490340d81c1103402c140482002d5810f010180075030382ca4001c21000c0900501d110715803182e00310301d07000c400d1800d403030f4241e000342215000410001180c58000780b1810384c201990410700c03291800e580d400b9120400600029042040725030312681304d01c01500d40e600746810010900d0866103880809c85010380505010b02683c4d0080a00000d00b040903405610155490f04500b6030502d11004580074071103503c900c00d03c5851196281300344890708890345801c5280c08a0034400301c0102d83e41d401031305480340070f0102400f07a8854010880491310f0404404c205200c0800089900d0b4035a00e012171550140700c8003031401034a450501c00401c280010b08a442c200d60f060761400c1030703640c401341151580b280e1007140f5100b941003000401c3d13082901c80c1c00000340d11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 544774316 1250 544773066 544773071
    0x11a10020d02060105041e15051806090106080702030d060807061103042301090b040f0905060d0f060c0e090a020a0e2b020d0605040c08011a2404050303030702030406090b0c06130204 80
    0x18688900c00580d81d00708ea04015140b4921001d00050400600d101c40680048440d5500d500f41003000c5104114148224030402980710301188480e4804e00803100c40ea0801c1105000300e07622850865101d22461040e0f80114820a00c048034504010095a0403514014920341d08a8801812118203000c103044081c1040108100800c07800e44004c0580301800640400c1c0542d82d0030100c0400c100c070801b0306003d204000c1c1c41e1071180001c141c02c4403604851340c01280820615a500400d40364030380c0c800d41c2c1d19800708000381004080045640500400902d41d03407211001451103040c0023400d121802c900088104000c0c10880544811142204551016003100c4081c1085c0c2c42d0342c001c1fa00305440484986072840001c00034040c0900804800d1203100a0948d901c20310640020200c1c2c80e8100030440e10980c60f0f43c01d0322005440e4003960024440902540d41d00e1400080c0292203901500541c00403e0f800d06000c101c003002107060b18510a4400001c1c03806880d1000b114258064080f41282e05c242c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 544775566 1250 544774316 544774361
    0x90506040f0305071209030201030b010c080702131104181503080a050c150a0209030616052529070c0201050414030c04151a0310030201110a05011a10020d0206010504 73
    0xc80d00540c0504c4416180d46d060b60703150840c8001001d4800340c001030340c10010001c0c55036001c40c010340708545809a0407568504540001c2c41c195025080800c0100030256000c200020303014028158800b15803440e220411900d402040c3d0b014012581b4080981440c40030301002c0c440394040c100400c004502c102c1114005060b15503114007850046804180c0715401159082d500e09040150030382021030140b24001b82d840c42038004026016069290404e0700762841c80403411070001c0d0a400700c3c203030449800300b1001070f00c0032612900701081d03901000300d004a6001400c0b043c800c06407a440c10b031f4160346441c60a07241811581c12400c82c10f6201ea4540100d0b00c24513079540d43c61090340c0e81a01c0d000b058010403480d0002000710800c0f40391502c80100c03810010003000d106491007074400c1c1c1e68242040200813102580807440c1407914540200150b2818801d01c0310030440030384803e500c072030444540c4219402c1c0c100481c1c032481d4008201c00540c0c882d03401405146000d4000c2e1b600c60780f101100c410000e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 544776816 1250 544775566 544775573
    0x120906060f05091806150d05073f140c0d060e0c030109050c01051c05090115050f010926030d0b09060a0303051204210f12090506040f030507 62
    0x56580d5800201d250103080310401c030342c0c01d1003081264090000008405620300c08241c1c01d480308002040301d55084108400f8403002d0365800c160600c415040b40031204d406450302c803030411818421114845050400421b940e000c4000a02108044d0351801900301c440c55a90307403190000714044040d140c1c0e0103503035030004007516101c241d241d146000c1d420101318200c4a03103070748d4100314900c01c0d6a4066411704407450b000c11400600b0305124002868a559520101c0b18440b0002000384840000c0901700400d204030a001508a601801281441442002d0b9184c00700500300040c1100d59020036203501c0308208074000300c8102c0003512110703c200c5130001d442807001401c0d68030242044052031780c0d03104041001d040900c40154411010380b070080c150342c11070b140508980515403028000c402000001010000d40460b89070303409000c00c000222208520030040c1c10000c0c06250100040d1003075192076000b484a000e90022a5003000c0540526103580c2c841d044500203440741601880020402c02000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 544778066 1250 544776816 544776821
    0xc2235061f0609050a0510030e030c03040810050f13060b040903170f01120b1b0d021e030c0912011b11120f0406120b031605040501080a080307120906 66
    0x151401d604120001ca46010408000803030507002201004484001807266444000c620000d941080b504954103107a03020040300074042c000c82812032404007191000c2800380000261054404100c01c1c5c0d41d0100b281030744201110411078110100054540100f200f08085030032040c03119010303410201e83c00d408030000c03c003544c52400044002507a98520102c0503c80c09040035045043d46035100e00a515013441c4458000e00a18003400c1c074110a000302d064480c28501d00c011b60740344110110f444400305210070700290000000e4480e044a03c90404c0905a19030741240e210b4100340d44000d09101c080418000c919440c440b4a42496580c0c240192024108a214000e04081a9904202d101004000b2401c140d0300b941e01c020fa60f0001c0c020507503519403100a94060350722500d000110f02e12140481c40151648058280d09801091038454044403004421825980161018080390340e8a100142e611421f1f950040c204000505c0070a03030b013a01c640003a0700c8050260b6000708031010380d51a035204 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 544779316 1250 544778066 544778071
    0x371101061a040801050a020c0a02010513050306040614070201050115030b0a030c08060426040303030509031303060515011d1c06020406080402041b080c0d0e01050c223506 75
    0x2007004020804000000e402d00603a5445074000e0000d600707003c0d03c001300c40c2d641c0110700d00003818002c02080030039510351500c0e80f20005010040480e13030f45080074200540200003072014803041c49070200009200034014081e0504031035002c2c221001c040e00017102140280300001400390b00c41400c42c00000483c100482e00d1019250400181c011810302d4030b00781581d00041c070f00c05c1d240c117044060381000401030324081d14102ca4142c18046010f40e554140d89046110b0403009c22005c00e0818804814007640e03a03c200d1090f07460501072511035a107400155065480640c040e9541d8203004446807003400c280030030000f414039022410481c2e04a5540b042d0990b042508010300291000341084254071b814090b00c81500f0340700d101030780305141089008000060041c4020040f001c00605120801c480ba40410301208550000b0400ca050006098100354010b1400150141c88044696520307060507907200110360300302e01901e030a6460200e56503080740342e94410a082c1c5948240d02084410306100031413 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 544780566 1250 544779316 544779359
    0x50102010c170c28030b090c0412020a0e0a0b030c011110150b040603090312020910030506010e03150402090106140a0c051c0210051f0302010e121237110106 69
    0x180c0704220b0000102100c1b12240140c0c0b248004000b440b21301c60711101200e0903585600c1c5101205500c80c0045102007140346e00c43c1c90180d00807000c0060984107640610203914003203040c1c421182c60540111804074040d9455031450700546e03031029a4231500d511222104005a0407600200ea880414518640045c6d000c0008130f900d03601203008259101f10382030f0400b40758660441c20003c3c2d24000c80d20340c0c1700c030038444000c0c142da46000c540365a0052448102841008088038a03100900c4610064101c0c00d64080b4001e9400c0d40000c11958080c4d0128410183c82402075820700d8a002d000311242e11000c21300741c0311030240603802c240c85c0016080d04884ca00190b002810081c217091079180480790020804800081c03031a80b401c51512001840d00f040300d0702480c21002b805101400140c0342c2c1c00100c0d901d52390b44156a01c1c0000d03100b40f80042e109904c5460007103000041e1500103520000310700c0c0c28401d0803400a580c40010b8030700071104954809103010000404680f00c000c8a13254444414105 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 544781816 1250 544780566 544780627
    0x190f170a0f03021e0a020c13090303050a020a05070f030c08040e06120106140103110d0603050d11030304020315130606091e02090904020409240f06050102010c170c 72
    0x620020782240000240c61914907085103450b020414410b01c0e18001030441d10f2030403000038010a45c5108101d40360404200808a110410310100c243c0000d000e120012400b103401c000004107486207a00c01d40360311500d140c4400d4a032450560781c600034159455021818004401680004145108050300c05402c2203200000b250030a1401c101c4034068a00740a40c2a1f0704241043c05681d880c8401c044010001b82004207150504285144490180250b104c0745185418400420700c003000844103c000d402d529510040d00103002285d0f00c030b01c41100e000e50907900007228404000817960000703901c8080d64003461000069540e503002a030365980d100c0200d480c1c85511001303d040c0c0b8a01003141241d1070f080d046161005040202d44844001040030748121b0787c5010709018018002910700300c02c107021900054030510450141d004226041400344100c1c5081c8010035503500500c01e0090025213078480f080301c0c0e11062404a1481402001c4510146041c000b40081d150102c0d43c6109480744900c20 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 544783066 1250 544781816 544781827
    0x706050f0f0f07090603020a050c160312110d0e01051207021506061e03060a0f030303090606050411070b2d011d0f01030f0501060e0f09010b12190f17 66
    0x150310007500c041d0500e201c01614805000308150494049000c4a125090261312181481025a030078000d87c1400c43c2640101180403000c00c07205007410081e244100410441a10808000c40c3e8507080c038520685a0351103449410341243c05103545c50f94681c814074141d03140403001011a40304413415038416000d030340b02019a0800415001d00035034401401d4813000e00300107150710201200c2100c403170002e4003d44000b0204d04161600c12100018000d892902d14807103690746401801040404001d030780385443d04001041d10702c0c087c09100140c040d24100785003081d50300d07220b03084100f03000780c40700c11140868105a6036030300600d030103080c840e0180b02c031011803585000d030000036040401510250000c9074404210b50b101da1064024196070700108190300c8503c03246803043c0104221f400c07456048a001c01049100e491050400b441442004000d000d81c2032640c0c2031000d01c0c0c0d01001010303a00d40141200f00f209811f86201d00400074003d1b4411a40007042d52682c0e948801400b001400140001030f4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 544784172 1106 544783066 544783081
    0x909040206071704080705030a0807060b0f270c030106020616052a0c011707030b040b040f0c0206090a030e12011b020c040606091a0f0706050f 63
    0x4800b908081000c42c3c88030b80d41052051340c48600c583c50300410389040204100005c203900100306800c14009907111000340149122054210340c3c2c0c400000301c00c1c2d441c0324031032281049864181d24400041061502000c00007403202d200c2c0102040100100e80d070004000307920080c00090142c0480301244225901e00c030b9107090800c0c1000c003610152025207035914900c10000d40000b10340e020f181311b60041d0b0f100e07080241c00f09082c2141c20300003402c0c9030103034120290b49600104001800030b0a180003600302d5659505440003155140565400c0342e804103c09904100030400402d545841960018003056124289501951040d000f040b01c0c16000d401038800c414140003080f4031010841d0000350f0314204081503c3c890b42c100a000221140207104540c00e48603400a03529411140a58900c9584c3c007121204001800800600010408a100d003c0c0104401c0250759207d00b000c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 544604316 544784172 := by
  have h0 := BRFrame.cov_init 544604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 544604316 ≤ n) (h2 : n < 544784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
