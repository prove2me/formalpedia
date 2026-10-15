-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5167
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:58:05.028823+00:00
-- url     : https://prove2.me/submissions/334b593f-80a2-48d4-8b41-b97305ed670a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 929136690 ≤ n < 929316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 929137940 1250 929136690 929136697
    0x3020d060f0801090605060f030c22020307050a170f011208070512031006020a08030a0c1b05030a020f152a0a0815100f080907050d0602040812032505 66
    0x200e210051020036502d44040d40038080042c0151001894840403030164502492044c4007040b01401500c081107403403040005000c0403031805081075181541c590400345031440110300c03508440c1c440d00d46488460348001c0505010f42800e5004281d808180400c41104030380030b43c11200310502408545400c5d01e4002a40d000d02c644c001c205105581ea101001607145c0041c0d4410108441c0c144e5440343d9030300c01266070351800600600100c00c00c01c041900c000340307a0090500100242010780080020101403c0e4500a01005581e260400704006040d650b06000c1400c94001c03020040440c500300a4035900316200c00340070003005108004c3d8011014042d0b01ca4010a141014001ca40300e042b195409011880200c0317072004610141d20104150386030513044042505000d0b50790b400c500c81000003d440ca0080603204074518414028001010340e00c4007140c210702c510409001d6105d520300035003d4901200500d5802d603919090041184d4042060201c0b6503850828000c10ba140b91044019100b40c407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 929139190 1250 929137940 929137949
    0x603060409080c0a03110d0f0c02040b120703021905130e12070305091009030317100b0a120e0105131502090d080910030b10030e12030103140106230103020d06 70
    0xb8011030000b400c90004152140b81c0e070300039190700c148038400c1c480485d200c1c112043d001d408540e400e054032400e644500c284d850b80d5407024200203100c12050380041d8600f43c0c180c025401580c05100184118104032001c0b400c081c50b02e404c105860780c24240041c10749070300341e095003515651300c102c041280d0703c040100d81c1d0007200030508541c1c1d8000038240100258484556203000d1000410159241c910415189080300d0700f55891011011444446803840c90300070b4001003003401040c40c04621503820800600b4001c0315500c4201543c4413100b200000c0d81c10b49075111010f07925107400c0100c0c280310081403640e81540190b41c3c80d8004800d001e000020300a100510750020400031541e010050f08400030400260216071341440e105003510120305882000003202d4110741c110019501039030198010000704030040c0190340118540519204094000364000d45144000c00107203181240d0078400c0c3c0c0064804d02c03140f494140c954070700c814094103082401904060380014a13031244074180c0d00c84000342 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 929140440 1250 929139190 929139203
    0xb01020c1302042619080d05090f01052d15120102160309180c05090616140a0215030c18062b0f02040f050123220506070c050603060409 60
    0x1c1c81040e048050016821041340601c201030342c0000c4c00311140e04012036103600c61920362a003590045501c01400025114810a20a0303d071405020003003070051521440c0d4040001e41004000840100484a00014066189500d0051000446900042068408040d211700e0742101c0d812034018024824111400c0d445694030703007a0401c0560140c00c00c2c0c00c5511400c0146004084442c03c01e0888440d03180d07002c04500c003081004501d080100c058038954001141d410303d0320b03002d9260035a00790301c61542440c1c281c00c03040f0450218a0320b484034106208603800b1440c00e5103040020305101d1b108182d804902c0c83c801070603001896481e03100700d400000140b0406000f80c6180c2d0b03680c0c4026440b0440c031810840c140707a01840505054421344084607050318510350214030302030054804503140c02d900c0f200c0c0d084821003101c2004d080d00040c0042c0d10000e040178010300180543c0c035180724450b04618410300f403c001c40310200b0540d1503008103a8400306c07181545c80d21a600014001d005a2200a050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 929141690 1250 929140440 929140469
    0xd05041506030503070c170a030e030a0803010f03120215150a26010615090909060605150c0601060c05030a03051504060801060512070501050a0c06180b06130b01020c130204 76
    0x1c01c03c02001038000c0742d11590042c20410b461311340080e8500102c0d45405400e0b8084041c0700c000c2803280640021120002c2c0a855000d8641d03241c1c002990300c00d0700b225551031102d00c400c0007004146860b0a803484802e10103010364184403807004100c03807000350940000341e0301001a100035959101e20f00c80145100c0e01c030200500004031240804031599200d40d1020351915a002829411810914a10300d1007030740d0b8450118240304500300102800e070000c0e11619550302c404602516942d001c05d603001840f102064032074404156072841c0c260160444000c01405641510005000009a80030303100e172400c0104e41d40d6100301c4062a440d42175481c01d54020f081c401c000481c1d030010746c403410075a02c05035007156441004100f120f958128510485000407000c000c0c038040d01b03114986d003002252040030086400a00c2c03c400e040205038402082d20483c2c19841403004da49002c03030000640c0384295a042c807110401d080080d4490550300e80c030301d0081d00310b800b042c100141c465048501509504002a20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 929142940 1250 929141690 929141693
    0x304020a050402370f030e0f0106170f0c0d080702130c0e0f0f01020706080c04030210051c0603120c030c0507090b0a0803031902071b1401030605150d0504150603 71
    0xc165410b00e8044940c00d60060340b0003802180118100031300d40e61500c44100011440c90121700411500c01d1050340c50103680b1052800c54402c4c007605000300146040e00c0182400b6400c29402d02c000055580c4055000328412004c03511442c81c550483c0b40c01140d4607807140d40c54004103400725070144101d00d1031850704e159070208a03041a02c20300c0042013a905500340d030b0146000d108050f8500020240587d00c80310040180038494903803580d000e0540f44000741040d942e54081041c6001a2403400f000c10004503458003080e149860607460041c0444003804000d140d80c440302400c4454411841c10840c1120b00b000501d4007440415081035881411101c0e8642e403100240b00415407201c0c07440c4242c0554034001880d40303000041e030303005000078541049400090800c407070007580404400c0b208940d14103581c000543c10300305940b005201908001004d00103500004045565a030007151080c0c00086010f44480045c906a0700150040c8a000030641c170340c1d00340351807410643c440c448803841c2004000700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 929144190 1250 929142940 929142967
    0x706030e0c0924030a0b0606072a030b070323060f060705070515130e190e01140901090c0302040f090c0f081e0c0f010504090c050c120319020304020a050402 69
    0xe4205952080c0c083c0c954111010542c458035140e00152203500c1e202c02054092524000500030148280103214010b09140f626083c1e1b1017001c0350142410038404d40c10001c0c09040854140d101e0301901d4100650020300d410300035881081c81d44c000d1140b4600b4006178041d11703889449800b0f54802845180c88131041d00c0c125544a0641c0106401400c14000d1340110700c41c800144c81080c2040c0c6c8120070894205014101170900c0101645130074181d5941035250003e2034400e100f402d440b420004203405c01c10724000454a800903055210aa14200d0a800440c02d140c0300d0005a80e4122004511101d01400c11400342600b9440507200c010a01d00026612106428000c2262401002c0c0c48105103800c00c58207540c4042800f10006400c04079000d8008c1ca40303101e8100595405041c00c60030151182410130480c0c15840216021900c00540a2480e280c108070b8007a00610a0070700324a145406440961880021180e080711150040041800c40d5a0000340c00040d043c0a001152500c400c580c649 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 929145440 1250 929144190 929144221
    0xf10050613080d0e01051213060525020706120f23010e070302030c030408220f0e010906141c1b05010305150a051504030f0c05030f0106080706030e0c09 67
    0x103480788200f4042114550203420480076845058581e01e05000003c140d0b96040c280c000c208441003900c3c6110000040c0d064401c0f107000d4414440300c0500c40d41075100c0e0480700d40d46808210155401140200b103883e0f80080d0b504000b10b0080c9001c1210045516014050003500040b41e40d5000b89580041c250108040907034102c80340201c03098000d40304e0300002d6040340320a90f17050380711990070000200410a15030007011580b4550f40002000602800303442290f60b075541160804000040c001c10084101e40a840d014000503a01004044e282141c048c0e000281003840a0094030200b4078404a07841e80c0800c41e01c00c0740c000750070b8449010010036400d05640e1900403a80420703c0e220120b25800008030000091810242421090500704010841c100020784040b1351003007400c110100c00200c10400d4003a06600c120481540242010f04050501c0707140500400541c2c9001000c020300c05001404000300c903042e0800051880c10300c555981080d140004c000e81103500d01c01403002c0200b844464 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 929146690 1250 929145440 929145449
    0x30a090c170d181208180d0503030105040e1c030507090f090c080106030e1011070f0503030603010b100905060703091d06040c0203211302090f0702150c030f10050613 73
    0x110f03190440504401820303900b290055091040100e081c040009000710001c1c2030119a241e084282e100d2690009600b0300ca464104403525003021004201d681400e004d400807400340710700a041c041100400883c4050641d1240c0320405032114081101d0b14050f178003010240c080241c0161505441d4800300d0090b009180a50300050030800002680b02c1c41f91055040c0c0120032405050981100780c1c0500c05005032618544a0b00c40401c00e01c0300188151103012034441c07185002e561603281500030103085a040302d80d25800381e81c0e810004208945e004d019107082d118115151a1905040e042c00c54000825402081c2400d0a003403e00b41074030181c080e020b102e042c0c200d07001d000c0c455407400200d8684c01f5100c0b01c4109800344020851181d514a040150f0144045589881410540e000248a1041900d412000100001c18055600d84c10b20840c4055610b02c10385039420704000005031803e00c8001c154005688a00740031580c1d01162110100003001c0c0241902c0d141c00c030510300b100d00503d59224 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 929147940 1250 929146690 929146697
    0x3020d050301060512060432010b0304120f020a0204020d050402120d1407110a0b36041d060709091b080103031211160b1b030a090c170d 60
    0x2010040600c40c0302100d05079030706a0784442c14081780d12400031001001500d2242c0c0207488880c0e08600c11320807074080303503402c0c404081d404007111303040f603804031000d07060b048030442010170010000483d903541c00941c5122024688080c140811306412801c2408101000758414000100c0c4c4d00202c50b0342d001507010340e0080342c4c2c980e11141131007030241c2d0302c0080c91154404a801d020503040d6001449001e0040240a04207507101d03541b9500014120303842c3e6401c482e0000703402003651b1401c4203100454403000811000003950320602c00f00394060708101e5200342840380e80c642402001d11068170b00320079560b03402041211500c1c2012040030700344102c2c6e8040c10b10960700d4040e480449550707002c0041c0105009845508481e42540c030300315140c3c0030003240d107110a0740702d801d038002260100d8001d060820101d5503401d030b001d500746410200c0708000f030040030340100c1003d00c40041c0000748045a4120f480311400080805440c580310640e40303010344c4218403640741c004440100380f0022800d10f2141506a4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 929149190 1250 929147940 929147953
    0x130b33041d040f0c12050c04053904030b190608120d200a110a0b2d01090c0f021c0318081207080105010c3305090a020118030b04020d0201030b100504030302 69
    0x401c0c40104d0301c040f0380d03404012000c9110700c180c0349507581000c04d1100c0c03c1944d02c011015090401c90ac95486903100301c82001c5d1400420032880b0480f00c20360314800303400c0400e000702454003c0d0290389600740030202000c4140000c3c03054549540f5403004102c0091a96902070304216000447c032150083c18880020514115048003d9038000c50181107040d800244c1e44125141c808601c2110f01d43d08105000e51084100c55981c09405503010a000703087c60003000c01c080385601e800400e107030608810345003954800e0242456258070000c414000c0741c001d00d0b00042015200c59012240b018041d4048d0222400007540c4c90415070121101c2d2181e000364550180a90b66000110341b6000e00d41c2001c0e00c080c07240b0307510080c0c80351445e24410780414201442a07606030900c20302001c40d1270580c0c2c008001d60141c2c40e54811941c0108080e40806e840080600e242865903e40c0d00010701e008000034482c040800580c0c00f1a8025405108240070140001501070312000003e48260b2080c041940544170b0003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 929150440 1250 929149190 929149213
    0xb0d0f0e071a0403050703080307170f071829040b13091109091504020d1d07090e1207020a0305150a14060609130b33041d040f0c1205 59
    0x40103c1d0220f039480300040902520b152207004031900007810590420581c20006031507031141100c058054020702090046505203418060110b41e0b0504038002c154280710410044903000e0b8090006261307080c41d80030400102203480b02c0070761089422251031000081070403034180000700b00e40419510320038001c000b0861014400001d50042d0b4280300e9104030140b000030341c000d503502590164010003500260801d040d04020400fa50504000ec0700811410440b0074003030882000b00d0001091071080c100921041160001d4031050208480140068009004030031505c680d1059001035402009403440b464413000040103605042c0c804400503030414a40c400ca6031143c4071254041d0000407d074901c1c201d440018003d84081d0500002c005554503085009a500d0784d4202070a0b01240c0c21100d1040404044000d025914415108801403400e02060100510017a90087e1032081c501000c106c03030303580380741c8060100e00060300108134200c04100042d10f50400c005018180d44618155156050381 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 929151690 1250 929150440 929150489
    0xc040501090b060f0a0903060501031202100501060915020a0c06020a030f020d020709050a020705011409010608010b031e0712030504050f0d170903101a01080c030106090b0d0f0e07 79
    0x841c00d085a11560070040c3c0d2148144842c005c02c030001160030842c0c40e040e9203031100e200711b840907070090300c100c0082c2001080b940e038180244081000405010045941025402003e0301858020710030301c3c003100700d01480c40383e00030010300ca030a55126040728101c989441009403603031003038202140407488505500100500118035000c046c503c607802407100501c0c0405070005004050900b1f00c0c0258200030441c0810001e0242002403120a94804040d0a00341003039821514139a1061441ea4581200c0d05d116503004140c0780356071181d4403a800054422203010606201c001d504c070980e6160101c800c5e0080503080f00241c011500200d03410038040c0c14010620019035aa004003c2100202c1c1e8544031000c4015409040c4000018044030f110203000381912040343c004402c035481411481250180641e0f04c0306880394490410035245003107514000001d0301241660051015101000c5003415543c40190310880d10590850024030400c04003140c2107481d40d07003e02400e4200c000454140c1c050512 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 929152940 1250 929151690 929151701
    0x5161b0803071206030204051e0901020c0613020f10020d03150503060a0905010e07060513051f0305040303090b1906090528020403020a0806010f12080a0c02010c080307020c04050109 80
    0x10409000c515580d54100121030480901c201455915510140440582ca85106052188a640c40b40c0054580340d00c80d41d40e601d0f90000e2081c0b659178010000d0a14003800420016000308058540385102d030030a00c0013445c05170004510070740000d0b810740781b90070f1154001219019412961801c028284141542c54161000d0b40691501a4006004607282000d10f41c040017606004000024806564408640c02d00da041c1d070040c000074601203805a102c21003044501e004180c02c81e1b0003800c259440840c00d0f00c2c040100c000c401410b5440340081d040c03500a420414565070301c00c4000e142880e003184405280d1248c3d400c20711440d13103412030105110425100703890007184584403e10715808036511000c2102401042d1131030581c0c09000001c0180c0307c40040c403000c0d18103103014008542c10100340742030080c9a60710014149507401160004140c0c840122200320940d4030b40901040c0840c00141d81404494400030b046010000c10052007990104410245000c115400d10560f6030300c1c40020306030342 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 929154190 1250 929152940 929152943
    0x1e0a050402011704170c0a0309090903020a082512030b040e190c1e080f2b2007260322030c0b031006030219080c0d05161b 54
    0x100401ca081d0000f02d03010701415030040c4160060701e04100d684540503503a800c4071180304940c0d0711500b4030008254100800c20050181c0b03031801c01684000ea00d0095840038100006041084001403480e038001d05122140c01030780340c80400d2100303075a81e490704081804a250940d40002e01d807130000f015034907140c0924500d0218070801442e400c1000c0c3e2142496602c1668102c41c1020900e000041c6d480d035161480050101038000800200d02d060038243c1032030401807211106401903680c3c0300d03040500705110405103900444454950349110019a040c03440c4082d146039900070259514084480025204180d81000c0d002042c1d09134030036140307025164102d1a0b60790030b8105121420000f408150300c859030700c00e0011030b810100d5885e250a410750f88190800c00038407200100f000003260603208004014020703850708515010b084000040b80c408603160500420402001184401c1200703820f8440d1b00408a41c1040b045c2410380d41d0005446440a1241c04540c0c1d0080c10304040904140c21002e05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 929155440 1250 929154190 929154197
    0x50606040b040204030b130b07090b04140f030a14160e04120915110706110c04050c21040204060503010c1e050f5a121e0a05040201 58
    0x9485140401014180220701e107a04640e0900c000030200d2005038549000302ea680c91541c20300700311303410440c80511009000b4018421402c1080100e86400301c1142c04481198040400585a490006d08580c050303100b0030342c0c10301c1810141800d000c813400e44030140c80c0342d03441100c07400b8940521842d00680c0a2107192100d80c1a80000f50128414100b240801002c1e403410603002500d48908080c1c508150089030b00141803410701d4044034404002541c060901c078101034181128408986a071000b8100401d03024986400c00318502c10304031815520040c210400c40a0102c951401c244002c080844050344101e040c048009050b00341885070302e1000c907590f99002c400c0b01141c07000e450003c403d4040d100420008006c440491038005003c0e1003507a03102c0c0e0030961510424040c459a1004411710841500900048400f09805684904040c00403050501e92800040708210781e49010b13031507403000341c42450010054002c06006e205001e0800c1c80400003150b440308044841261000c84009012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 929156690 1250 929155440 929155453
    0x260c0a14010c02030102120f16140901050a020c030d0f0e1806092a07034104050d08040303080f01080613050321160201050907090e03040807060c0b0f0405 68
    0x455102d8002d20041e180050000347c47e01c02814015940c01c04200e51601110004405009a04403403c1382c02400c01240d18042c01c4020381c501c880c060380e1180041d5203060100025a550519000303200c40d02d2200070007425102c03140c0d00303460302a1030585012081d0b80000e02d102d00d1040946040c0ca01840c1d42c2e0070794441c0050b0359031f408080c02001c00c4c01034441c0110026414050015048026074a01c0c4680328080c40750b100d1140746009005800950301c078101c0d4541c00c04008071a04034100e101691145240c582c1e03900c00401198400451050350003103600602ca40c4481d07020b000b000d40041044038820ba0b6500300d0f50343d460b0f2146160788001c5c00f584007143c00c0500492015800350380800385031809042964035000407045604440600c080004030039501000070000c500104500703800303030500103000030300c442c0c60302c48505034864805018200f18150f80d84040d0307408010030802d880107072401303404880d01340f0b4a641010b080641c0000c02203a01501860000b421068085401d0780902d0b03100005020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 929157940 1250 929156690 929156729
    0x3081e1b0702150d060302121522080409061505070f06020901051b06090c01030902031510050a03030e09010504090308040b1810020705060a090309030b0a06260c0a 72
    0xd46600501080e40d1003d21400c43e80762540b8988020041000c40c42c1c2c000540514520522402d20042c1000c0d020a401c04078400c85c0114804e4001503000424250030000780850b44100e040d10910018040d000300e501040c080745240316507201c402550641c8460303514281e05090212010300c16208000c0c0031191030f003c04c100184007600600148036050500c42d0403d03081d109200c40024040700005500c1e4400410300c030f41100700344022156108203180900c18000306402199442510540b21210301000b44000ba030141030450442c40035250080509062581e00c0c200100241a401100c511881e22440005020324080c4039000c40c056154841000300e0b074564035554200324000f0004c3e204010080742c1f091000f03d0900500e102c02d0414400161201514285186481002081d240c5c40520b04a10700380441d400120201c02c40f0f0b40000d00c0031280c2e842a0004019080c2580b0040d400800c803613142d5250350003c000b0150086400c0121124a42c804080016aa08610818000302451000503c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 929159190 1250 929157940 929157991
    0x201020709020c010219180618050d0618030801031a13060b0109080706320301030f0809031507021510140103141024050d0b1201050403081e 62
    0x1504583c45000142400e000c00300c07101c210740c0c44070003140004800880000090341c0304001300c0050045850494003151040142c100300c0ca4481c020701c1d20551207220290304105403500709282c1940040070991010500e0302e400317803425100f03000c101e0345240b2140203000550344000c951449000409034895034607040da116007004180703e00074541001401240800c81c10420480b0328001d049641e02d030704801c0e100d402c00c0c0303005561401001d0102500c0030030700601500c045096030305403034000c4071921014407145000781f400d1140b8803444e6003500440c050f5050700d440b1603100394840d0409400360340f0122041c0d41c041c40384640c1159400d10100c3c0c0d0080c28800050b8040f0031105419042c10006000c88009090010a034011142521a580711000a00400154a0402c08000c1a9045aa040d080030810141403809a41e01d80c19030690b8901d80010603680c1c000b60f00c004507058000800c018101400c008108910444075423481d5a1400120f00780d0000341046203103d0401c10090710001e40c501182c14 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 929160440 1250 929159190 929159197
    0x109150f0e16090f0501080715091e05040f0b100e0f041d010b0a0b04210602030f0105040b010504030302070b0a050403080c060619123c060b0d020102070902 69
    0x403095a01c81c941c01c103692081200e034010708010384440480c5031500560806581c890245200c041e030802d070042140c400d000410300240c803030b2800e0701007049024000854006640350700c11010a0a00f440a00940c0c81ca18a03484c15100169014000d9000901701e002c151100d084200d5003004074101c0c24040c440c07017407030103c480f044000c000343c8003540d80307800003800d0b01d92020000807403807200d003484191494244a2482c01c490309940c5014881d19190a132102400781d8030680303083c03aa5140d285e51100066030701d1101c1559200e0070440d1242440c0210044038074090182500a0346041c070516015801501598102ea40c0f5034000e145041c10030f903c0701920303088100b20206002003800003100042440e0040d05045004d2001003045150120800880114030070a0400044208400b84200401d050710220310941100046008032401804c0c28003030007503082900039451103000d00c54501d060060f403005010b030041c1014040300c0c00c03240401002015440c402801f40e808004104600706454026 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 929161690 1250 929160440 929160461
    0xb09030d0f0516080f0705101b08010303050c0c1c020108060a1a0c0a0f0f051603030509012106060f08160e011809050103080c2a040e030d020a050702090702010915 72
    0x101e0b030602e04101c0e03c045c1950481c02c0300301d45980010003070082840240c8138100c0c1041041c41062070340722110101620020040c0000307010464002958549004200001c2c501c20001074041d561040e00c20455025080c214481240000c0300c01c03000c1468be103085551501695040101d1002c9595085034000f86a4000702090803603028206100000c906190407400c40d05005185c03d0b0151007071751500311304080b000410f00c01d1012800c001800402d50010a48030303030240c2820611049245086296a00003110000324142410b0400104110790300c0394035004103402036252070110340c80e00844518941c5c09404101c000a2030a00070394841c1d0301c607010040c807078645201040c182c5611103002405480d026001511213410000300402141e03c20000000c1c05003401300003070141c0a098200754020030070310b00f0b040c1c49262101c891000440050080342c8003c407624604540d2040b001402502980141000780d20410703018000504030781c011701a40442c15804884031001034041e045a45c0109201001d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 929162940 1250 929161690 929161703
    0x160315050f061309020d1509150501030c0210051008010b06070f02090c07081215120a3f0f110a03051e0d0902040e010b0906060a030b0a0b09030d0f0516 67
    0x400640001c5505c000d1074078034503508000c50010401951241005559031210040320b10344a0440c038404034255100b0291507091030003241345100010200d00c0d007d9092034a030822880c3c9030501400c580100c1096003200d00d03c00090105044400410140740550380020300300319210b91000c80145014605a0303801507404041c1030800ba15501c4c1c02d580fa800c1840030824040804040c0242e0507016461945944403c5581d00703c1c02040910103915000b00160080200000034591403c1f0510072201d9120400e91140c82325001d00c0b2100c0140701c6d00d01c401c8185000c41c850041c85010345200d20602843c10303515000030940343c201545c0846c3c60340d20107002c14001000e01030002a10b02d090b04002d1116020440012400c2c82041c010030048422200121b08568505440c040c0e454440400e81540b04104954030750300c0c0d40d81e1030800c1e4040c050f00b000281d800320446501148034100c907c003400b540b103015401c8656980111070282e40301350340405000042101070003a540800c1301c060245520700d21800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 929164190 1250 929162940 929162977
    0x20a1503060b0c0607391502160b06040504080313080f2a0610210209180d02031608090a0e270303073203160315050f06 53
    0x6080c000c243e0849070350036619400241c2131200296201c20b40e0b01c0c0c00880c0c0c011160b13081881540380c6088001d0340184c1c00003080140f080c00c061020001204000341c12034907083d035031540040c80400446900140444150b411100401c0d12400d0922a4921540c0e1140c0e06c1469503c40301d940790500e0004900840d4003c00420401020040d4040685140300d805040428201101c00c04482a9110001d00445561042080180349142c40494000302d5a08030160380345120f007250040100c104114002e500585a03c0c28842403a115a440b060bc60f8030790829108010205041282c5134032641ca030b2110008221403007080801c12840080001c03080040c8500d040d541e48202c0c8803500a8100c51450245040300110318001c6412029041d00d81409006540345150049014203d050740c2c0da90f10740600309031054203908980c00410440b00030850b1101302d13101c1c503243d00000700210341c3c480c1c6030f0002030401e00005040c905000d6540c040da0030040c004150b03802140d085c40b143d504002c403a46034060044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 929165440 1250 929164190 929164199
    0x10e0d180801021c0e01110405040209040b030708030705150402181906140f030c0d0f1707240c0206162d03180c030b0c09091003060608030403020a150306 68
    0x348001c0c842031001d03104d440407924840742c02c4400c9510030000d0310a80e9050034402100002c11b141160309880301107800603290000603001c200200b030500c1030907415102e560320104209000102800b003862117501104c05400c805400c03040c001c1c40c1542e009400020301051051348510001d4850f42c004181080c0c4096421510389001c10744400e9071141e103100741440d0320504a400c0006015003060410313001001c1201081d0089051102080c0303015121408600c12041004894800340b100a9494491035844043c2400c180c040c4d85906003451044220780041c01d00801520701800e00c400d8030a4014121990720041c60148104a80f500c2004128005601100d550f0030303070071441403408140480729120b40d0f850b01d0250854a0048040d4140b0f61244503800c00180c7c0f915251082d81c0d40600e880140b5102c6040780407003405100d0700240e20010b004108800b4421150a0108490244409014042c3d5806c0060f0300c912590002a4100024460500c00415290100e914501d1249000500705d80d89 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 929166690 1250 929165440 929165443
    0x7050705040c270e0108010c1d01031d010609060f03030c1b0510080103060609050f180c0d0f020301050105040209060a0e28080d0219120e090a0b040608010e0d1808 72
    0x140071000181c0c0c907030700103004c009032012645000d00b003600000c0020b107510b6403010300b110500301d1401c0f030b0340c220484400c20300303900c00d17044030605980303a80b95090700400720b54200e0b01920b0345000e043c080d24a480400114000c041040c0822260552280c08402c4e100d82c4604d200e110b0744411141c44400024070024a945980001c002030903048e64072220b0310350440c0350030010382d4029800510100e04010502c0410800601c64a03000034220f4101c1b000303e03000e81d030503508214200022560022203902d029081c0010003030302e4491240b084008200700d0b030b251420002203000322454180c225030f091207000c5005001d103c0000c040600200219050071440b103048d00b8403040380350100d00d8040280020000c1c41380400213012111382e0b6001034445091040c0031440808004c0d07030054441a0402075084031980035082511305d054020b0901c1d10fa038074122404001410307032000c03190b000300d20301000021902e07810b104881c10a2000d1026100020034000100c41b18001d41d01d11307042810400300c00040c031100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 929167940 1250 929166690 929166737
    0x20a0312020a0506090a0b070f0c08030708041a0106320301060e031006080c010f110a0c17070b071b1d1803120c0307031107050115060507050705040c 66
    0x4581c1c02400b10880d40d2420904007500034066011641c05035525400044803030f54070ba944103440b8a00a51501a4044111020058900040d00407100042405076041e0310044961007107009003082c0c6500840107541d00d9010340240320315000601200c12102c0c40a507401400304000d03c40c2d0000d02148400141d91030200c0d030080c1d01c190f020407001c004190700b03402c090003440319580d4901c0c820056680713060700d00c0d6250502a10001e0421a1060f0101095030250007482401c1980c00304982c0a98110b203008240542c5500483d52540d0408681000b5218001154815690411003071418100159100070b0f200440010003042600e80346008500400b0094aa05460b400c0440511080c01c20080d03101503a400f00541c4e0300960010402c040d030070226842d0194000103040103131a50783c0d49500040700200210000e0380d1081a0015041c4203014054200c6451000043d1400348007541d108010703111481031a4005040d6001024200254034003503101a02842150500440064450030b0344441c0c040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 929169190 1250 929167940 929167973
    0x32802030c15040b0f04080f070303020c1b0a081209060705011b09090507050405030d0e01031506030911030d0f05070f14031803010e03070b090703050106081e1c0309020a03 76
    0x15280410402844000802135030046565103030402c050409403940c200501c180801001031880001d480420184207078120b030030b02c050741030540364049520446c0711403500d003001900c3c1c819140071601003804000800c10740c3c1400107401047d46047c41507000d002181c1c00003070040e1115541c80c00051000f0035680030fa41e080707000c035581e0918154200030015045a80150491042100038001400b680d1400103002044205e58102000d01c1020400105d020b040c000303c840d01c0754010000d0004400cad4068100742c5e2454496420036540ca0a00018142e607210745803001c0d00099880350418101e580a00d009080c0140248806285a02682c4512a034603000a156004941c0005203110246d05804480900481c0880c000d00404045401341541d138000d00c18081c000307400c0035000c01e68070002040713107000a50b8494001e12a4030f07038980003252201000c0b030400605000c54083d1f11010341c00402c100c1d0b00060191240d41c074001840318218024118006e041780c20440c04600480410840d032800719401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 929170440 1250 929169190 929169223
    0x61d030d150f06110109290a0e06071103040509010b070204050609151509030d02011401060e090403082a0904150f06051c150302090603032802030c 65
    0xc004103100d8100725800078000703101069941c1d00500075020900300070300886800d443c10b07600400800600500511030500014000030040c041c9042a00c03207107422856004006540c2c07200c0e903541900358800d80d04512220f600682100740000c0c601030207490b410071112081012a0304041d12207000ca00018420307004aa5040d801007400400c514243c00f49941c0f15505030350407001402c040e035104840042809001e8891003210a03000c1500d001c407001d80e10f071044020b08807080441d0f030200c060b0007080307052603078a08510880004980325020b00140c00003103030083d0030f0100c00d58076620100c03011400585500b00b4031400c058400180c0c0004404140803100c51140540d54000c4142040304440c04d014118821204512080100b54100b054140444103075040013a6900c4a000146801c03c2a9030b000706d200e5454001150710911035820503205072031081d00d1816032034480d4000c0669a005001601d10320f48100c20481c040e04003840580580c00400303004480c2482100001103090200207021a20308 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 929171690 1250 929170440 929170447
    0x61308060114092503180204020d09050c0a03080a030f11030a0c0e01110a06050a091502030907090203091b1f0203132909190e0901290d061d03 63
    0xb51610400e210b40180581e845294032100e039a460100d80401d9110f64400e01d695075a88404d1040c15048030118640d00500442d80d80140010000c020104443d050f2054030a00d011030a45007003e4a520054035009410701d803d018500500310040c2c000b5050100b46103484424010010315400003450240154090101307110300c480d1002400710315090700141c10400b00b01e440000005010840803c400d41028000c2042e5480040400241103138690082000710241e0b108038020025070302450007004000c090b115141e0741c0303010103000d901042e1200781c01900110804144000c2a95060b803440e400030304804452400c500c0c00c0a503002000b030341c20700507800003d00e500440780c003180011b02400c0740c81c952201c0e0300d20b0348248401c80c658940300e0201e040000070303001240e44d40d414400400c540301241242c5446868610010f803c04094034490745540c240070080d56110303290701c0c7c008000694100c1c6c5046c0c032060342d002c100001c0e4041a05460056581002c04d01e8418a400c80310881c0301440d005694 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 929172940 1250 929171690 929171729
    0x605060c0c01120510030b0406060b0403050d0906030507051206030c03011a090c03160809160f05040c1106070f0c05010e06010806092a040f0e06011707080c0613080601 74
    0x107a2074a44021102c1c43d4501010400113005c411900380599803c1950b4a405d592640307030090003000c3c6908090020140400c000042001c005044511682c0d2075a8a446c0d039580c94000340e00395042611a000842d04c2807040c83c0c42c411021681d103501c203800500320b0b89010408004a8216001d01c030205c0054410140d84907081d04081c0503440c2c000c40b060101d10724624250a610b130030040c103103182d0800c210241021800c1040100300700111007100300e0054810940c2c0303140c1c00940d8907840c8070341400b0303908042c0000c50305030103501036000c80c09011004c0c0c58030b81d4a0040071900420082c0e1403d05002541c4030060102d00e00f40704441510702488024001c035414540038520700b1307100801000f0540c1c0201020208400303000d100400c0071800520300c0e250fa500002c00107010307040c0e80858040d428a4401840111100012050f049450308052008240502101c42d6124036607409003690660203140700d0221400e0000040c58075207468060304410b1500c030300d0407a0130014203034801064918071049040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 929174190 1250 929172940 929172947
    0x721050411040e030f0f0318070f060908030316051e070809041404030f0e0607200109060e1f20010504060c050705060619091e0b040603081c0605060c0c01 68
    0x42400d083c5400640c00d1052846018200703114100c482010341c032010010887c070f1044840c8600540d00f040080d039804580310081065561071300d1281c10700291010703000156455020003101d0041d200300380844945243d141d4143c8943c1d120071507101280c0b02c09016180c2c0071301c03600c016102c420310540c0441d40c0ca021441c10001036402c410316596040444905000000390011499004d04a050402100c0e41c00300301e0014009000705c100291448072250103800e2125041007514429940c03d880d00003002e9200c1034210f440000080e0940d030000d884548045a0f600d201c004001c0c03100e0319107030440030b19581e08c18403580c1c2016000c03001400d0f9194030a2200300000f5005128405603c5d14040b4180b0f50310703440d4160f5400028100f0740c0100c5400e40d4a01642c252840503001600f80154103115a11002d14003002442642c1a103241c1c1da4a044a42140c0346002d02440040b40e800c000c0c42800d0038080d1081c0c09026803440c00b400e44850341d40f0030000e0300e0b45801015083c0340355058003034034a080d080c00014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 929175440 1250 929174190 929174201
    0x7060f0b0603070815030a12032306010c060b04020f0a08070906142b1b122c010e010504151a0105040b0c03280909050708072105041104 60
    0x50700c030381c405004100b1915485414194020501c1180840a51052021030f0408050741400f800d030300d00c0c1104296540d509500070504800a440c0036200e500f0450050000548041c3c9145001072030b0115030f040858103035003203001d44000007840149071a100c008025042c4e480148010042400c0104110318160071840300c030000c04aa080c40c40e640000424161501c4c80341e40d4012240c0c59002e003e100b100700303510340b4804c460303140e02504015040b1464003071520242c0f24043c400000c0c403040c0d000341056400d4000c0c0100d40e1080d10300703043e4031740006804001d121480d5808102540da1145c015466007000d01905004078000c4220142c03050140c0d1003036003600c5165403001d210403406441e50301983d80c008112021500d8004140b45c1383c251409603c2e06510407001d078941e80e0585a00b06083d030003058900103501101c5921400307501942c4403608400d0314011100d0310049100200014040b40c0a01070410103041c103481024807100000f90180102c03103041d40c0503103454802e023040240781d062a2107103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 929176690 1250 929175440 929175461
    0x9041b0803040311130b13062c0109050405160324020c1b06070606150f1b0201050307051c0b0f0d050606150f07080d0f061410090503010207060f 64
    0x5949450f04584800141340440c81c0320320301441a00d1481d801c01c00190b4032081500000a100c1c03114000c07114011400381c8201d0007040c3d13025203030340d880481441884414107044d620350340c0c4078a082c3c0c2c83c0c4a41c2c48000c1c40010015a1140560181908150404411400074512881c0710103000d4407460b1142c80c0c0d4041c50242044907074410020040444000940b04041d0a0720502c5000c030300c00f0803004141c0318003860307400a014505048002c158113101001e090300c802183d40d12402d1140d0650f20860f503041c24030000c00880342001c01803d015511400c011984071103d820860b00d080341401504010000210706c4213091039a4039001da1a0740780c0181c84070031031881154403405168550316865110200540582e01c6043c202c503e400031502c0300c500b41c1d804a02c604440944800e500d081c5079a2a61008184c202e640c0c0c80e1200c580391408440c03103044140c50480d00f560b94045203080501840703001102000c01407000301c800014039680e090005082a5204440102d00c0b54202907220781644c8111b9003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 929177940 1250 929176690 929176693
    0x5010614070f20030d0503150429010311030718060305011802180a030c090b041b050c0f011b1d0d231002030f09010b09131109041b08 59
    0x441e00440e6072610701c000c0305500049880314210f000300040240c1c00000c52850382600400114a180c0d60300103025501c521200c0504140e09058801008201c500000c1454108080d50703c0300e9408240035401101059018100001c914146003c540c00d242c00440b103000005055021898080ca400c69549008007a40d06092100794142501400e000c20301000146d0400d50204100c5d000d4083c844000b060102d0240071034104030b80b60304001c80401c900b405202800c50900d00c810b15a820984240b08000324209501600b100d04150100c3d0710354854461084a4841c0855500d0180400c0c81501c040c2400546500e04407020140003030242c5c00c0c1e112800c00304040c3c55134851003035280ca11140f0321881e800840002c0d8031a0100d552288041e8400c0074002500c1591001c0e4000c04d00e03907004500489640c0140d4400e41d66142d0500d0a9620382c680064104900300d001c06c01c00106c40c10500d8030703d84039203000401c85c410200441c928110480d000d81e02103d411021351b07c80410180004007800140c0c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 929179190 1250 929177940 929177947
    0xe031603331a0d020616020a030204020406020607020f030c1504020f0316230a0b0906071407050a0803130308091201111306080112121103071401060b070c210f0605010614 75
    0x10005240c5005074200d203611003000d11b112404564a40d80301c04099030b4010011902d0b00d0301c8000095880e601100d030308016100703884c0103102c0004c000003503842c120b180000400c014084440c0f040319200c0c016000302e0300000b49107129001541d05201d180c024215040415003014070f0200031120721000000c03502c1e030300480d0803180302c0580c444030760400580719202401c079a200010b0b404120a407007105000782403040700107690000144041662011a082250300c40007007920352000740d03100d1282e243c002c0d9888201081c100b0004800740003130020460014414401d0703403c161003503400d451840490718410807000544030740c0035051404840280c4040c0c5884400741d030400c2c0340d20028441e69640580300b04002d1401301c800510814049580314180c0d003c1d40d03240d500d989071050450080403103000c41542060004684400c40505907500642c00c0322802d850f15140032409180c00840c617103215042800000b0140c045220040760b1f04119220340400102980340c0341c4000c041d880c2c02d6150400480c1d081 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 929180440 1250 929179190 929179193
    0xd0305040b07142a0f070807090e0c09040221150a0c020615030106120b09060a15061103040b030408180a1802090301060e01090c0e031603331a0d 64
    0x1c3c09898501004103010010303000211a0b051008104105901c207503c140d1a004444000100700781080390903840031220280d440700c107043d0a41e40030a10032450b50b44075003408056450250001c0f5001340c00540280d075404182c06440240030b1924801c49042d911144a409080c8180c40f8240d62080401808103e41c00300600025210300b0094801e1468054400c0000c0c0155401e507c10401012403614425405c0c0562074003060072401126154401e000d4500007594100d054045c0c6070507480c20390741c4221154105941514092001031448280b444240004a004803c08000394041c40c06281240c3d1581003016040091114601046004480c03c01c3d0802c541c0c20b540d20a0407070303d8454140581c69501440c0882e00401d102c1c1d0007100490300a000008540e54194001494406540d54800030700d014041499aa0ba40d8121004c0c000000d1500400116000483c4d120f82080c98060502c00d200030a030b1402840a80300a07801e00c080e54547d8282c2c110038500043d403120007000d80754035030050000e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 929181690 1250 929180440 929180477
    0x509042f0909060d0c0b1b011b02010f0507090b1e0d0e0708010204050102070e0406020d06090c02070e060f090712050903190201090f020f030307020405040c1509150e120d0305040b07 80
    0x2d41b25000c41c804020603500c4009007208403084c03034003da02d0000c10500042e00004008a00309860500240d403038292100a9042c1c0360142501c15422030302c410f00117038a8000c020480b54000c54095001d004140d203a080c4208599008081089081101050f2864400350b42402c080c0a07921082e0568030401c400c001070b98010a0305021110303040e0025446a1b21410034002920659041c1d40280f45414000720711400290f00514800c00700b035003118100c4c4d07210703000e0703c208400513102280c4c800541d50444209160403015945d00402924010389000c404880050030ba81e01078031248150341004c1003220786032500302e1150300c4080c0030744028490510300c1d454560406500000c064090b00407004c000002d51020812124555406401044649001e0a0a103500905030017003a10202600e0400703201140301d0340100c000e0740c450000f40b002e000e901120503a42c15800f409030030b8008200d040d401291200620405c03502c030310a40c0300814545028545232414078001405030041c04102580807421012 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 929182940 1250 929181690 929181713
    0x10207080f06010e3c060402270307080a05031e0a0813050708160801110a14030a06050604030605040309211e08071b150509042f0909060d 61
    0x421311140750309844690040400e00c24003105508461403804201e110540080060256440b03110a500c03200c0c0c4841c001c000a9110741300c1c1072801c42c0c1c0c03e80071540940c01050107228030300070010129140e03035941c1d070f803210708085000000360349607080801c051528101c4410f00311015803900300300c2d81c03802c480c05002424080d0060065200da000c07000c2c140081100400021019041100440310084071074103e80042e409503003d0030140c2d500f8600078803c0c00d60700e642503030004081a122154451000d12083e040c0e0f40000f400a900c0c41d0311164000b99035129000100044c0d4080e503808601464907040180c000c0c4180c4c1d002e8610440c6400c100030075002840000120180d100782c000c0d04846a09004d4a0042415540600f00d00c03400250101005000201b4041090307440c0303510442c4695075003000888407014024080824010882d00301649481da12512842d090800c143c0307e00740d44070010700e1140c0d0900c9245561030b10006945c00c86031401ca5003007540328004455890702c000441d5070b040318900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 929184190 1250 929182940 929182949
    0xa23010305010f1e0b0309011d0f1f0b090a0b1c0803070507060e01020d060305060c04050105070b0c221d09030703030c0507150606030b0f0a0501050d0209040509070302010207080f0601 81
    0x21300e10785444c0008102100c0f00340082c00c0d07094040703441e410701d502d0170360003000b01c000c141c00c40c001c2140381540c80200c007180e03c2920100d40703000b421084031068000d64199642c0351840c10f486036030b0440321416a889010070341c050850f0850004041d03c0300780034840c1040708510480003601801241d980010000e030116a405121403401c0b070b44420041c9043c0014000305107804000b540003081d1302c54044055405541201d00aa04466003512102d00c20922482140511800204200402004a02880d00c03407a080400c00803080d00d0500000380c40c4e0703000d890b214070540700040c14810070495075408508000505d4803a4001c0350306414030f1400540d45e0711407841e0087c2415140c3d5168a141d9002d04141c1d4585030700183c03c227603140c2d2155200c5000b81038900489000c00d2802044030603500b403000e8117018200010b82107002d55802d0000640b001d4000d017181c100c1d4a9020010a041b44c1c07250b0049902604c0c40d2001450f05074158400681000038903001100207a11442812011b00e800054803070441c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 929185440 1250 929184190 929184209
    0x20105090105090a030f170c063408060a08030405091807030b0a1410030201050d0f0f1107060f0c050406080403170115080106051c1a0a23010305010f 66
    0x8600d11001620180101204154800c0d60309000200f0700036800302542045200303d038482502013512030441c00c0d42c01096a100c50950103d03000441144903d032144282c11007a000a042c02d05500107525200344940c001c00c00060640c0c0144841814074419400c09854142c0195040500740000300e00405401098840002d0501042030855034051000c1400b464100e0015a2035240022813100542954000480c40380503002c0040c450104440307005041e2071b0b0581d038803468a641c044052003e4034042003100d08041d0b4443d03c3d4641c00055200c0c400086080c0c440f026101e8085003020421a1080c1c241c0008041c01c20324110891a03100e4126020703034a10342881c0702039481c1c60400319001000e00050002814105c3e0011920b0030091100c0041c851259994903416030700d81034111000d00611f403901c20003d0748503510740b01c179143c10f40086421140d880f580d1032440383c90b200081d030140c8995000052084100c0d5441500c0c6210400c0507040000030301b400d1001d0b515040c411041040280b246e007a85 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 929186690 1250 929185440 929185447
    0x60f04050a110c0313080a020a09051b13051509090613090f0b010e0601110319020f0106060809100216151404030f09060c080415110706080f01120f020105 68
    0x71064503600211144400103659a100da00c0000c1081e50b85c0d109410402c2c86034403410000030158000100c0c444050707806170060003600c2c549808040903000161181c4603001e20440074207600c040c140c0180540010319240080785030b1600045c451090411a2080c0c903040d800c006510340d548641038500e4120300f00740c4641841d14402d00018000b04075000e0020115030b10000306509010009482c3d40c181d03420020705000588aa00040d102650104103818281d00144041c0c419100310b5900c16041404900540718641e00d4007500c6400c588980e003140c408100c0c61301c140003c52104022106600d01d28600440c078100e0010112603986503003200003030603420040500c100142c2c05401090303400d20020040c5506043c1854003514290028511000107040b0640c0060024861107d00c0e1406402c20195071802e03050858040147d24408501e4042c000044840411070f0030821011000300031966174000300341008040d00f5900c81060b4480c603441d617580100d100101e00062504040b540e03090810035503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 929187940 1250 929186690 929186701
    0xa1202030f03010e060f040e060435070507050604030c15141305030105091207141204031b140102030d05151306150221070201020a0819020114060f0405 67
    0xa1803107200030700d141980c40071000050300041d900b0113034024007080b103004c044081c810090204072100e24004101d0350303010030003240100e00001701040741c0307096001c810400c0300112242002407084010002819000001d108014000e05104030780181004031400ca16103842d40c1c40b00880291240240c815400e811442e2040c42800b036031040400d018500081e60326003002c5d00c128201c1024520440d8029420040001c150501c007050800c01c8464402c1000d041820f2038030360851000c00d92000165034812840200c40301d00c0e90708080c0c00150300c64114100d094041d200c2e000b0021956a20550008441c0c440650f0180e1300031090351400c0382d2080002443c0d5981101401c0c12917012141a50400303d40840980360041c0780d00f100301903070300380007104081d00e40c4140100ea488081e01c0d0520080003046980000b01400340d03000b002801d005104403029440280c9844840d98040da006005441414408a00c017030f4083c041d01408030004656140c0c20f10300040030800720700021800728491542c03000010b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 929189190 1250 929187940 929187943
    0x110909210a050415020a0b0109060b04030b0903040504110c070614030123040c02010e15060906010f0e040204060c020108060a0806011509030c06020d090801060311010c150c120c08090a1202 83
    0x4000b41101105046004c03608107000e522101303810400d403080f01e01c1100201f407180c41c5c0d0241e1411103000c00c0e42c55150524544480d624400c005e8001ea190b40010400095140c0e074601402211001c01c0c0001542d982c042c02c0340e640340000aa100006028610300100644003815096904441c05c0907180751402540c1d000040003010b40b4510300f40d000b4074000344007200643c1503024201205000c3c08032452001d05d09903000c101c400403507040b9403090300f40000034015440754030504140704d020709150f00c000552030006810398015400840004d0485881e100a40da80284125002002550b00d80c07142ca003008962a1928014041c2600c1f0101c0703000b031019580d1051020a0007036800440d02855952582d07002501c489001d01c010001500e003000c00300399514103108980c2181c0c2c1c040340103031001720000d005442c250b003855419116444948001883c0c501ea60047d4800f0180f5942e030a20305108140100b8103e44c465801001005201c80c1008400d030310018060b266542c010500e102c1d000c000c0c001c200e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 929190440 1250 929189190 929189197
    0xb03120c0a12090f060e03102d0506041802090a0b06091e04051b0d0f020d021b010c1d0607081c020405030d050a0503040f1b03110909210a05 62
    0x1407102d03070012410750703403550f10049040585100c00341040140c0c0d43c40c0000c84041e401c5462441d8181c0107004448450001c60344007507143c46d00c1112200c01c06205214240c40d07072842d41b960501403034541c020041c052500e0b100c0e0b0440306200810708100c59021350080761008000230524034032103540e4510740049643d4035003a02e0707a200c001015a0b40006844003070b51044008500802e00603405c0030301048913901280c803407841c0c400072032800d40c4c10148841d102c0400f500754540060b0b4455802c00c051410308070140000e0501b2201f225100c1c014200d00c0c10554211103140542c0e2082001e5910b0f420407000a0703400c000c1c400002100c12a480c1d110314100805035115054006d000000c0840c400c603106402d5402900488004078141c400140c007a04042c2d44504c5034215420001c0c000f0000900001c0000401c410790074041c0288480d20300d45004c0744500d0b8000740d0401c0e90183d2108507401001d2500d00d0a80c1c3d44210b0480c082c1060104c0c2c1c001032508050082048038004801152405480744208140c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 929191690 1250 929190440 929190443
    0x40b16030b10050c0105090f030a0315031406041106030105060901030914060702071410080a05070903080d0603021513150c051207030807030b0114091518090702010b03120c0a 77
    0x102107941802c0c00003810300c1d407040c00110010b50804000450b01d03070021440c0c804843d00d00e0044e514141e4400c0381113004140b82c1d885100210011180417022a9030742038540103410460f0014041e9007001d041107000865403550b00c61041608000510070390311804241ea60070b01d820308001c10000c015251000e0790200d002203801180c4640300401444581c0000d5400c21241d01c18410040c00e4521000d20070701c0100741204102045444000c20450302843e0302030380d880b50790340c60038118050f180d50344ca801642c02110928410f80d2119001d200798034018400000e000d000d85081868001c0d0360321040c072408464411b03044590164106800454022807100501562200c19910950b81007a101d503141e0700110750a50001c0e51000004410b00d01174070410031000016102d900441d4680c080c0862185d1107401143e401ca00050321085000b0030310009004882b00303440480011140040a004c1ca50070f0051803841107a0415803012580d480c00f0841490700c40747c0c400400d03920310842d9849480c2c110341c543c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 929192940 1250 929191690 929191699
    0xc0a0c0c0e040b2d0103031b050604110a050406080a0201140c060a1b0507170c01060b0301080102090102190c0302010c061d010b030606121c1707020c01090905040b16030b 75
    0x1044200030041d4051881492007540b440414256000141540c031440a048130396401d1030801807011070700424217003080d81d80c05482140c00114a5880d24103002041c0d8045440d416000108851840c04070b401001a090a907000c0000e1450300d00010742d40c2d4000c0c880641800007114003084030601030b100f01d51403240c2305400c5451070309080c514407000300a12558403000004034440d218015100b041100d504075000444840c0d03180e040a042c0416034440b0185c2c8445641c1c442d000504002898051402015950001070b1a00ca00d40006814804404207150048400207106400140d00f2034040e8280c0c0e40a00c0e10803010ad0306032404800508480c9401464072035443c103510321141d01500409207001d810340c2620110b4a41c2c90901c80c107100300c00c0c02440d6980208001c90940d043d500c080c0305000c801440c005024000b1048845680b40090300c03080f0042c0c12480e11071a143d43c0100824008000140040184d0301e4a5103c00d2180000034000200104201642040b000e20a030000301d2001070090 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 929194190 1250 929192940 929192969
    0x120a15030804120c0b1207140d0c08040c090e030a03110d020f09010905060c0a0308130215041a03130f15021617040e060108041e030305041104050c0a0c0c 68
    0x1101c40c420303820401c1115403081e0500041124044441540d0146c1d44000b28110251900e441c01c1d80c48140c8100000a141d405010482c4c0300100b0340a04014104c29490b4a00542420305100c003064034150441d0403514105444000c00d40b00c000116007040081b032030001001041e1286500750740c40703454081c0d65a18000b042c485100c00305080100032080d02600c1340e40e0090741d150140265030007a40703016115a084258608040384c081c0c032030268003a4090705032400000c844ea00040100c04188090402c0001c041400d001e240307101c02d038101114a684140a046250000c0301002503904100010501c2d05203800030b1b01004412894421030600c0948195111032140503034a0b020780000c1d4088e52401c41c2855a0344000d4a030100b21020380c4c1e0700420480150340c0c0c400040d640244080c208980c0c034180303104510301c403c9a00156440e124806e983c080b42504260801c0c001c1c80c1c3c01405c1140c481c034946824000707294044000c440218509051145101c0180d05041c4803901ca01d60003102e40907000d6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 929195440 1250 929194190 929194199
    0x509070c05150105040c0e01050f0f0f0c0f060c0306100c020102010e0714010306050603091002130312030c0906111c02011116030f02060f04112d0a0605120a15030804 73
    0x502e015410303903c041d1002c0080b1840548101ca10352541e083c0140800d10802542010210f000c0c002c100f04203840501c0c07450510495006040c0c0da012405200e07050b048000880d09650051000c582c02c080307217480040c01c40c10403200059045a16800c2e075800d00000d9800c09086900070f410410344400c14105a4902d241c0c0c43c10710840901d011500180013170f1070440c0201f0580f40010550b4011030b42000142040118000000025800307402c4210880c41044d0700000014014801d101c0e003608142e401181d1103944000241030308800e80c00a80034060380c50f0810f04155000240c001c0c41d0700301202c10028000010348103030b00408807505480c290000000c3d944600c2d909080c0e00d0213007180720b039696400c0c203103031000708984800c2d09494520000700d00d4000b00380440daa4841c40c0f185a8030003080082d4083d0284410032506e01460b19a2903001d1102d02d117082c039490a940b07420001d00403818030505d040840c1088040480c1c00a0030b100000b95184080d00302d0640c80784485000d9170344045274a1303075284ca8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 929196690 1250 929195440 929195473
    0x9250507150c031a0103020a020709090203031903060e0a11031f3b09061b04091d0d08090a0b100f0e0a06060201090f030e031216150903090509070c05 66
    0x11002811490500c2c1c104c4a0055120b40308568510360707035134003410700d1905040b0f001c07020388820700c81a6030610060112500b60b00501c40c07140040d00c405d490025155291000030809e20300000e1440003403c0c0f45c4003050840c0460b00c0c045a50014680001480810001070014003800503a08802e2003407101041400241e007991720954640c1340380c1550340e01b407000e060311001d0420710103c85e135401d20741100022607500b060f0104542800361030000614281903c510111040301c01802c00710480200303071004000a41c0d814068a824041031b0b01c0c000000e072400c8501103503210704809000f8803001d1030710b0000d8003075000030b0120400b610f42600300300091030780c403501c04000340c40580302c0c2c0d207500d454042c001480030300512685621380da00c800f04880c0c01c140d6031401e42c1c4107050489080c5d054002d8504011407860b60f5001800100a0f0b01c03001c94882d070103030510700040c0700400740c1c42ca1007925041071403001c60380080349807040329000c81399561140c0e03803460211041000d0907002440e900c00c0f140c800000c1c02c0e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 929197940 1250 929196690 929196701
    0x4031205280204080d050f0c16060f0e0306150a050405011d0a050402030c01050307050d0905030a180f1703070b090a1a061807110a050102070209250507150c03 70
    0xc104403103002821a070403032404901c0b89204981440e4407100300403003d54041c01c050b1004c6010101503a0818402501c03050074000b031b05580f209120710f101400d100743d035040002d1040502080c54605007040014010943d00e070009440c82a00f50144800706032b10356a98060a4058079010f072090049595805403206c5040d483c541788442c1c0d15000f000a004d803001071003064400d0380c004009142030301882c00150f480e40c2c0003070440820810108a05000040203003d42c0e820548110f00640c0d440e541840e0003084c00e40c03000461603001034110710420206e20890010340a0350342554030280c011001144003031852050300401441c160304081080041480402e000010f9401481d000c1402e29041c04400d11003902210801d512880800403051100046141d00340e01409608001c000e4100c0003241c1031501704501400c03035140e0740004a031421810170b40f08003030b0481100081c42d180da02020641d501034407560121017041003030124498061080da0300c040120642c3c00307102004840351042006000c0e12 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 929199190 1250 929197940 929197981
    0x30a081218060403020709110408010c20010e031b0c03060f0f010512060f0a06120b040606140a09020a021f1d0615040e0304080115060e03071d04031205 67
    0x811078520169400404906188920b6050380540102801d040101d8001c291040113080741c000280000300340041e0903c00d8004030310064980b4130f21007240070805110707440710003450b00040c1d0409901c101c1d240d40000a5802045081c40c0a8031803604080c9100d2a0035298010168184070f440207211a140c42080458060b11042c92103802c203a88807400c1c040035601580b204c80c1590700101c00a40c005d89040c1685030032040400003c070f401c0755107580c004015100007a084c1d60298014050004000d00e41c425280100020348001034100e003904001801d408051103400807907070300000d400d002c8900c00e001c4603030065801c5403804002840d110124000344509404001200000101100d40c02c400180d01031113600911740084002544e48240800f81c421000350150a100905c80814904028098201e0320540115282c40051400c5002080f81594007504c43c082d80107410103105081c0010060300043e84009014007440d2900e01d000c4959000038a40c2100540c40c06040c4410807080a03030b2880c000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 929200440 1250 929199190 929199211
    0x3031e0304030f1806050c0c1201020d200702011409130c11011109060c0a21180609060806030a060c09230a090507020a06050a1d06070f0509030a0812 66
    0x1a020100c0541d55040411500c1810b030130002010010180306100034450035203600199030740050700501080c4860105000c00e600b0343d40210703080300702840d14030400c0740900f441c00d501030511980d0703a803200041c450000003034100100c1c40c4001c00c0c20400c02d4215140c015019004040d9050f840d054980144816849140040c04442001070152414003507411010346500d8028039013115081000083e07031224401c55294018086200007040384011134000e0002d8141c10802e485400c9000245121030410a14a036030b038010605226055200d104038003a01c0300fa0400c04550f0311000c001a240001c01c84004002c282040020351125500040c0d0340c007201c4152030403000d0b0441072044040e040c50301541301508603041790b9042211184a0b040290000840e0043e00c110b403185e0303158801074550484148008544900a0300302019403c03041015050b141f0b405442541082c1c0340051040516501d29401c10002007a1011280c5d000d010564880342e10440140c1d4418030880100d008000444090008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 929201690 1250 929200440 929200457
    0x120a15060b09030601180b090a090507080d0f081e040609170717070303200a1704030c030c02030f010c02011b110a031413260304050d02010e03031e030403 68
    0x84070000c4282d070202e101c018050001e0340c0c00c1c0b0140c24010b039420390803000342a880d0400d805c078a80317414034001d01491503103202080d040d1050074014130781050b562001c04c1d42d41c801480d1070081540550000c1803500301e071900368000d440b124410806102d010110394000b8010500b880100045a80442e0b42a48140041d098028262012005500503181c029200c8200540c8031600c0c0c0c1c1c0818000d041c0a80309090008004121800a52880040010f200806c0c0c40000318800c049030041a500020182100050344501d81680c008181c0705800e0401800c0c1f0691500300c0b4215076050020b650002e0004000700445100800024060180c0e19801101070005a0541c480c41d8825a19840907405100c0100b2500f03505590883d000c4900841e5505403201c02c1c401c0e00c0b0b103420600514002040038500c0d8135104100390a0031400054015180c03c203581c82000100003030340f41d07082c013110500e40908164048110305000329007076109002c038091440f440100700310001c01440001c0c5019500075551800b0b03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 929202940 1250 929201690 929201699
    0x121b010c0f0c03122d0612020112091401020f0706060e1b0315030d09080c0901050319030509041503150c1b0f0c0602030301140f1c02120a1506 63
    0x5003949000828400240104581c20200b8041c1244c01e038144802c02000604450340c51080400e01d003800302400f444a0303603000350341404040340100000b4100304c0344001c4010105500203490382401c03c482d100c40c03584502c2d600701440319152015a001c40c601c1c009644d5800c44500002e40e55200301d03000c50381c4d00d10301000401c400c840007409500c0b80030007951101d0300c5c81c8003010708101e5800060410085090020741124a902c0912020320540111f03160b042c40d140c01c0c024100d08107000c103803c0c1e5000b0501440108501c1ea80018000c90080088904c0f401140f0181400c603102d102d4800d001c1e8000d820442c5050030340c000380e402001101d000e016000ca01005803640f07101036402d110260b900042c42082107402c00781c2c190b503d03400304034450701981c4e001d0800d40c0d880800c0c849081d480040560400310041003401d0480e070f03075030003000ca007241c0f01621403c1150020724400010f403440f000c03462882010504545580002880d1403449004032480c80c0d00718a841c0702c00c020040b011003a42d9061802c00034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 929204190 1250 929202940 929202947
    0x1050a080105010e1f0b04060f08250f12051306241a04030b0a0501080105150607080d110301030606180b01081519060809070501051614121b010c 64
    0x90503074904c2008041d594448191104a000e034030703080c8034103803120f000d00003d00d041c5800041000344100d80710842d00c0001c161000e0300481c8000d00640aa11118001d810154003400e480c0280003030a007401c128050040008a0b06000780000c0e584050340f41c071050110702040203040308009032280d07905010781000300520f80d0841895107031042030140380702d0052003142c011419990010140c1d034546400c01e030307807521810300424058804080056940005001c503210a004059200301050910700400c0b544c140800d500d4481c4c0c84d0003400b2006d010030415500e2a890300304500c0049805081f076100c2d6144e040c0040105003502c15a900d2454840402d0080583d13400f6043ea4414161584441543c48403a210760590480b855594800541403642402c02d99803a510b1000e0540da690305c02c1e0600c1c2c801c02c1c5a02e0092950445414000305000005020030070342130071140281d100e0f01c544026000c2241541ca06640884100d50303001000c91015114108044091440802503000744140d00718140244c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 929205440 1250 929204190 929204201
    0x10e0a0524010314101d011a030d18080a031106010501090b0d090f020603010801060f0816120c0503030703030b130504031d060c0615120606030a02040c2601050a0801 73
    0x150004000c1c0c010400b254000380086040c981d028250346104038000c1c43d2034121081c0501c01d103500020000e08042210b02407050000c02d003a00b107030a0558078405000a40c0d5040d40c03408003020003417181004c0242880a800b0300008006030402c84540800a142c0506000a900c92540181c400c1d80000078507036200d5881c900484400c0a5001e10b40110301c0c6882000d482000010b984000072041a4001611100d00840c024030095000040c25402c102c0c3c3c01c0d440590551008161341c0c06000c105140c0152280c0100489003801004241381c2c080e03241685d001c1e52150b011550500011900d0f805042c2c254001c0502418201c0c0c501c1203482100782d00354104c5005075405000220060a440c0c900d258107a0100c164000c0140500c0c1045c12a5468518005045620103031422540544a90b1400c0100003090041011400b9120902d0b044010954418200304041d110781c0d182da00032014240074841c2444030542a4216002c4c034880c803c4c0c002d409100a20841e400ba803050000040c20b0041031084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 929206690 1250 929205440 929205493
    0x3150406270f02010e0d320f06281b11010e0703021018090c0e060408060f1806091b040e03030c0c0c090a0b040f050613110408010e0a05 60
    0xc0302c0440d15001191048201e0504540101c074400b041c030701190289074003801500780e90500b051804144003840d100038180d82c00c1e214040d0f00002c51208051000714000358004004044950030101004800381d9841e61000600c10491402c4c1040c0d070b51b002401c40c1119a6003c82e02c5082089040e11100c0d42282c003140c150300c509810003c0148010300e4240038209007655645040102c80d000c03540e07500e207800b580e5880280060394070880000d2142c1c10800c415241c0c0401c851503404d142c6841001912110020b16000d000d52440c40000c000c6109581b81020454200045440d2860034511603656451000300422020744a404500345a14040c000d019650030000003450031502c5820345a0441d0700002882c030464010362140006589400c20344030300ca0134440c140859042901e100380001c440c0961400a41d00381031800b08002d40d21100780c4032850811751b040004400700b0007010303101940100e0700310803041e50070030035044940c400001d0000307050ba00030026214007102c50540942c458286840d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 929207940 1250 929206690 929206703
    0xc04050109060e1f02010b0a061115040803190906060603051b0c1b06070501051006080a150e04020301140106050a14040e042607032d050906090315040627 68
    0xc80700980e400044d0b00c00c124280d500010402080c000005180300f101904100c0015051501d221009141040024070103143c065004c1790034205030b261580f02e448000d0140110b584000985520107425509c4071001c143c1103d000c00c51151200300040150205441c600c1c2901000c0004030461034031241251a04aa01c00040c40d88840489100c00c45040d12007100790710240c1886042c0204000b0f00445100c1e00202c2d900c2c0d044141408400b6040403006000300e05d10915008070f04c0c9030340e214114884240c40225001400a03561440004d01400790401c2e0070300300380c128000000b01c081d017107400b070b1515401036199582d2092942d058812203015605c030304510101c402d0f0110300811039200b2070121b11450407070518180c41002d031a01c10b00ea0f0008204a0001c3ca90582c624412900c090303140244200c844094404041c1c5010010450301840303400300e01c103541c0050304c1d0301c90b59230400c00b0401e10b584114070305990b4a041d08114008040069441c10300c010030150a18046c400c02105030b5480341d0008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 929209190 1250 929207940 929207959
    0x806041b03180c0b0a0206010909030c061a120c01020d0804020f01050714010c0c0210030c080411041503050a020a17030f0a05090d06060f060914040b010302040e0c04050109060e 78
    0x10300440240029080310400c0d200307494581404500030000000141c1000c40c03507556a9200500000c0c0742000c1644622103491504280000007a1311801e500602500084c0120f11040303202c05801d002c0348040a02a8408012102c2c5090b00c1c0c00881c1088003014240c0036a20041e0009906644007901250029070040006107458159800362010740145805006103a80c081c0410540d54211401200808080340c842c055103011440c001880e410740300818501404003244009000e4200900074200801240124404031210f44890744001d24220003e0712000840e80d5038100300ea1620300141080c2d01032030182e103022514410151440c9200f01c0514019071400400181d03000040d004034032440100031042003504615602c00c9001503405006010000d10585480c40c6940d02880d03c2d84000e003880302510301009074240300c160464001e03105450103e10043e048004038001d02c82c1d0b80056085241d03650034050a00c4201c0c0280c070a440302030301d401e16415242c90090b604401c00d1401240e0040407003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 929210440 1250 929209190 929209241
    0x210d0c0f0e150421020a14090c2713020f040f120f12230a0305100b09040213050315182e06050a08150a05091534080604 53
    0x144c0e80070a44002e540c039402d03503141c0c0040c00148595200e482c8400650410005510b4800c07260390704210030b082c00701e141141e4841504500c1d52190200a40040c84080c41c043c0e544481d25800411307058094115647c41808041060710f03082070103003c03803100342883c000c5103100d0f41c4e41c0448040d40d000700c00b0701e0803405681e45416010718540c1e031a008024000030200c008803070044803c0446a030300b0805585420b1071810041c104e50004103c00111b1000405c104802d0380d007441101c0600c04203031805a0f81c0e4100310050050b40e40154003454251064800c0781c2d07000407022a01601070708041103c2003030858054071440d5505294407924540101030101204080c4e96103102103144204c1d01c6000c906070381d8403c001140090150700807080760b0885840e100c145414254207507841684c40c2810002c0b400c1c12812555204045150300e90020052008a003034285458090481d0300403541c0a425000000e03104c24142150004024000c00c1502e00410303080d10b403602071020340e1341000910003441d40c01d2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 929211690 1250 929210440 929210459
    0x204061706010b0f37050306030c09240402120106200c0a050904150f020c190c03060203070207080f010218030615090a180506040b0c0408210d0c0f0e1504 68
    0x4038034030b146807619071741c01c10b41031070401064000e00360785843e0651030b4a4040c041c5810980c040034002e108103040c2040108141426503010010010a12000040d50380c1c1d00120340240b1400e160b0b10b103146032002c000a031f8580d102a040300006030060380606000d14a01c552507540000705c42c0c1a52002c00300300c041c00103040c5192420390017801003030684503c50814034243d0445010f08080a00181c000910701040d060030810150081e41c10742c54031403403070190707100c425103094503000050030b0b541c0000104036030394400c000d2000600301c0102521210205400d0440c004c1d44440412200b41000701d00e100c031145008500e144c46a4508076400580781d04983c104803015100805008026036034001c00c0605040003040d1509440c4a50020080350516042c103043c1040300070412045240100401d210718500807403489402e10043d41450040d0040b00201c00301c030700030751030340d050424600107986c01640c3d400407400c0842e25940d159240c00d81300a506110a400d82d400103116241c00800c400c01a0901 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 929212940 1250 929211690 929211727
    0x180b0901080403090b0c06010e10060e06070f0b070203040f0902031315230f010503060105030a1412070f0606080f03120408130806040605060103051302010305060d0204061706010b0f 80
    0x329103400318a04c1e0f207849403800d9980199001103155405080144186501c500311030390402c60340007003925a04c0c43e220005018003010780007207006001c00310b400e20400c030341440e10300000c2d43c1c45a0501854500040020f50300d030064411a10501c038070040004001d02203108403070180105141c0e20424100030740f90207a2032032078615401d45841da0762000811000007030115a40324aa042419680c40c201042c00b8585400107030006403082d0023180c0100220b5500240110384103902002130f20024000030300450810405d642948d41414000507048200304044040603105440760030704000c025111b5010503981c1e01c0702c00120702c0c02e074020820070505440c1150a1680b10f441801618648945400014040031041e40442e69640c0842c09210030006940075540d8090b4080c80c00300a03500d0620400c0e699440d580e41c010f8180b503503690114041e0745900c000c000c3c4181d006481070090130ba8a20384103a40b1143c100580305a400303000e002090031804da40c01c5407061155084014140041400f45123090344 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 929214190 1250 929212940 929212943
    0x4060c0816060203150f0a08210f0a0302070218042604090e07170a0c05062104030206070215131b1703040f050d0210050a11190201180b09010804 64
    0x3118003030a0700014009000a602c107011501150741212443c0c4140803d044107049254405c0041003024001c43d0b90002da02100071002440514091420701d02145031803003400b9400401110004043d44a41e40540083c410f4500c20b403102d64400005401540d0040c0c0151001058016900c0491171040004810100b040385401e01c4903141954a1040354100c54403c0704034031181e0402e40c001c01c03442c0d85841c0384210048076003001e031030517440d42d41d5500520041d40c041c1034030444010806401e080000410451240080c00852034181402d003400ba50f40d4200322500401403081048800244a1020340b490044420448083c800069544d6804410351083d00e004031440c800d040000b900c2460101c02c5203204100b07805560384074180049100040400d4005902503801112500300686820110f14608115807030620344540890701c0880e038201600c5c080034540d02c04e6a40c50810004031082c000c1006200340c0700c0b0f00c100e10b002400401e41d10102c4c4100085414240540341c1d07654092000740364400d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 929215440 1250 929214190 929214217
    0x20901051c06240326130909080c010f05010e0c041202040c021207030c060f0605060d0b030c04020705010203090613080d0b03160b0a02010e070506040909020a0914150604060c08 78
    0x10070008408401499900a881440b17840403440000d01d28005403250851018100901d803078030301081c000003250248078040e4515920b403c0c1101b800703040700a848110f01500000d10840b0b550416040c0548400c0c080c00e00081d14140118000f03180c00407c580480d0f42c50514407040d02c9182e0200700c02804140c1d241004d5000d1340250340d42c07401601c00100103080c8603840c1e812400c94203007462821580540300060301c0740d241503030a0003aa42d96030191110300e00f03142030100c0c92010190100c0e06244112440c1340c0c001c0d0020406a0400030103401452085030150704a504a503200078a00c408003480290103880c074042007028440e2091150051042d04074054200c450700d444640350b0303500320000741c0c3c04094800808580e40c5480c507030a0141e001038124400080c02e00a040c403000440c0c0c0e2040c0d109045038541e0700d420110441d144c4a19802c02046448400c02c18241020b00d030041d2000101d50203200c2240b11505485245422002e40e0107841c01c60380c031103114032020b076211040c680c001d0380340c500603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 929216690 1250 929215440 929215481
    0x60702250b042c2211040204080102070201120225030e18042009010618080f030a170112060b01030b1f0f020f120f120a050103020901051c06 62
    0x40c0d04100000704018840034060242559404188040c40650a500d583d02c18280609011303002100d5070806180d032084d1030508051030390610305030704061024040c254201c2e00120340050254010340c003410701c0c28001c3c0c030342070034916510103510100d12a0769a0081d6102180b00302503041200200000100e40c840e0500380300c42e21b050f100089800401d000519107140000782000100202031030070341c880345840d20307540303491088000c0098222441401601d04201140103003000c402c2d0b102e26a4801001141c00b62007903000c00100b40d0303407a9070000084101084414000035010983e00801c18100c2d10b10a0303c818a071043e65580002600c0c10391407940c1050780320070b480c6480356100625200054100c9540300365581035450003400c0c81d608019100c00755088440c4001d1003850100f104440c0398044d407900380d0344190190782d800450003080008120340248078100032500e4110f07800213041c1e90080303c880c2d409a80e103000f080101c4001d00b500c1070601d040042e510380000c84039003204881204451034001d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 929217940 1250 929216690 929216699
    0x21303080304150b060703020c060919170c010807091e09020c2a010903020d141204050405011a09090a0b1503040b07020102070c12080f0408030306030f06070225 71
    0x119800a94090f500d01c5001007210070070361500c0c071421500c00000d880c0c0c0da0078140c05480103503c80c2c1d005a2428000c002c00030b0ba000141d41c1d481000c0d0b45001a00c0881e08829840c0d80d07000c80819035a40340c00400d8810280000714540c01011a41d01c1100140c1e0b07003104060a2104041070b20241c1c1410301c81d00003251801081d1001c09001510755807102e400101110a9000508032102c001011403c0103c04803010343c442c144d9102c01c10b401900e4054072040074020b45031400ba058030a203503102d1401806141005504089260014400c075003040340c003403016907200d41d100424110030700002880c20b042044a582c850520810b043d42c000c0c040c41000a02c1418003000c0354a45012900811300b48000000304010040900d603c540c000041e44002c50802480d0b030f031100030a06036406007045a100a10000c01000904e002715907941c0ca002d410a9155540d170400c240d5a60802c0c0c407400c0c130034001c00800580c428400266184107201079401041d000a094034072052040c05403c400710f4126a6000105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 929219190 1250 929217940 929217953
    0x30c03210a1b0303201c150815040c050f01050a111c0504051806030a080c010e151e0408250206040e061c1227060e03010f0203010509010306021303 65
    0x19080b038042d031404184003030f0ba02c288080520198051840280f07060080364180a0159000c404032000d0320400a000c20007450b01c0400440340340c0c00b4000d02c1c03190072440910300c00700512280c0660b1040d1700d00400e081c2c80c6c20400c0005040b04154500242050005c041000d105101d102030014403201603a0080003209a2042c050003030701080c502064001404210f981008071030900c2d90899000f00000c0382c00c040c40040e403104289440908680b80c0466101a0110290303c0042e081c0c00440031a035031400e03040c3c0c01f5954242e0444400e2410003c511641840f140d4002c0720301c1c0300e0359003d9001868424040411000080e08061002940c3c9420781068016260000100003500140400c1d0304c0394035006080080d00171042a4803095442c10035112000548000408940e0305440d081007221090518030308540704840301304401d07601c890300303000060301c0d90001d02d50910580705500910004d10302e0f100e440c0507403000388281d5810003d410010804500950302401d2940144420410038594986581 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 929220440 1250 929219190 929219237
    0xf0307061d01050304080f0705250303030b0414040b1515091014180105221437031a0a0b0a05180c0c030c010b030c03210a 54
    0x180118a120703462610340801d0305503440c044402407038501e1a41c038040d03603100540c1c000e40264103540ca0000c51140204541031140d044902c00481c03611040380c560030000c006180d0075100c107402003403030305940e00240d0425020341e2080740129483c042c1680c40e6a40c51502800c4000c00710700503600b40403c80307090342e500e40030581e50741c4804003c3c40740c0751941c603410010f00d03148a00e00c0e10b09000b50f20810070f1460400405450624001d8503514104203120741c010b0711140f04101c9800c0780346c030499101c1075800c02c54046d81d200380d41c00d2820341d5400c58201c109104110014000040d0306029103400702c010805648541c03400f4034aa040e2510300f0030b54a550745183c3c4080e09800c200c505154004110420384207100d0821002e20490707900ea410b0f40351401040c15a995001c14440241070341d00011500d0503000211030000701c0600840744e40301c680f010068002c2050007030300c40c8240100c11580e00c092070009000e2a607034416600c840c610308001c2e00050300c00c4d40300805100c07d010500d00b07014100c00743d10204 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 929221690 1250 929220440 929220449
    0x22050c130209100203120a0f09080c010c090915050405060d0f0515090a080904050402030f10090b130b070f0c02031608060703060812070203070b030103110306070903030c0209060f0307 81
    0x5a02c58104500f00204903014480b040c0865000780414041500d25040003078205610b15000110303a0150300c2210058400c031040034080c0700c400203440d200400d0562106064620640d6003400b0140c541000c2d1040d10540c800380a1b00c1000b4400c24070242c5420350206400c640010b0403034094686030b036111411164440c0055074281c12034400c46a50b40070200b60994882d641a01500e0072045ca65030702c0c019802048600d070b011700e686000141c01c6480130410103500d903140200300c401404940000401600045004440301054203001c070f10589000d1000c203843d1a44100d4002940ea01d51720121141c3d880000341e84100a00d010510000d41c8003840243c43c0d01d811001080852810684007500e00800508a00101071801108102c0c4481c041403162103403145a4885958502c1c500001e0318114203500409051f035030000c0000704100141c400383e441141c0a0b0251691607079200c8050f00c200449100160104041018071001460303c80000e07580048020301100f44080c0c3c00d0042840d0018030b400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 929222940 1250 929221690 929221729
    0x30b0a150902030708130201020a020d0b0714120402010c030504030f12030b0d0c030221070807141801050105030c07051e060603070501171008160609050922050c 71
    0x862500c6800384418610241180003020741c034504050000500e0044010320949840c0700003495001160300c24031a1014254000304410303041e0451f0305040501e0641540d8240106285145403049085100d09a0341604a554040c040c42d50340c0e80c00540f4124441c410480c20800104401b000040c00c110003c041e4074040c0d002100609143c02000c3c08031340c08a084280301f4001203404a00085a6400440580e6419180c6c1d149284610861070f000c0d035442c040a0015024446000c1501c48001601038200d03004031011710300d01441041409044042e803503a6441850404005000e00e5000304010340e0021142880145003001c252212030400d05d0350602040c908200c1e00c113035001402c0c100f0145030800c41c101c003e4040c0724038060000e0400245110b41c004a6054440003900344c0b09042d00800042c03039a03000b60303001030421740c10f0640742c4c0c00180208004a980708401182c5401c22a004030722a09240618840c003035030100c2c400d601ca14905504540302c0c032401c0e60340300d0151103004c0f074140305244218 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 929224190 1250 929222940 929222951
    0x17060f1807090b010e0616060b060f18100918151d07080603010507051c0b09100e091207230709091a0601020303060108220308162f07030b0a 62
    0x14001801ea812100a01b40308803c00e008003903946994a280c8060113900c003030006042c501000206526019500c180700d9503843c0131809901034450301c9400f001d024400c54070800765450030311090714081020700810120208030545c00b01b03c0109076111402c40c0c8032500c0d440d4900350f66020103042c074502001c50340002541c40018008442d400c0308000750041401c070002e004030b140026008000b030040240c01d5044a44045140c103a84401d030f40400c08425010300403034864607003000103074804900da11902c440507020100051004c480030480d00007500044101901c1c100e21503c0702d607601c2d00b01480c0d050b1340040410341030312800b108100d400024190504003203142e140a06254104003400403071003494001d10000c21805a0303000c03040340d5000000b4240000103833a8522055021444030840903c81010801c0500034140c0146403248a0b4115202c41c40d0781c07040d0b84c007040f205000d07001403090080b44045800115102ca034102126103911900c21a00516541d4030f8541010700c00b90740403911141d441c07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 929225440 1250 929224190 929224211
    0xc03020c01050a1109210105040503071707021e041b020d020d0c0b28020a020c100c020a2303010204090204050301060608010303050313020d0803040303140117060f180709 75
    0x20700515a1180280408001d2402c213010751003114818000c00780e116107071070714181d04d1a0966100c0c15084940e00e500800c4641740a10745242c1d0b0760700c4210182c1d00c04d01c107031503110f191140681c1121222a4050644040c0d400b000c00d0341c260120002424561003a1100e0032000c0a010400007094000da0700d5009202e070090b000c9019017848081d41c000c00c02c00250b402000c0c0481c06408039540c2260410085018107503c5031001c080002c03040701c40720301c1540000361202d4815400a11a54641011143d811224024040c01c0e201d1008401e002500702e210381d03008020341000b038160b000308074404003c061541c4641500280c00ca9005400400c2c55a41c04a4188840d04092040c000600301504041c0e00950660310058003500004000400c140341c4107001d03404548807040c2000f00740c0ea200020b66180d080501d8007a0180c80340303800b020501c1050ba0000108903084111038010b82c03010901030301070707600d5122403c07040341001024565038441c051020141c60400b00b080c40c00800480c4c00014400c0c015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 929226690 1250 929225440 929225443
    0x9030201090b13110d02120601061809060e0f040203010b030d081b031902090102011401090f0c0e1503061f02070303080f060a230a0815010b12041b0305010c03020c 72
    0x640003c50604401c1c2c036807000264159940d100f6010f08442c40540c4a00d64400503103845680c0e4068880c4d4025200006003c503040010444100306050903258100d48a503039100031950302d403150790b400500d81c80101e00c020310304001c800c0c1c01c540080c001092000d943c2e0046807a018501c600340d40000c08030005c01c012848001c0b034801004042102c018a1800c00c403180010400c05000783c3c56a0355400900076115a00035403104e0711421780360b4603425080d0b0303480b0048402805031409198400d0b0a00b11640b214610407402c00811352401030808110014200c2c9030f45081d000104002c2c0c1214090101d40c240320360301c110240b60055039030700901d503180c15450000d10903d0090050050700c03240c0340c18000186d0b110142d51040d1200111129040600b00342c80012202400717000d06c3d000510640007258810000c0b540c1440e800c20895440881d907030b20440d003c028802d40d1210803035421404003050004402c0b50f0b0030104094009180746070b1a03142c4d15200e007155044034460010a900190540b03a4400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 929227940 1250 929226690 929226713
    0x609021803100e12031f09091406010803031f0504020318070807030305040e091005160221030606090a0806091612020d030e1207091a1f0c02010309060903020109 71
    0xb40b8140603100701c20016550300c215662001224407400b00000303000c204920884104103490700031507000d060392002084000c1c9401c1905984298820500045400b00003030b01c0c1e41250a0500114610364640c0c030f0410000340c2d42d403500110400c0a500000e00c40d0781d0b0380081c5000e211400381d03071381039400d14010b040c5c60202c00e0b1b8011212600821000c01c042a0800d0070f58048407000060403070300360b8030510a50f0601c450003517410141c5141c103003030040008041500d0310303001c4042d408442044c10541442c141c60401e18840d00319000c1c0410000c1e429060510113406480c0001e41b1010115413100700f80d0f418a00c0464400585a012030608450207a514981200a20300000100002140c9401052103044150800340034040b8805c803c503a25142c0300e1020f034401d002c403c191415035407600f4400b4041c00710241c003548aa40c0c6c480900183c1c1c50102c0c801c90744120005011541165401025214990080010390500d43d82e6901480816210300078404c2082c03180c0c2c00040c406e5407600e412411001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 929229190 1250 929227940 929227963
    0x41107080c0d1e0e040203060a030609121103040b09101701030803190e0a03270801060305010605010906020a030305070212030103080310090b0a0302041a0d0503191407060f0609021803 81
    0x840726041d0403c2d1900003600c0c410f040c506482c007580d20380d154804201844030590000b8500d82c541910f9600380003080c03c40908844080d558a0249903406040c10b0b60780c010740c02001b000c0c02c410000da1b40c0e9807410f0b8520549141ca80d040c4801e140080b842410040302c426401540c11201c00010401c05505052801e445a2600202008200360700700c1c006558010614000b02445000c3e00200b03010f014101040003000c03501400380a41c0d9880c0c0407054041e00701480100c880c0e40c01c003c0d010800390f006582d14025280705500504a031002a1000c170007504014140c002980203803110302d200601d07078400460186000d02421562800c0942c8480c1c1001400d51002824030315001d82d059031355441140c1c11045940403680400d0100e814454180700d07100c02c481c11356000410003120410001c2c0403001d050603085001b90702541041010b0309480611f032010b400b03504588104405d4001800603071020b030f43c1281e0841c00044958803650140308990202d50342c080907518414240c01c051404020b010500f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 929230440 1250 929229190 929229227
    0xa0f0908030109050a0902100f170402090417040e071d030c0a170f0d11070b090a03150e010c03050105031b0604030605061305010f05090115020606041107080c0d 71
    0x210429118103580c0d01040c0030b81c2101940b24808180c1803c10780d0024005590002c050486809540e0005007604400341022000715000c94180004c03103003402c00442c4034a8001e401c4e8000c0b961156902d03583c030780c0c295504000f001c030140000700d8602c60056900f0320542d240d48444c030140e000b4144c0250303800b6080348480d1007907024000c40704142d01c615405130300f2201e1946410014450003441a42004010390417490300c1d00c1458020301c020b0303038441f0669a07210300030410b4446950f16000b80c42602d100e400e1105410401c0724204000281d55400f00f014a22810701c4005501540310303107803900752000001c5540000707031a90b0051113180b44c28031448030628141c070040c03900300000340d02051031360040d0700c000f5200643d20000503420b511b540d040c1d1401035144420030001ca42c0c4a4101200d500a107000d414010208500041140c1d03803980c00c1c82240e10307640c1d002007001d5950441004050103206d07507061601d66041c000c0200262f103c001404001c007010b40506502004100024440315019113601c0c1c0d207 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 929231690 1250 929230440 929230451
    0xd120c0b0c280c141519050f090d051303051e1015030b07050f12270c1e042d02090d0f2603041b150c051c02060a0f 51
    0x4540c125080040550307118108a030711600e8081c1450800004804145e900d4904804120152190310311804400382c600713108000f951180104440041011520035805a0007030002c400664020000303003404059503000c440203203840360340700e504181d91041004448051003c00121051040c0302c0804050517910080050511b070f0750760b0303564400c164400035260304540700c00706983d10711810840305019456020b5607950500b02c0c070421050038089a0009484d03040450740740616840380211010381d00320200070290400380008000035030b0321241d58101c2c049080314004e412902c0300c0c0104080424080d400081c10384100c4201c1c1e841903518014040038903c1040056402d640328502d99000c10742240d00601d4a44942c6064503002040d08541e800100e40c0c004902500d030550720007103100307900c00d01000c04403000710400171359962102e00071519010382900b8483c401a02c0707180058095400791088501035075864103410b51f001c2e170f55000b03000182c112008100c01d006150103182c21070810794108112 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 929232940 1250 929231690 929231767
    0x50702010501061d060c0c1009030314030c1b011d070e09030a080121060f0902010e09010f060c080f03070e0907020304080c04020a02010e010e010c0e0307050d120c0b0c 74
    0x1000c2400004c2e8821400032816505002040014103150030010700002c00003101980301510141c0b55100440000c8c440e0800c180d000035500c4240c1c2e00410491001906209110700401c0401c0e80c2501d5526103996105a48003075403966400301004c4880400280c04a5400d1820040b030300c00b401004401c1c46e9004000075903046611041240c1107405400c5072812412001a107501c2640c1c2d041009018141407402002c1011000d034040703418036100b40c171034250480c03c0000303000e0030300002d120f5107030340402070311003005001d008100030140d0030b1041062034542201101148682c1c0c1090312441c00040c0d4030040c1e420641065160203411100ba8002103092610348140940d50f50071070407a0500450b008135514150300d00035041140d41900d010001d000052440501500070281a40070600140c00b4912481941c14007117244020b07140090583d211010051302c800b20f810b079003000144100f00c005801140850740807a249400340c42c0e4000c060380c0c0ea01c81000303152070013461303c51444c002500ba07150405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 929234190 1250 929232940 929232977
    0x204090c0f0f090e06042a09020301090506120a060b010207091406120a0804120c0b190e0411040b07030e060408070602061602060f0a0e030d020d06080705010f03091b0905070201050106 81
    0x40d4041e80c0714001001d0000f01c0c481c0d400541c7c83d4542000080c8a841c480403490721010b40103181030f202152010820395481d03a00b00704030005003281d9404143c1000c1251344c0880c0c200c1d0400340107014107004440220759035140e400c0486041030328414020000000744121403504078150f46484407d036004081481a5445441040c0308a00c03594045103c80720a1400700648000400c000309814103080b500e03014525410740c0401b2403201d031940080d49034080b490081c60700303109a09407000c03a039a5403418142003480c0c441721548004002e0307003400019035024000d507490000600191240b00301801c0b1003490b1450291410078054800c03460903107400303003108040d81e000405c0740d408105900c500c031840e22040c200000500490440080c1030000286100c0c880440350014040300e0002041080030300e030b6411071203440b501d4900506000801d95940c4203046803203508041c0c082400345040f031046210b071082d2511580c0c060340c0b03c605600d49480801000316020300c5814010242d904000350540c0d403640804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 929235440 1250 929234190 929234203
    0x30b0a0c050d0509071701140c0a022d01150806010b211302030f010c0e03010e070b0d0f020d060923010b0705070f030b27190204090c0f0f090e 63
    0x304003c1d0b40c0d400191000300c0c1040900010030304080540204040030160901800b0007905040690503500045a10b805444045070f40040030341d40502150400410f60a0780c0c0c2d2004000d641e00c2d03204162003d50100e00a1142643ea8800080109440c5292030191428050147d1000701d054109114018030140c0340080c0c180803400d610030002c99681d13030600749101e65802000194062044c00320490364210158881050303d001a128864124182e508040c26200000340e4034005420100c810070020b55244050b1502103400070020542c0b204070f009083c126040244ea5a102988a42d800c21512025205400b059000300d65040440c000c907140f6030400c044103214841e46c036100001d41a06014062090300060500740c0e1842d621180e40e41002001410141d41c4c1c600d100c03a500b0401d640c3d40740040304403000b500402d0f019103600c01c207405644050807004001130b60132a80700d0031403200203401c402c003a0029201d000341d000c1d60b0311304001122081c0f00c0c82d508100e054926007a6485e00798100024070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 929236690 1250 929235440 929235457
    0x7080706050c1218010b0d051b030a0b070306060801090207030f1805031005010302030d090f1401200d030e010c0c060905030f12070e101e02070b0c0106030b0a0c05 72
    0x414070b501e9091064686106403a400400c04140206100102e00c03040c103076000810710400203010b8449010200000200000d200800c05d9204a01d01401701c500100b0740e44108200409554882106403641003e80c44102c0d449400260344032418040142c2120402c0e015103d840c50450600c41990703800740808500c09000e90a03c061a0b480aa903071004040c0300c0090040130b8241c8030f210052051501c00390400380001c9103c0e0148030b032001d6206100b00c25890444000c2040e680311145071170b003812031100141d03106604024070100d0600c1200c88c00e4409802d000c7c4182c0040040041005008048415100da8a130f0311b039041015104ea460782c09507107403255070303040300001844485600e4110710318410307030b52000c6103400c01148038007612070b0301c0c11a180f09420584412103084200c004002c80051003402d55000b150002c0007984100d09026024200140c0f070340102c81080d91a1044181650000101440107a4552702c0920800000200194004200b01d00030700507440302400c054043e00603c0ea0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 929237940 1250 929236690 929236703
    0xa08040e390f04090203010e010902190c02010203090402030f1015120f0b031606031404020d0b04150509100f140c0f040f03062906030c071b0e0106080903070807 71
    0x145803030740242404480072840006907035655160f45050000180d0001d00c11011104410310000503c002a802100c2c00400d80212140c03100d1030000c42610540390303601c000c4e81184001e0040c0101134690380300030341c0121601031850713406e8500f0b4010300d454954540c01280c546d42d00401d2031001207030480d1220b000825804008078081081e031007103034020048000415814403c294243c000c20510312150410f607071041d50107009550441280700941d0000b030b2030003034000440d1030344080401c9a01e48060f401500c10300c850301e504034110340140c0548070280d4440c4a01d80280d045a49814038a01c91908050350401c41440a04c0052841c80a6004000c0551a00081c001140220f24280108884c0945180202c02c0d001d2622428084001c0c801c600001d140301122494900c40c00c661440600381074400104218078503a10088080e540c0c0d001800708882101c80b8850b141407000c00c8144c3ca0307014148000c1c01228662429030024601917010f060041c20ba0000c120740c8011800d9182103600050300302d0b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 929239190 1250 929237940 929238031
    0x311070b031005100f050315013c021204050105031f03030504140a140607030c0813150305040c2903010b13050a1208071104020a02011d0102090108160905030a08040e 73
    0xc0050b10303c4200300c0703034418141160440c00c0407a88107400c0031130a89145c10500b011417801c03120700bd90345d844209103d00070070729060104008541c4540d008650020f1100b60101082040081c0701c0900e10f0365070401c5000c00c10204040c400c1d2044511600c110850840d4030b03083d114600030703024031720985d503003900d03070051500250420516000b500078245071540403130001e0f40c41c0c10342c6c1d440c2c840c080100e004060403260041c21752041e00384280280350040e504a40c01014a5203480c41c880c182008030083e009028100c003000313040c10002c00c0069402040c50380e05041d903c2051403020280840c0303e1f0003452150900503070a020310b111980c0503041e0b81d540424400e0703a4500c84d04140010700248041950f0003030000400d03e4103aa8190086040c0700000c1d1841c05000410744440d909038089d6040700c900180c03109000415401a1110038500450941401104c054403240030034100480303200295948500080e04009040b40704041650101c19420f05206800c2c242580541c4072404e10902c0d203800c038405 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 929240440 1250 929239190 929239231
    0x10e0d0f0210171f12050c1201110a05030f012405070f020901060c020a0806072102090402210c070b2d130b090105130311070b031005100f0503 63
    0x5180d1940a42030701003440c589440c141c80c034130384c6000b055034280b000b6a0ba0340c24006680120311013041c800715844030140013034091031030034040d03600707480c4400307401c25034842d02d0000c11030310180010170440f81039503145981e1780b80036410b924040c18103034000501c2808610303241c4001007121040d140b0f42c4200c2d190a50340c901c900d050011601ea06c500019520030608000004c405401140014140344280c4500d1081ea503280381e11501e0301c01c02c03191000841c4000d0f03660101d94031940445080a501c821006080182c840042400c80c3c120f0420000c014441e46e0070f40f074050058070b2900e035106044992152800005940d40c0c0e005101c0030780381c00d0b40e40d0781240011000303070f410240d00ca080c400ca84c001034006180c0f00f0000907100c0c111341400e8a19001311004101e00038410b00030284030f84450503014a82544035a1304039200f840854030414140503101006c507800140c88021030041d18200d060840c45401c0601b000f80006030350154000b0711018a0380d0042d1507800ca001d0b02e600401c0348180d00c00c8100300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 929241690 1250 929240440 929240447
    0x1207030c0b220b09040c03050f0c070201091a041d060a090f09060f020a0e0d2102030c0f0c0a0603020306240c01020f0712090e0c09060412030e010e0d0f0210 69
    0x40c04584206501c00c450110b0340150303c8002d0312a4880c00c41d0280001042410250101c0340291394550016115500140440050500a010305441850807a4042d9990800c030101d290320648088920701c000030f020841100700030b070403007402587d90800d0380003414000d0009000082e94840d04900d60b44400c0030140031a4140e10880070703a0341001c001d00010101d546820300039440001e600022070007501a8240c80c0c1013020007030f040a94001290b0007000d1700349403808024000f144034901144420400c460503050140218140368030100c0c001d09000a100c01001a000d90f107030810403c051050040244030343c0d0359001c400901583c3e841c0c0f5003a0100e0001d490509105030902c15040e5800020444180c01e41c4a000b40001d5014011060406008240031100ba500600c90074103480c000f540400c2c042001034006241901000700000c2c80d00740d441406520548074a0825000303d044000e8054195811024982c5144c20807142094100416940e41c0410780754240003034010050765042c001e03d50700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 929242940 1250 929241690 929241727
    0xc0301080c0103050a0f0c020706110f03030c162a150e04111908060a1203051209192307051c1b030b0a0b011b0f020a0911091207030c0b 60
    0x1c1b0700c0d001e10141c0c0b2141006942c0c0c02285c401d83e80001e00e24001002c83c03943c041280205002c00101030f40c51511031400c3e0450581000c00c802019600d1000040c00041100c10b0909a0480c4040405111801c5601502e02d084a552000081c0d1004000316561141c0c0000500d681c42c0d822a40014010028440164540617840389000c2d078902000003840c81d80d800c0b9038418800e40c0115040c00f00b164640855845030404018001c0c0410018010303401081142050260300000c0e64046030b80144411812815140d062241528105075100320803a0f02c654452801c1848074101005201840c03400c004542e18200e4910000418000e1003404000c0101c040c402030034068444108449030342e224100040b5034a015500c2d404031500c2d1490100c01b40d40150001e44209180c2c05441c80c11a0a540303808207002c091410491340290b00e9030340410f4040e441e2140050b8140404a566114400c043c10b000e440f8010b20100382859004100800000c3d1180c8042c400307070780c1d030014801c1c3c0307174207446075204005207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 929244190 1250 929242940 929242961
    0x9010303052107180504110a050f09040606030f140402150a051201080705032a0f01052a0c060f04090c092106050a2a02151006080c0301080c0103050a 66
    0x10240003031000c0681d000c410102c1ca0310304e00001d2160155200308120864441d05a04c0c810218284250f4900900032006440b110714610442454030900f100050201d480703036001030001c207550f2410251076201521580c11114030b40d2030b09603c0c0c0c2c1420307000501200840020903140c03900008044800900c40e00946002c403a42c110484810f503101d2004c2a260000c0d070003064000d1103504c60710440d2401c4a0103011803102c43e0308143c0d0226407404c0c1440030b1404188000c6051003410443c8804014076001d035464075040d03600c207040600c40c01c01c41541c200b9503e1620306114010601442d0b080c04842000c41d0111400000006005400781e4001d4070744140700e81c002c0f08115000d082010f2071106440300c6410143c418001000b40340e0741e031017400c802c8401c03114030403142c00c0c10390006804c401e8044d004004000b2440c0116400100340c0300c0d1040c41080b04030740c0e64031006041d4401f00926a0052141c80e0000e0041e82d0340da080d90f041200240d511030788164010704158968000c41c410392000c1d4080003d60 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 929245440 1250 929244190 929244247
    0x30f09150f0a0f150326090103090602160b011e03051504110a09020a08062d132a0318060911120d0212040f12060e03031003120801050901030305 64
    0x40800c00c0050070703441d5072000752080e40300700c9020000307049001b40c3d601a69507052211820000004011030084c00345000440d401c5500f044410ba030003062010365070460b48100100f4449604008200386907085034403c40f440144d0105060000480200b02ca09045000b403000d0040341d42c4a041404171001400049504912904008240440719030001c000007107880c4c46440807074640005100d103c4510240380348070b1607942074031004207014500c242c0058040040483c500c800c800e09100c01110b0840200d00c102d10300c0310702459026150b80900943d820341502341048071101c840c0031700580b0110313014010704a079500c0190074100303c420081120598809001da003955812000304c40e68401a50400002620a003600c0001180c842011141540c0c1901841020f07145070540354901507105c581c0480314a030f01c40c484001c4070b0390304101862080c3d050951480c603517455810400c06120b80c0e40c10500070804540d005105503140c007600141100d52514000d43c2c1c441c000106d02d0703040c0c1080a00a0143c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 929246690 1250 929245440 929245451
    0x3130f0302060403020c0a030206030f0406200d0608070509040b10030501020d02220312030209010509100305340806011808060106020f030414010c03090f0803030f09150f0a0f 77
    0x1031650018205201c2c038429001c0303440b0b4000035005c00c1f694900501c4000d5000b1801c0001070454025004120b0f0050f108040204e642841d425001c519405d4103049181c9e0724030b0100b2075404511040c040e40300100010009012010f00306800b1442d050002880a40200c1d240c80100e4490031a0114000055401c01c00854440400d11405c4000e58803502140004084044e2030741030038060401071004407541f055000c101d11803503240c181d0107504040350b260f050110500c1400401c0d221038541070300107401745c2e400141919014020244a00381d1945031010350030ba55003121207080076801441c040032101e00745404c0c5aa14080100d502c0041c0b03542d11a021081d0b8800003541e0100080c1c9103060f601c3c15003e4500b206946001c0c9a5a0300640c03140c4960108105201160395000e600d0101c0498040c1c60245171503511200c6001c03042d021a03100405560000080118018096800581011800e406494210380500c450049240040d142c081100410404510050440d0f400900c105110301c1c414040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 929247940 1250 929246690 929246693
    0x1805030409020714060915070201060e0a0c0f0f090b0f1c06090b06130504150509070807021b1e040b1305011a2d0d1a01030b0a120803130f 61
    0x43c0d042a44103d8001513068504400d541000c5590b610451320708008140000603000900385040010749082d096540e078030300106070b100f11480071074403407400c040c0042000602c4810040040d80740b42d003007004010700e660100d403016602c242c0d00130441e40001c1c0407070b44400d400454895a4410384146440b0080543d01005000e80242c0002d0b003141c0c0da030402081109112020300000c4d01c51078a4031960b05d0a520002c1c00b482c0b509030f001c1b101c5580c10302c0c8010000d0340c6810110729910f4050f109a0045411281004403281e41000034034010440101c03018000c5142030040f998031074035503810110780000060015002c3d107403540020f540b4030008003010445005d40410000400c8213004900e0800e04504024042c2d000b02c1e0b00300c0303000c0b0030325284010260300101c45400705c130700c21130810894031030041080949014940c002c403601c0b104200307000041004141e0026044504410700701d4002d0821190401000403100b408001080d00215800c3e036a9481000c500d04059076514000d00304040705030b0220 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 929249190 1250 929247940 929247959
    0x1215120c01081513021605060f1506040605040b0c0a0519031d03030a050c0307051b090604051014030c10170a05040506041707140303090d0306140418050304 69
    0x40321402038a03540c01c90f8403a5152410f4444010350010b40051032040f0404003044141d00400555003d01c1c1c07852081209aa18241843c03000e540002010300c60703509000e041d0090041141c2c1d0308100321841803130946042c201820310701a40c811a04584000714495142ca42d00b801035560f03241d80310302560481da00d80d042c140344040d11044e040d0005150005980d00c0c01d01030b490300b501c481c180140114141050311808a0306540300d952051101d0006002032000518104040941040f0100004500749183c009100415000070511441541400700b031100c204110490352040e50300015100d496110440042440d00c1c080e908090380191181c900380003c01c2d4002810f82c440f140c2c80000181680b07419503c0d030b040e1882030724090290f0b0050360205002580300400706d180348407000c1d203480c203190351a2107448413554418000e1955030030000c10022a0030080c40501d0030130f040317410100f00c0302c1e04244241081d00c000003030b1180104d80d140030101c0d901c0c52040c500300503964230208413943e980c2c681c407480 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 929250440 1250 929249190 929249203
    0x305030a0e011805060708070f11090901091a060a1a131a0a0e01120e06010509060a12021002030c06240909030d09080c0102071b08060606121512 64
    0x45000540070340e4642125846102203650614402d04016103040c10a004c000d525448901e0494144208008030800660450382e21500300d40a228a010601d00f14024407800c5080285840070603403400c500d4400103040b10b8480b41c2c20345042040703c80c180c0e461102080018250b82c01854001102540311281c44107814014501d000840403107080c0c41e0342d40c08024140740002d46401c800c1e14014031080e4803041c46130100d140c464105252106001000000d203804940c3c03803681c401e44941150006000c241800c411042d0840e80070b4401941c00c034500311108035503156007107009214101e80301d075000304940708209032119444c2d01d505803031107410052144e180c82402081c1407081070005204801013490481c083e02d10034450300020350b2401c80301005410050583c200d040b41d80100510440b00000002d00c0503103002885815800b9403084528450030000045503c0103503980c2c031660421446403180d805451164a6541941d20161503c3c01008190744481807480d030024520b0f41501d51040e00010117 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 929251690 1250 929250440 929250457
    0x50106050a1e0e09010f320c0a03020c0c03150411090403140309070b0307050d060e071b11101e0809070b0901020109020414010e0c180f04090507030503 67
    0x500e0105580c6103031114142c03803401c8042d154640307441e00030410f0400c440a0b05a102c00b50000021b024841c1304c0f110021104410740450140340b0500542000e4010120100340400e55010300e082d040c606450003c2891190182c00000c00d42c01080c03011414000308012034400000405484d503601080c4c0c2d42d42c580b414100c0b000d48142044091000450801c88000340c0900c3e01943c500241c40e1800b50528255403014140180510a4800003c0c400d601800514020842560f84607510710b00c45007254103582081d04030450940c06c0c0000c1c0071090382c000303680b01e0301d01e110030080900c11260360900100e07040142c0c120725046000307601405203d6030701076900f80f004c4002c2c2c0c022401d0302c00250400c03a41450308417841d001310740c40108103010894001000e0100c03c1014400030401c0308499011406035075049260081c0c0c903901800600c18100e00440300f0341d0281c0a15800790610303600404440c038056a06280e54065000841203012640b6280c00c00a4826000011605c09558070b180c03861386c039840100d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 929252940 1250 929251690 929251699
    0x2a0f130c0203090a09051e070801030b1f140a0b090d170403060203070903140105072a05010e0a02010915020307020105030a020c1c09080f0a023a0302150105010804060e030d0905010605 81
    0x1041c0347c056000d4462a01070002c55a4580040c0c3c05d41c0c1d9901c04205000c0d0078000c0e01004842079510003c6445a1700b409804c49a05155170044540240003d600c01d5810000c48428113001d154040d80701d001200b003036071f40c02c842d007945100301400d0005001e10030340e04003404540c000070030400e0142d0005003581c202e0348980e4100c86840c0a81404600b00d1f44141c03409000134a00c4a0380340c1907003401e61005d03494200380403160907001d1489c3d600c0702d086501c084610005030b00030181c1d12080d503800401ca8001050380d0324801d4000e4910120081d280d01c01e540c8024103000c00403000c41d1008d185a07050720128900b1000721118202140f58640c1050004500f1000242c0b0041000c20781d59004140301c8940280340d0014034989540350300b00083d88500441d44150f8190302910086000101d0300042142e102c840203000701e004003800d0007030030100481c0400d0b00c245d01803401000f01d80d0f404080705034096080840040d00f00d4001400c9411480b4004c0d4020805c0d04102d04c00d4240801903003d001211001c45 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 929254190 1250 929252940 929252971
    0x5060307140f091506070f0209060a06050d0203090a02090f240303073c0b0108120414040e0607031e0b030d1107082a0f130c0203090a0905 61
    0x3040c00400c8a805110340c1025000b511512141803003080c03036800c10420031589843d01e28010200b03840350060401680d922180c002d086041d824043c1c00701341c004205a440d2080b1504141c0c02a00741c0c820082c04030911940003002030800d10090001c018074542c014030342141805c004c0c07550440550192030000c401c0340102d480018010b000703082c040c480720015005e5401c204007030320b43d42d80841480c03484c2c420350800c0c005050700d01442500070103180985060320902000050030224800d9070705801103621503000d80080088640c0007002c0c0c2d81280c50b00003510100a5403100482c016101d40207407002248142401d02c100d16405801600b0a5042d490301c40480d0f0f01140c030040c080d15200c0f003001d80c26030083e1040c0c440707043c81001d400400d400200f0407180042e6541e0410b42c030f0b00011070b9580d0904060703c540c500d2030140c01105000d4040e011100b0480f0389a2a0001502e0500c0542c0702c86c400176581c030885920b06009105072030450600803c0040c2c42a950a200b070082d103012a404681018040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 929255440 1250 929254190 929254199
    0x6050f010e150a1a120702011b03050105090c0703050c0f011d030306150304050a0b07030b040b10020601051201180c1409070915050f1606180203062e030605060307 72
    0x450030502140001059602031500d0305000c200c9241c2030020b5401680400c05c040030303040c0d1070a019203000f80001d50001503010310009861207000350106140c1d08043c1800c0040016039038850010b0b81108415120755074440d01031409071114822800c042c503040c01170300040c030130041d010360150889100b8805440703a20a010818113803640b00840c0c1540d840703844107e40e900d0720345016004d50f42c07140c42402203520380d1050b134540800d0303050100c2c0e2110000340c45801540031400d003806184d01c4680300352508850841c4122001c3d480d1b040c1401154000c00b94428581c040b000c003508000c02003418024400e152203c5d13403c0481218401d80210103015400c04085001428601403142c8074000035a244410360b400e05146003100711101d031034102041310074044100402510401011070020000c400a16683c441c0340c002c1c15116844040b028107110380000d040981c901041c0668461b07941c0f4905a076081101c054140c25008030f50001003003942800e804405c0001aa100c0b6010380d41c100c3c219400241d0310b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 929256690 1250 929255440 929255461
    0x71202151008100e010e0a06020d060e01050609010f031d06060907050906070f030c4e0818120c010b0411090103021c0e070f1509030f080706050f010e 66
    0x851050001950112910f294107020660110685151440010510020103003060345041c03c0e451040e43c203d40d001070b41c80000d08642c460f080080c6543c944e050410340c0341034009055802440710580c10321000d10b03a117212040c071030f40c0001002d4003180e1080d011841c401007050b075208421580a802030500c0070204a01d140a8020380d010703464024031441c40e218565841e500e40360f4441900b00c0078080c4099601c3c000071440804c5a4420350b8000102441d2800e0071300484080c010101041d00103403804840d00702d10300039800209130800c5542400c02d00b039228580e0b80d043d80c0f00703142c0816295000d80000c000328840c22000801d90703000c0140003840a0400c100410084444000c020404030004005d2105c455000c1d4000e00032114a081d00d54000c2c05214462178150703600001c004800342c02446082c0100740c0e4104425014020f2064051814050960040c105d480d00e0b0101510221110302040e080050f140700b103a000300d0340540280502d00b084200c5640020f820300488260110510028100804 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 929257940 1250 929256690 929256721
    0x3040b180f0d0807080f191716030b03100606170106080f0615091002030a02010c05040b0417120706020a0305090d02150a020d060305160501080415020d0207120215 72
    0xc0c01040d050b003a4200b9528810301d603000d00401c0301e0009080c401e4007205403201015003101c0100411020712988510401810180f2086101c442c54050b18280480071000d0602504026400d00380000c100c0d031340400181c40c21145c0e520505450b4108100890126844901148810645d0015454598803004103903020403044a40f9000403080c400090024a010001c103407480102280d401d02c0c1c424000046400d0800b801a01d1001d64070015401501541c24484c00521010b10702d0490b08082c2066030b060150711492056186040c400443c408a4200c180001d02c42064141703a2996903411501e03080000e5009142c0040110b840c11000441c11270021804e00050402c03a8090843c981b02085407410741c04002d0209600c40368240300e091000c0d15540301390000b45000360700421a2040a080c81c0c44001c146030040380c1017010050a100000d40301c4840145100d103205000358071248403420040c0203000b00300010f0401c4000030a6010025000301c2c00b005e0350303000010b007002c0c1c1d503035024140141d140703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 929259190 1250 929257940 929257969
    0x60509090a15021b0f1e0d200114070e19050d030f140a0302070507060e060d020c03161203050603190605190606050307080105010e10080601030b0303040b18 69
    0x20394000c806a020000740e8001c0451340c05081d90800302060041c405850072100009180d00d0754008850f1118007058501540000b5820100820032100d00d084018000c0041102001708980e03d203c1980c04600c007074008003113010980c0d001600741d291410f001841c1915122900e40940c588802800034000c22024404c150f03034016213141d44840007075804440341c3c46001210010440c240490840c154044002400d040009036000742c2c40d03000034102281810030700d5114030140904400025000c4d114201a2000c1e01c910b95401621a2440b13040b0030708511500b0f1840903000301100c1c0600811111081002c2803039010b603810051582e40009155440c40340c0100400c8004100e0b003141c00003101a04100c0d8010321501c4e1001610745100d803840c003541c0f0150031120104001100b0410000d13400140070f07005040910700103000c1d240c03850101d082c03500d0300d500c0c2d101003060200c0000c00c181d00039044002d1140d03000c0d0881e075495540303424202158006203071050b010106400d0036066858094503011404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 929260440 1250 929259190 929259203
    0x70615031a15130e01020a02030d0f1802090406110f040806100f1e0305010e0607021501030308041203091403131e0e2706060a0b210c0903010f060509090a 68
    0x80764070420000e0604540034040142a2940c2e000c0c41d00c04c40030300181403141c810744c00a6440d02540b4080c081a10228501401d0b154500244d40c0108955030407003100d5560103980c03280ca00c1d1903600b0128040d20880c2c5145030031400006580180b03000b075800900c1280c1d489000d0b41c0150319400000709100c4200e128040c9100480141807003401120005642c00c001c0d40c8241071240381c1d81e03075a1142501c00d00880003078290080e004020009405002140c1c03415600c1715441304560442d6006400707003c0c0508003401c00d540c140000041d00d03009611140303007550407628a000a003810040d46a89502115072180c4503090000001100e50032089070a0042510418180c14542420b010101c03400d801050500c0b0301c000f48004001028230411044003140b09079014040924060b0240800d40d04241d100442c110340812944011206082d4171002414401070343c0d40e002d4469001d111410b0082801c2d45074907500c1d00c5c15505400c8401c6d4814030813140b045d28641c0303403035a0b443c451944441c810203000c1c114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 929261690 1250 929260440 929260471
    0xb09030705100905041a031516050304032d1101060321050715020702040b01050a050d0b1f030b1906120921020604020909010c0221070615031a 63
    0x2589006501ca041000c8549807003d0250350704c0d00043d003a6010020007041030340a03a0002003481c1014000c11802002108075040c503070511000c10034124401000305030401c04040b021404240c81142c4890500c0504005030784203401e040c850903004e221010055000c10f5540c020111980818010403044070340104150340c001405080c4005151003e0b201e07001001001c01400000400c0c80c603070403c80840358100141c031484a84144000c03250780c0c4c00c08505100003030000d00c407903642c0501211014101c502001c40c0490514001c10032044030004400012120300e0b40800040d03a055100c0d4030710342412119010f907808000360142d2280a24056000004e00c0c116441403410080e0700022102403284441404290500501d216050060301840c1c0040c1c10080501003503241012855420000c808000c200f29421400040d60f680c00c100347d246401c2c14490030104114000c2015904030030780021040c0034002810728280188152800211032103050204807210700c1c8848a90f00b4491200c0d0510f0000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 929262940 1250 929261690 929261699
    0x40e0a0e070b121e0c181507121101020a03200307050a0f050d1401080105070833060d1527020c01090f06051014031002030402060c1b0a0b090307 64
    0x807094001040c0400101e03a262007090860b543d8013403107104071818949103880702025a020490300b030000708414811411814001c402c21403040880f00c0c8a984901003e0a00c00c0b0700c401075603032107001d580d08181548040b641384030030340e00b680101198541c1c28260881c00380c0c000102c2c0000d8001035420741b00040080c001d03c004180560b15416107525a803c210b0700b0403400201c094248c034a581c41c0c1c030781400500307801000348080074020b242c1c00c1051410010641d1401d24403030390302c00d0040b203d5070786000c075500b582c1004144c1c0d90180d1041c0b4403001c2c111940e02d08041030f0325005800554100a0030b203000d040c002071104800450009a04010480700b00d2140c410070280c1302a4001d400c5100c0a9580c601c1d880002038080d20f44546d6140c4120b5001c9401c4c6032000303071120740805580c0100150441698130321015a004141c0003401940c0c0f100040e1a44c070380303002003641030040d1490700b8094880c00309040070180c0c248510302d4280008032101e19109854001491681c01100c0d00c05401d40c0c8144010321 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 929264190 1250 929262940 929262967
    0x1209050a080f1e072111030123130b09010203040b0106080f130314030711011d030906031f0603090b060607110906040f2a0203070201080f0a02040b040e0a0e070b 71
    0x42c803e850721021688025100c0102c0403010f109070091609500f00b4039640f40c1000003000c442220740a084000b0070414210207007099030b450100c40003140703550703508000030007000580150a045507045181d00d403091904403640da00030341c000e8a0664020418800000e41248030b65101d911440c1803540e1f0409541b544c2c0015025074031488401c605001c0380c00c0d18046000c503040060b610420840d0f8407004010b8001854a0071541500b54660403041c8403100f42041d80310010841305948400da480d11390320398070940612900c40010004103000c10480c480000c286626800440303d150240c05100c0b040d84800b02081454071901c1c0c030040c50a40203031021a0980351002440c1d52104c00903002162034203943c00321b0340031a80010760352181c9011108239a0400d4a5144c400b000b10580e600041d460002240c00103051910000c00714030544c02c01c100001d203680701d00d0701518002e002040d501500c0340d07150b40c034000c1150800c51720601c481e4645840814426000070790301044803a4020414542058161080e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 929265440 1250 929264190 929264233
    0x203060f0c1909030b0a0b2b1b0803210c120601050a02010b0424091a10020a0204020f0414041406010509030c090709060816051602030a1209050a080f 66
    0x24482e140c2c3e40080402c3c00c44040c144100d0b00c0c800300141b40103609081101c480c1045c20340502c1c0041290082c0002865266010003040d0004001200d140b44060712001e2007519401c00142c5000c00b01c1c1d402024208004a0100d144282001901a0303035441c01104450003940080343d65400b00801041d8294000e100504004901d07200105194226801040a440030b010802c140012a990007030030b640e00b00c4940c43c0c05400c2c400028080c0c007104986540a01c04c001c0c0d607241c4520018899000100d00800c458100d05501034000d548449001450000700e40191017400da00700c58480c101c05440c6054032501d58540b8a403528400c07162940001129282c0003849065090b22411441d207c05039a282d550501c10303441039032942c2c1c841c0e040c07410007402c16401a0007184e40c040c140700c039045010703040307001e13590b0155080201c0346040342140006860864480340c05415116003a56440d2065403024624095502c2540c0781f5018641d503400080c0e5480710702c12a250b40da0002e442001c1e008468071200c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 929266690 1250 929265440 929265487
    0x9230409021201020304030207080610121e120215040218071101060b0d050a0b01080103060b0105130b0c0111030405190201030f1a01271703070206040605090a0e06010c030315170106030203060f0c 86
    0x60070320580c007000c5103c0ee0030050241c1039400c40034820640400302d0b0304008402c041c540710045144241055800b1880625401d500305803c0c0c2d0700000018102d610420724060358a40380e80003030060b1903a4001e11210f9900c01003a040d05e090a000c0060b85004150041e00302d03041c0180d5840d80e04e6071860311800001c00034010060f04103d020040c80c00302500d0041c0d0b800141101d00703802903486821041c41409c40380c000304e00e407441e1541030081101244000c6200800c2d911302c40c007548004101840102c0007803140c4000784582520340360002c1e59400c280001c82d05c0c0d04100303072600c81c105949481ca030304c0c08403420b105400511101c1c0c841407000c101e000300d6828034201d45408a0b41850b140c0c1e400038007141c11540103100080c40114446c241d6180101d0740900415000c3c01d2000507090842c00201002c4515002500b855100e000080030551040d086000800c0c4100c114611070190300c00e41ca0203001c00b0f21003a842480f8034004220f0001c0098030340d50080c81002441e40c904241c000074807242d02c036107005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 929267940 1250 929266690 929266703
    0x7080d050c19050c10060e0403050309190b0702070611030a260c031b04050d0308070c02040606090501030f020f0316020f030304150c0923040902120102030403020708061012 76
    0x82d400ba6a60150300c440a44400380c0c40e400e4981001110141ca0b0140080141c0945818010200102c0c0080d04001e80c00a4152806035540c0ea0381000c02e03440c1c800000110045005244206014024203e0305c0500506645c1e0a80d41c0440e51100201d82e0f00c52050b000300d207240c1042204d44000ea028103030202d40000c5000048070108440c0e40b0b081d00b24001240d031500d00041c000100300c091081c8020240b804004030782c28604240c03c190204a40301000d0304010180070110000c541242d001d12a68040580d0040061222680354a00188038902d00d114035804207003408040e0387c9140711802580e40c1000110141400e582d140c003854000903442d000340406500512240a582003401d01c0110710072030103800c3c0c0d006041a107801840450749604c215400300a806441884a0b4804442420402e03606030965104050b6023000a0020308503850000e50103c40e414a2030b500480640145229074025025202110740d03440c2d51503101c141c100d5540d20356640f40708041c007501007241180c2d8011400b42d00b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 929269190 1250 929267940 929267947
    0x7030c0908101d0a050c01140c01061401030b01020303011a0f12070915020f0a080f0d06080c012304030201080a11161707080d022d0a030c0507080d050c 67
    0x82141d800c2800a07440c9181080c0c07504009481c2451000c064810041d00600a04000580f03441e056140d20200e4074150401207044445500d0387c00100075186503140f01030081056540d0307800c0c1165604d501d094000d01003814580b140030380d5800441928101d4407901d0310540c92000941c0001e0003070344160600d0920050901c5550102d07200c00c1103c0b0b120750925205c0141290070588086902c0e002c0d10829000c540c442c2c1010030804d5030106013442a07a620551254540c800003401107041d00606420755000c600d04480081d81203000215001d0400003a29540891424031a0500c0c1c0d551580c01e10340503403102044200010f521441c8800d0380300b6a41840004d204a4220140310740e54001c01c081207042001e0942d00c402c0c00751071520080e90b00130300155940b801e4200d95407900140a920000c803015940450380b25200012402c01c542d00711800b00d010417050301c2404101a0702e8100c0500600000c1c44c140c03401940074018421601116008162903090460b4114030703c0140c40b0003000c421000e40d0a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 929270440 1250 929269190 929269199
    0x50d150504170c0705010219031e02030904020f03010509010504020403031b060212041a010b03070210020c0c091801150608130201200f15060f01080a090c35030307030c09 75
    0x402c007030100d41075220064208180b03468002441c142c80800209002043d11154900190700544664810051321041c1c240017851748000740e0a40c000e0000300c5400c6800000d26050304012600154103842046032002500c5e40c0b45c5091104a000714000200410303601651a100e445c91139500e4018030348101c03809840c02d801e44000d0710007000c00380c4003203600c0300351141c1580e6040c44404c40079014010b400c100500f18502880020b503100c115249203a806503000504003000070051120b5420f401000c0c0c07040000e82028680d045681804540b030348a15464000700407103003a031070091030084640b00e036620102625180003202110415060482c180404803604244170010001c858900ca680701e0003808150300156006414820301e207441607a42c00412041102035951a0700f05840400c0a2801e42e04540c0d944500d8401803039111400350880ba841280082c0601c000b4030810907010425200811041480a824022040350009010282c100380005a2010700c03aa10520001650785003a9803d90703500c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 929271690 1250 929270440 929270483
    0x1051303060f050621120c160602070302150c280605070f020f16032603040807110603060906040f0f0203250f02030403081e160507050d150504 63
    0x1110789400060341c441c400c126030b514181030105040c41d001e005c080c14440760a04a180c46079a40c9a0110b000e04010030380f0158102c1c100903900c0c44090562103100380e01e448000c00b96842c01e40b80300c1248983c52103c1c91401ca01c0e051801c2d00c4a41c1c805070002d0001d2403501050720220700788110002024080144c6680101d4002e0203464061215901d4480a0208a800c02401e00b20700100140320350740000300f200380e11300e10040808100ca811001c7d210101c8001c0d030708480f040362002e8103407110780c80120034041400440c500801c1998494036021300c280321110140083c1d400300b01c520030307404120f500004401d404d00e07401c40d191800018000081030041c010007003040780c0061300c0001403d515400280c0407000301003c0f18003442c40c2428050503004840600035076a1085010003040200082603500c0d40941600b00e010304d0030150940e0540354039102c0100c2405000341c05040c2d42d40c2c0700349180040e00e03040c01800c0034011034000c4440c2d40b0f0300321601d5400015100c080c00c2110014451038070072001d40034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 929272940 1250 929271690 929271701
    0x61c02040c030b1504060c17040f03030f080f06061e0f040f030c06020102161202120c010c0f0e0a050603041707080711040b130513080c012c03090105130306 69
    0x1519200000c0d5880340d541441030300180800b51307641e400300c200018003080382c03c0081e1b5007246030711102242d00f41c0564a071121403030103207912164009580c10f0012003010f40040c1648a07132002981c41305d4440da0307903000007940000107413480341d0000303c100081c104601c08030401c02e155098000c1c801b8503024800c100841740c5d9106134403000e16480050790600c100a4282c1c2c0074002450303948020350815880021043d4004000d10004241e55152501902c0c0c560082c0541c1241034950541d140c3c940b5401340d003050107882400903c0340000e001070041c010721809000c165107071600140c00822400d0900303007800030701d50000c1e03c00e607500d0340a801e00c150303210b90000c020507135148140090f03500c5450a2030721405604a01410b10b104504090b0b0f0200d19884981350b14030004200c402c0407419841d40c00c113405030800342038000b40c4500300000b2410308000054104010b404200c0b8075114170784010108602d003c004082c05064a90000c000c41070842d03101d1400790480c13602220400e14001d40e00d81d2000110b40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 929274190 1250 929272940 929272961
    0x50d150603140c0a1502070b0d060308030c090f0910090c05132d1208071104050c03011401170109020f0f040608010e0a2c0f010f0e06010501021203061c0204 69
    0x3d00102c1800c02c00d040881c00b50703000b0602c112101444c1d681801c4041c0d2103580300c0c003a003044100701145840443c0043c6c3c200600854000314220303030f0b03414559181c03004c590081c2040c0c1d000ba583d42c0c04000844c148602214032070303008410700070922801d05000c0c402401c90b00c040764040000501c02c5205003500a480720008181c4200740d204040000500b100004405c501070030040c02900da0304100e103414602c104c4608176848242e507a600c5010f031901d41c003040b09130360f1820b030860310f0310080106c080000c60065041e07034002c140224030448000c0c0112403490055200700012003030701004101d1428660007500d9108002d408240c00c1809400000a41e500190301000024141100401607000036861300358010303c0b07d5006202c0d001e40d6540c0040142c10002c0b02001e04a88070078569604c80040c00b02d0b000b5204443c000740007100c40c0d4101d64002d0000100049494000c1c3d200001701503000060480709014150102825962542d04014200416507541c141e8140701c41c000384010380e80c4c4d00c02ea54854 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 929275440 1250 929274190 929274193
    0xc03010e060f07020f0307060b0d0501050a091b030305070b100b28050403020d141207060911100210051302040f02030901240902030408040801050c0c16050d15060314 73
    0x28a8901c89100b03003140007500300d00a54000d82079a401016000c000ca840c03881c1c000e60081800081341010850b1a541c9002c05043c5518110a10052020a03040036050901800e251820000f200280050b282c10078440103010400c00c00c161750000e20609a85940100c0c9100c800074a00c0c0e441d0002c004a6020400d01e0440040c08000107440915569200989040d02d1a143c0c0c1410f0943d80800c840c04000440500f0032800320503128400c2c0c10030450701c64a48072006520b41c44240e0ba19260b000340081d42e90498080710748001c4a0500e00f4642c4000944170400c0e4024211640c10780b02801c0200070140c0040c1080d41d25001e080c01523102c41c000e03046450554072005980c1e240c590969800c5810b44010940c214400038034030406101c20540308000e980c082c080050356500c91b0303d85041d0500c16036000c82c5295007003104000f03c4080440140c06a01e03015803c0d110703032004000d042c249484041c066190700c1032310a0040310200304220700030042c2c0002c2a03400640d95403a61122002c5010720040082203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 929276690 1250 929275440 929275453
    0xe120309061003110127080d020606040b3a030e010e01020a02010807030c090f03080909010605070818010302090a0f080c0306040b0f04050307080406080a1128020c03010e 75
    0x801010440e807a8072455820504641da4115034425500c134558001c0a81000002210f07003078003800b4420607580401ca6220841a490340d80c40c0010307111240300f20918054020030740001c610707042c42d029003041040004c0180d0300c030701c1c0c880038840398441200035440c3c521340a041c2000d20079000034542d401c096000340c4809000d20042e600040c09500c0c45000103045410015942006036007024000740c01c040c49003030218500c0f0700304008603600052940211026050a0f80c00820311440310000d142c56001601d849229030b07215801a6414498018000c203403903000c0000008510600c0201c0180190515016107407a4424001852040d00c503003002d2020345d5030410800c43e0b003030100200d036083d1764281c0c01741003140340503120b02c655001c000b40843c0005082c1c80000e41008000c2c0b0031503c150307510920030713038407180c41e56002070106100b11180088070380f808900340420410081500c042d94500034030041c0880600710089d070086050b01c1c81c4015413103040c08441d035907078082c0908441d220404009048 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 929277940 1250 929276690 929276701
    0x509060c0a1b0b0636130215130503060705041203030b0d11030708011e091a070806031e061605130e1f0f06050c100e160e070c030e03010e1203 63
    0x50790390a40801001907840030003e90707114651208500e02542881150841c0d5920000c80594411407004029840ba0400323000f030341e8900f41c0030003400c4803203000c05a0350211a154024195500b20546014000c120140070400c4503c0902859202062291401086400b000400f052210300001310454043c601d402d8100818181000900020031454009000c1c034100001c00714100d017120304400e00b8043e241c4501105001410851060261a10301c0030901894086001801c118007515424882e004e601c04148091161310b060207004103110300607089a403141400f40304000381400b000c4061103020b01c4500c4100c3d00503600c600090000041c0040e891401062445080310411140a0b20b859401c0080c400c0c9104c2c00000c0c810740b60a810019610210002c10503e031800d0990080052401c0c40e41c0900541030100300402103101c14a1038542e09901c03180a40d0aa0300c0458403140060030410a0b10040ba01c54206402c140700003400014030003a1142c500d6080c40d0214080c200d0200b0008240b11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 929279190 1250 929277940 929277949
    0x12020301081005160909050c040b0f0409060605040605032811040914010e01030222051501180602100c0c0b04030c02012c0402250c08100509060c0a1b0b06 68
    0x40c0e00510b181c0d82c3e40404c0400d8a0080c1440500d40a80c10310159660000350707001290404079400b40100100181d218105c00310701c48410381c0540255128582030440010710940503605071016542e05498003419907542c0b250010180380f10062102c4600c005010840c050503151082182c8081e1110541380e0f214200034411054664955400c2c820b03800a900400c41a0701d0484410f041d00e60440346402802100c070b010240701100e00001c64105880c00c000d00c034061482c0d5508080c2c660003a00c1d0380758220b01e010b0307910f440040d00d072003800c0250b040031030901c480d04079a90095000c0306140c00d040000102a440b42076100c20b08490071400701e0004d14400080d0340e00803002c55803c000d071542c0380c006040300c20703076844d0b6140b0f40c241c50a010300d4020844103147e20329088604100418400c031104031021a09101ca040369052103114014040c2c408042e101c14180c0c09500d00c2032811b64020031258542c10782c0307140e03268000106501006100381d003040b85c40000140001c04107001e00803015030340c10900d0400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 929280440 1250 929279190 929279201
    0x102d020d1103090d0806010203120a0b010e03011b111e032a03040608041403030906180c0916021507080405010c0c050a0f0507051804050601060c21120203010810 71
    0x41030406428400c2209080303001844c0c2072409003501c1e0003c110345032400141c1c40c5001e00d6840602e005540740400900000c2948a254007103806d0346d910725000540820305088900e00410300442c062140e05449507a405910f00c48100340f109400c82e80003d09804050f810256002410700d516040000c5142c41d000381d50b9100344080101c81910b03400400d41e0b94409a0b00e01c02c1d40f0030001406076100014080c4000445103403001c00700341013500d035a481d05807140d540b03e050444450102c004401010340c02000f00040302000c59602070000e1115455543c101c0708454007804030501180300c0c59400f0800190250721280c081c0030240c0342c4520a051a207041402d584819900310300b0800801424400f140b400a800c048040d0480c0104842072040e00b007603810102a508440c5e0014001d48445a40032002d00c02244501d0040054848590300c0e01c008858006070301d90050030a03c0e08509c8000d80d00c0c5080c403441e05110003410f01080303101819060383d00b60b8000340c0c040c098a0b08406507000f801c082502a5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 929281690 1250 929280440 929280461
    0x207091a010504140f0a06030203060109170703030c020f0a0815010b03100e0a06030c0b04050f03010207050d080c070606140102011a101101090c0f0f1502102d020d 72
    0x1000c4482200000828078003540c8207513500724250180c01a510b8491809020040502504100b000c4da2107040c00341c06580161032081c0000c1000000188070182d00015000c010410401350030300610399142225400c801c040300360b900c5803000d050a112503175450b2a000082c0103400c00346c01611021090038901e07100507840b03103005400030030400c02c107080f51081c010183d411110341005180c0b00d07000404006c222580004010090325440801c803214014090f100300c0388100c1d5421901c0303c1403403d050a0340155280104207500c00061580400d0007090b10f581d1045d00148254203250031502c40703a05403052540701100030a02c0030002c540b5540d082c010300a114080b100000e6000b0704881c04502985c1d42c00d407d810410021411541a29500307411000409803c00a190b0301d568813240301d040550901d2080c091170803881400002c88101522560301c0e0004160003801001c51108001c00180c00c0c2603107d4164522101041c4000ea594400002040c0360107403001a2980c0a00c071031030702241c00c030009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 929282940 1250 929281690 929281721
    0x90c0b0313020424030305031008120d0209120a030c02040f023901060807080d081e04020f1215101223060705070b10050d0b09070b0703020709 63
    0x10000705050000d84a40081c2e41560300241011801090184204810100104e410741c82c141c0002490b07413100165014a110601c01003203141d60741a510740e00c0723410300480782ca0700c03c092180c10360b168455800f03411b80795000b820038003140c0c09040e6100e09106440d0821004a5619a41070007581403a00c40e030b0107480b030f09030000c5240c50361007110728007080c80d0158a010301900d441d00c9003405c1255004891040d1340004024842d203602c41500946540725402640614400d0440421180784242c0e4964003902d45074900f1640c00460108030404050001c0c0140c0c1c12a00310300801c00c691321030451450013481844082d0070f200441c1211010842d4018041312079000072000c0078031041049644070910f465100001030400082046070726002a480c1c0b070602054015001001840c60b0480018201c843c4200c080c074010f581d51250b886018042c1d8092150024858911100041c804001082c1c101e110b180032503007038664034082c0c008290b03c8043c0490040e00500e40820540c1d24070f015000c8000f10044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 929284190 1250 929282940 929282947
    0x71b03030e0a24031b26010b0a0c050102040302090a0209130608100203092b030f11180f030d0306091d0c010516020319030806040b010509040c03020409020d090c0b 72
    0x12400c4040980f50b84a01c6070032008003940e02040c043d510880003003215405c001e008200490740a4a040c20807180140200c40c0f00000403010501030020906030344800380c4041c106980c0100c1241c01d9001c403c0c0840e403665003000003001592750644d800f0b1043d000303031002503a983c540005101c1010607017500c500c1503034200b01050142090100780300a001e00307054001078581d600e04061524010070441d01815418102c2281e54494884220500b034403061902d003072000982c24980501111001c5510a040301414085000e203441000d10550880d000146600c805000040000e41001e401021302804a60340b1f031420070402c0c1080c010001c03200030003889041c014481c8015961544510f0107881d0400000142e404695003003c01c001c0710b40c0b90040d040303842c4480103c2d41182807403184441035022542d5100000d11501d058091285000c1c0181e441d41d00700049070081c080602141500c2200b0f2580a100100300b000b500d01c050070413404000d40c04100441142407408843c039a03500702c1c114450040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 929285440 1250 929284190 929284199
    0x33a0204081b03060112020f0406030302010b0915100509010c061401050a06020a020303031f030b190e1b060f1c20041d130503071103011104030f120302071b03030e0a 73
    0x11489504403030050314841d802022620008440d608c10440880c6d00900c1c016010040c1581580400110282a90656101e8a40e4092241d512001034079482d40480c02c001c0c02c40213140b0420241c0780040041c102a0390511040d554102910307201c41400780f824400300c004209501d0401d07080401070039940003030422015180c02098507440000c0c10844400d102c070640d94440054052071400654205001c0c1406081034900c01c880007042e400103880103800c120007201e54031004514801004a055501c1a034003c040082c022141c00c010b0030031000b42018040300a0385054081c2ca0031356100b415100140918000c46001d003030324513107109040250070511061003095480d01c19030090101040700e044299454200c4a10902c200ba9402425400045100b03410040d0007030141003038040c110001e0001c100d0a01d10404030b07014900c0094903200c1d20103884008104410023030701c0001030910380945480c8180e2221380031184504044104c106510200b0024158050090301094100726620030480307150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 929286690 1250 929285440 929285443
    0x3052b050912041d04110310050a110316030f1b1709010605090c090312070b090c0907020a0f052508120703270e010b07030908030705033a0204081b03 66
    0xc44680e55107901310701021070207020050300c61070b096803001400c9460302e0f280318090401904041d0360822296041c0f010014000c6240010b491062100501502030290802401c4016081800740f071500595111100c04000084001c0001440d649485aa0303480c1050311203403820110041401c0c130240d00d41030b0b00340300c1e90ba25014983c0c1c00c184070310501626012141c00007420304d80b201c000640284c200140e04000c001c140826039228140403001e407001e6004c3d84080c0844000c0894910005070800f000030400070301710806024100c0e0165003200c0f51900c46c04480c2c51401d2070035807403101401100400b00040c10701001100c0340c910103803103010700f443c8865402030100140200301c24502e40f0f00d00b422034941560b42c02104020b1404091034002541d440d1000d40c1c15500844040c3c0c0011008000805c14038400070459150592240044d480c015007460404008034102c000e11804109103034040209c04802c811183c052000c071032005a0301c2c0d1505d60f40b64134200071152920b40b50320280340580c0040d41c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 929287940 1250 929286690 929286719
    0x207172a0f06041b270c030b03030306060705120409020318240c16060204051002011a10120f060608060f010f03050c070c0f0303260403052b05091204 66
    0x500014660241c80b80b130061500040850708003407034443c4001018200f14125080d10800d050900c601001062080c00088003a54041d20000f90103500c00c01c08a070369814140300604a450044041c0c900d10f407a4202c400502d54003c0e0710400c2c0054001c81446002c42600c40102c00f1342100f00000c0c00491401043e40002185070340400c844020b46000080300000618200c1d00c3e0002e8400380003442c9a240c0c82c00c0343c025002801054010351120440483d0a4014411141d00c060441640c0343c0c40d803002400c025814010f4614901044103070718540c0281900e034095940c110b090214042840740c10700c2001055044c0c01002d1034480c002c400079141c0c41c1c1e41c000c0d561082d0001c2614012506a989a400000a2180500c020043c9443c1e5100041c8240106008029248a82d940c4401601c42e036030340c0182003070b506d40d40410000883c8d012600080c001c2000740750003081400c108020f003070030784100f0700340000100060840c2c60b159020050f0b032520900035100003001103001c0d24289070401258919048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 929289190 1250 929287940 929287943
    0x90f0b010f030c03080307030207140a0507090b0609061315050909060a0b031503161e06020c210a0206070f0203060702160e0c09030715031b080a0207172a0f0604 71
    0x5c000086540c083c46a0111600d4640004103001c041c22000c560f165200c00d0203506980502440b0342c08240c01159000b11962050014042e42c00c00400c8000c200d803070352143e01c041d28070194600d80080c00d10b40c030750324001c0c04060503114075403600c00140910a0303010004200c14480c2d64900c40501820310308405590308a0003c51189540320206004a4a0a42d0140c2c614016900f042c1300060704407200c1c0078021070600203000510446999182c26a62880c08001680e07004084000001d112824500242002044e0808070703408088240c000c50343d0b643c4003010075228051030b0f100310404d50908024454105483c0d20041401c0c0400c403c0020f14050140180320148807080042202c0c0202c510541c1d03c903510042c1a03d10a56440440c480d100702c81003800c00100f801c00c0074940080290740600b06900702c868442c02465640e44001a00a41c00650220780100008400100c0c460b81c11000e8004c5484d00e200494040710b03281c5480416106071928070505900148010b031080c800070600a4001c2e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 929290440 1250 929289190 929289203
    0xa170a11101d0420070302010605040c02070b0d0b0a030c090b0102070f091802150702011701051008130c0602010506150316111009030215070302070b150a0504090f0b010f030c03 78
    0x145080b0001070064519030030311070b0031480c89440e40b8400c3e180c900002c0045c2803017600200103a81d600e90510003034807003400201300583c010440c00c0065154a1b8021702d01039204a20008404040000243e02d0500c9600240c0b459401004280b04004c01403103800c80401d4240000c0c01c01c0f514200010910914500030020003584500540c070b040c10710364250001541e03008002d628502c1c2c091808580c2900240c0c0264002074945454502c81d2000e01c4842d4181c0300f002c0c20303914505182c1c007400e036007524000c0e09041d00c184170b03604500e001c2a50f0001590103410b2a44c004119824540c007001003a404400a6400320b40003001030111202d00840c8107200c4003802c3c1410a101c1114407400c40c28103081d01010851542000824005c05601040041c4040c075030340c4170010304d41ca0b052070880403402103800081c2580c48080100b0000d07001009a041140801016440e50645800102e4140e40c910711003103807035503030300d5060100b040603202407107014100c0602c55960f038510319100c00411103181d1201a000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 929291690 1250 929290440 929290487
    0x41b1502102d15050d0b041a04030c02091e04061b020d0c060b04090b01170129010c142d0a0506040b07050d0507020f0f07061d0a170a1110 61
    0x1214200100c1c4004101c020017510380303095641403c101d581c004480c110f440b07400160010b4081042040d000b8000c1d0342595484c185c00030183d007485000d41e409030040700301c112487d00c4041d0180469100a00c02c80c0f0844000c02c040b50881c4001c40e00b58564070006044d074003e00480a1036581c4424540d07005600914085413607244540800c0007440d100780068240499403001060400d82c031544c844104401400030007041c403101d88260b418002003001c0d0440040b989100082d95803242105004180c0a4100c0f480e0100071440f10a1074207020041000c41c0106070805c00f40703940f0310307110f800d004480d1180151205007800d540d60b680318040240010000942f40c004901186c0c400d8060391845020744004020030700b0000fa0180d41c035101000320340d402c1e114a00021411440100300303902107505503100c084030188150511200c64080c25482500301515140000305400c0080c2440400305444001d86102035403030070400f1880d01d1146581d405180840300e0010304c558809110025003510005100a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 929292940 1250 929291690 929291711
    0xf0111120406060905070f1805090f1b03130b1005030d050c0c031621020a050d030309080d0b0109060203030f010608090a05060f07120b09041b1502102d 67
    0x1842540c0244c0d0480d480c1c07404111005412200315102e015450f20381e10440303400302e038900648120a0060507003001c04031000c115500720321507085400030f440694051070f440d0006500d85a0303070011180d1401030055800c245050260800e01d56030801540d82182c58070506040209640d48010341c52501000000108140c45c039009201d400c0c42d02e64000c056419800100c40c9062046200c1d018512101d84c01c1e10002904420000080c81580d80c00341044000515020400950f10303510390041c3c06164039020b9910014070003900605200704081c00014000c0d8803407000400b0200603802180a5610400601c441013a1182160381126814a010740c40c1d81d44000541d801c01c25084002403041c802c1c1c0b03052281c401d440d240007600c60440c9607070701c0d5458040d03854008151100b88000c2c58009460801203400314400003081840d85414601c03880c00c0c00d0341e0380008c10540b110801402c00580014a01e20004c4505000399400c05103820041c0104090405c52007020030004042c40d520b003039032036030200d9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 929294190 1250 929292940 929292953
    0xf020c0a080c1f0501140405070e040b1c0b1602030307021038040e030a21020f040807030209161b140d020303010513110f092d030f01111204 62
    0x3d0b01203216082030b840040f41040c801001d0300742805075036035117540c198281d80107050500c0f80c1761041c080c0380d03622243c0c5614881130200a10082d0701494004400143c00c11811f01a03000300d40d0214854518004185010b800d42d1480030a15800341d400c6400c1081800540c946c0040c05000344e03d40502c001405450301c1030310a07505130240420050300c0e00300f402a040c3d4191601c00d020901d0784240c0d4107102c80040f840d0074a450303210760304940d004100c8500b1070b409001003480c0303402800351030301c00300501e4840078240d007012a82080e4001c82456124000c14011400c1003508142c00a00005020000b204030000c003070402d000101c0c00c0d20440005d030304280b05002c035100c45050105415420307601c001030070000003901c0e54024080c0501072009130105441e09503042c03249100100e0b136100c1203410f0410907150f0074070740d601c0812104e90041c101a8850f048218039007400150320322301070010b0407081e101000d240c140320740304103001d0803a4901080c584906901c7c000300c648100810403000b0440e80c2d1854540f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 929295440 1250 929294190 929294203
    0x1050f13080a0302070f0b0402100503091510051804060c0c0f1e08030109090309050607030f20060c04260303061c05010905060601080c0319020d020705011e0f020c0a080c 75
    0x607011080601b11039040c804140c43c1e040c00b4900966441514103d00700f01a0707507038801a114000d0543c0040a000394050050b511103421044221511691543c0c81000410700651516001c00711a201c0742070104201076841030400381545800e0014015410b5100e17031600136800d4030054003003000d04d90200c0c0c42c0400070301d6000d8000c0c0d00c8414a5201c1d42c440380800003c03c0145011400f10b228440c02140c10300d00741069030041d56050351258986080e00c1e0085034983c240044005090b05a800581f0030344105202c0383d03101e10452411203440d140b0341414481800680025080d12411a4100ca05044004412039901030810b0b50300080321110403002400140215101074015440c1c44519000c001002c594140581400d994040c115120f2035101c081030b2100740c503c0440c11405195507400c0a200c0e40240c0519a100c0f803006041100c10744840d070941f07248410b02244103124406848502886100d00705000b9a0b2210071418035007151041c581d144030104c409080724001040d0404030303450402c0724 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 929296690 1250 929295440 929295443
    0x1c030b13140105011202070f032a061b0f0c0201080c0c06090304300b0417130305070b070206030114030c060c011517030304120201062601050f13080a030207 69
    0x82002003049400380c0e8065070203000d1a8005911407810000010050095a6070706410100d01c84010740240da05441100101d20340c20415000040900c0307982c515110310011860090102043c42560807000c0342040002c0780048060140e031880350498190b00040307101c0340c61ba080c28040840d480c0e5202002c250b004e10300482c8035600c105403c00915400c04005001220740b204075000d64403d0302e0b40307020300c00f81544154905882545200c40c1c042440304201310f0300b150151010110755400c295000e4400d40c0080e50740c403e0400800c100304204042041007034000c10400800a08283d00c4d0390001d0041d1206210381c280d0f0489c9048054046c1d902800054004a8000e02da555101d200701100c0c1d021700668140c07820500d101440c000b550784240b10200340512511000741d86555039036943c91400c643c0060142045640c1d802c030100706402110f01d101c5c40021a042220b901c000304030455800d46800802c20701c1c01000f0b410a000c4405800894ac1303400507484401c10b40c40d802052800c030000d0054100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 929297940 1250 929296690 929296729
    0x3250f050108011508100b1b072c2203030b090a05100501230a0c060605031c0f090f0f0509100f03020d1509080705061e13061b020319021c030b 63
    0x1110780c1e08c0f05405020803084949a419500e84c940d80d99402c00a2600d0101c55144004800d5030456600419000c00e030340c0720004041001c020480e81481028801d00c1040440c003007680c8094050701c030300c0c0410b055a07201035907034014005450090521030352030340c0368890503042c0043c00d145804071074100b0b1a0b41d0002501a1445601e890340c600c00104055076880003607810f01c4c034040b800f003101d05022030700c0c5202000042c102105d000c543c82045610074000c4042b502001200d0f58081a005030714080c4000420310311040e400003078140300803c0000000503050000341d54000e9010000d120f64001c0c03110440390100c40108805800382405929083c400003858400d81c42c0c141d41004008040018120003406081201c107250741d84125905003011070885081d03403000c03500c0000e084541c241c0c0b260061900c1250003003001c1c1d0001c541720169851071034111002d40c202040c0d507140d0b0b000340b00c101c84680c9030501c0104003011000180c02800402c98120104041c0c4841240404d51079103815040c28010691 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 929299190 1250 929297940 929297947
    0x1e05151c082a030a090b030a0e01090302060702010c02060f0619030803460506030703200103051321090b220602032703250f050108011508100b 63
    0x4803091000311102c1902c07824800030720079006800c070000040d1188180035444a210b0141411090f100c5e60300001d20f0804003e4507000440c40080081c001c0701e078854880e400034840da040406020307003520300d1004418115403003242084190b03e11900c2540c1c10410503603021081007500c2d210090035922903000036040714000402d000300000c549004843c59490540c0603100590603904a0220000c048885103480a4011001500702c2c12544911703007006005085810701a641e6a5008100018004601100003140920340155815004444e84400410380a004c001d0241d1f0b161a010310307190508280205010380810540da008030348403c098070310180e0350754680081008010024240141c403070400b12518000150300e500020544030b4442d05c010044000c2d000020342e0700c40c030450910400f0f0303162003101500c28207d000c025842101c0e1040c002e00010950806c07401286004841d03025504010000c0c00401a050402c070003d0008001403401c16001e8980440c00351000380c0503040030704a00c2000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 929300440 1250 929299190 929299207
    0x408090301291804080306042408010203041104090c0b0c010923010c021603080904060306061707140f010f0201110a09030b06040606050901050309100f1e05151c08 72
    0x1001d09090a421508040120110b2241d00d403d01000d80b00108408001d10100d449440c00d50043c880d0814110f64110428980810700c4001045950000704e46950000621042c06200882a0308641d41620305000c50300545d40c42d981c01c03021520540700d0041010903920451107080d080b20050a030480c1842514613002d4103c4084603d101c0d00a04c0d2540ca00501c031a1ba090021541c21070b00f041006100c1c14041c0395031a40e1701d03240c1c80160340a130f002c0e07074480003c4009a0307142314a0014004c0d11111500d100391200049187c440c694002d40c03044c0c01410102000c940d10f0000705095100b00786401c060b509404035060b400b40c200c4901154a400c40890301c2542c040d80b2511780c2084030700491820500c0c1c1c80710000e001c1118618020b2000281040001080550040c07008581058030402221881c2503411540400ca17100038180c07074600f030b80360004004004603608841040c20141203042000c0e04014000040b070183c078101c01c82c003400700c001440f02003c000400130003909401c1034900d59200b00c40b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 929301690 1250 929300440 929300501
    0x10207300c06122009130c02030403230615511b120301030f1103010b0f090907090509010506040c020601230d02060d0e0c15030408090301 61
    0x80b0300a9000003460500401610003940c001c20142d6040ba040043c085440c2c002e443c40190b01003100240c00c141400d1402d032840e10b60303106440215800d40d001d16100c070304602e000c1c0c0030300b2100ca540300a610007010300803e04840110f07a294004118a21124a50308120b000c640303a40301c0f120b44080451490454400c11092060046224540790080b81d649494091100002c01a0b43c400802c0780340070502800b08812103003030841c4200d25025040b10741282c2d1803018045264409d03041190395024244424040100c3d141820101801c1180203108002418001c200148032105405200d18100c02c049007600c0703c24031000c409084070722010b001c54500700035a075011700015214540120302c5c208070120090710200300541601e29034843d8210324004650301da00070760401c40001c0e40c450b10902840340180d075103c004107500b541011011802d207095400417810070070310414050003a40114140e0300c080001004a80d80a42d00100c06502d440d01140800c1c014044907260b02058610740a684484010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 929302940 1250 929301690 929301713
    0x60e0403020105011a0f19020a02030a03050c0d080c07020d0c1203050c100b031509072d0b040b0f0c01020d0204180b0117070c33060b0901020730 64
    0x2801c0003100b002c06440b41404603106d5901441d18880040c0300309507040c10340c408107030807520181c070440d42680340c2900024202900c0101c11404102c0000d4165402c000078800b064003601c250500091500c0d002e00d00d1800d52107900002446800c8600800c0204405001e6500103802404940b80440c1c9072440d004c0d00075400180101034500c58400d41030107101f5107018000c11000064064900c0030b005406415000201034070f000c030705018440e400b0408242c409003200a508940f6107040701e1400c0402d04103101c070754030707040030b007580204010510a102c88582200d881c0512030a4503945c440d0f002d80d4541c0280905007000c80228000240018584602040b4264100c443c0c40b003008841c02c044010341f080314083c00340310340700842c0b000040c0c1c10b507014440743d200b4ad81c012201c1502c1c2d8601c0c2c020b0681c0f004418000030f000110f210f1100c0803050b02510400000e440d0082055240441d040000303503a94041d48900c0d013078003e141e01340c901940c0b400d05002d8001d0070140c5941d65040003174548900c4104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 929304190 1250 929302940 929302949
    0x14121806070b19090b0712060e060a03031d0d0b060108060d110111160f0501120b01140313060903030e0705060f0403140a140703120305040c0308030903210f070903081c060e040302010501 82
    0x20305040002c109c07a202c08016902403400100800c2d03603585107a4040d1000305801c0c0d18a04c0b6809514443c42a64903244030401ca8544a01c04201c454a44880003401a0030042d1074a0700440c400100480010403030310f078440148009003841070520041c00c3c101450581c0e01c030f00e4a03050984103040020110b09804802094a4090320713080c0c000030800c150701c401c41c0c0340040e03082c0c00142014948000141c54400458100110004601103401903448050581e60310380d10440009a03244110810101d003844081c002e444201d980e61702d001c40c900e2140020340110700010308207201014410604890410801103055800100410003d02c42c00c0750030340710b0103a884299030861441490b02042131080c85075510840e8424048100705d4110340302c913290768100414140c1c02e440704000544001c1d903960f511641807034a40004d00c1513880c2900b0003070441c50005d004038060006050381440007481c060309841200c0c11804c440200001c454071001d0290589600600d5802881c0c000c4c07006041e07040d000a4140e8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 929305440 1250 929304190 929304227
    0x3030f0e0f150c0a020c011202071217090703050a06020c0c031f06060908030a080c13080a14010203100905071403040602270d0f14121806070b19090b07 67
    0x1c0e0383d14102da106a20034501c060005030021b101103009507000da9144061400000401820114039583d05c00700ba240b14840d010204013015110740000d144403180951010b80785010f072840d94a0b5564a42d0748009041000705031036000300303083e21000d200f08441400600c0043c120351504840c1c4842c506c141000302030540e00141486404070b40d0718002c40b045012186004002c1d881c0c000c1c01482181d4408002d800140034550401c840d4100002d204207401c0076000c0316002e8410307600396140040e03108240038219001030b401441000850001c02000c50101e406e03101c0e0104007591240000c41c0c502440001d20040004040203110a000c8203a01405110043c1440c1c03107a03040c1d48500f020400c00c0c4014010354070101456001c0f00141001050326040d80c8100300401c502e03c000c1e40c62509017268180c210701007090103e20045074010942420018010517030f00a450107a0548504140711030007030100c50398000e040210342d0031080950040c20660b07000045a40903041c00040109400800b95100500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 929306690 1250 929305440 929305483
    0x905011512120e060702060a03060503060c0d050a0603170c120f07030f090807090b060c010627091e03020c0a030c0f06020303091e0a0b010914090a05070303030f0e0f 73
    0x82d40d019001041103204018066420f0402036400c1001c00d5008a09820030192111b5000a05413410850113000302c1c1603c041c50b45492100080f001110301c01411020102d0a240d01000818280414170701c07036401c4080c0007541c9041020700c061511107090420240d20500080d00d22840c48000b010745200d070701c40e82e603040b6100321b43d40040b1000403090142c82c08541000800300300d40d201d0341c0d0007030310401d0003d003110341410440075860f0708461841d80014180e440018459041903801c19140030307403216200b420040560710342c076162030002c80044012a140b40c154400000e0500801c640d64050b40010801c01c034164491510003042040d500c03520921120814000c900c550011060f680b042140c04014203e4086402c103000b60a211784c000001d07640603003021000801c01407c2c50303038080c0c180e03403401050300034030f446050203240c000a082aa46400448820000507804524082101d4141c500032a0030078030301c10508006c00d10400039280d01c1c49810005c640c0e007140441c008004050f80b0000145 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 929307940 1250 929306690 929306723
    0xb04260a060b0411090907030b04090b090105041a130807030504230405010617160c020315250c060519021201090f09050d18030602030106050c0c0f010c02040905011512 74
    0x42e802006406648106034000103240523100741d001040c1820000c0c004110701c030a680300d1107000c0406480242c0183d4585d000c01c002d000c030b82183c410114107004031001a80c600304450040038001907000604544001074290289485402902c0182607942e016125611718080f0036030b400303a40c54540500590a10000040c014013030403131040c51890380954403503c2da90b40500301c56600900c00200051101080300a005a20100301c4d0710f042808041c540c40b020709149100023101002030b1300401081c600e10111100055128002c00e41c5254804804075681d100c0c00019412051400005848031f131000c0740b0100b0198000d01c5441c1221901307401000880d003401c0c82e00c3e042e50b180f40c8029020b90310000f8043d006501c21103403914034641c4a0820742140e5143d944d480184c0c0c0c001c3e80036000141002c502d42103646024015a840418202c8482c904e001140d00040c208010204000e031041c0c0e078038032100090103020341210034006011085000c40c2d64032803814101a00c6002c100391250030104500c00c0d03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 929309190 1250 929307940 929307971
    0x3070e041b08090111041a0d050c0a02010506100f030509070824060f0a050108071209030915030e1209150304030f12020f16050313030c0914010b04260a060b04 70
    0x54201c02c00c10a51b2405040c0343e4400c00c0410041c161403410107041018400746100c0340300301e40c05039448181c2030f9a1640d48420090035030f0300242c42e492085c05c0402e105d9000503080003100c681e00c1503c0c1800714495540c0c0c80841d04204040d4021100c0e030142c00c500780c110000c8800907040c0c000032420032144544400b014003004880c03c0045a80003482c500c020b000369030003040c1c420740c40070640c6407050030022012300490a480582c0001c4002c1080b900342404242c400c0c80c1c83c2018108540390030480501307200710440da640100070140800100020342550765480d022455a815021302454070341e01c0c14603140090a154081200200103400103030500e84811090085414092840a1482c1840712102081c841d403200d041003142e0520041103125036000b0700c4c500c210300660113100c00b0380500d440d0051400a503485141a0485400b07244014070030490f00360161004c1d59120004009110580054407900d015070100701000362143c00004003c128294201c02c020030000e6409201032000c80c101c18 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 929310440 1250 929309190 929309201
    0x60f0f0302150310091802100314180c04020705100c090807301202370321051005060a080a1104050a060e1c0201080c03070e041b080901 60
    0x9501145200b207040c44078001d100038540088040b0800c00080da0380b480c101040f180c2da540000f0714046800e41c0f450035072801c0d0080d0507001450303003003e100014101044811400c002007007503102d08410b900f207a201c010104008050324401030800c641e2034505043c5031b940c600c080032802100e1070a009140c14041d12510904081341c0705000140451800c1c101000342c09025070700c0365461696080003103111181c10044910080e402500c02042c04100c1d010021b040c0440c0101e60741b00d045001d094100040c001400e40848040010300410040255180440e462004150318842e0100e01c030900400584503035100500a8400d0b04949003101d036584140039650180403e8003011a0030a00081c82450050f00200d091455407084146002d8850000800448a075000800042c0d16002c100b80c041c02c10480108524074070751020210f007859540006c01410707000300540e44006000c000301c0d00c614051504524403580040051020700700c006004100003090400701c070b00181040000c50f00e8900d061285 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 929311690 1250 929310440 929310443
    0x5010e07121103030d020a080601020705010810030809040f020a0215010e100605130504150303030e12031b04050a030f1b050907270b03010512010e03120702011d01060f0f03 76
    0x30120382592214030a00ba51114141e4160104019224840c40300b48014a50749420f0b884034141400c0a0000a161402c907800c054103000d4120f00f48213446940c440d550f011079174000302903035440c04210003240c0170b030043e0940c244c21640081541c2c8512a00420586c2d11181c5000c10303501182c0ea1894807140d8044107440b50108411095014864984181300511400441020b0036541980c4ca00200b0121625881400041a02c81d00103208140d07250260601518490000348002045074940220901c0041c210301d00f26203207500b400c1a4402c45a003507030000d240050018050550720b00700660301485d0000119900b00c031846500080c655030481c0c45040e210098038411032640c0d1100140d03405006485410a1050030060740301c0c80c01000501d14001c0e00540b0543d80d2a54502028030919585440c0b80715031603410003d03080c6142c031000050301c900c40c840403103ca1983c0c503214400e07801010550b155500608020079120f40d0f210054114204031070b0070f06400c01e403441c0d41b00410725540409000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 929312940 1250 929311690 929311709
    0x1e1209030c060c1c050601050c0f0c0a0506070b01050402070c0b0f0a1707081530011107050307020f040e100b0a08071a131701060e0c0f123105010e07 66
    0x144202d810307044e5400039a01034018105140b919440d41500d51811002107000030307040e400051140d18a0070160003403402807005a071302c2400d0100302c1d076407c0d095050501a81d80240e07404505a02400204c2d00c0203002005015800741e6120b580c0240c8106540c0800755005c0800c11034145000039601d68101c1c0741c802d012641c1c072460592242ca4070000d000d21311446195210170034603c94102202030480705040221003180c40013459801608060965110b071100e0748031aa0280580c81c080740002c0110780e021503041394200305034640040090b0060610340c4004d5094071941c51031049084003940907030f451040031a0a2280e03590f6400000c0d54400c5107010725800500340381001305004410501400001941d6018090744e940c89040b85002254402c1548040384e449560410103180d5958002c0d4000c400f05400a2604d00d0100740110300d4030442041201c11030044000840b004950b85107641c00c0e280d034461680c2810716840115101034100b410656041d480d1001d46415510001201d0f0100c544410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 929314190 1250 929312940 929312977
    0x27030f09080606040c11100515190b07051203070c02040f0516030209060d230a0510140a0902032403190803130b0a02032203051e1209030c060c 63
    0x742030001074041918040700703004001c00d03403082241040c0501960647c12010005503840c007480e40c4003a090041e5021409403072500964a06078140001c10f03410385c0c4085d020542d441c0202e20703105107003928201761030105e02002700a0020701980503200c1c00c2180d0007103130280700c20040c03107001008440c0166100300342000b84c2c84d102180c13a400b940140c042d01100074000340c101100d0181c00d200751424040f2110725002d45540c04802070855104168015500c54030400c124501410100b800e107245000d41030385201c071055610701e0b80e079070881c403000640310f1076505644a041560b0316800d8005030072800410700d04040d400c640c0d035080010f42001d049040b03001041d02c0810030346501e0101ea1016000c0e0800c191802c0c481c101103a030120360309002c2c0360b01c0c030300c01a528940300c00c060f130740700c580401102040c54171080d940c00801e51210544a0001c02e022140f481002ca14000031918881c51030600760685043d420090040004000b8101c81001d00040d184965a4003040543e41d10038076030303071580010084 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 929315440 1250 929314190 929314201
    0x1b030e280510090806040c170105010f0314100c0e040b030c1003020714061320010c021003020d0f0606091a1206010c0209040b1605040810050a27030f090806 69
    0x40d4040001c924100303501e003c0c0d2a040c4075400c101003200c00b59102d8901d02c5081081c0c4815003401861070700041e000b041f41d541030500c0012103019a10000d024060f095184080d07807103040c040c1d0884000c980390f04000c0300340d0350040580f042540035103e80c4a5443c0c102a000c080c100820b04940c201e0005064801804a0060580083d0845241510509080541840e418a0410440c1c0c0103e0100c56111884440c6c0d1500c02c0141a2600809080c102c5200d00c0c1d009036600600441d444d1079040f030722014040d4a14604800038001c0e01d09100105040082024804140341c0c802015113401d540c6601c112074403003c0c9601840c9030361203405041130040011100e606131010791150042e50500d480544c17007210341c0015681100070380701511072080400034003034080c0400004205039492400c0a50410b071030a181e0545440c0c1c4220702d16003040c1c803500004c0310306850390b02c05a6103d20190741e05075910f170080c100036902001c8601c00c40c0480c02c14125002c0d01e13801000400103c541c0c841c000c10150303890 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 929316546 1106 929315440 929315449
    0x902030a03020c151204061e09110405010b0406050a1d0402030c1b010615030f14040506090d0e0a03080a0e040f020703020105150105030f071b030e2805 67
    0x401282c1141404964100e500c5904514002414a90101c2c444010748d4910340c13010205150071824810490015282c1889074420354080099a0301d50781d510802c1d1060f4000e92020520600004035624410308280110f60104d0b1b240c02030b1110010301080982c0c10580740c071201c500004c80c0200160074400d03400c9407200c41e808000d0000c1031a01b0342214049000c5803200e01010b80320595000380881d16001a003030301c07101c4400341c2001d00d414203069803210000c1c4c1b0440780a016130340c3d9400b400d501c54140900d6444000308588882407941c0d40301c80440e0300030000c10040c00b00040c0016100e44d6a407142c42003414180e80d015a480180d403a0003030842e80024910322a803050b40c0d2118005907800416a80d00c05a186020f100700d80340c1c1401911a98282103d052100b4010601ca504156021150030031954040e10200e00d00c2c5881d241169004d2000f070846444188880010020781ca803 = true := by decide +kernel

theorem cover : BRFrame.Cov 929136690 929316546 := by
  have h0 := BRFrame.cov_init 929136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 929136690 ≤ n) (h2 : n < 929316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
