-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0369
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:27:36.29297+00:00
-- url     : https://prove2.me/submissions/86027bf1-101d-4a14-a9df-8de8d62a6b05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 66187053 ≤ n < 66366909 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 66188303 1250 66187053 66187063
    0x412020a0201080c0327160602010207151107060e0a0b090a03090e060111100b0a120f020108060f030a032703111c1a04031704030219080405060a0e0f01171305 70
    0x2a80300305020400381c82c018046d079900c203849000c0100b030492000c4009186401031003221400c980201808070003d403c0c002d01d40140c06a41c84400e4041d100b00b200c140800c03410310908000284140241c11580c030282000d281c441c00181c0814050340001482d00b00003078100c1c0c030714000c460b03106442c0302140e5294001aa41140303458420f40890294080003500900907a00c200c034060b808483d05901d80f62070351380613145203602e940004c00f03940c42c0000176470140d805020303802e5021000900034220704801e100485e05002401c04203e02181502c4110601d840c081140c0c0d084480140544030003251443d203c08940708100e407541805042d1882025805030401c8042d00b80c9150402802120444108000390380e0344c40840f02640003460090100e01980c1084000038015a007550040004207006840c0d0041e0040c061011500c85804210009154880101030005415591102c01c01e0f40b03102024490031074828a0014100050800340411205803103108075048400900300042440301c44c0b5080c1d20300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 66189553 1250 66188303 66188341
    0x608031303050d020a0f140703020a0303051206010305060d0803090f0102130f08070e0703020c0f0723190303050d06080118150509060105040b01090f030b0412020a0201080c03 77
    0x140800105900c403210400d504034200c0e445281198002181d05008a07181c1000000040003103e404500001181030800e400514032080e409450300c89036a607001031101e4406a004402040000c60180c240340710b1821041e0b4089420708051100d89041e500089e02c14040c66401000d00c44023001040840000700714155031011588000c540e600b0303440c40c110003040602c6c41a410880702c400d402140c3e494001ca80351044800158200d50309031590300c400c1d4040d411003081d98100d41324200110200031410010301004104901e20000203413841c00c00007101d400c00802c0325014140103100c08900065140c0342d0421070f80c05280c001e48aa52002500b00a002d142d03109902940c20a2a001c210305000c49003001c0c11441441c0040111441d0000310080e101c1c1107543c4592504140010001824039030090170346800149011300b01c0c01d440c1c4690510742c07a50f50f04161241616442000100240d000d168084043c40340002c00e6614101d03400204000d800030580500e684011003c110410355815a083e94 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 66190803 1250 66189553 66189569
    0x160206070602030610031b08040f0203070e090705040905210d050a050106030e060f15010302071e03020706050301032004020f03190b0109050f0603100e07030609050f01050d0b04030306 81
    0x20310310090410300c0180d041620781c1881007032500044510703240244500780f24181c880d0f00c0c4028260051009441d1603000500540d040343c0b58290301c3c0016a000c2c414100546103006101c00142843c0741010315200b0715420503030085281030000380100300005a051902c1d02524502d00c1c5401200c1c441058078003030610045445400d100600995188540085068034940d607800c200c1c3c2212054050303600c102c00d90b00844900110b1010034810020b00c60b41f000d20b40d406040161401406030f4500c44a500d03980e040200344074041c1030031010560f042c0203002c020140d42c680341b070442d411520340c0004070342c020400c540d80564020282c10700d070b01c603601070300c41d44090020001e0f12840c1c254407080d600e64181141c0c6142518000c0c00420f258054110b0905941e00070341071180c20503e01c03040c0401544003904107042c080310908000703448008002918820301c00e954020401502c0d00d032114090f01c0703000e044945071080c40401800941c99800f815a07410741c100080b100d03107480c0c030f04056008090b07903088210 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 66192053 1250 66190803 66190807
    0x50d020a051612020d0e09060d2103050f07020f030409020309070f0603020a110105070c061107050105010f030b0a0c05090d030905150408070f03020904080c0c030304060804060f1a06160206 83
    0x2440141e0000d004501101c4e001d6540d0401e65000407030710300004010b040c0e408080e0401007001400e016080081ca907105200b50000081c42c6064071700b00842807403403000000c0d1500c00b04035141c07072407440d10354008803140010441c1e4002018030a80302e005d12300074030138100d6012001401a420402c6448014011029001d20141e2103400040280d8840301c20034010841702001e0074100401441000c0c4204056a140440c00080b691130b10040c1c020300f804002403001c20b00044d000b1660a100b518028203440400300e00c0f00c0d145140415004070014a2018294034010b0307046d9407603400c541100c016031011507800021105034079040e207a4415030340200f40c00c0040c2003e10280001c000300180140d80802c01156151503540700080200204d50200a420684d100c1c04240025640006801070030343c090295003010451501003880c54000303500c60000100860284002d100c0d003846440350316540280c0a00c02c013a80002c565140d81182c100c602d000d0712000440e0f01500401d10360b0001d1180e40184225 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 66193303 1250 66192053 66192097
    0x110405091c02070f06111b010906031505030d0e030f0a03020d08090a050106090e07050402030108030a1110020304060911180105060f0c0709020c01060b070b0109050a0b04090b07080603030a050d020a05 88
    0x51041b9860307031403810240b145044414511440c02030b0146c01c240140e50740c00303040e81490f1045014200c0c98203040c03a100c158842c04262580c0500444910f04850b507501000703500c4075030402d0b14200c001c1c11032000680040c103580e008207074042040304403003500e400d0500083c0c03200c2160f03602c0c0410310030010f0500c0d480c00b000801c041030b264020341c21703114416045500072621081004100c0c842807040e00c10680c401c100441400d0b014800c00c0c1d0803421524240c418041183c00c1200503644221000c5031607903503c81048080000d5801080082c0d00250b426142682584008400c4160180111442400301081c0e42e600d01126030200d078401501981600e01480ea01c10070000650072018010089500380840410a10342c0241a0f4003c150040820010f0b0303440c107103000c402403801402441c0c1958407080c84280307a84a0b070141481c0e042c030413101c1c0e00151070314071001010b00002601c9180710307030001c020840c1c401d90b005c400d49141c010b00c082c0040e82c42003458402c1d1303014032030128400182555400c2c50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 66194553 1250 66193303 66193307
    0x30e0f09070c020306090706051903021603260108030912010222030c140d030f05090406030807060614030d050d060305060c0415050708070f03091e03110405091c02070f06 75
    0x10000d0383d1090303048070f20f41c1d1100303c034481d2112900e0207400c0008000f40300a0340c501480c01a249a074840038200180341c0409141c600000303600443c81a00072415080032100025000d9842220300061910190081d504050703102ea128411040c1c0603203c1c0d0001241c1800c2400c00b07604841100484588503882103000010080c10100f851200742d4803040c084000080640250484e02c2c40c220300103010005100c0e4903607064504180070040e1000b00042030040d40c0c002d8070750780300d41c02c0a54094502640c81e440d982c41e100091390300c650403183c02e04846081c882010784001a15aa071039055040603070711200005e002c800184095840a01144922018403c85170742c001c0040080e9400250800303104400c0000031fa8182c0304202c1c000706160000c01a20740442e00c41007000303084e14030a24203a03140c5e9540d21422200104808024281081009010401c000a00100d511810010b8030148060f1504032034003a00d03080d1543c0c01e0017482c0345001090032107601c20301141d4054000072042c0b040381920b560380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 66195803 1250 66194553 66194567
    0x1091a0a0909050c0307080a02090c0403060c030b100e01080601030b04021603080601110111030604022512090e010e01090902060f03070513050906090c0c0106050607050c150c0307030e0f0907 84
    0x309894600074804c61042ea414080703070140c15520040c004000c0701000340d0a004075094000e1428003007040601011001950901a8030000c00490b6004903494644500304219413194010710401e00416926202041e6001040366500c840b00342400140344004002150181c0305400c5404110400e040a4004040c1c200c40c41502544080c0e8a03421308900c0040d05a088820055050200b08002d000151913858180c00a00d942215040000d010f0070440a98a8220940a00c12507034103104e0300441c04411786c0310042000402605c04031861551401c0d103809074000041c0a10f0380f0050b11250b2080964803003c4c211200342c030420a02664070701d02420024060b030005803500140c1c824401002880f440c00c03a1003580580c0c4022320030005611100038011869009040c290003d5484072400101039603140050031002c0d0194000e4000c002550081100c0071100fa900c145903268240000351380060000150b4a0942d4142800f28010320301c0c10020310949500c1c0441a4044282c408202643c0c1c1d015035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 66197053 1250 66195803 66195821
    0x603050a08040f050d05030301030809120a0f0209100609090209030f0d0905090c120a0c14160501052d04050309060f0703020d1e030504140105040308071101020a0801091a0a09 77
    0x140c1208032039114400c1100d040e020b0300c0050305587c400d0005001080216004188d000d10040c00e04200e03407a01200c49081103240d49043e00c0a001c0c0c4807009056060181030560310240301c1d084a143c1505002c00a0001155400f5001c080f680c0803c2d010f00a8070100601c1d80740d65214022140e00013404000201190698000d0034040c2c0004008a00307001500d0056810010842d4402c00e980d0b52410041e100030070036040c0b40404c21008081b40060400081c00514070b10603c0001918a04858100319003980d401a00034500d0016088003981c11001e80050303030410701d814100b1800d02d9251801c19525600601c082c207075115070001880c032100c94a01004107580362185c2c090300d0300c0d241d9825048d82e106039600c040c03405140d280c58034400e0880c881d9000c01d5210b44110345d080700c10f15070700316880d084034822030301100030918150922076016004031010190082c42d000a51414581030f5000708048030600c01d019555131210000d8a0f410400c011314070b10920050928219180c1d95250300016000360300c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 66198303 1250 66197053 66197069
    0x617060a0f06060503041401060905091006080a0305030615040812040501020d181e0e0c03040308010b0c0a060b010302072f010509030c0616080c0601060f0f080a0506040603050a0804 80
    0x405925006509000b01d1007101c0f400d8450508550342d40d125451142d40340710350f0143c40e540e194000328585170350744103950049002d01d0080042d22604100c0d4022581540c00981159100c05074501c000b0703600404aa0340100240c1d111080715408800c1c42c5058015074010035000c0c00340e0b641e00c000042c041c001070b2089030300c240d00f10380206d00f182100b40d815009412107a02c1000800c4c40a01000c400080710780d4800d5000402e2000340d668a612101d03c042c01900c003d0100c42002080c4414583c1c0100c1840c054007000030303110700d400c546940041e030369002560010010f0341c41d540200301582c00303541503074255504a00101030703240720b2046c9074a10141403404045240d041d2503282290307511520580d60b00c5500540100b80c0d140c0f83c101001441c0c0c00c1846903046000b0095074880c0011046009481c1e150030000041400c0d505254002c0e0a01082e00c01d101d0405c05020781c03540a0f40d07032141d81250495041840011113880741c1c40454040c2c1075540014100f480781d0340e104410031018100400441e003002c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 66199553 1250 66198303 66198311
    0xa0303061409011a0d1e060807063509070602010c0504030f020f0a0506040906030209071704020f060d020f12010501090305070605031e0103030804060c110706120617060a 75
    0x35050821800d41d654a000d50894a240c0040c098401c541c408152620b800152550415072801000401d54410b0303140c40084440d002c45081c1d42c0f108601640010342028406407550604251004107100c8030600c9541442040404c10300c5800c90344841c00d600e1072000603003d4594034141c034009640f2042840749600544c40d080742403030180d21500030b541c2980e9202648125120130354081005c481d020bd807002ea40706000c0341d00003900d075880100030700080200d104007140c001d00c0d5004001180074001d054005001943c05c00c819200020024248d007c0da048420600100a150210f00c02d4064070942d0140d041c4006008024132080d9030140514442490385c2004d10ba0b214001185da04085100003003076a4007100d03082c482c0c507001d1800b55910100f20900317024403131a031041900a030002039000f50041000d800a100501889001da41d40582080c20a0b4054080105800f541c0300e0440c41910100001c0d80d50742002000750ba00072100074124064001d60a8046281c004c1c1caa500071f440c0310741030501d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 66200803 1250 66199553 66199559
    0x10503011104050d1401050405070303030b0105070c180902060a020703060608030f0a0f0203072405060409080301050f030109020405150108010603060b0f09011101240e011404091a090a030306 84
    0x50003286101c246103401142814642401e00a0b41800c00100329225441c2650000c8408424815a071103035009900810034940307503083c064211125410b0a07810481d04101900c045030940002900710341d104044410070b11002501071009000a500003584504001042d0f4115036002804100380c9000390f00800603140e8560741140c1d2407040101491500e403050041e04a103e0040080d07041c0745c4a5401928500041a40c1d2131141104440c05052003e10038204850320088600c034156200d40203813030401030040c51f5150005030780414454107101301c84000c0059640c1e14207400142100e036025000b40401e090200401c4101025082c3c054005900000002401c80c82401018202d8620744032507840c003145107100007200d0f880003600c28144154200300812601003482286000209006a0103000c00c1c1205070b40507080321680f0110701d4054030001441860300350003a00d00202c8080310002000c03121b0b071400940c8000031117900480400782404001c1d000b1800304d0341305080c0d0720a0307504004880d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 66202053 1250 66200803 66200809
    0x16050a0309080115120201030b1206040c060306060201231905090c0117040b150127210317180319020d11191716120311070807020f10030c080105 64
    0x185c0318a60248036103d0811016500903401b070441c0c1a80034115407981704200f00f90501d03151044e2002c807161312102c0001c201c400c0e85886040060403d910081c443c0e085290040e000c40e040c40c510007000c50303500c040802e48098500c110186c400210b0201406249410b0441c1911450384c0448280498140c6056440c044002d02200d4459075000f00079545684501e803c241e100c40c000a5801e041c0804241c1c0e014050403490620f070311018a030f096012100c0d0800711f20700d40303410802c41808000b6242c6050307100040d401144001c04d402226507030035085e541d5001410901e0b8600c1840306094000001c3c1e0412010110040758810302a640890305940301c0128104e5026010101e0181a038200c148000c4400040413410312045000300030f24080e82d14020006441540560310000c07544a040221a0801040040c464211412410b0400c80c0b00803400012946104403100105180c1000600c0002c40d80c40321801c5d52003032030141880344119034519018005140000704840070508100c0001541c1c0303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 66203303 1250 66202053 66202091
    0x1503060227010912031b0506102106020904020405040c020313060914040b01020c120c1201050405340b0d05090715030b0117040b1608090a030516050a03090801 70
    0x140040e07440d50345503072078103100c04d40ca0054494100c04100915243c1030114402c2c040c400c0d000c0e4000e20103000355041c082070444940c0e1041e4000849500700190340c1c00e00241c8803590403495900141c0140c1e030381d1141d41c0020028400e9402a50b4072501e48040c0340e40c4c10358000080c0c10840c0580002a04658985d41c056580c281d840c450410030902481c003415031400c09400041e02240103004031240d8a02d03403000a51b8031600b032036150100d9440780480304083d02e0140700030158522128000c11007414035448081d1103a0900503852420582c000004070300e122070b82054481c030480e883d5103d4104c3e840b2030940c0100c1e4400d00301e1004090804012900126011440c00c0885040b0038040138000c0b003081003500545166074100b418046000039000103c88400320007889203103d07410488203440c2028002c4103005111641c070341081440001c04c45a1280000e02c80300a41c0c250510644a00c500c158200f031185030868010124092403440e6010160042d03400c000b521100c00c02400b5151860100c51148 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 66204553 1250 66203303 66203377
    0xf0b130306020a030f110a1209020906010f020304031506050108010506090901050f1206010b0c120a080103080d020705100b1003110d09050304030b01060c121e0807020115030602 78
    0x226050000c0000445036402003100d41080d080118040e02d001003948125100300d8946242d250000418103001d652110320140f0f0410100c03c100a40c00c025008240c41c040020840b606111200154641c034a0080090710010b6a10603810010520071591450242110b81304140c04070707510b10300114061070314500f80c0740b800308003030b0188080c0d038038020030800704103c42929280c12140090700440c04000500a25010703085105080c2d60f1014480500c40c90301d550498040101c0700300780070b5a800c0d180c0c0520315504698204c0c810070744860b00840c80000a02c0b46480042c15840380c01600076809070180c00010441d00704841ca45022200303c2e10075416500c1c0564140d104038010010310110200b298000d006103800b0780b084a04183e02d03507442c40310364202070300440e01003034008000100700008501c0c03680b6003050324034112848402c0d039440140700c0318080030b2020502c501000042d044a02c00d600c041c0b030340c3d0011140001c5c01962420620300a41c0034041e61f00316907010303d8400e01145500700c049400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 66205803 1250 66204553 66204577
    0x90e0105060a031d011d060a0504050303190f0e0f070902030919050c040c021006050301090c03080901121509060f0608160912080306030c0904050303061009051503010f0b 75
    0x5007109a4000f10010700555140071002d084c040c84600d4806024810348848140844001c5032002c0340c03d102c03a203000b0f8000e000c0307001d003410107040200080021041d640c101c1d0940e08035000d40100b400d240d81c05400d0741d80780d0004807480e24070300800d8400001a501d100d4400042901e1360552655600020307031100700c41c0d08034640d0188104001204010340c1c0410101e00603c00e5a20281e4664002015a600410150010ba010b260006c148940078810000180021002003049445990b03c60880000c0341c4006403a0440c0420941c501c1c0e4051904040b07542c1c1248000c001c2804c000d0030f03000d0f0a407058040c8038500c5140c0207012441c804411440c40540b41c19444c0c4683d0759a900711002844a4180302c200200104000001034400140c008144110700c92401540c0b285841400d01d440c02c00b810547e00e02c40c0314460240008a0380110440390418003da69064500c00340712400c0d95441f820b0760201b41c00c11440c10742140da180359840614141c1c0c9010035550042c541d22000e000a5018885c41e04070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 66207053 1250 66205803 66205807
    0xe090402030c0f0f04060602060105120c010c03050a0e10030204140d0c0b0702220b0f040504030c03052208060a05090f0304180b06031303030633110609030703090e010506 75
    0x703501d181c48072040a01d100010034004c0e0b606150030210b81030720816030200380980e12040040c00340d46003098030b84c940c800940380184000d1100c1d800003002100880005428072400180c0100614800c80f480040302c00c0c050004e11084c42100001002540603201c0c2c05c01c022514400b40340145442405a25080d40041c00b83c1443c508290740c0034000c3e800706800320380c00140b5020a0905101220300c0143e0601000c10025414502c0f0003449030310910f40110b144100e03e02002c100000303810448605c03244ae0103290141c0c642c00000c034120811562520740c1c0c885268061070006404500140c20303441611050700500440e180c1d821081e40c0d0b441480c000f1000c503082800305120080c43c1499045c04615074a4003c00e601500d42d000c04c0c140c0d4000c0e13507030b0f101d0304004080380d00905030940500e000034042c40710030304401c4043e010180d080034500b4103111000e01e000300803404042d1140301d01d0400b40c4c9441d426140702d4244418079940e01d6004030001c6012039202c02000079100c2d14414400c0c126100540014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 66208303 1250 66207053 66207073
    0x40507060302120a0c0203070c0e011a0c0303070f053f01050d0b040609060504030c260d0e03040e1f0914150411030108070306050c0c0d050705070b03160e09040203 72
    0x10016000c40449070701144014461940810340c09c110000c000c03c103001c0c60351100e504003d281416001c10211242601c9410040d00000c03000c0001269402a02c501d0141d1002d039800e0303c100c1d803a128002c0302140314040080402010717229107800c100140c03c58085891401e5040c01d90b00481d403000d201c0c20f50700005682110b40825003451665510903c680000146504ea50361040200c1c0c0c0c0a030f40a07400295100603c004001501001800d018410048804060030b0107009a400d8410146010303142d50325401c41400c0510700304203680140440103152505d502d40010a2103540144141d944080400c0c100c0c001401102481240c0c0040311000d40c004107641c41a0031000d00100c10304100741c01130358842181c404100c200300550301130003520000d080765a14609003401501d8018100c01e00e042000c0025465101002403140700c1801541419a290309640c140a820000c4607400416000c0300001000b02080781880c070a4983d51854540039291200d42003440005d00701194000c0d015803101c9480 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 66209553 1250 66208303 66208321
    0x60308040b1312030e03060603060103022803080c01051b0a02060103060506030a0203070312090806010b12040510050c1c05040c03080f0d0e0c0406080a05060c0a090302061204050706030212 83
    0x50461900030408200c029a940f001020302c03110043c03058000540c1c20303d0307201c0107240c20702802c0e820140841c02008154159000620341528100d07e40441542412604c0442185204840300440d000700c1d1480e124200d106915000c3c240494415288160012a0701d204c0404042543d800c0000b99000f0606a0f0940c1e0b905070040c5400340003650305224801d4600d005a8080203070038055031040c1603665004c1e00c2034001502c03100d980d1300b00080b40d070072050040c013800c4000c02c144c907000e034140300710b001c1c9a40303890030110b0924103031a65240c1e006060104211484400b4801006e40300d981900c1021000346400e80300301211400d450080c078514034110100040307154080034190034484001e0303007403422500f911440700b229078011440455400c4518114164a0540b088500401ca00c5024080d40c880556686403642c200400c503907100c0101142041c0000d12898050014640c0509030b00da441d8050211002402e408490840c0c841c46130704070100b01c0510a00030350b21000c141c02c018001c240c442c4070b04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 66210803 1250 66209553 66209557
    0x20606030a1502030c040b03070909050115020a02060f16030e100e10030c02010b130501030203010b03011e050709030c0306140601180e04080706140403020c100503060f0a0512030405040f060308040b 87
    0x2680c170034142c0510010402c2c000010081d8051600341d00d07030403000e52030020500b09540381603012035560301285000d004600d80115100100c1941242d480381d55028842021803a4001d107075103010900010b0703408508154001071080d400b40c0c5e045440305130780d03400303240704a90401e4a52800f03074014584c0c80080f461140a5080344030402c0190002103942e003504404075241c2c0704c4c403040b080e2039103882d02300400075810b007845000c3c0f0ba05400da00a1000f84017a454a88509041c2101c00310090ba907000001c2e012449401180302a40e80b220b00806407e41e0f908080d4060480198420420040440861050b47c0103100c1010944200b140340b15059183c07120444032390740000c0058403160b03000c1001c040060761511803100303145e05900ca0050b8900f040d0070024580310083c5d0740103004001c2140c2514a550f000020b60380d00040c121401d08043d4030840c0842d10508079a130000d500841d2004c4843d1140002002400603520305940411101400154190580d0100c0c40054080c160812050050140407c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 66212053 1250 66210803 66210811
    0x60e060910050309103303170f040308030c07150504031b0501020405092e05090a0c02011e0606030c140403080f0c0a1101081e070503070201090b090607020606030a150203 75
    0x10075111702031001c00380d1070203a910030120142c00117001e6103402c3d00f88800e2010103845880c1314080c1e40403a070966560b890141a0442912440e030710200300c0608007071140c01200c0107141e000782525140d081c10010a50650421402191030240c1010a00001005841402d2146406a507444401e20030034000034502d810406044c0c0307030755400700404501a00c46516060281e494820140c103034102180c83d80d00c0c1c1d540e120841140726482c0000400040d65035842c5142c10400b00c0500251154013104168014440000c140109602c1d150a03090845800e03400310044036101d44080c042c514503440100d50104050340007404203a018081807010401f00b0015210f2081c1c2d0714640c40c50140c0b1005424542b0030310020403940c2c0d843c5411441f00380c0d680190001e800a1140343c0c02150b0411980ca58904054000c103614200a0080005080300c2d2003504044640c54018080c4540b82c101908034945841d01119000d01510504002ca0380600703000546481050b040b24202894200c48420403001c2d61000d8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 66213303 1250 66212053 66212071
    0x30303231902041703120108031c020a05222408040602030403020f0a0b1509010303050d0f0f060f05040c0c03050304110109030c0801020309011118060717070c060e0609100503 77
    0x200021800b0041801100c840c508100d00841e101d21040151b07145502d8160410002600309000243c0e000107064454a48d030108201c007d80c46035500f20007103409011b070198030482a1045500b08918035400c8480505440e180f40070b06095640c00703031014074081e00740d241d0500090098400240451095809583c10901c2441621128a0751042e42c1d450a8001c881c15181d0f02401c07801e110f03421300803102140d5803070015a120302c040e41c51524050322900413440d075104280d03216030240d480c00846900001c050040072004201d441d40310100c060b50313401240500c40c080d9142540805465001d20b111031200c1d6810f54505107103903100c2d61201d19003003000046505004010001000180310803010384090041400016203914000700144d081d600d004d0b140b4015a0010003c4008031485ca02184090102c183d0b00f040e6a07403100c4c640bc00c0d03140441c0b11088002200403614404012000ea8014111401a034480b001029400100144d5126003030030700758001800d0008000c1e1030f0150b0050b5a0200c4c8035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 66214553 1250 66213303 66213307
    0xf05070512030403020609070e10060809010e030307030c12150b0f09090a09051507020607050c160605040f0902040e06090402030a02030f0106080709150e0402030703170301030303231902 82
    0x18961150340040c3d80860140e08080c00b004064203080201500a01200f0112501804d00322610040c0039214080c5004004030540000c038080700940121601c40c2c0d0300c0040301d68034600780301c004000b0840743c1420800500c4050440034181708070701a5101110280783c520007078a291201c3d40080f640500001309401e50305024130280b0741d503440341d0107219580d0340501050300080c40c40c1c4181031440031142100142d10031814800031702da0000304258016414200702c0d503203800c0d4468107468a80c540c0100300410320060f9001ca040c0c0c5e80a00034008441c81e03014035030015505e030070302601170307001c1c90080c1d007521f01c0d21038001440c3d8505003500d9504103001800707036501e24459401181c03e00d20408000005070f0b44841d010844a40e00f00b10740720062035042000c0001c010112603a1104c9081440740545a00030070303001c602550350500000d0015984840b603141006000c4a140303c0382e400905c400e5002c00c0c600095054000011420700c1c2c0c03103012000c01d981c0c0a81d5101301415112401082140c196682 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 66215803 1250 66214553 66214573
    0x3060b12130f060c0305150d23070b0c0703060501080a03050a0305060f1206060a05030a03091205031911010c090503030a080403051903020903060a0b090403110111030106180b03070f050705 83
    0xa52050040311130060703801091078a403220700c01500910345a0382c43d000c3c441d1980a00e020410002840003001604c48809a6440204c240d851501040790000c00c100701001890200500c40090810201ca220b200b0901150381d8500038070362110070009010b00800d50410a0584d00c1e40b113640119446034000f4407520441d1600d80c0032130a28280310002414076800442400403234034012000c03000401c411002401400c23400d980042ca160640c2c1b1900e409202c03040389800c01c1080c02c0c41030782d4008140503506641411251402031950a0044201005500c0c03c20340d110103600c140348010980740080c004500d8000c58440865040e40020020740030050103124040e4101100300c14000d650340559009600e44442508150a01b103001c2c054440c410718050303940b0819200d024019510a13058140382202040111140e405481c008a0181070b20000000101e45e00d07030090588200c51070364644030801640c480304000003521040d52903502049240141c450103500c210014028244a28155504144 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 66217053 1250 66215803 66215813
    0x309070f0308310e0907030602070302060123060f09010210020d0207030206060414061309050307030305040b1311060705030c0105010308030f150616060e070e0703060b12130f 77
    0x80580c2080300c20314000600844040002d1016201d0250488030103800c1031a80c1c0e820000600140c0b2031038080780c241c040040d0f0041c5c1d040c0300181c02160411001d564a0340b4070f04c0c0c0203403922001d01aa80c45102c2c8109520701c40702c40b000d11800041d5001e0034071403a080000c48a40340310b4004011040c1144912801d684451040380060140c41240500141e25103100303180190400700010714141c041c600d0f10901101405018a40c190003200540d0045800c1030b9504400b006455220300c0900140300003e40c00c1c040680c141d01c80d9218502070301440b000380d1a140002c980350a072210000e880e1060f80300240036586041c0009009491085089a1070000381c02c0b43d980c00c1d10401d0740140c0d2141004020002502d44085100b07501840540300c01c00e214029500055003409840c684201840b508089407041044907482111442c2d440b8088600d1165140000b902d1900115130303240c0040d0500800140030343c0b030a0141c0341d500d80c1144216481c2c1d0355054040582e4114031005903042403c00403a080822 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 66218303 1250 66217053 66217079
    0x8030d020d0b19180e070905040203031204050a0606050102030a0e0f12070b030a1b0504030b0711031206010216080712030c0803090309010e06040b070b09010204051305090601080105040f08030907 86
    0x700c411030380c84809113410180c1d08052100d40084070002d040010b03008203074401040e00c20545441c404001036036259030021a01e0f41c050110444001c00a040501090040000317031012030074443c160911800d9100c01c01241c43e402001600030202c1da200903802e450340b60410f04021000f00140154030030300c6618400515140c52540021208240041433200c9448180a0f4040e502d807400290481c1d84564040100300344520311000e49112000b2000c245010720400c000a41d0000308000c6a03220002c401c2072000c0c22905803001409441040304803841d0702d00400c40b14003141c65410180440d1031404c18038403a2540360003411400c2142401032a40050103003000b03140102d2075100151b031215248000903001030030f0110500e02c00c00051004120700c0d220841110002d41d0b020219401035118211402e000e0300907a0081c543c030000c4200c0b0070340724006552055129140b107204843c00c690380c44d0452400c80b0400e032000741441d1041f894034030102d880c900045070040e801204540303d03542d030b402c0007135088 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 66219553 1250 66218303 66218329
    0x1090e0601060c082b092303030403050403060b0112020a081512120d02070c080a0b010506250f020402040909030810140114090414040b070201060b250503030705030f09030408030d020d0b 82
    0x101e0224640850600c0403074280c14803107030007d0021861800c0c03940780030b002c601076440000c2002e0703211403000a0316445040c50440210a6550940d00d8020700c0001070300511048600240034600e0440c245e04503d498412481000c00f000e02405042d2040358503604254010054103a0039a0204550300018248410110003000d994002e0f196007850ba14000b1442e20041e88032920559092001002004030740e04424000c0710742c001120350a020718600400b040c0d000520107940b0074808103002400145170f400001c0e00a12175516407189544070f000c00050400103009001d0302c03805440403001d0a5001301044401c00305c1488006041c01d4500000030265551a008045009000c1c4280030400c1000c003da10303009150b600003409000e040420310101401405411100248455514810100700031001c9400b59041401d80e5035a2a110002920990068030304118040030b01d00000c0035008088140d8065403070800c0030b076182c0b05898105202035005140d280144a69a00540289035540d00280c0c0300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 66220803 1250 66219553 66219563
    0x902010f0309030e18090601080a030831031e0c11010507021c03021c1704020910090609060602160303080613020c060a1506030908040e09031201090e0601060c082b09 73
    0x5846d02c17807041401c129041e80b10043e10341c48212302400103a04170003c1ba42c803a6200c00b0048004540c2c9030400c4200009440e9403c184a41041c52001c3c0342c0e01400c050042020312428080207003074038004031040004040044c100403a51003900d082584548003c00e07100340010b04d0fa0760740c070400e2081e04080b84030300f00d400c4001d0792141141900d246004030300f2020044d814200b41e054a803140249108940b00100000d1080800300000351080e165402c414010708038031340c0d00f00501da440d42401002030200e030060202520039504403000740407440340d900d42580c0d0b150360b0300102d0340c650405200c00042082c00c501441c680034011125500000c1000a1003490b4890380865014104018040d003150181c101e18105414101e16070045107016044608855042800e284035544401e0301c2030641c00340700c000022071310402e0000608228a5045000705060100503510b059a9074070041d5482420450300800c080f10a1010801d0f42149542000f2640820740d6681c2e12403003983c8031003040b580604411a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 66222053 1250 66220803 66220849
    0x120a0206010311150904110d090303240b04140a0510030507031a010f1431090204050a05060d0e070605040f050d02030c060304060b06030a090b0a0902010f0309030e 72
    0x14851442c0c124030381030006854064001041e4413030440107100c0c011459005c0e0b6120480c6403d0508040215540b106500f0000c01c40702440340f40080c050001285100d0307010320904444810740c0c011101da02d0440d42018086840c152500b418000c6900354109502d0344001c040100041c0750f04d0302907030010100e1882c1c1c1d0020700e034504031501900b00d4005440b102d8422101070340b11083d41c1d802064841e50420b5505040d400300510640c480d4180c8503500f500e0542015440861050703039441800100302544103492041d8154480a11900706d000f2445220390046030350108024504103400240300d07864002d5008105000b10300d0550745064096480100014800181000303440d5020484001404044906601c000700a0700001d03512450420320b80c0c81110004089001c01c60030f540003070300307200c0c001c1d0005881c0d183c8441c03004000c10039014180d40318110000040c0e040081031052a40e4980c2c161a10461800449030071401099007000480900c4a0902c181080d99202d82c2d085464440541c80360b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 66223303 1250 66222053 66222059
    0x605010501080907030203030306060d06030f05010903110307020f09071205150307060c02060f03250507020a090c02060f0705040f0b07140703081e0409020310080d090521120a020601 80
    0x141002c00040076810290461841440107941c003000b103e0300000c080310026210500100184014141580020480040340007000c0800c5019004004401d0013521982144204c1000c515120f106541c0d00035800002804181411b1801810850300322441e80f501100c0c211010003403000300c40d010384108401d044e04102c0101c0d24641042610f019240314a02102c8a0081e0790204130349000d00740541c03004007400300020f00c0c00140d0750009507422880f401050303c52040304c2c801502a9000a100b42d00424818a0102c0c1d000c415008500d0400c0a9600034026540c4202d020381071180301804100402031b041200054841d216088a03015000401440d0364441203031400d818044030b07101b1150740744d4210b05410000f04c1d1002c8143d80c400656084009040415000c0002d1944115002102200e1011051000303840c0032440c0d0300240c9002408407038455692107411780704c2c15554070805911441c080a600c0c1074841030300502c541c100d001c89c215074841d00900302c414080d4002c0390800300140d0220b4010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 66224553 1250 66223303 66223307
    0xe040807080f450d0f08070602041a030106050a030902010e040905030d1a06030705161505090f120703030b041418070e15010e030a060e1605180708090a050303040605010501 76
    0x140c0d41030302a000c2e90060148000f6908151411110f102d0f030b110313500b040c0807241441005440da00501c0c0d072003520f866071a40300d40f074030000a40150141c1d240d080421000d00e001c0d4030001041b241030704d1540d12818204000300d402200031b0070700107804a041088282c018229a1200d0081c24140341c8148051510b0704002c1c2c81c5502140c04408005070300c110450300b0072040c0c2d12444200c1e500800c1624102c2d5440075460080c0c190344110740c00042070045980300031094400b10f940140d000c0c8404600340c0d07120304c8100c0b0080d80c2c4c40307032850040207500004210b9040040c0c0298004250108050400304e00c44220207a1038812050031603903d07400001b440296480303004180490f001500100b07880c03080c5414880781402e000180074400c40c1c1440620900300c0840da030104110404264095010711403c50280201c9894035000075100441600d60396010a5600d021208502042200c400100d055902c608003180c8556002c1c0c002a0503006140e4481b0214000b03200851150340641c0000c00c03d94504000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 66225803 1250 66224553 66224617
    0x20102040314010b0f0904031412090d031401050d0203210a080708010b0d0c02010209030a060f0b030102090f0613030501090305040e0c161202120706060504060e010e040807080f 78
    0x40040184d25002a800056a03206051244980300351054003d41d9107d140641701c0812035001c04801020103d2802101c1d455010b209214087d0302c3c00759500325580031816000c1c0c1c0c40400a4080076140707800148030b1800d00c00f0203c50031301c3c0000c00702c646101d08150301520b10036040c2c0c10035000c440001103000190350023004270340e08000d041c80c0130b248540c0340c0320f1118441d010f0001d5200956031100f60f440310880c400d4059584205004068441c01600c524080c40148a02c2d084101500e0501011080520b418401d8034000c40e03024001c030414607140c908011783d0303511544030107088a03030503000400421030034440c2c001c1079031194440c142c0d030b24140800090f0b02c4a005090511a400411060359407440200c42000456400300c24001504218601a801c06016414854079411701181c1382083c400b00341c2040d41200c20585003082103030b0f01e407960101280f01c240075070024200e80320042000580203034004e015881c01115100c1c203000000c4111501030b801022900408001703456280040784520308 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 66227053 1250 66225803 66225833
    0xb0309030711060f03061908060f01050307080f06040206130b03040317220f0c15020601031202030405060a11070306230c03070c060b030703050102040f0f05010504050a1419060201020403 82
    0x1404901307045440302080e409200040419026021245007114400640e000300c0000c0c0c0032801c2625210f2030800a14080a402440f035644079224080e00011004004520f038242e0300d800c500607201d16501c0e9000c2c4201c66021011000310203508510002d0444082c1d800345d406103100e84d803501031402c51405004d0f88100041c00c200614a0a4162289100002103801e505075500440c2d0030110261030404000760300c41c550121161000140300b0100340d582c0486c6c070314140d03803041485044c031203d032000481c0c0c1c0e4043d50003201c0c0c00000c104014078200e40141c0360407181074416402c491300d20b030701c0c1c4d5034074000d40b80c41c4007500002200901504902c0c942525507180d104a1450b459401d6141c03c90000f49210701001d40a002d080d5141740c00f640e10707201400328802942d04503000350340e43da6845a400d1180f82c0b03144581c4c80000401c203808107403584214200c0c1c0440b64020309085203039090a0f403140c140800641072030780c40002905031200c010382201080c4000d0807581c00044e10303646142095842084040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 66228303 1250 66227053 66227059
    0x180308340507080c010e0909010f050c0a0201061505030c180a09020703030c0815101209080301030b0f04080315040b1002031309060308030a05090a0602070605072717070b0309030711 80
    0x41c4842111740d0b8028000003806d5001c85150071551511224a801861090b140c40c2c4e020341042c0170481e041c2c6400f8001c03d40c06038140d00802c0b40503030703c018001544101d200c4141c00500e040000c40c41011990002d82210030520042002420b01400080d1149015610618070385402003988403c3c142c16100c1d0001d204d2640c14151200d103800c40c4e520130f080c0404203000788281000108080407134400c1403c5a0708200c1c01c2c008004040040c04d0010107a0400d00c01180c03050114400100380c84c203002c900c1802258403103213687c03c40d12800303002d408040c502880e05400c50b0f6102541c42440c1d031a845101e40c40b51594028655035583d401442124105540041c464141410310402c001101042180d0b88079441003400100c40d20351a03190760034104907a6011b803800c0c0c00840d80c1818050543d0040d4003410654940320304c200d08440b02070401464074400f05000d0204201c0400c00c2d0383c0c0c1c60040c0340b404000700d01511062a295552201d2982043e52028002c1d88007082007010049040080b000e270280c12 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 66229553 1250 66228303 66228313
    0x2010207080610060f0e030604060c0521010f080d02061306091a1008010204080c04020307050403022e030b010c03031a0307080c120a0203101e0501090b090718030834050708 76
    0x100003203a513808c030103400102829540c181c00c1094600ca50203903004001c0d5204031400c0c11003c0e04102d403005500b8007030b00da5036414221002036582000600300194100761380140c586595400da5000007060a0711040e0f0724140c4030041c5000041c1f44183d4416404624131840d01681400600f005802281d90003000050784100801d2041407030009140d2201c0c80100d0b005079407503031184801c071080c0c0100e40c8029044640c24071510000380c00081440d1843c0d0300320504a02001600204400303503040f0003c0c2501045480343c015021034426000a9a0107503103001004403240751902092a101d00380d40f14614507080100000710f14a0310011002c000504a4001c0c0903501d01500003903142c1c5c464503104040c490760b444110020b102000780069099000200800640da56900224090040507480d98400c41c180e40020354528000c0704a6588440c154248501e0340d07085d41c0d10b2815a0b4041311075001ca0010b4228100c5050b60940d00710760303801a140007190500001803a00a2401c20f168200140e15006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 66230803 1250 66229553 66229577
    0x10801060e04020c030d0e070801151215111c0e06010302150310050a0e04020f12060a020708090303030109060305070b0a0f030f0b030f0303060f04050912030402010207080610060f 79
    0x300c40700740030600700201d80043c0e890030300a81552952043c120324070101130070400741c01d00d101d41c0402c1081c1119580030080c09403a4820f41400784d0710019018a401c02c110348032004012139418842840540079a500000311604003c42c10081078000c00000c580391040d4100140c4040e14500610b2500d01c0207030007c089035411a80018200003000a4900ea5120007000182d03d84c0c11a412950060a01030903032800681c50340c0320740c841c9410883c3c0582c0180403105085480d400d280c90681098136a03134000cad100540352041503e020390f00c011804d44203481d003801880080e0742c040c40110700038104a2000640f6501c1c0d494200e0030040301c0e43c0216801e100911006d66000e42055900400c1d46040c0350000d10442805050001020111300040c0c2500c5040640c0012980010086000c1c51085a40e9624000d4103002c02040d01d00460b031541c56900000081c001051514001e5500184140141e40c003c03034454103510f103031060450701c1c00d0724003130322103003c000050700701d94100b8101c02c9903e40407042e80c1e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 66232053 1250 66230803 66230807
    0x20904050423121603090f120b060603070e060306030109080d05010321080103022b03031508010c1205070c020d0609020103050a05010302220615020105010f050102070302180604110c0a1101080106 86
    0x440f005042d4103101c02c00b81c203003018824a070140c05800d020340e1543c80305445803030700c1120078923038101119400a2800801c07503510300700342500d12800c91940c4040c00c1454820500509400242c4074503095900ea18170000068a02d0020380340c141c0303c1d10b500240300e41c034600308031030200030310420000f440c8010f05a480c003d5603c0520241580d1701559080403034600a2001ca40c0280381080c000c44404200303109208144d8140c1108410030700090b150078005171103220f000d080702e403a40041c201107804807101314409011074009907813003503090900050121070f0740c0214004000714102110b1840d99014028119a018031410f9005507018108010544c11a03000c01d00d28182e450f000791600320325034800715090050382c001c2400380c40040c00f035031110502d00b0350280c0a0700080c002d483c1c28001900c00030645520006054040f250000c003c0207014181c031248202031400a88000d4015466000100804103a080200350301086000100b030b8940031401e050301c80116208060b41044842001049500e03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 66233303 1250 66232053 66232057
    0x16060c0302070b24040e030306040615021b03070801140901050709050d140c1f140304051f0609022b0509030d0b0a030507080f07080303130f02010302090405042312 72
    0x5007103403110341500010700d00303200c4c00d681403141d51a07401820108880540c44011010f076015001c1540c00b40304150300c6828a001d811178100d40440103034400c0003d280314000380c1c07240160140c4e001d0140c80d45c6607103440105080d100c00702180008006041c09001847c0401d204050340725040d85170804e039403820300000410020307001d0380140007a481c400a00744418414800f020040360f0040900900e20310741c0400a003642c1301446c042c80400d6900c00c0e8204c1c00c00320740c4200e0740b0503944840a4440914a08034203502030240c401c203240c4441c0d03550804201c00d5a244000e00300420b504001e007407581e02c0030411180002d9a41c0c1006140e600745018420301150001c207460802e411a0b101203091108840401d180e200342c0c0d0300240c190310410f00002540070340490084c0b9514000c0007070b15030903500c41c4000c940c0d03480180c40b0380c515880124000008141240c061050483c814540036103071140c0c04000a01b641c0081e01d05690480b44800980d140c0005007160911b101c48050151101700b16103001c0c81003034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 66234553 1250 66233303 66233311
    0x309060906020c060901170f0613110d050c0403050106090501090b0414070e0402090a0306050106080c040602070e0406140f060f010201180f020411030403030c090e0114010c05011116060c0302070b 86
    0x201340105030300031140c0c02061141c05060819064100500d004228012404000c0d40c032140030b80c0c4164429413451105000c0d201c100b0010004a525103101c03c040003009150013401d10700351050500c00880010001e004d140c00600130880049101d5040030907800884050700e42c5070384904e24142042c00d10039003c010180e400241410803206040440340031402038403640c1c400650040d540030020041180591080703040c1c0d2055540c01c030302543c840c051840e1a1046009181c0580d001c14420000c08034801d51842d801841440c005c03074841c032250301c0c150002c175081c0ca502c48207604034030401c009c0341440c03400000b075104240300a002c165a0100701c0080d074407941030040e03c10000000400190b440e0342c0c10540b48881c1e4101c00580e241b502e820020003c0c01c0a28044000944513400002c0c0449c4481c0c40700c0c1030301c03080e582d5000c9001c1004015100c48103000d0048825540381c04501e880f0001643c05411135052041c04050980c02620b03104003110304545589003410b01c1070051703c001c10b4070180c800d544 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 66235803 1250 66234553 66234559
    0x201c060b0303040503010c03050108070605030603070e1f0603090506070f0f0e030307080f0a0e03010b061b0705031903080a11041505040302090a020705060601090e060103150b0c0105040309060906020c 88
    0x8028040c0400d05500c1590003858266082c1140f81c401568590b210741d0484a038101070391002900d40004079091301c4182c4240d94143d001d000c043c049990301c2110181c00418407810240d0081e80c001182034001400d0f030004020030743e1030340c0c16420b2100c03c0c82060390040e50752501c2c0341c0e43e040c1044041d0450180701003500c2045043c4100318403c0e1420811954074540215000341c450545011031246a0701800742100094090744050110b42414003440380301305001482c10382480310360307003544d41c0200d60512143d207a448cd0030346c0002c01d91418401e100340d11003a012101075400706c5040281142c5c002802c00510545000d08403480950640155002c0e00c030040030007101960441c504441c01d0280d9000690320480c90b40c20300040c403000368000d2184521030019183d03070f550744800654841c0304c1880b609400103180b0b00003501e198030a610004107185d03404400c010709501c0c0c0310041c41e42c0c0c22600402415a644000b07020038140c2051040008205626060141500f8004004d4031891501c1c2e040d40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 66237053 1250 66235803 66235811
    0x603061d0c0307060f05120f161b06020a1709031e160f03050f030108011a0301020c0c090a06030b040803062409010302071a04050a06050108010605060f0703020703020d201c06 77
    0x50f852159084403103800185032143c016003001c1c458000c101e081070394500c01c00340c00d1710900f0081a001d90b02d001e02500ad0060700c20700010954603600d010350b000e82010010003865040da94070141d040519240211031900046880760f2020018601881c030f65203564084d04001c0c80301e02916030607085c070f074000305901c800b01050b900a145000d860074010404042c844402c0440085000c1c00c0540c440c01c5902000714410601c00400d0701454200c1c4103007540320311260003c11900841d030502d03810098101c21064070000e410382d41c90b200c0003005801a10304031031221000040c0145450800c00f410f20754030070401c02a071564803507501c1050501c0b51544840c145034000c01c034402840a1809403100b00c07055201c01c0012480d2502e0055204c2c202c0341011a10580340c0f03000440c0e86001445184242d0b0405130040c1d07d0a030042040e1400c41d046400c0403000c5110300c601c0400180c40310041600400d214600c04d4911080fa40c25128a0400c1c07080500d02840d0000980002005003803502066150400340c001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 66238303 1250 66237053 66237077
    0x2031e0a08090f13050402030d0f021e07080709021b0c011b02060d09110a09060605090409060b0d0c0e0c09010f080a090507120605150607120306090603061d0c030706 73
    0x9038100f0368803481140c4c894420120009150764541019100e180308a0646011102079142680e900801c03940c01c0d401039110381100c04c64902e64a1400d44040c610b40200d035995a80d900980b8a010196040b014501e82c01040400c02c0015021a0710014900640038050b90b02c60000001c2c042020003a06c1d50223050010500d0095440e02030484078040304224003440010107a041c252440c80241c8000c2d801003019407400a4003010340c0c483c850584041e96150340c6000c124000300006090040e20075148580d440321105426505d2895109602d4400ea8800900c64904810000c0341c40c00204581c21002c1c00300300c10301e0f80d60b80c000703090f003900086414144000c0e10b42001e41d000515110310b004100b4415100e002c108042c400402c0040c06114400611160307841c3c142c061001d645450700340341c00a00a1181d0000103807a004c1c242c1d44030340545030000e1445e42d10941c0700c0690b112070740241c0b90349980b28070b074203289003c54000d0048400e040c002010b25a8000c40480c2d9501c0d0203114060070003624402039 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 66239553 1250 66238303 66238309
    0xd03080c0405030a030306210b0720030a09030c15020a02060d020903120310120209060d080d05010b04030209060d150f0902060712030c020610031709040f05010302031e0a0809 77
    0x52005800060104d400c45032192030042c008001e14000e50a580c2042c4034602c01c0302d041d05005840503907000808071416114540b06603070760140b20120b070000001c015103940e503800042028000c100c0c520303031340c0200c0c007072031070034440d140c1203079070300031403101c42101d88081c664a8002620034450760381178840c079035070710414101c440080c0150f00740302d40e060240d82a0703000e51511180c040d5010b65448840248115035418081e800c03660003c4000350000b41d944001000342c03030300c56811400385005103000c52500f542c405030102104c001b40c200c0700140c00e011405106500708410604e61241c0c060714440716103511034503443e80f120a25800c000516464042c0b01c00303859038540000c4002d90b170142140d601c6c0e0a451610400f0840d01002c61070020f446c203021101400d1001400030702441c04030348442e10580c2581c441010100e225080c0fa1700c01901008603020a4480384144c80f503000b803800000515505520400d410b1110210b200d940c001c2e601020003081f0790011504900496111140555a5031041c001c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 66240803 1250 66239553 66239557
    0x16020109090f0b01030b040c021e16030b070906030509030306130f020723030a05030a0b0409150507080702010e030a080402210307030305060117010905040c030219060801050604050d03080c 83
    0x200071082420014a4066040a600b080350107140903203082c07101072411005e0000b00c401802c07580d00103a04c40c514050100345d5107000700d5250350300c1d1000d4500030800040310301c7c00d00c2100d50081b500c0d001c0c50300402401c0c135400761040014100d240303010b110608182140558038080a40024864020607140500440c6290702005140000480c01d5489041c1800c2042a00b00351880000080c221465040305000020003201d80c0001b4584842e81141c40e1401d035203005041c40d40403036400a907560314034400b1442a4844502c04585904045000d2410341c200a001c1e1784080c2184c0256810005031040301d14010040e00c003801c0091529070555522030001642c040002c041280c0c1c102034150f00c0540418021000300003460207038a080c05913840f480300460b07003900c440003660a80d4080c400140217420850300b101d9040360040c03900410f0261070f40c00044001d20100d00c3e400c802c550710141040385541001c0d246004100460b00c081c10b00c6e28083c04240c070300c503079101c00070300704040480010f40110300101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 66242053 1250 66240803 66240809
    0x3050901020a0b09101a03070b070809090a0b0102010c110303010b1c05130b010e0103030e06210f01050f09040206040e0c071403030a140402031b01020a0f061506020706020316020109 80
    0x240091070300b007441c5401d172100040040192800c1c10559100c14105a1070110307101000043e0092111502c1e01070b000120390080d000803605d030311007040303141c81d9546e03200805401000d25500024440840034006821554a000c0c3c1406201e4440b8001040c100e002c810307a81100d85050385039035a4079078554080010b0181c0041090242d103032909120162003001005481c0600ca40004040c0340d07250f0041960403a003d101c0200040c028030025003c41c01c10001420400286200d041d445040344d080d8035000f14000c540c44030805c08110010031092a00c100c07110b0146408dc0c4006109007000e0700452082c0c0304071b001f110480e00450300811400010082103e03c020b8102c0c1c1040001045102c455450340d105807011901a0b04062050350070755505071090340102d034000c000703011020142041105410358200403a0541c0912003042011030b04500903aa4242d114100c00507584010081102491903d0380000c0704550145c4024000c098000041329031003000b2400124801d060b5100403201c0300c1c4a90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 66243303 1250 66242053 66242063
    0x30613140f0a11040c02060f0109020a0c050307030c02040501050d050a0b040311030d0501090b010305060102100e030f0424110615060702040908180f010c0201120b040606080702010b0603011203050901020a 90
    0x40c2c0600103214018001140000044809024540d0394444c200d980d154242e40c0160340040c00b0004119140c01680100428001030600d4055104641c5851381540c00090059020440e202c640008504d0540b050902510040b10302c50ae440b40e490f10303040d95a01514400418980d080c44c0401d003414000c8846a100341e0042c0c0459546141c160800005400207104202c00030341040c0705440103601900480d4480c1c40181d001b4204246083d584402070000c0c55221700300c902041140c0b0181e000010f0040003e409041c80d00000e0a40d480c8905208804022a9004103d0001c0f05d4021001000c508a42c0000160302e628409007503010002e80c4d907200c1c645000b0750161038022101d04122520000d00030304a130586a030452001440248004480700400507400200a007074803600560055101320340001c0048000520a205100840c0441d842c54100802098084042000c0c1c1903090144080500b804e5400c05c0c15035151544070009a68038040040c2440804501408140d100b0032429404076008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 66244553 1250 66243303 66243313
    0x5090f040e030a030c020c0612040c0510051c0203040c05091005180609072f010608010e03030402090c0403020a060f020c030607030507020f0106030519050307240605030613140f 78
    0x88001582d2540003404050100c2d09040d0749074020b50012400452000002c0c01d074524080c0449050001c480c8000c008807800140c4a00101e060703201c2c0e080082c2d074501c0c240c03501d40e41d400c5a01802e941049a21850841150041007048000f515018a540444600351207030100c98866400740c803611040c03a0007143e0441d0202d40340c0e500c0b490701111414024030b011b480342c40301c9072900041101c03c0d1805603103051440e60302100f00100301d80301241d0207802a5495000280491711074440d982500c01100f0034a18541c4044207200641c40c0000c5015000403078000d000b45005d1669010070742d2186070307201c2c0c0020303c010306003c1c01d8024000c0c000642003070001019551149010ba4006e4014841621004014403400c62108404401485031000b0b82e6000001800f403000710018440031400c1504040310240401d0005400040d20301c0c00c00410102c44440c540040008128a14103c42c0e40d0b40c4200c1c8280e00010a004203006400803800d400e43c1c000032000800120075041515094224111340020b10030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 66245803 1250 66244553 66244571
    0xc031c02090a0603020a021b03070302090a02040603050c0a1403040204020d0510030c0b0a0504030204110f130602160302010c030e010306050d0b0a0f09120806031204090c11011b05090f04 82
    0x6554010542181c08558446401c0d80f0307488101c00700c0c014180d0a6015034054034501c1c000540c09010900c480038020304880b001030701d03903001c1110a0302c01d4400c03401498000c641405010740601a1a038060b0026980d142081e0000070300400c0c2d15aa06809280a400000401c00350345640c0c0446000c0407a02405200506260307040922a4a252006582c00d8a4074803000c03c104610404482402070a541c810341803d085408000c010311004020f100903810070404040701746625000347c40c01c04411540da202651505c0400f900f400c040d06c800e489a81440002403005030380113014107800a80503c0e0060343d1100c0880160300902c000d8003d070f640800f1600d101d0040080ca141707000c0c0b0a082d9500217014100b0740d0b07104041550680e05004000704070070100b54402c1440f0f02e490030f034411b5004040b51040c0603418401e00c0c035548990041c0640c6034403001100009600110341261922440340208088194083d21180340c4400804d08000c102001859410903580d0031323004d15801400500c10002c00c59 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 66247053 1250 66245803 66245857
    0x9051e07110708031c0203090c041b020c090105060304080a09030206180a0e09120309120a030605100f091a0c07060224041112030c01060305030d2a03020c03 69
    0x20590303100440342c45a10300201d006100482650940da00d030400007182e09652040c800c4c080d400003000c0c840a4450a02e1100042c0e80f02c0c05002c0c0d28500007000c1201e0359a110400a085c111500d100340d0050043c2c000400c03540e103d00301160360240e04249a1500e419910b0011180310300d1030383c4040e62008010401307100079020030504401002007110104021a519269603c098034115100d0000da00041078855200c90404011a070010f0407a05654882c025600490346ca500518480400242d9500c0288290b09200c60507121040403800d040f00e102c83e010400030541042401035421400c0a280d10034040207404080c0e800d10b00350707401991401c0f901c03001d00030350f24100300b4496001d1100c0381000c4c0b441c0a8080b4403460003207801070780c0001300c24141824800c1b080d000d50204541c40c402003107103840f281402c2c8034400141d032040c005503588841403030f14142a14040414134040d9031a510b00d0014140d8020340c1d04100c80c15604003d6140e0f048030040504602030f0000c06800035010000303105480c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 66248303 1250 66247053 66247067
    0x901050106030e1603030525050c0406080307020a150c020411360405040812130201020d020c010e09091e070320060313080c010606030915051009051e07 67
    0x240320359400c0010100901d0f00907610342e03040d03a0080c908000d42e401440131902c1070001f000f8454035080c2e503031a03d000d10006103400c0c04a0160a0780c55401c1440560030721f1915014a4000f0700e040b0000310f0030115550002a841d800c44c0c81041c500412811044250f00d001d424840d4400303400510403c1203418200d00f0440903030000340e19440f8003030741355882c005c030021055202d036041c0464000341c80807842d000248001084042c000380d42c070110910420514449404110f8030412017202c2003001d500e400d10029180c1502c202500003550025120110b040e64001032004004008550200b0740351540850075080c5046c030740f144d00f0038841659014081c4400098594201c9100e1001080a00d0801e010007101c0c55902220f1640142e080002c02d000c1040e61410100039406010881e1605000c64005802c440e0700c4d6008802190b1105030030b00074060a8800c801c0e80441e420400d00240c60005000d110400481c00340711001c550300c1010840180703034815000c4031880068a1700d10036003814040a080c2ca = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 66249553 1250 66248303 66248309
    0x705010213050607081c061203111204180203060f030a03081504020301030b060103020d1401061d0f0904030f17130209180304050f0117011706070c05060f071709010501 74
    0x2107981060002880d052020803a02c21541003001d0b1424612040700d1454070010b01482c0b00d00140d114080403c607529101580c0c00030350f120341c030f5603801900701440181c201240c5205452034054140000c102001e1010804030800c11005401a942c2d603800000880040d1550a45030b09880707849801400c141c0c00c031416500a10b844010104450501001c0006a10003400001c004610365004950254029005042906c0003100081065480c2082d0120390038000d03442100040c9114000810b452185a800c480807041a503d04400560000201d079000798050001810002d0403052903540c944506031080b0000b8050708480c007e4200071341052a032500f8072105078030800040e408182294952505101d507040c3e81c1303025600b000d1a2104003d1850303405e4000c98184440d80d020310384801c0c0c648000e94060511003851280c2031701072614441c41d0410090500040c4042c51280c0300105100040083e40034001611b040c1007540c44000c11121041030380e0f040d1505901d000284000b60006402440c16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 66250803 1250 66249553 66249577
    0x151a0f0d02040e18030901030b0d020415090b04021e03101205031209010b1806010c150606020d080c0909041716031b0809040203040303020f0304081306090e0a050a0b030307050102 79
    0x544800b44c06043c00040c0542d01203195108000b1042154000e400640501c5001404054040050780205041c2c6140c50300061010060604c203002c00141ca2040500342d8009880450030a1400d844042c020070310742c40b40b003041d401d0100001da900a9109100c1024080b0b40403018031041c0c0da89407207a960b0b0811030a0302d0340750000f400003440616051103100405000101a07102014150250f448400b101a014504104006800368003080403000005444c03021581d000404500d40000242050350320fa2810003001940414017950070603900a90b08824001c4403c035149443c0d903d4031840700100914103801d90350001c9006000f030b0075072504034980350740a42c996205d652251418210710720400e580080500c030040c002c610407810a54040c6520912038180145810000c8200c014030b50030444007201e45610006100ca420814200b0540083c0401d0504540060500f40c0c1021403003401026103c07a590b07580002500390030590044108020b0140a8980d00d80c41da080090107540300d04080700e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 66252053 1250 66250803 66250829
    0x12030412031406040c0302130305060f090303011a1309060608190b0303041a0c0106030503040602010e010209010509011d0603070c0204050f0402010f050a0315180c03151a0f0d0204 79
    0x8540d0300034015884641061010307403040d50355403001c1100400701e40b0b0f5107004240e82032020074124401c240c04c004c043d60143e0014841840c00110005d00010300402076501a007040c001005600483e03032001c0e40580e01c4003401d80d1107103c122680b106441c0103a010309481c81c2001c90000f03000350801222401110718034817008040b00c00010210584640704100e5406500c200030421a10000b21a204060815844101c2c80c103036001380400d00b07480e43ea4200340e819030400681002950b030244a4403420341c5180b00258149007841d80042c149000341d80100d03040c0400c4408643c401c00540070081c0034240c0003080103489007480c0d40e005080c02000c4000b01d0080707107800041010410b000182038400d40d816520002d2442405000702c4654020780390440a040e110003901940140d000850000b900740030340d8161420414204000130b84801500b440d003810b28203a58000400c2c9903c801d0015140303045415182e911644000d6410341c03003074541691581001144e1440d421649400070800c65402404540c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 66253303 1250 66252053 66252083
    0x10801050601020c0f0402090409060207080309161208070501020d060608160302070c03030e0d1509021f020a02240d02070201020d18030210090b0a0207051c03090e0c0705120304 78
    0x60b0391800b8050145900510080845c482490582c000b00003826001d0004515801584e66600590300034850031503405a01004114001000708480e621440b90141ca9084092815480b80c030b0003000c000b40902001e90008001c2c1c2400000d40460309102ca040008200160b03035140d00800c1d41006403041504d11044030078120001d0f109000391018950090b1750404040d1941e50141c1f24201c0f140760b40354102420321a40000b00f200b0b40c48900c020b2004e4240071450381414070401c814a50b0300260400b2060031038103600303807490b80003c1d1021002e80c1501e9405160b40d459002c0b0204500000304c05241e8000002d12000751602c580181c42214800e0702158580340040c0b00c2500c40350030b4032410600c4200d1208041001d8601b82c103000c40401802c2c109240d000c1c0c3c455510089551141e00600d002d640400e03410850fa04010680c1000d42a2000c103071845400f6580c0c00400c501911702c9503040003441d05d40800c125035401c0080381c80c0c450b4001e04550f4209881502c294041d00112402e039030100901c0924 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 66254553 1250 66253303 66253307
    0x5010906030212160c080f21010b0d0f0f0903020718050c070f032f070e010b0d05060f0a0f0807080c0a03140c090a0b031b0303090d050f1203010801050601 68
    0x14410490000700c002e8207544d03d1810462520040c0c80b416010007080602c40c3c4080740030000100701a0480500c603d54425144115180c10340b803e41000440816110040044041150546100001c45207000c034000c010042c225018151810559803540d150460b00d6080540000750b802c2180c003012411010007606503682c100b00d49045441c9040b41604000440c0000c81800c000d1403441c1c440d04008412000100c86030000b504818515403410700d401501200d161801c100c80d400510055906510070740c104480080240a0194401c400300c0c0c6401c00314105554052400d00100c4014180c2100c0c075680c0d90b038404004c4414400d10b141c0b8011504049001c41022401c1c04001101800740000c0d2481d5030303900c0c00c180c031030303829011207a0181e040300d0007640d030301e0010700344c0241c541005c04a190480c2600b0140ac0401900c0c1c002d1140407400d00380405514040241e6010b620b04507640c018801c1d440c01d00504080c40303a1340c2e80f038290140c4102622070078440800f0394142e4040c40020400f650305c1c0401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 66255803 1250 66254553 66254557
    0x30b010809061005010f03060911030103110a050a060c0f0206030a0b090f060a05101e021b030102070b04080307050705030a02010203070e0306040c1503151502150c030a0f090209090106050109060302 87
    0x43e1280b0445414042c080d40d40188191485581c0e54507000800a94808a19040b01c030b49801c19483d842d40000104240103d10000e4404484100c61960a07145007400080442000d403085030244a6180c80d50b0051005000b4083e1840343c005d8580c55032442d0001099008041190754503119940c036801148810301e82e4000c00e0710034400a00411100c0d400d00342000146580401ca2500300a02ea5400495140744e88800403104941500205034104610309800350030740c00311509030701a07031042c41032801040c60100c030300b0f4001d50030005840d5261218401200d0070b104080c4060410311000035540302981c0d0545c021403146100396202c5100c41584010541c440c14103039400740020381101800d10010a130742840190303144840c14001b03003c007000c801c2c07080384101941c07140d00741d40c5029041d2100c2540510042c84001e207000142550391800c0000c1449900025207505079090f03030f034681410a04030580c000c1480e160028140d036074510300002c00ea030203412680200c900040c138801c00015001d0103402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 66257053 1250 66255803 66255811
    0x61e1f08010b031303030914011e05070f020618031201030308091005040305030711010e0f0709050601050a020d031107021309021318020913020402040305160f0302011409120607030b01080906 84
    0x250f880c0c518131468801300c019281400c020368640c0c1c408402d2843d905c0c0c091280400210428140002c1c00c05140d428004641d801070001d01482030b014a4220004d901182c3d89512a0702e00c0310b04004103a0740c0068a240d0f0003900210302048000000101c145a0010b202e41c0c440c262507002c49021410211a42c42611400c2c2e50003030110300c061012401c02402010f85a484010403000020140c52042040e0714100d0424604003203508294000e112010b407a000d00c6d5803207407081c24600c0c0380001c0400c0c0203540e02d240c01265010140c1e00d103619112025a00200c03610b8a40080920619018080070079009006010342203114100082c400c1e00b1161850150940d0541c00c03820311002ea85e0302d0340030b20840701002001c1000c2c40381e190b00e001005960340d20251001d940a803000f05202c240c0c0b241005408a07188d006241001200541000140e03405404507203201035000280d91600a41d00c0420b1141c42d40e0910085503008690401180507032640c132811181c142641c903007c094894107031154458200b5a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 66258303 1250 66257053 66257071
    0x51326160b0a03020912061603050a060f060f0201020432031b0d1401090303050103020a0e09030a2010020c0706050f04121704030c030c0815061e1f08010b03 69
    0x1201d140d540c02c0c081d0307000e000f417031001404036000c5007922041e071800c0c240201c2d90500000308184202c05202e5262081c01d80c02051207200b00180380c00c00c00201203508041c0b050204005582c01d65420041c07003034058400400e03201d030b044d1251250a244213402c00d18142440380c11540b14120b0030b0728074900000e0001032101007811031000c80550009100041003044010780c2d40c2444030304801c1c00031100f48240d204190007690005000c1d41580b04121811100d94481040480002c0612403a150b010044803541011401e0940300d40103000203030740014500c0043c071045402042008405a01c090b0024410700700c905054510140d140e80060703c1e14020050350944c00701c030900080c40700800300010344c00c6090180380300025109144810040d10382c0300342c10865903040d00c0c00081040000b081c1c42c110141c029a03024007181c210141500c80404001401030380b2440c0350790400381c002d403404100c5461220000d00302d09040152a91040c01ca040b0700d0040d0800242118000542c1c0c65005090380d000d28014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 66259553 1250 66258303 66258307
    0x3081b090906190f0308190c0503090f0f09130605010611070e04031b050102090108011202030606010804030e06041d0603010c0804060902041d010b0f0a0f06051326160b 74
    0x2c50248141c0d40d1100c00c9800c1c40082d100400700342410414108801540715070b0013555a01c46540305000841d00d42d10001041c4003821600c2c0001440c00b1068034185502503c8000c0a03081910001c0c182001503e00280c110140b282441880c000984030004c095004003001e100c166600d45d0100e070307010324880e500c41050f0000302c2c05000a290038081640c109020b494904124403081c01e4800b6082900d60040750240c0d0300043d001d2855800c00080760041c15001c81c100e250407481c1d0042a01d5920090040c1e040140c1800082d0805001b20900f10208802501d80c1c0e032910303201c4c070901c1c10049420540f5080103d0b02000161245014042d9188003101d0360703a0000300380c495a036031002801d0707803000480e030094461552030044a10709101640c9000c5400020810100410a000e186003689201c1c81c00f9504415051050700f0b07022107050111003903803409031f030358002035000740c41e80c4280ea801541e0b0201004000b00c0513003403104c2c0c0b4800048400030686403082c02c00c00003a2014043d1f4030401c43d2034401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 66260803 1250 66259553 66259561
    0x6071101391407151206050130020c010209041407091802090301020f03010501030f1109060c030f16050d020f0d0804140703200a050a0b0903070e0403081b0909 70
    0x10401c51500030500c01d144041c14420309611540c20030300c450304041c2d07582c4c1010110891265020b0300700341504807202c1e001c00ca05428140020000601c010440c41880c030440450002000440900440c240807144c0c02c54603440c00b01c0340c1c140030358052482c1510460600d41c000d92107010351450300d4082e60554880340c42851a2045282200c04042612802103600f031003c8041c41e02c081c0000d255400c4d14000455880d07040c800094211011504240c440d03500d0301c64903084042211085880d2081c2c100c4450303440c1e10628440604d103119445034803403a4007012802000103074543c4a101071044c854000c2c0c0d8a81150650103d80d0340c94081006004c1d64009002c0070705c0c01d0702030840301d038005028460105507201440c0b0310b10b2402c00c40e50710840304942034890002182584281190302c1d820203c038050429403070500000c0152100380502c5103800f4001601c1103940d901000054000c090b090582410b529003810301610600d0201c03034500a5955070340d440d0070103460b094100c0c0c20b01b4000604802164603 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 66262053 1250 66260803 66260897
    0xb0a061503110901180e070c03110309010e06030901021b0c01092102190e090f0105060f0303030115031b110d030623010203040803040f050301060e010f0603020705030906071101 78
    0x1444c0c6403400c1c05c102e0800b000b00c1c00d8103005010754420780203500c480d4401c0500380307002081400643e071340f178280c1d4006201e20300060384d01045802d50003804443c0725403603880f0345005900911401c0092244000300e00d1081f2000c003004222001c0340d0b402600c49128645d13032401c41004030345c4400441c100c00b6040c840400010324084403600107000c50700811081081c1c40d100c1125990300d096404428a030b2003900c29000184090081640c0300d10290791209400521502290756804180907140d2401031503000310060718408d61160200322402c0d9200304811481ea04086c1c01d0408201181e5545d0161404c0c0340c001500078000e040448182c4e80000c0341c988903440494210045000003c0d0460004000005282004102407c09081c0940000806628040c01c250840350540e1014800f41144401040b09035021400501110303424140541c3d40c0e0000c0c584141940b282d559007642c070000c04503225060004906440450400c02e0322140768407880749400c54404024a4100402009183c1e04002c00039 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 66263303 1250 66262053 66262067
    0x10c0b09010906050403051e16060e0a051204031e02090406231f0e01060807110109080406090501030f11090d020406090504050625050906090d0b0a061503110901 71
    0x601480009100c14050b603070785060704d07000d0310143d00182000c900c40e1034600c02007200400003019541c03810714005424000c14440340e10000083c3c08255a41c500c1d020106040c051090b105501100380c4200300c08000d1203d40c89d40050005480f200b00d0020540400507580c2e1039103203a1a0000c007410841d41c0c0c1c80e030b11480a840c1c8860302070740207031805d241d154042007070f003005501403001c00002803003640c001e00a25840c121b080d44032a112480b001e004011080d0403c0282d6000784d454507000c0b440304031107081d281c0500740103000109083c3c00010001225a8060f11280545000340e0300ac0c080c5500f020003500a440410a800711452070810242969181c40c0049000c05840a800030884903501d030302d41c004a41080718240c0701c54015030208198620100050709640e824020322007061175913410010101e001c1e000c00307a40514000145e20416a03240e1454202281d0b0001c51180c0340d00c1c0090785440500130b41d102d1403912140c1c00341681d600350f010f8003c425946c0c1d03100102c2030411407a103004603045 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 66264553 1250 66263303 66263311
    0x215010e070914010e0d061a0108251704030503010512160513141302120304080705061b06070e241602120d030507090603050403020604031d040e010b1806010c0b 71
    0x121041504d4021a0b441b0303102c452159070f010f9030000525025081a18881c0c2c05c1c1405540d040042c1c130810884003141c40050795071031001c406103d0000c104140c0c07050b03036a81c0340a001c0301e000344261001c010805d513005c4003c43c1625030948202142d4245480700d180d0b50005140308091081031342c9010300080c205091841c0701c0000c80f10010403111644400b91010702805d07203030504220809203000043d4180515a610303e1031280c001940782c545024110754076488a03000e058420240020180030090340900f5500610740c2d9503069901506240b036002e40640a00340c3c840d4020700b019540c1c81c01d640c0040c07000c916000d06244a2a02c1e0003c041e8000c2009025132000726407145908100903c4060100700e01c03000e0540f692000a482d080444015106c004c0650240f0100340c02d150420001030360209040e0381203603060074100c1c85400901180c1c264440c0307260807550440c1c5424019890500305410408a42c3c1040c0c801c2c020a840641c03c541c1c00190445120340030034a0b041460b00000c00c809016a84 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 66265803 1250 66264553 66264557
    0x30203032a040321081b1804020a0e01230901050304080f0c0307060e0111090f0d060c020d03060806010602070501230706020408012d091b03030215010e07091401 71
    0x40c1c4031400c20314910701d07002500241d407440c0301c40300803140701e00c505200021000d06908003400180703802415a28101400030314520783c0e440105071440500700310b51342c44030001c00040040d502d4403202c410042c22114a000c03040e000540c003441c4550b10410000c8410201d5030904011407901c01e0300c0c00103491030351018000b2542d040c41000b50072403040010340900401c8035690090341c2e5440740350401d5002d40e910040d000c0306692400c440e0120400c0024100c0780a500300740d8034503004102031000100043c0c000c4c9400303440a81052080b001e42507001c20300907a0b46540d03031130800645896000b00d036541c1d4001d00484000d0303400b01d03070140610343c06040c52a488500351044000003144440000e02260444101100c01036004101844031410a010f0304408400304008208103801d88a09425510300c24a0700701c003059a900801c6040c0181d000d008001403001c120b0a04006a484c0341c02541d071840840e091084401c0c0c1000811041a01c0d03081c01c0c09884076640c0d03804001d0030406c031107007040b40d8942c003541 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 66267053 1250 66265803 66265861
    0x604090305092e090b0405010305040809091503191115040f0608010303110a0302120310050409051501050d0c15110f01060602010c170c0306030114040b0703060608010303020303 78
    0x70306540c44065403690050f81d03e200b101080c480104040094010111000500c5504403041c07080c042508240e504030340c801d02c3d01084035100c40c00d0071111842500e1081d904843c0000c108054410503142e101c0224505804590a4040716150b021400400c8031f4020032952041d096420341e482d00540310301a504403168010b203481c0d9100750701d6881e0308595000c07501049004004101340350308082000010417400018010080540e0740c000d45603030707205084218888001c0041404004a8020400608070252081004246074141541c0d1451480c3d0708161211320170f000441c06052000d0440c0010f680a1601d000c800d08221030f6060024058040740100450a010500210302c10040c4101c0f50301c1c0b8400000d880350070480002d0a46e800c1d01b003000c0a1002035196102c280e28043c04042c1e010280d4220a80c40b910703600300203400f610000c05000038007040c01c002d22052002d0b2148650041000361020002255102002e840340c910034030001e130140e001800040c0c00200f00144003010310020081e402 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 66268303 1250 66267053 66267067
    0x100c0308062205060609130912030203090d12060f1412031309020901020102070c060f03050c1603030207060e0102030403110f0c010f0806030a150f0506030111040302130f020f0a030b0d08030604090305 88
    0x18501d007c2d900304400f801503e580716141400040d103540c2c19440b09518040d0728510340b49003002e640b0742c030340c8903800c00300485403001c03403000451944120041c0c03119a01c00e28640d6030b120b11103095120034205c410b1040a100c02800c06070b4800008858400d84c68803d290030f1246040400c60080d0040c40d11a81595001c00100340003442c2d00380309502921013600d603001d001911a4000382200c0004000c540c150004200140308440f0308401c1f900e0259142c540540e03032f4281441c3c2000900144da650b44202d40c004000d000801d60800d510007102a00001100d0164201c03d080c103a0314400020501c0c0070401c0c0b1510001c8492040003150386c8000040c00701e41074002e141d56501005264008a44401c0c0e940d00b10014ac01446401001d0700003e04800a01c080070401c50301c0c2c1d009106510000744074240025003240ad10b07021303411018101f94640b00c01c64885031282c5450602e544480e0001d030009192540d4500c662410100c50b5500540041200d42103a42c1c5c0000e02004040056090b800d201c4107110384 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 66269553 1250 66268303 66268309
    0x90109050d0f02130c080a0515150417070303021507080c0313050a12020106120b1612020d02070201030f0507080a0b01050702040e07090b0a12060b040b100c0308062205060609 77
    0x80c01c803095028134002010060444006c25100c0080c1c06050204c1c24281402000400000c00300703021507040312880090403080c81440d00798030540d0710102440682400c0c07c00c0401d800300d0580100d034001d0f007e0300d06154502c0b1591000781d0046031440d0201d040e80020805e1121228041c42c0c0c4244401011003400e038070741d200c107854840060740c21900d11400c2e500c00c0d02d095a0a0240c540245100705039100344001c01c3c0e4450700300c10750007408440150042c144403205248a1480740007104d4041038110340d550340b4031007404040d41c00380c00261701103418a00000860ae0441c0b2400b84261290342d140c00c89510b80541510107451103210b154100f080c107000d84000340e80c580c40740c0c10900300114010030b0014039200040b015071310f00c904c0b00381c8141116001001580d400484442d0740990000e400200700491030002801440001c0f2055041001c59a48507580341c3c00608440285010f611580010b58511040207104401c005800e043c20b04010030000020441d908101e070071000061200b0b04004900000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 66270803 1250 66269553 66269569
    0x507030905160f08010c1d0102150403050c061b0912070504020409050a0c0f0c111c0b07080f010501090306020d061a190804020f0907090306060902090114090109050d0f02 75
    0x590300360b654003260070000720124150410082007404028002d41c1c041181c090200c0d0444c0c1030080600c08050365001550f03100b4800100700c100c42c004010102c1c10207040040890b0410049241c452080c140803400904007411120200e07003690010a00d0700c80402d007400216240d031031404240b071042120101300355465002400c05020b444400280300d140074a143c00c10f58008020308800d00042004103048241c0c0480212560f07500850390103468020040400d44001119403514201220300c2010001c00400380c4d102401802e880e507071a035564030f914001c0c0d04914000c1c4600b5000c10401c241c10000543d40340c000d0860805400c0c0c4c0001c009549110525644a4416410828400000b0305800303081441480329005042072608018a1501d50b010444910784c1803c202d12401d150740c005401e9a11842d920809107a0103542800785507078500c2ca54020f5001f2248080c0405c50078014140d1141410b8161000448c050b50303203c0340203141100b44003445843e034105403104214003000744003586500308 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 66272053 1250 66270803 66270823
    0x5030c0a0302070906081e150c0703020606151902030f0c010e070b0a050f0306042c07140a0312110d08062b021507021e01080906010b0d0507030905 65
    0x1521400309180380c000d04006081d0081c0905602d0118180a8070070300258680d00042c04250540c0d400070b8040040d480c00000b000a2810b501c00c900c1000360b42d01c0180d002d0200c041c4070303800b111110b448401c104807030b03da18518045800b2601b0302402140808408a0034444001d50041d02d107082001c102c612001d501403212030210703a444e40c2800b9104c082c02c001d07078001801006407041c02d0082c0f202c07008105104113001c0c0b0040d1200440418911307a540e5001d0540e51000e41004101c480303000020600080a03034000d980389000300300001038041c1d10b00e400e003031109000801558a6a046940700540c0d00030502c2c43e0380821503c00f0083d41811070802c00500924450b45442d40140b0f0f202c001c1103000407018000103080d030503801c1c140300080b2248030417044030380c0d0480f1881e890bd0302c0880c96001c41d008812000c1d50221444c00d84000012071001c06003030f071000a98803014150742d5900f84c260b8070b40c1e00b0301c04c0702d940f0340c820090f20201c000598403542c2c2014051030046074020141d00d810340f420103844 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 66273303 1250 66272053 66272077
    0xa08031306060b090312040b03010326071b06050a0804150b0a03030804060b0a0303020327060f040305010501080102030402010f0c0c0b0c030327100218030d05030108100203040f020d020103090503 86
    0x4c80b140e65203420030031003602c044c1e8030700d805241034140382c0b03418081c0c001844000c10411402c1c0b02c1a04240744540400a04202480203a07250b801e641080703542c40c6900c40c004c0360b20305068503001c14000d1041d02110008880d507119504c03180c0300c0b07a650540d5020140d400204066a84080c1c1700d190391402941030040d0300035035400201e810541084400c1310b90000d80d59201303425801e410000030307402105075010b60043d0002c480314802c1c90b030000b103440000b60742410340c062000500041290541c5014000b52070007100204070b00d07a21401c986080b0300c410b45002e0b02003080d54290040f4640314070010a1102c0c85000700a0601c1c1e035403400e040da0b03a04580501002c1c0e0b080481041075400611020560201882c0148855200e0354501c003070b110f80d1540c0700e418400d030b00000c0d0640f21031070155170410a118003404448684a411800070407035082030203210412b0040318145104036a844c000e0f00e02898110002048410880d400c1108400c0a510204e0502d91100a201c01203007045c809400800004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 66274553 1250 66273303 66273307
    0x200606010c031103131d0105180606180301060b0403060e0120030c041e0311030c13111606060f0f0b03010612090506070207080c010206010b190c0807050307060506060307020a08031306060b 83
    0x1b1800c0000c41070050f00400c0c041c0c107141800c031101e2805040c5203600188140c8141c1d95804404603242c42c5114102e2201d40c05d5030030082d00080034180c0b0402403080303e018507003c01001c0c11242ca103900740c514000d911110a046aa001a2004011001103801032f180c10012881c0c036907102000084400090f170842d0100710380800801c01d110050b21446a1000b00300c001e0b00d95544494000350f540030309064000c084079030f00c6400b4100000c1130421a0741040144000101c500890300d080f0010341064050310303800c00802c000000f01458606c400c4d000351100c021500d4116030802008640300800308400f00c0043d502c504101c4049903040c00b105004d18610b81c0038001d12070410300071034078102d411003d150441d03011100402c88a036501c42a106143c175041d59400c030000c0009000c82e0380c40c04404000d49400f40000d20350080080000007040d005100c0c010a200c10b82d504c2c020400c4c40d0008170b0781d00b8096086900410000340085005541c8143d038050500c003202c00d0358941e0012184a07030040f5080307903c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 66275803 1250 66274553 66274589
    0x613090207060506092e12050601030c0501020f120304060f02071401050105010e010203041202011e02010515180406050705040b0d0605090c09152107200606010c03110313 75
    0xb540c01072a51002044c1d400038401c0c03d081c400105248600d600c04140d02d55918100c400d0100074600301c074024021042042c040c0b04460400707070386a210a100484040b10340010002d920350001c51004600f289400103080082000d10f020040c65000074400c80305140d49103030342d4081681902c0500700c2035000c0d1034211200e80c0d0110000c4e0031a001038021505205100030381180b00da0b400400c450a131130de49074031580519913620040e42ea80d205a2526a00c103403801541d907030600d07070550019216928121681e80400103141c2440100401d0b1840c064500b0784a000082c04210b030b9800260b00300ba0545030141c5000d07030b5003c901c01c0f1500030050b40324085c0e40320b010030040d038074148001d1504610b1100c5114a006901d00000303400c2500311402846540f400b1609070b284280680f250302008401c900814081e1034404401420303d902c071000c08208003904100c1c1490b8880000f0074610618042e19400b100000c1501d09031003842410340301071035501c410820704504081000c084401820000410307500d400c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 66277053 1250 66275803 66275813
    0x9020d02091003060f0302060c0f0d050a080c09090c0a020a0203030a030b190f051302090415031515050d061b09050901090b010c1502130b0a03060602030c030307030b0613090207 78
    0x302c0c400d00ba08040c02d0200c01d02c68641c14441e8402140d9046900c956101e5094099600b8209482c40d04419405078010030b03954036030813400500880b00340e66241c0142d550f0350386545005004040d00903400014403400504440c007400c1c01000d013407240340112980d45100c5d0340042d02d9603100000c07041c0040c4d198100004079003020144002d40d40c18140d9210b0b101410034440b41d000a046200e80c520a602012400d400c481a81c2c6c111042c8020240043c0303c1300c001300300380789504038051000b240c51034180741c400d5040c0e505502c1820340d84802100808010391410003003000000c0d458005071282d5643d06001494069203001040c00759949440e2100340c9440c06040050100c8160f201804240c100311007040c041c0ea02c807a90410b403ea000d200c10f01d119000442a0009011300340194002c9010b10f0400301c1c0301c0460301c02500b5058495601800714074cc40d02e5040703840c1d010701d1155810680c0700f400885c6106000c0d40124000c0b00c0b01911080c01e0480b005800060109554404880c0a500081020901c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 66278303 1250 66277053 66277069
    0x40516060206040f06021c050103060903080f06011d0a09020c100605031207020103051302031506040b01111b1f0c0203070906030f061d01110c06010f06080103140709020d0209 77
    0x19640098a8149003603203400c804200710301340040c40035500041e004036540d0b2040c0b0840400d040c50790200429a12071429000501107484c09401042c3c0402c00a4011707a12000918420001a91140304030350156251115000b0781c004016841202e200012070749240030310140c9014a10341000b030a00c4c00c0411220000c550403030300014041d40020185a038a0040300085414042c3d080c82c00003901e03038071824500b0b0713a0100010029410700035501720714048000600c029001c1c8204441c104002040d92006494480c50300c05500080c1c2c11151800c2448107441e1070614000102610050b22040c0810003503130789040c1040d0420100c1e02d0301e41c4500960800708403e1010b1b01011104020450030f54403420030540000ca00241001d0302d4a54009581d5071512044c1401c1076004020f0101c2c50640e220803031240c00460200c42140f103204000107400070081104402c40b0785e0340e02c1e000020b07401c6840e00002c0d1000c54145403a40d2041720350015107030303806100400565801403401611080070f101002a46 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 66279553 1250 66278303 66278309
    0x7020a05030706050304031d04020c030a02011d0c12010b04020a1806080114090403020106050a0807050108060603011a030a090b07170a05160e030a0206040306020918090a0f0218040516 81
    0x282c2c0c4004000c1c041c140e000000c5a8000d901414070070041c541c569200030380e02000e00031054010380041840f511a140000241c0b0319061035400903c03803d5207504140c0401c01c01d0000714815580150920700341420042030001000c100c0b40000300d22545a40d001c1026a48601c91072400101144582c3c070304406042c0c1c61001030100d5107000d01103549000c43d212006050031105a1242210300c0220f81018001d6218000412000d40640402d0359a2a1030981b500040c0c460703603000c0b40c60340340042ea291400c40e08032410307260811b01040322800c1d0003964003241c3c1c10003890022502d0360303680c101d0003141104441601c100c51aa541079103005000d030000000900240007810008d050809100c090344c1140b460000a00051410400b0702c0c07180c0001920784072101402a41000d400a408414010307181c0082000802c1500c600f02041d0200c81c00c0d42c424642140c0a14081c1c002d002480c00249202044d802e0b410300041110286410310f00d11004280010740b011545640003101039603c0c3c0b545001d1140c01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 66280803 1250 66279553 66279559
    0x6020f04260d03110909010e0907090612030c02010504080709050105010314090601060503060112060b0a030e03071a101d07030605040606020c0402030403020f0d0c050c060412170412050307020a05 86
    0xc0c80c81da168801c1c1c0d4441da03200c0c8900906484285480710030200d0030035982410002050008603596403804c1050080b016541c55039140a086004102040135000d04002c0350110010348006103010f4404403580d1304050001ca042010410000443c00410409040900b51445000501307525080c0050110380041346d17405400c43d44a402c010b00c417800401c3d210b044030240e00303185642e039545000488141c8044c842d0340c030075180381c50804607044040302c010b84458520703900c04010386140396030301c1586c0340148480107102410345000540d10b400c81c03d805a41010201400da802036490b0681d04110800c500100c213810150b00c01040384565060050300000c0c9029a000c10000c0d0070040001e440d001d0750300340180600e4000011800305403003000328805250040081c1d82c0b070581d110307800500388083d10905503064801ca00724800d9619156088034111014001c45200102c0a5542e2000041080d441e065600ea402d1000252501d03181c2142c601e1540b04001850f5074400354810407030095825000540 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 66282053 1250 66280803 66280859
    0x102070317090a180513080a0f03020f0705010e0706020307150908070f030f0e0a21110d14210406030c0207030b0c040905180a150902060a050a0807030902100302090d06020f04 77
    0x21400c0c6004070703181c444235840c020510350030303040e07081d40a4404c041c0700040808000800506200040d8030080daa00d0340b80301950b02141d80c8240490b620301864101030041101e035075a882480e40d00d81c0c04a00410311542c0242d003080c0c501c3d1540302003484480d000303502080500c400342d11748a5104601c10000142143d00002003030415900e40718051070040a52000c01601810030300f40800441c0400014a00038500c07105c0044603d04840c600759440d4460840e80701d00000410860240711284100091540b40380e41800d18007803049006e032200038414020340c0101c02010011480e8881c1c40f40c424465500034079515840c0c0300c0014101c40004000801444420800011501c00400c60300008e64100f41c4a1201c010b00c3c452450050404840084d800840021011035040d0414040c0000100382c0c1c4801c40f540d07503010015400d548412000942c42103075021480065030081d4064080d000b00904440340e4601c050b82c440d42281c1c8240c05241c40c11101090800c80d10b148151034034032101010469030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 66283303 1250 66282053 66282091
    0x90103050901091101200703121407050a08070609120305090c010e0306070305041a07020105060f030c030c0411040e0a0f230f0402040b03030a090509150102070317090a1805 76
    0x1c0c1d0858894540d13035040044811100b4510300c0440c8a201c0da40080100f80d0701c8081d0b403403030014a024000d9014501265203c280c11189010400a45440343e4110024141d00d01c40b903500c60b00ea940c0119800c6074141c1d528640c02c00400e0040310450030102a54500044904044c402c45203071560f203d0031b06c0d0401080000d004500d44010030440c1c0c0000081c00e0110309a1250305c1d21201070310040c4c24105500308003004000c0c1042d415005180264020707991800b0344410f040516854441139500d0580541c0301d40303404589400e15900004130b400c3c40c0c079841c0f81029141c0c2c0328064801019207050300710079101c82c0c44d054038048502c00c4082241030322280400c6070080f090110201800280400700454180000501703640341c43d000901c644030000e060340e5660440341d40103450000c0324011075005200040000e000c07098613600840e01944142c0051030b0b214590741d1200341e20b108140500717145050620078406103850301100d44029040303040c1d0300140700c0444044c000440d0001491080c07886403d890794 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 66284553 1250 66283303 66283313
    0x1a0603010e100213080604080711100509011d040e0c03010c09050a03030c0201020c0402030414100605031f0b030a080309190c050405100302090a0c091e0e040c03050106030809010305090109 83
    0x158014160b1601e02507202e40e01c504920500f04440d41c0824001c0c041d2034200400c004007007004107452807085140b0003842c44a86c0130701c0400500303d0024408540c0802522800f580104801c401080000095100e0000264046016a03440c03c18200c0c01e03501c990b070071909500e020301442e202e106151500c019050315040c001880d0000d81e100140c00e001c0360361441002d41e4401d10011864420140082d55603051074a8031041c541c0d041c030799403031040c0a01c40b10b62140e8110ba000d844100c0c0e1008000b00700e0741610352503040140b0314445401c01d841d40d0755404600951014004000745a015a8046413246006848141000015000403107038000080750b000000b000a00e030141911010f90f40090705076107006400070891100d0300065032143c40b01c01000700c40c102c29000421b107000c40e55104841d003590307414080810280c1c4a055188090031440a10540316000f503220381c410300462144207220355036110142140d1080d0000d07111000001509042560580034107038200e200c03003001304903001c4107842c0c1d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 66285803 1250 66284553 66284563
    0x70801030210020102040b030709140907020706030f0609050c130f1d04081303140115050d080f071401050a051f030303110705100603022103041a070f1a0603010e 71
    0x2000748914070016981188074404d6064074040d01030094648d5484c203014402a144103c14840e0341a002c085440b400c1c054140896500d004504030f80041c0360290411806401910300e001200f1450366442c0000149280c5c00c1c0a0103008048038546181d854503000422024441c2c5500b000900120540c07080181c1c2c801c61584040480c004c1000d1001034a91f45090000303842400d090200080d481c0c140842440407254a4800b1402c1000c000c2105400c0403078520012519482620740c80030000500b800441d100c003004000040c02c50b09600e01e804010740c6e500151341041c0c0603400705070b9074a1007007100d6002644140c60304100946841c01001003561015016000a40002010903440d4044000c100c1a1881544c5c0715a80c82003d841c00d011050200c02d0040401388000e9110b005000407810502070b0f10041c540070100d02901840c0340a042030013401c002050104241d40040c4200810401304803440382e0f0203036041c8200200107000310414201c0441d010060080d610a0345002c178040c004440001c1c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 66287053 1250 66285803 66285809
    0x3080a0306081f15030b091507030b0603130c0506030a061503050c16060b060c011b030203070f140d09050a0606080102030903071b0b0a02071707061b0f0c060c050f06070801 76
    0x44045a050b003643c213a00364410540d440203000214210500c10309100116405c80e8031703a21072681c0003980e92443d01c114181c580b442e01c2590004070410200f10b11744801901c50a03500d000d02d012030b07480e60b07803100030030340ca640100c1304c0c040d002d0766800c0f00344100b90000c000c8030040380c0180743c2804541407880e0680142d101b1404000009280d1201030020000c40c3d400041001c84020100b5072110214150300d4060624450241c4035112074951140030b2900920990b806900c07503943d8041c110702c09841c01e039007004c40c000080c11402814498030042440d5402080705091203000941032100842c607058040e80d60581050806134010700030007600320b1001080c1c42d000d54120146083c1d1600700711012241e02c881c0d811900c0b12300c2c0b00040b60110550009840c40458040c074040081e464100c001e295241c0fa014098200002d08001c001c2050543c4280d001003810700446c12403425000c2540ca064848a4540c45103010442c14596902881014407520400e000326401903c414540004d00902144d4140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 66288303 1250 66287053 66287113
    0x81b04021908060d06020409020703020123061201020408010f0207030e030a0201052703190b0f01060f08090309030f061b03060a4a060105070b160302070b0103080a030608 75
    0x80024030f855036010b00c2601c059030456400c40d90707540c6490086006c0e50040409030003641c00d203600d850a049107001c1340521280000045087c0352210020012200700d284036040f1199020300c00411a804203102c0c001102060342c8005a50310382d9490041d01c84801e010b1f083e48250407400303034040540d806c04210741182c850141000000704204100c1d2072584850010281c05d44541014940703c2c8441d98420046580112602150360741c42014491100609000c0c0c03a0000e0720b4100e00100d0355000340d00703041d0040006400c0c0c81c00c066100010920345809003403420096030101b0113000084501910040210b4102a1600e10314586040130840c40c1c0070300c0c45802c1f011314014070b0111780ca00741101c815480c811078174620b007121403030f034055012110541e6140c400c210216a0100354998081d80403600c1d0540c2c0090010519583e0040c0c00c2038691a000c111014035800b0004000040c0c010b0f18924082c0d48501c440c41d4540854030b100800301d4501d0b4110102513880f01400c01c251103180380004880c1941c0c4c1c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 66289553 1250 66288303 66288317
    0x42102130b22090503120406050c0c03090d0309030807030816020a08090d0804120b0a1116020108070203090604062304050a0e1005060a08060f040c0e0d080c07081b040219 75
    0x140b40040061201682c041c11a010100e0807002c25001e40781c0a900840c010901803080d600d070b02c4036150482c4606005030110741d1040105125a08001c80c801170000d0090030042c07002c655a131203a01032079005800840015280004021442c641c1c80c0111040050724402000d001c142a50303074002e1032064000d494403645078a40c4100402100e1021500503040c6031008440909030b03072800031a039400507500d0346c481504120180940032081000c2d522034840070350080e200c10060f50010745641d400a0841c00031070004111050054440b40020001403c09581b8801c1d41005082940c0c00085400f031000c03c0b40d0740401041080c0c0c1d451281000586081c1141000151100301c0c00062480c0640d01c5142c00c4007010880c54061074001034418407070790302030340e800b00d1400c1a0f90412080720b20030340581c804035019000902c8181440c102410a40348903a14080c0f401321161101403404842c0d07888036126500c02c02600c0a0354504c0524203406100030b440c25400d0030016506d03998844034180c440c80c200660 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 66290803 1250 66289553 66289609
    0x105130906020904020c0715021f05040507230103060e07020307080d150f05092a0a030f0e01050702160308030a09050a0b0a0507030b0306040b04080f042102130b 71
    0x4582c121100002c00600c11940e90350340f0b420054448070644a060518030001e07144503103090006c68250011690f290210048420070320182005000c0038006941031302c500d0001080340240414803061060034824031101350011070000500380c07103107034015050404840c002d001e5401d8001007500c070b07885d500c00310564035061051902030041007108855407000c1c0302c000c00012600012540e580a0b9034040e0307504a52035888542c1000d506d1842001c1d420b034000d001d034006e001e4403c1d03c00905200c0c070032458085014161182d016050740e058502c10314080e5034031800c5c0070581b9010040b16030000040c000190b201d0385982c46101d45400020b146c4078816440b54000302c1045800d1000001d0598403001c00c560504000e900c0d44020142101d03284c010925004168120740790001d29184031701e40c400030074030144c0e45076620854142c2140512601d00901031001090745100790310342c00b41441503e210442c0c0c0d800507004105184156145103040c00d854105143c07400e442e0381208003440e000c002110610050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 66292053 1250 66290803 66290813
    0x51c12051b060c040608090f07050f0a05040f05090d0c0b040b0601050705060a05070822020d0206070209010611060a02090306040201080603030c07140406061b0f0c1d090105090601051309 82
    0x21400810a1081c00b40b0b408000c1c01541120150040d5081540c03180c035140c0e280d0900540e00c0c807000384401c0c00c960000c03408200c1d80c40c0100d24981c0000024115041e1203540300b02140503078404091906000340c80c0c1c41040580351013002001140005807603c0d10544425403900000342401400c042c2540703c4103000601c107640030700101c3e9580c550100c01c41da0217181c000c070082c00500d03007030b204074002605030004201c44440307040d8051004552022401070115060f400c00a2445c8030031070480e003003003050040300e000d41d0720045c04074000c05e0951280314485c06490030322410007030001c103804440e03441480722035501e071400109203a02c01d0342800c1c05070312502d615001902d180030f440078589043c810828081040383c03610345940800e803400e440130b00001e61951000c1d40c490000010809214140402c12030100c2c820622400819000b00620f03c3c44030744a0152140791100c800e4480c5241c41140180001d070102403080c1c035030143c0d951010b01899410140081c018104c040010300382261a04d0303070002408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 66293303 1250 66292053 66292087
    0x60f140102010912020307030306050307061202090307120c09112107020a050102191101060b0a08070909050a05010509151e04140106080403140a05040303030c0c050d030204051c1205 80
    0xf0f6049803180d0000d0b400d00038020b6503a440300c00c0880c0080c1c24014001050300300020b80b6002e031000354135900e41c0c41a452031401c0003034015441d400c0e418495114001042103405220034115030091a21b0f403040c504102d04a01603d0702c0050f000c4554400304110b803880401c0105900959240344000301854841010403441d2260507200a401544006280301e00186104401d8040ed586500c5900d400142908003d003226500d100e00b8008030400c001c1c10001c6845081d40560004031400d00c550401e07100c125440807100101e038035041450340c0304014095468440985c4d035000140c0101070090322102008038110300120854801c610444004041c02ca5486411051703144041e03040c66017180d03941d00d800900350f01e400e0303400303802151150400e540003004010464214259a499040c601440d5a60850050050703004280c00c221840d284400001c100b84000702c1100c02555015884906050800c00380f82d40301384078807844403c0c46a5040c00200505d62030741c200260f034180303141c07103000e08642c6030802 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 66294553 1250 66293303 66293321
    0x1170d0c021503042603070905090c041406070f052d0706050a030f0905060406050f04050c010c0204020403210f02030901020703080c01020f0316032012090c060a090801050604060f14010201 83
    0x80d00d141a11060035170091000e18400c001d00d9403201081a038940c241b0101c0f91003650a0540c0744800c001c00e101c0064616200144100b0240100e842c1249c25254030a8201c12004119196007003543c0c0c00a1003603183c1000d01e088400c110200042040d0041525600d05581c40780c1c0701070100104201e039690b0b020b58000303001401640c0c1c0500209200d4078140c2c1e200c1c00c0440e03089815504e4800840e484a4012403d148140d5004004080400d0710301c0040d43c1200000b4012a0300036020000840042c0d984d91280015480701605440242c01d41a40606210f652140c07420441d403081c00404800c1c2e07400585070044a030004503642d95804c02e013031218064410481c180203141c0000050181120300392407818208111075508010700c03003171046090f0180c000135005e011244801c0c065942024407141040350071640400032212006020340100716182c0040e600d500210341c030014104040e00003800f8003644030104450030480d00f4148580c102a40f200ce00030021440d00030703d078010082e4002d510003444 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 66295803 1250 66294553 66294593
    0x80f0901150306020316031401061d0a0305010b010f0201021804050903070807030507110d0209040212100e07030209011e1203090506181003060b090409051501170d0c02150304 77
    0x5902d89030b080c04000b943c02036a04140102008000e403603000c0c46445000881c0c5903c81130742001d03910b4020100c402004a0f44401203088480b100716040d0f42d40e140c2140001c5104078000b2501003031802c0050481c0c819900a1020359004208030324151030b20f601915481c2c1c2c070444000600e0380711040154030b5070180560041c081d1a000841a050503000340c06014030500c00c95041000c040c5000034440310300c10f10f0344025084045500488c00501e0704a01440310301c4500c03c05c586030103140803006425241e48152400564226141c24400d5090000000d0301524a10b00c0d40c40c00040c02c003d40c001c4c0a5540e102c0c5c0b00d0f41040340e202c050704140c860b022140003010b0060007a034440460704454100d01c048018514407c410407040b0300d48160280c0107241c11121111000c44c1000c24400a01000c0d0161a4084641e4020800e58594601c4603c0d00c03d03018007030280c2008544c2c5103810805242c00100800001409444107002d8016030b01c028018510041861f0680c0e2661140d1501c490304896071008909 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 66297053 1250 66295803 66295841
    0x140705032701090302071809390f0504150509070e03030c0f01060501120902010801050f031002071203060501110d050f1903090318030c0b03040822030203010b060a080f0901 76
    0x100b459800900e540943d151008454845290840e01d80102ea1721244009c0c80c03201ea504c14007400244000c0144c0c0010f9850b100456050003461003e180b00200d504201c6100002080a1120b401c10744100380700035041080c150503807418000002c0c1d580d81d00030207007004c110462041c0030b010788007070042d511070400b200c0131070720444600c0250b03d0190510303009441c0003032800300140340000000d0140c8440f094040c1c5401c1c1c110f0b420031007800001c6011901c02500f5114400d0402c40702e610714401010000d002d0030109290101c80341c4001e054604980c0510304001ca100301191071074178049000c403074035102800c1455441034201c60800c5580601c080c1408113a004270604840d4a41582151300a40d01c01d40d00d111038148070a224008840d6140405130514099007001d02c14980548010b40e00213000d1500107092a803002040105010070304024440000c941900b0421410240a8019035000860b81c580c00c0280c81c1500912891008013a900d038800ca00d0042840e2403001e600040b0b42c030f240d2200000e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 66298303 1250 66297053 66297071
    0x1202060c03070b0f0c030103080a12180f02041107030210050a090b01120c081c050705030903062404050c0703050a0c05060a15050a05030309010507031214010603140705032701 77
    0x401c00c903c0c211412910790000c0000102c000c80311404480c180c0380d010080d1801c290f00040c0407120502c00006c034030781c41d07039070750030043c40d0b00900c0704685861500c110a0700b4006c0301c55105100c2600e0355200003002120090005200082d0046050020100b44a00000e5255190031208001c0c1c0710301c4d0000f4008541b880f00115005640041c0c412416001d00c1004138803580e9020350650311b220150242955100e1f030000540da05104100505000c0d0142040300d040c801003000081c02d0000039a0140c005085a41c0500260102900c2d61601910126410001c3c0e01d400007110308144200e80c1c3c000c0800900050b0340001900039125015000e4010040340e02915100348144010030200030030044501e17000780001542e00c0d194106e00140c030b8020300034604281c900e02c0155290340182d4030840c21300603400701c0e10106100e01c0c4564014520213503000c0300c0b41e51400d08041c044031310825400c003800c1006e00c104118a90480100c98229140804072500040303002c2d201d83c9113600310300f0340100a5003407542c1e107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 66299553 1250 66298303 66298313
    0x90203040302060609060a1e080d03090311070806040b04050a0606060518030703120c1a13030e06070c0b0a09080303160f080f07050f0904020d0906050c0c03041202060c0307 76
    0x14500c264402c1d022280c480e250441004003101c4211810f82e4012101e81080c0f12034008150f5210301400d10401c0b5085407a10340c0d8101d410a1740720440400002c0c2d880d01c1503424143c2c0115004d0043c1c0e90100907000c0d2504165a541e145d410040010f424801500d0204003003117000c0282c050501d0b0010030800210740c0b1401c004019502030040c1c281c19480308405ca050524002c074060003101d0b80070101b00c0c1d03846402c3e84c0a5070141c182140580d000c101c0c02c0c1d40d40c4481110550014450615040c0031400b040540c80c020b0150003070284068017407007040c400b035000601c502d441d00b019605c80804032a11241824012108550560814082400040140a51b990b00d017144428cc00c481c0d03131500c074080c0401c0d0204031920082240c2c801480c1c0c01140100d54030501884c020450b640708c50b0360301c40c60307c815900410280e03488140346403080c59441d505402804042c1c0b10b41500286000c1d503003442c004446541a5480c0654014000e00c034140d1104c144c1103555100071500b0700c0d074034031041c5c985801e064202 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 66300803 1250 66299553 66299557
    0x120a05010f05030706020a0609050a050a0302030720090711100204060909051803030c0a0311070506070207091a04020c07051c0302010506030109030f030902030c12211806030406020d05010902 84
    0x1081800e00030710002040614010401a00340c1d601c550041800307e485858050192260a0003a1041e00400c07545001096090144460442c0a03030021030fa03c2e01c8501c0d0800c078042191030405411710101da9140b59654030401240e0300007590f440c0c0710603070704410b1001074103141044014040c001e200090000e00300e9000440324044900702d41d001c000545d5112100b1070140c50100c1a526160020000070300510344110103429260100d140028407941d400c1020420782c0d20003001500c4680c051401c01c480254104002800b400c8400b4043c000012a03885a0210418000c8968070a81d00402c07003002480c420440b22000344001080900b085450500790b00d034040145c10150015400c0200140340b40c20140240c2c501581d05569000c2000d6003428120010140e00034126418015001140060b580e03812055408090f0000034140c0c1090025101c0030040f1840d410030140307170080c01415240440030390504400030b019501c00da529581c0f4a0080000e20a0841d215407076490f00c00040360008081e40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 66302053 1250 66300803 66300809
    0x8010b0a0501090b0304110d08030a15050102061602010b060301060c120302090109030b070e1003050105030d0e031c05040305030703020d0305010501110a02040f0209040f050f060607031209020105120a0501 90
    0x2001180410024850440100d00807580842d080000c10000d999840e00210f503c24003c0c44540a90000880005c207004d00030b180949280b4404400d004080000d44145680d00a00f01075600b07010749003a00207911410700800744e203002d00c0302008243c2168005e40108125000051000703030b0343c0da103900019001044103d02035070f41c4100d00700030b40b03444c81c004d10844910120513191003030005e1440d600c04140c2c1000401e601c00b0064091440341003601c450004000180d01a200880c29606044c01e051070000c1c05503c40c1b0030056809400e0300192400b1581580c201504410200005251071040d43c2038822a40002c0581c0300018a9409141c1d01181c0792508250b9540c00380080c2c0da03148011900a10b840d07940d240281c0009410b03100624280d400602c2d03601317030082c016081010207000101150f41c07112000c00c0241e00d982c1000f458120240c51198810300c1240c003282050300765200202807038082c0b1001250550f50f1600c803000e5a0003801996003040301c1c21009022407903c5901e02c00030704020300c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 66303303 1250 66302053 66302069
    0xa0c0603110c060103170909040f060e030a050d090507030f08040e0c0c100c022e0f14240604090b090a0608031c02040306020f03090c09010f0302060319020c07 70
    0x81d94102000c15240803a5800720201004040f264255228000204901408455004006c010880b801c0d12107560183c401c5002e040c00209210302428100181c4005002240003030300104845c152581e001001e031103c140200c440080d0505039480d20b9442c0402d0341d040035201d006014488020044044c0c0200309030342c80300098000c151981051600c0350f01032202120000d80190328114043ca000b80c0c40b00139100d01c5841181e0210101078502601d85501c02e1441c8100603960b8480c42c00a800ca01990465180707540041041d18000300548600320b1014100150040d40050580c51403441c081100d1881c00008006503030b110f0380ca40707009004140180301140180c41202c0029100500341c41004100ca0030140514948901441d103001e08082038a00d02040d6542880040086410742c809080309101d1070311000c2da241403990b10140b911001605440c8200d5081005110807601c0036130000480e58165125030312616000203013a501180603501c444a240b000c90952401300001030028110f580e81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 66304553 1250 66303303 66303311
    0x3070902040816050906010503040210091701020d060b09010503040b1009020a0c0210090509010902090a030807060603051002040b040603050a140f07110102180d030210020a050403020f030604030905041d0a0c0603 93
    0x40d07130511030324030f000b142c0707541c0494000d00c00240507003041c41e0780741182d208030302c0c100030203540318000d843c1141120b40904220769404980766503079001c1e612403600075109081c0101d08051504000800e40e1000500c010301c0343c100d440c0410080100c000c00306010380284003056445140c0404000c0292541c844186e1103410300c85c18145280c0d0240b1f11001c140c84003e41100324603030030051444d000c1d61001030030a4001e902c0300400408034429801034a40d0740c1c42444080b8201f031540c01e01d5480c0105591043c0d1a40344100020425180400111400c40e6040d083c04160369071509409002401c858022451680206040040c05040030f241984214010380b10303411940303406803c9a00b00e000d141210200404d1550310091203213000d0303a0020310a8401c0c4112046203039040303500026a0085039200c03020410104c4e06100710f2900c0301c0c1c40e60040c50244c008060b07034a0325440040c04c0300c82c0c5125950090f59944000404138070b0b40c107c50004d00c0d4000b4110f456641e814031b065121440d05100c4c11000900d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 66305803 1250 66304553 66304559
    0x6030812010e0403020a0803090c0613030c0e090a02090709030206120603060a02120402210d0e150f120a0605040905030c0c030a1214040f120c090b01050a05070203070902040816 78
    0x7218582d405550140e00404c038211050707030b0b900030a5101418101003403049140d60103003a6196802000401c000024250f03000c1d01d5031600c40300d45001904203c0103030450204110700c03400d0009036601441c2d0101c800c40059190000151074a03412074101035005a400a00095203150070306d1440c2c0607003415800c503511503032410031000407400f96156080c0a041c0c40c00104000d8a8070800c906407040c0000e00030380000300f4030b5a42c40d280c4008015240040361000011401c5c41c9040f0008101c6148101501842c00076144da02001034458503424200600d1329001080b500002a4420006058003420130004401d40b402d0040d9a130f00300400c803c00502c40c15105081c2401c3c08144882d0541d40000c01c400b02409010301a10b107254800c1c60076003100014400000d034901c6d0640c0480082c20991503d5504810a040c100100406504074000b03990408000c109140d034080704175040350005160607910707030006100107400e140c11030380800b0860b4008540400d0047c408544407621100851400707800350303a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 66307053 1250 66305803 66305819
    0x60b0d080714070501050d09080408150f0702060f0106050d090203070b04050f0a030f0818040c0806010e0103050c0a050f0d0e06010513050c07022209120f0201020c0c040b01020708010603081201 85
    0xf05001c0d090001c1d4041c403010108030100c1d00540038280c0b19424803420a903c9511241c03410741080c494220b65150780c401d2001807010b1244e9203411110070b00c0508090328003410b55903400f0f01c0610585040003000240f807406440307180d214010340d56009003036900c582c1ea038146210ba95000303401150b03c04c00b030849000307185207003e407070010840b9842014004001280d40300c091709070300a041440505d80100c03c040c0c1045e510307071080141445260b1192400c1e810060001010b200001e2901c038141454a01484070318100310007030712414042403620710b81e03511011003555468050340c40004030740e40c180b000410700d25001164140c1600c80c11f54106c5501d0500b5580c00064510039105079007103960030829000036081c0703461020800c03d8560a209800c407090441d200071511034000075a25a1100e5001500c80c0384e11515aa013900c015100a45c2440c6c2c921100340c1d113440084c24070030f104580d10080c03064664004e003c4800144803400c02042955500d0401207100d1344007940c540d844080007000890200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 66308303 1250 66307053 66307063
    0x71703090f040203041704030503250b010302100c0605090f010b0105040b04060e0f0916020d030204030b010b0a020a0b010603060302030d05030108031b030408100905010b0906030607030504060b0d080714 89
    0x100d0040003851030481c11400d20000394400f420030f42d20b424024080c0780305000c10700014401184500000c56130340c454045428207810865030504000c07034003d510744000c902c0165015055940403118540c03123100d0001c042e04c1c04201080c00804041c1000101b007214400401c20201042c00310000744038086141340119500d10480c01829803120f005d103c05e000703642c0304040c8011040c002a00c159821680c150008420303110443d074141c044000c001922001c0741e810712611920084e40e003400c2d0704250850742d91340c1d01a4014068000c0308840450300d8108280700300032074042c00f9006403c00d4410b585030b440060141c11036010a13070080c1f2a1141d40d980d090300c524105c0381220384c420091420f14900f5808051400e924900d40704641c84181301c00300302c0e8041031040c6104404034100004030001c803482d1541c251210110128803440c00c01c4c0811156850108010368040f441e4640018240e0381d514201c00100001e01007070382c0083c655a9400100581c580091a01e6801200017080e12501c2000f10f0340d8031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 66309553 1250 66308303 66308317
    0x90906080c060f03060a1a091306050607020d080f121b0f030114030c03010c050406080f070c0f030c05011103190506060f13032013020c030f0a021c02071703 69
    0x8440b04101c1c40f03d100c1c4100000d142c010303000414040070140c0d5050241d40140c465214100c07003c1c40000c440ca4586016a401c80b0105905502400388a1a100c0056050b00403404064003c60000b20b0b0101040044804c40d04086100d224450f10b402d5007030306004034050211101d141c41c404101032100402071032000da6100c405c106074414510307030800c0d1100c4e50071001810400e400d4450031800210b2075030203000b0107203070031a29907503651141e03c3c00d8802450250081c0401001000100c1848115035100f540203e041d500300d46500300d40034031480c1c22182e000f08044094415440e040d890743c6e078082d048005500074188030402d91009140e030390344038044490596900790f0104042103c80244a02c90001d414211000d074000e0180b2a62600c503044082014004420440c0e000848840b030341c64031050f006c6400300b150108604011101150030341e030344240d0a40541a11012036041803091003000300242c0f0102a14113803000c0300072584080e40d20101400780036001c0b07003081c480e04100e00700002a42c1c1d41d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 66310803 1250 66309553 66309559
    0xc03040c03030309031106011509050a0b0703050f040b0c0109021203030928050304080c1206070c03080a020403050d08090606010309030e0402030c1207120b0d03170a0209040903090906080c 83
    0x2030240303159415402000852811018001100c4821201c5002404468020005e14007600703941c001ca410010a00c21142e00301510030381700a2001c0c00f0007441c2c10140c4600c2c55060411964440b250002030300d1502a03540f01e00c003200000604004a4541074020000311842507030038070b640c00c0e00c6040d45c58690004903040c0000354001d07940c80b1480d82c3c0c86d80071510070760450001104001035076140d990456005800c4406c803580071701c02e09086410000300000c04a4012805804641003d1000504c04241c0785005010040750303101299045074980e045a00075070303001c0c0c1151102150840043c0196200b01c0c1c11055602602c000240254003070b005e0410050752513955480005200c000b080000e40010b040441409010b010902070060380b030248038014100e5454484001250080c0b9509031030080780c00f640206182c1900ca800650000e241800c3c03c00d0822220441c1d039200ca1011000340902440542e1080c2400b01620616400158020590716000d60500002c0c3c0c868510702d03600c2d0190324000360 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 66312053 1250 66310803 66310823
    0x207060e13091515080c010908030a030b06090904050a0b09060c0a030f02090405010605070c150c030c05100c0e0301050105090402100c1103030403061a0301050601050a050a03020405060c01140c0304 87
    0xe1010619405940c805219403d003c1d12404010203100c1290310705901a0500041100240403c0c0801c004180d41c884091a11004660400043c5901d901480d460401411307111030a50815699560594054400c0501840241d107440c1c00c2080e600e0300c000380c00f03842140600f00031540b10391010551503c9559007802e110303c0c1c0032003007008030000c08040c4210b0384e515034280702c4d036986d07651140a014000d21599031010344900c1c40d410452031010300f40d0300000b000700e031081c7c4002c4130a03044030050340c010f80c00d820f20840c05d01d6241041030412a9800015040501d801f00303c2e804160040d074030311210f41c0140d00070082e0742e8a0f10140b200f010416a000382d400410f591007480003901c10107424003480c0c0b0885407080d4240007000804e00e180c0054000b100c0903a101d050301807106000b520780140e20340c801c400a202d603051140000e0854442c481a5004110000544041d101e02a40440c4e0050074054045544c1e03c00000b0620f0082218820f914030341040000032030300916242c030030b40f07000d90b03001a643c00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 66313303 1250 66312053 66312079
    0x5010f0516060c08070822080307051c020a0906030506090103060b030304030506010605071e0b0406020c0c03030f1e030f0105100306050306040302010b0301061d240a0b07030207060e 80
    0x103245074000085900c4580d8004420400154180c040e0b0120004552101152810402400741001e000105804801c0448401c00c01144011410410b000c44d0800d003c02e603281c031119070841e02403081c010b440d4a9035050010b000031070079445c0c2c000c0c48030491300d944406025807a110210f003a0b400644600d070340b00101e10010700106200b90300441d102030004040b41d1525599540b901c0c1095801d900000c040f46c1d0104070b010a011640385092040d80000d03181c100b01340516514000c02c50b8028002a0980c3d5000c520f00703c2e19071040010003210b1900504813901e0307101c041c0052500d40d21032240f1500620011101d0241e4001a8003034a01500384480d140e00c070b9a080a06002d4448000c45440c020540c4407000080c0944007400b0140c0504d010354004912001070900741801c0d155036601c0301c59203008440b11000c9104a03a2240c9400041d00424201200c0519090b14070982c50f804031194814211207002550000100042481602c43d809640420355201c0c810707901c06c00f1481c01c0d950041c3c40d0700794103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 66314553 1250 66313303 66313307
    0x303030f09080c07174201060206040c090912140c12030405010c020106080a060b03070f060e040e070812070204090b0c0403350c070323010608030c031207021c050a030b0a05010f 78
    0x540504c1ea03440e075907111414034842c1c013100c860740a230320003805078000800344801d01195009041c05081110800d02c0216280d940e5222030105001d1500c0411942c450884100c0600038116070500c103102e41169039100c80000030750010390040d14200c07181e6183c08210749603d40103019030310403640b14034050120b20807a5101c0a0142c03058819055050007401c50108802541007484005004c80da6503115000065100f4042241c0e01460005141e074402942000044c000003810856940583c100c1a02c50300c4c284081030160901d000c004012032000c80411101e411001c001d8003c80707001d07074164420303a07003400241402c030343c40c441c40b131101c0b1460800b83d144440c0399140189911408035044031212030780c940b40d20001c3d0038008900e441c03400c0c000040303d40b901d100b4000e8802411400380514505502c40802d15620300c10009001940c0e04104001420a4004e01c00c0c8444044440414418010000c800400b00d501c8901418042442c0180c515001e0401c4c0c5850425288181c4035040900202c68003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 66315803 1250 66314553 66314623
    0xf100e0d08160512160e010305040c05060c03070c0e09061302010f140d06080c0f0301050c07061805010509030a08070203070203061f051503070201060b0c070303030f09080c0717 78
    0x5041c00d003d0108a502460702c401c40c1124410000724001c00410000c891009044084a104481c10107042000313000c042490740030428200c520458810b55942d142e1443c042c103600882d84082d01d000300d45100011103030140812148945044070584480b0761360504410f107002040c490203400503041149008a0703600458080f99009407840e08907080244081c03030101038607810342004100d500300740c1c00c2e4101d0b42425041004c1150084000b0300075071510740440100703400fa050b00034081c3c03915000c8618440280f10f948440468005009004914140800a683c4e60041c403201002901f454005201030344040242d652035580100030b455941c4801c0b400c041082c0510341c068201219400300058541d65806081c0700000c003001c1d129440749011500a8211202503020101400040041d8049280041030381c00a907a0305060000d4514190100a001071030083c40c024403140001401d40540c80c0b000031100c0c110351803103000400003054881d0a40d118803150311030340c994501103210641080000c0f20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 66317053 1250 66315803 66315841
    0x8090d0504090b0d05011d0d02010212040602090406051e031c1205071107030506010f08060402060d090312060905100515040e060f03060103140607020703080301050603180f100e0d08 80
    0x80200b104d510f0645406003103901c103007441055401c0c008018540c504d0240600604807450340002c5042c202d0348d150140010900034002450a0f83c0014107641c55510759000e4009454050185011b030240c0c01c5514075444000303103c1501c030748101200f07000b0a219800d40c100c02c02c10550b403405041394030480c2420262a01419070000d006ea9950103040d004800c011440055000383c3c024030039949485000300303560300503404c0550f00707810040800002d038540500b140c580d641103410000d01d0003510b0401710365800804009481090401d44005650526900800e0091521074a9030340c525507920100311410a640e81d03500c2029200f813100700200700e41c1c41905984240301502010211050500107400c00109810807100c0c60b00801b80280c0c4103074100301c000d80c444480d00041407040d065885400e038074081403103035500c1101c0020009400c104801503500312001440200d070100112007020715184e8020402d0309080e68600300d0360507440076000541807030088490b151801c84e51100c041c084c000c006884 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 66318303 1250 66317053 66317059
    0xb07050705090901091b0f0608090708060414250513060909030306030c0605070804031101120903050406141e0304050f030a020106030201171509090f030f03010608090d0504090b 78
    0xc0005030580380c40446610410000f000019400003e20302080e003095002c0a02c521800700c00c600384007400e5914030f0403055a0072420481c03101e6940b0b0702124502400e541003000c4500540c030038030041048811510b070b0340c696004140c0c0c0032000300a01d0b028100d240818100780c0784400c42000c00c858180183c0030801c05c2c0c032400d804a00903444051100075039402050880020390f441d8010002e106c4090b0600025040c540b419510b441c204c0d4076107103818048c50202621b040030f624182d900301c0e800b038400a00d040c0143c20050110401d541005812a0010720521011444812007000b80c1480c00d01120304213006413502d100f030900000503840307042d04010411030f21446080c034902c4516000f0009002e4060041e400450301f2411440010306000100071940c104c40796180c180641c8400141480c0c04a407000e03141f11807141d07126000b140c94060ba04000e03101c0340c040010040084840c043c0118161b031200d4030f0b061130340d0f103a40c90349039a12016003203c400090002d010520540d0095007148140480007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 66319553 1250 66318303 66318313
    0xe130c0903230a211704020603060d020d03091403030403032016080604031e020a03030c05160506100b040b041e050402030c1b06071b15050f1b03100b0705 68
    0x1218152800c5403400d0300740d542d039502020048a00c840c28843c20308111207444d040301d21481d100b01003205c00001400003031080e400030001400f640c450514007a203142c0c004280d012002664100030b031114003940511030350800c070700c200c03410b1a08002003250110703607050b0307030358501d0301c10100148800c0502c06803400c1d006d0042c0f03e54000c1000703a0000c44000f8041c2c20000d800d041c28149400352a60101c8100413541c0ca03480b031036119800d0703004501420055090f05000c0f44107800b81c50100c4242c465800c082c1c085d031800d0328400040c0200080c42c07a104420000b4001515a29051249140e000c4c52203034000055081000344060740b0a03054651111400101500911341c80e1000101a1380044030249801c0c003010521360f5401086c8207441c50b00a010b4405080d40b8101424001c249424035040d01c04c660640f14081d0301000081c11a250408201520800c9039051818181e0144203051310304407c10703079200d1901c880103c0703840201d0b40640707c8050b44070300d89480c198201c10290040902500c00b800340c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 66320803 1250 66319553 66319613
    0x618060a170c03071e0e010e0c0a020c04110a020c03070f1703040f030b04030201050a0902090105060a0507050304080604030816020d0e010e03100b19050a090213080d0e130c0903 78
    0xc00c104c80c0b0043c01e03001da0344102005008194110b908101c0d80325020022008004120714021944400d1300000030041c0565170321b0135148264640003052200c590040d141062030640500001e0107400d00f1003d036030030b56845c407010404241d50380800d80601d0710001c44080040141cbc0c10815020021b043d044803e0342e080c80da4501c0e44210355072103a070065a410194400304001c26a0a2203010392114000100300080051500032807100c120500070140601000215020040e02078000c0c3e03040f8980c003104882e030f52030301d81e00c02c9500c0e0300003600c00310080344c00203012403c40d450311942c4004094055000780300e01c4800000c115580304500c45481c0c1030046d420b1a403da030752400d01c0f4400c030b4418003860208171140781030140200d1803009004030426a482110034000e0356a01d02c0f401084800349280503850324540d040f01610f44982e60301100c03443c815060140300c0960801e544981410f81120995070300104d840302c60302030728200b00790600028000c45c4c0900c00118002120f240c0502c00181d51000009 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 66322053 1250 66320803 66320809
    0x1090b0a0804030e01030203090c0f0d02041104080705150a18120501050106020706020102090916030b091302031504030c0b1b0a020615060403150b0303070213050618060a170c 77
    0x40084003110004220750300700818103030402403400d007104003860300710302c0c42c80c155010585440c4200540b62040402e560f6143c2d1030741c3d0305042c1c1c41509800810070459000908900c0c1402d510601c1006418011070400003480c0c940405800c9064404001952900c0042902143e440580c0f1009031280c044524001c919910011015809548268000140f80d410100c000c0d180180541c400c070304680c0100044d003240e458110010ba006030a250400010074003404c0250060303e888420180c01200d202c0c03c000401c032603504072001880c001c0d0142c0c1c912051841072030101c000d04803805008501041d540301c00098603406d074503074440e000c040c0f070050380c0c6800100d640f140d47c401a41c0b000141d0107041401141c481c00442d14455450440d00e003807a181ca55941c090f484942c0d08040c8104591b500300200f02e9450900446d03c10540c0140070004400090300d4800041109440c107d000d00c01041444080c031000e12020b9000354001080300c001245424076505260820548d400f0031401690290f0350283c07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 66323303 1250 66322053 66322057
    0x406051909050c03120f04060813022e0c020a03080703031116031b05060c0309070306142203120b030109060e0601060807080f01030201110109020307060816030603150b01090b 77
    0x42c40780d00504095812030003014648034116031400c0c1210020008640051180800c4400301e5285042c0307444e0580c0c1d03410720109500c80701400607411a400580340c2c1500c01818250400d16040710481c690100301c4040100d8603401c0030200250030801c1f28100344003048010700600312103486441d020512190903000e00b080c5170091540c0403160440a4811800c1581210b0303508026034071807a8820001949071a81e943c0c40340090002d06400000102161034460b0500c180d4000d1600039200b4880321050300020411000e007112403041c10303206109142c404203050a040300c1e90780d2f095036400c03640c151510f00c03840090000000f000d40c10365980c011400050001d00030260340368103900203001d07030703600d0003002800d0054010504001c1103e10720800801c2c0c0015440e05040d66028071b040f640984100b03001a004220100001c1d50503c41d0103c0018820303032020310144a0100b131039050194074002c6070268240d13611400020030b003c162001c41040d020440d804881074420500d440f15080380d1b100f4401300e0036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 66324553 1250 66323303 66323321
    0x32a2103090705060f0403060b0303040b0c030301060305010504021204240e071a04030308041506030602030a0f0609020a09050402030c070b070c0201090e041110020115060504050306160804060519 86
    0x4501104001c000d050034041c040082c00b0a076202490304140c00c0e080040c503c1940401816517640d40850b5a154408205490140c0b4161042030754902c1c1c0b44890940e250002d01c0703060700080c10100042a581014001d8580080b0341e0b0144515907201c582d10186421a124001c400d0115411540306d0114020301600d1042184200030700b4040f42032100104c8101c6c4e079030704d1940748905c0400c82040025030200c0c4042c0d200390031000c040b2804003d144c0c10030240150303034006000c4074004018040d10320351a90040035040000c6a00b0040c26030707180b900d00164040e080460010403600c10042001e0300f8150021644141c80084083c0707030100542d00e10300485000d481120005481c01e01d10b80c11541c002a80301c01409035910341c07441c00e1070217030b83e02c40c1c0038102c2c0b031411130080c20000000100350b0300035042404048480702e00c03000c0c0e103511050010180c0d00107104141c481d01c00c440100e072505075405049026092030313940390b0f81c1c991f48648807580580800b620500d2004042e10861005a00c584511050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 66325803 1250 66324553 66324613
    0xe120d06080d050403020d0b0603010920210d080a060905070c03080c03061005070303090c06020c090f090a080c070b0d021206011d0d0c120c03050f032a 67
    0x110304281d2514504401d0840300d6040c03010401061015a0314601566070b006d5001c1e080c80d08a50302d10004c03c1c00b401006000034010104141c01e200c445800400070b52503101d042d83c01e01d043c90300b9186103414040801070040704d81d4100300c2c0c518840511500340340b0740c40300c0380c07040105201d580c40c030000007151401c6606c0780c005500e01140d0000c05500040403504003030082c8035981507044c05800610001c0c0e403050340d1000d001c00000d8010405019410540303949800200b4061001c0d921800a500d0340320440e01c00b4850841c090004885002418006018040d40e400925a4600503550510360764068007075860750388034801d400200490301c0c0c0014903038403262070f00243c0c03230381c000c0e6155101400c8068a51414450840d00c10814540f48071191109080c0407900400407030001d00b05400302c0d40d01500010b180210308038000040c064015420b004480c4a40d08844964000c0504031380c40c5d004c3ca03c0e1203109205420044007000300206807041400750171901781d940b04c4207032034040400900c0a66403810 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 66327053 1250 66325803 66325811
    0x40602040515040f060f031508070602010e15040206030603211c0b0d0204020f04030b0a050403090501080403140d0204050603041401050604090215030c0c060f04110d0201080a0e120d 80
    0x507400d2282d815006140c5480e60b0a040500303140400809003441e000344c408200e40d000d02648094030075080440c1001280e2610300180d40c4610150341c8448032402100003541c248104803905402c000b680100404c0c0c500031010550322550300304040385d031000d80180d070702d0304c10100000010151002c244495005544403180c0d02d40c040241001e40501aa069400c007601d02108c407407981e15050780c0c44206590440300103a480003030f83c0c41c6010380d00450708041c084d030910300100703d100303c1141e000314041c50103034854000855884e0011603c2d60400c45008000403e05c59500c0110214180034016030141c00d90b0144c00c10303032168007166485e00102c4e405d5440c0701008075100e000280a20034650030110640b4107000d4041586c01050301c00300a644070014114002000035040d000030016148004901e200355252400d241d03e1060020f18161401e8490f5414500d0b1405a480c0a840f2490314641c1a1620300a82c2c1d2813041010007004404400849402123240b60420100688001c28850900070740000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 66328303 1250 66327053 66327059
    0x30e06100e060d12030903050c010f09020405131212021e0921070b070f021c060c0509090601050d1508010204030b01050402070203031209030d020316080601080f01060e03030f0304060204 82
    0x440d024001c0c00450050b0f0740c00180401144220405404030501404c0c0410302c40d07000c0c40c0803a611f200702c0200340025440c255003d0700c41400e0f9000041d60034001c640c14403150b1541d0241718103400742d01c0c200610012460940000140c081d411540c84843c01140040c24001216810f41364005001754030002e1000000705181145040361850f0158507000031142411407029849913621070881c0601c071401800484c3c20070400c00424038041e801a405007855561209441d081068503840360001c5805078100f10a80201c2c61040317081d0381010720f0007010b81406481b4000107444640c005403c41115036128603000440c085101741d00001010031000040c0d03107030700e181860060000180c1201e846180100902c034056503001054a403075405072500d0401c5911000c0c0c60501c0e61103008078031000c0c0e90003c01080080b60b11800055088491a105c250242c2c0e030300c0004541001c0200c0701024089500d1006006483c0304908030410550041c085906d400f144000340001070708212801c07640150005418 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 66329553 1250 66328303 66328319
    0x206160918020301151107060c2402030103030207120f060e210316020a150c050d0c02100c020c0109090c090305190203070e07020601031b05130c02011d0a12030e0610 73
    0x6901c000905180c606c0c0e642100c0d09003543c6413070592061408008104001509100e85118241c403007800100f078080300da12140410001940003448190f015003d1914002021160f2907102401c0c16408038071450214031603a80c1c080100b20305075490001d071040c8201c1890400d000070080c81c03124040c8000d25201d180104150a05564107030480d421504480c4590f80000c031350310800c08a07124401e034046908103400008503074038001d942285402500f0200d00102442e0042030100d83c2e004030321014030103156001004d90795207070524420381c0040c92074903013004151220307482242441c6403450000c0c11141e90b5120207103080c8269460703415041007920b01e41d0441c9402c002c402e009109420303510b40c541ca000e04000e5210501444090300710084071402c0745007141da500490000d031400078110389590007100340d82e4009010102d55240958030704840d028140d8052581500e0207c0680014541701d1000c0d5070355011403804c1d036042c1c401c0c0342d20748028184c103040500c41184950241c0d08005101840c0c1180 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 66330803 1250 66329553 66329579
    0xf2d020718060803090d060902190509010603050601050313080d0f1e0504030c1401060b040e090106060302090f22090b0411010e09070807090e0106050a020615010206160918020301 79
    0x41c0001c110b19041081001500c0031040c2c0e0500c1c001220b040302c1d60000c50400c0c1d000b034002110300035446600d0403072204950800301c412205607841942d00040d640e0b2078034800e4007110001d440003404140284000f0b034040340c4a82003401d94a21442850703091401c034011030010350704401240542c60747c65408485485203014004101d030140c4080901150500f9140a00305e4130305a41e01500180311949280c0800e01c2c25089100207200900031943e0715030351a11403d54a150a50f880e00c069400d000c40050301034440c0c001e403180c0c0740c4010580c054100701c071402c001002540071602c1d90100000d01006500700410720460090a0107000c8040b9a45042e10b42409800000f41c0074505004c1d240c0500c1c0d1a507218411015805803043c240b9118035114440107455a032050350005004010000003c184540e0100140114054a808454482c1c03940c200b81c04904103508012801680014001135211208442e442080081400c4c50f9031003a485807006c50300c0069200c2c41d0100d03160000010001e0640040fa = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 66332053 1250 66330803 66330839
    0x109060302180114011d0915030c0a081f0f0c02030a021203010f050906030f010e1e06010305101503060f020406200705041a09010801050105090105060a0f2d0207 71
    0xd030b0360000b03605141041d2000d480713000802e41000013510300031145556041300700f03510030002855428a854851040d03040301d400c803035070f40c0c0c064050a400180e007428402c1000c4140c4c0d503844040c241080035880740201180d01080c16200c82622000c02c540b9000c07242c410304c0480051030780619a1812442006460108090420b45414204000400440301954400d0056503402c442c01001e5842c0c00700000d14044007590700d51529440c000701000481c1000a046103186a041c00325150754404a0f0a980c9858003484080e0a903005804602284c502d00da1024244014220920381d0aa45a858000440d01c4480301c07000700c1580000c0038080150050702c0c142101c030245210f4100f102a07031000390b445904900c6001c0c0544d4455605079818001061444080380c0b01400b01c900e690b82d2009424080d0a00388100d900600c8010004962400c05008580458210382c440d0007244262880441d0700c500168200c601e800c46c0040e20302c0705002d400d03800701d4685903140d00410044d0305105c0c0c88644154028 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 66333303 1250 66332053 66332089
    0xb0a03061e0f24030207060609021602040b04020705120a030617010608072c04060b0d0602040302090603060408030f07021603050d090807080a0303020f0f030708040302010b040c080c07030909050109060302 90
    0xc8220325140301003440f41d248842d5510703001d40c5a011902c6c0445c080c01c9241c028100300c0e80041500444200480350640e2000d000b107805012681200d41417004034495210040c0c900d401a907100d06003c8281002840d110317490303180002d4115510800421000458000c0d80310a9445103402c0050041c01c108100150803650301a242c0c1c10a040c03607030031916108a00b0809955641c0c40014103000751941314a00c4c0040c09803d001e4002107502c1c0c610f00075401800224440e480d440086845402e0008495125035800b015086c5551a4081001e0111000809010441c829850303d21282015082d6400046108100600802c16110700140c08040f05d0380000110354454071041140203400552032401c25010700303006035a64000d20080080d88920240c1c41c002500000c10701c4006075201450a11860080d0b0080000760622010001038070b1400c01c1c0701001450340302c00f08070507010f140c8c000d12407680300341003191406030ba43d402c00060700c409a2040d8041c0b542c0d00f50030002d50034415200c1110140320 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 66334553 1250 66333303 66333329
    0x18010207050105120a1104090605030f011503020d05012018010c03120c0c020a080d02060c030103021011150a0507020c01080f0a0c0c060203040b06010e0909070b0a03061e0f 76
    0xb44540a481503001145240390003117482134600703604c41222581b030800c0b45c55a441c4c580c6140c0d005403287e442200e0107446000120203842506100e10807a81030031400716091507285408000740e14920030307000c1e43c055584041c00700340e21200f21043d48074912002c0f03120391128a52061110403141c040038140c10720900d01e03848400264404501000020400340004d4100d240f007004550424010304002e42003000e008010901c17074400a580e0410b41380c240c1c00c03664103585900c00c07001c940c0000c2c1310003500300e1510f040c900071087c000c0d54484e4070722100340200ca2503610001100300305a90142c038000d05c03460fa102d092001855042c032021107414400e0900399583d04003c070b03a0401421004000e50706603903440b0301d10003105114540d00300300c4541140c1d003992a070820f42024088510b043e03480d6400300d64400c038543c0550a14481c014420442d640c0540403940c601a02881c95034482c260090402d59201408a510340300d004002021707403410000d808425007090207030518694160410102d260030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 66335803 1250 66334553 66334559
    0x301090209060405090115030803090f0a030e090402040f14070912230a0b190f090209070c15020408010219030504051207051f0b0f1c03031a1518010207 67
    0xe4520741942084041d280001c0300c0c2d40380765106004268191005d8014011030b2000000c3c46454000345000b907001c1000d6804614031000115615003040380010040340618220622528114641d603074400d0002c0c0c00861002c808031507210456400c1a41e0011b41880b000c24070a04552002519000c1d0200380d4102200500035200c031005440c0c3c1e21050040700069003641c0120080c00c1c04806000355100e040b030042420540202d82021a070b05007855500ca142c602a1001c0704403a010307416034160040d150f40c603244c0b00e070345084075000d109070300c203130303075402e8003040c0c40050801e01e00c0204010140c2000050b241c000100070302054118420003602098188001e0001182001c00c600c44104e21007410269102c0c410b150a5040a028118424211400d640960320040035a0420320592100320740200d40c48442c0e404011080d04407007850186881c800044c0740002f4065032001040c45080082242c440c1c00e480005548480c0317503040c2c5102c0c04008030700c01d10044015424101d030407100f40040d1442c130341 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 66337053 1250 66335803 66335809
    0x12090a0309050427060209040c021b0105030613021815071109090601060c0f0501020a0305010806180607200a05030405091e040303050c090301050702070609060206010f0303030e0f0313030b010503010902 89
    0x713011a0200454451410f190800c45650304544084001030710a03c0302850104000e511392804215241c0114100020307100d6540c4100112445142c004203c107032954410f400c400c0086d0880c481080100001110405040e9950611100a40c8204144641d100000d190144400c442e00c2005800742004000b446074004010502e42c0c1526401d1a0180a920b13107824500c09a00d180c030400350080d44000740b1041420b903d60003850603110f00c801280c0c0ea41d264012004851100b0300d86030040c582054020442480c4526040c0c031002d40d51003204413120001da540300c2e041000c400030440d0b15a100140c10040742c02d08031001507101d00e00e44c10404071806410310804103000c0040c0010209a42d0b400003602d40509201a2095280050001c000a02e008480607640d81c010340180750105003e9100001c0e010300c006071007416940030b0452480a285555004d402030155281020414014002e820345075140c1000581180c0f0020f60300813200503d5410101c410041c10303001a4000d0341030030751803009a1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 66338303 1250 66337053 66337091
    0xa0615030e1509010507182d0e0a05040b1f05040510091401140d03050304020607030903080703090306110c0a020603100803030903190906051803010b13090204051008070e0a0212090a03090504 84
    0x1400c2c3d400c10b004024230101c000712604564200c1044210840306124510000d9404544210711686074a00d1039102c0400d015a01000203403414001d064601050145085c980c001c0d0390480007d8001c903100c10345842000b01901e4901c0406d040c40104030700100500010102d103d101c0c014241d810002d08502e90300d00502c64800104081d00a02d0002a20300805114041e002d0055411806d05501c58149240040881c5028882640c10b00e05110340c441050018000312802002603100800312244168240055500020200402d100040000052081c024030085202d1012880a0b6075124800070048400f001410450820000711074010b12009401c80d08646140c005441015a00b02d400c8002902500c616914250000c1200c0f140e900006100c0e0004143c0600c02c480a0101c2c1c1c2d07564503281040c461074456500e8903849554200181d0040d07103115904980d10000141c0b0b01054111520038504051b19a143c50707501409281d420706910414050291208072804e1021407d8050000000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 66339553 1250 66338303 66338339
    0x30d0c02040b0f0108010311030c060406020c0102100b130b0f0418030908010c0509040b0f04060f050109080a0201080601052508030103050f011b030c032705060a0615030e150901050718 81
    0x8d0301e00141d250809540030050f0703e07050100100359035600d03512680025103580480390f06a015219450b04107400c22041e0107001c000000103041d1175101403052402e14058100d00ba40346801000c9101401030741d0b251350140070035903034440c1801440301e01c251a000300540b0280d4040303c280d03417500040744030281d40401200c0d0540e50888000c180a001e100c001a605174620340c10030b41c894a42840044c4020030700b818003080f11426202c44c410555100d4075591540800031000380022448800a091580640c024148006c00f01074203600074210b10a40c0c1c00e81901251068510b031201000410420100b0000e168405038040f00a0001a550425800710101c404100e402415140c48544080c580300350b000c122a4404000004801e01110b06000b40b01c005060003a240c038014840000c20076240c6001c1d050803645443d48100000c060400120014a104184403205018200c134441100c0c0c1095811806982c9200c0005032030300340054060114041002009040c00028204201080302e01e120781d105 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 66340803 1250 66339553 66339563
    0x8070e030a062a090812040503060705030c04080d0909180b0601051e1201060f080c030c0702040b041b0305010f0605040905040c0e0901090314180d0201030605030d0c02040b0f01080103 81
    0x1112a8104590b403020a05050208a140030320440141c29030310410304c004841940742528001d403014020025944924080c29405603c140085207000380f150000310340c0000c5050900f420151100422400c002c0102520000030700800428005595580304080c0c52500c031500b050400c0035299501c1c50314800082c040380c1803003000f06100000da0001d041c1c4005454801d0119035660300c902e400c090390f00c003083c024440007443d0303034403a018154041d182a9000e401104a502d0644e40c82420400715548442e000300d0300141c03030741c08a132036540380c0340568009000c0300305c082c0142e40002603004048410503405404074a80013841084440d070010122801d42d0714102c008a45c80d40c490a0001c40440070f54030840300c0e5803014080145120040d4031400076248665600a00501c40070b01140150188804c2d019120400181041c40c40c0780c0705490b078880600c181408900349a071040007074200301c801155040440c1e6000101c0d0118a054801c011800303808691104030502101c000074540c0b00c050100501d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 66342053 1250 66340803 66340811
    0xe0703180501090605281121011401020105070516080f030108010c030e0309060403020108090106030f080403121701120222061a03040302030a1101140c120907140d020f0a03050d08070e030a06 84
    0x21f64103910085130785003000707c50440711a09001c40904a40300c001d1155a02000300310400086a600c10300a50f4000d0906903107031810000d0b40820744000c0511084120380c61901048140300c0020000040c0d4001e1590600004148010b450040e0540320b4041c4080c903030350010401c00303e070b9603191000d5605482d02844c3c11001d030758924095a00500fa6900081e1110b0712100d03480e01000b054000510a8a100320600c0b907c0003105001036400001d0705451643c6070ba82100180010351286450215075400100310385840060005080000c4110004500000d510f401d02803110040d4620342c0700403071352000c40b5240f440c5040d0720025101d00818020390300304030a00c241002004007d401442c500f0030401e20810345400c020860f05015840700060b01806108000014060f06000c9114801c50b070405074583c0c121003501040000305c64014404a03844041030382c03960303010389a00ca205070140d40b040d802080607402405014184000041c1880100101e496150340240c80201d569030703503d58052004070b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 66343303 1250 66342053 66342071
    0x70e0402070b01080a120e0307061419030f060602030711011b0c0605090405060301090c030312060b0301091401120f02220c090603051608010e070318050109060528 72
    0x200603104460010380021032140000c590714102090741050588a5074015056800d41d04066030703049441006158143c00c503100400006000f402409000c4800458851410070924072001c0c5504d103c1e140c03c00003039503d284085004c0e5541c821100944810f0000314103103480356841c1402c0f010610005810840764000e0060071106c105050102c0b0b60f480401504003a46802c00180183c104004c04e600c030714142800b1880354201072150000c0399402c02c402a1101d425a1000c0d40e1407403600e100100302c15525080001c811140501031406810407201c0400c49804110740854441c07010307000800b40d254a1490040000c0201c1c0801522943c15078580c2c026100b04490802003d024500101d0b042d41407031b41240c191170344062100305a80d01a24100190f40f20100100304100b07000b10100d001c2006680140448560303c019075070320228034640401c2e1810103060142510041290848040c0e4403101104100b201d0b6001d00341d40203544141c01303043c000e000210344042c250481c01d07a4444035541d403050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 66344553 1250 66343303 66343309
    0x8160309030803040506060405060a0b16150c0e03100b100c0c0b0304030507020315010b0f0313050f030406030f020f0919030b1602010e0c010e10020715030e06070201090b070e 77
    0x820300440d04048641c2d1030346828102103071961070494205104516250000e05607150000150301900c4d80318115a0505808035050342036484810700544107110b004011000c1461030303000310083d80485a840315000d211340402c5c18500340e15588522040c0c0c1c20702c1c1e405a080d803200c040b80700d400b5410345000c0c0082c904508000789602d42603080000d502100000f00010f054001c001400818800e40855080c408840300094849c1c9003806034095044c81000002540d0701c141d009150801411507140a1440c2030b03a590383e00d000400e0320400500e400100b0104441900741c40b92001d894000107040d40340a01607044641c90f03106881100f8030600e4a0b0081c900a24005141003001d148e20090f98004c1c0c0c28110940c509640d40400141c0040d0b0804000c0c1c80d07032140103d6066444401070311074208041c8008104241d4059820354001148202c500c002180c10a40e00132043d461010b850014401c1007914099081480080904040d68140306556001900a4000e954410640d2800b40a005488400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 66345803 1250 66344553 66344567
    0x703060b0406030207050c09100603020f040504050702061e0f0402010507150518070f03110f120105040b0609070f021b010c06020f0408011d060c0d14040b22081603 72
    0x40410344640218020aa01d0341682c0106804d0340074404407299400240100417000c0030840354850700c89102c40c4d08022150091b0050814021295680c504190b140c2011904850b0111001001a406101480302c4001da10381c1d8425400c2c6d40d40c00f6101e007490103103000d50901c0d10180c0000c0c10132900041e200c05108804002603282072040c1020710590400c07a14845c6c1c581910095821180901580000c0b40c1c82d88200783d9040360751040d0000d00e44e01843c8100241e9200d20fa00b055088241010569400b03007007031107114420740c4980c6170240d0508140741440b00c0c144006208d1b0033482442c52006601d81c1e00080c2c8101c01e03c0310107400e0345074515a540100c2e405404500c1c000e0801d4002f0400c03680782d00d244005081941c0f4018000c01001000c070003403900c0b1162400d03d004654000b4800309003c01114401410f81ea60210008100e40d500c05082e49043d110032102510401000d106010128601340c00c000070080c610510105c1421807a168200540300d900b070084c40c00480c2c2641c903400c241c043c90f4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 66347053 1250 66345803 66345809
    0x803060f1f020601030303050a06140415120609050d110319021c08160219120c0c0b030403030b010503070912020f0307080f01050106180b090f04060f030b060402030106080f070306 79
    0x1d02012100c1c2264060b5032903000703020131004a81081d0004000b86840e00c46c0004407800d20704440d102c00385d004280300003815658803c0d02d080b00c04d901c010410f01c600d040302704007051103081b0000b41017a40781403040c146050b0f151000c0c10401c61507003410341300100105454003940070f0388034106004041007050b41b41051140300458140040c0c00c25807a66504404400c2c420001003036004510501c03940200c3c0c850079440c1c00031004407000c4c031000010502c81c00200280002d00d04202d200600d40b17840381413484440350b0244022610001c01c02003010343c94002c001030401d00303090160031810700075000b801c502c0301401405d9410036455181801d40d61100d0f800245140b0240c01d8075103845d1074083ea01d8072900310502c041c009600340000051501c4c0308102d00381100d800300d2008004541007098914007a40a40740c0b00e988100491500c40890340c5602c1000001c00450041620903491807520201204004000e40c0c8518810303c0100942034200c1e0840307500c0145041d0000159035512400c1c2c00520940d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 66348303 1250 66347053 66347089
    0xa0c08130f080f19020108010312120614010f020c060d0b010e0d05030309070b0a02060a0509031308031804020906030c09010521190510170c04050c0d0e0a0803060f 72
    0xd0000c1c9141c004900164111070500a5920a0b461054400d14080131034200a0000380d81c08010070100c0c0c3c001e010300c54010064507044d88450700803070015050302c48a030042a0a01001c2518410355a00448007174411500b03800070f4040e000384500040c0940c05a0020707824040d4540d004a001603100c1c61201e07030030710f00081c0300340508887d5082c4550341e40c10440e10000d40780300e400303008941c405094054410b84003d41d17000b01841d50f2484400340103800041e10f07003000b611050000c0782c445a004018800039092050003181c41d0311400b402c5156116440c0881d41c040c41c81000301b8012a203442c01140c1c4c0c40528040010303a03407181000100c60a100340240401e07118000e0100e5000d031280350100341d024030801c000c01000a4500b840d540221241034866696120101c3c0c002c1040416a01c0c40a5500f2004404d407040f0800c0840800e065074001c40c0c285442c2000003540348041c22561040c54a370084840007001806180e070340d408880d02c80a031038207104a00c0150345c030203150f07200f102018001c1e25070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 66349553 1250 66348303 66348329
    0x210c0303040602030105030c03060f0a020a03090f031d0109140423010b0a0201050a0b03031615020a030b0a080a05060403030b04020708070b1918170415020601030c05060a0c0813 78
    0x5042c1540250020f0280c60b200c0c0c0500c01c03188800d0302c2d002860b80c1c01490f00075035140b05078030f84214840c02588030004150500d038945500c000403407640302d0401010f60081c2c94501100500400005200b910100d0243c14000d080c41c01b440454148022481a21815140020b008a120302e00104004c142c0606050150500700086000c000c198040c2c0b682e03c0b0340c0e03002800540c680007140c500703407170054452079050b0f4024024444190205440703030802c3c60266400301d60784a540151a003c0e42c0c0410800c0000ca0b840300305203075540c1032030a80d0a0040440070301070624180b85071384203900d885002c0c03c040c04040e151b40000d030655030b60358101c40c1718039070020115581c1d203101c0c60a0400c00350708490786400c1c2d1300c8113598411160701314095200c0300d00901b0004000766613a51754106981e90824015003428505000111300b14031851440364109549400034101d561540c07901c1c0c420342c402504101c1c003402c82070004030140c3d41c2201e82e4208213584083c450352250b0302c1150200360310038103030f214002144178 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 66350803 1250 66349553 66349561
    0x60c0812100303020c0103090b040b060a0905070c030e18040321020a111615200318090c0c070902160c03060605010e060306030d030203041e030f03050f0702210c0303 73
    0x6501400049070f219400b0b8940c20340c5a4801581107610114018000b041c00c1d8001030700280801d060700f42d1007400208905a0141c07100301c0c034800c0311011903404000c00c0d0700b89d0101040c5070300548882e810540803109200200764110034000007030300c003401c000d0a110741c40c07031004040e410020202c0800100c0348400c544640c0c1600d0024000151110307900c24030b028200c2d60400403890b211f203031070540e90900d03070081e40c0202c4104100c480b140401120f1034088180c41d00c0f44611003041c0000e00e000c00b04580c480d0461705000d010051307102005070644036190003c015000c0001004140300d8110303440c5260050b250087c1340d81c400105000e018008040d01240e0341d006c41000010390224058503401e81e01d8210008903001800210b1001b0764149501d5480440c2c0e640c174840c401c2d002142d1040c8114582180c000c2003240780c0c914a0015a01140421081e044c08200b4540c1445115401035103407213841100d00f451640a529918010594200091940000035201000d00c0c100c415042c0480101ca98a2034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 66352053 1250 66350803 66350821
    0x4020322060f1a0a030201050a0e0901080304080111071a100339060c06090204020403050d0201090215030411010804061116020a060207050105270a09090c050415060c0812 75
    0x10700480b10b482042e03e000804201601643d0102c07050070000707480e02c8100c50441d0010f4a10ba04000b601c1000c20410050407581900e1f107407a054024054000290b459034101410542500c08141d100322801c503003440800003003440c080c0c2580300c10721500c404d0b030501e4a80011a4140e8a10b40c3c001a014001e600e203210300520300e0700206404090308408d505042c40c52610311014107105481040d00017809440807102003000d03076000842c180d10082c401464182d0305d030f54440c20001c3e981b82e4000981d544402d40015802d104117200800a0b021410314650324296039103010b03107000e2404150412070100d001604000481d4000340700c00082040f0b01d41c41c1c44146040c9004212580c40490080d694600e0000d50f203400040c41030195041611914200341c941510040440b05115020111650485101445403200c164100203000c1c0c2000204102c0100e060401e50a041c580c81345010760301d0b06902500e004802407100c0b055852030701d0b1241d501d010720305107110103000c1c0140c90019289203100b884030b0b440c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 66353303 1250 66352053 66352061
    0x303040605010608060a03081612080702010510030b01031202011d2b0e0d08040f0605030f090601151b0b0f071107231c060e0c0d020f0402032206 64
    0x80d20401062007242e88542044071550307825243c44d50001c0046200348001004640039104240410345107121421480e01c1d00c0c46c420041c821030308085610318003403003c607a90a02445034002901c130360400314580b0f190b0300c41c840740714144005010409802c2d40300720f0b042e100707402603034101503400c17201c001e42112050415111307201396010802c850401c001f0006034802d0b10a0310351451020b1340360612510007a0040c0462288054001c50b9940002c010100340c062084075914080c1100780d488980782e140000403003c0c449006054081582e000c1d000400c0000c43c421800760009000b07250074100503c2403507404100203001c4400405c19020302c010820105d9074025200d203d0091503844444a000b46102c1580b81c40d1180100340ba04130701105980d2140307024120b0701c070003200040c0c0781e003808000c40b80141c102d504070700718215011502c0751811801103c0400114004103c125491620b40210b5400140003c0700711078420302503a000300000c1c0d5400829888400301c110409625802d04200340307000c1c4010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 66354553 1250 66353303 66353311
    0x90a0212060a0f0504050604030f0507120f030e01090c0302130b030f0309102c120d030b01020d050c06010e0408040b0a0f0912080703210204090905010e0105220309090e0303 76
    0x943c40e1440400080d2403a010355409140c11401800e41501e07161001c461001c441d82041d03050000030131401000480741c1c155005a06103a83e210150703000c05080007001e0f212540d110b08916030500b6010b20100d80c0c002c0c00d100c1101d40c111412800e111003800b0318000703494100786030380c0c5c140070703c5803004002c00000c4002d0040407011034040c2c5001548840554071404d845140c54000b01545401030840d462400006d624900700604a100c0030069091080c074141062802d03900080d00c40c40840d00c5542c041045880c0c805003404c01c0c80c01c2c1700714103806a9850105101b408560846600841c0510804804440c003601c0710301085030b9203120f03040340a03241c881c180b84a90300054000900061101c0c4901c556402d0039032040d40c035132038404c0a0314102c031184010001c0c2907650017044010003551020380700030001401c3c1410080794800c5942031060860b01d0070350741000700f80d040c1010810380342003482c90b903808120742d01d00c2040325030340b07605013150400b4803034126010651034104c030031b01032a2000020303502c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 66355803 1250 66354553 66354571
    0x711010e15062b03021905010b13110a0e040b030303010312090b0301060509010518100c030207080303010821070203030409020702040c0c030503060607110303071b0e04020f040203090a021206 84
    0x903585621080c01820710300f1011140441d2840aa10301c5070110310350074100c0c21400391045502103600b948100b00c11502c01c00044a07980c5d5600700c82d0845040201040748078118013101000b61102d10f040844c21482031006213010411450704201c2e407640c03264000e02ea510009402c0b640c0782c0da1285044101c0a60f0fa100c40c80204803c01c0002424122480440e0705a80d0a50f513140d003000c803180015200e64000340c0000115120748100c03c0c4007615aa150711500b81019030701c0382d1040c01141006410700708150042d400540041005205003070000800c240b0313100003003180540c1d01d9502c0592100c24041c2c0800250f041c08001000100d01455130040d0004a0007160300700280428032106032210700900030000c0120301d041c03002412a24124002d0b010450003843d40707003180c0034860002411075001420440d51050b9460390b94070155a00c840d0340024143c0064240a541000c0d0001140448040c0c0b00303901c100c3d0000002100a0401e218844100f81e0260281040c4844082041d48a240840d01d03010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 66357053 1250 66355803 66355843
    0xc1709031305040207060b040c02071418070c050a050105130311160b090d02040e0f0c09040503090d11190302090603010c0c02040b04060e0f0609100b0a03050711010e 73
    0x2140240100031501907481c414507600e4464500000c0c0406504256025076039140e484c2207015040e11140540086610564054001942402d01d800c040110f1600203034050100314421b405458009080c03150045114244180b50b8045031405900c2c00e02d4508004000b03509007828030994900401c0c03c41c0e0800d1003500c6100d20184580416035917510950300c3c00300015a422300030402d04003058024214640050548204500c1c0707900814240c031400490a141548000013660540d1418070041d0044442162a0f060320300b42926025540c0c01010036080c4a00344000c211000c1020600e030b14045c2410107070908108800e0000c07003080d40080c1d0b10041c1c0c010f440110004401d07181c188124001c0c44c0590300c1da484101120f030240401440b601c0d4040b9007143c0c0d1410017164101c0c2076000c45109020710b080910091a2540500201c2c1102901c1c0c2010b14030b00701c000348680c1c1888003c1d140c108429141c0014680d50714641140d036071400d80d0710b00301c00c0d528002032260030f064003240e21050240342141080c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 66358303 1250 66357053 66357061
    0x20d050705010f08040503090d0c050a0308031005030303010503210d0615020f030306010c11060702210705030c090c090d080a03020703031a03030a0c0303090812070e04090506070c0302100c17 84
    0x91113220044030020010380040160a070640303010360002c1d2446004a400da030113191500045259690f05800a8035041c04c04020000c1d051482e48030703600034104c00d8010f182154580408030342e032040441041ca001c8480e60847c203000b2555402074540d5110444000d1040c5590f605202c80d40b00a0489601c0c01030103041084010b040c0700004403401407406950354040040380d52104031501c4424014aa84208104059005a640c0000d11401c40a034080b032000444600c210052428032281c4c040c42c000d4009541185143c0d9510155952103c108032055903581c010f200040c1c48450b4540f401407030090042400c03142180e00d0340c0a0508180300e130324104044541c904207a410000090b00c01a4194400c0020008040c81075000f21503152082c1008618480d84d40d8840b121034000d0500680701304002010401403d500c849149050042074404100b10100303521206d446a00040c10301086c0700003d03111608151007003107040d0100c08601400c00c4108805500200400001300c8010b90100c4210042 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 66359553 1250 66358303 66358307
    0xf051614010f02010204240f020109030c06090602070c06020f010b010c05192402090a06080708010e0907030503070b090105060114070618060c0908071a0f070f020d050705010f 77
    0x1401564000c0d01180a11101040110341c421165644141155000c3c440060740c41300c000c92108034014085081120250801001840070404951071000c40e030610b856040429000b86901d0213854011101048400c014180b02c0040d00c00c8500080c128042d03080005003995010070a072041891100c02400044410801166088016031028026410030301c02e410203210300100301d80c502c910503580c00c0b48420a000b20540605402160303c44d5454001030003c40304d1504400e11802f80119080803200c504141c440107007080d405000d881d0100c01d00d10041503004004001600065603c40126940e51005103008014910141c4055103113600701408554198007031100e2920085010150714240840c5072104000b800c1040e10412801d164101c076000480c20a02552811617256260890072a1501c074100389007802e5584030300b4100d480d0480b0307084598440d008032412075120001c0c480d190f41003428400381425055070000c0d4010001501e1408210011403a84200c0e20262241c071400d000c4400c1c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 66360803 1250 66359553 66359593
    0xa060506011d030c04050901090515060a0b0322030203130b07140705030604060c21052a070807020402040b07050f01050c0a0503011214010f020c06060609101b060501030f05 76
    0x1040d803642007811390024500340340d4002980040d15000210710040035441e01403c01c04403140d000d0118100e042004442d00b0103500c95002064a012030b186103152403d000d41d01d00e80815880b80c0d0600b8805096001d040c82007094071001d420400340e0010840d0745146054040d8800d0008a41e203401d290492940e8201c0851a441101c1002d000340c42c40d50713035640c1c0703030380051850621701c005104100b00403088410401044203030051602d003002451b0304114204102c1d110741c3c00e0034840c101541c120f51500391840401a15a10b030340c0249030944803a900d100140190117150000d5190010103d41f0809201000503441c0c1d0703210240c0e00030080d648680789984078502c07600d1b40e42004030b0030400c010404080c0d8407c8400c40d69003e107000350720b0b0000050120382500d01d410310500e0b02c10340114020200c054280803858000400320b0340545068208008079400014015040f402d002e4001c01030395002e0f03801989107034465480441044650303101d01e481c4200d43e6030100155a28031800d00d1900581e106540c0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 66362053 1250 66360803 66360857
    0x9020306061b01020f030f0403110a080d0c030b030a0507170601030b010b0703020a0b2d130b060307180911060c06010504020a020f01020711010816080a0c0309050a06050601 76
    0x101c003070300d81400e0401c021510728540150b9500d66508201d4103070014007030000756014241c204080b2a0341d041c02e0800a00079502401c203020b65400c001c1c2044001140d440803203a80c0b5414080c007107034070003000708164010240c0f03c3e4450f40500800700b4203010484085002c1c4207036013114607003021040a100e54159942e409000080c0f55a090b200180300004803180502109486441200c0c2031030b10035514592140c4041e685d4490701c05194082d142c0180c0910704800381e120313031090443c0061510035400c0003070010b00d0801030840b80300d0602003505901c00b4001a409417000c0c02e505071403040346040040042088040a032218041401c90100c10f00d0180e044038a01308013031004007130507401c00c020000250701c84180d1105500c070702060700e86ca84200b03002800b507043c00340000121800201002500c5a40d0003002c03650000503218185149079048130209400130707415040011018860a03040e0028004280050000d1150042c808204016500954031880e0203996282280c010b00103261072080c0392031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 66363303 1250 66362053 66362059
    0x607050a050a0c06022502090703020c0604060c021203040302031c0e10050a06050a0305010b03100e060711030714010b030d0908030a0e13061725050904030909050106051309020306 79
    0x1125410242c82841e0641005004004c01440c014104003483c40c44060041306900c0d0440111141c429450040107490b4822280d04080d49001645012207890340001030001300120343c1c4400f641402d6100b080f540300009a4203400c1035136824203040103036903504151514a041013610044000e0b020311401404028a48a0010a96020080d40043c0038240003488540700035550440099140d0350f40218400440c095000040c08070486018181030200100d10071042c2418041c120002c0f03c000103124bc0e20000a00e4540306101c61a24014150f2150750341c00340000b2081c083c0c3c3c00c410071065001444805e011000c070b074101b404501083d03030084141d06c0307031090603001130044109190180c004d4440c000740041c0449a00180302406000f1200305411603440031541c2500d8880034101003080010711145d07112503640020031200328030412a464004c00d40248031200101c3e0030940038603e00c0c0054004248184590360310342d2401840b80d003000801045580c420340c800907800c4010301c2180c1c080d042c05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 66364553 1250 66363303 66363307
    0x1207021903051b0303070c150c0c080c010f05070905031b060406030b0406080703080909010e01050d060f090501050405010c020705060f040509061c060506120105070c0219050a030b090607050a05 85
    0x5460550300382d004400d01001e403103500d141d0b4103803040c03040c4005c42c41034501d5250b48210807511b0401c0100d40039840811006217180c8070200c0d01180e0022700c044e44240c1c0c48200f0300d56070446403811501400b20324141010b26070030b20381072103401c5400c0742c0d040c2c0a0b580203a049514512a0fa85580610340c04944440e811400820080c4a103070321079001000700c0308019002041c040d40e1043e50300e1509445034025a8040c03c041480d4405103460074989005288407469488030794100b1001502e40c1c040208010507503543c90200901c000c03840d4200242082d04140200054a01070038102d0190020341da84800600900d103002c0307142c0c90600140d5801001e400c0302c1c9828942032905100c1244070143c6040e500c800002c60101c000c4041100000080384501c5010800d818036005011642840300b03174064590b410b00d810422029880079102c50307202d404803000711502c158040f00c1031000780141c00c0260841201c480102c01d0000752400a4003a89202c2c088960300d0343c400703104540c64003807648450002841 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 66365803 1250 66364553 66364603
    0x2306040b060907030b0a0308070c081f02030a060e15030705010512160207080a0614070309031d121e0d0c03081305031b060901060b0c0d0507050c0303030c120702 71
    0x2450b100e640407846080c0000c4408164000880c02800380d0300032960b07168001031040c00c0100c0d040710b42c001401201e00420460315003c41a090840b58a121000b4140d03020001807060322603500140014080740180c000d560030943d0000c4403c89500029074040d11495500040952150b811034568404906c0c50340380e80d8035010003a01c4200e140f20368020440c8600a000320300074005114002c42e030b610458001445d050040e4800840c0e940042820042c946080c0b055070100b1780003132480741401c918800b961400c03032200c400114800404009003d46e446110b50b8440009102420680800130301411180410fa8182003121480d2280000400080b000c0000c524200341801000720f200d4801c009481c02c0500300c010f5503200c5100c068424003254080824002e41c05020711a80000e005c141840628020741c2e20001c9541e5203079507203000e0800800080e5441031000a00a000c854031008041d00d5880c10003003201c00c6140c1011401c5044031601c2008109a10700004400d800640051244c04100c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 66366909 1106 66365803 66365809
    0x702090907090b0d0b0c28020304060201181205160501140f07080103110f0a0b04062102041a030414060106050d0c02060c04031b080a2306040b06 64
    0x40c104c076140400c4004000380c1c0c2c00700350340c8200d82c2e49010803030310024042d074888540c3c2c0305c1c0000d207076000e000c0643c08070042044444d50b5000b80124601100150414103003030100510300300031101d1138040d260040c4043c2a030450086005040e0020589801c1d003075401d402e011074500c1c0e424004002000c40e00c07208043c1c1242c1d061800301104d604656940841090301c1c00214031039009031046010070303515880c018028100d1507116a4441e0b90761a8054551f0401b241061548034481d01200d10a00c4c540c800d49040360100302c10208032007416040c00940d0b600280003a00c1b8480070443c50743c0440790400009008203400c0d6110381e47d610303507980408226403000360810700b1900160103001d0820506001d440c146ca4205041001d90798180180d59807440302503100401500907084800e0600c1340401076403552403038200340d11644045174400d841c0c589908035401007100c6845004282181 = true := by decide +kernel

theorem cover : BRFrame.Cov 66187053 66366909 := by
  have h0 := BRFrame.cov_init 66187053
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 66187053 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 66187053 ≤ n) (h2 : n < 66366909) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
