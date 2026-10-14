-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0875
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:20:39.648619+00:00
-- url     : https://prove2.me/submissions/4c3157a2-113b-4265-8b8b-b3ca5bfbef69

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 157194244 ≤ n < 157374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 157195494 1250 157194244 157194319
    0x603030203270607082106030a02040f09020d11040b060702060a0f02071a09101b0611040320010305160c08130b1201050a0603020a050306090a061208180f030a02040f0605 75
    0x500d035000481c1c010340301f600010082c1ca581c0819400340005802520ba0310003940b030b660a01c40c40140d4400d102c001c011400b0700728854004170245c0078442290040804288150700900010300165030b002d0840c0c0e900d58081c81d010b00181061503044c2c0c90005590000f10a0402a0110858123158000900005da104991514000503031440507240c118550034010b03e0654994240804620290803000c032100c0030044007850a03640791200102000307180021140c2e02c0000711181081d69041c003031150007002c0b01440100c0300d2007036200170f4031949807035200802c0d0703e04c0814061b16500402041e90300500c1c502c28690b1f500c40203421084940071090003814414108907002181b014428402c1e9100d21102d512014915243c1c0d20800c04821401000c813820251200004151255050b001c42c00140c03260340210b0b1961151720084c10301d24618a80c042c080d11300501000015600003c0303142801c0c0c6c040d00d00041131101c2d85203410192240f0742246400c000209030701c2c1a142c51982c21044020a81c1c1e203c3d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 157196744 1250 157195494 157195537
    0x316060b0123090906060306030303070f02030d0c0206090706110304090b04090b04050c130e0d0c05070b071a090d0504060807360819030f020c04050a05011503060303020327060708 79
    0x41ba07020544001d034051f4000e000207100b00e8087c60a90f01004a9801102d08080100324044207407441c03405200b005801060900861040805c0500083c08050908140d081243c0c10465520b010b1486000040303900c070250365105e074440c0d6014190554100c800c2c107040c1c7c90603080c05552010340c4400103024000c2030300031950204040c401e940c0310300488009040c0407040010120341c103001186090b601070250b04d500141201064005040309403080081d04002c103400e00c0180c049100040c040912500329001d820f410603404412901070305e115040c481041c0d01c8881003207a2038140c40c7c45034039900d620807424616503c402d0584070100c100003d00c0315140d50f00e8052180e1901130400710001e13814103010000700041d00842824011030f00e036204403000144c2401c00a8180c92095071203200d56030741c44006011010600d80d03405040c070194101402494550341e4001e40d24490001c00414003107584007080603d43d42c801c4030f4459080c008080726116181c40c2000002640409171024040003180351a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 157197994 1250 157196744 157196749
    0x2040e130503090f01090806090708100605061225021f0608072106020406120c08070903020609060915030907080a0c0e04140105180d020316060b0123090906 69
    0x60100c503951000255040c01e0307102c030500c20015a9045000d06109040801242c0900c0400c2074600c1001e04100030000c1e01d2a24901c14144003841501e0a800ba04080040c05503840e403000700c5440c1d01e0460848000c0c0d80d2000030150041c2820741c201500320001000c030441e0300340c2c00101c0f1800300c0b40a00c10101030007031810016040750a40e00c10807007680c21140e420041450000c02c7c0c900d6411a040310f00700039000aa40d00c00407a845900414041030030205d03011441a01407141e4800c0c5101030030205101c0c1408200902801991301c0002c0c801c29001812001c0c41e140c00054407003142c0d0281c0214040300e8600d048400a80048454851a120b861400141c003000040c040301040d8110000a42c26818242c0030010001e00600543e2652030f00740441e41804000d110b007030311540c5d942e44043c61007001100c4c0c45080000358045c6c101154800d00039082e81c0040e170b80401040c0c2e60f0112001851000000060329004180800c803107014154a40f5112054402401001c1d801c00840d20200c04d82c0d1807a08 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 157199244 1250 157197994 157198021
    0x90e060a030f0b1f03031d010c0b060f0609041107060b0d080304060e031e0d0c05030115110a050106030b04060e030a0c02090619060f110a240f060902040e 68
    0x54034a02ca0070920401092003c101d068201c1c13031308000e82d510f140e01c020321000c03042c205900441c005440b00000074000200c8108401c6148802d203070110114140d81c8400704400d00180c00e40748201c82d1400d00c0e600a603182e601301c03890039502800502001e0117000800c04190000e41003a1404c1c1d0500062a0f458601845031640540c1d0040e2141d0075a16641c540303200038150011030b40302d5888100f020302001548440c2403a2403020614a00c2c0c2d5580f000710f401c00565081c02d81c0542404010f2006000c2c411700c07a6038001d02d494540c03400070b1004403407401e82ca00d80036501c44080c0455290031408011300c55243d10302841107000e6038050000761511445613a0f80d00c41c0c410081e0003c2c50750300b2040018074000d42d59681045000f80940002004408088841e03030040d4801800301e400d880700c80e40d9240c0c01c4003a00201184030005004c118030304d40c039142d840c46542c0d00902c07009182c1c106a002c80d00501d07400304901e010f49030800c000c4180c81d101c12200950040c081c0b44030080402c1300140c0089000c20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 157200494 1250 157199244 157199249
    0x80d09081b0108070c110303030a061701060f0506090411040e040507060908060604052703030601030c03051902030405030c0a0f021216180e030310050109050114041401031b090e060a 80
    0x95a6035084c0d900d405080b50409070341e810449031080e03a03034400360142e136041010754040d81a0f59400608a03103032514880c0c03440740313000c08141141d042c91020040d00e08020070203170440341d0a48103141d90780150b20010b4003c00080f07000c0c150121000c06c0110345080c80c803001070300c164865011202801d407189016508203c0600c00d41c01140d0024001881d01d040540119400050003502da640602482500c0c40c2c0e084094482d144159201004005107580d1501810400102d00d04041103d801c0141a014000140052404140b500040400c00300403003002182c20704030518007600c80d041642d103031100758080d0050307050344103815a02000d035034032401060b034945814452007540c141d24603040303002c1410501a0b014040d881c0c3d0303078071600c807143c0d509100840c460310306240500308242c2800000b4040441c180c02090421603040030062060007004120f60036504604021070340302840c100105d0182060544080010050071104150141c0005803135042d0344880e04000c0e51592080d081c02811380061 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 157201744 1250 157200494 157200497
    0x30906070c0312090e19090f03080f180601150507201f02030306040c050408030d0b03010606030b100e0f06040b070302011103060d060207171603030b040902130e07080d09081b01 78
    0x12004909140a0042507094044d446040410040703070544407110088c90090703080c2c01050003130042001c0f03400f056265640c00454504000c90001c40c555102d0b0744c402c1c05000346600010030805800b51280200180c940e41035000700410819458034500700642c582c2070342414003485140d40b440070000c05001c0302c013a880080c5e900540c290f9840500300301c0038115440b00d602c18000100404a0390702c00600c002c00c041000010b010030841c3c0310105050031110603908c41c604052030b040d00d0f05819070311841510300d07801c03003403814515050910380000e4000541041e0780b9406140050300250440d03203480075003040da0181d00200818862200a018148400c4546540c0300c41d4500d02180044c0d141c0c0d000d029814011513040d544102041049040f0340d11000804024001500e030840815074940680c8003160002e54050040105a901040c1c084d221a007003450301684880700b00007c400700b0444400105698403c48811005401d000f41860301580503071185405500c0c0005c0c4490b11007041101c07886010b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 157202994 1250 157201744 157201769
    0x60c1106090d02060a03090c15020705030703020d02090408040f031208090d1407080c030703030e12090a0306020306010309151b020307051b0105040317030730050603030906070c031209 81
    0x2c40d03080206541c040124901030641e200e6040e000b0403401140d00c0d010745000504603040400c80c1c600a45050519401144603601034602480140c44680c0d000f144203505658010880d1203501d4811202d0040350090803846160520020911074529584000c4500640390100b15490f5000040e40310ba6120500c800070a2010309901040803905d00100ba0a0340140c5065050020001e0528156840001f0a9000980b20640c440600701c00b4401c00070340c030348040e07901490007480401042d202601c5d48800741c219540803001035a02e0740660055210a540114506899010340c0484030003040c0e0500304004000440c402010384034000003c44064a0b0080700400a200121baa003482c03032280800340504010f0f042c4000030000b03204035400074241c2c151501584d220301d4500d4005150304181464240223044c1042c1d8100900011864000c24084100000c10107650b41c1d40072034914451600202c1d0802c1e40000d024050002c4030824100f603d100e040390b0900407860700c400300c42c80742990099a080850 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 157204244 1250 157202994 157203019
    0x102090f010f020106080a0f02030106080d020c040207080903150a05013003020c03030d05090d05040311010c06060b160b0c030c030106030b0114040311090a200f040807060c110609 79
    0xd100c0711180381c0c0c2c2c0b4400030601c50746400c500c4d414411b20000441d0100041c1d80b0711b8045190a0081401400c8004c005061840c48200002d507520075440569004070b6000034080306003c404001c80c1c40803100035044401c404c1500b0901405804101ca05141e0307503140c00004526400c0d1043d1500144c1504400c2c0002c2e042c90010004458070010012015881502900411900c040c0054124554244c0c000030305440c18140103418805001c2007003007044010002400040d565150011040100707103454003000d0040d1a1801c0140000c0e0000590900045500e070500140c0c14202500c4503c500d102102035101c1a2903009540004e0358141044081840140842c51007981300201409051420060220844070390030056849a01b00b03644030481e45d6084005810440c15954010203085420006000c559005640342c00c0b0580400100003800245907641c4e030340301000c1e9000fa050190a5904240d41c0308000f030840d001641c801c40b54401c100541410382d14062069410050010b008140c0024 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 157205494 1250 157204244 157204247
    0x105040614070c0b070c09140c0c103201063002070305070501050609010303020d030b0f04020a050406021501030803060607020102013b061510050712030504020109080102090f01 78
    0x80c1d00d0040911500380c10700007900440ca45031812070013003d201d00d05a580b0311040c00c1c048110511a0403046815042151107002d0704485081103910000c5c0c6203c860b02c4011145809082c170480c000100c000d281051540b5100e0041c4503a01d94441d251100164540a034154070340c1d440c00c3c030922604010a00d2403001405145c0846100c070051501c06551030001c0aa45030f0200898001d00e800f07600142d4007054820070400240308070341c0c001004464075a030b03641c0340d07a400a6680410704000000c05840f420107551070740710f003406240941130003401036482d542c2c1030100403c10b0304648507960040c841c0c403041144175241e882002d8107a94018101c1841d540c0d034001401b6596100010803811590307070750710f40745075045100e80c080c4608054164003802800942580c00c1c0801140e9000c0d0b5983c2c0120b0280a80003030140c0a000c8880c40c140c4d529415101d00103400d80b514010200701820403ca60052504c03801d6140c0e00491265100b600c412000302e44580c111400c074007034030f95510380003401c0001005656 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 157206744 1250 157205494 157205507
    0x160b0304140312040b010302120328020c0901180c05040812090109050402030f0702011b020a06050403050705070803040614042904050d05010605040b040c09150c12020c01120b01050406 81
    0xc1e03091030480740b62a21a0070622204441201d0540e020804800180210b142c120400a2041b40742d000550420280010b8000040c4010b480c0c0264008403400800846000f844408141e5000810451096a4a4000c00441d0401c0c04001007094a00818060f00501650580b03051307503550030042450014070280d421903940700f4501941808011b00c0000740e2a17490740001c505c5646185100b00b06c03814100c001a00391800030300709210f280c92082198100030790004481507801d8000401140c2601d03142802e4030b1512030340c240a002400386400c04031311030340008002e00c1280c101e9503442d040340d0880b642d0030520b8000c5024104140c01a491045032140c205221440f40324a000700c440d140983d2030380011406d4034074000444041c3d441e048200064075045c4244080c86000391800d022801448070000c01c0000b050003550380c0d0084920240300064403a164441695512040b40088040d0700d0001942c1e6900c131842d03050008000d032925800d1620302e800f50843c11141078442c0c0382480d083c0102510314 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 157207994 1250 157206744 157206773
    0x10f06082a040501081c0206010501051606060e041b050607080a030e07051309061a030619090503121512060112050c090a02030f0a05041101030b06130b0c160b0304 72
    0x2800075030140c0e006569124856a030080c0301c96001041141c10254803c11440f11010709017056400c00801000a42d07004011601500c4161440d68003e100710b180400062005411914550480c0b4041004011485c0a0b5080d40d1800c1504000220344c0c501c100900b900c2801c0c1d005007400010310050700036900a80200c070055500201b40d860061b1200c02080341e01b05003240d010360103a254100381040c05658442c4e400c103035012840340e21801b820759011a03070b2200054081c0c0000100399100440c18141d961001c040307183d2100c01c0d01d940740455003035507003400e070203445070b0140595032428080d0038a4142440b031940c2c04868040c03d420b03882c0050044861031000000d44460180c40319845503981c030218464420600000016241e0400e480d80e10112003004200e84030b80c1c1c2c540810301c80490210241229601001d01c0d0110322804c0d428042a003901908400d2103418861840114030315504202416040a00000b11000d1100407042c5e80645007281c41042c15a40040000c1004902e801201294 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 157209244 1250 157207994 157208053
    0xa080109031d01021e010c11030301031707020d061802040506010302090d0b090a0b040803180a0305040308070804080d02060105090a02091804030c08040602010f0c05090105030612100e030c010f0608 87
    0x400004602c1c17040b90226280340340c6400360b5522494207030b1294000781040b410700c914034000c0d4103540c1141c6d1004809414404c03070040c1c24001084420031507558807030b07201581d0f0f4400317818404048000c0e102c0c0510b0071a03050480c0f1031810040040c817194071034800c0d40d80115005040035100c0c1040c3e100c42c081d2140207400824203000d49191500410344e45481c2500075441420007984d00d181c501c03103841c4040520010848039400c0b05440e440401c0c0d1120666007501e804c06651070307561039207107000c180c203120350b91144270700e0300407080421805070300484c01e5070486c1d03400e07182511260f03507041d0041c6c1240300719401c0d84d901800903003030000c0e590b0348080c04a520a10030309000d00120020348035440c00e900141d118a006079180d5411404080882c0181310420b140c5091141c1462401d100103041d40c00b00821450240561030320b24990b10104020010103054050400c00681400448080d100e0b030004246c140b05600b80b100b01e03070002c3c000b4480d071070848080001510103410802d09010028142048101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 157210494 1250 157209244 157209253
    0x2010305070309081e0910020a0203060c0a0c0803060303041d091e03070b090f01150f05060a0e040506030705060c0304030201031d0c0607050a061802041a0a05010c03090b0f04050a080109031d0102 86
    0x82d1600d8151f0882d00c3c038071103038008040c003100e50b204140c5464001410000142d2086c01100240c6411406002034160302c0503085807250754510100c0c2c90b5000e0388e8000d0104a4800c40041108046083c40d54000c8034940c0a44084402c3e80c00301c101c9411a03081c045216600420261010501c041c400d140c02492074010340b0264500f03082041e09444004500e0303203212900500c108108503d6840d654000c25040d9401824052008809010604818400c83c0610380300c0300002d00c0c0d42c0e018000c07600a014024001900c441107008902d030759400c1390000b28007003480c1076600107042c0780c20041a038010320504000d0018030841001d014003604500c808a82501c141c0c031200f00050103078020300c8403d100c1082c00f408900700c030b401004142c4401d00c1c0b8000d81310446040c400ca513502c503000004242c410a08009002c40201d1604036880d00d91b076401110b040c000800d51444c1d0050180041c001c0b900b0444410042c952205003184c01c842c1001c0380100420841200100b00400002202c501c03000140140c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 157211744 1250 157210494 157210507
    0x90f0703020f060c07050604240216051c060509100e01021305010f0c060204060c0b0c12040b13150606030b03072304060305030d05040605160503060d0618080702010305070309081e 79
    0x2903a260801e41200c921090381c1c41c042100105048580001015184000e103107091a40324589050f6a440c010340c0d002d03242013700455a41762036640d401c804d03036100d01d08001c03500d81400030a844445612a5070b0165040c00d04160142c4014001c1e50f0086228941c0d09540519010054604210b010528818032528085c20000301c1e1a503c0504002d02c2e094540a840488030316000c91401c5006101d00c040040c1030241c45c0c016000000015806503001326200c0c3d19031965686428038506c03120004001c3c90440d0710004000019400c004c046801d59103040c08502e140d2420951244224003e5011080031400a410f903116041003102412001410002d81c2e1a00e80d03c03080e0440c2d210001d0b03801500d8858050000b0040349200f0607074407030114400b8542118208500403c10b10002d0803c1d803280584041200900074076501c483c0034144113681901c002c411902c2c001c0d41d5500800c0c426400700e031401000034010741c001c0c01502c08031548007207800c1c60b04041c070b403400c807200c0b015550080c2030003401c9c00103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 157212994 1250 157211744 157211749
    0x3090a1505040302060c040e0f0403050c0708010902032e02130b0a1d060c030d0f14040c06020d090f0302041a1315050a14011101180b090f0703020f060c0705 69
    0x1480508401100d01066a1515040117850000090310105032041c04100070006003c44041450f0407000c441200e0b1402c0e11242401c49150158208000440c02071000020ba448015403110004c6482603098912550078001c981000c030031b030314054003c000c00c8c075500780341c1c0340d190b03540100b0711000503120718580c3c5504c0302c020030269000410507401040008912140342c0b146a41d9641100004882c11032500181c10034850f100e0141c43e05120b1a10740307803a0302041e084890f411490074030190714070004d803525041c280a8166601c0c1d12850004d4003d101341600381a01c5502d21400707031004110b11000c0c40e4611740c00c0c800108110300c00c601e203118002064056942d902d1b41c44151341c1c0a0041d02080b5103500080e94070301c940c81c83d070180b40b148844200800c0b038001842150141040c0c00d003401c0f0791400002015601400e082c01c0041e007980304062240c8108400aa881c07805230301030400321b4141c113004000059460303c035400040e41c0042c01d0103404100b86490f10003020402c002d10107684503230365203101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 157214244 1250 157212994 157213013
    0x7060504060605032505011206080a0c060809030c0d0e0105070b09070f090b091f0b07081305040b010e2704120810120215070203100c030b220203090a 66
    0x804480c80e0340c07120003c0045180400103d502071100ca42c506891400c0c0c9107055100644504c03a40c0c0c14040010311280d00d080320313603022500500154007030320780c1140c180c80d004000e13842c00e00461000c20b22010203d0342d440b03000015240031031410780c014424110035076821b991500c280410b1a0400c04104141e200040611801c28012640a40200f4406040407909504000c0d980c100d500214078040c41000c0d00e0b0382c3c9418403070304040101f004c03400c1c030f4103040b195119402850f000f07504880e00000300d18040101c81001020b02201c0c8000d00900c2d04c0d25001003000381d0750044003090024040c00180c000510300300240c501c000050400d402c1481104014404910500f140c0607124009520300c00102c032508201e0072680141c014000300e080c42d080002d0019107403d6034102a000300100840c2d0031441c20703a61700300e550040d00101154502d0041c20505006482c0d8000e4100010b400c0036103549190401d040c09151481502030f1300e00b100090403003c00020740000745082514480d5640040202e101c241 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 157215494 1250 157214244 157214251
    0x4020c0f010b0a15020606120a0203120706110304150507030213121505091c0c0c120203010b01110d030209040b06040f09050c03070504120c0b030c040801050f04080915070605 77
    0x1000402d441121004110088000d540110030808a08004520341380d40426590f6012000311240b100b24103121600621b440d8892000035010720a080740c40700904800c0c005080100e204400601200000e500702021501065400030120b4441c1400b542d42c801c459041164050054070700142854800003080405603020b5020418099000100e03101f88040070b080c0c1403a81c603000f501803185041c091403484c0d0303031900900c10b50358a4080c40c0c002c0445074412040b81c101107030408911494141c480c00c1e2034118201c0c0a00032440f030b43c40c1000c2d40e400c550007943c421241c010610007414684026040550103540254807842d4040d5030b60074140c0c0079035242c0000d04040c100032401401c00e01c1c1000701d10000c841d800342c140102c03640c0034010085940d41c0402118141c3e66508083d4503c00340740d142044a0600c190040c1c0d444a40c04810131441da070580703014200b226412002406240c13500f0600000d901c100399005000c01e40708000440550400990440002118800725882c118039621001c04440c01074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 157216744 1250 157215494 157215523
    0x203060a020d05060306250315060306080d020109080904020f09040603050303090609060613021c05010305010f0b1909050601120c0215060f0a090509010603020307080a0203060f2404020c 82
    0x100b10000c10300c41038458076620002c240c0c0240594102001d95040c03801480140d00307880d000c82030224206610a410280e0030340b0540c201c2e0301b015a207407603001c0c0c05030015001d40340075071180d11160040244140200c0035600c3e0442c4400c0c1c6007420a03030500dc041e42c04011500c0a103241003003207900c942c946214040045010f035002c1c41c0c681c240090303601d05180010348100320310740c0511b003030000984c1d40341407808400d0003076000166104103d8145a001c0d0401d140c81c42c0902c0e2170b04000105001c0c064100c040b4003c04101c5c200004011074081100c40d4109180345030142c08014005d00c102c0f2441d03848960402014100450380c2e4101481c0c50040e554444074a10058108412000e18444121076068010b0340480e80c00245204281c04502c41c4142803003022000ba4549001c110601020f50020028613000340603248030984510405540350030340c0b0b04c100e00030300c85c400c001490300202c1c009250003180c0d95103882280d98180760000302041d0f0881202c0703602a03406c01a405000c00d0800501080d200306 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 157217994 1250 157216744 157216747
    0x120609010c170f011e03021002060103020111011a0609040908030408040302030c040204180c030e03120108060106050a12050a060b190306060f0c030315080106060504091802010804030c0f0203060a02 87
    0x51501c000d200c505101512825410307000140064048501034190541e480c929803040210100c0024101d0a00070b64400394000000803c25034070180d010030058180c034000e884011221090b03400c0c0e40d080b075003107561421007030200c2641a586844c00000810040c6801000030480c0c4030542c841207115032069074201c441c1540000c3c20021070030b05000c403145403401100c0441c00c261030640c0103400d03400b901460104543d651003010708994002d0340310b40148040303101180d4991005000040d507600003801072115a00c1f4510000602c42c1c4280200c4190541550b40d2000c80d5004a13980303c06481c0142c03029901c151135020214000070604090300340900701d201c002070942d00c80c40c0042c0407280301e5001070003000303000d0300400080c85c3c11a603442e19650b810300e0000390000d41c0091001070140d00d5001182c0ca5403c00320005001e661110184c01030300c8134135404002a4107404190944c0f40c2c55004001e011401d100000340c0440c0c020301c00c021007940074a08001c140c1c140c6a00180c01d00c1c0c41254081c041030350 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 157219244 1250 157217994 157218011
    0x80c1201140c0d0f0203040b0402011b150b0a0e09030f0d0f0f09030f080c0f090f0409231c11010f0915060e01050f06030915090c0f031b060912060901 66
    0x25900902d003089161090031461400d041c3c8401048d003000500c042d061100925041d50725181c404030100c40181c10030040340c010421a2109805130100380181c512480703a02c04040798000e008404680202c0301390000f98a0b0441030510010766030000000e4026050b61803400c8403107400d09000b1500c00e40c42e0f480b00095100788500c2e000c0d2880310110102410003204d50104071006544100f119800b20b80743d00d442c1d440e4084840054010f50042024079045401d00004204000102044241079500380075007a0260710f55401e050342d94003100100c12101242c81010f000024003800003801f505240c50004601750051481900c141c4100c00001ca4a90301c10800902641100b8400c010203480e0b449640d001c65454000012144a24002030b00d101d004000040303002e1070780401c001ca00e0748500e64a054441d15010301c60a403541c1e03407070030b54601426002003904040c1c5804038000030b0348030389903164807084c2c0051018000076811030140719801c107600b5407002000040801c40700d0f00c0b80d80c98100115020a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 157220494 1250 157219244 157219267
    0x180f09060e060904060209060f0d090204061208030c161b030303050a020c03090f0a03020d080a0815370905090f0c10080a200711010207080c1201140c 66
    0x44041e848080180459014825259103140400350056041400980c889900034001103091090000b101c43c0d545c00010481d4014a25804c0700d6402070003203804004413540c1b0507419081007201d10009002c003e0800000382d404025001070050300864103500240d0010590712883c6210034400c6030303c89500c90040030400c2640c140100c2d540f15541a07c15030520304c036500b19564034041c22072094420481803d0700d1407140c031018054002190000d119480550300b9040c640042c0d806958090001491203000400b24200c61161400510014108142c0d80e40268890310030025814919134a42d04c00c0020301c50071000c00c01409000d8080504c0000d0f0074205500c3e414034101128480c0c400540101096520345d540f030340400d01082210341406107042c0e507605400c2d03000b401c1c100310700400501011340d004c5003406002c024000c50f906c10008040c0700c401e40c100699075485c40d03104602c1c2543c06045080012f09041c8000007070500440008200c00d1503101040030100300890320134510803004140c081061 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 157221744 1250 157220494 157220501
    0xf030412020708030405132d050a090b0f04060608010c0e09060a03020607080c0a060c090806060f03070909050109050d080906070507030210050c070b010311010e0303030112060c180f09 81
    0x82181c1c0010410580740c0400c00c1d45070300841c4640e903c90390086480d450700741e009030040b00c1000004540c14607801c0250120b02081500f001515005a10305400100101c034103100b11503166802080f0305500d0f640e0200c240501140090084441c0f13030300c5640004143c03000340030b040c2300d402a035181d09800e51306103000e0020618000781306900c202d2140d60108050b03150001180c00711034001c02556510840d61140c10720708201e0410081200c0c1c0b510b009401415070041c0c00e5000ea400c9241510000c0e100c0c282000783c068002c0849a0f0f043d00b01000400c0040c6c003a41c0f02590176446403002280c01d201c0b6407507a6040401005500c80070694000400c40c80c1841400a41d600c4105424500d04000d11614000e5980d0440c005200000d49d4800c0440c0803801310000784ca00c0e41c1d5105a800001d50303103c3c0340078003c558036844a180842c4000355204050303d0702201340d80c10b8400740852080d646000b52225000303441105510000d02c00000c49850a45031000134400180000d203085a20f05441c0040c19001c6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 157222994 1250 157221744 157221773
    0x19030b1002011a0d030c0c0801020d0f09050c120712050f071d04030e0f0603090c09070c02030a060506010311040f081005070e09040312151706040206120a0902060f0304 74
    0x710392600704800401c501903a2003a405400c2a03590000c00030051a0988004100c2100504551805100018495415001401d04040d8080c0901c4800b00c006d04e0307042580e0201100814980000650f1452402e12084081d0180d085c10100c50a142d03540c01441e080340c04840c819900c0790840c0d100e540340340000f080000010060f004524240e40b8a4241c49450420040d000400300450507621840300d644181c4040e034030f218000c29080d0b80c2d05141340d004d66141d48041140c1c7c000e104802c001032820380500c103000c41e419005400351049441301e07614080180b40040c415418903036611160740da0003400002030005044065030b91201c06050081091605d892240c41c25078440c2003000300000c6e554400f044856081e002d1300e01ca16103480702d14087d1264401100d401d0380c11454499040410b808070b00c2c04071708507102070b00150403110441c131201e925003404603030103900305074104008451880703486e55031030f405800148000307802c061550010b102a4007008480c52006004070900c4180040c24010420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 157224244 1250 157222994 157222997
    0x6020705010909021305090a05090606030706021b0d0f080c01050c09100c03020c100201060e09030c071208040801050c0a0e09010e072a030507230c1519030b10 70
    0x45880d000008103550498003d0703a264a03000b01d01103681d41c00c0302c0038400103010300a1040340c0501d800c0ea1004002c08040b02c0e0b0503c00d108250102d041c500700400d6001c203450455010f0948882c100000301400d00c500c8980744d030407243e0700240030041441411480000d900c1802215600c05010341c0301030035104050446030b000202004601e05943d110400312b800000282400d0b8000340203810309905024000314a10b070010081031070004c02035070660150003074030349080402c0520389891440c0342e624060044408450b6100382000d00c64812200c65100c4118810210070745060b480e41d00c09800d595060702d14071486440030440d102025000080301c04480000c3d0b40c0c04243c0c1d0f00d804500102160050050400d104400004040c1118404900c06000300494403210707602e1060300d40240181d00c001e07000e0342d00c80f03031801003044040080020803041c10085070041043c400d110007002420002d410020110700c0c410851881800d40340801c049420a0035140000d151007081d0501c0041c8420b480ca110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 157225494 1250 157224244 157224253
    0x6070503042d0b070516050d090603021204020d02030307080d0617010c0c0227040809101b030f110d02012f0409090c0b040810060e0403050706051b0706150602 70
    0x881d00141c9507440c0003041d003103800900303d80c80d80030007541c051050050110280c0c026420600c144140040d9104d1b180d2403035912400950754030070044089015250034100160380800124004d840d020031905055400117046c3c80c5403084503504c1444950101c0042424192203040030458800c01c000c0a4000c240003c0081c01000c05e145d0006005582000307009100750403508021404c0300d07000700010400307900d104d0b400d006070034541012961031b001001514480c10b40b00c40006002031054540d208501c030070a86106003640555016610040c00340b14403410041d052041c051106802c00030312007032041e550000030b034941d940961440520644c0c1d00d15404100072101800f8409401f034119409c41d646032400040070011403809820315003580e4030528040b0004a07001c100c55a0114403102010200e4000b000403503500ea0180c3c0594100f102e02801154091240c103002c0f84064000c141d215403613492000c3c1102c841114031089800c1601c050f11865503c00184603461000c500d003001030542c0340000d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 157226744 1250 157225494 157225553
    0x9010504020a14130c021c021f110a05030703020702040914070504020c030405010809120a2604030c020904030e090115090f0e012705070305090d0f08070c03110607050304 75
    0x755190080702c44d40034140c1d524100042001c1c8240007030101d070301103203142001d09211003800a60310002d251440d0005140035500780266030452007000400b034101825a07048c40044c003000e64681e0002040c440c181602013005900590b0343c0c0c443e01003080d00c15001c20300b040356011090351501e03113141c21090081c1d10402017044810800000d07501299000d107484440c0d07586005a00d410403d2019429000c940041551040c25801c0308160a8080814040e0048035441010884042e04181c8025000c07907004070503840542045003801e580f25009041c01329000c945000410b04c00a4240d200e0840d5100c130030120010755900c449500020302c410828040d245041911007001020184a41111428001c03585a49000c00c035806500c5540c003800100200d01c0c1c194405000f031301040741e011949005aa120f40342c440e0040e840040380d00c0380c6545040c2266241d040c295038445a03130f6029001d10489110301c400d511010480340c0e11581295035480d40b01d04003803078111f0300081942c10402411150f115003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 157227994 1250 157226744 157226749
    0x15060225120f1202120d0c020c0a03030e03061005011d0609030f011d030301031707050a06110a1b110418020a03050c010807020f12031e04030e090604150e04020a05060309010504020a14 81
    0x50321000c0c06c821000040004400da02689800041d1000c540c200301004400810b142e08404160b83c0c1d410180d080e84ca45035200c0b001c040412030540030346400305160b1030081103510560840da40758103001620951401c00d844001a282c03441c00305681b9403582d1940c8180181c13921300c1058809d2000c7c664000c500715411695a01c91408507003d0501c080e04000c6906d0003030150400180011580010f020000c400004035910107a5100c0401540402c00c081c0142d014420454403072480a0742042c402c03051003000c002044052320300010380701d601c03010f1701c111800503a40341c04001e40211b00c00c03001800b00710380c41400500100760042503c0113640180020b0f241c40d41c00801c0d41e2001c2d480c114070547eaa5a0364240c0c84884481105484900c1544901007108054202d00740c801140c0b0121002825a42c9103004c00095842102c02d2102c20454090200803403190210000d03005440104072038520360312000840c0c12500f0848850366aa074486041c041036091060008010340300c002125602e00110102 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 157229244 1250 157227994 157227997
    0x60504060305120d091a061504060e090c0409020f180a0803030106030b13050f0403080c0a051c02160c0e010602060f0c1e0a020f0115060225120f120212 67
    0x7070b1070f0b018003002402c0a181c0c03080c2d90180c3c00780c1d58406413a24082d10321040f540703140d0104555440c05440d0a000000032030342c003a03007950112652075440d004c0320f42c8110140805001d0103000240041d100b480b002c20712000754000741c0204807501c109a03448615007801910b4452020507114000c4809100c2130100c1c00002c800c4906450243c200403d201410034045001d498a20390223910701c0740740c0024400e0300c2d41d400e4142070240b4002c0e601c584942c0c031b80783d000744014401c02c4428000b1603810070162842c0d080d01004c00042d0020703548010b01301280744040e1503015014110484a120350301c0f00a0005d040c1242642c0d01412a51009102d1807900c0d035680d5500710f2001c1c100103040140460141400001460404001600c203181d43e600d0740c0c11450069503550500804212950030001c51803584007603080305d82c049078580e5004010505502c00c04080b000c1d0000c0c1890604c105406011414002c52280d0516051280000301c881d2081c0e03017090030114001d00810400c64000400281280d85244d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 157230494 1250 157229244 157229263
    0x61804020d110904030801182c01060b130602160b03010608060409061113050108040b040212070f0303120614150c01060e18070b0a050304121b1203060504060305 71
    0x4450752845445030a160303120700c10940e0401d42c031155100402003050762144103d41210400e00c8281e004103c103403501c0055a0100e80b29a40c100f94403402d0b40822410032241e508203c002c00c0000030b400b82c43c8c2d01c050351198020110841d005d0007082c0e040194560404c20a078803050301807640701150342000c2700020184810310600c010415181e010400c21356030395029a8005910600c200588420074000041c65045140005881c00c02c10000041a500403c0690f100e96801000ca00c243e603203540c2000480e5400c41d012003424428500301182c00c10f00c0075643d10245000303445080214000450304000d94500e500404400b09034030011038000c0e09c6038203040100315180d100b16621080011201c0f8010401079010102c5800c060301400340010700c01141480c20f810040030741c0c2003692101041c6500f40700742d681070310015030b00300001800b1480928000d00d4900300c600d40090041c40b02009035072014880b12040c3d070349500041070800d04174ac05100c0c981c010306095409100749072030b54940e16151007142c1e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 157231744 1250 157230494 157230499
    0x3070e0106030b06160b040b09010b0d0f060204051908010c05090f0d05031306050d06080c010219031e0216050a150503090120040e07082202180106050a030506180402 73
    0x141003240c03c0fa40d500c400e0310041c603032060014a1100c52820b1106440c10305485c00d43c0c04c025a035010407450301d01800383d80d2044001a0141c43c80599a603107000c0384032202542a1502d40d070a2101140a5481842850064024080000c00d5034244201142181c2c885580a018448200a5014a911004041d60b4004001c503051142c400c01428414118420070540b08104080c0c032a01003210f580000181080b0304034143e081100f1501c44030307001da589003500d61080c090780c0300110000b0080d140b00c4119080b0303440b03846c02c20340a00750902a14154a4000c101704056000b28580c51100c3e501c4100001c0100000c4540103a0a8600310b8a1412054039028580810800000113000c0c81c0d4250040410040020100c075401d48400c660300b04070380c109000700074020410101140364103214814081c00380c00303008503809182030132000100d20f80c00500340032a045000801c11406402982104500034000754850355680d0050800c000c0440f24010802c40c462040e4080050003c41166191036000f54113 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 157232994 1250 157231744 157231751
    0x20f1213120609080313050115031a0c0408010c08060414150103020a1106040c0f060e060306061809180f1501060e03100f020706060501030e120d0e01050a0c0e03070e010603 76
    0x4600b45540604a9800701502c00d000000611500c00c154001d1103511a00800081056030081800710502140070721014025644846c203c2e00790f1a1180d0318039170016140003e0b18600f030303920b0000c03030b00b51001e081e05000450300c00b50800c46d0505150141c1410155200008045494030003c83e18031a139001c516241095030100781c5811482c040c4510300700d0700d1a0340c0100c0b102841c0c28500b030400a4807500401800459018001480e14010089003100d400010106810f503070710842803003a80d805c4800791a8145050825409031612400d054a0013080100400c8501c00c5640c5455481d280c0f0320001440300c0c0c0d200150201e0710f10803184060741924580c0c40e201d602c030100e26000a1601561901d00c2008500d000301c1861b010400794014010f0384e200b1030040c00300701e130b40344010340031983c084554030820740102000141e0344410300010318034a24000700010f1a00410030030076084600480b041801c0c1c3d035440400181c159080f03000b9620030b010440081a81030708040c003c0c03621a0b0180301e81e009040d01c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 157234244 1250 157232994 157233029
    0x1303050306030304080f07090e070e0a0f06050d0303050f090304080a0605070c052a09070c1101140d091502070c060e1809030a0f030209010203090f0f10020f1213 71
    0x90510071100280240b004542482010546c01c5440791440e110300c400343c074545040c1c80403101000c1103c00448030545040d1026545088400000c3c001d10703d48001d090f5640c850114803991104000d80405000e560002503e2822034000c00d0350103009000c0300f01d02e174014401000340c03410000c0e445d100780d9405400451991a00302c030a58a0005608000b80580510b08480314102c80014900900c1d030403031404920300c10445070038085141c05c10750710040001c00c020b042401084523080740702245001072415080000c83c660340725001c1d80051441d06406525922140240324841c0200408004030540440c074081442d981c840d0661514840d001c1070008180c1040c441c3d40d68501002e038074032685c501382c810707502d0035075a85a2280d010103c00d0010a685541280070144a0f200b510040401378006528150b00903003001944040c40d0300e026800840303280b0b0342e2095101c0036298070381000c490300201040106264420306150a046d914134614405005441d1800681c10030001100d0355100240c50011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 157235494 1250 157234244 157234249
    0xb0708090a0305030307050a03050703110304030f18080d11010b0105190c051b0405100302130e01060504020f120f0f0c070501090f0c050a120c141306060905040b04051303050306 78
    0x2482d40050301e00e010100404c050190000010550892666010052a0303079a00080c0c040360941840c0c005220380600c009000130f8061000c86441c070344a802c004030380358181440507400324a507800c82101600301c5003810000d2500540312240f00c8000c04001c1c400c20905c000000c205004440781c0c040c04414121003c0c3d007142c0192403081e10386401c0b1080d60b40603014080740d40210b2030f030002980d0003140b510300002d440190b40ca0701d000070307641e0040c104040c000021a5140281100c8800d98040395130f80d80c00041d0f2076a0703078070052405401d003280d181d4031030000306070f03103096000001c04926403110008208904d1420400c026075001460b500f01544940050178460b00400d08a40018801404803962405002c19241e1460032698100c4030482010f46600020528880c0c48030002d044030b142c40010b1000300c0b8000420041503801610403083c3c203003902070810503508540c2c48400407456040090001d400c0c1343c040d01a01d0817003502c00340070034103100541c864944108400902001408008076840380d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 157236744 1250 157235494 157235509
    0x807020a0902030403031a10080c090418201f1209060905070302030607030e06060d03170a060603050c0c1b04063302060708150103021b0303060a050103060b070809 72
    0x200101e80003151207152525016006188088112202000240e400074081c43c1c10a40001d41d1207543e511380b00d058a400007148090b80040400b1603203c1d0b20b44820401c2d40076500c9081d50028000c40d0381e141110120940803060304c03004280c0c20700414005455100c1e128a0302011040d4078128503000c030f03400d80c3d0700158100070015494004d002505112410b814410001284401d0b240201e064682c5c50301c1ea03845c16800c40b410580e61504a80003000020854a1b2401c000401240241410b00d00540019111030340018202d4005003265500c9030107120695041c421795901481640340640740c100081103d940d030b01440c001d4503620102d00d41020196480f1038001c03100914170048072007490032032a42485400d020301070f01c10700c800d003008100c1a81340e8400200280541a1034403181420340310400210114030508040c281850740801c41305000020034642030300c501b5510400b554503410038000300030558246a11590406051060520059080400b01c500740d81e440307034041d95602071102c0803d054 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 157237994 1250 157236744 157236749
    0x904080f090d03020307030207080d0c0f0212061303031a010801090b0a1e0603150b0901050f12250c17090a030503040b1201151b0206070b10050102010c09120807020a 73
    0x1101018038800b081580000181031498803d400f6505110340350010141d079104a4010704000480180414000c13508100e4005038050000d0088254250043c0c14180341c460180ea070016404802e1f402d40c4245a0700d40b080800102840042030007103440140001c02c2100d042c018417142c184e440310f4080300c2d6a10840d43e00300814540d4041d00e886000345420600c41d4001e40b007240082130030841d00000a64000c2c0b800000d41c0d918808085c103010390000110f66540015030046250300e420020140c417210421003081c441c1c00c0c0d0700703145505001203505941403047d045203964240000d060002000405074840c1c40a02d6142030307415625100705070005002d030840fa81c000707815400002000b00d0700d84c0c82440186180800c0340088001d690340c0d440380b2502d0b80e00c035074401d600190a246a1508c4d00d1103132100c00c08060f0005050300d082c098a80c8806a4a0f8016140000030081c0768070200100c0d44c0a0103240c158000038100ba071a028600a01002034074041d5100800301a0700050900c01c40d500d81c181d1502 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 157239244 1250 157237994 157237999
    0xb03150a050109110c030406050703050720010e040203100306150e090d030612080304020405100b0307030608010c03021e0a02010608030a08010801110301120209150d050a110d020904080f09 83
    0x5950512103490001481e080c01143c60a9040154181d00d9449070b50460b0750b00d450044c010f41c903003840c01c1001c072560742245504408000e000c02008001c20120105000310751001c119801443e8540c1002404100703c03110201d00441c01441040704102150454a04a070f41026003c00d4005c008607214140c8045504156800302c2400280505d686000900b801540c138141c42c04c2100310303242c00c41e0040405900200070b0004100300002001402c164002c69008070b1488400802c064445594001030380007100c1e01c400180da00c4004204940c0c09020f54541d203081401c0841c0340801c10580850055680900c81002e60b100081c16407695201f58440c1e0b00405030881681e4403a60f01d0701d00180488030a101d444015802c0802c2c551036a103c000071a8122200c180316a07407503900c03550074084030400050520441c2d440d5900340c40026202c1c001d4510101d40b080028141c08a00c510341514200c520700781242c000c7c4500c01d240c400581310070180c14ac100742c02c0000301e9100c0300b0101041c0352500c1341c00c0d0300c10b4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 157240494 1250 157239244 157239283
    0x6050301020d0f06080c0607120c1401090c14032d030c0d020c03070f0611150106020c09010801020f120a06030501060b03010303080906060918120406110f010603080901030b03 77
    0xc1c1299943e500c103010036010210184903040d41c1d40c071071569801400e080c00354072084c10803442d80080c80d0710304490f00703150450404440c040c0b07140e140c043d80615501d01c9002984d441304034030390421804808407400f501090001ca501c0038040b0000c00d40e1140341000196240001203940340c440c4404e500b44c1d240030b10a04085039512150408880d0b00d40f0100c81d400e0000d44a600401c0095181c040782e200140d0703194020011400d45018000c4800562210242d41e03a400340d1b411080b0034218000519010380f103e07030000c001c00c1100300107219582c0016449105140d10500403110403c007808201c039903000e0078440000140e00c52502d840000c0000b0703400180250310b4540b0000340c803141080503504076400380c0c1707850b00c4950322462a2619214215100c65110415900060085650b042403400f00f500100840703032489507903c4417081c04c0d0300c030350800e80101c1c1a0f6040a140604d040207a46a002c0302c0070300130301c9414a566070310b29150144c0c40d0428141611440d0343d48903a00c08102c1405900c81c00403819 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 157241744 1250 157240494 157240507
    0x1201020d020f0702150315010e0f12011a01031802010806060408010c0c06050f07020a2a1e050a0e0615120403030504020f01090303080408070302030f0c300702040b01030605030102 79
    0x41401e540800d404a00450b45205c41208110b540001c0d40e01c10070041004c9203c83c040368004440c074080b81c19100f41d010b819641101c0080c3c560340204a441d40c00a400044c41c4181d860880106400c0f00ca0101d040606118680114112541000e4180755080c2414142519a240003030340c2d0b0700442c1c011890542c42d00080da0350190740540d031420510f024100402940c0c5604030526100e5000b107900c5409039104440d0754000845104220f0f01d0b8a0041c9042868102c81421121021041e0342c011804001c0d6685100b101100c10042d50006040482e950744010380750194004000d000100f045109441c004040d9600e45052812a1148001d6584002030303860145000340c018274060302c080c3d001d11a070a00140c010b501a4032a2016690142c5440d0302650711503417000403503031080030100c0c21400117100c88840d41c1c207aa00034000b2100d407030010f404901c400150144155810504000425506500303d2003184255011900e5064041c3c41c0441c02401c0800147d016140c03d0340590303015880060349 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 157242994 1250 157241744 157241767
    0x1a0d11040305160603110412021002100213031202071d0403021e1608030a0c080306030109020a06020a0b070806211204060c051504030f0f0905061201140307141201020d02 75
    0x1c3d00c0680d0041d49040015403446107032110785000c2c5004007500c40066030705100142c58076403080748000b00760303104a560050b0000010016a0414038220400c0b1954260503c00c1001002c540351035000c0d148020407080d417800c480e0f80400d1010804040700351510901040501d0310a000b03201c4903c040c0128145003d0b22156425034540410301c81000903140b8100215000102008441c06400d05658154403004151102421a0b10240445605650b2101c200c00161107540c40d00c4000c18094014100801c8a0b00301800e035080000d042a003040740f0241007091075518080c04402451030300300e005010f50442c8203a03515000f00692480d41000d000f00d4006a015406103048480c0b52090041c1c41c0442c0e90b50514411703c800a40d00103020078842d0342d005104038800d00d01c4014031481490205440b690726008198598401c005519100c0c1c0f40c040180000c0060035010684800700b0341c01804030a1800c0b22001b03a20602c00c20442c03250130250a44e88590109405030368009801d00070841d943d4000406 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 157244244 1250 157242994 157243033
    0xb0403030809010f060f09020d02040e0103050601170d02070b0c010f05010e15030123041509110109050d02010e120c19090606050301060c0210050c0a05010c03061a0d11040305 77
    0x4616400c2c1d030034150304c404480218041d02044408a01b030300d04155040c0400d1030003a4101080c441e0496500f84000920b00252040c0c0074021070050000c0c0500d5410a9002c4000c00301826241c0c2c140d51040c0e8807954003640c00180403045030506074440340c503036041b00744450140c0740c002c6400d00b00604000011401c80482004280508801b00942c0c9404000300306140c02e031001a001d0030380d2051080c0c0f0f807560011072480705591051107080108226404c1c403190900300da800c00740c00d590740181e0014103a01544c2155124020300403ca0302102810138683c0000c01e1090702c403120901803040d140500c0c1001504001600002c0401032211062210219252407616120300c02d1000043c104000014414040e1301102c0c1642c0c200d0765071003511551a000e02c1000d09140c0d00710010070a081040034000102880000409071150001203a24503140c08002c0640340150800c0b00c51403400c01442040f0b200030012900e841c45c2c0d488000c0b0300c1070030441c00d80341c16005962010f0110300940c801c0c3e4000d218142e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 157245494 1250 157244244 157244251
    0x40b0d03031a1909090614130c12021c020604080706020f0601330e10030209130516030905070510051c0c0f0509151b07050405160f05040b04030308 65
    0x5002c03814000c94400300700c1c020402500440301081015014401d0b20320310380154049a010f80d4001c5040058203c182c030040000b00c580f2080da5900c10000c208104450150303400401102012070f208042030340001c0d134200500b03610691807541908128045454080585008000705000d60310380a81c0d81030007a480c0c00940480c0d0340c00d8040c03900003103003089030700500d000316020060f03c2551000407000b4515030201043d0f10f080500c00a040c500009541c0c20184d80d50f140300580e805611400c4501c28400031060044404034998102001c10010070b0081c615000111640e01d00803610715a603050080c182000c4c1d1300b200b500f11462404019045401a004120306801c41c00c04030303100a1119002c404030341070000c4000008244405800f0307403600c01d4019000c031420050616418240c6250030907043e03031107029801d80042c000149001c0103c03091001c0300061005940038045d61401210090034124011725100921100d44012400e1a220f1070039180a46000b0a04642e203d450341009403680c107048 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 157246744 1250 157245494 157245521
    0x61107060e0607080417121603140103050d0c061d0c0a081b0108090f010903020c040b01020303010b03130302071707030c120b010b0c01090602040e1b03130809040b0d0303 75
    0x2619442407000008026101c3d03140caa40704010303a00e030b980d90304d1340d03484000d000e10305843c0301402010f0841071529120780c064202d01000d2500c0c40e81c020700c05015075070207683c0000e824002100400100d60049200410500a0b02e40007100100340d01c0c0c10001000740b4004010301040407890504041000101c03601c800e42d00300c0340a0354096882000e19030302c52194141403101e44641d030680007294020303038629030841c03443d005581920055000240c2141d0501100358010fa1059440100c0c0d03080074414644240d40a1024600c0c540c102480d0080318031028120301d41800c078955040040c0b5100f406030801411018280ca024042c444803001e41c0d54078640025107010810950015041d01c225046030140380e400713618070145a20781b811011142e009030f1f010b0007065480341900000208644000c01c060000000c004050342046500c103107141642e4025885004010030610a8001150400340105075100070341d140d84142c5000864068030300c000080781c000f81048450410581c15070000c1c0c00d0b06607035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 157247994 1250 157246744 157246751
    0xe030403030818070509221505010911160f050304031a130f0b09011d0a06050105040606051207050d060b0d0e01020f04121403040803040609081c0807030906110706 72
    0x1042400700b000125515021078550140d44c080003c2d05107400c01960010351000400018245450041c400030f160003402c446c02c21000803d00d00e4210709108281c054a0f01c440104196440c0c034150300000c0c0300302c68108102030003030060803040008146103101016403003416280c8659403885d10aa40480c400c05804280750f040c070002d01140341c06840c0b0000d15400049072080603466441312642800080d2a6040c65502ca003035000c110034400644000d0310041c1002098a030155050042c215a8180c120911980c20044100304040c1d0107001c1c3da1603201090111140d80d159408141c1d02480b132603e440c00c0e00d80c2410400154400404058492002581f400f80548006500c6250803032103448041c541e043ea0501050060710b52003155000f94a202d02403130200342c3c4481240317910f190000d41c0030094543c400901401400e80c0141100002d016840080a505080d080c0c0d04c0742502480300960b0820010800003603c180c402d402ca4501c480d0084010400c5803483c1000510301d60110a00781e400c00d08 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 157249244 1250 157247994 157248001
    0xc05010b03120d1d01060602151303090e09010209031209040b0d0b0c070c0b3c0f090621090114060603150607060606020601030b011e05150705010e0304030308 70
    0x140482c90200362018100b6861500d90140c11000081034691002c4100c200c40c0000000742420912560000e420b180c1c0081c01c0601000b04200170745074000b05500d01181d1034400f6040000c1d0444411800d40700203032103041c0541d031505089402401016599a8144210711410700d650171210010302a824081c1c0e070501843c4403110622580911488000b42900c0011703002032646555207003d004201c0c4a0001a0200c50f0307212000035441d001844140c8030000c00c910394200700010308014003218030020240c0c20a000c08040000080d0050304100900c03804001000c0809135101d00443d038429080b80d07142c0e130303034218070f010b0440c06000104e4040b0304542c43e0000500c6804036505601d803245100401e40c610b550f40c0d1601da0064500d0200d02c40e50800014018000010054064007020f801d85038001e00d400e41c0b450904440924040e40280014800a0074020646618040b1101915401d40d8801300703900015081400c540f05200340501154070342030304ea016a003000f200410440380607039202c89040d01c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 157250494 1250 157249244 157249249
    0x1a070804060522020f030114040602040f05120a03050d11190f020109022202040302120f0c060c0d0c020a05060d0204170f0601061b0210030f050f07021509070b0a0c05010b 75
    0x2204000100b18031403d00d50005107480c0c9004c0680c2d010140c00401c5800034042060394100090354100e9000d50007280c01d012112000134500000c00741103c03080050b03020300783d22a440318403010b005020801e00198000e0305080356084a407001414404565888801e4054526840190030b05680003403404603070000c58a00c14001c0c0241c1980082c52090344d0f21001c0c2c05c40d003000041542145446400303200010240c2e48041d010300854100300e0203449100c04103014036003170810f02e0315018450001441248002140021388180c6042c103230420ed01004c0c00c500010b2000d8007540c0c40140d000c88001041110055544c004d00212141c9500c01c00404071010401c90b1580103041c41c0c00b246610050040150360f1041295000c80070400c60461040b00f410b40100310320303160015100f00400e4903028840011802445145e60024a07060031408a0600c114025218100f1010001c000d441c0080868500141231101c07000520321000f040382d6424215502500c0f009200c80d040d10b142d443c0c00d40940b860b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 157251744 1250 157250494 157250521
    0x100c12020111040e1f0b120702071208030603070e07052205060a141c050105180609010b1e0a020105090706020304080606060a030f05091f0b090c071a0708040605 71
    0x1803103100c210707091a044c07010107840d68000600030344101c0da40480f43c02c030b10408441080050f181b40030040b40c0d6800415440c504441e00944848219400524104040c41d8010940c40060b50300c440d10950342c3c0c4032000020303d40001d42d040340a04107051401e0000e02038002c4001e011191060243e4400b01854140718146501e00744512508444100000c4030f0b60381c410004400c480703031070b100079505110310031600070003d03040b965004585550743c000505c0345190030b03500005081e1500d5000300c101d00d010301c0814215034061180c2c0d205004046401d02d040c18003111440d05c000380000c203141d11410f0644009000e03084c01d0340c5004c000d0044190100d41d4920200c01c640555003a00010a89510354400b80041d6522080d02102015501c0100c0350910101d80078041c054026400142250007106901c01e10085080c144000d696180984040040e22000c02d565404402d0b0650300e506c5080d54100380c1140e45481030307903040510fa42400c100304075800c00c3c040c43c080c0d4060f007030410046d501c500c0e803000391 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 157252994 1250 157251744 157251761
    0x10302220812070f08031f12201003020a090e040b01060311070309140111030d0f180b0609040201030e030f07050127020904081c05041209030314090f100c120201 71
    0x511311081504004a04c440c001940c0145400c1001c09003500d14801081594640e50000003003144907659000501000c0000d408807201035507281c1309600c000341c000801d40000b0070100c0b428036070040750040c175240c0143c0f80e2030020440104489a1894035142111101c0030034014140400d00c0c3c510b4200c05810bda106441001b07525131280d011060a02e0344c0310b0202c61400305c4c3d02d070400000705030b411191241400580740226041c01c011401142d14500001a80e01542e01411515881039625012030601e80c40c40e600101c003550f508551380c48a00048003d04080c152444052200103a100d210b20040b6005081e014003400007046a1410300030341c04c149444036503031000e08405020a050151410a460075040b41c8074100d25071030101300007400501c1d0001444545038071030340c801c02c1105010ba400c00045032100b092400b401c2c00d07815681c010f00600030032400450300300310205440160740ca840148a01d130200c001d002c190100c041250040c400342a41d001280d608a560929000c43c50050003041d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 157254244 1250 157252994 157253003
    0x31508010c050d0e2a09060f150306060c0a051c0c2111010c090810020a091707050301050c180901030203030306010f03020409110a110f031801030222081207 69
    0x2402a0308820f02025040220304200c640c0604004481d41c05500740d81124a84120020240f1140b03101c0b041020303016000b044036000349401c00b080c00080ea42c0054444641e405004c84540700d032100ba000ca03c40e4024100440304520500c0d441000b8000001501680c03441054511441d00c102034108865103005820001c1c10a500d00046c3d604107803c4610484404035140746c5030482198001c0ca680c00d44000b2000c0c10046050000e080c04003c90a000142d80d01c0d079091800d40c07400801100043c121500352181c0f01c410640201c1020340c6074020700c00c0c0c074010100140240b1071820300c0e20100307825030f002c010a030150782c0301d161b0301d0407035403d2803010380d0304807074004000d94110399401d8019242546c16250302c208056007000301041004661207140c40d18548003005517240c2c14480c60241c414047c0d01c4450700d59038049461202441700c00000c0b5181480800010310704c8903440b00050300a800b0305414580c04403100d1504846050f00c00114404841c10602103840b00da00318001c901c020701c40d420001c1c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 157255494 1250 157254244 157254247
    0x812090d02040e010f0504080406030b040e030a030506030a06050c04050f010c0f0b0a06030f1119150c0812160906030902060708030603120f1201050907020c220606031508010c05 78
    0x2610b010382c05060300d00801c1c4004a03408000766206011107504440458445a001c5002e020465140c030500c1d04903202964204802c0024440260b034a0003165a284101030f12000001c14a40b018031840a20f09e034440000d100e80d05101d0180822a0490701680b8001c0c10004107a0301c0360f607c91001c40c01669005240508801550b881c4c00c00000070091003c007000c0d8442000000090f034403200700c01000d0190000790081803a040420100c4004541c03c0c1d01c9081c0b505005014251210f100800107508a040094a1f02100d1400c082c0300e010702ca030140d0360607081208000f41c070120740245141d526951364030703003003001d4880710142d04a43d10203070040e400540511591000941034001503801c032200508441c460402070380c0c914800d6100441c0646020400b08030204a10544551903015200858840100e031801030300095035000840f018501ca00c604085082e1030008a00110051500c03050042c04034a840d00b4000d0046d124200d800c001844160384009012001131091341c196040c2590303040d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 157256744 1250 157255494 157255519
    0x6060304120915030f0b0607021c170a081501050f0d021b0109080706050108071208031819020102101b050c010b0a0905040b0703060303080a0903020c1009081209 71
    0x41c500800181a20521000c0c0750049a280d01910b2103054881c00369601091031030050384480c050718948490f090003400c0c14098000140e6030b1980c030401861110800050210490130100130401055041c0d1580780e50002c0e0b140c6115034030180c0c803480fa900d4603000c00010020440115018455803984018145e4140a00c58500034076070020420b45480c0b0310310703030318070100100c036582110200c00c002c0f00c13a00302c0014407804020040c040c540c0142011000350108914080c8400401a50b81e000202038000000001c0d00400c0200e1402503903c40210403900300000010382c03e041030720002030a81c054400c90741c165540040500441021001740308550210344610702e0b050b0703415002080901e00d65500da5100c01c04030f488070ad903898020803209502152900b800c0c1000d009104010f01303940e04060610038180042508030400941254203030000003030005250600302d007040324046415501182e002c01050100350710404039000e4521600940c0c41180a59810210a12401000c907410004281c040f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 157257994 1250 157256744 157256753
    0x81005040f23070813020f041508070605040f060305130c0b0414120c010c03120f05041109061e04020c062403060702070909110d060c030e01060f09020a020102070b0c07030e060306060304 82
    0x45c00c10f064070243c002c448540c00c4400040c160303151003c035803c1407a0051410032190302e0408c0315000400d03850420350316160501000d101c1180c0342d0f0050205040d20f640c0420840d001009003484c030b00c0e400140742141180c45107585089940039102d0746440c6000c80f100c030003851504140b030440304140b15004000150002005660301e295084090307013842480203401241000500031001c8030204118000303014501071511250301203c010501d805002a8030070401d450700d40075001343c08810a480084080340c1c151000038043d01caa4046410507000d640180146071030000310342210b07c0788951041652207a1041410b0713844108030360b040e0042e80026803c001e01980799010648060244204c040c10394030403008503035800c0b01e00c401107900c543d980619608582e07251080107048401800244034051826804105428160080d2440c1550000b94205118000d504807204160b010034445468905a8410111904404002d074040343e084c1812110a01e81441241d218080c014041c0e811515180c4a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 157259244 1250 157257994 157258021
    0x81b1b07030b0c13051e03070627062c150301230a060302030a140f0f2505090307031703010f05010504031e050106030203060a0f180c0501081005040f230708 69
    0x20003000203841b00310f5101d40d1802c0c030080d00900201d0711006000c00610044281208800c405030145540441080c0710a581c410100f90003000c000e40009070054042504007d000c1a480c8680c2c0d218040510700f11013150104043d504031030103c0c1300340070f0407000181c00340204a0146150365000d07203442e0003400704502a0340a950413540c0c64900150040d5140902c1002403002c2d2001c6010103200010072407003030001d0000591102d030a910366501e510301494618101900680440c0501c44003003190b8040d13450411414000315005220b440c550700280c9a000c00e181d0080c0114000156651030208055018804607400c0303039030190b4403e55840a03000710204001c40392904450554071440000003603601041014040c40000e980066000010006d00d0100e84015004444000400700084045036800c070115044590a080c0700340e490380d860716501701e009010381116901c545411100140011580c1c040c240c051018481810004062031000c08c0c002c2c011584180028140340018041501402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 157260494 1250 157259244 157259269
    0x307210207170a03060e071110150605070212070609210201080601050d0b03070e091011120c0c010608030d050108031206061b12030402031903081b1b07030b0c1305 72
    0x1400296085d12041580981b0304241c54440c0054082100d00000040030310617403ca030688080c041080785150303000b5040015480c0f0902060080124000b0255180c043c8070060000f14170054602321600d946010b80740c25010701078120580711507001c4152107207085512852841d0161107031206c03955030500440d056031220700c02c00d40860312545440c501d0f4404101180c06080d032148480c50500d4809405031400e83e450626400640c141452844888a42c408540d8001200c3c0480398503952881c41001c0548120301110a05600e00320f0009201c400100241031201d040090600103030341c0c0d84000303d40e40c2c00b07000c00c0007518429403004035540e4a414001441025524200c8401c1e01e811086000e00389084941c4010900100000b00700440c5011b0000110071500c050060100c4025520b006201c1d200080c01c071152011102904a8407100354401c0c2d813003c1801480c40e0301c11003107000850303882e11103d20044403d0b403460300208050345c0c1ea8130181e50a40c3c0085222080f210f150400b00800e004071003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 157261744 1250 157260494 157260497
    0xf0708070905060a0c080a0c140102040e0f06180f04022e1101110f0903010b03030c190f020d12080a050928020604150909110301030b1005060307210207170a 69
    0x40c0100c00040e04000240c103624807d5180c01e044a10b00b400c200ba409800c41210044591040005001a0482c80c03849074010038040300c0488155030b10f10109400840b00c0b21305004c008201c6040007160054400140c3c4034034400d50309041c080d50029259200440c001903809189003030030754510030043c4501c004d51103600440002107a25900f40304420500d034407109000c0e03411000042c1c0341481c0c0c1000d008600740382a095006500c2c200e5103121064583d40c45814545075103a4111000e0280205100b4210307009400420441e40428985440759905481240c03000110380d0700c10001d030849070745100b50b0b0701c20007009015000038038900030f420703040803207029a413447c00070322048480c0580c5076040944080c0002d00700c030903801129508040c1c000300082e8001e05c40780c1e04160200300342d10030038000e170b90440c1e0340801d010f80152101044001c0246a0b50446a00060040100a4030907440080c100b686a07021001644010b82910100168451510040c1201c51003000303c44210581c072001701000840d6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 157262994 1250 157261744 157261757
    0x2070b0a0b10140a021e0706092408040809040515090603151b0409020307020705030709201c0c0810050109150806010c05101b0e090f0703090b01030b0f0708070905060a 74
    0x500f006100c4000c0c40b101d20020030b6009800600c2300c2e82c0c0204021014081d0b41402060b43d005400b80c41c41d1b1140342d104200c0c200081d010204080100e484240c4041c400014804d01c001d14203012250035a907c2a40d4142c4202802c00c080f4032941004241c80860f8080fa0000d502c1a64030130701c03080d0f0004401d0200240e04003041000159481143c8041c50180030180e014084807854081094503020607504000d00740c91070000381010001900390319403411070490100b281c0300e05800002d00480c2d92840380c40c0c00e8650404170402e906c07561040a0380e1294078000d001c41c2400da00e83d0011284d01045000c0c150b82d200c51248070840c054062002960301010500d400303021314a040c0e95003410003144a09200c9002d4440001d0311403d0107c403852440d640041c85d042e0600650714002580c0eaa42c040c000769a420b070300c000480c107164482d402c0f00807407580041c1d9039002da5a5a140c0a50300e01c03001c0f103003a0022454080031800162180c000c0e10702800450fa40c8209003800c2400b0051264400c01424082c4040d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 157264244 1250 157262994 157263013
    0x8060109030f081308070b0301050d060f15030c14090c09030c0d060e01050a0b010c0201080601020304091a15030c12060a171b0307120b04020409020402070b0a0b10140a02 75
    0x1800b2500750070b05842400195100e02c4000003001c5001c0041d080b040058101c540280603d589900569044074801c0303c0c2090b0b480c03410305040e0010400500480440350800c0d00800d403041e04450500f040b00c0c071502c660402a83c0e43e03041c1d46040000201034039840800100801d80c482c140901510701e8220050a03100c0d01080000090301c4007101020844000d03454a010000150742886690fa10600e80b41e8184210b004e42c070700083c803050f000b034002410705c0b01d00c10100b02503034800c0042e00c02524001030100a203044912a904424030b03142540741c4030b28840942d40c7c11840c07100b800d0b00d00503d0000074032801c00d00801c100704552907009043c113400c074104200000f010b50011011010801544000c2c00c1500140902002030f55250040e0754007a03417064030f0400a4061003a551809980c001150b100951038902c006400f0b00342d1445d010350b0050001c900c1d00d09010304020242d000d413006550070409010481c041c004034008054650780820207400c0800e0b2440f0040f40100303466240d43c4180c555010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 157265494 1250 157264244 157264253
    0x702030c041e0f05010e060120012c07030b0103120309051b01020f0a02030d0f03020d09030e01021006120605090307020415050f040e070b0702030708030c01090b06060306010f0806010903 82
    0x1002502d6031140d01011040003956401c0320300c039003000496800410700c1030b0746c1000740c0e20032003000140c0010304100c1140f5a40c2501c1c05c00c3d40303006010150080003401a80360103004040c40c16581030210003940c0c403182c08003010050018521302220344c0000c50350207a038a0360f1030307030f04545400503c0300d0185030b141c901c698000348040c4410b55108102e900e01049080003c000240780c001d032005410708a602250704903001d60b0b400a031990780a201071400c0c15110401d1070044020340a00c41309a40740c02c0c1400e08030410103030044c40120200320281c0c2100c0151b9642d88060302038030711921a101c48181c0c1510300300b020071901d0304800c0d844000503041343d18010b181e5011074112880612120040c00644030103006500c1c21001e40e0852880c1100e06005a12050a215881e06c00f035210310100c441000442000315101480b21000411002041c1c1e520781a9a24420f070103031071b200c58200ca840e1044000104e90380340c041c0c04d8a000c0e0710306a481100d1903800e801c050b2041100035000c5818094030a00020008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 157266744 1250 157265494 157265501
    0xa03020d080717031801050708060f04060317030708070206100308070305040e04111002010b010207210803091506041e150b0a030e0c0a080d180308030c18060306030309060702030c04 80
    0x340d110000c03d036036403412118111030b544480242c0905c0d6410403041c0224144c0c800c00c0140c02130030444100d1101120040010002c00ca075900c010704050303804950040031074040c00610301c1070f0f01d2503c1d070380490b03a18102e040b40c0f503020031107400102d58803035001440840c2c0e00c10041d0000c0e5201e41006450f194441d024030240321012102110327030080f006040109801c03e02c490901411040c0001c1c000341c5807110003c2d460b0600e0303014110000001e10902041485819801d00076140c024007401d0f501c2c104050702903110202c9142d005955410351020070021700b07284c851020501d1103c0c43e5414100500300c0010064000d00152228104405501083c0002e4a2006101c3d00c6180d07100040c04100e110038003420101a43e080741d00c0713441110130800c01d642010609009101c11440d01102210135801c0390501d40394541c002130002d81c0007004000d901100c03400106110010200a030110012403070401990b40b00803585903070160400d00c4855540e081c002e02420380c00d0703c010140d442c83c400c404041400c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 157267994 1250 157266744 157266773
    0xa03060e0903070c050103020f161e0b040309050d0c0b090d0501020d020901082d0c0c0601060e1c030e0d020d060212010f0905070207030f0302010b090f01090e03090a03020d0807 78
    0x494200043ca00100866028048020b02d07083c01c05601b40410300e8004086405030030754038071040c00e00512003020071030801d13907440046e103002520181d01403160503d120076000c104c604901040864201040c075240c0143c000000f982d0103090703540e0032801c03d228072481d5044030301e49039008000601c2c1d080000301c0030b00142500c0c0c0300070880181c64001c036100040494901515420f030b07910100c8a03001c0d035510104540f14010070620041c42c00c58440d036205541600c1503e031100d040e8003525001144465002a02c0000c9c0c810895880714a2200c4080d0341001c2d48103044014080b41c68440c0030102400c0c04182e0003c258002480451031400b9911814107a900c15809203284101013401446401140b407040030180650010801c894641424086d644444900005c4c1400854801c070208262007500804c04c001005418040d540c10b00c801c41c200082400c1c003480d1707a03d9052562205005800200703480c2c24640c01003403118003d155400341b103c200c0d115481580c82901c1000004081014040181c20 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 157269244 1250 157267994 157268011
    0x30a030921020f2104030206032d0a060b030709030b07020703021e0307060c08040e040c170a03020c0315180304080d0503100501030212040b0a061710150612020a03060e 74
    0x1c186200008a50503c14400d25000105640c00401000c4070b07141000c0c1c17010f9035419107042d0303940d440b4196001c16007440a103044200c10020b44050700c8030305801c1e0f901030045403010000d1000c55146d103002800c6020443e01c1d03800250324210304002068210390661b8116002d40181c48a00c0e0b140c1c0c0101d090414081d10010415901002c41000d9090030000400240501d107810102c40050396a5404648a00d104444043d201c2ca0013040a11280d514190028081e0f100c0d0328a03500600d09026440e522000c40603809405206d2440101d401c0c003040d00810f0b0a004181c6060940e24840354103034201059541d85424803041c0008203520b10104007a100c1d400702500d0740e0b0303224076140308968810351903034205504040c01403191071003841d04d201440c2d030040e41c003400d032080030b07500c1c445208001c0c91281d002a42c20307207690305c407a82140d40200f00800d5407070101500380300c1d180318072a800300c100445205d10301c00508441c000004080c202c4c0d024001c40b070464500460529500c6034586500942512401c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 157270494 1250 157269244 157269253
    0xa02070314030a0215060f040e060402031011040b030901020f16050f0703030525020429060c0d110106120c150e01050306010513091104080601090905030a03092102 72
    0x309015007541090080c41aa500643c9010300e80500203448a540a042811000c81c0e1070104105584080c111405200d000d40100401740303002060960b15101a54141d011303014511200a280304a40100d0003001c1d41c11a401e40751628041d0301108075407009112800c955800e00c000f00c41c00140703800501141d0301603805045005410b0138003c1c180001003403140d061750301c80e0380704000103a0070400b6665030304d40c1a004480215003062803200144c1d100c01d0020f51040c42e01014020042e940c0d0400c1c0e400032220001e595101d507600c400c0c4440c0c1d200e810700800e460351003c003c100c0120321499403161070b00020000841c0c4265654100040e10341058411290b01010200900c0f2940003200c100d190706160b460205a02c1e80080000380c240e2101500c1c5d20f0422034009604102c840e02d4056040080c00d2000342000285120318240d125a04035000d140068002c880000800300c0c8079001d2100c1d4250001c0145d03142400c115020340c000c1082c445c1c100c0d4071101c920761b1300502030381620403d5648982500500b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 157271744 1250 157270494 157270499
    0x2040501030614071d040e0c040e0102030106202503060504031e03050f0f0612060a0606030e2821020a05010501081f0c020f1207020103050105040b0d0b0604110a0207 73
    0xf52048001080c5000304201440b01d0403040c144452001586081a580043e0140199441904100d503107001250000d0622120081c03850056004504071505036641d0444d850703111000044069105203050040e50010107480304c01516503507a608580d0b24600b503a455607030b03660344100a07224222810303004514140e94103041582c0c0260500c03094155450100228230300000004140c0d04003510000c031880965001444a8590403440041944400200c502d14070389500800040d01d00b501403500000c0c10510001e00480002445041e414403900214460040100251100d84d0000702c054038800d45c440c0100d84500a500f9100c42e0f6050641d020306000051410140d003500d0041e8004070040e07200780d440446407189010906000700d01080049046003c0d140300f2441c00740080300080c503500803920040c502c48203210041000038400e880501090303a0302d02c1004225100c1c51121038000a0f080d605400041c51101c05641c0650014800900141c03813059100e1150080307003d5501590103000305 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 157272994 1250 157271744 157271771
    0x1407050a05040608060a0509030c01020d0504120f2307020d05010f06080303070e010e0301060e181002090109050d0c030501020429030106020c0d050c06030c0703030b030724050403020405010306 85
    0x4400152006a4040c4121864440c58517a0350b20f004056001c00c55445001c03410554080c8115107a101500000390b46400c60038412800030501914101c0c5c070f40121081700344419025094107405404a44c40e00440c0f101c0302c0f0038400302c444234680244110402042110016650050b40c0c0c1412800344000040840c1911000e80807528241c1144185500a0080051003a1f100c040916400f60070310b0b0180846051801181c00341c10f403508041c1c1c600d41207604100e01c0c850340d214600c0c0028030010803510b807000c114480c80c04901c01c1080d0980065a803400900c518104108001c3d5010b125007007104d007859480d20b0300da0890f0420740049070002100c06c2d840502c0c50403201ca08180034810101d841c0b555140010295950816106072030241400194000c14000c062103100c90102004e01059a0307480e0044d07407407655900050040780070900d091140d11003400d0029241041d5003407600582c805c89840000d07060001c9006001408000d8204004401078603503000d024004d51040b03030003003100b0041000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 157274244 1250 157272994 157273009
    0x506040506040b03030f0901030f0203040501090b070815151c05011d0606030a0506120106060e010906031401030201032c0d1403070c02040b040603080a0e1903050312060d140705 78
    0x10a40300c2c80c240100780c1050356001c0101c9000e1040100d0b15659030031040d0050b400350981c9058041d1440c0701000f004148881904503500e034622603602010681d030b5205050381c0108055501d101034449800041400c0c0c2040070788080c6100d034420720207062000f0140c842203411001505540250385035001000a0110301c140024018030081000405103001004502e003400b000742807810722070310b85021441c1911607003994181801c55100138000991145c40240c80348203409243da0005030590f8001031514428480c219107407a44604c000b05a0b46035800460141c22644443c0740c65442c42801c050354880c45a0f41e80d0f4030b01480c0c40141015600a0201400e01c00b0b20748a04101c0341010001c110007180e12a038801d141c1c2e80d0403900040d1a202000c041002010240c000070501100019407100e1035400c03076a03071125030300e045404101641c1e8034800c410318500e251100500c3e0358004c1c42482c100e41003240c00541e01400141c81006030350b1443e00c440d420800100c1c1c070140b941e005550240224100100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 157275494 1250 157274244 157274251
    0x908070323040305060c0708070503041509140102030315040e0d02100f0c0206011a09060304060f050108010605030a02011101320709120b040335060d0c0e04030c080d05060405 77
    0x241e960616186464080d11440c00030035100382c6450010b2400c08001c0d1004c207480c00300390410100d80d00e0300d0312140d0042c0c0614031110340e5030116024000000b600300000c10450009101070340a94150384400000030b1101720000e03171041e8000e03210098581c07030400802c052400c0d01d4070f0354010001500300711418401c4600744c140284205051503480c1030000c0c0c000442604507541111244405000c1d108400c429012f641c103480d601000000c1880207101103900440d00404030408100000d0340d880f860304e400c80b00d0f00e00ca569016000a0580409036002e80074545500e0003400c0080788080100315146c2102940c82d00c00c015002c048050490b2103a090360501e544072146051800132582442183d203a23007100110000e01003500c2c1800941050300c43c80b0910f42c4003560858510203405003010580c0a00c00665511601580040014031207181c12019445081d0300f02c564118010f00306000e012103000b0081081c1c00344445a09004001031506008008624900000144608004007080203468000c4c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 157276744 1250 157275494 157275557
    0x31b1b060603120c03110c0d080a020a0503041220010f03090510020a02010e060a0e101a03010606050a020d0c080403080912030f0a03050612100b040f0e01090614042409080703 77
    0x2004909a1500d652444052309030b04540740a80701c6038405070403071400302c0040008201e40008100040d294815403504d2059500c83d4450103845000703000c4444080011100c045c0c00186501415034019000c0d9002c150811b00030740c00d851500a010030040207903400b00c0301ca000143e644050300704a0000c14043c1ca9003006c10701405121201000c034495640750960240075944550b103040c0c1154034003c040400c119a00c01030004e2016030307035400024186420a2083e0b4026014040d00661154820201e4000c559803159000c0d0800d411904d80380c145811a1035490340040c01d08042140700b03e07080010f04001080c0000381c03951405c60420080070381d03001400c0319021b001140078001880001003805410415810030029204940f00005409826503020107400b0314070f001e03038407014010107410054280d80942d000748412403420f000304040080454015086403038a801089003081c0700c8044450085d060380300401c5030200e9483e070700784951108004a003c15152480316942d21101e005629445048 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 157277994 1250 157276744 157276753
    0xa080f0726070303030515040507110f030a050d0207030302040b03010b030916050d0b0621060f0609040305040303030c02030409020f0c0f010e0a0611040f03080a031b1b060603120c0311 81
    0x9126a070340c440703440c0001001e044e220400240700782810b03000b0561001d00200180058180420083c0480600455200140c052201030320710cc403100204640120090f941c850303141c14200844000250401d460403001c051702040000740b0781080c103003c0d40c042c0c2401e8180580c0c0703080080410349081d1820390210b19069240c1020001c42e90750404d40e050040d0055a40d06540d503070340001405003e0030901c070840304c3d15000d0700f40d500d04100160161180044607000116600d0304000c00c0b4500c0c008480c0280040c1d030030442800000d00c81d401001004210b40101e900785506c40401c1010303030300803d2004980090105511a541c0e8040040b0014826100c00820084c62102c0000d82c8610361050041c0c20075032107103001d81610b04400308135401018041181c2611076202e00e03160a460f401003101c1800241400200d140242002080b210102e020f51102480464001c0182050084049082d6000c5543d00400004616400c0000c42d520416640b0001040e13118074010b01215520780601d039840d0310 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 157279244 1250 157277994 157278059
    0x70b0a1b03210b060406020a020906030601050904032712021003090b06061602060d06060207061e0e0d17030703141b0702030a082101170d08060a080f07 67
    0x4010141181c0520700100b440302030704803403290b034014020948034190070060000c3c0000d80103501141c0c840c48188221400c03221903c0342c00030180d8a00e800e0180941c40f00800000c01c001a024514545516070384a050080b000c200039181500720746180e2041d82d000e07042c07040410440c90b01c00741030001510181403c201c4142d03e5103078010300345001058180039201c0040d8a0542107130300c81d0104480ca0340103100607515294251031602420792403140c0405031181e200045005406000e55180f42055050310501680f803082003100c840808020403034005480d004100c0221300c80e180e54007014007610f004a0307540e052203a40181140c0940030000443ca17050020b000f02c1c0550081c050084031000c4041b03644482c981d0000a00b09100128014100f0310004ae1850f0884221301da1100e80d0705100e0082c90b030503030381d40464040003000c0030f50035251030300b041d02c403441a14065501d40390040c030301814a000303140d22030350048d10f44145103c1c42002a07000d010104004004406103542d001f401d600c070700080c0007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 157280494 1250 157279244 157279247
    0x1b0506040303111813020409060306140c0a1d1c06050103031b05070306021e040e01030c1202281a1c06051507060f05010603020c06070801050d02060d02040305070b0a1b03 75
    0x340c20b034200b0352140958083c0510b1421454040d20080d11807076204102052b0b4030700d045401099042c290b5410080741c500054800706030780f001d5038031400c01601d03000b03209400c144407031100e1000ca40d540f40d40180018601120110000030a2955a2042100242c04e5065080c060603142c4903102e648402054000041c0004001060103000c0f41e038020701c09a110050640140724601101e01c0c1c052103040c000c40c00040700708080c0800c0c0d04030303401109001400c540714801c0e8190020f10b10006504001c464512015901c071a05040c1d5484114418a8942549420701d0000314425208141e80400010845040c10b5003001c1030f408180f1054041017020610b000080740810b00c0c2c080c185140d101c00402c480c02400000d030001081c94444d03001c10445d41d82c594102034001c0d0001c206d2440184100800182c071140102c0d003490503200b0040043c00f1074a103c1d4208141e95001150041007140c0038400040025010442d0034080d045400360030307480d000303403c00040c0380c900d00259059451101020300c1c0c0c0420f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 157281744 1250 157280494 157280527
    0x6150903030302070c050319061a180403030608010c0e01092c09030c01021201080c0915100e0402040303080105012c151903060906080109120f1b050604030311 70
    0x1a90706040c056200c403c2ca060440c1080030580c021600760142c60004200b04d1261320007261078070712406040041d00c0443c10144602007201b418250002c141800e02d10801c0103d1040340d50180c4607250106103203031545080c5003541c650800400105103c40c0104404d5a002000d010280546514808568140c006070303601d0389204640a8000ca040741c030100304140814022115040c0000009550301c0d4001c42c0b4844181100b40726404041c010605102081e10301040058020040d050413812215031420821a611074000d6440080c05911000784601d41c0340c50004d04015402a1200703055585044005007490828421140d0041200b400d241c82c001a4030810002c1a9019981c210741408010f040340682e1080390340712401c3c044c1c81020301d4480ca605401c81001c1c0c901310034090003c01e030780d101c030f9a0980c0c0e0b0704d0704014013802912007146140bd00c6106541c0340c0c10024500384180034107091002ca042d40c424402555250020801c220605401d80a843e0382c11103444000d42c90940d1100340354020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 157282994 1250 157281744 157281749
    0x9060d090f140304030309080313170a0b1303021c02060a0b0a0b0309060105040e010608060115090506030a0e010b0604080c0112020d020a02070503100203010f0b0c0307140f01061509 80
    0x1129980c618010a20000074801603525500692680840c0002145150740303800510003180000d2828038040360080012040d03c3c542c040424801c0011400c0460640350888075541494251051071640f0001c00e060984146c0a00006030030b01d0b04a4404d414024101031542e00404030700700d02c1a40c024507169002861640c085044a0005074181c001000039500c00c80c25031201001880c04000d000c0140c0c4013203003842c100c2d28203c07001c001c0c07802054401400e030362692080007400d801c400010801c03080483c8104942000c2031602102907511070000a2480d007059510b55205542c902102d01143c10901c102c140401c4121465401c00f0b1071700300c8403070351344010a40442c100300c400740c44a80e0034065601070710701003980c0d6042075480e88a448030003903440e0322902c9200d101f4410302d142060645c5003442100c0c180e50000410800075030130306010742c91591000642180601c810040d00c00811345040071240903801c0d500140c03450b01e10501002c0d0a459454000c400c603036a0811380090425003041d4400308 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 157284244 1250 157282994 157283017
    0x3012f0a0c08090607060e1e1603080f070c0308030115030207023d0e0f180f07020c0d08091905100c1505040507060807090e0103020f030c040f0f0e030906 68
    0x240d43c0c100c5000f03d0200d000300240200b86038100700724a050307101d0101d108180034207441030030030303c003403850310040c0d035640714241641c4010030042c0c001e001041b8200010a503181e00040303040d1529486640710301060034075603c00d0b1503c01e0040300511050201308a60742c07140c40c0618040d401d110745a00011403004030b482032a154841c1001124880141d810310011288000c1003403869003611100014103503008450b075551051100d00c0b002c034074030310f01320310014106800c05404880755a07418002c0b0110402c0944604251300c145191002a9660305041641251060000586800082c0140410184411030003803d088800405024136141c540285009120901e0014210f41d02828000308283c0c00b4000715150034140010031051060000383c541c00c0328003507034841d800c0750784801007100c509030a0702511000303003410b0f001000540351030080600381c04801000e07603058402d000c001400b00d41c1c0d0090018211a1506001c0c501e0f0009072045c5603410000d18003030342c60002840d00049944c86048103408 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 157285494 1250 157284244 157284247
    0xb01150e1e0103090b09030c0c120703110a0b030106020c04060503241003060f050114030307050d0c21030905070b070201020709090503070506010e0a0510050d060c03020903012f0a0c08 81
    0x1480e846500030301040390f00b105c02e41030181418140c0a40b40d0384084408140361052020715495401c1008000c0090243ca1002c3c010b09415035840316158221035214a82c0501456804590548500c000314001d20031a0000e040001a03102030000390740e0280d208911941000c14004440c44071407040709084910013100402c16507801000d902404803d400242900e841c0115481200c000c91780302606983c112548003110104400403d40e80c1e01c9510700c020300541000101006041c0580d1005501c64440c1822840d00d40520680822641c51490030700006601c2d4079a040a1080a10402001d002c083d024540740000540000c1e5a810040c800c4d10072040c1d68001403401c0c8001403055075481035000065030510b59481801c0b240002c0242c0d0003100e00c600e40400300d414414a01c80c04412100040c010407074224141e142d00f8004c100440c41141410340800030320b03201d954281308001c01103400711141350150507045450000304035180c42075515203508101c485c0c8096005130613640c81c42da1100144d0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 157286744 1250 157285494 157285549
    0x70e091609080709050f0105091b090402091002010515120304060804050102040f08060f0a2c070302030106151211040513090605010b0c0c09150d020307050d0b01150e 73
    0x201da0144580d030140b960303805026804100034074a42c010038013905002c60071591590700d030410040242016501802201c524401c1131031482c0401010f00501c8034020801414894134001184684116410f248010f0750b40d801000320a100854031461040420741d43c0451a004080003182c2d80d12444c000c1800703002c000d40c000340800000f5011a0f02a10132200a4140981c3d580d5059944000035550030545002000004042a0152280b81404200741c41d14082d201c0485540414142030061404000e005029001c001b50f10b090252074001c000c0c12030701c0120072503541401000402402c001303008041c10000c64030256083d480c190750a4903002c440740b590b06555100e0030030041981c6100100b199040c8000002c2c6001038001801000e82c050042e140403d05c3e0404100994508035904251801c21000f1110a8100388500b52449480901183e4080341c5030000614803130f0400348202c40300503107000140300142d082804c080c291881c90804075903031a00d140004901180e803104e010810414580c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 157287994 1250 157286744 157286747
    0x5010311040f032105070302060c0306060d0603080d0f2009060d05070207180c021b0303040b070501020702011b0f0308070509040c020109020406050f22110c0c09070e0916 75
    0x200d40040525a0029a249983e85000c60020383c0701c0000c04072070b40d40d111078603940320b01810848141c00d5040d4040d00030b55940085010b8180c0000e040d054014030140180d0b01829010301ca02800782d80101859929036024806007010380b41c0341e061140a99044c03c03581d44088450401100802225641c0503407030b48000008502a17001d00d09480b47e01d20308110070700448a0300031070f552061341d0440b41c407402c400480c1481502905c444003642801684120034210400007404210054403d0040950340303000c0d03a0700101c41864221180542d034595002600204640e0003406400b00c0310315040c500c4540d1b04058664130f1294107040b02c0601804405000199014401c20403100750700d8000300300300700030b40300d03144020300802410300d0032805545440c05c04600d520f0115124000c6460091030301500f0192030070118664002041100304d5a5203c103490514103a64402821072103c89100400040a00404114904202612110502104085240d203076150f8802580c0d01c08131a40420003801c022600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 157289244 1250 157287994 157287997
    0x90405011b08010501020d080f0a0902060c0f03040e151008090129010f110706030b0a121505340e09090a060509030315011d13060305060f0601050405010311 69
    0x18100507400304407100010240c1c2042c0424140e50080e400c8945c40440035000303480804041d681c880b01035034100001221450950000c401262010303010302e0400340d56862540c6031400010500296410100d0300340710304c601d0842c0142e03201c5005045003d4921100010926182000607900308001d0401c00043c14070f00e0035044507220070303824502c0103a114412144200c00101007802140020a0441c200840360b106600070316010800001800300d03030340380c030a0070341c000c2400c5181e00d1f811a066880000c3d100046030320710540030740149000301c0440303096000307642111002006a41d002e0142903d02940d4001428503c0c3c05031602d600c0c0c00180080b0410503101e044464041550044882040180c10700300441c84070100c903ca504180500e03192041f03c01d4403400100d6038085100807aa401c0b498561194800581c80d20303140d020400d0700f03001d11012500040c10310040e03e80b1540c5540c820010023004006644d40100c010100440ca0b00342000000c1252050384145030416484503901c811080f0000e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 157290494 1250 157289244 157289261
    0x1f08040b041a01060806010f0c0b0117070b030f04050f0708030d050a020702030a060b0315010e0c0f0c010207050a031103160210050d020712090518011e0b1b1b090609040501 76
    0x9000c1e540e83d80d503150000c01441c1c0c1203c28900149511004420781406241000380883d4090030a8146a080000c40e221220680c0407880c01c41c03007502c00002d0704420041c002d602030504004084558a82400e005180922070314589506c0d03030260303c0420103038001000741c0320007540b0004042040e0b20307003461080c042d01a46001940c50300802581c002000341d1907111840008099041d1803031248080690107140e803091152a10b40c030a024006172010300244007c20881403100d14503814100b06240885c220b8105c41c02c1118903034800d84ca40300c10300d50401c102071000e0072204025441c0104561402169040c1090024000c0c1c0a00d484d42c0c524500420641b82c1d8000d0b907840840d19091203040c03080d000010507200d800850050103003c1441d0400d11151542850143d1200340664030b0049002c92600c1030303210b007490480481c3d10100340030303490748001d014460756032a0550620318060307481400d04409403024061032440030301c854901d44524000030341c403c07021103c00c4041c0d5521b0511502401004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 157291744 1250 157290494 157290533
    0x70e04060905061905090706090b0903071a030106120e0c0f0a05151801050307170405150a020a080a020a090506031e0c07050c18061e031b1f08040b04 66
    0x180100500701101c0355041c2490380c481c00b01070055486171b540712622603560740684000254094014406403441000801c099480501212000ca0361441c030880803140300780001c0740381c020010040202a41c041c903c034813002d0f040302c410004030310b10310041540e0f00089074100740144440f00b0001c0071951001c0801000f0100a400c031030090014543c044180d60107095401c0c5103444003c00ca180c01d5220b00182c910820040e11034070b0440e00c045c03440d5441400024011541d6224945070354110300101d68035203004540600700503898a40407038014000560003003034010b441c0d205001c0403250303550004100c02203440a1310303683d559896030005480903e481c0050a1114050f207414045500000c0004100c60b42c000c005498007001c5110400c0358200701c4400651000c00c040010880c640f4101d5200401d80000c0e0b41d010850f11000d00202e82000303007445c0c0080001c40d40c16900390480c01d0030781044030703e070300140103810a20031a00405001130002a02c094100e5200c00001020031260346164154142c0a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 157292994 1250 157291744 157291753
    0x4020d03020a1212060e13020d0c030f060209040c080603030f070c080708030c2119030b0d0c060e0d02030307060b0d050a06020a030c0804020a0b0d0f090c060806030f070e04060905 79
    0x81d035202070402c010300c4420b0341380b072440d00c0400103100f454118034130b026013918608203980034030710f400b004801140d5480984082075481c01c0000012404104500c413144a54005030700d4424850400044a002803002c905228282c0c042200c0c0d41d8021040f03c43c40340d9241d50442d22600039041c040104090ba401032003652085503004600c82d50000050140c840e0380c642110034542201ca001041c071040300c0b60b51003055000348070442a2007807014001e11289400c0c41c0016074010601c0010f48192110303002a124a40c07034000521403980d010503244400501550135085c1c01d0999400319a0320310030700601902c15130391403100c180f031640c1d0554a08540d44d046011940c1d00142410218003d40c07140f0003007000b1a1030310003006c05180c0a100030507c00e0350008c10320200c15140800309a101d1f40b206000000303040e900e0f10b0100c1d0710130071441079140260144551103801414458050400d100c091300e01446a8031240e650f41e884400007e0120a0700c2011501c0d0701c003500c803490f054000e404d0328400103159008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 157294244 1250 157292994 157293023
    0xc0106080a06050711030d0209060c0d080f0a0902090f130b010902120f0103050a0f03050d1d0d020f060703150b0f0a0306090e0307060213080616121404020d03020a 72
    0x300040049001c2c1c09480d0411480d1540f200503112600c0222040440d501b09010038001090b15902900c0c01d0310015000301d1428608800d42828403110000d088086001c00e0203104d00100400d844980c01600a002009281d1640c0c0000745000307001403c83c640c003410700b00051a40403040e10b18208180e44040802c50958441800c100030b03402c03524450702410380010004440b20445460346048a07048005011081c81e59114030885130b0405500f9414883c040011450345035840c40780001c41c1042490700d940341480300c0e882c503003040c01d940c049000715400505d0141070030901140c80c81e040601403c0005407104284004010001a41e0090300b40c0b200110700b07a400740044200804c4880401d503400c010325512580400b04603090b80741122701c540e105001c1c801c000f50450380213018030400c285c045d0220350f5948000514011048500d803080c0c00c0c085209030541504034201202c3c0011900043c0003000c45800b40b032651030001440039100f00b280c4149002171500034850040140c0e005004801120b0303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 157295494 1250 157294244 157294259
    0x3010f0207080714070312050c0115140102011107080301050d0512070f02180108031b0a150b03160302090a0506040207060e1e1507140d060609060806040c08070f050c0106 75
    0x1006004280c581c800e031881304e0000d0348000f0540d2002d596101050302070109101000b221039030811070601034259a50a0f0904a42c4081003044004208140313082c2c2c3c00c00e030003c000909603011507007204403404040c00a140020591010b80c0e05450b026628420078007101d040242c90f1800440c54001c2c1514005003c8050041c0044141c034110300030388030294003030ba00109000f040d200074440c814087d0800d0201c0c1c00e12641104241c140781101c1411501840e030f154880c4110203a5a444582d9291340c0d943c0100000c1c101885100141c510801e80e0760105865074002c00c14000d070041c20509240d5645001401c070380d4883e4103840602d600154200a9504480401561201c0304a034100251420a1088640c40000900c204030150031403681c0b60300c2d488401c019107031a5041242c690792240240705e1100002010700c5248003e184d03e07a592a9a203240c040041c18010300542018044c50501c00b04000c40c5400c0960b07507800c84480c1c505030200c090301020403100750065000c03450040d424103400180d100b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 157296744 1250 157295494 157295497
    0x607020d151506080613230117010b06030103050309010e010302160c030c170a020415080303072f0d080601090f03060603050c03010b010801060c030201140f1005010206060105040b0903010f020708 86
    0x6040c0428000101c3d1101d40a0301e16800072580e041d17125000c024441d0500300190009189200d0343d01d00b020307050103103414582400303509800500343d0080e2450700c48107504007401900060201a210030389154110348603541c03240b04a41c500b50510408040f6450300b0f900c0303581221700030406018058100300c1e0310b1800440c0328005100035119032901c10000b00d080000903011507034004160005080769080303a400d00003d040c2c00070b21800c0301c01468400013420841030006510820455480544180743c81c0e20403042505000e03001165509588806001a100003503280541c3c621405c1c4010103681b00401218650000e400c8144050f410a900004104658004078140d901c5801515442503209050600321040020417a0020352813600402080340981d29850039107000740300201e003c013f2191041c1c0d454600b543c4c22251540e0b003204011041e15006a000043d1209101034001344c1003800000b00b5601030f900031038405000003c6c880b0700c1d540d0258030101003054851400c0d51107000038141080705 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 157297994 1250 157296744 157296761
    0x120c1a071b05010c0f0206190b0402120403050706110405100305060a03050f100f05090a200603042405010f0b1b120913090506011503090f0510060918020607020d15 72
    0x1017500803a08190050020980c94486c000088003400c920b0207901141c0701402441500b82c3c4c2050707081040389855121000d0403485240a602c48541d900302614041088031a00780b40200c860740e06003c107108640e100000409035103103600d40032a01d500d80d080000e80c0c58a007584020030620031031700c08100c060700124018904001040c1d007084241c50055154050707843c219910300007030f0031141d202400075400c040d800311040d40c00140e14030b2100010003c566107030f105840c02d4030380301254040e00750310485003d001407400450034018080b95240c81030340040090300d0300034000004004202803002d0f0703500e5000075951001c4202100d607201080d43d0b003607045620030080b0340d000b451090201e4000c40e8090040c0010aa4400010a50380e0301c0d01c0c100041032160310100c0003c01d0786541e080d00204010104006400d400740d400f8100c1d010080c40c41f10100c0d06164490b4041600b0080c02c0311030305034035560003485550182c0e00c095541d6200d10010385002c003e100c00038000038040e401c014a4408680c4400f05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 157299244 1250 157297994 157297997
    0x6150906060e060f040524030906011505070b04140a0203160503061e010905040c15080601031d12131508070216080d0c05070918120c1a071b05010c 65
    0x21804054140f106522810303850801004082104000f81d081101c1010201d0b01388220a800303203030007180301c0c0c100c551054405002d1580110010b1203800007240c3e50021143c0316003483d5151401030b80e81c40d039101c0c0c03008001a04594604a09000e4024203005a03c202a8018165484da211003802d83c54100524040c4134021300c07554002910049010303ca40e03000722203d641000340b40c0c0c60a0140030103060000c000b00d819180c441070010700582054403107035190249445040e01880d002c0f000600f1201d9403041514074a12400e0300c0b0f103c02c0b44c0800c1c0341d800c0004640c840f659540c40ca503140041e9141d50b910840010161400c1400c600ba80003c40501649d501c1c0c0c20703605902d415401d00a841c500720f008561654004403282c0b400c440c00f4601c2868014400c0c000d880c810359998078004100c6054801e890209030040b11540d0802c00e920001c040d52114904200c07081c0c290548400c05640c090003002846400941c010500450180e8000e19204607040114404001c8916001e800380c03129450340e10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 157300494 1250 157299244 157299257
    0xc1605090403020307140102090a150f031503030507081209070806010f1d060f04020d060603110f03012c0c0d1401150309020f1309140c060304030503040615090606 72
    0x29a45050301145000c0c1d40c05500560800e805a102c0b0303060302516050284686d0b40c208004603183d110040b440c4018060840d41c0b9484004910740030b442040c0704088402014036010302c0400d8881c07450214070603250903140140d00d83c5402d1030881c880c0d00c40e04543c1c4c191072050340100100d501c0001900c8080e00c04580a880c903990fa100940d071200d200901520404140c442c0c0703011409524440030300e5105000808620707844040c0004070b0201d92046c0070400b04217849203020f1000d10b800d801030912481080700c09501d408116a00181640018011100301c0c4055030914582e0014084100a452445018419031404d201d034010a4075801410030704441802c2c1008021107a0700040714078101c03201c4c000c1032403600711003d404500400c0c052600300e0f401800486002a69220341d00343d03940c1da881c1080300296440c0710b42003020b4250340e0b0352820000d95000d410010310350384407101640e170041d41c103040c10358894031103240080280c04242c100001818404000040038000303504600c08481c0181c0311131 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 157301744 1250 157300494 157300499
    0x1050702072c060303070f0804050102070f080c010f110d020307150902030c0909010914030903070803030408040e04141015050a1d07110a15150e0f18030c16 69
    0x101450b40858501c00d69200910006522898001203038000801002d6914003400769552508018103c0307815164250082070910640d40c04200b000050b140c0e01e0380f003840561800303c11540c1d54142030990b40c104500080a00b1030300340941c4580340c0c1d11481c0c9054801d8100c08150080d640e81003420140d840b068180e00703498070101070340b061045032034004d409001d00c1080b210501088080203000a00c81d0342d81e41d080000442e203940d060644146c4e081010f0f6556600e100105858440c05070003001c0c0c41e400400c1400006410042240c003150044038640c80d02d941e03107041681d002024444407a0725030241000056501c48d00341d00c20108008802c3d58054001e4850f4180001d0301c1041c00385080c54940c0c8003030600c00d0750121510543c0500c00b440d000300410742161150342070107260070007143c3d5501000030300300642c3c0084c040c150b00e0b090032103c580002c500c0c00b0340700c01205001034003d04c2c1801d0b80d600426503c2c682209040b2204940904980e51801c841c0e0416580380406a00300400d1a10f90201 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 157302994 1250 157301744 157301759
    0x4020f010302030603030d0903050c15010302121c08091c081e1504051f0f08120f03220c060504030c0f12030516050a03080403020d08070f03090602090405090105070207 74
    0xf0b49002d114098015824981c56040100082c811040c081d41840b40610200b80c0301c0c80200f045d540720910030511807025502d5441484110a080100301c41a40c112041034002e44282e240051060400ca26000440752030704800141080f40101000c1c86c0008000c3c982d64289800c0890240034004101c1d20000d1020f0f180540392100c88195a90142031034000300e942003d1503d5048113400c80701161050070700c20b40d0075042180041c5142e100078030203800e0304010405180184115111406101500e40c45c01c80680341c007007198070000b421000328284544a0380c620600c00165142d4490303122850744d0020340c40e4000940f00781c0061200b2260f1100c44103010607400d9507401c13100308030f503001d80b00c0c0182e0724210b0380c095406410100d5a0303003120001d5201c045c04980b00300000c0044500030745603000c40c0c0c202070500a080545e003080160601c5010028000003660000711045488054500081c1069003840c201020b4807880142c10b5006044c01c060003071926065000601442040d001c840740f8035901c104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 157304244 1250 157302994 157302997
    0x204060f0e0102030f07140d080417040e0712021b0102220506040b0c030706050703050f01060e010f0f02211306090b0702040b060f030907030c06020c240f0c010504020f010302 77
    0x40c0d0b00681080c0000044120013002518485105640c83c0d0003242c50442141d151a4a1700b24030b100084041c41840b0500490103000c40000ca0340d091304501d0541000b814807440400a04240c04104040080503010402c0d07606031104603400340c442d0b032440307540c41911a000c0c0d0071800010403c1c40700d129504c01120f50001d01d00049800140220341020314150401c541c541140c03c03200310034001088040c00140003031280030700c505402e031030028050404091a104c480d505800200502051546070f20b80c50b0303000412500e04111900e400340040c0000b000072800d0801071450301c1101498140740004252101c800341c004001c0302c542134581159600c00444181d0301c86d00c01d0a800740d108100441c09030500342c114142e0702c800070b8421071900f07103401070345c1855170320480d80f045054000320414801c020f0605108001088948000c0c0942d00710140001c02c111200d0815013400f8501e507400d503050300c4114080e50b100c120039810050b100c00034003106a000c2c2c001107904921500c05215240503030741c080d10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 157305494 1250 157304244 157304267
    0x150f0406081002070c030b101404060302030a1502040f03082221030c020a060e0f01031a0603060a050904150e120a1d090901020a0905030102070b13080d050a0204060f 73
    0x14018440d4001502c0a040294002d54084c2c604940c0c1c1140440071503882100c4038040d1080180000055180a000e44170300088564042d00c40c41c20a0020800760360b0000300404c605030060031102640c0c40c80c20b22640288225444145203200c1c0c650004203010f01e0b040502600009100c54050010401441d02039050a034007030f00180d40c5600004500b003600400c10f54100610030308008481103010f0b000540d0512a43c0e000d00005500c1d0441001141010000014810350a003030900600002990022542c088024404c1c0104004000211255141e50000e07005100c0030300b004c02c45040509127440c04844020303c001005040110f0001c0711000015020311035407501e103003c1d040c2400c482c0b081b145000c00c0d003000c12081d802129054803a6070794481da213004003201400160307101d086080244c03920302c0503400300c0d119900c14810107004c10b0000251036885910030383c200300384584c1881c010b003081c00b8912a4100c480c4c50031007007180208055000700107032000c130303102e14120300c00d4450115180354144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 157306744 1250 157305494 157305509
    0xc060a061215110414010e0114030606090301110708070309060f02070b030a02120a0b0f0616020405061c2603070c080c0304090f051b030c03150f09150f0406 69
    0x7500340021450390070250480d0184203101240c0300b03404240520103500503401c00e9080d00c03490b078a440b80715a04510588141d030f2081c2014a400102400801c100380002040d941c0220340004001000756170030350120b11610081c0400f10349030201400c201c0c085402050040300403070781e01c3e0f1001c0744281c002c070300301214030031981d00814420b4141344d4184602e0300301602d01307103446400740040c80715440140c4000d0f2081c46a001c0005161400c1c40c10005101c08140b0f0b03070f501a00c42041082c00c4c400e0054910110160180c80201c0d49440307540101c0c00700d01800c04044442801c0481c0c0000f0060f450300c085140c99004942203414024000c18403620b4801559903402207428a040400007500764005010101140c2d001d40e81400d641e45400c3d4182e8184288038108a65500c040050181400c01d641207003c445022150552500c2540c42d8040d1001601803c1003030316418030101142c3e910300c20283c0401024114021500384a03401ca41d050001082c240e101d682d2440c8254420b0805100700c0c0112460b5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 157307994 1250 157306744 157306769
    0xe0c04050d08070203191709010504050d08040531020a080403030b010e03121201140a0306180c0b07060b030f0c010c14010207051501050303120105131506050c060a06 73
    0x3408100a801140c481e4112088541400390402598040c803040e144c403000030144151000161400d4039485500c12140c490310310082c01091400e03613100041d41c06882c400d680c0030740c01c2d02c0305091410990185a000684c011195101c0c0ba1a50515600420001d81105448000d12040b01c200303070142d000e5140518000b4050f04009004607200c0e400c030108000341810405003050000007c070703080452902030020b45140015401d54420a1100014014846980d54402d50510800024104030440c03001409481d12030345c950001c15000c100c1e1049042e485480060841d6440e0004905a0848041629540d01e80741418179036003804180032600c501424044c04180c0700d030400650340c880d501070707042da00d10412071010b6185450900c002c010b030714040e100a240340100c00f9403141848a050b0016800381d0000c2c004620b2a000030b01c0418107482003203170038100421144002800900c40901c0000c02030440c1c6c10f00080c110741210040000c001b405065544c41d80c6c49400038010740d40d50740300d00c1c44800e44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 157309244 1250 157307994 157307999
    0xd030b0604210c0305241509010b0c0709021908060103090c0b0d0905011a0a1d04030e011e050418020702060301060e030f011b0909330801050415060e0c04 68
    0x40114808043d02c900224201aa100e4075914a0124042c00803207034641505001d032034141c440d83c8542c0c1d2207103400368103c05001003800819081141032041000c413080c00b2480000258040c0240005004400c2c07003191142c0c025000010552a40c0c1c81e80380100e000704007c00c1095229000e1540718580103802c9580c00c629003806180541c1c011107000780701030340e40c903090341c0066001c1c080d007001c0c000c561040403c2e056042c010401c8040b16548400b28403814884030320f07e9240e03501c107019802901810405e8030500c50354016581d007450305800c0c00b0b00c0d10741c0e0030f10500b0031a0003002400c00d80b40b440154001d04c0200c19904022442100c1c0d01a50201d41400100002c0f4403a0800301026600a019285208810f400e118290744882c000c1110711302c110b2a00d515122b0f4848911030080c041c420051182c03c180000304400c4c100c1444058500c5000300c0304001021103103a06103001440320400801c2a490281014090302003041402403223a07091560000b00a64030800542c05030803d000f0a0b45040d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 157310494 1250 157309244 157309289
    0x31d0c01050f04030b0a021209060f04080307033207020d140a0e130b0103050703050c0a0e1203120f070f090b07061401030303020d0f0c0c0b04020409060e0d030b0604 73
    0x4100c1c01251240b018104804800190400e410b5409041d0086000d41c5800002011001b0807000030400480755001000704030603042d80b051519081034110481aa43c1c1e1140340c400c9014010031001d00c454401403a500c0148860140b2801580d54580c01100c2c48980f40c080c022a11085040c100c0030000740c0c00340c8120f05408841000307044d40051400e09020f4081e01001040f034901d080e4241803840346e038031007009900f541c16004883d44180c15240401803841e113840c031a0100e02610200908000c0b84286611540e03c6e441c00b4200610200c40031242c490310f44100808542500b00c4101e002400000c2c0451700c2075000b500c05032100d40d5a40c48801c0e001c4d051980c503090680181d81c05480701620b4408010101a03e00302c3c0c240694000e40e400359481580070468016955950306042d6440d00e42249107068070f511050301441c07540e01079640c1c0b03d2a00d517400014041e24603164050700d11f510300110030404040014403501039041c16142401000003440411045006505c1141608034000d4110500e15 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 157311744 1250 157310494 157310497
    0x100f1a0108090c0306070c1202070509040f0201030603150606020708070503120c0c0a060c1a04051e010e030301080a29131a0a0f0b0a030f02040507051908040201031d0c0105 76
    0x618482c08540c10684800d00185c90410705441c4107000c51401c00201041c03080207080e01085000c18001414020324000209518100061000d065500a00726510440e8801d4000d10020342cbc000202031042e000d12000d060060113a489800c015210352240040e141201043c1c11003201e000401a1060f0800310308891025841000f10540501030402e003500c082c1e540f851410040d21003903994007071b4030000746080c0002901071885250480803810400c800152300149242000d800e42c0106841801006c0201d0302504079070b4140c80060201100215401100080500e41d15014003400034513031641800c080000f20340d00725812843d45d0329000082d812100b4680ba03882c1a40b00e000760f1003184210714082510310100b0744502ea18a0f45a0420030450545030141c42d059207001c0720b1040807580b840d40c605000823203109000740034989820000380c4081c01001035865903001e0100ba0300070070201620051400c01d040390b003240030078a0001001c02c0c0c0c44c054216201250300000090000d00340140044d2040d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 157312994 1250 157311744 157311751
    0x10f2427181415010801020c07031e20040b100f03180206180406170601052110060509371113050301140613020705070504020c100f1a0108 61
    0x29140910981d00020004440350442110b80e0026283d8901c4809900301d5000301a40319900c03503801841304400d070010118840c0e045075808540c42c0440d0728410307942c40c4000302da01c3c0c01901e0405140800e6141419240c510b02038900304a9041015000c4002000701780071091607000e0010700c04041d840383d818002d034800d200601034905070700c0501d0101d90000e007244e4001c940c84001022400403481060406d070003080064031111405e9425122080e48043c2da0b1801449001d100b0001c1d40309030001c82c010700030b841c0e512400201c25101e20482a1140d007018107da445480d0040d008400022060fa42c10030b40c803120f00c5a440c84204160500c00e0300e81e03440d115078003094810a650f41011300380704020400180001202d400d03c100e6194500b004060850b0203561591036242c407000c0070818680c2ea010702440460402e4800180c032081e0b5420708514003105038116581091000581140c803140000e501c0700c8200c040042400f1899080c4104c1e019501400b0700756000f102d140f0300400301c2c1c0d0300070b5401561 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 157314244 1250 157312994 157313021
    0x10507080c03041106070b0c0903010b0f0d1709100c0302061f03122115170601150e0402131e150c03021c0c02032b05070302010f2427 59
    0x5010803501c0c0c241f140441641c148583c008001440000b5040a0080f106c1500c0304992944c00d070401c0c240071801c90241040000c15012000c0e90380d2004000c004103894240001901081806807803507005403501031000009d0700580b0401d40040d0040421850030002c0040d0004102d18061441e07944d83c90310300c091047c3c60180012800306d4403035401c0c540e40c545060828911b020800d926401690030440344150425034504500d04e84801030351400164150450380d609040e0300c00f00320800e01c1215000701c42d00b0305540c400e0000548100b41d01c401c1d4030360000e13100303d50502c94444541404c00c0c1000c4243d031065006014414019490950243e100c1c1d4080900900554a0154030800302e094841c1030b80380d42c1c001140403800a0700650504200440c0340035146076920002d000f03101002040007040c020409c00300040001c82c10300300751013074111105030790840406108409010302041884030a0b9400b414020862450001d17560805074075070400c541094080c2c0c5212100304140002510607050f070800c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 157315494 1250 157314244 157314247
    0x5090d0209040602030711010506090121080301060f08070c05060109111b010c0e0306040317040606081605100302120f090f0f03030712092a05100201060305010507080c03041106 78
    0x200540c071041d01c5a8400d6118103401a600c1c500311030701a081400303250b81e00f80960b14250130130a00f915800d2125064a40200b25050702003001c0300b9402c016055103c00610f46000480001510354001d440342903424403d48070042181c0c0c074504119604e4404400c00752441c0e01c134000400031054a41c1c84107941030640e414080c03418501030240c3d106803400780451040360790364020070700f507442d401034602154a0080740545800d0034207480c02060780c00886000c0c00c400d01401d01240170445030341d011000821500050701da01003042d105220404140e0320030307a40a91150040402228464070031211440c54403885100903855400910b4420300004124465500c0b482c070440c1858002000a0703203228003080c004548c0c0c0c0c9803294000b03040e000f84034805000c41e402c0800d200e0004174200707801100d4600c0c40c13501d9645c41242461181644aa6500c11a041090040d00b00c007410b9064002c1015a4043e5009100e540c0f40c0780002c481c61a4121144040c002c41031000c0360029007a12842e0000c11001032106 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 157316744 1250 157315494 157315519
    0x50601050910110c04051009050c0d060306050f0604020307050d0929010311030c010c030507020a090608070306150501050a14041e05031e0c040207050f0f150c030c0a0509 75
    0x31004142201d10b41c02080e41c0010020b82c1407801c014441c4500002e541c1071100b030602002e800c42a40c940d01a00c2855516100041c85a5854506591842c0c102501c14042e0940c0e03800c12100500050300c1084070303030054100003121400c00b8003c89000e00613640d9820b24110244662800402192004031002c040c0a0705030200c45422144060b417074500d050319400345514504c0d28081c8090040040c80c040d41202050304141d03030300204091041501810080d60b17920f4940700049a0b114281c01c450006813a1200200d01c49800207200301c1a02d1086000f00003001005180c0450703502c4510416001500402c4440f00b503520603408a65000c0d4032003a0700d42065103411025028000d06883c846103901c41400401c61407034200700420480384c068143e101a110b480900945070032485a1032800741e9000104e807000c00c842004694500f005071410b0f250281c440d005825140c2e038001c88000000d00762000458202c0c0d842c075040b00d0060300d28101032413030050320130030565050b085076048551000b280341c40c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 157317994 1250 157316744 157316749
    0x120e030904020d0501061803020f040b0105090301050403050307030c020606090601050c0a080309160b0c07030816081c05010509090601030b0a0609050414010606020a03230c0d020c010816080a0506010509 89
    0x241035103883c1d5400208a03981009001400981d4030950f80d0803802030a0010030140c0c0314088101141002980d01003124105100160391910075104c680d82c03d5072901081000b41944003001d580941101e541c1404a480420720481e501d6000f5120994491131840101d03040f503005c1d02c0100241d85004085d1000c81d4100d860729025500100e80e00032242e04070380481d0300180300c4d100345e80c000707403011201250801303403201000b0303555451a0100500003c40082d41d003040041c0a100403101c41d522540480e660020148220103c081048107444110b040100100d15440c204a10b94031610f10071005011580c40c50b241e03a0031000c00079000007030b2103070341d010085016401c1d402824495406004c50840940b41c021480c2d003198001da00810454000d003540c140003035403084006c40001400a03003121a200c0308000c44020744100306003176115204120380c04540c180c003c2010564124262200600b0740e540303145034400d01040000e0381c40043e030100d000481035146a807041d50095018501030382040c01c0c81d0301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 157319244 1250 157317994 157317997
    0x90d020f0307030c0e06100203090405040203010e032a06040506070c110a08030912060c070204110d02040f0f06080114120c0a0f1e0b16060b0d0807110f01120e03090402 74
    0x19130310703150300c0760040c000410011032403604141c00b47c400c4180070300d083c1c20094803402060080b5100365128004102550350941007400b052122006480d03440002d200211030440c1d0b6404030103032280c044101d812495801103901c070701c515040006010790b03507038580003200d9080360f8160481c1c81d0a221100f11165071038a01244d000f600040e0300450b5541080000c2100c1e42c0b5007841710824652002c002c11a04002160a1341c010b141d0644000c80c0313a00801401030820702440750300c020094804500002c011110b04040720485114050341800d80c4e480301000c403825002406030024910702e01203803030000e027001a000d070540340841c0195880c10a2481c00180f2520603035105041c042c1000c1014400003070b850085a14040401040400c11490802101014001c0c44442243d00b15588801e005001081e0003042486d030004041d4081e054461415040c207803c4128150303000108807020910a0a20612024030240141c544107800314214103c1c0014100e00c00700c0442c0d40c0402d12002c28540ca80c1e00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 157320494 1250 157319244 157319249
    0xe010308070201030e0a021e04140c04170c09060d060e0708160602070e0402100504120614150f0f040b0d0b06031c05070303020901050705032110030206090d020f0307 73
    0x250155641d0301140001425201908020001504801840380043c0e6642c60400800e40d452011542c0915500001600402541e080b03d0002e1120350108402c0145590040c000d0301c803043c418a10a00c4542c0079a56a8075442c5c107c80d412445500101d1903629004042c0e0694600c29100882c81680c904260b07030528400740d00c054516880400c400e80b10107807001e10b51000d85030520042c1441490190820b020410107032019010311914058100e0142c0f0440884003d0540c10520f443c9520a6241c142d0090007528200c0c894640341c040441e1506043c8030000c10320071002000040d00550000420034040210480540d00580e00d6040020715150503100c03640f01c600500c00c64020f032409509050070140382d990701d1600200c072044c8252607103821005813084030f078161400503202c0c503015005945510030380d40050302320300c00820110f51075601d03528211128103840c10b6405140d21a031003c450910130360302000703600070414040c682840c1065003104000302d000074844607030600d0001c080b82c01d0139001d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 157321744 1250 157320494 157320503
    0x504140613150207140f102016060603050d08091005060f122109040612080307051e0415030f0605150304020a030206190206070c0201120e070305100606030e030c07060807090e0103 79
    0xd010580b07d8116841812040c4c584413100c000450006020b07040e0500c5407c01c240c0d091300c107080001051008907484903000c0c1d6400300c2101d40c541c1d480030002d02a980e00315a210b40c14032400040d90b03143e4001d0302955000f40c0020302403001e5000b8420030802c420500901c110214440e00d5091800741c040c80002204d0704c01c600c40fa01d641c6041d584148800c0c2d0b9510780010400d14502c100c0480040c0108049aa101c40300c2d00d01191503820039420b890388002900c800f5842660041400b03c2c80400307180c002e407250071890300c08010140c1032800300c2e42034403194420958080009820020038020031401035500510080c446400e59460b40e000580c00d0304071514004008000b000b80712030464040160070b8105a01c1e0410350503440c45ea0340024180000d064590b1b01580d1510503941c004a000c000b0100659404415560451450f41c402001446035103d4440040c1c10305d107202c80940408400c8071100c01d41000544145da0a182098600381c001a00e60020001840d90026040104a6169019512070b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 157322994 1250 157321744 157321753
    0xf01020a030b011b0b0105060f130b0c06060a080613030207080111191d0f01170901020a0201060f0b07111306060206041709031e010902040504140613150207140f 71
    0x70070000511680c0300a1000644d503495080321404152100041811603004031001952200c40b00344020280c0200d940c4599074034014000410311804180250840180c0f980440303c4c295215007c0000b0b0101c903200d0a0a103030040382c04aa4072492504440301c0c810300900484140d1903032400314500712818a11819a0308bd004030b02c0c1150006090000b0210001c50300d4000b0281800f049510791014900c10003500c5400001003c0d001a400317440c200010203110045151289030902c8458080c0d4002c81c02d010055180020100c4d03480045850401a04c4401040703c2c280b80c070715600d0f080c01358210b0305a140d000c415007a100c084401c0c6401035801610741a805031486081500d40640c8130a4650800612060240900303503994400098900d00040c58001021800d40c9105419005141c0c0c2d9801030f420a090008000500c0155000d07040c21441d000c003140d50560700c843c55000d400001c020000c00c2e010300400010824203060300a058503a029215014880c80301015091811a000001280340c6d0030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 157324244 1250 157322994 157323011
    0x6040b061203031902131509080d090e0c03040f050303041401181505060406050d0501090c05030111120c0904060e090f0c030304060305100918120201090308180f01020a03 75
    0x2816201c031500701c40000019421810a007030840d0791442070322180c500b856408150401a00c2c032045161004104100c0100304603030107070000810400709805152450f10440071861140ca2180344068200c44000019080540341c083e9440026407003d0020344e407000c01c02d0100404180240000c50090f0b200d9070704c1500200400c0202402d43e01c0c8108085503100380c00600c81d01240d482d40100001040701c01c40010540d6414000070700a0a0a420442d00032117840b410744100703c015404560214000c04405441c9a0350f0410542030303c42190204142090030700803030800c1c2420b17040143c0c00c90f0341d4542c0d090078500c001d070100d411210158050610444a81c0c18000d1148041c4401c0d2411410320016220764601078002ca90344c2d1240d032213641d003056940c03400281d8041410003014040c1c6a84081071186850100101c054104480010785600c8840c0c4070303501e0101c1c0140f180300d030a25071607100e00b000b556078402440403e24a0400c01d2003140103c03110100091401c3c0f005003010025610001404070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 157325494 1250 157324244 157324249
    0x10f06081f0e040303150e040b181002070201080c0304030509130906050c0409050717160201060306021803060c0c06040f2118050303041a09030f0f070918170a0e0306040b06 76
    0x207417020381b88540000300703510901014159014840c0d100390002d00c54902c582310b0030005a00484c45079104a403500070340e07520419444254000304802030003607a8580c0c59880340b500b0504148001e0781c0080108804114600703045c2410344040d1a0b815201e140000d071180b85852b08021f90b0021134030b40445450000341840050703d60710a035030b00807007949449450302c4160641c1e558030b4000644112107080c024541c408110f03200350084009180e001d00295110a02c14a11560040000c20768034402d010384070008012085242c1a2860800301d4030080c90b10b17481c1e41c1c0b00c000601030a080d0540d40d0400b20b000c128000f29001007211180480d65940301303513201c81842850700814254119070f00c2600200420422064113400c03c10f0171b40c0c0ca50710560b40d62074400000030300e00b181c021840ca02c035001c1c820005003071a5001c0742e40800c842481a050198100032a81959100e8500e000144030f041802260214000d9800c0078142c3e0966900702a1248027440c00020314001c0704850072123468262404100c10390 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 157326744 1250 157325494 157325501
    0xf07030801260c04020904320601020613020f040906090b010306060510021507020c030708010203060a06050702010c2a03060504021e01080c030c040e0109020703090e010f06081f0e040303 82
    0x100140d0003089072201640300961a80f842e542410721460b000b00e040350b007554450340600e100080a4100d07074804480d04400400e003544121904084203a0070b000102154004100d16119072001e040410b071000e115420042c1030a50300ca92160072a60340c00d08000020140e02c54000d006000c3c500341541c3d503145240103000e848881d0801401000c40780412903805800180000c0011013002c0c26181c9a42c0c1c100c412443c000321154090f0b0300d171203881d0b0001501c203c10750065000700c40139100c1c1c142c2c45456900a40e60f5101c0c0540090008103007985080c00304041200d00360400e01072565262440c1c1c0b403200d0b0340044a0107900240c0e03800d40d9810070f100852800d000f600c50300c45041c18222500b4000500068a09040203114040649000000071440d041c00b4003203034043c02609558001d84e5071110201c8000350400d08044001c0307800407401080d1080c1a410850480c2c0d005240b2018030b07400c1c51011030f2844400307400c0b11407004100c180860000c003026070703000240542e503140060038981404d004065 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 157327994 1250 157326744 157326779
    0xa0b0a2015072a02040209030312010614040f0b03060a17030a02152203030b1e090a111c0b0301020705030a1403101208070c060906030c0305010e0601140f07030801 72
    0x3030040ca103541c1602509989211070078000940f494821140701c50001c903010f44200850b1560501000420501000031800c0c42070589030248e90356911501d140c603c03403505201d607000780120f80c0040c074401c0081116403401164030039800f07000300c0c0c0c0441d03886c101d298258800220404868002240450300303140d04014480d41d143c20401c440015050068141c070032000c160224039000b6040920020505009801100c2c0000c0e001c1c0c6044021143e82c4080c103288064145030500c03920100f80410302d07140ca04c0c0118050079901c4200305140c40d03100d07082900000c1041d00b56400c1c0a488654004650b542880980135083c0074001031651080c0c054001442c0c0c540c000d4110412803010f105015203c00071100303250a94144441521500716a82080d1415025080005080c40e4110001050b010760190b1040c0480307585884c01d12005140450035420780b14240540c80710400c401001510710342c4160074080d00ca822404d0641d10340059041c60f2811940542c1003680070803200b000402101c0c9200b83d115030b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 157329244 1250 157327994 157327997
    0x4030305010602190c0905040305040e0c030403030e010207031215051201020a030b060a0804110a030204230901021213030c0b0c0a180e04061505030a11030c010e0a0b0a201507 77
    0x121340160b40c4880010b40d650081040761540d07400000c0800d402941220090910b0381081c0400e850101d810b54000d901c1280c045000a0415604032000c0745c0500030744442c03542c1515251003508440c040e100040c078848030700a101224403c000905901e40c001c0b00544a41314600150b81e40810480146c15104039903c10384c0154402c0000000d61948001e6541e0080c0d80141c907a6410001000003035030804a176080030350f0261404104175180e03a0500304d080c1220414070b682803242c2d501c150000b4200d0140303000c81c2c0518010800060300d0112a80c1511803007512a061441c00007480346c80e0441103060031100982845800a10320702c83d26000800c10429542d81010400942d00b88030b0a603807229005400141400e8442815040400e00c07855140042d00c0040e0454440034802c1c03c0400000079140c4080307010b4010070140900a502c9044454006000544001007491401c543d01c0c0c4e03d170f48104008130803c4a000c140050b1103000f0b4808018605200000784010580b40b603000d203008101405080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 157330494 1250 157329244 157329283
    0xc080f090708030307031a0a09020309160f14030109060c09170109030509090711010e011e0203061c1b0e070201050717070507021305040b040c0b03010b03060913020904030305010602 80
    0xb02000000080340e510401c1c4c0d00c2c020400071000c006400d0800e6800c040a540000c0e641c1007c9a8000c031035021358030540840040b1581400a41e1088007a0b444501a6850703803500c030380d800e018143d071103a10b5803900c2102500010300d49409869110841d000902c54030002062403008200e0f2403884000ca0342d11202c03220080148011594002d00180300b00d160540c0901c40328000108014010b031000c0c20407941c0390703001380034603200f0300e80040c002c1c40030052181d0300c540f0021070010201c00c984240c034420b5102500114800708a01c0400390708680a403011240d1805101481d40d50039081d905441c000c0c0f152140540c0d003410b00000190a443d00103003110704210040410103004440c1c280d61070740008c02c034184140c0c2c4500318004582e00d10f5250840c45110b41c100070a01c0204200c0c02d83c4030707120314050f800390f01001d921089249075500c801c1c440c01441c41da091010940924007140207030742001603405c0400e60390742a64041507031004100c40a4020a503601d004200081e014001c500500180030444c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 157331744 1250 157330494 157330499
    0x16080712050c06130201020a051b03010f14010e180709020406080601020a02010e01051308071404060f03030e01030f020d05070309020108060f060412050c0310060305010c030218100504090c080f0907 87
    0xb0303595640040901c942181e0349a44c20781564002e00c281600590072209039101d64181d0307561320300c001174012003503030196190002414103240d2501c5a50041e100e0414100400d13440e140c0180c54181e806003099204070b0000d92407904420f4100440380c02001d02910160b00c1d00d251000241c041d502c01883c01e41550812203103000140e0380248000c14401c001d0038030a07102e401c0841e04aa40c2e07111078021090f01e02c146000407803c0201030754101d02c20803080b6014000c4e903445a5000340649860b10000700411001a0212010740c042e03005402503030b003041c00041c1480c201d850b100042c1d0700300352206400303e9512043d41c801e550703005802c10342c00700042e10b540024850550101d03940e031050f0b1151401028924400d403081007014082c0c1c4151010040c2240c010300d40124440c0d0003000c5502c41124650303e050555030700c2a02a0003641c40441400250710f000203044d5050204421800e4018000c1160800012030078603e2482402000d524540e150145881c00500703244070103c010300403407056413182008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 157332994 1250 157331744 157331767
    0x609010b0702130f020903070f08100c140a02030904050f150a050303070b090322060306080118020d0201030e07120c050f0f010c0f02130f0f050606090d02061608071205 74
    0x2480c00c0c107102d03c0c600051401d400e21300e1400a02034112083d070f06000e20b0740c00003400f00144000100b0b4800d0b1105032007031144100e00c15003c5400e2420304601041d04501c0c2840031200800c0a41103100c10750060301e1506812000040c200c6808444038003050f4220300030312680f801182004900440b05442c200e030a1410000044d0b0f8074042c50200070102e81c0f40000184159100f1f10a6a20f5400884888151165407550f03035003140601e806104000307485d240380024a51014014001c0300b41407075401060210721340c0c003403014031180850107a0505403105c3d111a1424410080e51008002d001501c00240717841c0d1400e5258900305501445c0310b81c40c64412410596218000390844800900f40314869014034a4404100b4040000c0a5070020144152485aa81c6a00b16003101e0210100c05c1107082359548000303041381c005452043e000841481011804e04182100013001800280000d08018040e40b101c5490b40d508101268904c802041d40010884580c048071002d01071810b0090a003031907180b4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 157334244 1250 157332994 157333009
    0x305030106111218120703030503090d0f09050f03011b030605041a030304060e120d021605010206070e0105031b03010f03290a0c110307060e060717010e071b0b0609010b0702 76
    0x42031a01413034500c94840381503a8024003078440300354107429075101941c1ca04003d0015002240c401016001e80c0c0d805680c140d11540c0342c20002c441035114a1445400c003424007208140c1340c0b40f916091341d642d020741c1d030904100030001c800c0c0c0c84541d1b4000c58007904040601054408402140841d03030003008503c90340f541d0100903101601d40914000342c400c85810f002a8081101002c003100c0d0b07000340c20100000ca6800300703496080c44c4901d81400c0400383d59800499807407000701c0b010390002c1c6500808064540c4110001d60b00000c0360040c0c1540c0110102d0b201e81c0a601c2a8000280401184010020485492034121018080030692427490710040103180386203400501c03003500c071035807000a141d02500800c0c0801c80501400704480c1c0740d41003450044024054030000a07490300c6607600180004d4401e07228a22104040f40911189034a01851849a101c020f440f010030301c03070040e5407140c01854030301c40b0034aa03500806040342242840c0090000c0120103030440e12801400300720050160f2149e28 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 157335494 1250 157334244 157334257
    0x31109040807020603010305010903170606031302033409020901050d0f0f09030e12071518050924030615060c01112208010c0c021203041203050301061112 68
    0x11012102551a8608201c0d03511800000940c40300c0003100100134410305500c025400780c0b1035250309006261540c0c45600c1c8071002c0f1540c039802032040001070300816031215407410483c406012101c003080000421080d2000280c078044410318840c08400b407401c141c0141e00700401010108514041e10000001e1161103500410b484442c1c5070007030a034005425621011501000d01002c00101c03865280c01410011060a40e038803440d1004200c5c10304810100345002140c9030803089081d140c0228000340d80800c4c1c0b407001c12010003001180010b1544440c5031580c0b241250030740484218880304802d490920329190000d000794048420880d20304000001d0302a80c0904403911503d8204102c0703c64090821000da0500100000c1403440c801443d040c000740324142d061290040850312030400908a40c50b1020150009142c41d1045000d0300301051218104950482901d1805445072040e1005400e01c403001c03000100008010449250310150700c040d800844000350101c80300802c1d41101d9801805d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 157336744 1250 157335494 157335499
    0x2808070c031107060309121107120f08030702030a02070e010308030106051c060b090a0902390a080d0c083313050702010c090803030106080a18050f0c04060311 70
    0x444000c0c0a050085241c0c0c0e16200c1040b04031031441d0745500d001406443c8041040b40c00c4840840c450460b940146030005005c0f03120f100503c0c649140c0455085520346206060328000c20410780035011510a5004502c24085500103591301d19019070000d150000d5603110400c1510444014030000d880b1078100d0703046421a240031510b0700107a09a5103c1c0c0000c41642030045882c0240019030014030001404407008101c5103054a075503100500e034141d05c00c150142441354501c3c940748000e00c80e02c011103152410340c2904d040c101c001e44820380703190160100050350b5190b070100b01d441418086020f0109100301a1030191650704004598061007446a00c1c9a402c0410568928ad10102d10303030124041c1c0c0400600c0091a004042d00300802410309980000055003402541801c207805650071208454041b001189140e2a0410031115403401604904046446105440143c101900041c0c489405a0041e1411040d648500392401d1981c0003540e000b03600749501000031030180c0598044ca038105 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 157337994 1250 157336744 157336757
    0x1104020307031823190813050a03060504110105090108040303052806140109060210050603010906090602030f071409040b150c060109060501030b0a090902040e01060605280807 77
    0x50307980a4014142c011007810000d1000d4820005200010180d0220b4214181c080f500c0020340da91195160001c0c0380010344515441c1500342d0000702504020258010104c0c1c10400160321800020aa007416a1050781c000da12681030006001d07010740304807594482400c066251500d8100042c0c1150401000501459500c00000d541244100c0f4044601d4a080c20641d4400100751a42002030007a0f004020482c00384802128865000f02c3d00700c816100341c2d0b00106a440303100810030707001e410001c20594065480d01c801c440014154040c9150036481580056124607024945402c4000001d004c401002030034049040110010000c94094042c26140410383c4016039010581d02d51581801c4036844400040c10680c40c0c0004c103003ced06803401200203110b0340d603544004409444426003040c1c0c2c400d1440a080088410a42c80f00312010320241012440000140c0110b00b15032103640218046107000510801c0310440c440c0c21940d5401c80104d0071601100c0e540018140c0710009e241d003060010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 157339244 1250 157337994 157338001
    0x20a0c030207091e18122a05070e0c0d020a0306030b090c060409110f0703030c14071505070309020310060503150405030a030c02120a030903080603032106150309070f1211040203 78
    0x203071a80c81035482a088440c1400b441c8640000030400d2513581d2640e0308603200454a00081c2e11f000d500c034a403c54104004000c0d450400c0074503240d03044050a10704144104101c101009002400074121805064034005006451810120b619440041c2a490a80c100304a00e18140d5225010380b800c0c0c4031540000288490413568040b030074480c003454550383d1072000c1108801c0541c181c000350b80c0c082c0540d4440030682009030849440d80200d9074001c000719071030b51014403c03e0159100c2c5600400514000c03c45814030b402080c100076065040a00150303c401042c0424101042035001d6491400036003001c0c3d10700b981703d4135103070f005800b010402c141e10b614241844070700c00c0069840708286400f00580c0c45000010290052072403100440114080ea00003450b58900407040d1076000081031880401c007000c0782540d19401400800075580a00b20b8900e201d8003403c0d680182d0f10600f48100180811401e00c8200241000300d5030021090058541100740024803500d2aa0f1039804295805030310b070f44 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 157340494 1250 157339244 157339271
    0x906150c1412030a0b030f0303012301200d0201051602070b0306010306051203070204140403020d08040c12110906030705182211101b11030709020a0c030207091e 71
    0x500c05802c5000640201c00e01c10159650390051958003012022030700004003c2c011940c43c0c1c0024421610300444400c07200528601000569100303410515100d89900c041c621004810246108059042c1c0c1c0045114020701c1d0b02441035607001205281c1030340100100100095859025001d030034012a008404110707940d0003504040701078200203040fa4024807200c54010b81e26088044180c0c8551700380030b1340880610703c1028039400f694255014106a0454440507540030101900446005240c5080000c0742e044841841c20414880d052f528407c09416003040715441c0d0150901388203803c04c0504000641e500b40c0b00f8082c2170340181e02c0c541180d83d045840c200d180c0d108005a141070700e0240f01c540400404542c4c101c1034000c211180f83c039644010204076100201c000d124081030405081d58004143e40d20154420218000e00701d039002629500002d040e03030442100140800c0310550440100740e0140032032006050030a0040001b00c2000d00703c0c0c081d0f06200c4443c1c0c00440d43d200380d00307010794 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 157341744 1250 157340494 157340503
    0xf1201020f0307020d021605060405041802040c02030c0c030f03040e07090302100302033405090d081b07080a110f03160303080718030c140a0e040c0906150c14 70
    0x12049403982e140c1c41e1141e000313034450340503110b00c100500860080c410561803041140d02079803006030005003014101010301c0002c155894005e203981c9080d08110300180d85500940740c800c06150701468a0b0305182c409249000d0701d10910307074401c6d00030402030502084000166803c8452440d1030f196642c46e00704050303846031540e400194016404060544506400d80c0045001e00c43c60a010321101c2c1128402000c155212150041400c0601c10048003c5210305c0140c00c940000600d040507031000c1e0b640b04d5070954851440030b8955901c1201c544004141807103c0001010588068200886a0303a50001e0054040401510911004240b40035946080084c01940c1e452003110035442610303400d02400345c0710100c41017400903416036022000c00440c1405407045a901042804a003818614207844001440a485401c001c0300180010b0b0811404103a50140b4040d01c410740081d400d00610100340d404907007080711501120398032a640030740d010040c00e074019000003407061a500c4a02a07079060 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 157342994 1250 157341744 157341757
    0x6060d030c33020703020d03050c1b06010e09060921070602030a0608072c0c07080712200606090603070b270a05010c110406050d140114060f120102 65
    0xa00050704220451880306642c41040c040e000c140e281e0b04111044400c0203034450542c1c01401601309800144040f8080d030001a007002d428491141000140394402c4d40004030b03004010361640c422070040080410f07002d03a1b1030304003070300d031016042c28601260320301d540d00d4820044605454044403000007541c3c100044d2050300380e00100c1555241801154003000d00325900543d0424002d68200160100c0c100c607800d00c180c3c0e0103416050815030080d10350300204030010b1005c03036503550401417080002d0110005006141c450f160980c800d850b54100100148581d8542d6104942c00d003e40c04da407180001916035000030201c900c12410b954810200c4d0810441c0c1e0b0210614840101d11036030b110032100c40c4030188050341c69201d1007680700350040281d880958481c442c00b09994840c08804240c02e00c40018048102410100760195540d0100b07040c10005d400940e0311740000c20181c0b52940c42070042904040c1d051018070050306040f00040c850700402c0451600c51046222031340c0e424142901500c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 157344244 1250 157342994 157343003
    0x6010e01030f060b0d0809040c0503090a1704050414241c031206120312270f0209160e190b1303020a061728020702030102090405190e0106030506060d030c 68
    0x8284106d184c40741a6030441d042551141d410f052203410814868005d4030f100b00300c2d103c018100c009080d11100200725081030308510a107020080814682c89500480d480c4441c0c0058540403032401c0da4007034001200c52644060404980c0e01e80c0d40150b82e4014030354620745404180313041c0c1340710356207010b68400014018242d0070904024000440c0c9402c100c803021481d0081e1580c49013203054409141c1124500315180c1d07030b10603c02c42c1f4251000c85c101101c407103540c0705054040f5250f5650b000210764080442e00182a500003401c4520f041342d02032403007810000c060309c0c0030800b80fa64409030700c12007070700340605441098081180b0014003405801c1000841d0098800c0303242c26214080100344030003118071003d050b041c240c0880c00200442e000b0040c3c00d680459903c0b41d101c44041c44002a510541007030341d0541d024004501c0315652885664002c4180490550411840b0003044094034450030145a9691400d0000c0004c110f001c200c0d194880b00032990b82c10301404a14081d0703204900b0300303030281 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 157345494 1250 157344244 157344259
    0x1a090609180903040f0605091e120307080a143109020415030c0c03020c0906060403060f0f0c020a17091906030506010e040c0c0303110417011d06010e01030f060b 71
    0x4141000f1008100f500c2c1241300c0a444540c54a200b5a29403140040c0360340c11442481c1d120030281c16910ba0440c810740000c1040a030350380800035107480e54000c500c059506060001d80000d0300c0790800c408446002604540600348058464405002403245082446c0f41c4e40300c1012141d82500643e45070007512172290111345480c3c6800c03808841c05201010f07540405c0ca031803150520140210a4850940e0b0325a0040a000d1800002e20852120140c000c1c4d40180c2e040c0400300015106006003007a501c03e032040042d0361015484d074102030701c030768851401c150b42294010708040b0b0100c0101d2040c2200d9003061035518140b001c04030700101801e142040c40d14030100c0010541a61640049018180c00d80ea110181c0d50608100030840d4112904400402e04182c207147c00030f030103030f0091040f40460702401c1d17041598030890034040041000014415075580c2203103172464031444100104010f030b00002440b003903042c404404000030040c08050301c904074030040c0c0402c0041c580c0003007402220250090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 157346744 1250 157345494 157345501
    0x120a0e030408070504050117060a020903150f270c040510031e2a140f030f030706050a051003170708070311100506060d091e080a091a09060918 63
    0x143d20361005001e010710440c10480001404d5600c0445100c220407141c0180c452529101e01800c000d40c842c14149401d40100c0030b81c1c0c1c4086c50185030b905d11494415524800f01e180c0169800141034101d00d210f582c010042e0910b1034001c2c000200d141d0300764010340e00010380d920303100c0500050f6111680018001154031510702c1524501442c2c000800307100c0d07102c606c000304c078028803c54000040c00101c256854041c03410003034034110600b03000c60101c000c2d003d036920842b1030b4040303410700740741d1504007000b907100189210802c1030700e2181d0b540c00307000c42000b0080b509041044400500003840302804d512204e05c0742014001c0101d045800c0540d10185c0a5030f0703000e040ca005482040c5c84000da484e5070240f181c24044190351406000d00c2103100030900c5103450080c01d0314078020300c2e1031234060748c1d8111544400c402040c0b281d06c6540741c0364006c0100c00c0d225a1400001094090740d90089154803030960943d40d40c0116240c00da454a81c01115071945450070140825585401880c0e8960030904207011b1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 157347994 1250 157346744 157346759
    0xb180604150e18100b0d08070204090204060e091608121308010f0506040f18020613090501090207020a05010219020402031e10030c050d02061e0712180e01030305120a0e0304 76
    0x294280c69002002e58000c83c14110360041145c080110300707034000b0154040340b00050b952070300030305010388020000121014160081021103865800c00010005c00034140031004400300551410340803d030b104102240d0410032029198040d8920480c0744030004101045e0790207031801590050803100c80200b0441d922200d40002a100554102e805a031a000701440d0213000d60040e222248081c00701407518030126824000c2135400901c1c0f000e441c903a081d0f00400c2c1903210303000c0c29000300b00010f805030300c030500303030040000320900c0750312690540d801201140101c43d4154000f40526804031001a00c0b80d54400c504180702e4000742da68521680c0c07000401110320003041d24170081d00c0c0900708502c3e42c1c40e1518240003034021001c4002c0d60050b010f018031018004c418803060102100a041e1500301038036542e0740c500b4003042d41e002e44045412400701441d00700340151604010143d030b5418a0b699451501d0241142c8a907002c219559100600000d101c980703180c200001c4800d280045a54542d5280c02 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 157349244 1250 157347994 157348021
    0x2090411030a0615030603081c1104080a110a0f030f110d05030c2a040216020303070f050c0a0308070605061f030f1119051e1c0b180604150e 62
    0x2800035080303504c13003400040603c28800d54060300d9000d03c030145400c002100d00c4403c9003550030500c14050b150514010300c0b0b030002d0050401015282c0003010356440a21f4010511000c24295500410084400f0841e880c010700b0890304a90304080508580340650030300c4101c076000c2c00302680d00b003071a00b0110010448000f00810038240507105880d4114949400c104108407819035101103204140200144c514060740104042c0302c441c5584c00882989901003415600887d0040e43c03201d6941100c00d01b4000103208035074028a040ba0920a03017070950796010310900940720050b0000e0303a5580041c840c1d80f51443d06800382c0c8000519800640043c3d4070040c0074100c071154078212182060080d108144d54003068843c1030358110000d80010401034000c445980184050750000d0781a00c000c000078001400040801440d2504c842c001200c044e51494195113154020714003c240f100d25503900d41c0b50000a02d908007504a40102c0c1e039604480c3c009224201c580c1010800c8c00c240b0301804414240c040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 157350494 1250 157349244 157349249
    0x50403050c01030902010e0f13140105240426060124020c0a030b280b01080702031e0d09020415080d08010b0f03180d0809120f040902090411030a06 65
    0x8089541201e4504011010b940c02d00340004e020403100d010103001440e1a00f000d00310124003400c40150410300c21000340544030f240b144240008244801070100c2c0c01c0c00c00da1100d859409072103441401d400d03d09030345114403c0c0c0c03041409c10f05400100b00740d86209024a14101960700c003c4800b0303561a12070303407540784954a060070852a20300c01181c115500100d800500c2c1e00c030040442d1030340e500d162640c201360300000b00700311107551520407049110000600f400c80c9080401c01c00061b0407504000144c04003402400304030035988140101d81038805905171050b8004070030f80b400e07522400c0b81204000544101c00d03000313600c03074105800700d680300741d5a526003012101107038111040c08401100940e0001000c3c0034602c4000400c100c0750954100d00e00086404c401c603001e030f0307a01c02c120444245007007003507508100c000a00c0403000d110700508100845141003160300001840c001c0c0441c03414826104501c14206d446801040c0d102c1e090ba00d5074084001c10303242942c3c041d940c0c901455114010201c60 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 157351744 1250 157350494 157350503
    0xb0a050f0612061b04031e0b101202130e030714060c0304020102030a05090d080a0f090803030705092701150f0318060510080d0f14090a060810050a06050403 69
    0x24000340c03403440c000b15460540c0d80000080c24141c3c880700f01c580310858241c210a18401410800040000c804141507010b20a07016040032203c070042c0342140c21700001601c8408201c1592000340882c110410b444280c4a60450b0b600c140c031100d40d910310015001c1071030040403600001c1500c01c24420b02c0c6e030003500602003082c2980d21aa07146e0480e00e180d40400d86010f0300680c0184045840c0074003c200401d140c41e001007010803488140d40d280303900d5034820070760a000a046c4000003840c50303401044420240c50100051811450110300003403003801100c801c0d6114502c1400100248960f00061904c0241801c44c490b10035a11070090700a901050f10307a0343e00040c403e481040400384a0302c20000c0c0c0324880c0b0800400180c841d01c0d0b240251402131708868541200c40d500251500c0108500855014152502500c0030340e82400503104000440806a2541e005c008a941a42da485400c409480b401c1c02c10039025120010801401501504001c2d04580d080c00040b40b029041809082101d104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 157352994 1250 157351744 157351771
    0x12050a080a09090e0a080403020d0c08010903031d06070e010f050d050114011701060c06050403050c01090303150f0b0a140f0a0201020409061d0a021b011a0913031202070f0b0a05 78
    0x2c0c850f55620301035010007800d480011f004c144018039100000c1041240607449139180d068807880c1c12421140300744012070109503200411180300444034000085401c0da200035151500c0c0074200034282584000303900c1d0401c5808807500e2181070144081c2d0b503401c40100010800c41d030711111560580141e400ca032601060000004a8108079013103111030580d440c50f0b540001501d45555110042e08000c0c1086051180a102c5920300110902c901821b4900075130340403801c0e0700d0726008c2000c100e0903a00546651401094103002a0328408103c0b29812310364a001d28003e10291002400c3d4044c400e9001075003900086d03680c03e400e41c15006442510202007042014a070345442242e9108401381009058400c2c880c00544003070002e5015000310880140d943c100281e2501c42c20382180c0300d64100da4000501d0000c0400c0334103080e4035146c0d12500070161410204010745000e0b11940d500c1400d08900741d0000b806d18108500304000120466104505100f00d04180241e600508811140100c2c034840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 157354244 1250 157352994 157353011
    0x30303060b0a021906021611090105030c060f090f06070623011202120106170102070c0506030903030f04030c060504030f11071203080a0902060304080403110603070912050a080a0909 80
    0x7107000440e030700466550014155100208203000c04c40504200c02e030b40d400e0703003408840c1d4041c4464003070120862140d281200e059141c401040200740040c3c203c2400b0343d210320031142150310340c2c008890079001e15407007060300d82000340e00140882d480c072502a0380014010900c0c404004858114171805055000506030400600364040c0e1080310034800d1910a0030108451809030801c00c86202e602c80701440041402516640e48003400841c0a4402e201a0344c0003541d8010b110302c55008d200034050882d942441d50a203003030203130341e6400042d20031400c5600c6500841d00b0035002d54281814983d000000b0b2100385070504000c2d1011019001110114902420320050048045000c4003500e45120800d03a4010301510100c441040041410070702e42d0b550a983d60160f6180e40282d48200e1103441250358407808e528240c0400311104403041d006034001e106200300141c00860308400e440040011110b0407000303041c2940383c541036140140c281000020404002175009074450162103900d0020f001160 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 157355494 1250 157354244 157354259
    0x20a060f050709120c17030a08060a050f06031e041121060a0f020c19150203011202010f0c0c0f0503120c0607080403140d02091e010212090d06140103030306 69
    0xc41c110703061000a030210000b4403c00d800500e400a0440c05804000c0c280d58540f0804c12180c1d80c50500c400c225407001c600058080c1d8840030b5030ba1702581c10381e501a40d25140c2004625000d5500410502c00e21000c0005a41c0040c170041ca4980c1c110310b10080c2a0500f030508212100c8030070b08000500400101310364442d03a0f00043c4d40c0905980c02d4400415003903030742105002c010320079440303412038140c2c01b0060520090300410203020800d0b40d40480032409016440c201019001c2d440721650114018401007043c100b0070003042507a1074080c24a2829945c240b0011280100682c6009054002d4007001003440f1000c011548280c0c0d1090b02214641c480c0c00130402002c5c06409100101035000340002000284291481a000713032083c2001040101c2001c0410f0903900030070a031400b40346d40422010080c0c075002c505805081910910001846c07405d0f00000e40b5802040d00303500c9640c81c000b608040c5619501c1c003002c4110b8015400708215925141015032219080c40b0940010340bc1c04808148074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 157356744 1250 157355494 157355501
    0x90606030b03060f0702070824070206040c1202010e040213080f0a0507090b0102030415050d1803020a03080415020a0201020306090f061c02010306031e020a0605040f06140c0706020a060f 82
    0x6440041c01848150b40b02c100020504900170b203c0340450103628000142d200d010860144060340301001c00d480c040c41d15008004140300244147c045610120510010680f89121003082c1c402c64030700d01c1029180d600043c0d85104540d8540c80d0000d200103141c003480c1c0f000b044503000360356851003503910b0381c188105029960a0384c140007412907082203004005055060b40904c20046041c01500d0415965003c1031201d000c0d40b08200340440c1c1c0000344c0000b022111712034482241c0c990b0040440148490320000e645041c4200010148442c0b030000c50140030303086100e160382210524042d076550000741d8000340030b50401d8070100e000300c0520001c60140342c0500050743c814503028021805036512000c050182c01e02c0c80c2c00503410325581d8040400800d20090f841d80c0d081a5064a8490516061040c00f0b9100c4050740301d542007100a2205011046802401c40100c0d8803d03c0c2496814020380e031564014400d80545400c0c40c452080000f401a402107010004680a0344040040b1000e43e428076064 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 157357994 1250 157356744 157356761
    0x3050c0a0806060609090a0603050f0a060e0303040305030703020c0a0501020408070609170d2001090b070e01030c0503010b30071206140907020f0a0803180712170d02040b0409060603 80
    0x84c1c10f010080c0641048401594807401c0020080707401c170b13500d0316814101011003440044da038200400d060140900d60241c80040b40040c0010b40c5545000c1c1c60050150201074400c40805400159a02a94004209202e01190007200855889682d030203290768416042c4038041c00700c1c6a4000c00101210307c000302e003401c0304c0001c010703103e124190b02040340c020b038421001041c034040c1300c400b64108034000d10480340340c540708030301804490038003000c0600295003980000e81014108418008080d0b84502643d046960300d14444d611440142d0b020702502d01c240030703581111b107007000d55210514200e001050046903d81c4030150030601c01100c04041d10100c2c020b14510343d0440486120605001140c0355014441c0e1058842d030300d11000016040119050080c1c0e0094408010300084090024402d034030710b20150010708003103141182c00c1c0340307100d0308400140003201001d45440b03003a4800000ca42248000080447d9200e0300d901c1206810340083c0580d00f801464044007140c094024403404c2903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 157359244 1250 157357994 157357999
    0x200105010f1703040e22080d180507092d0203060f1509060a0302070b07020a020118121401060b042d080615041514040c0804080423060403050c0a080606 67
    0x381505216a1500c45640074100840b02078000341c09048403017801403c6e1004511a4110561350250340c5650303410b4840400c40050700c180544003290000308001072040c00c4075001000458405030401c503402001b040e00403460030303035415201c00c02101c5840f40d00442c03040c0c00c21900c618000151303000348181c038000c032501c600c1020002c012070321a600d0000043d000182c418a4003503d0840700d03540c1d0030032484013610b010780980e11400c4680c4c02c66811402c3d0303104840c851105010202e25054540905c040100300c0640307443c000c4651600504000e4201c5000741c010122080c0c1d481c1e640302c400450040b1451005d1f801510b01408030386001003c1085542124003d20050040b612070070390752111203a408000c103034400d80d1480444072005451110b00d005041400c020040485641c090200703545541d180340d800c0018201c1000700080f070f000305403401d60300b240c40c1a01c000c030080c1c4003007002d804e10044810f031720407408913001042040009864a00200c2a565600a140c0c1d5107241f0b0740c2c484054410704c0e0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 157360494 1250 157359244 157359247
    0x200301090c020303270705060705030901030f27080909010e071b03050406050904090b0703020403030306080a210201020c06040809011e0905060c010f06090504050f03040303170403200105010f1703 86
    0x303942110000315808030307688042500c0c0b5451f581c100048083e4480e1104640c580c1010a80c4c403031941c0c2500c41c81815a1280d0030034441201c454001c00c0304c803081c503000b20b0200807080304a041803090030815a80111000b0340144440c0d40c4032040c401480008955907800540b0a6001080c0d05040a80d0100036592640340d02d07013003d06090303040d2281c0e0446045030f900a5540c000c07030030104043d45019070040d201c5490050b6114210700300142680d0643c0c001c080c05a10a41c03299001840305900b203c003103246a407030710181c4060700c8070881c068420f0321461090f40c031441c402d1000740300d1010005d100300c1800f602c94101c6040280e500035650226082160003003103103c6010801420301c00010819146104000034024151b0300150b801c45510307030082c6189650f500c0401040100030000c11a002c80f62000550515185a50050100381032140c0f007600d00840300007007002c15000783c0790980415508518002c40e4290902d81a0080509224195004420000004401c8604044403c21b28800005103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 157361744 1250 157360494 157360531
    0xf0c0806250c02030a062a050705030f0304080c0105010905010501030b0102061501050d0e250e04051902210d08010906061b111009090b04140a0b04200301090c020303 73
    0x40e2866018108240e13058003030a40d03410001980762203200c8071014810380340903050b000c840d405151904418841810f201040005d08003048002054951032b4200303100c1c2941e65034071460951100d000e15000d2042e06c2d800c04001007142d5407150486416030b0000c1c1d07401c00c0314103074043c01243d80e40d1068904030503804c1e0349480b80321507501c114003c0c1241280c00d1400b0515110903400c0c603142190344102490882e02c90f8188017003400c070303050030b240062244001c01c50903070400d5107038035440e5030140703090010070080d0043c101c9c2192a0b5412030899014036086004581402c5102c260304c0b6601042e0820016001100103d1101c0303031842240199102580d038188040c040174014842c03180a03c1043d500c03c1401c002d00c050954402d180c1c0c1c401d0074810765581a0151600215600380e4405602c00ea02c900d02306a00045007020500c00b50340d00c40014203020031781c42540c8010a005000391004a0268086c0a4148a50980b80d0b00118100d0744200c604104846030b0540803600d9004c1600e40e6101c0c502080f450 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 157362994 1250 157361744 157361747
    0x80c011a040209090403030b0121050f0c0408030d050405070f0306090308100b040603020708040e0115080106090605090f0a09060b090315010303021c0201060807060c0b061e060a020a0f0c080625 85
    0x22110a000604081cad03646500c40c500485070302d1170020301c00307013258541c01000f64001c10b041040b500500c00340c00030303402d09080c6021941c41c1c1c0102c040b02d501142d5288001401d200040000c1c1006050305c00c21803502c1d64403402c03c94040c00b00d40000340d000c00c6548010960100b07580400038100c40c080391000d801c041c1800000c901039400944d054455403410700c40800c20310129040240244460780041080f0790031004050400c0405034000802d2100700c0d0740c10440c2039000300842d00246402c5481401d02c01c5178400041d05940140c0100302554a0324030081401d5809000401c22228220201d80c000c00c440003814074207001c03d000003001a00030800c0d47c00c8030980f40c603a0308120a40313400086041601e0720912441c2c00143e51003180080c003200f442e039081c41060600c40b0b8000c0801e0302e0b0004140042d821070b2840440e1803410074010340c00064041c040d54401e10403031402e035a201002d80d40e200c0850030706140c1c015250050604d103005d0a0013044141c0150003411900c0107000b5070180f598a00c0703c0d030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 157364244 1250 157362994 157363001
    0x810061b06020c0d031d0109021012020c0601080c041109030703030e12030715052409070e031e010612030909020f12040b16110601090b0607080c011a04020909040303 73
    0x302224101d07001d0000328518002400030742d9110525a80004a0a05400258554200100480c48140d251a4640016803114aa041d10f840ca007400c150382d010f26002c0a0b007009125102e00305405c0c1c02038600120f904c560200e505184900e080300c6c28801207000c8000084c440c42111580c5174958817140080000030f01590300f41900e0940280303181c0d98220b000366100e080d0350240c00119126505c00002e40343e10422842a5604522800020b80711091019110000f420038440040d21400c0c096001030080c030302c54201b540415001805a03207410441158070f50440b0b06201e4004c80c3e41d401c082c00425003402c094966110130750196110a01c0e6441e10791204000d47c8074445c05d007945c0108008401c0a032081d42001401279208405030242071600050000c0300364042c009100800022182d81200280000350b6981542c82074617001591603052000226584524540148030110201c0d0001209806521080c10010000e0303001d40d0088500d0100012481286601680f0030381400108011078030071707031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 157365494 1250 157364244 157364297
    0xf0714120a06080f010b04060b0405010f111c050c0d050c03071e0605070809010f050c0d020309010617100c02071d070e0402041206140c03011205070308040f06081006 73
    0x407000403815190400345007450000542c2d00440d03034488900700c650b03017131500c641801070188035200350809046c100000c0180e00c42c0c85008007040164114040c6040060000961f40b0002082400c000708108101a24642001e036042c0002d0117042c04141009006200b1903c0031030403400a949031025940d60301d01c0081c0c81c0340b0030403646d102c80342007a000584c0d0b62003100e000301e540c1c2e110144685094420582512898100c041665007440b050085022800d8191920728629100143e226030359000100d004000b140d208031141942e985403c40740000210b0b031000e460b404d062003404801411041607039150310700e01c81c48040c201c281c00310454000c102d131540ca0f080903562800c44a001600400201a80c200303401200e9140401c03943c0f10200b0205106403405008500000c10f1140344ca03440041c1c10340014881c0348c241803189410601005030500440c0c000d15407000c080c980b515114440d11040082c40e0145101066010f404a649244643c1d451400c039030840e52804a800e10400c500c80700f850004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 157366744 1250 157365494 157365511
    0xb06070512030a0e03030a020c0c04141302060721020d0801030f06050405030910021b0301200705120f130618031523040b060a0b07020103090809030609060f071412 72
    0x1044295000351301032004502505c160b0501603110b8041024080c100401100c2c5181b04515042c0e0540a00070000b001550100d100100d00305210020300103d600d500c13590000070000c101c00c0d600d0082c40440321180b10125200c03075084500311402c0034400c0c3c8511000707020151802d16454102000228140c0107180e01620500a0300e04040d49803021480c500c1119925074003580210403010300c0031904400540d45440c00310300901c00e4200d030745054010540b05601c02402c0e0340c5d0004060040c03080c2007200d000b070b448200000607500d01414494079200e403c00c1c00c0864a04940b07090000300203200c3d40c00c00c400954103017207112516203140c5d01d41c2e04825089201c0c505040d1a0720181c5050030408884030103410642d01080b80d1442c0c14640010242c0d0000e144034454019403006008a408620948808a0303081c01c001034845045d050801c203600645808940c548214410800740313542c0807901c03034040c10741c082c0020000d0700c032030380213948102045641005c5010244000c2504100301040c5c1d50704030190 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 157367994 1250 157366744 157366751
    0x9020103270b070f0509130905030d0501090b06040b030601030e0705120f060603210d0920010e0303090d0f08040302040c09140d0f03030b01140d0c030b06070512030a 73
    0x1c01806a441411a4503001c0c98164918201024003901e003505603803000c402d01d00092040c1020a014005000ea602d815004040342a107204030388083e98010485181c00c50101c98481c6a40b406520151000340114100c203410546080080c0c10018207441c01d4402041d00e5a040d0356a07080110014500000e05039082d206111000440b9107520074056105500d04020f089c2040141d010a40340180c0540118025404000c80d0710100e003070031842d02c0a1110183c011a0303a04040003186000e0088003c01408007039000204c8100c41c11114015181000c1c00c1c0c8a103034801c0309003001c0680341d018060300140c000e03802c0911400055480c0d82d82601c0140700c2d0341500d0415440381c01140132102c030908101d0206c0d41072407090083c061281c41d080040c000c100c9840008480943c0c80c03020400c0d00f0340c00141419100c0e111405140c5c00307552076007803030300c800034960352074102c0619a5000b91144d41c88010120707180034446415810010100c44402c0c1d04280108496401001c0307401c0360f0b9000034804401d0030365 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 157369244 1250 157367994 157368011
    0x10050f0a15020c0901050d03021e01290301050a090305091201110d02030702060f0106120b131b030606031b0503040812010f030b090a050d110c0a0902030709080613020409020103 78
    0xe500d803061615241640200000c3c4014001d01403543c40c107130002c030700c105030000000c000641e0001c1d100e03504ac40c1d507180c165662424141910301500c0020030414a0910015500c64204620b08182401c0d080490090005403200c0422008442007818081c000031800c0140c0d080301d003400603c210f84a044540000f07011012000310002d5078101018a8110035000010300514540c1003001d260410f080b00c0c42482c940d494801d010300008220000841400d0b03c815590309550740e10000e104014180b20414001c0d582c0c1d0070b05c9030400c0c000b0051540c004c64902140415198802e105042c03030b4404100070104191038200d01a2443d80006208461000d4100100c00b0302e00c1100794214001d0103540c21100740d26081d0314115400200081c100c030290b0307000c4886070b8007250000030b015143c010030381000645001003c1c0e00794104483c84a8041d007000c0c66000024841c2c40c294011445104e00e40c0c1d840980da034550482e65107594098980310702c007100c0311550170050f00d01580a1441e403031050500056903203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 157370494 1250 157369244 157369259
    0x203040e010e0a0c170604090204140405070305010f150e090304030f110301050711030a2a0c090c02010e060c090d020916031a030a140109061803020c010810050f0a 72
    0x100340c108601180c000414040419201e018080030900c0d85c3c18003030744140711402e600b02168401896203100b5511006c0e2541075443e60b40c800a08005c41c403041c001c16140a08248c1c0e0303a11640c0c44101c4080d868511607101044191240310382c4e0051082d40b0403001e41c504480303c404c81d8005048040280410400000010080014001500c1c0700309031078503103843c4140405007180d200070880800e0204101c16410550700200844103008401e0401c0305a0000c05101c060030b141d03002484078005499106000c0c00e010b03424031114112640800103000d8812400d80c1207003a241c1c64500000d19520034408a0002d2040502804401e0000b8100e201541c03d55000111404c40036034070340b001c0300c2c01a0042c0c45c009505000d41008041000038010302c5800c2c0170080b0303545920300c070800b515407003502c00c0e804240f00c02900045407080e0003040070b128080040c548a500d05601072030440c0076200e00c0ca0b240c01d580d4000d07403425216840152142c1c002514220500940c0c014440c0d10a50100b001840499481c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 157371744 1250 157370494 157370519
    0x120606020a0f152301080304050901090e010905010c050705120901080f09030c01020a08060f18130221070807080607083103030b012003070305070305190e0414100603020a020304 78
    0x100540090f400301c0c0d841804140c1390b07070380040e00982ea40e50010082231100781c0301c0b484103604540508800080d00004520003e0040040c890010100d50a1111006c0c2a640c044050550207016200b13075a0b0700152003050403241d00c2407d19240c0801d0306440040c200701040707843c007a88024502d0540f03160400c03c151607801caa1041d03203124007044038901401518200706440a009500c265510010300341183d180e071483d40401803003050380304e0600004c0c07000c54440340d5800300009030480007401100c1c0c401c5070f499154481030040030b01c1c80c4550030b0f00082c11580094aa070054036142c6031a18191103410041c02c108100d20022055004a104201040a02c00480c01031690003581c0015174034020000040c42e5034507032080440300f030010780580c008002012007110012945414103a80d6002c00749415180740c014400781c8101664201070300503c49410015040100d02c1c1110100800e0b1031b0342440d146d2214060350408100f03041044188500c2d070080d4000c0003010b00c80e00441c3d09042c3d40f1100324800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 157372994 1250 157371744 157371761
    0x9080a0302031308010504021503090304090207141c09060c021f0f1101060501050301140a0f0303020c0312030906060d08040924080a3c080307120606020a0f15 70
    0x1607100003600580f444050031000060040c00001b442075042540004041d50212040c9003582c00c00000858180c940030800c480081803084030a5442c6e512a0520781100812448409024080c642061840070101258280790449686400202504040b0102c0c1c4181d100c11080780c1148284003a0116451540360070300f01480c0a94036903251480c54903000b04003000d10307044410700c2da0600000b441640e0308801501c0c1540c81d0840c04110340d020090000c0c0d41c0300c2080d07104540012001c400401810f90108018100990940c1200c580001000ca071710381a00c002c0710420080c3e0481400f062081c944019a50345480c0030b502c64a09242c1c94420303440448042803c1d000c05072001c2210444401c0400700d0f03407002080310134080c0000c0c0042d91a40080b4404288000b030801016429007004d4080e0030b07446480740c1082202c4441041280d140c030191560058550b9004034083d202409900b550502540341990165405000101c0310340e03071442c0c0c0031686080200d074045040511103140010501c1541103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 157374100 1106 157372994 157372997
    0x6050a11010b0409051b060301030c0302010f18090b0f04052e031a040b061e041d0109050a03140c0a14010f09060218061207080709080a03 61
    0x1031141581040d0f01038074041c121000c1c0040060a44c0b49100c280c40720301d05444170b110400406010900c0000d1501d03124074000c0c401544190b03c0481c0b084402c0c03d0840c0318024250808a1fa50010307080080020360f1942140581c3c0f82a8056082041083e5030401541c2046071a5905000d80498003c4003a801195507508250440444034000c513000b403c03602078110041c200040e810400d41d019036503040408042059840c110080c108401c0001000c0106854504141720242400d100c3c0800494213645003c01c8411003801101c2545200300094542c01c40a440c000d0300c0e10809901600c2c00030000d12401001ca00002480488103411102c0800d130850040c580502402e402281070280c0b608000b4400100032103034020302a40d800c0110f03104041030b100f009114050207401c14200c0048074850100712284d00a02001c1c3d0072100c503107401c3d05990b032501c000074900307400200e0840 = true := by decide +kernel

theorem cover : BRFrame.Cov 157194244 157374100 := by
  have h0 := BRFrame.cov_init 157194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 157194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 157194244 ≤ n) (h2 : n < 157374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
