-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0864
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:14:44.63997+00:00
-- url     : https://prove2.me/submissions/3ec62c69-6725-44e8-a3c0-8357f05e6f4b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 155215827 ≤ n < 155395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 155217077 1250 155215827 155215829
    0x50705060a050415060605340302010b0f0d0305041a0d0c1e0305060a03020f030106030203030301120c0e040b1311090106022a0307031b030c17060901090506060d080d02040618 77
    0x11340c207180002c180204c03500841614038240103090902c40b120620681d0030203a00354178056414002060811000301030b019004010135600c280c5200c00007500070410402e0240c040280540401c0e01008240316000c094540c40c90059003290416280004046800702215410b00301d6100046424085003038248500740d1845000b00c961400384041c0c202200015030700711262000a10a604122000c1c5445d09c080d003100b0003c54008050b60b440c1e607540c913283c15420b0702c225404c4a0307894810780042120000091654002c41e00400e180c0d4a0b50b440c034203080c41c001500d02c0199490414940d21401940d240d02d48c0324040d140940c041d01c2100300d00c400059542e503045656000c1101c403540d0381600340c1c0380080d04404403908500303a1048070b121114800c2c0f10a10b02d401c06429488043c0b0046040c1c0100c00140014203500c02c1211159611300d02e40324222402c854004000b40c1100011940d18544603c902c500d03a40200041d41c9861071604032030041703078015440080490454080e5501c0301000101e004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 155218327 1250 155217077 155217113
    0x20c03042301090812071407080607140a0f031a0406090b1221130b040b0702090903070f11011119110d03050301060810090903090801060611031207050705060a0504 72
    0x400f03c20306000e4141d40394000c004040a54003004034122040c410305d5803105091144480a507000d00d6181d0444548681d402c0301c0c5407020500521141c040030411b0340480b03c151700c0715034809009558030001200600200c4500703548010202d404240c035a56103210705001044c05110001c0d074900b80005000034403402545103482500700108045144081d07580c50018050142803e6039101044080c0d4403420380d03141c0101890120208000c02d0030b402100040002600840d682906565000e110f560780c1d00c1079050003003081008000241c00200d040d032503490046c805043c601c03050000401400d141507400210074241203150341c07031541407140b00781e103c525940703040d1801d815812907030b100904184418440c500410000100181514200b11241e034050880c410007400070040e6802d00800345451030080c0070035546002c000040c1c1c070b8012241c0f015210304880246007021140c1c008072000110082079442401030800c02a0006030302440306501c00c841d0300c00001401d0078141014580284804416 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 155219577 1250 155218327 155218337
    0xf1b0d0f111303110a030b010303090305100209011e050f0a080f061503070c030207030c0902030708011e0506090301060306110a030c03022104230f0105100e0f0406020c03042301 78
    0xc140708610024000039a5000070b040313503481030711a005c50907480003039201600141c040c400110805a124921100702ca0040089500d0702403104401c0c41240326030907109000c540110012146092100c04000c0c102074182030043c20103d2410505000360320a681c1080007480303000801c03000f441e80110305500712400b9209800440030389011001076110140c04c40060010020010301094030030052031000d0355100940c2002c05030b85440800c0650029030325080420300002c004101c1c0c03c4611804500c43c0350000c1840c071103910b0407060240c95403000a40f642c01d0b54840301c0c04000700d8a940180812510b407012021b9440040c9800141120000c0034003008160040003103840858200d03821703c041e001207019a200036140c6180403100d101520b00000d2000ca50b01c0803850201e44007042c40221142040001e1290380ea0b8420408100c480c1805030001802001c001300d11145000300006902601c0f6440051922501d103100c1403440d00a130b405004c0020400001c0d0138104414455041081c2003801c203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 155220827 1250 155219577 155219587
    0x901091203080c0c030c19021305060a09020c10050108030403050f01060b0301090b0103020c010908090f090c031b071509120c05060103020907020309060c070617040b0f1b0d0f11 78
    0x1c0202048000b070b20410070608045038043c080c0354140304954000d981e0710111500d40c03a4040c5401c03180e0003159410381c4105140494500040014040ca620848005099040071030415450344025006a5900d01740d40c400c2e4031060061200b10b104260107001c00360001e603150392075031818a10346050328414140320f9040400030444e88038500305403415603000240c0481e805821200403002805491101019503081030404418028000c00804103110252559405190140103001030140252040d042d262010030008041b41c0101c00800400300004003810704e41400e507120756404948516a50101315030743c0175060308101d0040c241900781401420804a44000c640b199505c07540140b00103400780390a0700010340242e1007401125500300c0c005001d251600249038000341d885a00c0e009810210b521101a102c40d01c40079210310748141e80c4011200c0e2aa0385000e03a40302000c0001d05003d04058003140440c42c6418803002074120105507042c0060386805094541c0141c070701c1c5030300e0079102003401c000b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 155222077 1250 155220827 155220833
    0x2d110c130507200f0f070807030809010e1003090b10050d06020307110d0306060206060d11150f070f060c030b1e1305071806051602010813020d0c061e0f0809010608070b09010912 78
    0x24230302d0708980d04010070f03030b4540c041e02005860362205081000d91051035208284180c07500b5500c49100c80c0c1c02580790840e07503610380c0c054101500c280c1c001c1641c800020050000040e00c0c2c0e800456200025181c80103010b200c0d00e0016191a070301e5841d9001182d10ba84003407050a504004003035210b6003c841c006040142ca4a0f21040f1851007030030300380200c1c000111021341c102841c0072510441090680c080c1d6904040c1480c120707640c8416001c0b42c80c20708147c4040c41840c42400f400c41c1c0990010002081100d2807201030340c1c0180318410280e000000c500d143c102582240c800d0600c1280c0715144d298103400c00628070f48800e0425008071050080078000000f0103031a0703000b034011055080c2443e2001d500d030300e10b04403d0003c040c10000e42c400c203a150311104102c100380f0824112a05522503881101c01070000c500400400001000014214070810041500c50030400e6003010071400002465522180005d0401340c0e55017050035255000502c03a60785580c040c044000900c0c05001e25190307040a07503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 155223327 1250 155222077 155222083
    0x907050d0803151003091502030408040b160206070605150a0609060518031b0112060803030c0a031d2103010f05010f2d110c130507200f0f0708 63
    0x2403005010010048005039411214400d00d0400341d40003043d1820407007040b00020054094440304a5142c07150041d2141600300c0c2e4005d99000c6e0f40c1c0b06c0c02d1541841d00304000d40e51181c1184a81101d100000c020703010158903410700a1909601400012070203141c8110001c400c2c9a0f400f10f0140180c000850401010b90310041031000d40e0080d2811581c0c0302081c82074024810016501151315004201c15407001121490088501c14004c2e22840d0440c020b004201040310310a10400c079150308104001035070032110380000c107a4000681030000f5008a014055241b0656020030031107543d20100c84c580e000903145403004001001110b600b031442d070501022480c2e025041c071510381802000790820459501903403060f1000402d8444007c5000d0030000c090280d120341003900c2c030100360741c4030569640103004a104105660084d0801d41040c107030744d4102c0c00500004161a0400580704200300460114912603040030304c440c8024174a100d0741500c040c1c20006aa801010107611008007001b03a00c0d804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 155224577 1250 155223327 155223349
    0x60306130506030703080d09060c050f070b040f06090c03061b02070509040503190509090604140403080a020c01060806180706020d0804020103150602030c0d1b0807080d051e090705 79
    0x5030801141c66103410010910300740403504028070b120300108100d615024658810f101700c600500c801e0001d420f2440e07050783c2c5032003110004491001c041000b600801e00e4920704503009403040d103124240c2901600c40038101c85441001b2102003034003900410600019005e4140e00c840c2110b004100800b124a001c1d50700c0034684611070150006100007014070805100341d86402c8008086441d0300920f04100400c0c0d90300000c48070f84140406400301e079450404d03100d0550000303c400c2159802d0b896544040d1610b0400500f42c400850b020842003995074070138000c2000521900c8005c0c1f42c41d042215480401c1c0e2220700d501196580100010401749500080d00c21030704829050040458942d400100c000c0c040d05010700000b01040c40307000070010303400002840c10b84408025036810102424084405c0c001307200c10040c41c614403030302075070104030076030000c001c228880c1c40c07041c2c030b032500c140442815994210f9082180e030307900b00101040000c617051225031010020003d003075400c0c103001c000b584a0b515 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 155225827 1250 155224577 155224609
    0xf08010e060109090e15040c0317030105090106120e030d09030206061f12020c0303040b010e07021b0f0a0807090902190f0b0c0c030f03030907060e0f010507080d0204030309050f060306 81
    0x317a00c040d04d071509042c44144a0000c0f044000802c514003420203001c02e00f81807108032900031207440c810030030001c084142c905070f0b18010241d0186034070b04101100c42e880314042c1200040d1380c82d0080c11030480108000c1c84c18040302800803070421502c0c180030342020310082100d4040d65030004602025046416981c150340c403142081406040c2809000009000d40f416075402c900c000402d0000748011942c0890407240310885031240c5548080040f40c4030615000498002003c80381611903c0c03800950701c0013120b0000e806040031a5032101070170314103603c03a4090450b9503681d02c00d010a5041102d0140140884403801040245c40c1c10100305802144c0c1c814808041c07030109a0110f1000240030302840c0c1d40c401000c50300e015901103071081c0c480e031050311742107000d02c40c212000030101e00914034544c0754000244003890400d03581c40159101c0c0d01499084529043c200002c6e81e540c005440900050740c01381e80c070080342500300300500214509640e2224030031300090040084950341d43c0642494011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 155227077 1250 155225827 155225831
    0x50303040306150b0f0d05011409220b010b031b0a082205060403090602010c0309051221090a12050f1804020405060d0212010f050901031202100203070f08010e06010909 74
    0xc04208510800c24240c0c0120f101c000000550b541900d117182d0103070600e881d0150042083ea45e940092042150800304600d41080d02d07100028090708000401c0e408445520300f1003c20440c032a0364007264803800760405c49140e4004014406ea404005100b07030711240291240c1d52608924500c041c0020344000c003d02e0321000807070b004000c0b014100c2484880542e015080392514285441c001e00350300d1640c010140158031b00b4580d80e0100303100b80209020990884007401600c40e084d2419089544030090924440780c0b4040050001a50032039500d2140f01c0c10800307008440b0443c50a0035000c809807001408206e02480420034120400e400c0301d4030f03070001681004800004c100850060700950744030320751248011480f50614046900140140349840c000001e2507a202d4550b9010865980101c5400211035030040c0b0000c0c140070303611400703082503004880700c04104c456040d0590b0b00880d400e0001410650f07032100f10b140c10800c02800b510780c6540c6074101c0d1a26000080074003038548100c160720341d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 155228327 1250 155227077 155227091
    0x1a0301080a120e0a0303080604050c16060203090c0a23030a0b0f07090e090703031205010b03040228060c060c2d0512040b040209010e091b180406051906050303040306 73
    0x94040d40160840d00343c007900d112925581d905000e490b52004441c1c090046003458000340090908500f11203944100400e6041020f0154403418025000207000070058031801900511640c1c5014041000340001c1c41e00d0240b11031400340c4101204080710519001e513120b00c01c0180000c001c4601542d204c8181c826100300d40d43c0e00003003140c0100c01a03111043e050082018400050408141401500d029441700c4802d1549981104221a024840e01c4150401800401c005141c440700d900445020820b02e0303507080d0140c00d69202c044c455540040085164003181004004060042c0301c0c61041505000380840d240500c5003c0300341c401d84005020740e03846c18010350002e0295082d624032030281c1c9400d0b40b5a260500d0501032044055800342e209507060000011400c1031403001c60321071217500c0e000e440155107c0d08400850301d0944505544880010300380000101400000da2140d0301030900400c007410111b0004618040030040b055181342002c4060244d5240042118120399220341d00041c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 155229577 1250 155228327 155228363
    0x31090302030904060801060603060b0720130e0c04050a14190e030d06060e0a0f0603020d18030e01090603090804031403090603010306060e06010801051e030316030201061a0301080a 79
    0x184500c56500d43d00c00e1a00002091203241540480145c5481340c0701049940d4a44034441014007954500410745010b10341c0c0039911245507080200c00d0800901400101d002c03c190450995010304003415040c1c0c40051145401c3c42c0c5801110341103010030000300200c000c001410640703071400600700552000b064a0701454008560300150745071480c4016681c580030401d83c400c02521240c421b1800140c5403038601e450a2800c040841d00721142d50341021102850b215065019401403205c142c0710f00d55400c2045c0f000d41650b00c00c0c100081c42640c400c482c41c0722250000d030843d5069004141010f2818602030300242810080341c0a03250003501ca84401000c0c540c00901e1482130003074075600034001000010811910760088400e44801d100c2d050030b541d840c2c000460300d00710b00f480303000d078030100540c52603482e62030119500741d080001600ba2441c050310581c40c1c4200308145042140183c4d0746038810003203290317610102000168905100c6e440c41d450007104980c0c601302110003074000a9481c1c0c45000e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 155230827 1250 155229577 155229583
    0x807060903050904020c0619110d150909110405010906050303070305070c090c0c0b0106020d0504050f0a05151809011401050d271101020705062706040308070231090302 74
    0x50003100a20656550840929564903000c040e034228500e4140c8005408c800e68043c0500410264201c1205040c200e0f80111140030b000b186a45000000500e42c01013485501c2d8000c1008441c003510340c1071807405c0b403117050004460b4141d205030040d40c075040c028404e0f513602200700d680840d0589003042e20361341c480c00c24000c5030105a000300c071907a1030201d50013611900900d20a11260180c1011042d603070b80c0d00400ea031a900c3c16590480003e900308014480340ca0005041705400e2800360803000c01a03210b6010814010304101a02030100c80402c4580344041058010b41d030318541520080c1300c40d454000b4503c8944464004c0605102000c03075100c2c001c2c3e0003507200c10396502810780c01d0001714450b02d04464060901c00340580b020100d4006200055000003000000c45002a10040c1303001420901580000003803021090107040d0300204240a07612038001e40055402564a03a07911001407040005001c42c4001542e40304104c0c0d4000180074a030003000c4d000c410070750100854040341504d4103c0c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 155232077 1250 155230827 155230837
    0xc0c0509090c011701030c03030f02031207050d0f060509040605091006031101080105011106040222050c28090e0604112a0c0a0311010309080c03190c080706090305 72
    0x1820029410400a08003000600c0042c0c801d400e89a0141501d07901a000070044c10902010300740d940808010000a0321070080142e4160b00c610507241480a00c0e0f07005682202c0554050002800c042001c18132070080344035201c00c0408000e82006400c3c07409010442c924802000904003584d9100013a030350540611880f1400000c0c11401c00016840c1d2400052405c090054180020030f054000318095000e8914500c0c04400341e402441140d0b6168204440f0040b5450510801d621441084801d01c8941c0581030050f0a110801034075503458000d8a0344015000510700b0000d6881800741032140e0700004007101ba00d10780d44501909644010104014141e01c40407041c003844005105010602e01280414051f242091922850100c499200741d5070420034203031a0340580342e5181000044d84220010007201411306020420310703004e0b00c0d51b9095812400c00142e0540002405206141604025202094481c28122148005900d17110024042d1440080a05030b0b241580b00070b06010f84141c81d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 155233327 1250 155232077 155232079
    0x9010302160605040b0f0c16050f0106170f010c050a030c051225020325230a151506050c0703021306030215191b0f082206020d0c0c05 59
    0x181040040c0d10b84500280000c44050341c03c90a54008111040031440d4070600803501660700504061240e403034070204004019003200c162040c626081e0308001d00b030183c03000074029039105170001500d024206080c208070418001c0180d162007910300a00b60000c0c150b070740f0b042882c540040c03405000c09090381c440c8101c7c050a03a175410701108004400c140e1502e500000f06040345205160a5851001d07a40c0e809a18820b011450002e004c0d083c40c000b03900b40c0041d50354042c0e00328120481c20058950304814641011a6154005640d00410710030208120105110b04140800c00c425031080000004045401485c0030018009584548100c0400489001d103800510007080c46040c665108000d12880c8000c0303006046005154412100700c6055032150504502c0e0380050300d02d803030030407240c0d05140c1c4924441400380780340140101c2e030841c4c96200818440e05c00c055950b015400544c2181d419800311200d01c0741e6006003445a03a0340880c805641940a080060300d1188a141403004000150842 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 155234577 1250 155233327 155233357
    0x9040b10030602030c041806030203060c0d0207060c0c20030c10030e0d030209100e0904020d050f10050a051f09050606040305030706020d061a090d031214040c0b0a120209010302 78
    0x2c0700d409680f10300100111100c480490003070481d07c1c51103200703680300352101a505800500000764003010101c01003820b448054070062910b0a144d54910442c1d05046040000820740b03441c2c141084503200000081c3c00c8400b80e031545007215400013036075a00e020071140c2d000d00701c1d000f440f6031214000c0d0000d9014403803d40960b640410540801802500f258121520545058400c81c6160b409600c0d039102d1440003800242d025a111f03024400484030301a03089071240700303001c646142680b09021071107151070240c4c404a51401c100941c8015524040e0003501401881b02700c014800708070342e43c404c0440ba11801c01003103a956041c0010303200c4c055513002903c03a0100183c002c040003503a60050150044040d4100711807901d40c400b52003a4911080c141d11846000c0024441034034040c0d100301081d43c880e01d00210000100356224003039030001c440f4200c1c2c01002c00e060104200d51000d42d640a03010300b0900074101803900000826591002221100d0385600007620f40c0d840c0d103c1d4045514210340c0c1480 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 155235827 1250 155234577 155234581
    0xc03020d0f120f09090c050910020c130902041b1e0e030a0501020d050a05060a0603020309030d0f0f05070203030712090206040503120d0b030309090403031509051303020f0c09040b1003060203 84
    0x203000d0714039010203c00050300010020a040d0560f208062581150b50340341414180da0106202d074440b1030400380ba0941c400c4801e00c1580b503a500c007064841c00e8240e00045100c104901c180310a43c0d00880c4c50507445645408d1040d40c05070302250030040030226103a515600040e412080c0c1c1c04428051015400d4024000240e050010540050440d902501001c112640e10300000d01c00b115070680d00903a0054242c502005001d00c40d802651700204103105407072400100b00d450400319001010000a1581c40d2802d240f66000c50307100d1554040014005075140d0300c2d09030390080540500380b54032800e440d50740e44103c0641d22880191005000054100c030032a05d00714410350301d160050490034140b6414500343d84000d0601109039050008040c010500703a841c0e40d64194068070b881179032443d182d0459100000d81d02e006000b441c1c044c450750b038a0000c1d5140f50f81002800d18544903807109495104d0580c80680b901e91a181c99845604078010b0403490319802c0302400805a0f5500103024a030010003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 155237077 1250 155235827 155235863
    0x606121003051b120f031905040807030f140d080118021b011d030c0d030b030c0d0c0906270b011205091e060910110403021e0109120c03020d0f 63
    0xc801c8449000844c1d0340740c403070700080420955030440030b130380d180041d00b0501c8400140d146460384036042d0780c01800c0c0076040a03140c000c5603151002d2540143c9a09032002d0805080c0700a2050854001c80320f40003905008040036400790010b00180f0410040d664290781c2440b201e4690b070b05075628803800c0b9452810907a40080c950340078007134010000e4021071102c41447d00038040041101c20391070480c00a40400d000540050f0010003c4400c010f405010307554038543c80f0359503001a2180b4611880d03a1050090400780502d045881030740142c401d205485c02d4010045144400c0c4030340040b500000850f01114120040310081d51604117960114100b0701480500400840c1c4904404070030b40107508001451402d41f42e070380070160381c111019007041c41580510606038011461908182c40000d107416500e07030200d80d152201c0e2010390f0b83d02c4034401640301c075507922840c020000d020303e095007500d00c0c0c0b0540350746e11102c513070340710091040f03903290203010070807608900382c41603a90819140f00c05061460 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 155238327 1250 155237077 155237113
    0x9180408030a050603070602060a0c0306122a06020c09040c03080726070209240a0305060910020f0a0c0c090606031409010c0207031b0314070f0905060612100305 71
    0x3540c2c11440a050400007807560900060100403200294000c00041d107640c0e40e804c004011142c0c0b02d030209a11024045101080e0b0001c22010702c0c0304040303c0e080e1188043c0c2c1d85000810780c01250100c513144081c1042800d6001034007800c2c81c1c10884002c00b81d40c60b03905c0c0ca46c4501902d58401030802c080801c4e15014002628170005002120f4800204083c0d1000800c240381d100300d01000350303c0050480030030a80410904038414080050050740826400f040009041031000d5100325050b502510800082c13a02c103004c1080103441401055003406041079210406005052040d03080166a900303035420300c001d0b11050802401c3c1910100b0000e51903000003030240035044a000c540e0413103d00801d0a607041403040c0c80610400d83c0c00b40600700c0c00e65880001c5210b29105464130302003d010b020010840c074444d000f407194080002022020300c0d08407512030740724131544001200c41c5060100031181d00c41100701c03040d0b01807440001d001d0340d541ca828082450a41e40014156229601400580007002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 155239577 1250 155238327 155238331
    0xb0612250f020d0f0503010b03100e100314070b0703050f130306141014130209090106021e0703030e010305060402070f0501020a18140d0c030501110409050c0a0e01050918040803 78
    0x2d909450b1290802c10095480e00d500503800c00000300c2c2007004012350b4040c03c028640040c0442c1c8050101582c80c0b11840f40c4e540300352640c1082c1070302010200308001c0d02c403070446c0b0328156400181c240c0709d20300005052140181100501840000a901c42d00c100c0b01b18100c41c1d144503841480b0b440240c41e810840c006000080745100d08407a0440407c40750270740c1c40c17a804c0840b13222110b11038100550f60103206080045040e06016250240851009581c80b19815806441c1a90007030604480c90060041c01561b1080f03035080d40e410480041c40466070041c7d685100080a09010a40b0f40341c40020a00a110b403074400307840c20303080500c007104208041d00100800300f074664076451840c60030380d180041041ca078468280d88485400c1c103101d06080c41d0036410303a114043c1c0c2558035515600d85070385082d038800c40c0018661700400207091140c2c583c14030803130b901700d00ba1540e61400c100d100440505010b070f004110505002000c1a0b00300c4035074a03110b202d04198843c0001c004039040500d0a050503406c2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 155240827 1250 155239577 155239607
    0x203070c0506312102070302040920060309030a1805040e011e060501020309040f0e03031312030606020d0c0501060812030a0b0108040206030f19020324040b061225 72
    0x202d01010460b09003500350742a1030507000507003002200910038a8441304201302c2e0300c060a50142010010260b43c8900c600f007070603401100c1d0030a020320700c0e054034a452882d8200b06031090382c051080c0a00d495002003034500281040c2410360250359054003444090080da07101c560f115003071000340a038684040d0407003411000c1e504009134504003082e5a00c0185d503003a02803980140e2080c0702880b41c42c80e142c4c2003103200680c1e00c5800078a52180e02c3c64542180e00440b0810b0b00d02c0b6055148904100c0c003901c0580589109d460200040381c00c002c40252115080010301040040006840c0c00323029087d88103030010301030402142c0c0c40140c1244d10b014160012120603004a290000d000202c6d402510103d00c40e0740c1c0103144500d942d940014103500540054201c0481d2507240c251211410003a100031801400c200251205818954020042410021000310702460400c2c804000036100c11302516980c0d0f40b4002c81ca900342c2c1e07549440360850303e0740c40fa40040811001e5503402806030411441caa00640c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 155242077 1250 155240827 155240881
    0x307051e090102011506020a03080a0207060c0f02060703020405060406030203091612020a05030106060503010b0d18060209090a0c02060112020d0606170709060501020a03120b03060a021801090305060a0203070c0506 94
    0x100341c0a17460b0b0403482a2084c20056000b44c20414002885080c449611140f104001030601c5615101c00c000c4032486e0b107882d0301242100e00d407010b120741c040107205e13448215840d083d858075007044040356040c010307446a5000d05402002103051181c05012044030701a01c4104100202d6503024110076066001d2400d03030080f09603403c00301e224201801110195031990715658956464480308013900d074000c42d03078112040d40e01d94000f034114000d0031902c4240c0340078282c0580c40d00311100400029520140202035040d10788890070ba00c00d6000318100f41101e01044244500d4820f47c00030a08a48400100411544c80c00030003165221414010546099208040315007907920340d04400100c034034901416001da8010b074040c3c000a8030580301250341c180850008122400d543d03010034540401600c000030b206070007285162021001c0f40c0c0e6131842c42002d01c1c24a030782c149540c944039101c601c040c00e0f2025941d00000011006401601d110040303c0c1c0c0b1038101c1d0f80d00d01d0000012500ca4a001c8070501e6200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 155243327 1250 155242077 155242091
    0xd05071802031003030f0c0b010906170109020a0302060f0913020d110c120d02041d0a0c0e0d080d0e0604030806010e090c0d050a060b0c0a060f060b0403080307051e09010201 76
    0x5116482500d11a01440c3d074008526400d41d2400e03a000402d2031705280c00c10040e8902c40c4005013a0b40300c0c090080031f6509005c81c04034104078403204aa0007070300d00d0b803016030324040c110b00c0540e84094205007200d40688209941d5084201911200e101e01428690808a84145c400284420364002c1410510500c810413421841e1020a82144105800748802d984a48030f4103540c5034144005000d4008a118018034260740c6188040022441d5582c084c1041c08400070000f81915078080c8034280046450000e142c0c120143c001070588409050140548a000c0307501410340d00554800f54452602d45c00b10342c503a00d06403900401c026412500b10780010005030211b1494148032034814015010170302c1d43c2c0c0c103061008034010020a070081400291a4884400159034420000100f440c802003001130001030a00b81047da0603a5210744102500901d041410000c0d05000030594007030b681c0c00440c07a0f903241c54410b000c66040c00307256000c109041c8442440b100800108009114482c4203800901c141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 155244577 1250 155243327 155243369
    0xa09061e05090c0706110910020a120305010630050c070c0e0712020c070f0b07061a0f060c01060801050a0203040b18031c060b0f040806010801050903071e020d0507 72
    0x2002c825110100444818440344000a0290b0001100481c0106505080040840c002904044c0a611300000340e04160007a02c2800300b031000b4070001d211682000d02030365140180082c6400c0811040010740e041d00040c42d840216000c5030b81e01c09a4a5543c24801400d040051400581c003000040310380c8141000c0001d920700070042c01620600040d03c2d980b01020607480e40e24043d600c9995280c0240c00b483c9400706010001109900c080c14001040c40c0d20f0f01c8079071800c00c0c201c2c3d01245117003d4003182c503c1985000d0fa075240702290b0030282514256161810380312214098903036a00310304840d50800d0b04118940e0031076406548220b00482c80d424198440402e406100d42548040581581082210784183c15140300219580414841c00190542d070301d006403001600541450300d80c7d03210028041100c8c0d070041041d6405415903070003c01480c1014904a40d0707034866074100800407000c098051002281c01c62420003900e4019004c031000c401c140ca070071a140d5089010b040c9225100501d41000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 155245827 1250 155244577 155244589
    0x15050a180602060c071e0b1b120112080d050702030711040c091406041805041406011503050727030c1d13020a1701020a02010c050306090f060a09061e05 67
    0x4031800c607000f0b04516160210b5610b40b80c1d000d003a0980c1d4001540204040e00d9012400d110000d600a1044680a0401c035450800701c0c4402c4000b003c0008040c403842e004a903850340386604642c444180c0312821180c901e8020900c2c043d001d041007040c1d02e400d080120a075000720080003400e1091000d880d800c039011080000b03c2d0b03d0701c14a0400a204200c00384002d40c4608902020390a005100f80d041035034541d40303841055036070041c6030b95041c2c41d8001d0100300031507071010f50715844029000d4241581031041c648820b0f03070003031074030402c03d80c5440209809500884040002d102e021414182c89001c9001000105100d48811644041c595000048008400409240c00c071070003403507510140c481a40e180020608410143c1e8011b40049000440f9010a00c008101000141c00980c0f00c1c004144084e0071a61405070320000c0c03007030810400070a03548000312207602505034182e003902c5d44c46583c042144210b031604482969072402d80301081d503000c9501c85586079140300c15840705280c3c59005000c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 155247077 1250 155245827 155245829
    0xc1a040305030a080a0b04240b03070212091f080402130e0a03120b060a1205060108061008180f1e0c010e0d030e0a090509010b0d0b0106030e0715050a18 67
    0x30941051240300b103203d110b4000300d9049078400c4008141c034a81c0c400010b040360500748032500c0882c1da235801c010102444034640780081003500541c030f00f149482e80c4040d448506c01c13203c10b104c02000043c0c1501c5640c4090b41051405c100d00c402140143c0e181d60045c2600d02c0c03c1d54280c1c444d0f6080c080100c0c3e22103541c025500c80300c0d040e101a0030f501c0400d6070306907031031501506111542c5071259607041054031060003074200714246665401807400712100e903600b103800c003901981c1003000400803c4100e848001003507181040d107241c020100c4d0303520b005882081b00510400d0400f40203070260b0303810300c0342e0005d5151400c46100400d000c0318403403207440558414000c00014085200e64203003c4480c0740c111000c240c25806401c140c0c0405000c1c400042042e407258001ca00415600d03001d001c40d0200c00d11484190b030342c05403558154403840d51a2440098014481c1d1005c050f15800400c200440500201004155260000c0580c42a012000e0602d0300b10610146c00200c052090681c80d0440400041c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 155248327 1250 155247077 155247083
    0x5010b0c01240512010e010212071112040e2203050912010b030c0103051008120d0606020118021005040e0c04030b0c070305030c0a0302041502010609050601030605061b01090503070c1a0403 83
    0x41e0007440c040c01c0c8013200000d4049441555a40c204404c9103220030300003803c40ea800c4010441c1c1c80d141c240c2003c0c111100c4012080da176070744400b10304041c2c02100ca0032602039420050843d0b41541e0341d00c0c030140108002c4a010124002e01468540401d0740000107030000481c2110708460174a00840c0d10390032200350f02110381d4107a103c80c0101b426940290300060f001189070f007228440303170f44a503100c2c4d1604d5559590703028000800900c41e072562041e480303058042c0860303100031310401d1520140d68000c5200c105010b80f0402c0c47e8812002c005028500b1900101083c007400c0c030786860545648210340d0060b200c1680c0c2c08519400007247c900f000012a91802c0d41512842d00f543c44142c48005642c114548900a260782000089092640041510b00795001c075400460001d00b0101140e081e144003500d5541410f04103031007806150381e03041c240c0b08000320f00010442400c8014800d203002d0400c2d01301c0a802808002a840244480100803070162001c1034076000c0c40c052401c2e0f5110032807046200c0a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 155249577 1250 155248327 155248391
    0x40b160c020d02120a0305030105030601060503070c1b1a041503090305070f050106050d050a12050910080613140f06030a0206030105010e0102070b04090e0c121f0e0105010b0c01 78
    0x244005181560ba400d001d1400a0100c03000160818071903882d2072039184046d0007003407011004015030310b400c1043d1805003006140260440c1889400544107011020b00240098030300c80c0c0b80390544604c8940c54001380100c11000c041d0200b2500c1e5000c3d03550013802040404035072650b45140701c3e80203004402c1d0703c80c0d1541d02c480c07800c261620307946584088807030300f15400d5494010014155070f481c010310341a180104003400d02810a40785c40044010003101c2403060000030f101c072034415969001c20340e140f16540c1c101043d00d603480f100012140e801c010542c040306460211082140110b220009100e0700424406040a407111020140d48248012000398000400c0006101a5104d400c2002c5643c1040c0100c403000c0381c48480313450464021ba04004845036594120349101a42041450102d480990b1801e00101d0205000c40d1540700740255038681c021041d084082d640c03d5070340200c096254040007040596111070303480b80d030756004034440c0d1201c0d800c082028044902d9550f00321000808441c40d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 155250827 1250 155249577 155249597
    0x12060b040f0611010f020a0f120e030d020c01110c1501090510120206120f100e090303150d06061d011e050f15030f040308090a12030b0d0812040b16 65
    0x21103030a0082c0182081a5403544100c5c90800d01c1e0340054160034095813103100f149a802c0000424040318400003104d810f04064a8201402c070100403160030400030f540160391140e003040e0850151501c0844c041182c14000b038071000c0001e002c41d150020a0703c800d1107220590380e68030541c003a10408d545800305649048010480100e017011aa4002031010348101d0800c504c4501002d44c410044542c500d89005000401c03070441c0003003500d42c01415a080711000a0300b80851100d030360b400300500059100f2010340c1c903804141e840d022082036580d0700210500106456811803040b503046101c103c100c01e071607800040b03180ca0350403900e2080007020152550b200c0b4074240811508040030b010140c1c12803141ca070505d542200c000011442200b041d9950a07460900c0d14004000c0c1c20024054415504903a00c0140024507840e500e041024440c640401e0142c001000218800c014900040c0b112000181200c448512a002584128000c06420540d80e80729108412205903c245c000001510898 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 155252077 1250 155250827 155250839
    0xf091e1a090303160c050d030b1c0503160204090c0902130501030b010507060f0605040e03041508071b030207120b060405010602010b0f09150d05071701180f020d06060612060b040f 79
    0x403e50403400c98070703221140c00d845841b107500300300c000c41c41c081c0000e442d0300e80d0491030704001d0601c595448400310711842444081d01c81c00c0c0c80e4016001d04080c0103c1d14018001999501d03000040d9403a00308442c01c42d640d542d44400c50096212001b81c3c20840025100000c0541c06032113900c800c81c8062315080c2c42c2c4402591940010b00103d1403508905a481d640440c06460703d00c144901d0684070f02c000c41d039980c14601d209800380d8042d404039040010305020010155801180b001ca45d03940d6100100443c00685030584c101201d81d000740041500c00f004030824031040c4d030380c1c043c0603041c20303501040349980b107220803426a0341200c00070381c1102084d180741030603061900120b580880c1074a001c12403103165000007074281c0301c08801610076070300c00c64051005403028240305c210b505c9400c1c0204400080606d1225110f2000140580b030551f510081000b076403116224880d24507480101004120745920740a0040050340820130501071800c41c02040f010740c050211030079606000070380380035a0f03e000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 155253327 1250 155252077 155252101
    0x50108061e07120c030b0112110403120921060b030a0314090102030403060f0b0316030b0106081f061e02010e0606040e0f060114011d0f040f091e1a090303 68
    0x107480d50341001042c0702041ca40064600c2601d04c6001d481d50301082e1810700c000010003600d000840030906918005c2e04007401c0380c1c03201c1110112030b482030b0700540030814803c09503140000b59004014548068403208114504c044002c052603202d1031040204920403010f055035800650b0000b03010508610001b8020810b10024000c428070520450f80341075107940da03000648202604c090b01046d15821812810701d802d000740032141c1c0320140d20403029450340e100d1261408040c4155401c0c488103001003440c20b44076054411040d441400d0b0b070180c2c0ba940d501c00030411030300310b0603001080c1c80340903a41c0d98180c0306000300042c1c40141d0000380b0030380c1c58040c01c21004094040c0002482d00c00e4822007410907400b486424000c1850707a14035007444400c90005484003040c6800c10f40d10414440c0a60155a01c0d82242080d03140300360b44c002001306801154600a004010024104440b0b120102822103042e100788020320b0710400c4403250701600c0e0780030345990704010b4810030910b030018000542d4903c400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 155254577 1250 155253327 155253331
    0x608070c06151a03090d08100504090305040b0c07060206070e0906090c16030504090501090209011b020604050315090d080603060714040306050a051015050a050c0708010507050d050108061e 83
    0xa902c524242e0340d5400840400344402d1250044442c0110030803c0303080042c041800b800d4054180542285070a441201c0d1800c89130140d0792050b584c544112040c0761203081594042c10918154581d244801c1803056640c02e040e20034038006102e2140000c3c1400e116400c68910880c1c050002d0354a9141c0b502004001003000f0107540706504103020400720601ea110350407081c01e0190302c07401d50711414030680784181c4e1016081401118010000c000440e43c0c0040c1c13203401d411030a02102e64140319031001604034032403548216814403c00380c000010078210f1011ba8062404501100c0d00f9014042003034980010456005070301d07410400c0051122401403c0b5641401a09840c00d8509512540e0300b030200e4206032034281150340d84504001c0002d01c0606400090711808680000c804046c00c2d0003002845031360012420403802244e00c40188904004140182c0500d43c02801141381a03100202550025135144511074104000010030368004030f4290f024807401600b2079508101068414101000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 155255827 1250 155254577 155254601
    0x20c211b1f02031911030109050f04081207020c06041508100f05060a030902090103060b03160b0f09010306090905011e0902060301060503090c040e0618070b09011b0804030c030c0608070c06 83
    0x41030b556070101d0013842c414032104c000301c21501512035041404103400c50b4001401c400d0700c1840102804003080c03a080075034041d2600e01440840b20754607640201d0500e071703004041c680c000320f02045c0403410700c1d040390641e140e030324403642d40100e41d517074990040c94007103000c0c41041c4c00260404410300040c1001801801d80c462a03080100e41e400d6140d02240985109907c1516529500c80c82d0460528043c00340c05407445031008110000c90904501015920445a95503020240000c801010f40d00a8100c94028483e0b0710307080254040c64105103001c0c281410007131050301d0f982c584494400419108821105402030308450850b801c01d00141c8907988050080c01e014815070b07450442c69075840c020a0100f50340d5901030301b001e04081c609030301484280c070702000890f0040305080c40f100041d10191030151000b40b80022440800060310001850080d0015021034030008010080c0710101c1002d8003241e00c00c0002c201810fa4406c801c0301d83c40300554401000961089044004c00d01316000700c21848a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 155257077 1250 155255827 155255851
    0x170c0f010503041e050703020406050607020a060f0c0203150612160b0703050c011802030c06070b04020f0604030b1501140309030703030504051915050106030b060a03020c211b1f0203 80
    0x10149143d854070f0203603100121561b0340300750020300440c2001c0c05a013000380403c0d1002d6003000455800071340002118000c400c2040001411441c0c01d0784101401c04500750007505030342e070380302d200c03a14802c1c2040c1c00c6804500540c0905a1080304540015403030402d03000070424085020709003194000c01e0750044101380e0411a040c4618000c5080038421583c201584883e8100f451a0324810f040c28081113101d9a1710840d428410400403840c007030b2006038410703411213032003003860f131400005510350085400c090428413070501002601044014800c400d550240c075071105007126201c1d48941d521048070010006d40045c07140e403002034000e81020383c00074030035819500800c0848003039000c400c403100004d131001c0600042c0560034950b00d100c0e1901428040c80c040c4840c52101001c00c00c144181d0b001c5400701540044c10a000140601c07000c44084041c060f201c0e1661414580d844013500101641901e40301d54000311010b100002a01c0f41c1c203500f40c400500302035091541c4440c000d40000b0a1600000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 155258327 1250 155257077 155257103
    0xc0303020f0d0e0303041703061507050a1a09070b0304031b030309051b011106090304060f090504050106050d050a0608121b06011205060708060906100e030d030501170c0f01050304 79
    0x1920070b005409580b003c201c003c684034900342c2010803041076216104134250f401081400701c6c54a0742c0b80000c6184001d80303841a950031007490554a04030b0f038000c01403c0d0b0140e08901c040d404d05c16500c0b132801182e140c1c1c00ca40b200340c3c94005540c00352206441c02000700b841c0101d0401418240320843c104640a410002644251501c945040041c42c0551801c0c101d24600c085031a9a0014045004040c0f203000400441c50020846540e80c4140e01a001c18800203031050000c035442054004e000c1c4c4009002480156965400900280c007c00c035008019400c0400041c0102e0151250324120340044009090034000346641c16060342c4904500079020641030001d404c0403004011290007007030340000b00d00320040136080031400c002c00030b8042d00070828030303a0512003659a180c02c1c040d04140c088940d4020710300070382c00981c1d04c2000c95902c0c035018018004040d10064040c0d00840c1202d110980301c2841c0039030398046c0d40c1c0355090701505540c0800768802c201d8265225a01035940a0301c00c0c0c08000d041c1e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 155259577 1250 155258327 155258347
    0x30f0215090322030c0b070c0801020a090302041406100503060607061406010215010f060e0f100804050f070b030f1f140307050618090703111803011a010c0303020f 72
    0x10304000c84010540750710020300e204400880c901030211004140c1c070f40403a11815039640c0c60324428184560070610700c0224405051045d405003c50081c00c0c100001c5590fa000807001420143c07880c801a0b100e246031001010b101402420041d01c030354402402010241c1060b103050f107058001500c8180c011070244400c40c00900c1520515080f20000044040c0e00d01e4214002403503e50702100f040700d0a0200d0b0010441400000652400d41c2c170181480800e01d0194008161000d01003803220303500108012594080a4200c0d0310240101e002d0380a5440c0025a01c80b05c55030746070b0910030b412290748200700192005082c40d8006400c0900c1c2041440459145c18070103c22000c180c00c5440b0340310044408007420302e010005000107040580742e41c0d003000040b48841d811154203800e0140070f07200203000101c1d424844d0340700fa8a01e0007906140c607154848034004071504015240c3c11400b039071a04845003000700e4041c6015183d050305035181000d07a090b999080303010390031a415074060fa25041c480c0100d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 155260827 1250 155259577 155259613
    0x10030e0c0d03030b1c120503040501020d020a0305060a05030f0c060702030c0a0f0f08060c0301060f1e032412140703020913030f03060f050d080d0203010803030f16020307030f02 78
    0x1c40d009a030080f5650115008104041000518800d0001848500f1500081840c460440e00c0c0c00d071424902c5c1c6a55450900340d0280c03103400041c4841501c00904000c5440d01035010b540100c40c183d420f004030b141c890080c10740e1042c881c1c200071115400710101200301e103406002011918406410784444601400101d03005145a40280900074030f0f690701440001c1e8040007810050250304000c04050038400f015810380c3c8010f000d400b081003000005d0700610b60040c008400e2001c000c00c46c4041041281000400900903c0201c00c45059980034203041c4059420403042074501804840da240ca0b420303a20151402c8180c0400c042d540030b030700000800b60755054580e134454034240300a4100e0340600c0c0340092541600c42d03407900616241410601c000c403a030740d0190f02990310648200e200883e560810003082c0c00f41c45440c0c004c543c000000443d070aa40400594003a1f0940840c5a2458407003540718146114003a45003001a8030500c00000464403a07030000d019120390b4016107411442800030120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 155262077 1250 155260827 155260849
    0xb040b0f160308060907030501030b1303030207240608120d090f15051e070807120e0609101817070c05121615021002030702010e0a0515060d0210030e0c 67
    0x2020424803c10411103003005202c02d60300008502d400c000d00d60455650001d18100034290020450604160104040c0a94103c07000c2503007008440342807010300c0460103480214030107210401810031500040d6a20000b512095000221343c2c568201888407004200a0483d00c1043d134001e120b154003400413030303c01c20864101c0c502805002c00c103868034114210a601c80b40043c0b541c640d032024104001d4543c0828503d401c040246030140e4a9160b45220714060880e1034000003040c0205414010111000030328410011002c80c01440b1a1460b40f10b030404004850300c001e00051680084e85e818031701004000c1909a2140b840308400c80d4580d40402d0101c60301e40b10f000c200c1e50201240c0e0403080f80740710195004180802d00107450501008000f51034051140022900980100101e02e03000d000790011910070b1209821905440744900380503503500f400d8812003882d04c288401182890400e011000d4040ea009440740381700300350400e4200c00400c003100210049008091511000369540c4110740 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 155263327 1250 155262077 155262083
    0x1204030c0509130305070213020417061f050603010603020f0f03040803040c0b0f07030e03070305030f1306020d0c021c0618110402031e10090203010e010602010f060b040b0f16 77
    0xd50224108402d001510703001801c5040e4290345001c5401c002503000d41151515641aa0132203500000c3c4c15082020b4000c80d0000c5240c41341c0c2e25425044088002500e5128444c9690400c500d807400a0f02c45550350380b14003a460300f0842c00c00c0180007850007a00181750070b000751400b03203141074a403d60703254281e041a282240d03021400400c0c0011301ca00c00c40248050007002400c14549112118200490321400400400340400041d659502c0e540501c0392400554021050b02c1d91011914160882540b0000c002500d99060f880c006c02c0da13910000300008c14510030345401c0c0354449a5020010711445d43d04440356a4400350340c4200024846008101030302401d208075488034142e0b0b180200d2104000981c0d94041e6105004004408481ca41400f07400a00d051044502d034561071025103261040c0d42060a000340000b00009a00d115204014121181e5900800114880c0c01022003682c06521404d81500828002402076000100040003400720006405103445101820f42e88002300000083d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 155264577 1250 155263327 155263343
    0x5060124021605130207122d09091a04150f050303031b030903070b100501030b0616080a090f081b0916030911040509011a010c0b130203120403 63
    0x45648031411002036100400360018011181d07911420b07003041d640a2040d0381c412032009080002c1c80d41c0603030480d40303465000103100f402c00601c80006401009030328540f00903400b60250704240c045821007040b6204441d680c54800451402088030080d0081c00300c001000804107080d030480380d54038495600280c5180183c4103096180c4510381c00520019400030b17001c0e030020001c01980c103c0300410680d01c82e059030b524503166203408804074a140251075004005c04d091405101222200861a0381100d800343da05010b0f00352611705010607406a40b105014000001c030701040010f8000d0302604600300b5500d051507003d940c030428540101c005502100458201b103c1d102d05c1031040911070303016113005036892400c60074010341d00110100c0c900490b1040650340c00014040010f0214a00340c45400100140050308007644081d0081450040112444060200c80e4103254001c11260745141d030000d088201d203039110385182020314010042264140a201420345407464241e02500165010f40c2071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 155265827 1250 155264577 155264609
    0x150a020c0d11010608280503070c0e01080123060f120307260c0a1101090509090f0f060903070314070f2406030b0601050a12050a1406040501260a050601 67
    0x40c85003112019000564180c1014200200801e02440d03000341080e11010211450310306c0f03041c924154050380b8001020600741d400005142503140c07650038144d5801a0007009144a02208900402404110100c00281c0c00c0000748451030984070303480262038084c06802c81115402139041c1580c1c00b0030000c490003240c51502482d1100000000c001700444201402e141499440b80199691512000103040500a0041c51180d91281c96404001c00b000780c069101420211201603da036145021500c940c8941301c0000711101d0000b94031070003400c1c7c00c0003445c9442c8843c1c50440c0c04100b04a017034048050100920000a00c0f240c0e00a0800c500540140351840701d042884060fa0030000e0012910382e08100b4180080f6100443c031030b0300b10409007070480d95140d05d4542943c2c40c0c44821000c212040c50f04041103001440c5400601d555401c05061941940e1070400b04030840b0428040c0744c0841c21581407900e4998604c0c1d20b00c1522500140c1103490f90155980e65a2500000f40c016042c18024426 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 155267077 1250 155265827 155265857
    0x110a120204150f0914090703020609220501030c0305010b0a0311040c0306120609050d0908030307050315040c120b061303020f06070602030915090a031d0d05010f15080d02150a020c0d 80
    0x781030340c1c202d07002c10040c07c4484e01c1c5800040d600d00411802921179200c10314900c8031400b0b00d00405503141030032907080c4101e44c2e690906c0c03880c66589110a489035400c2424a6034145083c2c0c0e05c81041d69442860300706a40308400900c0000d004a494200c1411b580d840040380504000b07104103000c602c9100b012511100c503280260030005030003581824000381c004240503907103000c02903951001441c036040b6120303554035101e001880c400301580341e086031818030040c0d5050340c05001c0100c00d4203800c03030501800e40c013002808210304c03a098002c0c00e181481c2c07806000514210a501d5900c0b28018401381c1807468903118042240d109130745030700c290307840480349010f5000084009507020100c031018010154031038401501800c1c000c00880d282c1340b1385004154480e0356540d0b0100ca6941c2001c020442c22820031071010003400140c0c10b0b60200b02c181c0380e000401d444002541100b5000580c040c1070200030003078200c0300d55840949580b0800b5028805004400d804001503503813000565520760380000d80f21 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 155268327 1250 155267077 155267111
    0x30f02040b0423100f030b040902060c010f110a02030906031e0f010501020d0e030a020405100f09020301140d0f060209011b1a160e01120f0216110a120204150f09 71
    0x61071090103850134803191212107402030003928101d040d03424003140c007405010005004140700c41000354000700114210415402c158070020030b01c00150020003480c8202c05842415000d91600240143c0c400c001d40201820514080e58001511040c040305450034080c41c501d507168201c43c4003051203001d10042041d581d042040180310206400c20f1a0303a903a1000100f0f0301c54200d203101078081d940721030200d030360b00007025440700003080e003100c201c44015100c1e2740c1d0101075070080c4202ca046c5e00a0791035020346d600d0281c1c040c465140e803085260600085c2961100003a42140e200c0c41d06101c0c251662800038483d01c80d07600311181c8140111144182c00d01c245c072100d07800c0a000b40910702080e152801000d900300301c1c548100442400d2010b44214000503c1000d8440d0350b54400c509270003c61081480300000a286114501c00d05014841500d82401d00203c1581440390205100ca0408020f002d82090342c090061001d511400004082e210a2945c81340c01d0341e40e100d070020a5868000d034440a000d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 155269577 1250 155268327 155268389
    0x1b180b0c03250305030c07110603090717160e0a02070503040e04020102211b24160f02030307030c0c0605010602031c020405090a050603070e1302010f03140403030f02040b04 76
    0xd4108907025192001441400006c0c03580d800e201c40010316000340801c10b042058101c1c40244516035030b15025600c00d4032900c05100c1d2000900040d4644240c0910200b003036818500003802424038070340380c08040350003245c000d08010100ca90811440d804201d060001708041c02010b10038000303d0074039100080c90050041c0840ca140c2d4202c10000c01ca0700d010404445000502c42031720546050300010860900481e8510011070900a41900c036010740c1c5803c1d003502c02c101c0d0000e043ca0307030081b076082616200740345485200142c0040000400080c00390f0b212a91504403858200a5801d0340d03600c280841d4801e030480b0015900200e00d840306080e24107454540190442c1055041134586404101c3e5402c0c0503080c01c280b1919040003c6441d2010001d4100414422060400c2820840b0128030712840551041c0d0000b030040d21041441402401000800c0c142006600132039034a80c0c504400034002e4a1100580315000c102c00609072800c940a07001074045800035210b80b151502c80d080340e440700703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 155270827 1250 155269577 155269627
    0x23040e07081003121206030b06031c020307291f0b0703320a050304050c0f1f03021b1f0e121303020a030b090607031b180b0c03 56
    0x1403078100420700d1141d84000007100d601c24250b5204518104056824542011452018510300320b0700105000440d00b0712401000c0540a40e80c040d200040340c4244040e1000600d4003580c801c02020000445c0061016204411440700e1207044403800f4500081180c103958440804040c00c0000031400c03100c082c00401440300d00b403c1464410650380107840148400f041c41280c0d0743c2c050a600c080541e04100c03010280d41d1210341c40e80e400609402a01c2d640059400b581ca610a182502e81941400d8a0f0340324821001071901e043e0691090704d080b0203020f0208a2000c15400380408054007a80e55440000028410040c01482005a09203c03422024941300c3c0407450500b80c18400d10000800c507041c1c0d600142002d40d90b1101500d030380c618000d000e03610094000c00d01c1c3e2000810705c9074000030940208a0740b41a100075445900701102582c900019082c2140700980390031008a00a1109000081d8070b0000c030340900ea5101003001c45034003c8a10401c2035000002d800403e420801d10070542103003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 155272077 1250 155270827 155270837
    0x1302030406060806010f0b032a0403151415031e07290906070c03080a050406030e0a03051603090905010e0402030607020303100510170103240902060306010f23040e07 73
    0x8508058940901854411f000d070040d400800704a482c00501074024103c41a0982000035071414201b8010b40c1d4070920046d2008407000a16880c01d0311540966940c90790103101d001696103501e0701c4407a4440000f2200d41e40b6109858001241c1c0b540ea600700c401d00c007112400b600140d482c090400c0f4040c039200a251040a888405c8000545010415a8000340c002d6929a407904200d00d498080d0044a801c0030380a0100411a40c1105a0100080c026540103550900007026020045940c4000c094401400b20760244642a44e00c0444040c000515000e0310700b480b001170b500c84400003103030300c280c10041103040d4400810065042c20000681c04c10680e10041d0f02e9803501c04544d402c00304460242070710980600001145003440343e00c001c40c1c0242d04030103003107c5580d6840c00c94804141c901c040c6800d031034a03807203182039841c40c1d02c10480a540c018218070701d0340c1c0d540741c01180e403c0d103640456001c0c0000b10200c00d481640b0301c1c100e11401451280e100ba80c4500f0441c4800e18001e0007413000003006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 155273327 1250 155272077 155272079
    0x1090f05040818132408030705070e060a030204050405010507020d0224130b091e01020406080a05040227060108060d03052703010f02070c050306060108040b0403020c130203040606080601 82
    0x103120200300c030409410300040382660b6950fa0000703014909004085460b0702c1c10107560010f0b049195440388500c44601c24011401c0c1c2d40c0d0882962a0b00a100c1c0107032442e00140300c1000041c01424000703511860084c035400c0320607200c0c0e0005080700c0707050f41c090318207030740d01c004100e60350303404024801070030802d0300040c12500e43c007125440318000c03142400e42d01d8807506004103002d444401c43c8003070300c1d42c1c6c0000c009080d85415a41c8640d2088a00d10048003500240381c0b81c11110810f1089a040e10700079501c0000da50340d109001c00180001038400c03030708059001c0d0a209014140030080c111040c96603900707001d90401070300050249130007801040c810841c0004a00001c4c2d004003c13103a600c200a8850040380304281504406030701c2200c5101d4055003000c101a0014620b81c0c001e01d203c1d8400c00317154046a8a91080c59600c00d001c88595011620380c00c08100803524085803c1e43c054440d20495464100840c00b042c0d0301c0d030101c000c20108540100610080101c03030b000f88400ba002142c0101469 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 155274577 1250 155273327 155273333
    0x203010b040b10030b030c060a21060609051504080619050609130b040203010b0a260c0102280507030c05090a0b060a1d150c070b0304030e040b060d050c0301090f0504 73
    0x1983c0e00495050594030740f480101c03034a0503c200e07281d09200805007610345208250140400140c4040c407500c144a078512403490040501c1a40c00380d400565600b000d081c1031000307220840d401820440262201404006a908002c100f040e100c2d0b00c10070384201d1062803600d110400d4440103403295105003241d10820001108000c2c1500b4403c1c0c000a0950040e1103500100740100125018103401000588000c11481200f20b090002d890015407042d050144c0c80350500d40b900c54005080780160041d00c2542c410243d200110000d0f61508550303e1013240d050b42c0e6076840d06590303500072218014040e604222501e4000201d83d80084411011701c401048400040d12911a08105105000c13000c1081e810a402051403c203400901405420005e5140580d00400307030810040038600b4482c1000c0820b40d41003500940e8000c82d4140c0329030340c103101c0c0e2108020150400c0e409041e00b0a8003480307011114042402007038000d440e041030107035607541816984004c0d54014226000c0d1541030100780400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 155275827 1250 155274577 155274589
    0x113a0603080d05060402070203010c02010c2a02010c02031606020a1109070206010b0d0b030f1e0a080904020a031107060b040e120706020702010e0603090d020114070804060e010b030312040203010b040b 88
    0x661410b01000150507660000094000e0251006c084d426600c0c0c407800a000039015403050700c4600c04d03178441d101516000782d0440300008460302c8803030b1a80c50006a200055020b41c01350720b140c51000b02911402c0302410711b60f2188003205d51102d00140c2c0103640441c280a0464034542c04000190340b03400d034514100401039503808040c1328484010000181d03000707400c180c40d84007040a04d402415102001444941c0c00c0e980d1480414403088400c9141189001d404009114001664445003c5003400429020880250841f025030414980c4585101419001c03c00081842c41e10481c4009103c8242e581440100d9800d2015140140e000d50805408070741c4003004d90354481d50051025988858078401200d2502c00c10b00519040344c004020301a06e50070214940c070001486500070850503c1c1000070010403d41600c0310303c0441c01e44030100e00400c1c80c2c2e400c03007203400001d030002085845c0720700c020a1030750344043c0303c80070b6140c481d40a21086203401e01a041782103034201c030305000d102e03040400140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 155277077 1250 155275827 155275837
    0x18010e07110d0c05030d020f03010509010b0c070b03040201020a020d030f09090c0c06020906190914010f0e010521070507060b0402040518040303200405040509010c050d113a060308 79
    0xc2c8020f2400740303000c016080040fa8409041c2503410354484610704070902e01c9030828011184225100000816914119000e50b038910051800505003189403542c121481c3e407025000f42d046004043c0c81501503112800000000e03031180d0f03915046504544401040040d0310740200c0034050500004600b061f1380b140c10100c0d01e6070005001a40c8902c02d8000a80d01d11134480d0340b25041000e0000d1305a01c41d002030130790b81250a006d42d050440e1407520011a103034840c020034080402c018842c1c0b0311031548a41d0150070261403402554100365281001400030407412140c9000140e400115038040050743d000c0c2c003880350002e5509504081c10140060300302a40000e080710481181c0c00000c040c50702c69044208241200b41c180054654031803910100c0d41d00c1402a68015401c0c48007007076000e5014803415060312250381e1264105004225504080d0584011100d0008402d10003170340381c0b00c9104030598113082115024800031680910070a0315691041800420614000003040803d00c80e40c2268 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 155278327 1250 155277077 155277103
    0x32509050f01050c010e0f060402012604060f020c0a140c03010e0607080c040f06030c0f1b0b090a02060313020109050a0303050f0901090909030207052b0f1118010e0711 74
    0x545031144d000560b4010704d000120040544900403d403c1180c5001c00d02d503004d28001e0740d4014004101040113255183c1125504110703800030000500494440e51000d90301c080460005842c26442228007440c1c2140203034260b8105070141d12015a2050800010f950388605500911061114450300d42d10b9000040c04c2c1800d00280c50b00151100b40d21a048801501c4220240c0081d0380e2540306c002c004010085040001c100358031030250b01c05029a0111200701e9030024070340d010700c0d01c5541c1d1603150340c2c2c0a085000184641000c000050341c1d2070018510a9462440c22910341400e800010090402940a00d00440f01080d041c408a5440300031141460100f01c4160380c1e80c20200c2c01265a11855440b00075401e1030715500e201016404034074a02219402c0350908840c1c81c282c60070031160b00d03641c025400b8010143c0b04000c005000c01000d40e200e01d0189980e5210350180c94041190002901c08903031002d220340005000c2e05d042072080703d400003900d107420f0060320110220213035280350701c007424 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 155279577 1250 155278327 155278337
    0x315180f06060d02010302040512070305060a05091b040608030a0302030a0b0607080f181002010c02061f060c0c0314070905090a0804030212160902040501030b1e060a1202032509050f01 81
    0x30f80969002e034044030700410000c0c1c2030711a410032200c1ca0036141c5501d8002164070340a040081020001503001321401054420050240c0f0001e100811802c825144000f40d0855141c210008502c00181b02401c0210000e86016a5928009100008807508a04640e12070300c0d040c80404007040c004000d407604000d02003061683e80d9440000e156590070100c0040b0382c80321400c140840000e40c1900104c40f0a8203580803a00162500c0d0318504007108000c4920b100032004a104010303144c4100e807045080c0f400703200001003e50700c94444100704071409240140030f601c19041004003007124072826610260000240090228550340d000042c4958071010f4030413002585001c05503242405064180c0e2200100f14200903581c00c4080042d40052086902007072801c54048558100102484080d42e921140328601c0c1c240d1000b08912604920b541504003d03810440402c201d13454401140500a41581718000d00f00c3c07681c04840101e13203003441004002305250100401e03103480106121600013428070b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 155280827 1250 155279577 155279599
    0xc020c0603041401060308090907080402011b0c050a08010204080d02011514040f0509010f0605030a0503030f0c1b0109060c0509030d0f0513150908030414060a0e0315180f0606 77
    0x102d04228440c3d54204403030b5180090000400200d14003c1000500903030700c1d142141e0b0b9001040d550540700b1180640468500c031203180007070040008042605100e00841103081d503c8101040301201c0300c3d0400f08030760f940003078103200c103171400c02c18050310110510080c41038102d062005003045c3c0c407900c182250024a85074144065841f81c12649012031182010082d928107190f41a0213010f415a01482d018075241000c152414003141a1b605260040f0041d807840d02c400f0056465048002c1c1248103401c4148030065003641e4120341180041803100001c01c07a0401e80c140242180d11321095401840420040284581c8011441c282c1d1410513081c540c03015404040160740501c07410440c2c1a0f5842c000d8804a0850b0302d80e103840d9003040032503031404015070f00c45d08020ba90b48a00c0c045e030785204400130500b101c030749010402000d40030a5458402d46e00a0400c1c0407034507065046952805001c5070800b041030100700d803003020303502c40c00714401400c1410b0b074007001588956015001500502c90f17803034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 155282077 1250 155280827 155280833
    0x906071103011e0506010c020f0f0d08030103060f060906031a040804050d0503030103060e0316060e0c100809060c0a120f090813060201050c090901060e0301140c040501120c020c060304 81
    0x200c501045001030001c2c40345110024041008520384000d10303502d03510b083d01180d020b5118071600301d842a8041d02e005400d80f0f80c1c804004c0c2514080e00c051703500000c81968240080c4100d0040c5009512075940820000301d4407422205a03a001d41100f041149081c2c020004031b03140c0424440e104c036000c0f4803001c0d561140c2c1050760b1548560380041b9007202e040030f41c0070704102c0c000000714101c9009840400c07440c030714814019200c1c4540c076048803c02e0b00c03102480300824225440840101c124030300f22190250300b40c0101e1135814215190201003143e0000304280014103015842e40300304080589483c21100c414054940f040310344107200b0345617840480e0803c0d2551a440075103072580116142c1c0e1140003541c450124041e0601170540194240380103d80280c01a034161002004d008000142903820204115040c03003039141010f030302d0764864408044806410302554041c10551020550316810900090440d5200340c1980f03800500c1d0044880c02240c1c045903d01416008403000c1f662521141 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 155283327 1250 155282077 155282093
    0x50d060b0301080a06050108030f1b100f0c031a011d0312120403090f1a070501090609060b030f03040f140a080d090306061517060112060e04030305010e0c090607 71
    0xd04110300c224400000418140c01c0000d0202005100751014443c503a00c8000450f03d9019104005000220500129203102c015a101036180001c400880c0c0d0b101c414403003450252210504881c040d04d907552481103401c1d505d401501d80c0a6002e2000751142800740000804140c00c40a01807140e240c500760b54042590f042c09184001d9658404894613100f5069071038040e140b0554040703012030f0000c100000d0602c0c1042c0c0810884003083e845820441c3c8140c00f0700041d03441101c0c1141c20795600d4a8400009006104031410300380251000035100240109052814070360128049441d4024007040018040c40ca0700b10044d00d0300080c2a25a201c020344c042a0b0440103508101c0b2640a50120160016400381032402100e00414060080303035903600d44203101040b1003407080c0c00260302491011240303034610b14042c0c0042c018508100c03140d42064448048521a40042444000c03660034001450b80c0744c081d50f405085102c1e208801400d140060030218447c41503840e026807000704050041c08810 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 155284577 1250 155283327 155283329
    0x20d1e0318050d0206090d050a0804020a090518060105040b0303030105040b010e090703200405010203070f140d0e182203090905090a020102150c0d020f040f080d0e01031803050d06 79
    0x2030724501c0501020702c0c01a4a940c1c2401ea0100184500400a81c004000049440b9100b89980707905203000c0c6402022103125500400c140c0c0c001108a00026083c00d4034811544903c0c2c0054415030448010031080d414003406a0096204500700714201c08179680200c00c40e41196021240002c03860b0040c001038400b0305190380d100368490a441304101c2c100350550071900c040c00242821313405200322110703004540c1c000ea02071203005038428003a01000882c0c541d01c840c9818001d290000414003042d81076494400e0030303030f400800121100b4803003200382404101000101503e0700a03034003614101c00c8264010f000a00001442c454030004c3d4814140549100800b03800510b10901c4285059044607a82e6580558202d006110380c51887ca4001d5502111714001c200c80b6400c01c0c03070070018050000180d0000081041c01103000c010006920345503402c031600510100000c1c0c035400c2d200d2070000c0c08484c1c440ea0460b050505218000341c80c410500f014800e00c0e40d01d400d14540f11038a01486c3c8000f4045 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 155285827 1250 155284577 155284601
    0x2030a1202030a0f1b110703201306060207080105060a080d0507060b0a0303080426190e0301090b010e09190303090f05060f090d0201140a0e030d06090203060f01020d1e03 75
    0x341528210170328181e00b560b0140c0480329281c01a40325540254190364010500c0080c01e1411868803007450405103054100f00d80d04020701c5202c65030030070200318049807104e0740508090703845408100428a001c1c002e6690002d030899043c4921450311605c00e44031103050203008200700b000120b40e002c00800342c2c4050081d131000303001d90302c56903201d2401a092003000d0b28141c501904c0c1c010250750800080075aa42d12007819201e080c01d2208524440625071058064078003400071041080015172800d1082c0f510060203004101d842d0f515004c000042410b016203485440d8026181c0c5400200e03c002e1441c5000e0360610380001c0c0304500b410f060903603401ca0100180301d802083c060241d100c1d9589400c0c2c5c001c0011105035003040c0040c01d41a801c803580004020700c14a80100040e20302402603002c06138590410050b01d203090203400c8501d040701c01135080f284945901106001c1c5a003040621710000a80a000074402d40044c420041d00d0b00703640d42d6079007101d28041d021200803980f01c2c1e0480c0441000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 155287077 1250 155285827 155285831
    0xf020703080301030b040308240907020a060510060f0903050601140402040504020a110c19050909070e0a0f0c0302070b041b08010c0518030c0108190209120c01080702030a1202030a0f 80
    0x1131a03117480740481500f0b503030136000189548007141650700000324500c00401c06a6000c4e424400b0401400000d0b039004214400350f00441c400c48000c100c060190f07c1c860904a483e82c071009051000203440c4d00080c407103203010850999003e00000f100000d855055511402004800f80c1030100000d01a10440d042540c1190011600da40002e0308500105408454501a10079284146050090b28040d0003d15104840040000c0042d8140055540d0300000c040c0c0544203c00c3e100c1c41d84040740306080e660030b03500c541c3c0c90040302200c4e282441655007940e06441e00f98900180790f01d80740d4584a0140c405400ca00e48135800f070490691820b4000014030145000380030b0441203580140130381d005010107901c840d81015060310170345404100c02008075416110448180c40e280c2a1141d02c0d0425aa51201c50f582080a44090fa60f0b00a0007864401440004d056405510000611202015001c1015540300380022003541380c000d03d03941c16a6018400050310399440380842d40180c150300154110043c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 155288327 1250 155287077 155287079
    0x4030302010b0405150303070b0a090b012c07050904020a1806021b0406050312070302030c1203070f090b16020a0b03010303110d1716030b19081e0c010f020703080301 73
    0x180c0640141002c41c5007110104030300d68501d0004005580c04140850b40f40e0030410445000900e90107002e60024091040001d076180c00365903e01e01e5400a800c4040c4100d01092901108001060800e0542c1c2c003801c0540011700b0b105102401034014004807511550300402d1094245129003180c0080e0360f82a00550182695148040c0d2101070900e4100c140780c0e4140354503445810207000d0402151400b81c0100b000710200201a0a0398210380c031f085007140001c000c0d50103131210400c003402034070701c101c4201d42d80d900700704001814003480b4413180350602030004420004504800156503100ca600e4011641c40c07002e5200040d001c0134550082c440c82480400040207040c0c0c0302c0300802c1340e64905401c545010b10200001c0c2c801400012610755100c4400c030000e82c1e00580600425a2045039050100f11180c140300003444c401029400d1000720480070004000c0035208200c4140f145442009130501e824002c0c03e16512001900391090501a44040010160744204030050003146c00400d5035480e9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 155289577 1250 155288327 155288333
    0x151106010f05150f041203140d02090906032407030e0304082410090b040e0303160216030b18070f060c0b010609140409140d050316092303010603080403 67
    0x112189015803030180c085100f1103005002504129240310f40c030b00d862903082c1403410b8402480315595080c220100700320002e116141c551401d01400003c00c03030400140e104c0350305205228a505000f070185100b0750000281c2c003940c00030100e040708800018100741005980382c441c203074081e1101440c441001c0c07200041c00654a403000c01c03030314025050b00c16882c1402c814441c2c00c0c1d400c00d2007941e6a051000c0c1c6507508200250309644070303102c4c00b0700241002c5101c0d2814400d40b801c5820484003007601c4888601c1e20034000d0350500103483e020f140c09001114a81c2141c40d00391038014000c0c007540404122901d1140c084408000c203000804822a541d50110348400d402400e601c4044000c6500144000010640b580217a10050a4070042650500c140c0c410780c08102c090004007000303451214003810741164900701401903080101103600c0d404d0382ca042c030386040c82002000c858400100041100f050200c15100c510310340b018038040300c2c140c83c00c00100000038010607141d4801030141100042c00030170 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 155290827 1250 155289577 155289599
    0x60b0304172215050301030302030a030e0c0901030503070201120618150e040c03120305010605030415140c1201120b041b0803070b010806060405162a0c050a1d0115110601 75
    0x682c0d4880c1c021541c15214400c041d901341c042800000c0150300306000803861030b0700c2540301c94070b207101c5441102c10450309480403c0040c0d2081c1c1090b1119000081e0507000d55801041c00001007800107030070000545486e20b81480c00c0321b03e0502c1e6011903290400e50491140155a0314050702144405d4410f604003071915205060540c84103d0f52607820320070f1a113003503010740b08407812681c0d56140c035451961680d81e054007040c9403a5130242116074800f0000040b002d07080079180b18115240c03186a40d07000c000311107114101e05a00c40741c0203500784d0034100000b844980c0210303001a4001d404000c03106079400c40000c118520f4004420910001c12003c0a200380300040314122078401e000d03604243c03100c0c0103000c2032ba08201c07a0940f01c0900c0400302d90007e131040c006094002e90345070780e0402040054044e00c82911a801c8190340c0200c000106100358a4040014002001a82d508031196400c18036200001441407056001d201c1425401ca071546020b0442d60b00f0742c0c0e8421040c1d62183da160802030750 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 155292077 1250 155290827 155290829
    0xf0d120305040209070201020405090f0c070b1006030e01020412062a0503070908060405150a02040504061202100903030e09041401020706050108120c030403080307090f03030c05010f060b03041722 86
    0x100c1413500a02091442d40103108803000e90b24042c021031103e0307681401c0a031340410b010b80b5501700030031b0802100001c01c501ca0b421074060300c851180c0c07001c0d181c94548000d055031b80904406005910412040110b10b010744001d8108680c0324001251a01009580d01c039400403e6400001c0c01843e0304070000200d9000d401544200440e45401075031a0302c6004a03543c3e40c408640007003465006801c0c4d850840d0741d01c080a603108001140c054901a2220089000d03070b100303580105c8c4191100d001ca04110b142c2003020cca1800c10341d03c1e03c1041c031441e5841c0100800601c00506010350780c818085820b2111510906201400c00402036540305c0d140d19000005040034860540c050041900014081030120101c0d0982494100203500b0241076440d600d4590384060b001009003c4141d40003d020308044050000031030298940304850f00c0c3e9400d0450949281c14110a9103a00e051170501001c40c031801502e800c6600b01d2444444200d4030828410944103100000c0d8141e00f0040180d16640b0b44c2e60400c0e4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 155293327 1250 155292077 155292079
    0x60306030605011d1512150a05070201020a081302030a1e05070603020f0f0c2e0606092402010f05090109021f200a021f1b030503060f0d1203050402 65
    0x1c607130340c40803584000740b0501001d2010043c030308003007200c2546500c2c416400b40710041040001c0300200c4034a038034001c2e504142640e1004400300700950400144640b56110803140005e62400c140c0090080615000070030600c007a140e8544e10030155202040070180081c0e029100244d29110691344010200d40e00c0c10890b113600c40c1d4800821018464000e9403024600c003060bc40c00d0940d000342c40030964008001d604070612501d081c4071f029011800920361078100f403030034880035001e40800b81001e0700ca071600000140000e40d0070402a90720040107403500040448161841213044120481c09082035400390840141890244401890190f1000315014030031140141101121510710510500000c600720201d4202c1c0010803600c1300040091102c41005030945000314441d42c00145200494009406600002d980c0d58284035000105440305101054440c00c0080f44d607540207101f888001c00650045500104000d41c0f510364542c41e0800603881084c06e079486504110080040c03104590507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 155294577 1250 155293327 155293331
    0x7020703080301120224040b07021309030f02100c050318031e04060e09060f0f0105040b0d0c0e030f06010918051c0305060108010e04030c0f050a060903080108031309090302030903070603060306 85
    0x44010928540c0c81d0488050306c0e460a90400d85041c0807100755400c00300c070070382e046041021140d440714442e11071010350301d02c643c5850b4140d040d50300c070003843c00035084400307041180fa08034036060664004041d80c0e4014008030b40e8100e144000c1848a0441c001c48001070109500d41c1c201800e01650300018105450b1595121200c2c051008100294103409030b40346a002400d108a401c22070a00c7d0b01d050114a90605290b07191035518410310409900410085061555406034a918240d0007891416035400c100c005202c84c1d01c60302016602c0315010b104012a5507030754907140c0c0420000304a036640f000d0f001801c0d542c3d000b80303000d841d00380d0145c2035812034000380c6802d002038a15806250344e2816194200341400c3c85580790342e402e035488034604009a0f00e20f11010181000aa02004070a141501c00c4030045800e010601e005480040306800043c0190001c0c0111040c5200302c1e980002102c420035030108039403c0c541800d0f400e5118000015030076010700307440480c4058058021508480c841d0b901 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 155295827 1250 155294577 155294599
    0x801060311040e0105040e07081b040b01090501080601080604062d1205071710051302031b2b060905150606040b120601030e01151a030103020901050603070207030803011202 76
    0x1400d030742446140501c0c03801c143c8680051029051581c4210b07070301c001036011118201e856224403440c0c01200310141030f20b03240c0c0c0c642e0402103061a005600c0c44070000e00302081c82d035041600203010003400a01d40d0341000b0780100003030220303a00c5820130300c000e110304a09404175181d100c213089a5078080648101481c190a8400601e94400022404100381c0000181106a092080385072000250f9008a40e480c40741e945600032180302e03413040314025a10710140101091192041c035080032221490355002c070204426401441d2150116001410302c115040000c24440c0e03042d84040d001103482c00340204d850410403408000001842940194038016012010341da00010480288203038004c85070381603007d00c2f50620141620b130368140c00c10014100441c4031204900030b40c3c03c68000b6150b480c101949400d00b0018600741e60143d04109940070003c924640c156008500b40301c1c0c06104045c042c44002001a0009100b44541c50155601c050b4080e920751f5030700c01200798051074040903407154000d400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 155297077 1250 155295827 155295851
    0x50d051b0301180f020d02041401171611060a140c2a010b030a0b10050603153d0806030a1203050c130315050c0a080402040c0309050d08010603 63
    0x3000103000e00d0805145145070300b442999a202103010f03640d842000c1d100d1243c190b0720041c500141050607200207005898500d85400c218000f001002d040781840044e000b405000828004240d0340020300e008100000b00e00087d00320760100e0b0507801029180188018440d405109410900308801910750b060b0941e250410722254600c162031590000724104564400904000c0d1024001c03000900000214404c212020a0514031951411a1801030b00020043e40d0103000200a0180ca815070b2080c0c1146400116034000008180d40c2a110b4a1040005551054400c2590000100c00c04420f5200b910140c011112140781d803030780001082e007100001308541000282e0194440e00075108006450700904190b006181c05060441e903100204154400c444c46101c41100a51180715501046501e4850380340032180007074081c07150a03400700465010f86a019900d190859011a0005004213041105400400070440000c180d801459440001e1581200a150489215480c00d03c551a1484 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 155298327 1250 155297077 155297101
    0x70b0301061706011704050a0b01080d051602040908040b0d06091407030519020406110d030b03030703030b0a030204090506040311010b360c03071403040c050108040606030b07050d05 80
    0x102881c400070b4030000070000c40c15800d078a40c942008041c100f8541001841884c0046243c045030151280c3d400720174160704114030300304403500500051000e00806c404510005041d440707a60084851700c249292258190b41d6250f10511442c1e5003e24215511380d640c444000407900001c0300c1e00c02581c500100041d0001c813a001d041448032100b0b020425954405c14154010b11015007030b01003130b074101800490102018401400945034644505e0068002441c25500d400c1a0074840d20030541080d50041c282c1d1400029201c1c12581400c01003104070780100031490400d5107502c003a602508181030101807100200384207002d03502035618196400c5041d00c5c00703400d0300c03524400e894101801c4441c02d501c000c100042100054000029000c00040354004044441001d443c0b0001c185000000d00c054150401e0441e40c1c4040516005800c5103010f40791002080b416200b1103040c000e403000080c0400145034403281c041c0d588507130100218184080d0081041e045808801c0555180c0008103070105148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 155299577 1250 155298327 155298329
    0x20f060f06010e0d0c03060c020318151e0d0c030f1416052214011e080c0a0219050102130e100501030e07030605011206060603051b0c0c03060a02030108070b0301 71
    0x43c2c440360380355920750042c0a4600f00019054070038542c84c901c080300003100e50103020310211b502d034011501d5107072204c540d60115032098045441603c02c14407907289030740f0744d0080e20094480345160903242506d000fa69480e81c80780d000e050711002c2c9404900d62350642c02d64400c52880d00380e14010010700c141000f04400c5c0f00c9041d0b03200c07054160140800007085100d040100080142c00c0306804030740030b0103039403184600407039001940d980b603a00d0841c24065030301c8030035003101031483c4150404050b0300d60005044508050320344150745600080141c001c50080103209030a200400300b0001005103420024000c0d0816081121004041e01000641441c02040c0602518240c0d410001c0c5134685001900203041086849800707003d1850300001060092007482d00806448500c005902c14a2a1680440e1166013000090501e4503040c441c4a240b10000942450004146540d4072404014003520300f0354003403480d41d8103104000070000342d0320003900030318101c410f200308440226849a043e90114082 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 155300827 1250 155299577 155299579
    0x10903020c0f0607061b030b0612010911120405070503070b040605040b031b0403050708010c03022b2009040f0504030212031005060a0201090b010522020715020406020f060f06 77
    0x2489449110b4030300341c2d15400c4922001003510b4039041d015a140c809030b400141c00d14000000600003005040d8040c01280090501295910f1601611945120a003101070003040b80d00e5a0b180d8202e9040c014100c100c0e6062201402c0b8002d547c0381c249002ca87d075040b6030145900a010700c10380000c1100044094806660587c3c440724203050916400d020143c20003001000c9101894003102d60001d000e070300400c05140600c020303140c5107041c48821400c1d103143d42052010544108140100030342c0c3e10b000c810001840646d504044000f40c2910320245c01844a44081506203409d1102d640071018001c00d6030f48419101440320402c04000c5608461084034003038056007041106a201c40700203001903521480905561781c10a071030703501040e800e4000350070b80300c0544e546240300320500141004513401094101c3d56903160030304c2a0b16180402c0405040c12031840e80100c1d031340f002c220744040f500100c02d4000c01b08549072555110020355078a81c51301081e030940202d074042120b9005580c1c01c2481040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 155302077 1250 155300827 155300833
    0x180f01050915130510181d01030b06121009030905030a08040e040f080327010e100f0b03060906010f06050909151c06050a0e0a12050a0908160f060201090302 69
    0x280d40c0d100180ca90b0100e00c095828003c4404040703400e554400c07001900340c030030380c0e41c0c401c00019134402c03a01441550b400014103295010380080d1604a440c07001750550303502c1a5a0903082d1208004143c8407046800f0403040b601401c185410311010315031040c1c40e42c600035a16100700b9983d0382d048c50340302d000349040a090307564100300502200b81101d00554004d0302c5a902c4554103071940d1640c0e141da80041d01e10300304401180402d41310201c040d8083d8007100003d20020005041d08000325a0750b415410b00302c224484d15100c41c00c020760303602e0b0700c200441030015041d00e505107007030200c1c1c5031101d000340107541c40d00c84c10725000309503d480341041e94005480500b01d51040e89520503403002d6802e0540525902006a0010004c0e8021a40188110501c160404143c500304420380205a4400a03c2c0403a140d000c03000c3d000c0425400084801d04513400d0525664855216000b200e51045540103120288180d049103100c40d804000c00710100d40d0b0841010503401e4641408900b6240180400340050b4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 155303327 1250 155302077 155302099
    0x506030114040f14030d020c0102180627041e06050108071107031707050f100c0203130b090307030209041506170312071b05010e0c0d030518010c0602180f010509 71
    0x40c004d0744056054500141202c0c10708803a600c06200340d03841415000c2c401d03500400c3c03014405007009442c809040044400302e044c50011410041010030384204114442801d102c102e45548503540006040340c10107031360b5800c10b0400a285005014141f00d143d000801d040c00007100d80d84a0040d10000d004c00b280542040f91641d100c501002d58002e02d28614400b04110303e00000e0740402c5907040e1991000e01901690030022240c40072181601b210b207040d500100703c0441d4106076010428240e581008850740c030380050001103850201a0741000b908228100288070038400c944c040f6410f166607103181805200d460f209090480d4420707078404009503105100902d401d11400203a07582c40b040364940040040c880301a038400b408000300045e591a5921580c0038400c1d541072280b2114001c090b109405071080c15075009045104810303501c0d50781d000c034003a5401c15178070800ca01920280c0150040d0740303510642421644004018a04921030356070b0301c00400340c0c1d50040d02511841c1c04000c05802d208 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 155304577 1250 155303327 155303333
    0x61b0801181a04140702070501030203010b09150c01050403050714011505010c0201030e011a0111030309030a050a0e09010e22050d030902040e070b0c0d02010605030a020f010e0904060506030114040f 87
    0x9400310b4205070003000d9031504200002d4980c4d120340c81c480e40509070f02158606001030041d0800543d034000074101070041005104840e06401111261704e81900c19000708800b040310316102d4050040100c2c060b508010500040c10b9019001c2c081340e501940c00ca503212030b105452a801c17103450510542c0103140c2090708200300c1d070203041c005a090740107040101d4100348940b0010708403110381100240801c0708a01e001c2440d40c0c02200f03060260314800c001c600d903040c05074055640e0300071f441142c01000000582c840041e8480d038954100381c0b4000c4c10b00030b4103517194040001707400d4040f54030b9246012009c1038101e1b030381501c42c1000500f40d0018042d0181585400d011009080e80070b0f01030360407540303825551380c130300d4010060306008000c0c0040e41500d0304c92800806080404096240c03007103a0400005002a0384d010403e0a119030741150404440144400141d0784003100d111895844004c0700d0400c82484800c1d04047d102b004114020000588009941a403000f03040d1406000f241c4006011000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 155305827 1250 155304577 155304581
    0x100c090801090c03080702060909040312150e0c030915011401121802010e031e030c06011e2c07020703020102070f0b12040606030b040c06031107080d051909061b080118 74
    0x6c180054541d900c0c0000f000e0200c3e800c0c00c0c0c151070442c00039508074162038922106224034649850000080b4040614200a0304590340c0098403c05020341e0001c0441c4510340200280180992003044800d615a516108171524050300c0380e902d40441d000030b09602141c0868802c101c01120000684545980f05800459078001c0142500d5050b04c510340400c10704410401001c1e040405d00d900540c0e442d100d02031210f0401c241a80044a0f030030300011014110002080d51070251094810b00c1982c640c07150b0f160b002d4285055403a51100c98286040c40403481d4042120b4065034000e800311601e040d9202e05803800b8540724801d008038041c041c0010126544481e101d00e03045030080034042010341e1262201c407165030060340d04445200b500c401c2000550b4140c058440d6040c0300c1c1134100e003440282e407500070f01842480020b41c0c10a50f1900083c1c0136007800d4013100d00d0043c4d001d008003c3c6456605e8142c004201150840d0604801c0f610030310003041c8244203032070588014146100300d0400d0300302d107080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 155307077 1250 155305827 155305837
    0x1903051506010201020408070e0a11070210050a02030d0615020f0606130207060e03040608041202070e0708060a180c12020403020105070215041d06010e0d0201021b0111100c090801090c0308 83
    0x1c11135408100000b200582040403601400c2c15240708140750904c40780400850395441050020134038103000c004050b949040d04030003c04101d0030810b94035448007200302d0442c030030040f0751600d45181c01c9001c00d0044d4003a03015605c10030950200da043c0d1550442c20340d6030719412640e840d40080007844a00d000f46081d00a0108944505808079042d14400f2003141160450f030821030000c0d030b0890030001401240703580303d500500140060700c0740c1803c00015064000008000c1e6050043c042c1c08201e05845100c0500b0040928101c0407901100401050000d8900c2440700c000080100030800c0481745540308071002c4a41c141c490b07516101d100d50a00c1300b041c16501c003408122400748400109065200b14010036043d6610b105582d41c680f40c0005003204840800150003240c0b110041c80060f40c000850204802c56000c2d42418242d280c40121840d010705201e8080302c3c018800b03c1441c0003650740018800d1444c0391150749803140c0714800b242c200c4464070800340544440103000c1010a6114000384 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 155308327 1250 155307077 155307079
    0xd0e03030706020408010b18070e0411120c0307090f080a060522060c08130b0c1309020d020414030f0a060c0504030206120f070309050a0b09030c07060e1903051506 72
    0x19007420415140e001c200d80203039001e0540359444600b4190149004016a42440710110400e40c0f941040750340240b81f003240840c1140501e95440701005682d155030f060f01d0151718103844100710b82c82d2180414185820503035044001c94500781001c0380d5202e01c0c04400d1b007038845090081100d1200da07180d4201800300500030b42803090710004a11046c0c00301a008445a07802404042420400000d000340305071030003041e00f20044840481d5a0026600412040d000485100362a031180e403c0e4400303400c900c2440d406628054030000c1c1481c0d00c0c40701174014008494010614101601031407040c140c8500b102488404130303401c0b40320700a00290130f0743c0c04461000d80501e400c500705501c0e03501054103907000000003441c1004c8001004030b20141c0b5400b495000381039203004d00c5034441c140e42e00c6a851422190051088420100090320030004005803524002c52804441016585900141c1009445080a4018107030742890760300500e6022071000c1180c2d03000340105041e050455402d80d4200b0064222 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 155309577 1250 155308327 155308333
    0x90509010515070b180f03040509010f0506031801061206050f060904030f030c140406020f060121080702150403080a0e032407111e10060605040506070f050a0807110306090d0e03 78
    0x1c0c40d0305c00402a0306801c06420008564850400003001a0f2650580c010079505c0e001840c10703c01500e0307c2081d41d400c01000725540c0b4800111300741880c0940011f4100c2180e8049001210342800003e400c824041c519589040006031610000e10541d030740d045501031301150010050703807a0f4070b11135840780000170603620b0144159500030004500c154003561085005074003232214080da03c0814840c01f4018403808401c64026002e0052035807001007032000c050000e40e03001c92104151740300d030040b01c00342c200d1301c1070300513a995104c0c6403c01194000c02d4040b00062100000c031885402c0c00030300024504a000300c10049840740a4080306140001001c203410050040712642d010201001408111400f244401403109140300c1e5080c85c045070300940e404810b040090401001b03402c1022102034800c26a00250342d54010b05204044a4003004001c3c000d200c1c1c5211001403120140103041098492904d0841d2100c9100c03c042d514a03041d942200f080d0442c035002103140b402a28001d089400c00b8040d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 155310827 1250 155309577 155309611
    0x3050f0408030d0207201c050c030115061d0d0b040302010f0905070821030412020a14060604111201051e19050f010f020d0509060910090509010515070b 67
    0x3440c11504000703c0c03091030f0340d008103c160400a900c02c512102031540300b40080d141e0801000140d0000748003032007410404007000c003202400428042c60480b42c001800038003c100743c40040090300001d9100d6440081d503450b840e04040d00c0040703120540c3d1702c0c008116958000c12034032900e10401010740120155940e4090803807270680c1c14010b841d4200d0240d00588055458050b405080043c0070810b44440d00c3c0c681500e580065000b01a29045500150310f0000c640b07a0314010f03460803104c0680907042002002c1c036000c0c00c1100240340d62144100340d074240a00d81458403618501c1c0603052007002000c5040d001803100d410039400c0321420290182c11820700c9001d800c0421001d03035442c007001c01c00c040b21030340034001414421903000c3c901d01b0030311709412024040d10009468121182c0b01c0c2e010400000707200340711513458074241c4510b090000c1411115000403c0d024103080511321a850080d4419800001e85280a00c42e010095490490130761070410140c2e10b1a04403103008042d00d607c2e42d50182 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 155312077 1250 155310827 155310839
    0x5060117070806010b340b040b0907030305030f040f050f0a0c060e060d0b0609120303010305010605030a020d030c0503040b030c03070906091421010c050c0115050d08030a060b0a020d0e060a050703050f04 89
    0x100f14041d25009660480030740c1020b040440190100510ad6111580051002c000082d0b108044a600201c01410750075991501d240a016854100798080c01a01c901059103003210000701d091280244904000c1b070b0007a40d100070649034491401140ca920900a0001503001011b607040421003550041c121480c265808000860101c1e4024480c2c03016030021005104101d401d01c0360f0805028210000d0298200942c00241c000c00001401410400c0c0100c15400b04a000c20540d006460340010076a1070340703000989a01503800494000c80085c0d40e4070000140749000c0c440c21819100284080d2081c0c1005c5410f0080c02030a6204103082e82e8904c0c60302850b282000c0c401e5640c6c2d440207644560351507840c00b8925007516001e41034403001c1344040808020300c0c2d490143c40c0d92030590111403291295504c82d850b4009080c19441880b4003c0300080d510055030740030580c2c003001003e680b00e89490700c8824090003000d000d00090324000c44c40400032039020034040c0000e050b102040d0307510b01d481c10351a10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 155313327 1250 155312077 155312167
    0x5040213150f082802060415110307060c0206070905090c180604030605100b18090402041404030e13051b070c090e011d01051005150705060117070806010b 68
    0x140c040300300c41d00080c01c03021400c01341c0000d002c48115416200c0c120031190b900001e4040c46140301c0d100580f003840e41018900c0d4001d141c402c4030303014030745c00782e80d280d16442c1400381c05030000f60040d00043c080c800c00501814016200f1109a900c05042c2a03855507807020141d003540c1c44107602540c6403100c86555042d581e1618020400b40d4410600404d680c10302d40b00c602d0101200d900003048044047c0001001c800034441c2c01140e8040445003210580c40b02d00114009040c03c0f08030400440c8040d00f0002416080400e809441e60291410316030340403000107400c12241d0988401607081840e1046810280900c03000d0902180034460111000356146062022038040d01e050100d070365116907003802d07260000588002d03044000d90003486145000d40c02c403400c4200740e00076544201e034030b64143e00343e0b03070242010b54044603800022120306513104d41310f1a003070380000d0100101510130b504010070344c0980880c1050486d035991305032030b003041240e03581c3c0000608044215006a601c2c0d400b9503150150349 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 155314577 1250 155313327 155313329
    0x604110304051e030a020a031b06050f0105010f0309020a030b0402010917060105040c05070b0f0a11070309080f01020921010219050d0c080903040b16060e0d0201050a05040213150f 79
    0x5000101107080302d04500720400200c400c00c07038900d5001485072072417998010441044040e4586020821100307600703c0c090070420b200901810403440c10007040a0000040491030603175a00b40c0381c041c00c0080c454800c5003900e240303201c0203400c011289410400246d48020081d003252050414941460301c1c0c13003540081404d41001e0016075401280104114185032003a041c540c0e240e8604240b83c140191201c0980140c003610a61004400d00001803010302203a000345400510f00e03101a0359442503041c0184260001d004034401402070f0507000f0284a01442154900a0041c01c2914524101091250850b080591100c0555002c00080c88114014511400c0380729003911515210920301b5102030440d030800e5007000a114140003402003c0c4c04c004291022161180002903907408403108880c80d00601c031000910450904940c00300c001c00105007107650b010b0641c0200000e94402c01d02c003068500984020b900300104540c01000241a03802c01c001042409001d10110f42c1d80310383e0600352903c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 155315827 1250 155314577 155314583
    0x5061603110a120503070908030406050a020c120604020105070503070803041a0603061b070609080301060206011701021321020d23060907061b0501050406090b0c0a0210050604110304 80
    0x4000a82820190008151020360154600a2801610303603602c550555003c02da2140503c900840001c0040703218039541c5002c3c058000640f91195600e800103001a004106060054017910300407070200c1c241441c4d1a0b040e905480000c041540315a001903845501c1403005841c2c1d80410050107010520000c0110300903071040281c04003506184030400c010200140246100c0d4102e44240004450391002d0b054a072002100240c5d901c183d03030f140040040545034401040e045020000055568011859030f0483301d501000c94448104c3c81c105500303d11800045800240170007800340b24200a41d4202c03184602c2030b20011440c1089900052140014010200c40002034800d0f000d817425481c03101c4031030031024200209224100a03d200d51070340120f0140000b0417602d02a80e042d900b01c2c040b02d1480c4590000001c000c0b80c181810210040c010b030400581e80c10035000c000c6144000000708481240c59aa4003400f6100004041c0b140900000b80409a00944440f00d101500c4012401180140d00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 155317077 1250 155315827 155315857
    0x60106031d032b0612031b0b0406150e01090204060924050a120f0c0e0409021f03060314010504050c010503070509010e040204171005010602010c0207290708090a09060f05090406060506 81
    0xa0921b40144000c0306183c2074032000b200c0c004a00009000f80d900550041c2d0302080204903051031014010348000c0030b038000c03010794040700300008100541d40e00910903078840b552180c8459859528106030480f4001072542315400301c80c0c84049880c030490143c0107208851801c1d08003021248401e4040c0c4008003106400d15640b81184400c185d0000c10f0080d0710042507800b88401d803180d400203a43c0083d80d074001b0300f5010b585031450804d10304c207502c184040c691107094010b60619a0b03821038000c00307040b07038211018414101c2e00707a00d560007101500e105241560350540740c1510a00115905105070080d039400580a11011a034034092581c000f000d402d0f068020103840c070285a045003614011382c0181c0a6900d451625950185e002c100d460030b03150002c0c811b290b020305015180003000c44403942030758402d40105082080140c0c800003030000c0030040701d0300d80ca41d80e1a0010f0b00204c4510b4407842180143c0b020b010005410090462907206004480024046503203d0208000707903c10507035669003030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 155318327 1250 155317077 155317109
    0x171903020309040617120c24041106071e020a050406060e09010b032e080724020c0306011418040c0519050114070221060106031d032b06 60
    0x3090074130030840140719581e40d5650555030000c5441d110202d5505185c80b6210000d24483c0ca0342017004618244420041c04081500810304007680701c00381a602110340d0070746510b04032140e00d07108081d21030302500162554600c02c54854150710b40d020480e400c9030081c0c0c0c2400000303240d603105e01c41c8000505240e00d0743c1d500341401004205940c00c050700070303028004051040c480e800e4202c5250702800c410210452501141d100042859810342d5448580988540c0d01c01007007171001c00301c8000080040201ea4010501108810fa840d107415804068041e84410010480040b00740118445641e01401500c0d0400580780e1040058031304688c03e64500800341806c2280b030500e80c1d1540945a00004211846070611000030200c0750b40c10f145842c2c140d03000c1082015941d031030410102c20035150342c43c0310480c01e40e101c113291502d80c248200d002213807074001206682041c0c0d004055410452001039807401c928030300c0035000704680b4500c0ea051010328850540c0e101c019482054058200d0392500035145d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 155319577 1250 155318327 155318329
    0x10050a0e041406060906041205010902120307030e01120f11040f081c0806132c01060506090d05030c06010b04080105060a05090a09110310020306030c06030907171903020309 76
    0x314140000c01030140307182010984503a0580a0341d00d03008001220341d160385648030800030ba01c502a43d0480210381903036030078038420030005510140d40710340301361109039198802002440d02e902074030202501107001d40c50a64410342c4181e00c0c40400c4544920300245c2c03a031034092007008a03180030068902d000c00000301806440c40c01c8001704000d2a00c072006110b9041e2071079030224844003502d4400305001200c2e000c504507a492001c54541c00301114070801010480d001c100614a90a080c240040d60040c4000020140d0602a042c1550300c00b81c1050725091032031081c4540140e4400d002d49541c0018800c0c28601407050150034020040b8040d01921039040400c13103400c5900c080c082c28810114040104511385400145945c40700444c00e001030116200e04216003804442c012055150140b56005e01d100680c40c1d010f1030103901c040e4125541211610280215807000f038480c030f0030550000c0d20420500d4950304c120b01111107110283e47d480e054100240205820942080f03001d41c00c0481d0382c8480e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 155320827 1250 155319577 155319587
    0x603111201061a1c0c05030a1103070f12090209040b100f0e0705282c03031b0a0507180506040506011b03030b1e090901050c091c0210050a 61
    0x2080c805035000300002d515007061201e44048403212203450319808a07558070a11451385052038512a0032070184a8040803100c01031141c5e00407907030200c03120315050412250040c0401624429243c548171401054108081560b407030f45c1080e0700c41c0059407614501001600c0b41100c0c80e0084c1c3c815121008142007a80054506803456000703503c018000c13800c100000310342d84040c280c1103030280c140550344141100d451103104558480e015254010305c03490701203090b4040100e407503404405d04242c0070b410104003c4120007004440c91540360b0720502088603a2414072138110405800c0000b2a1a8800c8540e529818101641d00040c3e18100070a01010302ca000f60252952048046030104420710300000060422402d04590441403504420007070101402948080307030324280141104850841000c0c6116041d0801e50b100d0f0099801201042c142e0105003e09030003641c01140450800ea503c0046c4084800c43c0840124040b03e59081c20003d40c4644000c5d9003c3c00c1c4540d1515038400440d00058a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 155322077 1250 155320827 155320849
    0xc06070315030206030601021006081b040e0a0b060a0e070c061a01090308031005060f09032503020d0201140c100b0d150f0921020106140f040c02030c01060311 70
    0x10600d4100034038250040c120440c8482940d030304641071a266194040102c0c41e002c440012100300615160003c42c800c00001400c81842c5d10000d46403034040485024072050303440172602295140d0107081180c001403032510400740d010101908500c80c456039110301700c54112050f940c44000c2880304101c1d405003c0640100301d0f4002403042804c10340110440000c208805610010b006c1c08000f101207501d40240b400701380b0052034000c2586403100c41401c540f2005a006030704e407511920403407250450000c0010f2b003d004000400701c054000c0303859038007404950060440201c0c101b01b0b407014509440e0024401402c04000c11800070090340101800d00c4007140d156134092841440300314800c0c070000300c900a0b00c2501c40c10708040401c1340a140e440e1171001d44907043c4014030b03452941986d0b08026290200d8040030014940c000c0c002c3d941e0b600408800469034441c055007208141d43d14070310700d0505800031a281c1c0582d104917031903c0c0c55940c0c000d08640140e001204c004e4001d1135150041d184c0590421 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 155323327 1250 155322077 155322091
    0x601080c03070c0b06013f050705191205040303050402040f1b03150807030510050f0114010e030a06020d0b0a0509070507020d0c050303130801051e0a150b0f0c06 71
    0x3515509020001600c40584208010000e006140026480e6407040300483d411450a820011042003038040880b4082c0815114030083c0c0300c034160f26080411f0758040d407805400c032034403007034504000d10355440c44080d114202da600713000c00c1c0030550f00c0610480c400d203445240039540000b02810548100400d468049164101040c01c02d500190960001c80364407044410b9410001b42d4407640b0f4071144185440c0b0740c0414031501170064004284000808c031885a956801410042540c6ea1200100c220f5028010703c4190b20340d901c85e0041c21b5019540801c52140024115040b1034856074440381641e04c485c2d030351401a42c0302c07080312004c1c0c240148503030040c243c200e4a0041900c2e14030802007043c010702c0400f0784100b564560344001e1008440f84400908000350580c0c1d075800c41e01ca20914280b4007849114002c0d0f1801d40080d8884012400e0b54906105140301e201c5c00391103002140b00038000406c0c24900c0075240003000130310f640c00f0340c0003040d5029012407410340304c074a480500c0b030500030001c01c05 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 155324577 1250 155323327 155323351
    0x71a0c07030e040b0a06050717040e04020901060206010b03060103020c1e0106050f0109030b0402040519021201030c05101e03060803070c15320904150e1003050c0d110d0803060108 79
    0xc841c617598100c16106803141880c0154461501e41407019952a4070740605480d0b420000307011a2410f020078220b403180c1e00036130b003542d9540d0741d03a90102da84040904c01ca401c40c0d81d081c0007184181d84070b40c000300905002c2e54200e424858200b14504442c203410040d800c0140e65880c81008207040013042501000002d08210000e42d207181c40340030784500018002445583c1c3c4c0c800040130966001e11000301054007403021034560074030f1a004101c442080c0401d940201c3d02180005203450060445543e8240070755604d1806c408800e032003074000040e5130340d003001e0540b680b00114800c602000680026401410048142440d11a41c1160158880b20300010800c10f074444a0041804d084a00403071140d071212051186c8200c14481d24500500c2d55480c0d02a080c501501d210011414541080c4c0704081c8001159860780d0920100b0f011440c4401022a0004203600c036280c5041c508266030f482c090114003c40090100006d0415801404c0031207285001009024855070320900b43d03a072259065942c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 155325827 1250 155324577 155324591
    0x20126100609050d060c05040305030307080402090606040b121b0d0207060501050a050604060507020f06070f051e0c04090c0306050708070305010602011a2809020a110d09050105071a0c07030e04 85
    0x13140200246200141089807650800d17142184140100c4008640004c01e480c2c4034244000d00900b200c0c02a20143e04c074110400103d5624508042183e0480e00e0180ea810b1a00100c01900c0410304c9000301086c0c505c1409000c4040d03140c40420040044802d13280340140d03200d4080c074008c000c981068001c14001c100402c0203111a0303c0d25000c803801d8070102d007066030722030603e07200149041001e080fa80f90050b03000309142c01007051602c03810345500d1113041aa14007a50007034100444001c44000c101a65200c03c1c80700506017004d42c44001054020280744203115140d40750b217000d59000740c070700e8000240801d0410403d03907858400d440c0505a00d2009006c0441410200f414107405006080d1081c803046d011405101084983c0104250403050119032441c0d403003140400a40105502102144a10010400c40000418005803035001500e50803101e900b00001100c454000000c1110f900c010207807901c8060035080f4043c6d22402c1c401403582e66072211450000c0000c4101240140a6802d0503c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 155327077 1250 155325827 155325829
    0x2401090b010c14010e0d030b0102010c0c0b060d061b08040506090a0c0315020702040e070f05150301061110050f150d03020d1202040f030c0303110303040b060d02012610060905 77
    0xc80d08419800540c400e9501601d00c805600621000f01a42221b201c0d10349a041c40f543c2507041400140b0f000d800800188072246010741e1985030700100105541e0921000511602e4900070840019005a80c002021000c054904268200307078002c04001c10510803c00c4100401086003a40c008012005403801100c1030780c42c0c0c0411062808000d005044e19440c141800700158140d40751690010000d1262800e582809038490110303016200d1543ca00342000300b118180f40d10354092031101300302401e1450b0b10300601100c074840c41100301c1100d8000c031280301c02419404d01441d030013900c12100d03030901ea09140c422190107548145807103000e04e030b4581c2000b0110b40c002ca1a1400030000b41800000c90811403010710091243e41c000f007440045011000c800d02c6001c5000f03000740c0348281ca4203400c1e41042904996207003c1110014030f200704920001d0000d041060705034026a2040c14032002424030040214444100309072407e410030300030002c1040c49410040d03440010400c9003400080242070030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 155328327 1250 155327077 155327087
    0x1401150f081b31051f051303080901030506040905030a031d0d0806040e03090307031515080309030105060a1208030c190c150c0503040b090a052401090b01 68
    0x18040000d010041e80001c007820a4031000c10007414103180e070541d0303030000c0729500101402a1909501d000000c4046155000c98024002e0156840100042d540d0041d8a090007018150852a4410010140440c410940007210703000d000c1e512a601307442d2903a031b5100005044800c0100501c2c410390801503031002043c0d0200c2190340c000450f103030101e01c1c5406100d0102c185101041b5440191184070901c513025030348007980900aa108881c10710611100e035111a03a070740250b804099240c0c1155208100081030070035a140ca810b0040700c041031606180c041c1200300c0c0781a6008014603000015840d007585802c2c800d40741d0207030080704c0791401c107400c0c12450542c0603c6200000c1031840000046000100340c402a55100c07101c4440c8580c900c550346070024031003060150701301c0741a40102c2010440c03004038000c03030400c2003070381c0c0d00d040c155a40c0d510b0700305610b40090002110b0780180810000443e600740b00e41c00c500180040d504030b14100705220758901000c16880001c0891030482080600e030f03801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 155329577 1250 155328327 155328347
    0x30b06160807050c030d0c03140301050918190812180303010501030216022707080903190309051605012d0807020f0703291005010f030e0a06140115 65
    0x204103203070b80b142100d150a5140c1003822070b0199051049042d10344541c2d5012561103d1a8860f40d68041c11a82e030689800c00c500083c0500e541c040c00c00340020f05644100c0364110004201d480444006411120b03004070040303152981035138042c100081c8105007048041d0185d405c8175540300f14214020343d10f00510380364001800f602c1d04141d0002103107600b54000c0c3d0b00181003250000c0010600c4442c01500100d00700004c140b00340d60340b01440004050902965065103e2100b44000c5c0d4641806010300c81c032034122400d0b55600b03260703850020785c0104004100c00d5090402d103810174084c480c03d220014101d40b400301d180591881803484881e08141c40b0011301c0c2882003940c1455110390722441416800d1030080705020b20ba5100340c5400109200280720000c9108144082415001d035240882d0055030304211211904e499500a04006a502c5602400c101002e00d141c0010103808845078181000c0b07400400f6101103840e80c111070300075442a5030107401030903600e151a4656001d0280540780c80c000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 155330827 1250 155329577 155329583
    0x30207230a150c080c06010e060909070e0c0403060c03050a0e070b0f030601091502060a0506040b0904020d140706110709200c010209040c02031803010c020c061b1606030b0616 77
    0x2c0c0080e03011078500403800ca07421290b02c07072051512008a00000d59581c4003d120322050114031070003260403403c0004036980501032100182020b075082a290075a0980f004e0580c1d0302c02c4004020001c04a50944203030b24212603155004902c2c0e06107102201d0940c3e80c20402881c0c260800700081240ba80d42c20101d500050810200380e84030f59942c001610b01d8101c50f401560003400b0b9a5080018542c0400c00b944201002c000811998942405000458850600041d085491207010401600d8000d603004400c910540c0720129440c03642c005075003400c41691082e0080340c1c511040c0c02800105002c00e1015004880c0200007146590380c3c40d0203130180a884a8603070712000502110020420740440d0b451081c040d200744002000090000d42d03e40c0240e201d1044803903c000c0000c407620b018058900b103411a64001c1840071404020851075610151640c0803401c11b00340e44a180b0038061101c6004400d90342e8900782d00350b142843c003400b640d40c1605018031400c1e040100341450b100c0b50000f4998503030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 155332077 1250 155330827 155330849
    0x1020304060e060f040807030308010b18010305042f0306090307080405010507030c051911040903050306190e04050607080a02040806070e220f0e0f0307060c09030f030207230a 77
    0x608101281c8288220340c1a4004c41c0400140810003050029200044a03c00d03550400c8aa90b01e07017809510b400b603004d2802d007500714039811070074540c8a0780080790001d000e070388103001045100505984914800c4048141c620b030400d11b40c00382d8581440800d911859240c091072510380c0640e124403680c8218081c1a06110020540006062140c0101038101358044202d0b2000d0540d0360f00f19180e4a0404412a400524442425520308280c02080304456160722220304680b1000e041101040660740c807400e0f5508072080000e070499403166210701440c082e4000c0d0015092040c2c0017031880d44010020001d00d40100820000c1c8a000143d0b994007180516083c62240140000100c07010480101c4590341914905101086003d81d03108a0405a050904105184503840c155482d003503161460381858209104443c041603168000c2102c09003203243c07140b0000d880e69101041d000b50038100342e005a01040c0140114000b0101860400c8003166201403035081e0000003d402d0440740c01a200c10711 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 155333327 1250 155332077 155332097
    0x1210090605120c150f070c1401030b03070308160606150305070804030c0f0311010509010621020303030c0309010b100e040605010816030f11070501091709011209021c0f050c010503060102030406 85
    0x419584241e84005d01d030070780215901d032000c0c2030158100b02035019412403100041d424101d01c0d03019100c0e4072100203004d409003044915545810401d5000714000800b105c551038201c000049030703445184050711b40103080e2400006070301d4008080303a400038120020320800c1814040842c0e0040c5e60700b600150305c03111940420540b49070446d100711515405100942c01c240a0020400064110006890581403018903901d040309405c03404890140d00a909034108001144810042e0030045501c02c0480f000402d03201c028402054500c14421020340c00107c00400d01c0d038031442c240c058600180310034a400d010605100c03031091742a0700e005071070710185642c0c5c0c0390203038182c2441c2e00540c41c218030042401e034a4550b60b08006000e0904110f0440d01e010038030768a903400142040a6510210043c2d40740d0301c2d0400e40c44a1240189003124080c0e91007007828411501900321044030031b01192142e1131200c42090300e80360182c508040304c111941400014020489141d9000042d5002c440135441c26070311348 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 155334577 1250 155333327 155333359
    0x2309040605132024040501030f140f041106040b12060d0501060b0406030f021204150b0301020a0519020a0506060f0d1b0f08210309031210090605120c 66
    0x2450102d00800c02e64100d014514040303480c0429001040040d61512075080c1880c09000d210b48400010340c200c044103002c28801d652180d0301c1190402641c401c0041e0500040403880b100030000c90781c45041150000800c02003011000012120b00d03c2a2007480c1800e06150008120f1702500c44001403110030b51001032115900e01441000d45904280200002500c81c1084600c650050107001d0100c0d0800741c42280401861084540c2c40311800c10070420342d04e40356240300034030a1503a0741040300b948515a107219681e0a2000307101d000480e8848641d1241a000c08030426980780303105400350340180660b400800c0011541580c003074422100d48660241078800030360700c0b1542c214094a600300592a030080d003141441d90105450000700501c06241d51030380203640d0303803140004c103140c080d4502e588030b081d036420310000d1900880150b0980741031032860450b03003002020440761003180e0290b0040c03c01c042c0d103180c85034101400c01030b542c986e42c40741c00d11103080d034411100c01c51078080c1c40000112804 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 155335827 1250 155334577 155334601
    0x50703051204030e030c0108010f062102041e0e091216060630080702091009020c0109110607030e1905090f09012a08060a1508012309040605 62
    0x20079188900d120390181054180184001083d42d5903a0186c418000f042160b51301800005040320501503820b03c80505200b412914031030a40e00c10340f580081c00c0e210040341aaa4000342c005824102c5101d204002e410120b020100c2c800c0d400680300010440a00110080110b001800c41260382c1e04d244e51042841038a110074003260602600c41840d1200102e05d500f510003207824120300180302016910036044440e01c0c1030790450350080c910a01045104014144020404d40c8180c000e400c20b100c1d940e40d4882d420590b4004104283c999540795801c13400c00691001014283c2410b4492900f010803d94016012040d4884003c0c800ca50f11310303114050b80381030301d401c0c0064071000d00a211541050440508040c109803141040d650a0000840c0c011425648120b5802d200001680010142803415189c180d8003414440d04240340c6007001c140600480104171300720801d5950202950314011480640c4004150503007036002406000035550f96611540b1034026401000005040d190b03010300c1c81e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 155337077 1250 155335827 155335837
    0x12050c0409020a0804020a0902030601020a06090c0e04080a030c030c140904020c01060b03040b150f0d050c060f040e090604020d0209190504060b0102010b0118060c020609091513091205070305 84
    0xc2100d00004844501a80c0203004d503000303510a17100c001d16a5203030b0341000e0590000300e40f0140180e115200442c08180d0720341140c24018058805c19030180c1d07d9034800001ca01c0100c400740e80301c500015200007503517403501c00c01074010b50901e020003911010b4503005000d0709202192010400c400f055800d40c0d43d503640c0c100d8a000e54440b000b0007220b50b40d2881550390390812142070741c07020011000076000c42c40d0f043c11950900001401c0d143e96141250401440940004040d40c051081e03e40c00c0c01c4640315031000740140c505070000551a10715200b817201c003180008080c00986d030407040c10b002c0140c4800c1074103100c50754104c0d416480d0f0754a504260000d030718800c1540504605050a110502905502c9207802c0c0070b083e402030002c0c151500054407001071290707292004c232002110403c04140314007140015988024181ca141c10501c000082c3c1c1c03081c003912070725084001020705c40080d26043d240c009002d00c00740700c14005110161115115a40c41d040004240240025600700b014856001c43d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 155338327 1250 155337077 155337089
    0x13050c090603190c1503051f15080901090c0e1501140304020607241e0c0e040203090102040504140a05090a20150703030b0a1a030408071e03080610080712050c04 71
    0xf6a8140340c02d10024080c20050f100940c40c104025845403408e03000c3c041d42c2c0e098a003004031803180308620280407144000000c001c0100e035566810400c00298400841c1070041007140c000521a0a00351521031800303c0b4582224103000b2550021000005208181d903803158044803080c2e00e4441038101480a2007120704a40d03402191800e40102d80102c0383d000047e030f400b0f40c0f48801900b454001c114000c03981c400d174a0740042100c00c8a51400c61030941c005562009003140090f042c260360310302040956518001491600070000c0c00c100c00c00500f440796551010400000f45200310181e00e43d1095440000307070b008103000105218480c0c5490b90f204c0f1104030300906080e1955100d0605004000300851039076544a0703045000d0010f00d40c00b42e02c00c2c840d402000e0003000341c6541c440c0da444030081d5000d000201d0325031040d40541c001c500e40c2103114880082c00b0b9120200c1a00d8500204110382c02226129014882040144120541e118801000e6510b41020014107501c07480982070050245500c24 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 155339577 1250 155338327 155338349
    0x6031504060b03030721120b01020303041410021605010c0309172206180b0901020705090604090b040b091002130306090212010e01020a020f0304152613050c090603190c 74
    0x11b034070800d2084440c0120003070142d660300c11541000c656801aa01840281c1d070040c0d0007440802c0c08100405c480140130f0149030200c0700c8000c842c0d02c201050380c20182004142c04450715079071040c4082030107a20341040d00c600d03040040701083e68408030743c1020080a801c1c1d402000c00c04410384000c485110340301008003d8031243e40c035030352840200840e0b00200d5180316081e20a800080c031030034403015203622810580140005605100500c5040d10004040591040e15911003030042045041014052401802c81040751718010742400e243c009480780891907a8030401005440c170300d1218042c001d8ce9445400862441c1481c0000703100c1d040d2402c507000841d440d0030301400700f041c4150300a02d4000055000c1c1c8000b86254030100da164001c61195070544c119580302080514070505040da04090451740e20000300014001044080d1000c654045c5e81c807003c0141801400300c2000607042d00c03101200c0d16106880d00c900400d072a80703da100056440307090080c04a007000070700040b03800038007150100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 155340827 1250 155339577 155339603
    0x130c05030a060920010906050c010b04050928020d0b09240115050301080601031103030705120a1b1101030c02010b0d050a0b060603040b011203030b0d060b0906031504060b030307 78
    0x404802040b0701e86040b02c0080d06182c4c0b201003910700d0100d00200381c505865a401d290b00e04101a00c0a03070140304841c01955841040b06090354881c4105401400c81070018004100200100071141800f034200480364070190840e1801682c1b0301c0301d00980a0350020944419403660303105a03141140b004403103150400c4003202000060318a07a58141215080c3c0702035050300244001c1550144403e014510064000c0d0006101080102c503040b00202009011a80780402075228141441c0f00094810b980841c001030412183da884921100d070300085a141602105071503440c04005030b501840c041c10315071145032888501d4000e41c851200d150025100d030340041c0851608130344500c98080f08a80d00f140d00404140f0f281081c2043d01c2c0700d1688140018820b03400c10800c201c0b02c0300c203c001201050f8850b42001c0c4681c03558050840f0702032099001089981141e010801e194000812660007a07002c00720100c000702402619541040d04404002451114400070030305500c50307020054000100c000e1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 155342077 1250 155340827 155340833
    0x9010509060409230c09010e0607052b03050106030e0a0605101a040302240403060b1302040816050609010903061104080a0503031803031e0a0912050705070b040e130c05030a 76
    0x1c2160f0350349103600703880c2800c0d9179540b91510701c9020390144180010b80f07480f41c0c0951030604100909185028100700d400080b1008030a40d940102403c1500003000c41300e030311103001a01406000c0c05410755080c103100520b40428800e6031074080c004081c2c1059103c0e00410101c20541a181015203030116260310084807462001c1c40a40c4203200c101d01501c072200e4042c0112041001d40c03040d05002c50307070940c90a807940e25100040c255903150580e1203280600c00c42013080307551005200518843d0007400000b07076903d00241010303100b43e04c03c60154008002d42d0756140c1c2c1c000074010680342d0015000424122103c4004001d0180c1d0300300340100c1c42801040c00c28400000099881200880a04490310303034043c41442c0c5a001c1603035000381c29031142c0d4500322045180e00406511140e2150b000030722101e10b031900031100041111a0340840c0000845c64107100c0144076080103489840d803414545807409100c0c44c000e410062a900503640d030014080301300200016200700600c0000d0442e40044202d007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 155343327 1250 155342077 155342111
    0x1009051908250b0c03160c030b182503062d020712030b01030e010f1d0601030b06010c0f0f060609060503011803050c0c12060a050c0f09010509060409 66
    0x100a020091140039165242e0b0b0780c0b42c0400d68411100400301d10109440c211a01d15242c0142c0c00b540e2081c001031260111000b5082010b42100303000d0300c407080d9000d20714180f0b2002e4402c007502c1c00c95000c16965003589242d0300041c0745900c10b00b10081c0c05142d1904211610540c03032182c0c000501c200d0400c640484181e08620b20300e20301d204040c04840c281700440b08a5000c80c4205d01000f007522003102210340e5000d010b0f40c00cc2d140204107042c041070390b00021000e103003150340d10444c0c1c00c0d40a81d205100c0c02c0211801c050704801601d1140100100d50642d1116604040300402c014100800b00f4400307020802440344640b07106a01044803045201c035482c2850140100d80500c00e07007036240090024aa00c2c050281c03003841041501c200c06412095241161290300810004905101d040f44992003500d80c07031141205d83c601080134040a003404441c040c2600c801400071454000240318028031041c5800032101801d07400d00301640e60308014004a8024000e80c0c1c040b0300c05520300115852404032003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 155344577 1250 155343327 155343329
    0x50d0b15070309050a120b06011704050604110d0206090910030b010b04051c1a04060b0d060b100201061a0703090308040602060a0f1b0c0501020d0c020a1101030b06070210090519 78
    0x251645055151254107005e0540440c0c070600b650074960210400c0441c084080b2182c10000c185418049160b29802c004003031907081d1000c44160b40b04c6010401440019035030154192011140c020213447c0c541c001800d1800352242451041200388042601f2100c20ba1101d4000c6521481c410072940e50b401581c041904140b10f1140600440c0c0003210781180140c0c92090103540c0b14081c1d5012210124000c4240034004108a4400f42e0300c3c0140c038801c3d6a81984003840c0c500c101400320780d030b110081c00d00290a44004580095a0401905001125000308040c40c199000051540c0759a01403c00300c900d810642c0c0041c10a00c00042e010407844e40c04181c11303200382d48407001400350300740c01d000f0501140c0d01e03070018034400d0300341400e104502403042882d045107501840001d0b00b445800d401a100316002c08000101580c0000c2e240810800c8805c108a5008003d003420403c01c882c040c085116403088001c020310600c03901d07207411481030145113580040c1001a01d040c0c0c075503690740700741c070034011207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 155345827 1250 155344577 155344583
    0x12703060905150903040f03080a09210623040311030904050403090806180619020c0f03030124050a0c060f0603080c01141306020a0210020f03010504050106020a12050d0b1507 77
    0x103000207038130f00030000841d002c640c480c0301c00340b0b20a89036072070713400482c0c0152403400308004000d100081c5404480580c2204145086031071540003400d0714101d400c0f00c40b5120710500c080c1c0c40141e0b889050500401841d44030381c140c1000d03d4024102e00780641544114540c0b9603020749004103000515071303c80e40603002d4603402e40c206e4103035440c0c84001c4503810741182800100e80c0d0142c0002000c510b400042950341e0025241c003d030070401c0d00304800c3c0c1410711250380e02d28a9800440100403a0080c84d204541590b12040c824181103030703202000f0018031070766800000b845402d0b005075041101540c8407500329134400004102d91502c038a0940c2d250740c80106450050340c2015810700c01c4000d5030711683d02400000501500f0380d13500c1c3d03990b10301a4000d46c2d1500f0035401060f106255080450004208002c0901e180315036a40c1003500308000c58406030060070440d401031941400181c5a0b010140600886041407a02ca801e40781e0f039400917048210041d5001000b000e48401d0406500000d0402c80344 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 155347077 1250 155345827 155345863
    0x3020f010309020f01030e03091f020d171609050306270c0306010317120a060602070605190309170c010203061813080a12110a110c012703060905 64
    0x60040011416540810780103907025002da0940c0415601a91003080c1001c01e24003a6414a550031300000c0d0403a00107000e401c1d21009081d80c42002941c1400806010351203030a20803000c188810f508203122000820040d405140c104103d680c280c0102e4462004201c01412140149802100802c031050a00340c04091100c14044040c282d91001c6581031545001a00408490f0302c6d5464103203501000d0040c0020004042120315103ca5454200344e1042c202d8480105220b450200000d180c41401e40c0302c2c0080000502c0740c2141d916544a40b13041c446090f1401154040c0d044c20101e10308028650003400d07042c40060aa5031405064002e075118120460300448144d1015410701105c201c215003000e0280c40350350a40d00061144405050b280d012480c041d090810003048840c100c400e50480c4600d100c82c0815441c100543c0580803440054a081c0034021a07903846c4006002d84810804000310425000603491101070b501800000440d0001c10501174000103060081d111030000b82246030400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 155348327 1250 155347077 155347099
    0x20a030303140123090a11030103051609020a05092206060c020a080c03120a02150c1215101202090931030e010f0e0907020f010b01031b0c0213020304050105010302 72
    0x42034146042c1001a000c0c130764035072081442030070004c00c0c202c020001d80106549400d403a07204001c900c05107018611401c000c1c0314440100300070100e1110107900c00c0300701600402c540705219501900b9510941826145000c1081382403e42c0511a042030540c403020600c1c1c030350001001075210000445031802902c00c100165100c150301c036101d03203a106246406900400202a681c094a801056030305c80c0c0f48180c034094404880840c44000c5c1c123460070151000c000c1030400c40c004400c203480b07412400f8102400d0354400b00e0070210780d03060a030055000a10100c03540c8051440d8460f0111140c4100007030030b19450386080d04280110304d03010001101014500682111010f440360010000a40c160311440201855980112143d080221103a0200030080c0400243c41d00c540002074014141038001d07240d1899040041400c4504190344a4101821b1400ca0094109420302c010907803009440d103900c04142c0c0c0d00101d001c00e0345140c11a04003500c00810403040c400c0641c0702070b060700e01c00c0312250051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 155349577 1250 155348327 155348339
    0x40f020702060301060806061306030209211b2209050c010f02060103080d060e07031b0207030201050f0a021216051c0518040b100e191d0a09020a0303031401 69
    0xd005418000350031503030410040c0142d03801122100c1d0302484c001d081500d001c1c1e04c0e500110840c160b5038060800300f0740110303200c01703c0e161102081151f0400c0c0b0140d410050700700070300c05645544042409a44620412581001d43c84549445050000080901d502e602070943e4520003405508419035590203035011210b2258408c414400603005264000c000e56401c41e201e02d50030340d220b6029081c0140ea560800224000c0321a03015108504507280001c1001e6800300c01940800c3c1c0600120031500004000e00041c0c0e002415201e801d0701e000d16840c0c07030f11b01030b0344280c0c5003550003044d6511300303600403411311900c40c00c0c04488013040380b007031054400119525110740310442c2e80c440c07000d0100c0c0040c0940403003001d0001e1000340ca050700410220740a035144c00418088440d020324400040c50a4100604d24101040e40742c11800d2a181d4901800d032070304007503444401d80d103a803040711062240041842008650088000c440e0020414450155245405001800c0c00c050070403a81c0d034460000100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 155350827 1250 155349577 155349581
    0x10080f09070609090507050d0e011a1210050402030316050f070605120103110a031b0f050d050d05031e0c0705010e01050c090f060d020403080a020f1b0f0d020904080306040f 76
    0x403204143c42d012034960410700072030060100100b80100b040018421400051041d004005c44005002c000003144017401041d0803c40303c117a003032070340030f04824680006040c00000c1c0ca52950a568500000c075a21140b0001307045100b440740c602585080f00b1451014800042038420030190900301300c0381125aa1442507405c0d00448600f809007040e504d0040000c50425444070b040540010900314142e03803642c0d503031808242c41c1c03ea002008039002c0418001d070401740304180050981211511800c075120394505a591113000d11040400c400400469a108580f86100c0d0b44030301c080d07042c0d0b240c6150000400300541c203c2001aa020360070000d11400c1c0e40d106104160207141c02e0200c44d440c1541090034494199880c50011b600820204042a4041600d01c0034001452140080581c1c480c0d11041c02450310b111f0044801c001d4000b0ba00c4003c8074000c078180200216001e5548400008031880042c101089510000e5000b141c2a42088204082175000b5441445c0c200d600304200802c81d051841 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 155352077 1250 155350827 155350829
    0x605090708060a15120608060a0f020f0702060c1204080303040201090e04020f150f04090c0908120d11070b15030105010b161b0302120102070c0e09100c0e10080f0907 73
    0x280110b15801d041c000120000f41c2400004005d003400504650104914401c0704c255a1110035280c000006025024080340265022502014415424101c4030285d0710450302c12444028803500001884d8011854240000c82d04800c080031202e4442d540c8014082e00d9a004440c102d0004564020205a401040b01040c1c001c41d000352514610380038010a10a4026851081e80100c000070b014011850900e0002003001e0010544041790704003d089024000030442d41111400d03400c2250b2031040710701003c058034080e00626030003084e96006061440414803d0560140402c0c00700303002c0100018017100d4040c160941940208440d070b07030b520a00303a224002e54440020200c0d451715000b01181e40600d511201e90540004030084656a5000800850b40072a51200f917035000315404042c03003080d044820042c00301042645291818681c090b85405050303148010241d91003013030140d0383c1e11039001e602d0143c030042e001c2820b58000000123000316108888003c04c200d0b0300720000c1c01492004c91000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 155353327 1250 155352077 155352079
    0x6140708060f03030d11040f09020906071104110a1710140909160f091802012001290a080109030e011b08040b0901120b10180506030703060509070806 66
    0x1000c075101e0004010909941c100301070b074548410311420158040500c15404a00220814917035501d107440070f4000514190380c4054021881800100754940300c0c807044039421039200d40c07110240f40020001800a06c02140d0022080350f011500c01c9200350001007008030840c440d881c031441c40d615411140c0c1c11101c503024000b02601c0c140240c21a0b42000c03c0d129400c800040e0941d00407448080c401d6004160740e60141c03040c0c444200d009c224801d414072071704015800e0b0445109840c0440c5d00060080480c030710709500a241d10328402c254400c002c0d440290242e110a00384681e0f0801d41b540241c0c14610b0000e2103114484813100001d1304141486400302c0c0503410744a05105941560040d03a0a128503001d0500310b40902c910000001c1e0024000c20181c0040583d04e40c4035101800014120941e00318030765600c920703203607141c56296079850200410f42d01c10300c1c00101e020300f5200c00d00442c1c41e0551100380c0142002c814800e210790160040415208161601809981c40d080300f140c0e07200d0140c4140e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 155354577 1250 155353327 155353337
    0x30d020705040f090b0a02191d010c21090503100212041101120c05120702030c0703060f02040b0403050c090619050103020a033c0603051e0c060403050a061407 70
    0x200860704090300010440074501c480080c1e4584140c45810f2405c0c400c80d0079a2905c0d90001e03039013620894a0080948294883ca0138000e40c0200426000b132102d0f5070300040c3c0c140a007400314001002000c441e807041e00c030801c8040c44580013007010050010441801024880e00549039040b00b48141803003a02d0001903101089038075511070b9140c0d010317140da481009604005000d48400030100035401044074a2225650712640c4078210ba0781e001001801401000031034008002c1007090714000245113055a0b04400c00050713090003080100000c2c440d690161860b1000850000140400441d000701801001d49540c0d10990310b01c0c04002c400720a80071503554014000c40e003400594841c0d0b001d40704000b41401d000803030b07030741140034014a00324900c134240352a03400640c44440c00310450009102000a0780048c032086055a90355500da541505110800c01c43d0848100b0b01200200072800c0e80f40d0001d017100355030343e81b2410034170385800d0070050a0301c1c4103080280c1c1c480303082002065944910125558 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 155355827 1250 155354577 155354579
    0x6040b070f0c08071103030301060905190e0a0c0908100e0601141c0515010b0a02010e030f091e041409120a0e011206090203091b0906010e010f03110d0207060b030d0207 74
    0x10b8030f40c9500224003c0c1e03091045c1241c8050543c80c1000114064881c40e1a490091403038002002401c0b0342c1d0640c01031aa101c202c108014904850403c5900b00582000c0420099588a07040310710403000e6203c49558410035102c0b030402100c503803140da505030359002621002c3c4c2c0c0f90380c020070b9000702c1041099000351a685070200150081961001f442d4442c005803500d200014171514084602070b08107070280140002c2000d000f580903c65004604140c030065800c040000d80e9503a51401040c070503a0052681e0b000d41c1540d40580707141080d0008000704208040c6440311100c10b1a5082219802c034140304440500c1004890441954030403401c41c2e984190034070001004441c00005441c4200e200e9403500c03000b045c03810780760024520940406005005144c0b00418002c4140d141100d4a4003441c4a0002e2200590740002400c003029400c0c2008030380d61055100c110014581a22210840b2501190580140c40301d03400a082050184205003c084442810151a502001d060340003603800300344 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 155357077 1250 155355827 155355833
    0x120510050405071a0408010504060e06090d090504020c10050a0504021c170a02010e0109060e010b01051801141b01050114040e0d03110d060b0403030305010b0f12131406040b070f0c 79
    0xc1c06049082d44142011705051303503909131a094442c00e0307604071600c1d5111113582d070000f40100205503000300d5103c01030400b145080c00241c0712000c14010340d4022500003e242040a104011403c04080a180f08020350328154a08030020b1409641c124440c1c449405003500c000101c1500d07806264114410ba010070400c035620090310b0b484400c2e410195500c480088800e00000c0c8280c040c018051130010440010325040c150031565082209414080103101221000c00f124440c161484002e082c104000b0300ba03145580201d000e04280c850188400110403034022206400260403a81c004034500800c81200c410402602c65000d5501e007140c0c840009401854400c1c0c2001e2401c0209508062414030b01c1a440800d555076608011480a000602041059414803c050041078080b442030304040c1074629401052040078801e0790090421800302c0d00198044d5119441140d0001c0856118040341c589151550130445055034404d0100300010929401180b07100308008856958050801c2556 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 155358327 1250 155357077 155357099
    0x2a07081b010c0f02030f0a0c05060703050f0705011d070312030e03030a09150f051803190c02061201121202030901020d050708192a02010c032003030112051005040507 73
    0x81d500f40c900c000b201c455100903031402d018001312803403402c0103859440d4481c20700082c01707040c5034021350050508001700e001003680b000c26114200c0024040719900e11711420700c1c0b405010010540d00c480d01c076255452a40303210019074a0300701c1e48031301054004070307944840960440c0e2840b40c40014580003000013500c0c106065000c000d419100d024401d8a4102e118901e03411217450701d947c00c181690310300070300942c20401c0d9614241042050011807030708c5000001051030000714804d107014031614803030a80841d41c80d40165559030840700c400d11740c13030340c0e440140301104c20680100b980c036000c607000304443c11440402120000841a001030070100021201124150300c80340050740c0b0480c00341302186207100e0500c2d4280044085075180342c00b00102444514090440002c2100700c00500da0004c001070741c02c040d4010546805041003400054060072096111094240c0314155000010004c1070005c04100128505400740d812260314208444200003220010380d405040c0d50303c401d0003040100c0307840c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 155359577 1250 155358327 155358347
    0x703030501090b060d0b2b020906030c010f08070318030507020f0109030c12030c060905010615020601061e020c0927010203010308040306050402011e080106140306010e01142a07081b01 81
    0x5d0140f6402015900da07124519a04287e043c0100328168404000c2d49400c0c1c1106402031021006042410350107400640800c0d01c0015407811f2181d20000500128003079408007050780500010000700f10310501e401041d039030016000301d1148118540445044d482214441b0039640e02800d9115035908140050f118480040412010803460a04010000341076000320701103188181c0004c00c00300e04100e00300303602c1c06503c1030160465000c0c0e0010050594404d41803007a015142c60080395540c1e04a40c124109072a0300c0d011a003241101d400d121f010342040750741d080c541c1c0948500140c0e43c4001c1140754240c1c0701c20710001e01903003418001400480c242d039121580140c814105506101e81148184900d80b200d802c8002c00310741254010081d090708140006003072582642e120f440c52a0040c00a402520703038080302410468204e004900c50f4044c803013102c81c0040c0002141c5450019103071a00300038118034490a495000d186030002d80300600007040c038450440b00c0d948081d00c03500e8070300458003040a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 155360827 1250 155359577 155359579
    0x5060a061202041d04060506100e0103050c160b0601020d09030b01090c03020c120406021002190e1201020f21330907170f070e240a02030703030501090b060d0b 70
    0x2081000080b0f003a41850f070851130942c40486a4800d00d01424100112080113003102e0041005406421801da80b1154007111007034242070002d10f503220f01c6034640c158016808880e0a2020042c000c0d424001382a0b280d40c8501402d0742104d038500660801111481014170005013541039080040c0070141c020380040e40d031303545503207030040c20702c0030f4600b10750314082140f00071610501000074203010f00c542c1803001b0b0700342c0d1101006c10b500d001415030344c8840352085040c0c90000c00000440c000720a41d00e508460034000c41c080c000b5902c4107110f080c0012654411828421254071501040d001104003a006e5403050404e05991a0445501444800360714240d00e131481068003201e003038940e555118007a40e802050b950307a9a0420400f259032a402c0040003034220a6140e80040402c041d00c0e9110403074004401c001e41d03820540c44080c01d46082840f8006c102e525040e1804030b00d180729541c2c004003400c0654000c1e9000d00c147d0740d030740c0d030312104036a0b00010f001d42100707040004803c00840c540000d020703018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 155362077 1250 155360827 155360831
    0x40614150d0e03220f1d061302181201061a130305070f1d0906011a0c0a030203220b07060e0f01050403120f02090315060d0c06090f0905060a0612 64
    0x30703503400d58505681c800b0b40b0498030f1383d1184189403032280415484034080c0203540c02058441781404045102c44103028911240d10741c0e4500000d040341c440c01041004104403060554841c0104814404210030011150340111056403602414401c14003400e01111000c03404c00044100c401c0303500a00340e0044c4810300490103515400400507804001c0c040c01054103c1d42d01d1480c034241481084408091008040c601030b5501c288032241c080494080d0440d10000d10348180c1542c60036040000b409681d80c800c110f40035500b0410140768003c00105042c0584421011406c6807c40d80020108400e006444603890180303c800006011b07544120318455001c0121600004075070905170a40c0c0d4100e800710005200d148401115491a0107440301c4510095000d6041c480c0c40c030042682d8048203003114508080b031001290382c1e034603400e104041031034104505070a000d0302e40c64058402d5004d4454041072294185002411841a201d2140580b0000f00f00f040070f0340ca002000c8a001165100100c9203d1b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 155363327 1250 155362077 155362091
    0x30904050a1d011b03090206040b03040506060f030d0206010605030a0612050303180703030c1506170a060f0204050d17120103061515020307020d06062607080106050604120c0302090a0b040614150d 86
    0x2c0340b4ac007540c8640e200f02c1c000c0c030f014540801446006224503103118029842a44042c080d070b034001c1b801c14107481103458241e480c1c0e0781e05080f04010313040f07540c080040303100d845410006007c0044015032060310501d80e440c0018515084c02070741d414441c800680000c01e450b0400d000100880468015510401000b1034507640762072031061102c51151010ad03642c2c0c04442038200304421402288882259984110304040c0340002064080300080030040540391081580c0c101180c0800a60b0801d090391030402003690303144c1c0f80440080c510f60b0341029000192000c00501c90f010700c5900c001001040d07018608040d810340c00d01c90345030003107803017200c429407034580c0411000c50035001100c10740e400720a82c5241c0c002c1d0f001c80034108200ca40002c071460341869410300403501d643d000c0318203c03004040e4400300c420240c108601c0c84401c41d08000d40c0403000d0424060494155041040416801c560811040d5540c199218190045085150b0401d00c80b9002c00303509070700c2d84080d000303c40c2d12200c00301d814 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 155364577 1250 155363327 155363339
    0x3040501090c090c0801080319030905070305010c05040608010b040303091403010e01050705070209180a02010c03050706020a0503151f121e0608060903130e040203030904050a1d011b0309020604 85
    0x30b0301c81c0d0000010345a0703c4504250b01070703015002d01d00512000c0d002c0c0d0301e0f050901c0108205942c1002192040c9038403504014104581041410021a000002040700c1c0341101c000401c80c4c3e11501c42c4000040340c800020609852540444003181d51607110740150f140b0301403520000210a800880c0d05560b04c09566004100038040c05200d07824507580c903a9502c40034410030940c000f000c1e00081070088a04d0607403841500c0040e0501c215502402d0503d01e40501d03241c126140d106030b06004050900114299009030b4100d0091030050107024001800858a042403040c2410007162542201d050121420200303400340241c01c101400c0c000002c500500001795048000049001e00b032103c59544004102d9a6000d00c2055048074405d0041d518040030500d02070404017081c05030000c8241003c01050444d9000c10450300c800c040608140002e01d02945040f0090481c2e0303a0131280d01201c11018030503140d041c404c02c0164490034184d8400801030940480082044a00881c0c00040401c008519 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 155365827 1250 155364577 155364593
    0x30204180c0602030309010c09030221071e1706061003020c10020309030304030305060307060903120314160206010503011401090504030c0f060c2d0305190608011a0105041a0304050109 81
    0x24240310b4005654031b05100050508580d91044100c007000320b01d030303400d00050740c031501850b0140603c0e50001400203441d0031080d042c1909a80000c0b444105d806c110b050f1a03c1c002030000c1200c81c0300818403810b040481046803510300885109500c605000081a00c8501a6000e0994504a10201c0350110038000030107049a0058070340c1140c0c1d51001c01000201341e494000d240c0d000e1015000344c4020b40c60f1035000f0740441000e0200a05042c0480345d01c40c2c1151003030784000481c1d44800320001c21400c210b403d04552110111010005015031000070441d130505020b02000607000d030b00250365503032905400c0001098054021000c101041c05240701058014540303c2646028480000d10070001005c007428003116514698254690070303410003211001105000100302d184d0402061030741d100f100b0034a0350f00040d00c8020203d0320f031000126032560158046c850541d403400c220364125030002c1c01562280618490080b45008070740c44220b00500f00805181c215100c1d20012a081c26551350340b41c0c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 155367077 1250 155365827 155365829
    0x3020f010f17220305070b0612150a15120201030e1204050f040e0706081014150903070f0609031a061c030e060d0209040f29010908070e0906010915030204180c 70
    0x140b0085140c01c18014030187c90f0782c1100c07046900500c020021214a6100d5154170342422680401d40001041c84c070703a80d002201031424613440c5040b00391b00c070180c1080300119610244c3c001783c94580041801c89d0000703424150152401103047c141450101041511904c42111540040d03d900900ca5916000c22991010385456210101545010400340c40c84c80e00c0c0d503108680031800d0b00c3c00001075458a0218843c01200815020794138118080031a1401649a00280d42c40c041c0e14030000340903501ca0b0000c0c0541b84140e03204400321003160681002c403481603501c250b0081d221000d4058940c42c118400d074889209003445107a07129540006510b43d082004202c4c6540c1c2c0000b142c0b495407909100c0c10a501c0c075034180420550f000d0940c03061010501b002d03c0c5650350000c0e0b410b61403aa0203102c81500401401040b0781407a601e8443c10240b002064550943c0d61250300c0000c100790440380140a11210b9504080400a2030350302084090198070b001c2d1070440240303030350380408612454a150 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 155368327 1250 155367077 155367083
    0xa020f130e061006120203190203180706021c031506110f0102040603060609051c0605100e0a020403020307060c0b0a0209060708180102101a0d020301230103020f010f1722 75
    0x10f100380381c14006002500c21408208905104008200381d00d401c0f1480c907001c21070308200060710380e0381d11003401501d001c144080810364420100c0c0024070981c0000c040604100809010410540d48041601035507008000d0030154244100c00f40030041c0f02d08940c10b0100074980841d0b82c00e03901042e50b00c0c2264440d0b000400081d4907500203004094000d840c5500420007500e101d00c3d0102e0402110301c804c204960018030454a40010412915854540340081c01111400072800c1c101015160000d600c44e00c000c0707002c0d00441d030001a910380950340c080d031095080704c04903605603100e01c012402980483c3d249607100e04140144004142150050840d10181240310103c6451480c006880e00c02c0c25004000340314180800020102080c40700036003051000d0721710a02c0344840384002805003032468505d5296140495400b90241a4103a08030f040700d00a56144e410b52040000444034100703100708100114038851141d8460010b50101c0c95807256a4400d01c800007030050b101550100d011800035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 155369577 1250 155368327 155368351
    0x6050901120f17090414010501020a06200d1a0a06050307030e190302030307140906090d08041707181401050f0a09021b101422060c080412020a020f130e06 68
    0x4c3d20280c2418401e0084001010b800c40310607614220000b996466590401401c16880759070b0f10382c00e4160640c0c4114105a034001c0b0b41d40303072591840c42a008103201c001005442940d00c0092040d410006c1f030385016185140c0d00c00746580e482d40310035006040d0b0703081c408140d0f200d1500c191070807184940409142601c664065580e0341441c590042c40784070010740000d60100c0420214802d50341d080111a50b04e1000d542c0d07100c901485017005903c5014a074004280c1120080c0b505240700008501700c4191085110481c480b44101c10860341160100780b4540400c01c400c8006004500c2c01001ca82d0b11000700520a030000c4d0707103507041d08003a60403c5160036185040c075941e0f540307092424828142180c003542c0c410052034503504d21088400d04064a09a101410100b4882060b901d064400d0141c41d00318a00b4084085010401001e0000803181074071400030400715206010300c04280e40b6886070300100318440b07001141c420001e41510240440b050543d4a14141d0742c017040500c03030320703200b130000c4092 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 155370827 1250 155369577 155369587
    0x40f03060c03150e070c051f0204060807020a031b052a0f0f03032b0c050909072d020f0f0610060f05040b16060f0b1306050901120f17 59
    0x809000d5628100e00d0000b24180f48100340003280c1000700ba640e105c4183e251603842d024882c2080c0342030120703a07140e40b00c010202040c08150140c00d60000c00440d03101e82c0d0740d40f070a42e540743e5080344c40d00300700c0100138000780034000603241c1080c0c0c0c880100380c0c250033802640c1b0410b030426003189da1810140740001c60340030800380f072070014a44662002e05020040e66010610071090340001d403070f0700c11504089071282003440400600b041d8044000441e403910181008805074540014240e40c106100d1284031307010400008100c14414416403180503480303200800e0a01d4014042c01c00810506d070031404511515416100f000b204006600d60f0103a900040e064500b0030240c0c40710007000e160407c100748103611070a0307810b0642c42021181141c40800e5503540b20f0018820b01d0104001e0810042c084505001074550440b8460b4440342050720304071a0280c44009459030070099130301c58481d480d400b2078420010000c0d580d508026940f8a4880c003031a040781c4000380c0d65200b006150b904050f40039100814 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 155372077 1250 155370827 155370851
    0xc1a04150506040204030f0f03020c090408130504060b2706071a0105010318060504080708120a0e0d020a0605041104020c03030403020606060301140607021801080f100b06071403040f0306 82
    0x10440707400ca0001c0e20f0a519050450301c6031000ea10b8040d0004154981142055042c54803c1c4020b0300545401171001c09181094181100e841d000f01e44500c600103801d40740014140b9040c801d100864018403140c03400c03c51480b82400035031b030ba041609442800080003405450380c40700c3c000d15925219080d480c0d0200c80e1000c0c07445003924144c2102d03042c98a0603940c051618545a0f011012640c0450040303140c0e0f0700d91804a046000e28007008280360380126a140404070410603030b80c41020ba12508111a4044808a6170785000c4041da580168001d40d00040100341e8a07004140c0c028000c141203551403900c000400c0c1207038404e80304551260000300c103000030540e06014841e0000400c603015400c40d4100b400b42150100c91812140c481d403070000c5c4020840d11110940b075410500450600398a41e940c90303441d41c41c1d448100740c06540307008944c403040071103500d88149107426901411982c2030560035643c0c910010114690000c2500c030a201c0015200c06105120000e58400c003004508959008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 155373327 1250 155372077 155372081
    0x5070302120f060f060c150f0402030d0206040c1509030206041e090902151c3b060604020f0d2306040506010c03051602210d05040602060105010c1a0415 67
    0xd8401034810010b02c0a102940c0d80301401419801d0b8125511942c40d182140c09614284095106d0010101000200000f001b0209240c501c61402076080e904c280702c81d040202e03100d030342c01c507001818410072130002c0c000d0b103901d01004c440c504458280300340100d031a900018038640055200000410901044851401d42014214000d00001d4001e001c03d4055900041441102c202d08010880000c601506074a048013269800740007000802c100d4440f000d00f80e40c0f0407030010300070345c012880c031744c0b80b092800749640300305030310714459003000c0c04080c2c55032010400650b001c41d0802c00c04600600080d000c80a1070702c900085162148045901c20518a001005902d03000300480d10452400c070411005e643c000d1880316141b0751614040c0e0f42c0380e000d4010180c0700100100c010307400815450010840c00441000d62003441042000c0368145562400e0840c0d45125500070000140c02c10f5004012550003401c0c50301040307100301c004007000d00304980c94034641c1c8012034054480154140c0c00154821042c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 155374577 1250 155373327 155373331
    0x10305030703021203010f060804060204051c02030f030a021023190c1407020d020a09060314010b030d20030f0d02031e070c1e0507180614010c0609050c03010507030212 74
    0x10384d0403030039585442c2c80c4198034191407090805210f20140050200281613040b1805800e0003440740c403000b030701410001000c0000e52812401392003060728040303034140300100f07503140800300e40d0041004800c103180e0782000d42004903ea00788265614492804041605441442845004403080354294410b04100549180d00050418130100c1c0c1c005200406640d001c0b29901501503460708112211440840c0c0200703010390207600300320b103001008802c000051640d9090340264500038402707201c4000800d0f4030f6622043c01c1a000c28403158180700c2c00300d84080a140d6002c2d03c6415a811b0400480302c4a04640c081e400f54401c03a81d00008022604032480e84030341407101c0407840f50b5000e160904014040300009034001d011102d403030010100c078000c2c0346140d4202035400700c10ba50342c142d44d038064507981c00203c02d610728000d414441c0200301d04001c8600503a083e00d0580d11101c041c40591680b8005000141d41502e0f10302440d465510345440074061540104150307940103370743d04040740040d0401000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 155375827 1250 155374577 155374603
    0x40e01181205030112140c120c01030b040b0307051c0209180f120f07050a020d032003070b01060e0409020312090a0e060a050613150e040c1112030a1401030503070302 73
    0x14801807117a105590480300d001a03010018040101584680a140c287c0400c58140d00c44814a4100b1030014003050340082582c00782c0b42071012040c400208020344412002e05501a40120300410240c0b4122946100d116014034804450140540109400700c10448903651a201e00d10842240244200011210814542d010702250150080c0c0044241b083c0d0401488401001c9600c034144101802440c544641c0100101c0c0030504a1038090a59545d4004a46807050144441c9149001c040100c6004651003110321200d81c1c20410190348089280c114140c01c5a83e4211801c0140c41c01c0082076150850b10f60850317240c070310f1301d0304102c0c0405481d04a00c40364002c80c0c0a010301c1d9142d4045c84001c3d240100ea042d516824a81c2d030403160078055500c880c0c0c24107c2028041c803402e03008032042048040c1950148940310004105a0300f81c1111000800154071041d000f500102802e4043c1d034025443d984c002c5000b40200401d02180c081c00e800c2a40c254100080810406404001590388110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 155377077 1250 155375827 155375837
    0x905040b0f0426040e01090f1508030a050d0e100509010b06041a031e010605070c0b03070e0409151113050108040305070605090c0a080c0a081b040b040e011812 70
    0x5095900c007514203895031215100c0f80403d28400c80042e0051040d10040d05d174500c84800c103507966801c500302428084158603d500c0c80c2c10b1031080061880e0040304c0550786204011450144e484030102e03141ea03c20303040044295036640c81d01000d070005228095040045d90000b0a441c100380c1c4010f82110200d50f8860300c240c004200030001c078031504a8181d558603104104584130b03502d00c1400b4550240028030100b01c40e03517642c0046101c80c0c102024010301e07070061080010941e01c2d003101e8402444180d48138000f141540203001c03c50724080d084200024805c0c0c6243d5041407100b44240155900842c91301540308001c2000c000c075017050025800100400d01c1d00f00b0040c2044e44018000348103014000e0a696240d50000e2142141080b8031401000d001c1d09401141c0c2d95a40e41949810417000304a01c139004054002841703506c0010004243d010302d80f003d1800e03c035a0400c002c014110720342c9a58009440e02c51980c01c030381d022711840c0c00050140c03211a800c00980c0c54121014802282c003601840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 155378327 1250 155377077 155377081
    0x3020f12070906110d0c020f0d05060702060a020301030b060d051606020a030305061905090907080a03080a0c03061401030b030a080d0203010e0a0618180c152d05220905040b0f 77
    0xa0006aa0708204220308100e00c4d8406d031400401e080c45241c48005401000c110190001c0020000705144900f29540c203403000760b143c0140b480168402844081c00a120070004200b003843d090740d1500160b4450800c03035810491003e0500801c2c04180c2c020005a0030082448007856014000d0b164048001c0b580c413400b030110b14003e03000030313039241c0101401008000c00050002204001c60740140c0441c404903940d80041d4500200004801c88210352501d041410303078908035001e07008080544200c8a01c1d00310000560740110018513182c091990f16200b0b8040020110707140f80c00404508001c410f001da601d6040c42110391400320085d10711a201d51a201081005500c045a82c0407132400044020818002c240c03402c0d070411070b80c10703800f42c0b03108068400080d0000d42508072449107401501e542e00100700390b403030f0391800c4210421860320410f414000c880d00705104070000c141824000000310741a605d1540002d061005940100c501075941d034040c4800c0c040007403070442c0c0c40341140c0c0700c44c0214 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 155379577 1250 155378327 155378357
    0x1050c030304030f180e0103151a0906060d050a0207020a06140708030604270c080f0a1b080d0201090218192a03050a05010608060d1203020f12070906 66
    0xd00c401803020f003c001c40c04450303d04041c031440c0070212000008540410762500e036081d04084803030038482100c0d001202e10100019054901628107041d00448108050a26000501c010910010060340c2d0107a8100b01c89030042e80c1900c00c850143d40500001030300c4801c0d0344148000c0030703125040181488480c00015000c815654216040030f503120f2000c580b603403100404134001d45003c0002202c003100c3c032900321142c40070161010360100d00850281d4203141c0c2d941003545c4c4134840190903040c0c03a00060b58400118644d81d400342040b0704602200c0e840c2681c2c5004c61824a4030702c404c000b0050351a80035003025460100080e040c0140c5c400704c80340060030aa00c44002104c80d411060300e6140d29078600c10b0f032404070b44100d0781c0c13000310720303181d0180d42c1c214850000c0007090106c40c0d01032200d00d400004100e00b8820a116440354078050860202c0d50340545540b0b0038118011034910130150200001460000e149000d07104c408140010804107042035980609034004030b405c01c00800039142103141d0700b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 155380827 1250 155379577 155379583
    0x4090b0a0e09030417030f1c061e0e0c090904080a021506100c02010306030b0c1b0708031c060f060504080c030c030d030c0e0d08040e0a020304021818060903030a060501050c 76
    0x211240801e85c1c10081d003030a0444d608501446c0391421803171401098040900030b6500a14100d6121340d00704100440e00c071040100d0050310134023100d4006c8a1100280402852108000e0300054461003c40c00c0115850000b811080202ca08561240011035007079545034040140000c81348044d44ca003001481d203500418118122100998200140f40c001d580075079009601c03060281d500500c20522602d40b1030030482c020703801841a800340150321200c01a10441c08138140050b43c18400241d880c0600c0ca50b114551403182981c0d034000142c0d0b4041c0050445401c1202e680200303041d03113030309807074510f032201281c1000c1c1d000c40700c0b5000e41c101084580882c0d5010500348100000e5040018644850410859540610118541d080354508292034284400710000c2c00495541002d0100e83c0e43c0c400842000ba0301056030001d41007803104130104180c81c03500300c403998000c800072808007581d507045040e1490f000054410950541000080c840a07203258011040900001e003006072a0041008045a07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 155382077 1250 155380827 155380829
    0x2071703090c0f18091b01170114271503010903090501051804020714070b0f0313080d09060501081e030301031103031c0506030d030e03031b0f04090b0a0e090304 71
    0x8401c00103c000340b012655107000e024207138004500d407110107207000b288659640200051400707402c140c500d443d244640c81400f00c00e2542100810b190302c680d1810340c543c41c1003a160101d0b01e900603c0941c0180d2078958105001e0090019000025030a0402c50f84a40c80385503506401806a4100107800c1c01280c3c11161a6088410030b107055661008054000a501040382214a43c054000141d00c4240891440c880408521b08806c0c2c40d1950303511401c280c4207100c3d414010160340f100740001188196203050190030b86015100c0360b46082d500140901c00c580424600300c075016030301d0005001d000410403018142c8403002c49030321604010000280d07a24001480018000e030340741c0d00003042030748062055804180000031507000746412604010060f0401302e0b010707402481001195801684280540e503500850710020314519240e0746040c010000d0b6038090380301100400c05c4015480790201d80200002d000000d00054480701d070788100215405c1d03541c40301c28000e80481c240010b481c0c02004a0b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 155383327 1250 155382077 155382079
    0x6010809010f06080705040f020a09030311030409050a020d0507080705070b090c030a050609010b09010b0d050a06030b010807031403091f0207050a0303110d0f0806040c090509070302071703090c 85
    0x21039a1904201030140c0104008a0041d81c1001c20005a00c1c00000b01c2d1029200c2c116028000c40200700e40403001c038024180c8510014050480800200e4050014900460700e0001a00c2c07400303848079030880036100f050340c1c511001c2d075000440c91f4002c060741c45050307002042480d02c00e22605002e60003d00358020324501801e100c2212002c10301d04882040100d0b50f1041c083c0645101c03989d1400d245445d000101d84048d21942000c000c00d1581c60401e100c1d60684c0c0520f50707020704246804040e0002007000802651000d65140c401001280b0b042c0c1c000c2e40200051001003400c2030035860540b44004078a089071800d41e00900140c070455403683c0b61001042c01900c00e031201c007400944128604030050744443e800c002040740c04000d066100c4407003041a00b49070b0440305c80790564142100d90a681100d5180003411120108200c0d240c0343d00400c64601e694600201c0c644d4807440041c02860301503a180b80440d0f400900300b0100440d01101004075603103050094118500741c010b1907140c0100d58409 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 155384577 1250 155383327 155383337
    0x10c0c0b0714070501180c060905090f190e1b01080f0f06030a0b040614131a06030c03010609020307090b031506030408070f030201091412041206021b1f0b090601 71
    0x142c0c400240c1c0100381c0340c106402c4002400200b202e00d00c6180854201c030402c4d02c10400c00d00002c18180e004079031100c21070b140600920003940d5000000711b04040c0c05084c02812281001c031404041040340500d00c02c0c10380e03035006040d4000a0101c1603030944400792005040c003a0201c1049131445c1e18020082c0e0100002003130b800c8503601e0400090602110072401044000408180028402207a00031010f5496103900c005441e00d0b660100400f101c14a8401080009150410056200103402054104001808840c0720001d074400207802d45000d6007149200c0350380441045030340e680c081303111801070415096061850400c0f50101e2040740c0c80e241c58a02906000011a0130001448102c840781c98219480441d0300c2c502e803400a0207000920340a4811801542180c9410035020030242800341d480e03041645040e150603000e2140c0703070a1401c1554595400c4c0212800701040b074101580302c06d240b602818210800c0410142982c80303810300c0341e81441c41e21602d4034103511717414075040e0005800d0910b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 155385827 1250 155384577 155384597
    0xf01140a02070501090c090203010f0e0105101d2d01050307021216060906050f060915040b030c06130e07030908030402011b0c0b0a14120c030a060b031503010c0c0b07 73
    0x144d001d0500c4071402000c040c807030140051420540d6000d036050310445050b2010913a510084003c0b03465003801285c0d4000140c543c4001072501441000c58044410110442c2c410491170005914802c82e00305001600707800c1d00c2c0c2c034007500e40d00350058650301000d0030101d041d030900c20002546e030000c2280710b001d048000990000c04540320801d280e2401c1d0300039828004403006150080141a00b42c910030001241800442c4040c54101c4480d44148081402ca000e400d04920400000c1c003002c01b0100d400d8007402c1d112542c540c86110050900460400380d9080da645851221219060000d29a01c2010b02c1c240102000071b40d0b00f0100c1e174105070246045080c280030160301010140c00c85100902d048003110000803c0502000030301301060303143e2500c01500b5080d5003151690303c943c8040b0308001011500107040b040c034090181d500564440300c002071140d244d0380002001e50041d00c102600c0c8a009500200914090059200800c1946030004a00707945603140706e110207014041d2403c0c8409030603 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 155387077 1250 155385827 155385833
    0x2012a080a0209030a1112070b090f0a030f1a07080105030601270c08090c15030402010309030212070b040c0512150601020109050303040c050f180c130816080f01140a0207 75
    0x41d01d00603c40102698000c1225180620103800c0e48080607028006c05d42601c02c1e03140010984034101c80900380a14645001041003220b00320946881e01d41c130205440d40400819001004600a14820f0b20116038440014440c82000310001b82901c0401400c2001800a0b48000c1240e42c11528003a0070010200348c0840c9062080001484041441d46440100c10f04254007685043c01030b4082c8083e9481d040d0320b1000d1140c812503888240d00c620004101240042d4442d9101d56a000d0013031040d40ca10b5161080030303000715800707030380c06a41d03020075003081c40144002804014020441203c403c2d41c5003181c840820f07200c280144042c0d000100c0c000016905900079000071312056403020030390341e81c0c1c905490412603089213800f176907000c0c0c20311402107449800c1c42c100314050400d004d1004145a07881d2850b203c240c1e0300110500752038601c10400043c280d481040610400f600e40c0c840d00480509040010745820b00b030000c6001103a04242080007a00c440401060300044080c901596440d0b141c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 155388327 1250 155387077 155387081
    0x70201030506150a0c170c0a14030708030c04080d0c0302060a2a02151305060109090609080301080d02062a070c030b01060206090706032904060302100309020102012a080a 75
    0x41c0606000000080e00850ba80d805805e02401a101c1d04480200c00c001d0121805203010b02e4044800c0c070350080c0e0f07a01020501480c140440181d00b031081b2413506800d0359551780582c00c1aa0400006d22000c103042c401380c0400e016646558903039140503880340c1e821341c5000395115030207007000c080103a4400441103800e051001d0301a8113540d042c9540401840641c00950f1030348905941026440070b003000c20000010507151100b4550420010704d0a40d0908a90030010040910300b01c492070b41d0350740424002000b00c2e024500804015000d0401019004006402c000f00140740d4080c1d801580f00d03114581503c103112600e000c1d600d10400b03171245050f103400a1000b203107400241540110000000e1007580c0013603c10305c10042c0758240c5034243d5540d0401e80c241d414000540800751441302006c50006280501c10246840090000c80d4507550303500802d0030804512400400a034451103c08150f58090084000c200081c807451040300c458094001075810103203000808014021000c62040c00041e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 155389577 1250 155388327 155388349
    0x1091203030935090a03080a0e1801180605060a0309080c1504051e0c01030209011b05010b01091a0a0e01020f070b04050405090d020d18180203090f12070201030506 72
    0x154940e02581c01d040083d01401440301268a4602246405100341e0344140d01a986504000341041402506540c5d90240380d130445488403080044518049401e907450b2340500301110240601c0c140da95041c8001c1034440c40010b090480a181031150400c140d4071076804075500c02e01140f4001426178240d2030091054442c0c08103101c4244180c407009d0300d06440b4541c615010b41c0c403500842d484460309031004500c6001e0141c0c03c55643c0c0080107081660750080d0010040c42e6014500100b040064000c00c8a44d49200907081c3d0780c81c1c0d0f503240002040c1d6088017840c0041e240c1e051442c0120003043c8501d40951141196a00400c0703680350104082d640204070342030f900e06041e0b0584501c6501c52400c3d003c207821502c0703414403440c10070010405840d07012800800c0900c0c0b9a02418688614142c1035500040c00e120024001e080e100d0002030254805242524020b000440036950303042101c919882c00c00340039014099500140b000b4011410f90f030044502065081c20301040b107940304400038811801c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 155390827 1250 155389577 155389583
    0x31306020c010509010b090f0720030307080702070b07110607020103090803010e1f05010c0f14010f0609110a020706030f020d020a02100f05060303070609140313061706010912030309 80
    0xc41c12205000064110621581c0701e040200400305601040260603a42902e5015440c0e1140b030206003070360310030f241080380c0c0c0d580040c121005500e1004024503561003200e041c40000c648805000300c040c4c4c1441010010018644e54500704003507901d4600c040740901c01d01c07034131074000080c40800b1a40a40c0006d40c2c0107030008074560f00c81d80c0d0381c4650385924804454514140c8942c2170407582c0c0c1c0040c070217100c0c20f5901c182e507028410280755983c2065040c0e015401d40b0452590394407600120401d0103000c100307144004000c1103840c6441c0e42c00d41642c405203850f00d4401c0c8184002406181d002902c40202c5441d4500420b40042d11813001c0001d1281010305a41d550000a0036241c817038000924040710b0f103085800b0000180d03c000043c3c101c5005688440d0315400800048011581a821070100301b4015482c4466200290170310a1a50740411681c0b000e141c0b03d43c008200035074116143e0006110004030400251620500007010000c0e00e00440048000740c0c0120410b040c42648000644c9038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 155392077 1250 155390827 155390831
    0xf0903070302190602010c03050408251203140604020a05030c0313051006060e090103080415050408060112020306180309011202070f0b160912112202120604020c1002031306 76
    0x101d800f818001e040e034507000d00c80142d030034502c0d94044ea61191146603c140c2d0001c04141c1850203800c0b0000449984c1179503208543c0d60020450b020520b60105200c058442d61400542c03810105c01102e000760004201c14400c510501000c82d01c0c40e04030f01101da104240c3e10036556a55910f4405a403010480800500302e44a08500d0014201703042c0d2001c2c0668002c1d0300c5814007104224100700003840240001050480e051000700040d0403c0b6030f5500c008035490800a0500d92200055440e10200341d2000e4180000d0b03100c01b0703081d81000d00000c0e400105003c4108405242510200e0352442204002c60400c4541c49148983d851960706a42c1455806038000c5240350003401c04003d854019a1005032030845001d00c011240c0c00340940604030b40b0900e000309200381658907a0a5400c1c20480c0458006200c424844003029107000c00c8401819008001625240590045800300c0c800900d0140a14030400244480003400030b684010003100500c05a0f0325a10b110f1205440c0c809024001c000074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 155393327 1250 155392077 155392099
    0x105041e02030f0f0718150915050d0b040218130f08041e150e0a0b181c030801050f0918010209030a050f061303080414030403080d1406150f0903070302 67
    0x2102103540400c80700c1c0100303041b480b0302c92130982c84125103646501807909400b0603010004039910f40c1211224800040d40b1110485d41c41010a5250074085800c40d00300865004110840c503100344082064080c030010b044442c5401d561103030703020049203005800c02038681101003c1007a00c2040300c002d8482c840522400c1c524039026000d100d22940a010060203148486240f5070744201c08400e1030a5008100f54003843c030700308219245500c000d55140c60b1b40088800c07940640c441e030410b40d50034000061509803131086810020040c200603006144030760020b07820750010b9500c0c1e449407074105c038800030350103041110200d40500a2003410500c40e0940660034412090110105020210001d0390040e2080c669a100c982ca100090091000380840d068202060104c2c403620301071581508801c0c1240d141c141c60381c544120310f800ca04c13054618191900c1559041280000c02c458102c04152040c24100b041d00d0031410b100e0103088194800020041049001d03513604103c0d0300010b5801034490641c0d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 155394577 1250 155393327 155393353
    0xb03040321180b0106050c07091509020f180303030705030c160209090c13050906041403070512030105040b010206070816090b0c160803031303030c020a1b0603060501020105041e02030f 81
    0x4042c81840640354084590300004095026500300c41d50300b2620b5000e000b680707003061080c000030320008000e1410103400c080c0101d00c9400d184000c00d00b049943c5000d03911560180b0408603403070940300d480750082e00b052040c0049150440c0650ba0031034001e00703403241c40e95140b1201420040c036401c0041d40c050394140c1400b074007a00114021940000542c0c40010400c810f0320030354203a4a00344c8150115030b101000243c0403603c0540809080c25420041d81d24029258490519018a2040305101e0450010040109261504c105100d0b801c081c00030b002680791800000e096048e00512100d00703080b69400c02800c0612540446025010765083c2030348540d25464980d40d82d40356040020701141e5011000705a412000003600d108401c00208e1450340e1501da54200c003c2e00624001100b54800e00c1480d40c00030702d600003101c4103002c806015187c40b03450004024161401540303c01d055914080500c0003264011a200d8070780700000880039002d10305840802e192658902501929019100d03001c414 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 155395683 1106 155394577 155394611
    0xc0e01090b1e010804030c140618010911090a09060203180d020f0309060a0909050a0e07051903110f0d210e0102031215030106031103060f010b03040321 67
    0x208140e441c0d1000030000340c00c408d00c1d600101d080000316007200e28103401340320b41203000b441078800588900890070030b07003401e450045541c10300041480c90190404008603921440840d500c2c85c2c030b010756074902d00e60045550810300a502a5a00e40752001413031a146100d200c01451500c100d000400240c0ea1002c42c41009200385c41c500007521010318400c2d24400c4160b00c001040400680c5105401c0803010b40065200781400f4007010302d001400d00107101666030004692988a210f480000c91071500b40095070381c41410300c0f030074204101002000343c61051054180c000302641c031503000d440f4408003082c101d0050b8070900420051030b02009440c0e0b0041d00100401c1802c0580c180404c0c00d6891680040c0d03101140d0412010380da040c10844903a00c401003074440006c950400e54070400d1480080d2000c0c00300001d920303c800c4014040c0721200c000c64807034601041046011003c10341 = true := by decide +kernel

theorem cover : BRFrame.Cov 155215827 155395683 := by
  have h0 := BRFrame.cov_init 155215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 155215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 155215827 ≤ n) (h2 : n < 155395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
