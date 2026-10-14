-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0453
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:53:15.484433+00:00
-- url     : https://prove2.me/submissions/36e160f6-6feb-4246-944e-6c095f81f89a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 81294965 ≤ n < 81474821 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 81296215 1250 81294965 81294973
    0xf0909112106030c120a021306090b040b01210908030a020a0f0305060307151209080c01110c030403060c110706020d14120118150e04020406050306070203160c12110909 74
    0x30355800501407072401c4045e5a000020440385030020304000f035410b03020350003010b0b424001c4400d401542c07099040c0d5801034010849000011f00344002c851010340030070301003400c000c0d110702d5040551780104483c015014010803c0340582ea01c0c039146800a540c41403002d038000c100c0d199419001001c02545c0911444d0030403462400200082d076408092182d504040b1200c0c92038001d140c859a0111514800c0600c180429160341c900f5070050340c00140700340c0035940f82c041c148040e070006900310f07810418100021030030281561a06401001d00141001c14841012012004a01c05201d220000e0865402030454490968006040c05015611070034040c1c00c204040c2d4a5418a0350b005410745401c0784408100320850140480240f014100401d04082141030001c2c030003e800250910882c820390703061080c90394503018990b503100103030341076009070300300b804001001d038049908900e881c0c0c022140ca0300075a980306c0e040000d000021500b13461b540b0080699000c81c0c14400320322508010400000c2c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 81297465 1250 81296215 81296221
    0x25140303070e060d1113050a0b160b060301020c070f030b13080a08040201021f06030213050403050f0901120f05180c1005090604030c0602070e07140a0f09091121 71
    0x24281e68129541c0d42c443e000c04200c603810f41c1e4140c1d002e0400401004a40b940c0c0c1c51740440c260090982d07500c1410b100b1110351038086818010349040e149244d10303042400b140701415a8400d000144010081d0742c0541d070074405092446020000c90b802040200383c1b03e2252829030a1030111341c503004255841170070001041e44005520301e130450320701010614091902e603c0c7d501c0100d0900c0a022a10380d075400411843e503010110540c030500c1143c0c82112440340c1c54150340700050030355000300c90281c0824020702c4084440700715903004000d1a541450000850f90f00144a502150603068491118954460400c0846c0800405c00710b040450100105001e0044d0740014000034030740001041048800308840d05180c8881052360051988001c0f0441010f4032404002d5882a9601c01c400c100940a80030482c0c00740580241407440000c15105d615001c82d000050b205a000d68103480100000703040300051090301ca10501159110f1030321202e0340c80740002c0c1e00410228507100803a030b068524800b4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 81298715 1250 81297465 81297467
    0x1030c0503030f071e08040803120109110405010c03020309090c04080613020901090903030b09040302060402150306090402100221041706060a060c0f08030a0f0e0d09090f022514030307 81
    0x140c6882a50203207010400e0700a09050105e0318480d0640101103034004940403440312000700c003400030000050010711090380e0b40d1060209417542c610706400c01000400040c0055441046050911f900034011030340b0b0841e083c00400c0102504032000c102c0000085800d119403034050142580100051039600e00f41d0040d030b00054051071701840f80e028035580c1c40018004241c000d0304038150b4488000d00c025120300c0c1a04019444803800c48040344a041d5510450a043d8071b0300b41568001da0005c1c003a071440756a60350911542669240180e020362103175914050146480d600c40e040d0880c1103400d0307980c03994940040040c1b0b1044201804056401020800400e911440f44503c101c070224548802c2c07003240ca040c401708224a00b40054000d6200108103c01c242c49500060300716200d00d202002241c1800c0d25640c2c6804d030b1400c0c680000758030b001c010810b8410b04d03040124a690154401461304500701007007403403400864001c00382c0c1240c01782d840c0240000a50300c00f8031801494091031441c41c1c5010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 81299965 1250 81298715 81298717
    0x501020f070b09030109050a050c010807081303033602030c060703120c030204050a0b040e0a020703020d0831140105010501081612140612010606050a05070614010b0301030c0503030f 80
    0x41d5440c0b110000c00e072614280d07003d400c24070b4a079400c10141c41051490b41849500c038100075603a00d020810540214954622500c201446458107650014050707503030350750450241291440355504607450300b100344030f01403c10b482c1c41e00340c1a0707072515007041d01550f01c10b0504108000301b00c0751003108184010030102c0d0f04140c603102c0c0d080320080000350785905504140d0083c01580c00c120b0b0400100c0401190240d040070090041c1c404c0d222440c18295642d890b107400341e200300342c001001a0000c1c915440c100303000741e510540015042c0d00181041c001d4040040c00c900601041403200c503020620f4800740321005480001004040b030090210398100800646080c07406002080038002182d00c54400c544143c10b21050010744030000d001d0000010f01200110506844036803142d9001c4540c070504580500c02d10341282d2890300c4180c10030741c0d80c5c403094445421440050701d05070723100d603480e2040d0040100b030ba40c040d02604204a850354110f04010100d56141d4102c203000e039204000d070500d07051100c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 81301215 1250 81299965 81299969
    0x20309030c091003060204180b030c0d02040b0a0e0a0f05100f061b0506010605252d0206070501050f070305090c060703051207030c0f090308030a1503150b0a0501020f07 74
    0x38400b49281c0d110b0b40c0c01a00031100903403000d003d60b8404038000c2040000742105040d01d180300001030005800203001c15444051102d00c04d6840641d0b140d8203c01800d0a801102485c00020040d00c1c2555a401ba00511901e0803150400d2301d559500362030310340d202e052140e41d822951001c210789095040910310060781840d40129814800002d5404588a81c501010421258010107a17441541e41e148050700b20303001034034480403403450081c140d10b07030340f0392150703a000f130b0a8001c1907108403804240030603022030030030803a220300c8850070f800c040c00582c54003002008124030410002943e0b140055030800e43c00009040c040070503080409000030844002240d040381202152203642e03c1d4128501a100303072150318001850a160b40c03040050b010303003581c410341c442040780e29180c14144490b4001c541c40b17010341c00300401e009410320100b0510314881e80113030010320441340444035240d00d0703071501100740b80480307070010142d901d8034003162580c1448003001c40209400c0c001015044145410551559014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 81302465 1250 81301215 81301219
    0xa05061e0c16231c020318100201020409050103050c04060e07051e07061407081b041a040503060a0e0c01050405030604060b041503060f05250f020c062107020309030c 73
    0x4401208103020f41d5444a00680303000310124a22107088542840d02e40d8070b070200b00e001e010300c580d1422a407a030003c0101c4904580351030390f0000950305035041080304880b016492046643c244004a000700480c41841e01841c02000108030130b40c0650100020b1301c039150007001c2c10f40701a50034489041e401c0b1080d107a00543c903c050464800c08a844440c02c0c0c001c0b4100078003810700303203003c940302400b02407855405802d00b0303a1045600d0755164070103100569014402004010200003c101c01e40c0b09103003482009180e400918682941c610010745002030669201920583d141c562241a41c410001d15000a00c01c2c02c1c00381c1054608400661105001080034101a8907643d1542141d522030744002801d03480070b09c18000c00c94480c24604010210380d078685000624040102d0345c215001010070096031940860b8080140c00050101c90540440c1c5808080d4411440f0001240d5a044050842841da208080c650111001c041003d4403070060805801d41d00100180f081546010a41807114041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 81303715 1250 81302465 81302497
    0xd05161403040f12080a05060406080705060309030409020a091401030b0904030336050610030503041203020708071d160503010b07030e03010216031413030b06040207050a05061e0c 79
    0x2c90801d0001d690322500020400072040304c41075021604525068011515840100801c2d5140020303c0110790301c80c000c41e070711a44001000c020620703100004661000e081c0094a050503a203096080913a0020304447d4040741c1c03141c20900c40006c08403010030101c9002d02c0c0034000f400101c8003041d030441003d0000b508150301c0d070640d1801840c0428407100300c1d0b20316480240e103407254500c074640702100d0044102d45500801c0081028400740e40e002c0e000b0340f0b4108015516180c5000c040c080d840c5294174085041d0f025107000000e0310340302804454000d059030005c200804000001c2108045002805452028080d81440720360b180c0c09001e0b24156103048440079502e6416003070aa4202c8010040c01d58035600024400c40d11081810551a0080c031a0f15030130000e4102d80c0c50400c05009904007141007040020b020008078900d2060240c20000182005181850a41302d00781032415040055619600c0542400b120400449018240c040c07130100f10443c41c01c000405030254850840f0041c48042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 81304965 1250 81303715 81303721
    0x70501230f160b0910060e150f03070e010b04050a1e05040c0311040906050306090604030f0c140f0d09080d09090b0307120b01141203090d0c1701020d05161403 70
    0x82880b05a0450036000b480510043c80c1c0131840581d15484848103c1c4110704014000442d03454450a0078021020300c82d91180004040007400300c0c210f0460b100a500d485155400034140c078054810501034110740c0c12070396980d070a10b001e00c00c3c0c001e015402801c0381c080740842000311040c112044015258222804075018107a440c0883c043d100303860050444180c0002c001030034122550018003150020303419100280d66003410a500d4a10444018010804103031041c500503214a81201c40c4034402c80c0d0701040e101d00780c012c0030700d01040c000700b903803003039010101c61032007181c01501c80c000a02d02e050007098031720a0020000c180b030805c0c1c410074130540d4481494418940d024044000a02842840034072442c0356818542c0c03907004203100d19042a006403600d030070b40e4240030045042000080006500d4850080d062050071105c5403416903480404840108080220481034201100508005600c80340d000404500702d81d00500281244020864031541c1190882081c00e07010072042042d684a503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 81306215 1250 81304965 81304987
    0x5100507090e06221a0a0b03040c06080a060e0f07020c04050c0703050f0409020708040e0114091303021c0f0e0a2909030a0605070e090c030c0901110708070501230f 72
    0x90356194201001c80c144481e004901d6084031031203510005c02c8901c0c0a0b02c640d17828001074603110940c2c0241c0701c403030024418801603000340002c0340c00c9a54402d002a0140d50342c0d12141c8186801c0e185410600c00e49800e105249504018402d110002158100900d0a00c60b541c1302e6a0310034208000c1c1407084c0032400f006c540c401001a2802048601400d41d40c41c44140303040704c000e50250150030603d9003c0400490030907603812500180e1000134010602c00d8880d500240d40d1114000300490440c801d0070124084041020032100b10b4a041d0b844031a100388419101405440c115500c1d103004084842c1d00f04030000203030b9441c0c40c0d80c0110b001d4000c1c110082105100c10746c0328044d030321601880f4240500c420402036a0089105807442e07074400e0703559140c0310104140ea440075210810307040c03014004101c00d080550018817400105040c04403040259509950800c4103d5100d2042c0d03400c814020400ca507048070f6545031902e0008a060440503100c80750542c10b018100050040940109644900c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 81307465 1250 81306215 81306259
    0x6120606151b0304051f09030305090d15060f0605090904060509151f081609020913050103050616050c0a060908040803030f0709080a03050f0a0c0c0305100507090e06 73
    0x500001420ba2044609a0054540ea035001e486558011049400c002c0c60a1640704d904000d6003070141d9809401a06e1600d08941c5038001501c029440000703246454001080d40050304458512160046100740c500000d070000c5c40040d1380420b0a00900f0000407006170740d4001c40d0b03903001398080c90021f055200c008030545061111100c0042034a135030005d000300c198880b08540c07550101c0241b01e00d490b58560a60540301c040d500882e60415500369070030700600d80d540d00034088a00340034190548140e10447e0003005d5031001c2c4c0c0196015008001885800c400e040032541e0085040c0c00c0140c0340c01100041d080c4e55028683c8040d0110396038000c1502084140e0003140c0c01041804116034490900803000303901080c05499400118400c04400103c0c00070104c4c40507403842d016240c60341030a4020003d02c01e01c1d401500c0303034001c1096100d900c0e00002d4035880f040020314024001010513020b204000c100b100c4011f0444401c2c8880340c0010800b41e4410f00000d40d10040641d05001c0b00040401f1600340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 81308715 1250 81307465 81307477
    0xb100305030c010e100b031c020319210c090308130506070b0703050f060102120903010b0418061112010302061b010c1706090103030e190b180103050612060615 70
    0x240e03010001e484065090b054201620202191080d60790040d01290501c04980700059290b405811401e822036001805495042120a00e40140c034a41317800c1c0e283d8003e85c03507003d900c1030010442d110001d028030003501148504003504002d080006005440018100791014130005114210006d000044000e500260000400c000340c42a42c0f10802403603c68103090b000c40d0007100091403b00000d032010f05031312030540504c0c01a0050800311882003510b2001d64400325030680c0640d01c0e00c400c41c00584442c894040101c8a10b0304d00300701d0450314a01170302a50f00310301c050782418905005040300c06103429a06411282e048440b00d6995001410303000000070040302e881034652a000113510107541040424428200d000c0c42c003e015642d003400c00074003000a000c098001005c0350161846800d2a90302c0f1686a503a0303000003038a40e0b81c2c81c440c1d10201e60000030f444503414081c000429a13960540221034000c98122052020079481c604100e070b0f41c95004015074490780803480e07003100c04e00740e480c101c0700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 81309965 1250 81308715 81308723
    0x813060608120909131707020d020d05030403051507020705010c06091a01050f01110c0d0f0b010312030608010902030c010f030f060b0c0d08011d1b0307020a0c0506160b1003 76
    0x1a445440d90200c8229002000e4450084c5040d034000758528541d02c200102c8140d105125400306800c1081a40030390b04407400403a080480131200c1e1016940e03040044001a100f1401140e80d2400c5103011420b01841e01c104051000c503403020f2155043e00441c508090320001c2ca003402c0e26103428200344010384141c59010f030010400d45d14445807032100c000081d044e9401030360040c0d180d140000045442003140074040000750803000f003a0380149084031151400a018031a10000804d56403905114082c00703030700480c0c81c0260010b142078040d030075004e03c01c018000392008102035010740d0007090310764030242d2566040004070b606410003180a41d000840c4203940d050104007850f16011018900d60100c0380f09201c91140390030340240e00c0d03c01d07203615042c0c1d00c4c80b03000740d10401002001e101811001805d903141c01304c1000260400700203581d01443c850141c540c0201559001800c107a05295807039003005009107410040d028400380500d041c180443d5120b15003d80541c3d540c002044a440184c000030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 81311215 1250 81309965 81309973
    0xe1e0607030905010f090b181813030201050c040803030403030e21040509010b07020a0e07120504050d080a150b0f04050402040b03150406030314030601030f061815060813060608 78
    0xc06041d07110396444180c0780281c840c102034201c10801030350032030298804d82101042c00c100d084030040c40f181d0305506614004e03015001242d0641340002c8240c40c00c0300d9004410007545261410301d07a090044e681c22003c02c156162070981401b0780c03541c603803000500240606031036a0410f420180d0400400c601505482c20010082c0521400703070610744c2c0319100781071250942c20004075690300342d4001c03949181e5000308201c1805141c4401c8421446008141c8003d104103402817101240c07080c0251845148a0005810885103500d406060500c1c00340412142500c1c1c50140300385e0010300c10107034054a00c00c03900d25441d003110340c110b0701081c42144c11564116001003400140100d018001c2c0d0f02456106c02000080c11005040c841182d2044c40040c00050a04c580f550305038140e035000f56000740c0103140110b09184c01c501d0340005d882c01c2e58003120800450783c0c0700490b00c403d540f080710300b0381007480004001c0700d241140060031f040003c0c01886d240c0f03455103400703000c11410f98403240c000c02080c001d803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 81312465 1250 81311215 81311227
    0x901031805102f1b010603020904080705010507020c06180d080d05090d0f02060103060216060c0905040b120a1403130e010906141302180a03140c0901060e1e06 70
    0x10301c000e400402e2442d090900305803007041110360078000304201118200f0126041482c11240400c890701c01540c40d950725585e90f003021025071240072040c0e1086000b2880f4036a144107a01d415821142d00400c040c0071900b01100d111800ea8400d400c07110080e50914807990300307262590004500030742c40c0701c0c0288074010004012018400942042d032081c0482019608034500b10941540c1d44200400d0100041e000280148000b650755400340c95840ca5100040c80d0604850340ca5408a558244210000c50b104420410051400f400b404002d100d050303480c9042120040c0300e880d51800300c40d0000b4048141003041840021040064440340c150780d0000e903189a58500c5294001d82e020b0140c00c0c240c904148000c2104984401c1c415070710b00010700803111901c90700e00b00c10000d40144c403407107d02e02d01e03202c8921503a1351980e45d8031020b10b0180c140b0f0b50103c20300250302441d0070200c40300d0601451132680100a21a041042800e09070028ad8150380c0d450b101e0000c030000803041c40742d0154040307008500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 81313715 1250 81312465 81312493
    0xa1e02010c062c1c020703030c0b0a0e0f0109020411040503030d05070c020303041710060806130302070b040e25050f070201050702090112120206160e030c0301020f0d05060a06050901031805 83
    0x2110b904444064018000580e1017243c54956502024010171a0384000d1000200c0b1045081c0e40060000000030f884070500f141e050401405511b21001d0742c1d1100310140a40c0380600c40c410b454100b8032103d5140038507180c0440d40b03c2c052110501e00c40b55850700000c0c08540242c440c003002d140e000f0141c0382e403248c550f500160a44054050160795104829045180003000c1c441d02c030551325004010111760307480070380301c054000440c401241140154031001030f20007403401c007a001030980f0031451141e44c541081c2581c80e9110002c00e0303a15001e0612000d142c1142c05c80115802d0304180d864440c2c0e15040d070b00044e80c45100d030100094010311240f00000e112248850f0b000b094512820000005804284089a44907010b031201c1070301036401d0724492042d501030b03094042b00500103000e54031a80180400a404c903040171030401518000011080c40d400300c0e91080991101085407080c8065040c0700d4000c115004450f0305038141030783c44807081844149250f0035a5419803220884203058003487d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 81314965 1250 81313715 81313723
    0xf0f07030806060a08150102100c030b0f040911011d0d0b01090e06060307180609021210060201020403030503191e0b01020d0e06030f0403110703050a1e02010c062c 72
    0x2600340d00250814010071000d25151088851100c1d10760b80303c00c01610b0794003c910078224040800f038158882c2080c6814040c1ca14000c2030790a0360b1503200000d8201900040c070801140c42060b140c031031481c06802d0740000f5407511064000000030320f4134005808000694100032104440c0c03490b07000f54002404400c114000d03081a040c1c03041e48006001e504030f4030859a035110400d450399a07241d00f205c8030034009a40c2c4440d207840710740942103011810f960340d4102001280c0c403080c01607005c4034551080101e01031031460610b008100ca81300071850b040c40c40d10010b08500014003445014000ea441031044100e01d40c20409000b40041d03001d017a0804a0740c0850b00604490000740e015019850303402543c9030091007140c00c40100500781c07502e075a903a00c08640440300010003c4060103c0e0581107407526800b08240f0700070318401d01c010321100e042400e10f2101e0b5207210702c8203810300740c020241c2170060764007070208000300b60320a83c085110a03d00e80c0d4800101d219910382ea04a010140d0500b0b64084001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 81316215 1250 81314965 81314977
    0x10212040c060c020d02010e031f0614090108030a0315050910050f060c060a050402030a120819020a021b040209040903031506020a050a150b13090515090a06050402060f0f 75
    0x10140d1445550303291003d981a422a0310003941c0003604402440142d40030700031408a89100405954240351640c101444040202101f542a40da84000920034180503040b03602c25418110b40c490300c1e035071510304441d60328032442031703c101090b40381e000d07840300b54000c1413505000d01001003010119142444e0f10310480100303032180314490604202d0302000303401d02d0001c881348208640060680c546d60300c0055405001c02500403a014071a0070a25008182840d400c01d82e040138075614a1000d013070080010007900145038400060510410249032800d800003004003c3c00d0007980f40001901e0f005000600070701402100c04e401c00e0404014a040540c10751010f58041412035040c10341503203c2c60100c0c1c1d280b6460710018071581c000300c03620011031412034543e1103a60003600080b1301c110355040403805003c0354502e658091512420704404012080c40641020081c40101d840c1c1440e002003503030351b910108880900803c0c2c0e60300c041415903c48c42c08840e100098102c1c8a90703207040542076040707580c1c002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 81317465 1250 81316215 81316223
    0x6050f0f0a0b0105070201030218030a0c090c1b02010f03061a0a0207080607020c190f06030902011704080a0c0503090a0305071505030105062b0504051b0904080301210501021204 78
    0x900001035000450b441846641d0301e041e55090705020482c2d0043d0000d5000208800081540c000d070042c1c0c9640c104284a4000c2c4038404400c009445d01329503d01b5074541d2003003c000d1201031084091219252403040b40f00c00d80920300079403d4a4002015002081340d600010240d800c0c480414150300a00b0008098801541c2c0c21100c80903134410030b140d259081540c0100043e00181841e469a1911030840c00d4160703042004055002d60f6182c0d5405119171607804400841e4846151a080d9a04460600405204084a04e1042c035003540c41840c1480340d680e003001400b070700010050030311004005607500c800b4007402c56000c054036810f1260761600c0921520200d42c02200140d03000324071600540f412500082c001d107003841c14184900700003941310240e440ca9141082032084500071580940c0c1e00450040d806459035800200344201c0c0c0f02e0301d0040050003440076800380400940507200301c07411601802c1c06111301240c2861154a914203592000d400c1d0343c00841c00e82d00300c88c0c08000320384c0500e00c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 81318715 1250 81317465 81317491
    0x2070206120123191511030a02060403030f0911090901090204090b040507080706050d0b1206070804021203160204020d09021305010e13030c0312020f0403080c0c010c02090a1806050f 80
    0x700c0d0b000c0025506400000011304800500c3c01c00c000203a00d02055090041803c3c603095003a03d60100301d18541100190030b0040c0d020505201c1850380600c01e0b0b042e94109140b0a004076051901c0e690b560110095100c0c9c060300409c00050070002d020742c001d2030050380c000e00503c40b002d52410b20f55640f01007074900b034956000d100c000080c40040020440c04482c11038940604010710b101c2400c00502a01c041366030010025440306000d04030038013020344a807100b5125103041b410140140803410406241200c0303681d108219129940d43d031564114a090760440c2c025a843d10706285410141910700030003908640c0c050102009006190002810f0390f0042410308150364800e040031560000351200034000c01c112860384400300b803003040700120b10f40d800c0401510303041c910000840719901c0f650043e50342e100d002c0f407021080301090280c1c08600b40b017488c10607881c0402e0740020390118809003041c1382403590f40e102e10540c490b040640f0404c1b641c01c1542013146150140030041d1100301110070848150b4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 81319965 1250 81318715 81318779
    0xf010207060e070f1e090c020109121115091504030507031725020f0706030204050a0b040e010b07030c050a0303140601110706050f0405061306080a050402060d020702061201 76
    0x81c0004000c3c0446824583c50740c40645000040444450704141604440c1c22007100401e03154100c0c0071350714090165078000214000d00e4105036040ca00c00301e50300f008100c554680000d41480014a203080003441b500d41100e03541340d9500341843c0250840c404211a400602040145034020707028102c03041c002e0708d8540c401c01200700c00c80341d0900e044a00d050050801c0c46510120f8211244004905515004035001c080e40d21b19403910b002003607800800060340004042c8940c1c20500e5426004001c20303c0382c03500341410329076400811001400b4000002c003000c0b40e031809140c804c3c1c0a030603105420005691240781a4200100030340090303001c00041d50390403030114446511520410241b14400ba01030f02845050001c100d8059200201c3d0841c1d00f14140800310701640c07100014a051404401c1001c5c12030714144d8040c0004030b00030096100c06150000b0800507854813400c4403141c9284030030041c0c1d40d40e00340c070018041c0c0c007420804600c0310f4890000032402c0d2404801e092154807101c0741e4210441 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 81321215 1250 81319965 81319991
    0x7050d09171504030c03030b0406171b0306070c0c09020403210203030f0f070c0203030c0a060b030601030309030204020d140a0603031407021804030c02190f0b04030b04020d03030209030f01020706 86
    0x800c01064807038a4a02d03001602082c0300f80160140c0c0c82c400d14010511aa0000000d0182ca040c1e03045045111061040302e44802010000d400c0c01000745010313440380380b0441c000681c0b100c00041a480034403041250940821103c00340e418090064520b0440d250ba03200d08055100d42c1488490b0703030107200d00307a044000d06800003055902c14480ca001804d4155140c42c1d240148007006070508060107070910307140300180d505002402c451202040100800f64480c10141c00790742400c4a00e5000340c12150040c0003290b40030b400030b01075a40590380136950344074a910000c0240040c055001c0d40c403041105001500c0e4850b007140040b60700a543d0303190b40d400c010310f0030041c40c82072540c020350000311081c454100c2110701c55034a9106000342003441800b6069004680c40303d0340c6800c0c4c40790000040e0b600340814058002031002401d1064a1182031078110390f42d01e2000140a040a031007143c4c1d01003040d0030540310f501158404071025080d15210002100002c2c043d4100c1d1100b10396031400c008181a0007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 81322465 1250 81321215 81321223
    0xa0503100f030f03231605010b01090e0f0915090a02011103130e09010f0e03120c040b04090e0a170405031002090d0b09030f041211040c090501031107050d0917 70
    0x2c0c0340c00100415000c180d5960545d6172500c590700c8203418903049506602e80000b0b40d405041c03028006654002044038915101d82154015504c041c180400c41209200c8000b08901c40ca0740548a0660b4204688542c20154609881e124951040c0c2d000c0320200003441c07070302042c03c9001d94400e8881900d600200244983c0b01d000341803081041e0061400d0400400340c030701c4041504100036600004040540c80c005005850700051303010402d600004400d030a00c5403075094181e1003a159582d80341098100b82d410903107072280c0d2041c030a820b6100c02903140708030401d000003030080e42e10085a690380c0302070b801e4070040c41d0054400c4901c240a110700300300f11080540212001030743e00030140045221982e0781c0c60344900700504440c0c1070744014460700003030040420080c400fa2980702c590000840c1c00d0314064050524803500380d801141042a503501c0250801040400d642cbd0900700490b01c41c0f14142d00841600503c00050a644210070b14a10305e550009410002d407007480045004146409070b40341c1d03035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 81323715 1250 81322465 81322469
    0x60e070f020607030b0f040b0402130b03040b0117120c0c12010c021e0c0909071815090b03070620010504110108010b1204060c050f0c010501180e06130204110a0503100f 74
    0x2218031005001b0851800d42d00450501c1c2000784014144681c1900c20171500da850380103c4001d131000130911080c440c00c5070442d40108400070203150000c11b03043d502ea460f0802a40c100020180101c0c0070080040b007401105840340000e481c501088282c21402d0307020f0300040300300c031b0098080c420305c019140c09140400d98440c14000b00622222a0580501002c1000106141c040d03001c0d05401003a443e0784201041e0101100d6000820110440004400c012b11980e110001207480e00c1c60341b40340f64802107030403400c0300c420341009104508142c11a0b91031031030300042c6142130b518000c10401041500024011070980c00e0b641c094007682c0360340c02c4950521403600c450400700d850100190024040b500030090030002403034800d080c0344c7c0122281085411101136052103944540c01400655101d00d40310348100d038030034030500006440b42d40484d10380101404c42e4a9801d040030380c4038107544954001041c00b2821144841d076890f9020001881500103880c035426054100c0000255072080043d4442 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 81324965 1250 81323715 81323719
    0x90a03030507020a0f121407060b010915080f06060c0f03071a0606040b0306060702040c030e2a06090301110403140c0d11101404090c090b040807050d0303060e070f020607030b 77
    0x170103002e007a143c800e02c2030303198180c1ea81007080c5608015540c10000003d02002c61280001107102200107002510300c00d0b082d0040c1112013907445001e51442d901007491508000d5114042d4525100d0780c010502d58407c51410481c40e109506a0f0085050000000d00c0f00c0c90040301402c1d510340c840c10020b6091401680c1e180c0e880b8805000900c5004c10580c0107540007080105009d1500000d075007c1001d0711801842100425904c200d03121302804180000701090022003000380c0c504c0c003100c030000d003007480300c6c18561301410021941d5101c40c2c40075841040aa00c01da0081a11943d680c50203941913101060021042d00132108000102c2c01c2c81101d591489a200c5941c0040040000501441559070400b04d4100080202c000d40c1500c0c600300100043c1c070071154042440320700080007509071030456101c0e0100d11f804110400401c034000c103022003074410807102c5044010f410b040c01c5002e040d454006050012a9500b400070441c0c0140c0b80401da490940c0998203681d50351740c0207800311071081076280c1d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 81326215 1250 81324965 81324983
    0x702030309090a0605030703081809010b19030609050a0504020a1d0402040b060d0c02100b030a0206090405060112060f0911070b010e090304030516090b1c0308040206070b090a03030507020a 83
    0x980702d107040e0354443e0b8881d8415100095103030381e60300041d24020b900c1c5e00c01c1c3c81e520300c0010f0f003182c000c03881500c001e14042c00759072035a01545001c4440003c1d20580030075451022010a8071159a44a9003004009205520040c0010704012180d00d00404054408a200d80d044031400140e4080100c0004c90400d000070b5074200c0d40da04e580070702c0700ae010b0010303580303500c078504000d02c8408070742d01c1c4603648050000354010720300e002e881c121072400c5038205004c20307119610120249005036100801c45646844c1610003080c161102c6005032100d880c10514210a10b0800c5000b0030f069421482400c100d41038040300f030046e291101881c43c524452100e0162007050204010f001c45a01e20240d160882e41990440786400d5690b10b81c40e091040c5d070207140c06410000e1604200d218828010740625250480b22251851142c5880415180720681d008040c4030b00200007405554581d025204140d81107080640d45182010909440d04d1000604a011a01c0c11001c1418188009031004580e0f034414404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 81327465 1250 81326215 81326227
    0xc0a03080405220c0806090c04030b0a150b0d020304171603030c140c2103101203030f020a021614030304030611071b0e01080610060f031103011701050108010207020303 74
    0x400700401c5060910751400c1e96a242d42441c03c1500e1140c4a0010a1560f90007024108030081160910006d000f102e003100701880240003040100b03181b20342051000300000342040f8152802d880e41c4603140d21000f075214001c0f6007090900c0c4160011071140e03210f44003e509a0070040b290b18100d006100d51040c0074140d40c854100024020b900c2082d09507100e080141724450301034200fa030039900140c020b0107035401080ea1145a082d81444018a0706110300c0900d047d894014414954500c96100c1e0a0400700408a28000e040c002d601001d21013010303150039503488024030030203555840c0d0324542c1d800c1424403506c00100070585002070400310800901542c6050b02c2c40d1214809805041e1003101e030b050003000258006005407079850742d0212400350405181c0e251600c003c80c01c950503400540c05401c072070308001908042c003800c0ca0603942607080c000c000240000048004000038100e844206030b0020010954100c0d0080c503005001414000b44016030f05c42c05103034240d00a000c0002d405510610103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 81328715 1250 81327465 81327469
    0xc070b04050106090203010801090501050105060f09090727050306180606011d030105070206041a01080c0904081e1903022113060f050a0524090712020712020c0a03080405 75
    0x5840c0d00103000340000300340c9644842060003264801e0f0702840103690345110b502e08003c000e0103854010901110317020b060000000c1110840e10401404c14840d50500000950680c0602c0c034a84000c0728000001c0c115045e818290309044170203000d418482c1c1b140c1e2000880000c000008035030a404010064840d94035004019500c10700300000f80003140043e203a164042c0d890910441d440740030f09600400d80760502e4140b018110429030400c94090310220010300c800c9000041c145c0200000b580c4946d2283d07254240341e00300b0700401c1581a40c0700c810400c046001d10001000c2e100c100c1044021442c1803000b03034400c1d0200c2c480c610f0b60070400806444031000420b08059038a40c018886490a0207800c4203541740380032916040080b4005907030716014400030b40002d1061992212680c90b030243c1690200c0c4102c810f80110302021417055a070000003c2045105400b26402803203c0c2100f03544441d103e10b00341e900d42a03945c12070f80c014421200e0030b00c401d142c0455080116500052031b10b16007424401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 81329965 1250 81328715 81328733
    0x80711100c080310081b010e1f0509041b03061401020d0e040c11030403030302070c050d030816021e030306031219030b03030f040b0913110906091903050f010507080c07 74
    0x1c00941c0b88130403000c002a500c0c0c0203000c1d00c1c2002c0840303094200300d034200341c1c0054219030000d40b0041c05132900504640319801032100300d840c2c4036214145151114001000a800b6005076400d1014100d4440d200818003a00364007c1d0f002d8a0681c410b1a503064014001241d496a4081140c0001051102c031407030542003d50001d0086c1c0003a2a052200d80c00c2000d166203154000d500407030020f680043d4020501c031f00000408040c142c201c402e4844041d15480080144c000a000b018412001c0301914290390700030080c1190a200704128030b2810f6a41c1384185840b5042251071500a000d080c2c280e0b82900444001c66402c0020700c0b8071840c00064824045000313010034010240c1600c000c0013000034500001c030140000f4440000159076070300070744c0305100c003000001e00c604106904204031411810388a4007540d0000701e06945403611140d100001a4808011818a080c0c016003614084140320f008600071001d00b031907800900c0750f62558007085800100441e0090402003042c880c1100090b0941 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 81331215 1250 81329965 81329971
    0x30d02010e10051b0a050a030e070605040902130801050c04031e030f0507030201150f0513050c27101107060206010311040c110f0102040f0503010b090a091e080711100c0803 76
    0x2200100840ca130304a6010b91590100c1440004030328017284d9020403503854000c12100d450000040d1040f54a00000600f4a0003a130045a0b0b500d900400c0c0b2400550200c0b48100060502200a02240c20022005a41c0e41d12a01050301e665201c521105000d140a56100c40309030390581d20111b0b04d150030319048440350044130040302195250344c800d422100000380038202401400c841d9010081c03070007007007164010034510400001030901081001c051144410369018030705142c940400c100c0c80c0f070800c900d2901e00e480c1d503a6000400303c040c2c01e122940440051002810380089800098031043c003607a0341d4500b488010314490501c112200f02c1d050030340001c0070006550600144401044410074104522144407203c241c1d8045002c00c407000e00c8140303040007003c0640c020001c0c0c031107000c041603c00d10000c00d160010b41c1c8444c03101003000f15401c5641070401008900041c840003900c0c00e00c00360750000c00240c904a0810307046011500c0e05070b0804043c02003031740f00c1d01b040071216555102c50b03030801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 81332465 1250 81331215 81331231
    0x80d08042303070609060b1003091214091305040308090708030301090b060d050708041b06090b070c08060408070204110307080402090603160e240105070f0c030c0305030306030d02010e1005 83
    0x180f040e01c0c000b450714001c4000c0c440c49110007203042d0346904140725550780d00f41000380405007403c1c482004142a1809141d140700c0d6807070072502640080300403000303a1017042840da4002170408a58401640360f07500050141d442540e0310710080d2204803c1558562460041200c19081000100014202c60b4040c4000c241c014000504003501c5003003880c200c400c1200c2001c042004a8100020400c86007118904810300c038000711500c0e400d00b54014100e01c480e00503002c010000142c043c0c2488540c0b203060004018013801c564480c6072501d4420010313084a502207028070b00f0701060380c804030300707003400d6900c110510359800440750356075000c00c80d1f420006840b8981502410514000e84800740403d00090401c1d0554a403590424030082c0c140c034045180c03070040512806503a01c1d4a681c0c444102c039419600072023801141c00701c0d400c02100b42e4500c0c6c0e0000348241a5a50000100000440074521a09044094400408815030180d0a80b41b142004040903002501c4614001d4031a034441c91b00100342c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 81333715 1250 81332465 81332467
    0x3060703020d140903090310060f0311060c1f140f0402060d0e06070507031b051e010605040609060905070c0b0610030207060e010203041b0320031c09080d08042303 72
    0x441c3e0041052100280c96460310380d040014101103d040420818041d00c0303003840d04000940c0350441c036580c0c1000030f020090287c41c0c0f22801d44001e40d079180956410544c1602a070f01c0c00400c03003059449039000300c00e0040311581000428002d0b00d10083d44c0520401013203203814042c0d6525402c00083e0380c45002c0f40c019241d034586070f00c0c00d840c0e82049104c2c40f031021a00c610307540d5480d80c100584034240701c500003140d4402c101441700001e42c010038a5540b034003080700c0d8400055642c07281d00d8058401c40d00015001494410002103104450304200119a051071007006292103542c421102c4c8030091102800d80000000030486500b0101c00d41202080c0078900103043ca4203960302d290583e1300140c042c22507a90040284000d0104111405820130f003c0055151034601e50342c1c4001504001c0c1d5600b60740d0b00c08841d1815400c1c0c5051003440072140c042d404000c040700348200043c002d001d15014001283c400c00491500040c0540320f0076001c0c0e9002281041c404451207001c540d0700b49900008402800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 81334965 1250 81333715 81333731
    0x130812090f0604050123010308041401110a0302070510050c0c100c06111201081c0507060b030f010f0b0105070206190207051201020705010b04050c070605060303040b0c0705120c03060703020d 84
    0x90305202550103144600000b01e10071664240c0340c04043c0d206d00c001299400b01d03a004100080c40c020032a8100d0300c0c8112141128100c102c016103100d02c803c0719098a43c001e4210101c20154086036505c181c8400b100c1000070252403031402c80e158080c00da800000b80c3e0044084050600e172852031a00c9810b40d500c1c110142d83e48654131001500c44078400f00304200400b06005801514585401d4050920b6800800c48624034054105100b001d882031203003407100008003c1c00f0b020341604160482203010b03041701c16410f24000c040d8000e1106000d440807461a20034550341c590300ca4011585000c1e0001d200c01d080c0b00d003204003120503820005840040d8865a500000c264540003006621481c0740800180c490801c0d04065081d5811030440c0c03031049281000b00000880c845041d40c5040303400100026640e44d4240202307146102c3d50b001142c1841012400107c00d07400018400c2c02c0d1281640c50604c00740c070071401c2c3d0341d41d40c2e5440c00041c0d01d0341010f800503030258803e40c058900304000c0d11000c14021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 81336215 1250 81334965 81334993
    0x3070f0e0604080f030711010f0c030302031003060903020d0e010e03030f030a06050d050f010b0105040303080114010909050c091c0b2809080301051017070e040207050102040e01080613081209 84
    0x1100c0d11500c459690000706d180400e2001d0708000b130b41984000e08008041c02c641d9000109202c059550003818158040b02140404507524101350103590722003010840201c541c240a582e807402c5401c5480021000078104c08194440c040a04206d00c01034015800e00301525800000c0e90001449003c21a9aa14000540d035568500b00c0c04204e0090020308111102400d155007511030f4000b02c2410b0000030441040003c0d48441001d0455018014190b0048a86001214204200d41c0004d4142d4280300c00c2c440c0803144400200b8088004507405c80035482c8010303102c50985081d800180000d00403000159801c85804080355401c0d404102403007046200641030b034200c407000c1d03900b0703209018040014441c03400c003500903003148480740c02c0ca0710758010003051646006000a00300c1e420400f0035643c2c3c40b100d85440d01581c1806521400954446032142e110b011440700034403030046640f00d1100030418512258107840c4c003554002ca1290300d0a44c1000c0446180394014024510500c0b440e00064150 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 81337465 1250 81336215 81336223
    0xb030111041202043201090b030d030f02070f03031b03180809010c15050106030b0111100b040902060f07230a0308040c0902030703050a0509070f21020604060305010501021203070f0e060408 83
    0x1d170922189080105940100700400e400050b002101c14900d46900440745640024001c01005440d250102e9080d803030902007401790041150081840345540e0f80c02c0d08041d05a08010700980400b900d41170103c0d10b04004170706490310f0406000c840d2000518500100e410000200540d40040c1050100700c0100d60390811358001e000a208075490380c840c01401420b41c1800b4002c1544030919000303c100342c0c4118010b88841d120301c0c0a41d0703095620401003d064907543c102c2050507030020b081c15220702c1c141810645541c41443d080f100c001d10761042f0081410f610170480b041580320802000003108030307a400d86104002400986406c0c001c1000054400f4041c00214071881a590300170a65003050342c0442c05440c4003801c0a1002c2d00030550038407103840c0e41080388040f00e00b1014040f040c1802d254110284949011020750084000100410b5003074040d084107048607020703802c441a141402a080f21180020780f8800005501240c0e81100a4410030403840b00f440000c043e03900d803581c1c45113160310b0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 81338715 1250 81337465 81337511
    0x1030807020604051e132d0b060a0201090506010602070e010b070c05060706020a030c0203090112051003020411070510061a0901200c0f0909061f0302090709090b03011104120204 78
    0x40b40601c0310740d05c10904000600305100c00c0011400d000070081441d6448100071078203d50082001c029444440100a82c1c00c058407044014201955500a403072009018000301c0c80180c0307461007030100002d80c061002981c0c104582da0100300703032600d90074001c0d43d018590000c141030f42c2100381d1450104560750f0b030794000c012280c8150401642c07001920809400d8648110325401550030a100d40d10340c0380d0b0806190006184d007101d00050940e070300d50014403c000d1981000c0e40240c03804100c05034081094009144041c0240302316028198103881c000e007076580501030070f1001c6a040c40c42545182c0ca48028141803c014105140240b5100007958002c1c0e00000581000f9030000d1808005410005140421000241c44ca1405860032880f4650382d504007820001c080003030a40900030b1121f460013001c0103154020a41d01c802e0a0010004085010a00544845500e0a509170b0b07000d10b814850300000d8841d44417014105072511903550008038121106a800c02c1e242c00005070002000005003403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 81339965 1250 81338715 81338749
    0x703050f031201030224040f18060501080c09030a05030d0e060115050901080618090c0f040515091306090c06141c020904090501050109020a0f02160b0313140601031b0605030103080702060405 84
    0x20304d191404c9c098102300c40191842c400303a5450038000740030356640680410b5010f0b80d002c000c0f1b40d039140b207600864540f208103a40035145d8000442ca048501d5690381064580714204c0c02194501e0742c80d00c074000d507445541c07480040403442c2001000c1031035000715142644840001c00c0d80b0301c10050441c501060b080110317108a506c0d00010381003c21031828028460708200c095804106500d007185d00b40100e906000d0b47c00384600d0001d4005920101031450602c0002c0e841001400109580d181030450101280100c0011034503445e4001800a105015101c0750388511854000e0300e1010740e9844001e40c002800c403070300180c54810420214400340121130007800c603800c00680d11101c01100900004000140104542002e191800e80c062200e1aa03030a480302803083c0782d501d4441484891035103041940c014183e2103035262422200e2004a044d41c100d9000d040012000406005c0c00c6c90400d81d14001c83e808518284014004160b044c405000350610140c103c52a0030f031900e000401540070b07501c140c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 81341215 1250 81339965 81339989
    0x2040f1d01090516030b04060504051212010303170402131e09050f0105010905090a03080a021306020604050c01050a02100b130516110307030507020904030315080703050f03120103022404 82
    0x8080090800c9120703000c0d4502c00e4200c113407900390f6a0b141201100903001a20355600d40c4045018441c0c140701c41e8160302201319049554030048400012110720910003900072840001c944540f44848092140c41158018464401c08003003c10180c01040403142c4001c0100f00255151942e01951080e1269180210010408402095462030950350141c020760708017820801400818207001966484084e8103007000c2c41e055980c1c4101c00000e000f8050b100c400c1445080b00010f640f40c001c05d110307004a005d041920042c400e40c60054071580300d10a51a4010fa220705a14003000105a0041001c0c0b0001003040c502107610301c01c003401740c660569852810701d003a49161448281c00803aa18450303003200c00a9414072b0f0641d00c000e0024011810043d003e02d8141e00020105032290b03104010904c00300c064076021700e44904000381d40d14503d0100320344501c030361805160130003000801d0300e82c8025000d562191907070a5a0138013282c05080c00259441d000c801844108582c034000181c0050001382c20b8003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 81342465 1250 81341215 81341231
    0x9150d031701090906050a1b140f0f0c24150102070e0403170a0902010c060504080702030d020d020c090f010501200601060f0e0f01020c04051506040905060a050907050702040f1d01 79
    0x80030880f080501001344652504a23801503d043c5e40982c0c0540a24500303107840c01081c0300481c0c010b82e00c50728400d130b40281000101c03010301c0010000680385c4041b01c0300c00c0b83d0440c091000e1048104d00003507141c0350503003d0307200055104181c1400c1e004a200040c0705883c0056a1640c003400e40807001d880c1140414a40d44c548144c5000c14250305511113429070090003a214a600003804045094a020b007036292a100003c0c107008860342200d10381580541160305c000c10300c00c402074889003000c940b200140030b030300108569458007107225805181c06400540c07650b440d0100641d04000200800c5210030390054040c02d03034103014000e4030300904207070302c03540010040c4060007008003005203031040c4610703a940703c2941182d90000e159030618409450014031501c0c2c064002c010106004100b59000b2000280410160283d0308007a00031700003903502251140e1150200f1402c43d8044038a400000c3d0300380118405403600b5006240e220201c00e00c0052076121110395000845400181481079030344500c02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 81343715 1250 81342465 81342473
    0x20a03141302270408071209031a0601260402030c0a0e160e030f010b010f050403150902010504080d120b090108060f100e010303020303100b040602030406050c0f070e041109150d0317010909 83
    0x6441031510149000d020040c1180c0c2d6100c030a074004580c1c1c1500c9880ac3c000242107901400b011144040216548081200354400c61308000c18111400c80c003074020306140c1781c2c61b400c20b18100010f498000c0c8450925540700c40d4081c00e02c802ca40402e10403c940c3c805407030301079101400740040e61381401002141c59451440050207da07d0a400c80782001b000308010808030f0f1160324110709112900401103007c0445000403501c601a81e001010140200180d94031940d4201545c5005c0315600c1d10b09001000742441005169082480340c1040e5401540008202c01104500b02c1d81c002e14081c2907605103921803660000d8500243c00c1240035910000c01d2005c90402074030710b0720091041c100d05514107818000029182d001c1c2d44505c0e01840b03000f207250f0b100484140a191a504805402c9032041650340707520740000501520300b503810440c54200540300e130400c5e42c0814801c10501d01d41042089109052142c0341e102011300b0f4081046202121546c40c040c0e0861a0003007076140c4004c00e03c4c0d001410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 81344965 1250 81343715 81343733
    0x30307170904020c2b120903120c02012012062209030903020301050f15060a020102040305030313021003020306090403260106110706170103080a020f01020409020a0314130227040807 80
    0x10b05d4402c4401961040404240c0c0958045c00669203924017060b03800c094a4159451003121002d40d8829041c0070141e0045641540a445114100f20180c0b21060482089106620400d0340815011103010002000382c01d219100b10107004c02c14200146102800c50b41208455419000701c0010316041410002c1d032909001c4d09401100040034150380b410080c903140300026131000f032a40a02004100002518000e40c180c078000d640140a40355203290141c5001d00c1280880300c00c0784203c0d50a0029486c6074401c0c1301b0b4a01c603290180602d640d540765a00c050319503c140b40070b0642058589607004030b070a0350380242140244403035103e070b081c40003c80c1e400c01e0a158154100ca0308000001c0c810038500442c0307222090440c0e40150070301e992043c0e0080c0403810103900c034000922560000400054000a40e801030055054a6608010030102d2102c0c0400c0a5425504400c0c003400801040303025181846031100b5250502c1500b00fa0f0b5680400d000703078107007030440d02030310311050203e40d00040c8072901d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 81346215 1250 81344965 81345013
    0x220203061f170c2d040b01051c0e060f010609091a121f090c03020f04090b0412020111040602060604110903070b030109061401051c0902090103150c0509030307170904020c 75
    0x24658646440c4c40d03200340c1402c4000b5514a40c8074a4803000302c907035aa4042d50490b65049420091240b81607900c03600342016080e844441c002e284690400034072100b000c0b404060503503607550b0780e13150124544480c2c0b83c040c04100800030031f4180021642a180e50f140160543c0c900d40600240522030100c00e42d241e101608111910803840c20010707880b00050000c18100140c0741c1c111055038010b1a09400710340200308203600103280c40c1164003400207000c0f4440c0406100251076000703004265010061b14032900440c0b0402001d64089408140d2030300c3d240d08401000c000c03011145080001c0f00b00040c0c9000c10300e0f80001d40002c000030042c4440a11406004040d2a4940450300d0802079400000c0452103a0a1008a411038003402d140c3c03c00c007503070000690990024000c40c86d0756124107107400304c002c43c0c084114650340f9001369241407500500c1174414151000380950300348800d903103500115991800850200d510104250445940c079071002d0207504600000600e149540342d40d1048607490f00e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 81347465 1250 81346215 81346249
    0x60312080a15091505040204080601080d0207121511040b07060f0b0a0308030916031101081303050912070909050a1412090f0418030503220203061f170c 67
    0x10910214914071042e070910704075012454005140089000034141d01c62080d0130269000d40000760010f4105000135159058805007000c3d60000c0d0f4105c50142c0c0d45046d00c0c42202c900351881c2c4050700114409031080344003901c003844085084007132903045201650141e00180c0c5403140115050092118030311a401c50450900030411441c0310a07030005203c0c0c12107100051140d0b000000107000d015050000618a543e070204065140e44c0300e1a040d5850310601c038040d80058810f03000240036203003000041a08a4054170b8880c90b1002034018414841000442c031000c501c00d4400000780f03900c941c85070a541034007460250203028114900700c00d9a81c48060141c400b50f0244c255160001c12071003c8807a2010115103016002c00940301080280404040c4848400c43d0b04441505254010006510400741560650800d2411041e551001c04034404081e405a01c50f80004408117181c6040c081001b401f5450038400999504001c9030b4444482044c010b0303600b03d01c8041c0d02505010201400009034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 81348715 1250 81347465 81347471
    0x2408010305060c030603070306060305060f0c130b0901052208010c0206090c010e0a03050d0822050a02040509011401032108010b1206010e1216060c1509030909060312080a 75
    0x55912501d41d0740001800caa0800360001010900796542008894002d55101c000ad000701e0341d5030704140e0780b02e642c1100d001300c0b00460000051140d284600031561030706104c2880d11040d5082000c0540b00360003a80c0664140202084220411010f0f00075160310b1020030948d16074007030300b401c0c940e60942d01c600c20400199030001041c0581c400000c101080014402e00e44011040803140004803607021540c030281c5240901541d06130700d01d81c404856881035481c00b501010f40358404000c0c2d6451410054050030176005280c10000600c2e1940010b60400080b00001c1200d001609c101c100701b040a910444062130610b02c140564541080e6403800500f143c28200415858541c1c810103512940d00d0340f0a14010071070004105a01034007460005140250900324a1041882441e40ea640c4c054484dc00007800704000040c0c0318492040d00700c4181c0d1101030405241c41550f845800f80101d01c000701d052000c02c0f00085882c403414443c1100443c001c40303c0c1248503180d031a0103448420054280544581 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 81349965 1250 81348715 81348719
    0x207150605150f0d0c0302071101090f03060914030c0f0c04050c0301030311010f02042d060c0b13080a0804030305060102070302031b0103110a020c0a0e06030d0c1a01240801 76
    0x307210124112102e0754490788640d220031101041001d4824102c01d240c03a60314094184c0c803004da242e03002c1c14a85210351222500c0c0c40d420700054030164113034070400300003449900013480013400c16000040207604c900c1106c0d00c58860018000d040da0890304407202c0a501400752310f400440b00300088240800c0949080240f400c0100100070207110500001c0c00303101004400d4a0080380c00d500606540304070010840d01c03103880d624202d15003041d40401012031241c03210800106000714042e001215000d441e00ea2001e8032590769089945402449410000200c01000001c20801c400900d480c080c299658030091605250140460f4800342c100d60455204100610050303e00160340702011882103070140440f030300b180c0101c01070450003185e180c4c2080d0200d810304440d600007a66003920581206c2c1140c0258854000014840085070310310350688c84a414132101c0c600848045201c280984c0c1c280001c024131480740b0f401a4401c0e40032040b110b52545008491600a80304048121070034688009194 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 81351215 1250 81349965 81349969
    0xa03030305061810030807140a03090501030c02010e031801050d06030c091b0c0201052b060f0e10150507060207110301062309090a02150901021225020a0f03060207150605 75
    0xc80b45c080102900400581541030245080c00b50082c1241141291069801d6107001045001503200b2a0301082c00c01c129441602e006000b5002d007815104000d50030103c00018084950031680906c07418480c0800c403481c03101e1301d54002c0c40041d5000c0c41070108150320f0074503403000b2910000107414403a40c890891941c107503402510b5500b083e4091030181c1e116800086070f0405440d842c0b8030604203000d071000c20403281c0082d400c080111440741611210140d0344607034010030500111903481001c0228002440740200b0502c03841d26403c1c880c03828a0410905030b0b140412684069030680d040114195056058502405100e02800001517145c00c26000080c01031290700d141c0300c001c2d01c41d085920000b1070790301081203071441391030f0010603600f0310712400403c0768816403014000d140140240c0d42500070460f6504101d03408100d0710009a00c4980190604008031408140d08903070140d04924006403031754030f55000c00302550003004016a20384040c80c00c0080c00104c81861b0036441c1c01c1100401240e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 81352465 1250 81351215 81351241
    0x10317030114041104050307030b0a050a05010e070f090506030109090c2106110712090f081203070e040914100b040b030601180e0304060905011205240f0a030303050618 74
    0x1075281642c1c080b0301c1001613803010907140290741001e50544640b40000062101c1c03564054011210600104580d4032000001c0040e1842405150f0003a4441000309010310300c5000080440d9070203181410300d0684440008116600a80c03040321020744a000c210184003000c41800d001303000246244801000e800c880c2444c2c000d5920024290a0f03580d0018000034031142c0c01c6512081d0700c141c815960f40b0503039030060658800750045030b089090888022500e2100000c3c984c1c43c0c1004224080c0c02c1d40d0341d218007200d117a0481c019850300700f45c550a021000482201d110a40d103c801c40252104003500602e01c0200c50700f400046229a0030424050f18580700418441e066a50140075011850b20139401c110150080702d030b501000348000240090901d5000e480d050035204242d03283e40c003808030522040c05036441038038030a00d080200403029449400403840440300ca030018041c440206010300000300780850991098010070b403180304000300c41c0740084803000342c92150307030303440204e070400d02030152603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 81353715 1250 81352465 81352499
    0x3050f060609040f09030507051902010c021215010b04180510170a150501050a0603090b06010305090c03060f07180602121303020d050a0302060c0a271502060103170301 74
    0x604070016804406403500e0700006404015210244613407260303454020801e0784503040540d00c50003040c0c030310001410300200c52102c45070160345030b81c2203c80c103400700121040340c83c40b65140e07407081d20350694111459602c0c540c000c120005441da1183d161544c1d20140781d00080070f00c000c2610340b81c20801c0c240d00d621040c0080c1c41c1c406a54211019109403030381c0ca0241c4410000d005005030703d05801c0d80d03181075000b4605903101034a0143d0341590342c0c03d0550641d20820b40081907042c0680000311035510a5004560114010b411200100040e4012a00b0900180d03250042100c104082103681c2d42c01c5280c940b80300c0030058110401510300b041c02034a6482c8111040f900880010f00340e4403000c13401c40500007440d00100341030f500703411500c0c10a6035000d00d03250403805401400006100201c5110030380340c01100988031000d44100c0124003a1100d01c1003c42e03a858112152030101c1c4103082203c9111404016400078812541103082c003145107010842c0d9480c4c2010304000500110261610f0684 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 81354965 1250 81353715 81353719
    0x90608040f0c050306010f14180a09030203041e0503120702060f09060d020a0507050d05160b06060c070f081c1b06060801180309080102040b0f1b15010e0703050f06 72
    0x12481014506107000c203442e5030103030303a162041d4000411112100b00c03803513003102e80301411148020040b0007808200400c03050821191f400550000e051a0541d410180320a8400d1050b40c3c07605480b48107600f910b54403101004901000c2d00030602c0a402d0800c5092000d1258030f0809040203c2070303000548034031503040016140c0e0008601501142c8601c8107640c4181640101035403101c1304040c0041c010340103400160784502c242c6590002c1c040c02031046030345180d0942e2414114201584403100e44140103007031203803c030a0400840c40c40c2e41081c0201c40140540082c09100c141c03404400310318050400f8032290100b210b4500916a030340d04040700302d00071a1902100c089100c0107080c1080101505c0e8001012035082c021718440031440e82c1c4005030700138400e8485501440d1203180c445c1c201d0055008000300c105081101858008106019141074911540b44059400609480c02e0030b00300209140c2c1c00082500c0014412600602510759000042c0d00e0304100710b10b0000c20418200f080075110078 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 81356215 1250 81354965 81354983
    0x4020d11030303040303020a030c0c0c0915050405010b07020117090312070c060504080a030c0306080304050121180b07022409070911030115020601030521073009060804 74
    0x140030405981111946020000c094a4403032601d0b00303001d0302075444000c1210000b481d10700c200c245240510040030405070001d01c0c1c0141141400c03005001801d04000d02070b180c900841001580d940d850142d58043c2102d6811517480b031f02c1510016001d460b484145801c40c940c2001000084040003003665495814000442c0c450340782c420041d214220a544040c1042c0e0406007004140b042080c01060141d0b6941d408004015a040c4101d044075000d010b14900b039001080b04001e00d62050110540a40e0f11011400619612802c0b51003200c1c0c43e02c1050503103020740e000d1030050000d4074010940c81002400a4812881484010648407441c1c901346608041c1c0c2c034021078900c030b600300001409801812410002c80c60040b902d0611a0001d1043e15540c6401c4004a43c2c0c140c030106030541265407010080018034203142940820315032500b918000c440c1d040c000800400d111404110f01070b686d07505850a00e10f4001000701910166008481c00d00131440d40c100080b0741d02818a07503106401080f10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 81357465 1250 81356215 81356239
    0x3081303050c060f01051e01051209011d0f100204050d170c071412010c051215040501030303020315041107150e0d020601090e01060f03021306090c11010e03040506030402 75
    0x103071010700401400c1082c1e44520010002c8000000d2851416070343e088850107500100c00e15590282030025009030700040c41885010800503a46a0325030700701140400204500340241a46000522007218000b469402101420b0050500744000096601c2c1381c4415441c4c2410100810500c901d880c00080042d4402d5041000e10b044a805488071407500d00240c419240d90341400150500c50400d032240325008030701d900b140c1044144a01e19188003903488540c10030540401408009200500000742e09128000f03c54542e6518130800d4082d520070380b00180c40b414202d062400401000500c14060b41c640a49030030040c8029080e261110f5200c45045c1c1e0114400c080d50b0013601d50030704000854030918848181c06600414031505036400107004010b102c000c0f0f108603090f14854400c1c966200c0c005d0500388098101444e1074000782d100715001158259071003144104a07103000128200203a807210030744002e020280110754800840c080114102401c3c5400502107200c00742c0000d00c41c031000030340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 81358715 1250 81357465 81357467
    0x4050d05011415030c030c09160c0b0f0901050714040b070c03061a030d030b010e06030601052b1401030c0b0309150f0f4f0f0c05090403081303 63
    0xa41c0c1514982d03203100e9403a05240c40154000001c0402c141e1282c06042040000e038100000c101040040043c01158262075250040240368610140350003001542400940418001d002d510f0007503c502810706010328190409900b11007024142030300b0407200d10300360a414030700b20080e201a2491081c40d190303203043c03a00d0103d0703000240d68001080c06041c601640b2079008003070450045050250300f60703124090701202c00ca085825400c0300740d01255040c6c400c0d02d6503090207806141d2000b4107060003441d120150303468071914038055440000c4d0001250450f4580c04441c001c0100117408044010b41d5075040d55150180760b03000380036000203580d0110020b0b040d01020000f00c1a001c0c000c0002d0051800c2078050001c15041c04c50f01090f6a10001000c00c1804102c405c07507005500d028110f0443c80c10f25290640c084140c845480e09000c03884070444402d070440125010f501900c00c1d040c82c6042d01192400c5030ba454040d078403107407103510580704000109411070002d9601000503034102ca861502494 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 81359965 1250 81358715 81358721
    0x7090e070c060603050102090f09090a0803130503030a060501020705060a0e04050405030f03010b0901080c0702010e040903020102090301060e0f090d0c08070201030f0203010b0d060f05011b020a030203030c072904050d0501 97
    0x44007500b031a06000000090100644c02460ba281e4151806117140105909000c0c03a005c041d604075503a0340c0b0121504e40450001c84c0a15001110041d50001c10784164940c180b440e001604c0e00c2c07004a50700c110401907503030100005030041206a07201400c104244801820000325054028011030b01c8200003010480306000702d4284030444d1a11075242c0d41c68040b68030a42c0c006c0004980403910060108104405940545421a905a40701404800078406102c042e0440d0b000c12002d41d9003d114100e003d580038020603000c1d11a08507608802d1500c5481c840c41c0100c090542d010503007080b05c811310341e1070b405000004510340080e500b960b41c103ca4401240180f5005040d00d124620203c0046011081180280710031980040140b003010b440c0d07002040200550300c14070780461541803c0c04c404c445d41c0f100c0d10303003020f0009020074100c9030740c0e8001c80c0c00c550206000441c1900494024418260429528107440310b40f94a010400c03041080d042c41c0b03500c1640600d070303c80d50012036079208002d0250 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 81361215 1250 81359965 81359987
    0xf060509030d05060f06090d140a0c060801060216050d0f0b070c020102060604090218100e1005030d02010c020619020c030a03140702060403020c130b2e0e090a02030601050d1103010e0f07090e07 85
    0x9c1c2285e109034918282100c55407014060040001c000c03900000d1064030014038820654001210840744a240c82c00300940c0b1031090308216500c1e0746001d086000704045260180c41040ba580302c00260901c14070009082200050145206038500000d880242c0c0b01c03103000c1400525002000e084544902c84110030b0000c03194040b990004004080001c08075084114804075802a012079554801c101003d038240c8003c288100f00580c031000c0092016078030900d0302d281000c4520b900500d8000300300d19850540e8849510303e004030b42c0320001ca1007403180c03904055a11150620280641d802c007507030002d441d100f25100862150322007510410b0b4808060348040811440100b100c010950101500d200c8140240107007080f00003a65440034820f4020414100b41c0f1800a00d006103943d12464054000e400140c0703014100302e410301088100301000d204500102c044038840e10b072690f142120020802d0f100400d01c01e4004240c906000e0504e400000d074000b900d607030100f00a01d507551004110b4007001c030b117 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 81362465 1250 81361215 81361253
    0x50d0206070807060c0f0507050606190803040306090201090b0c0709050402011704030f030509030a0c020d060204150503010302130b0303070620040b120603070305070603090f060509030d05060f06090d 88
    0x282c50f404000a56108480903509503c6000c0e00022055080d20390f03000d45103001d405034200c8000200366162524511180c3c2c102c1c8880c0100302d50700d60480601c0c40d00141c00c11a40c26580f54003003419076070031a00010060015a601c103107029004045961071308200e10400141c992500301140442e030041b406001d0b0842100c4075840c20307151030b06008242c000200e1111010907c0e00717000c207502400c04402c540a501c2a525141002211542440b14102d108801a580750360700740b10111794142c42180a80e07541540d5502e0503260b5065004110104c0c60030310103110f6079840e2090219054801005071f81d04c2c940c1050b400110442d94915007001d2450341c0380c090300c1c00d110000700425042a204058001c00c0045901e001d00e540da808181a0350303025901002d0031b01e601842081040500c81d0700320b4072110380301b10401080300c010365840c9010340d00d00791100810707030f00041002d05115400c0d215803076000c2805c40701142014080c10100b10715219901d0311602411315001080e06006240450544080d88 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 81363715 1250 81362465 81362467
    0xf03020a03090807121403060109030b060307170d0318020a05091005120d120506031c020f010213030302010b0405071e0c021306031b0b03070f0e0a0b030a060611030301050d02060708 80
    0x403d05e0f24003400101c1d0503015004c5214100308008404030402540c0c858075060b182c52040f9400c5403642007010130020050340d410703c00c0b25404100d0400c00203182c8840802c4400419008080071b80182c1581e855860050110300d03c44411070240c1c0c1d811400300201d80090312000003a44501003d4101c2c0e07482c68001a4004201f107426818062000034013041001c40c69444000c000a6111010151802038680a901d603001141c8800c41207560f84200900f903502c1c1c011241c1461a290f00036099802407442c080c00360044034000c009054081c000c0108108048404005906d4840b40140140380d8403ea00c0e00e803000482100003c06010303c0c03d00c500d4940041541c0cce4030320034a00301b450141000b404200d0f50780762201042c6000800410000095405190245096a5a90344101c5103c2d00c654100410410304e0214008580c868040000107002c0821a407a0b4178a0600c1324034042d542d40d507000c0ca0410407002051484640c1c080141ca064031000c490b0807c00325850700000f00d803801854000b40c80d440b8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 81364965 1250 81363715 81363727
    0x405060f0a0f050a0e04020d0308060a120308070f02061b13031a010302030f03040303050708090d0803070c050d09030f02040c17010803040e0105090402030d0305091f02180604060f03020a030908 85
    0x4440b11880701125400c544043c5055122591200105d0301507074000e4110442c81409030001c0e014030744035a40440c0c060440d0f9261030b955094000da20450603410360204040a060241c0c5075030040c01030034088070341d000420036400e0102800c0740364100040d40d100800e00108608100d415510026001980c000c1d07a80e0041d0f6514021059090b0030a104c1284a445a9045007141c85000700680f002c4039015210305040c546940c03210301030745d40f08141c8136034403121210124001542020146014010690f112001035000b45000d91030030044801c4002030003182441000000c02c0100c400c1c1c0c806270705540105624240090507151044103000000742c0305801000440c9407074000000d0300c119007201050794511f907690814004200c0702500c010390140c00403180f0703868071800303a001103400c0034501d411a448803516a5001e990f0b108100904218a0380008500481c80b035554450748504204648032232419142160182039081548286011325401298002c00349000c0d0344591103082c1c010a41c641da0341 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 81366215 1250 81364965 81364979
    0x120408030c0c040b0603010e0c0715020a030c02012d020c06010b0c0c040204050a1412061006020c0619080c0d18030f03060b2a1005330405060f0a 64
    0xe0071106550509204104404440d89040c2c0074010815002801d01d514507400c00b0042490306d1002802c000d040b000402c8150001158180402c00d0014050300040c1c80d5100c1090040a403080d030b0004504687c18a6003c1080030711280d20745460346050494500320700d8030070548a0280c02408903041d898040c080001403990b1268004000d0301040d4015500a128113504000803406140206500440c0e4410207002003e405505402046801004401c0608a1a607801d1421104030b500e0721415820160820980740c040003446000c29080b9822400c05881c0303100060b003580c100441d1420001daa01c0819010307002031040310200d0903014000d12000300c0c2c002081000545040003203000482200940c131006100c0d210b08001e450140003e1880c003035200c0e6450100454041c0504c801008940c800c2d840c50108009a8041c107415450101c0d2a20344600c40c0e0b2800582002001c0030001d14808041c880320b103c040d000340f03403a0110746c0010301e41c5610011403c490b1900d40099005808000041115 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 81367465 1250 81366215 81366217
    0xc020a0209070f080406110c0d0504181808070c030b0703090308060303072a0509101a0703050d15091d010c020a030c060f180b060108071b031112040803 67
    0x5900035500e040d01e03511081400c540881c0442c0321440000d44c6031000c10001001130b00720031500e165907800c641c104603450391941d00308030880d241400807802c001410040d81c400303107209506842050744108100c1400500304a207003019071b2401410704400140c0c40040080031038400000e545c00c00104030441c640710001400400340400e01b0b801280042000a40c1032800004843c0740c1079011100070320350420280d005241c00c04c482540d604003441d600c03000c50540c580b070000610503a04048a010600d16143c0700c80300c205110482c1c9402040100f04903c0880d4101c0c080b100301d18184280000c1205a054241440385d880e034009001060810200c60b510300c40b8648094541c14041c00200090302c8421020b0b40e0720100c400000303002c280540012408a100c641c440704820380180c1d030100740554202c0201d10217010401d022241000440140169540d0002c0078590040f400d0a00349000035440010401681d13124030005c0810400791441d250034002032003001036000044210a0321507445041141d07d0b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 81368715 1250 81367465 81367483
    0x1203090c0301060f081e010b04020a0302120606130b030601020c060d050906061c03080c13030323070c0306020313060c1d0315011701090b0703061e03030203090d050a05010c02 77
    0x425800c00402213001c01c0c028060a0032203005070300516000d101da5141641c050004400d042484d582c0322095081d5854a00082c0118a01e6640050b81e622100044030001c51000d41400c0c042d4006104030300301107600c2c010b44000d03544000c505a88a541d40340040b403420b80f0701d540300e540046012400741e150301d00d650845400354a0f50400d03101140c1d40c5006001510116500e0700000d8151143c020000c60b003da96819081360309d861f442494080c1d0550000100070080d401180010010500e10300e40c40d500c4402c60382d08140043c01c15103040a41e0b1140846043e0502000c2d000e48c0d8000b0114081c0803130381c080990b2091f03108105124404000d00c020300386030342c503134a45540c00100070310310001840c000c00c405200d442e08902c14681c0da42040700840c807900400551400c1036685181c018045289d280001e8461191030b500400da0f24244901c44090b030725034440c0c1d484891781090702070000035008010341e08007003070030f0320f2000b40c000c5d1504115103041d41441e0041e0007540380c41c59180a180c0c1c0410b807441 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 81369965 1250 81368715 81368719
    0xc141207021c080a050d060e010e040b0114030703111305040507090b0108090307030c020312030a02040f0815010e07030209130605010806030303160e0a0b2809050d0f051203090c 78
    0x118940d914080c02d011042102401090088100401c80350180108003901000084920002d020741c1c8a50140310810820380010110a00480401040002e0f91024901428a1200c003540040119010035a58017107400018009450500202042e031100f905039080e04921000500c039608141c00c00d661100064050301200c0350411030786c40541d50042c40410300881c260402180b40c07041c01c1d10211505c1b400c014080760f040c011a0810844000800042c50291401002c01070b69185030461020803580c09501511540c0c000010b13402617664514801c42c115040c4050703240030344d51004402c0b002485800d2030580e203d556542d003003610412651000040e1031080c2c80d8074440340c541c83d04042d13a0340000c48144c0c014001011500080fa4422000f1505a10019100f4003205480f040d1080054101c2e110381d803a510b2a0b40c040010703403510012160310269403800d201041d14181300c0415405460124054036204200e400401002000c0042c168100039030103c564a0f410300115180c1c581052a1002d8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 81371215 1250 81369965 81369979
    0x7051c0c0207050414060409030201110d0f0c0905030307061a0406080106090515150918090609060105091b030c0408010203130c14010503070f021e16080f0d0c14120702 74
    0x2c65203040c00c2c030844d85408084110030017950348250411016020824045086540302d0803280b4000f008200581140c100e055000b00d5031200f03811000044805c1d820010b000c1000c0c3d288100819200403088500040d001800800c088940350303962403d02102c0e001050f000342c40c10a00007100301041d03002e44113441214078244041c2e106c0500d02e41c404101245402c0d80282181d42860310b001440004002c9010302030215201400c00d1007c80c41c290500b224200c0c03094201c1010400c0c003140c1400801d01500084456901c2c40c10440404000c005803901c040d030030404000302041380741d20f0041c155170003881381100035940e0f031400c001c03809071130742080600301e581109a007070118002180c1c00f540c4c504000103035580c60030b641d0f03104012208841c0c203603540c6040d0300810704120600040b0040c0d00d564110500003e180b03c039080c0d1002010500f090780440c04d60381284591505513240840c213100c401b04240b81003015803a0504105030700400c0d40c049003555104002c02d80400a94a10240103000d000300c4003d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 81372465 1250 81371215 81371219
    0x40605070b0c031005060c0c130608011d0705150d090c0806090307080d0b0402090a0608090d020312060d0201260103030e0d02090f090102040e010e0429060907051c0c0207 75
    0x7510394001130b40e8128000f00f40c441c092082c1d0070600301034a00c0030081d40465040040e51300200d0200c102d4440c244034403e454000900c9428400d000e0800160340001c5006022416003205a8a40d0218081e0510036410344054a80c64003540003a612080c541c580d0030081a8020714010000139140e128080742030089100042e034419000c003d440088e600910510300c0d01600d058500001c280002c644c1358403035400d201c101c405403100c1500d00c01a01c1c05440d01161810106985450844c0054070034085520402400c0380b1240e2130031455400c2003081d2040310300c2400e13901c01a07429140c07a20840d000f15100c00c1c52000510100304030036040724001d44605126845003028818000040040607400c604084041401d041d006500c65622400c00070005041ca501e501700b2148400c2c0030f90001c00c01101403c107100c00d100910810185060314032441150b07040c2840441001e8043c0141003901c13a813014000601841c4c01001284c243d2401b5110014030300c903003890302c0e400401038403540740c006200702c40f00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 81373715 1250 81372465 81372481
    0x2120304030b0c0a14030a0f1503020a09060305030403110301110307020619020f03070c060e03070b0f0907080601120503070b1905090d0c060908040f0e0f07030903210e03040605070b 80
    0x1103a0b03105400c5e035a006082ca41c450001c041650014090720300103aa201c6804c5060000c0d481071070280c09080400080c00361031801081441e220b85e8001c4000c0e01e281404c20800180000201c4044a90041940c420400c4c0383c00044d0040c21b02020003210a20008100002150301040403482003040035000b15056680c0c1c0f41c110b049004003660010003070010000300300c20038090039140d000584142404544400060700c113900b1508444070440e241c499400900151003003404600d6882030084005003030180c80e18044d555190701c107120303070b810040a00c031420082c41000c1c005c59940d590000000390700ad080114545008000c0a8411440c1e640303824041065200c01180070340326082c0b11f5031456001e140c0c0761210b10003003802c0380e030450750b40904100004000c7c5601010341e00604009188110503d000d07440914240c1c0010444000c01d0f203000c00a000007a08030034410f101e4080c04d21040031500c15060084020420070b00c0c040003501c00460300003020b030360200040845c144680c01c1100b0720f0b190703421 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 81374965 1250 81373715 81373717
    0x4050901120c1a0a0810080f010b01110109050303070f120203010b091e010915090306110301050a1202060304110d0b01090506010905010914090c130603020702120309180702070302120304030b0c 85
    0x2407546049804000d0380c01564032801034990010780b102c10300d0308200c0da03428287d07140c014500c40000f41a5190700000d9120344c0c00071020700b175a0b80e051000784400e0f52540d40720b940b6844020414414048425290081244202250141e450380010f0841d40e03961581034000264000011840c418071450804109400400da175002c601041038462080c00c0d81080302c49902300c0c0790901c1102c10000c0c072900000202d20319008010941012168856695043c0014403081c0314280d000864601c41e030f0081c0c200141c854000300c9074066081a0110f0380c000700003001414016591002030148440d04001060b0001da80e80180e0181900762160030b0300300d03541e00c0191000c01c03003407140d0260900c10b16841a540d081126181d944011110758042c074108040c51218041c405a422240009038046040c0003181001307400a28405c072140000c40c1003080c0f990005400311034103d02d980e040640301c2c1c0403400160080191034044c41d03001303002c00c0c50081c03038010382a6260841d00c800d803014000a8081034107039850740c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 81376215 1250 81374965 81374999
    0x130f0c052803022205010f06020706020d0e01050f040902070302101d070902030603010e0a0b0603070e0f040311010e0a0312060501030501030506040f050c0a030308070e040501062304050901120c 85
    0x210100c0407034a1a000c210000c50420740c100d024034001d4009141c4000540314107030282171660344148a087c2080e20003032500c0840c1c0c104009540c04003450512458016100c102e011809280c40c1c0d5807414401e03131b01c280d039000725800400ca245c00851080300301a004501401400d44043e8100445107200500030500e1170020346505044d04114018095080d06030000c40d0300104c081d00106400c142c034424a0b00e8071400031000c0d00c6800c5040b0a00100e860107000c640f004010180d0111140d041010440211400190005052100c01003008207448401c0d00003500c5201044140c1d0b07401020341c1009000200c228014400d014949180410307150b00074030489041e2a0403200401403699240d42e07809000c0002401900c0c036104003440b038000b6584407420340000c0c500c41d550359407290511400140c9041c0c6907100a52090b803c2038014440b10764410228601d60980610a1511144030403218855210702c0d0403142c1c01c080cbd0030001140c2c1c850078000c1014803501c12031160311010360341d901d4509c402440d2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 81377465 1250 81376215 81376279
    0x50a020a0f031e09110a030506070e03070312051b0318011211040302060c0708101b08090c270c04031208010e040b09030c011d070803030105030a0803130f0c05 70
    0x3c00401c0844080e440106824410905649200242800503043c410f16900440d1941d000404010f0456401030051a481c2d00c140c00600000e4110f079900c00c0c189800c0080395003001408114261013801d480a036a40b0600134105696035140c45e201c0c0000e05800103000c00d40070502c2140b090307a0a000324130500c1c4200317201016050a0509682c208000366201c01d15010702841200c8001c40c0c2c0c113000303200c0310600c18110304001071a20040040503c80c0134036900d514050140c1b0404103d94814081900020050101e42c0c00303ca0070f8060b04a5804e0700e646401180c800c040310b504210101d01050010320640e4041c500740c030000c00294000f110400004d00500840c0108080030a00251001000b51b0b0800044400d40e0709003c130036900b032404c5903004031b6050310042c40c1d01110148030400748103400151402401941ca598144000302c1d95640306420011301c101c600200050302c080c40000a12059603101c10620030b102030605001c456102d1038060640700b4885a40100c0310361030b45044400e101140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 81378715 1250 81377465 81377501
    0x602061803040819051e03030402010801150801060e0604080604081218070521010203040605010e1e060609010207080a03111605010c03080604060b0f070c08060705120c0d050a020a0f03 81
    0x4c0380c21002c1001c0c01c00b50080b02c09106008018082107003010400080040e00741c02161030b0b2905000040c040001a0b01188a90910000012616501104d034030305580e42824a50382c0c5050b924003084071846203500841c00d42c05504140001c000189d00184482c1c4c04400c007441d82502c4524500701e000f040425071201d40d038050941002a4201008c0c00d00740000744804079401c8a030b940c05010309a80c03003150b00301ca0342640c660043c011045a800025002815208050405002003480c42007600d0050b003400d101d490046200f420030380c802c100b803401800a0340f007030b11500d0f03103c2d00d000381080305100f001c400346001c2c04202071480c103a10f042070022200169207003032010480d510265502c5601900450700161600004607051101c1001130003203a0204006070360312415802d1a4007000d5040d0468055a040380003813001190344403044c1c0e0010585500c41c4851b640316070310145024451724030150004c42c2000c08000d10030040303034040c000c0c840c007a4135126070020030500200c04503008041c4060103092 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 81379965 1250 81378715 81378733
    0x109050a11090601091505120702060402010f03020c07050d050705040c080702010b0d1a07030e0f030d0605030c0108041403071514090d080c09220c02070603020c060406020702010c020a06020618030408 88
    0x200c1b0140c00c4100840a0a000303141c07407100b549443c40000c04076201d50259000c4000d07c003c6503400220003124007003601d011400c00080c0701c1d4007a119600c43c886c2d54031902d4000401ea05000c0c041c4400c41c028680204104000103000e10060414242254110059483d204004000d82000100806034036400036180d6044540800301440e12100648158100350343d508500045200400c01400c403540400000c0d80c075600c101c10b5030b4040e5203444d080340d40260800f403020300341070341c000c1920382d0440c3e80248568201d003c00c030034052641c0203101d005084803001d002d86c4040c0b10240c0d840540296030604240b611035903402078260352885480140c1e40002c82000009911038442c4014104100000b00005100111011a2100c204c040d070300c4007060b5540ca0404401c540d404001c102c00030700c1207040a60a140414a0440c3c6508001b00050081900010b03588210380c890107d41c82d0555006146003a410b0700c1d80c00081d07440404442007010280100c280c203200110020584084130b1042c4020080c2d0f607 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 81381215 1250 81379965 81379979
    0x2060402011209031403073e0102040e0a1d160302090a0903020d0e0f0a080d030b1002030a122d05010b070206040510090305030307110105310201050c0109050a1109060109 75
    0x11b40f00904501c01c1041c4030303543c1c103203c950150016040c05c5007400c001b0100c00038035100d05d031841040302401444da071042100b0042c5a600e4408907a2005070707980d000480c14081500d403091000071001148140c06000710005180700754104103400c1e64001d544507070031541d0b110700f00800c0704d105079405009684020100a0305600c140d8100114100c05056131000d86c82c01c40100d0003060341500500201c0c3c11810881c40e09903894841c0c170380c01d00c408036210443c898078910b002c0d403240301d822014410400c42820803180c020070303a00715507010700d1482d0f04084030a800e020140c07a4084004050400b5070709060000501c00540d03829140426001030280d07241c185080c0410800e80e480214410920000c203100001164041c00610310030000c6843d10141e406814019508444008000d407249032010450381060062035490309400030446245001040c44d107000580300c0d8010050f01d51915801c010b1118200138000c02c220104a11038800d010303110b07007010204007403503208603400360001e4205001080b5076 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 81382465 1250 81381215 81381217
    0x3140412030906030915110910020307060c03060303050d0e010b0d0807020a08010c140d0e0a080307020c0a031208090a020a17060109020c0a02060304081909150807080601110c0301020703020604020112090314 91
    0x101f0000c0b000d240c9080108000301e45900e08288281c80560800f0840030288080c0340941c000000451904100107421550f01902a00448864181441e95040c420f0701c41c240c2540036401c1084000e0082d0401c502c1c4d450080c90310780c000d050072409100c079074a0008036200305028a031102c521580b642482054001130701c44103078011603814407025403240454080041c0a000b110245801070680c2a45d9103003215020345890031f08034140307000d510059030820205d4060011a005007a0310b00e4502074544681c0901850314103001e20181d0b1040c00c00d103000408285070130140102c01761510a40b845170f0303654040c803003c80c000c6440080c5039411840a510051521070015544a482115990f0400752041c542d0300c02a08445c000c5e02c00306000320024403440003007801c414225000c91524040901c0e080c50014900007015280506104101410803201c1c0d10a001540180c5000390007151074402030309000390380c1c02c1c05640c203901007846805022201e490358050f0300419070305903d030442d081c000c1890300401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 81383715 1250 81382465 81382481
    0xb0a050c0a02040203040c0e0f01050d0b041407060f030b03031c020304020102120d02090a08030306010e01110c03010f051f0807060e1809011d0102040e1303140412030906030915 78
    0x818001d80c11010700590329480590b0007031340200324040e0958201030035100c962201409840119101c00700411859913581d052021003039200400400c1900c5d68501704d8090340803000d9880c0503025401011540a500281c045000030041ea010300001c2c0301401456100c0c4181c107403128164480c40785031488085144c00540e00a0310620441c2d9400380400940380b03140e006400c03a050504d4001a1103141c514203208000040e100310800b030762440c28403900181c00c529580f585903060021450017000c0c3c0c000248808600f8410140090145c00460b5010200500084840048904036403c401c0c84500040c4011015a110324008010003800c180c420741d001410402481d500c507551800480d0481c5421205034050142c800000c0395000c01036100700305000380c2c841c1c0351030140e10500080000711144407041d03411900708600000340b5038080c1002c0b210344101014000656200143c0010f41d142052029883e10340a95140400a52036110843c19101d1980b40a840c504801044201c4013403180d128241c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 81384965 1250 81383715 81383737
    0xc030501063e030c030a02010609050f0a050604020409020f03061504030302060705161406090105010b03060d0201030216060e060f060108010612020d0b0405012306130e070201060302181806010b0a05 87
    0xb8651804112a500e143c1c42044195481e41004c40d074001c0140e024010f080141c445d8802c140101d25150303041002c2d040e0b00801116550b0740f0750380455580c1d12294112030140c40d03076510643d40c844042a020039154401d8820034000e410400406000307032212000d40e402d69901d5805481540c85003c1b003120160003d40030a00c0048000361054005100002d000b401c101359540545594501242c610f0300b120b85c164402d115200701081000400c0e9940802c900c406582403c005807140c1d90350b108210000100600100840e16051209a8000002410ba44501070010049842e0342e58400116040e010a2054001064440c1e03000400c4880c26005046801c2d220700000494201c074130005070135a0700a90084126210020700c02d04280b400c01c0e05242c0044085d039405140c40c8026804e00301ca4200c0d80b056151400141c0c000c502840d03c00c1d04950001c6400810540040411001c00c0541c60802d4406891120640d40300244078000400e615048551444c1018106a40010190307802d0b03222042c032070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 81386215 1250 81384965 81385067
    0x40603150906060e09180316140706090b0703020a0b090c03061b0403020d080d1103011701060503070915080601081f09030819090501021602040c09031e0c050607060c03050106 77
    0x6c2c002c0008001629803244502a0078002c8502401d14005002d0f241e141c5008a0704070000900803580c10040d10011030300d04035513040e0782d0207043c1822030600c00300500041c8240c4082051090b03602001a581060f60011030a8030703001e44a09614070b4501c02e800000084843e01817100b04050b02d00f040b098000c1070b001c0c2c04203601e4000c900c0c150300126220080110704030400400144042125025105c0b4106030450080145a0411000903520042d9204038841c1035100c481703141d1005031b40c04a810003484c03044122a0156191031041d40c03201081c91030409620903c500c41c009980041c06001c00a5415855008664441c01c9803402c00c0890600303046520341c0c442c0803480009409200803d0003001e441e01420b40c80210b8030410082c6da404030544010411090b0080c000b14800c0403048006041c100d148402c7d43c400c9180159510340258400c079401200130480006100b91034000c0c030003444070755404101980c0c03100b005440c049048107089655030811200c50049038844100600000e05001e004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 81387465 1250 81386215 81386251
    0x11032a04030f031101061205070315060f08071a03160309030302091905032e0203101a0d0e030c0304030206070501150602070f080613020420040603150906060e09 71
    0x525112101071000c0f000218071204e45400c00c4d20a101c2c1d000030b0250300c1001840b072250b076114244d4606c0d50b030201600b014820400c0314201700050340000e00600a0b4031030f518020b680e81305502c1e03d6031464441d03500f40d2a010366000b9400310485049a118800448840d01c9248a0042c108c00402c00250120107140d8204401b25950b524001124040b104201c442c40d100c0381030405041c10541d2311541402c201212003624001031440c041c14100c504410b440c0140c690384c45442441841050364031545102010340c2354020341034110b000402501c064150f0601c800960b6441a40c0c0c0d911070380c8003010064000b8041480180383c035000418107680500004511401421003200b10004940d004901503404240308014244039550100700900700c440260440d480d01c40c01215204a500c0002480780d540c2c0c8101520764000500018581003000700e0700c43d240c607184c481c05030040800c4441705c181100f45a40000d016842e0303010f0b141c15113001c0e96a1910030310038041406003050024200039100c0702c61101d2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 81388715 1250 81387465 81387473
    0x30e0114010b09120a050a0b090c0406061706010905030322030203010606080106270b160507080d0e09041703040f0602030a0f0f0b0901030201110709020c03040911032a0403 76
    0x855020b045101201982c800a00e0308120346200f07110040c6110b43c10100b41d040119102080758044281c001da0014082d1340c2d5000794908040b400c0c07201c294414a0900b0119000e540840303001c030710001d840c0491105455140054428150301d00c103007540742e0300c01c000054501c400108051104512554000040c0741c80e540002d003135070178a802510020b020100104811940310800c0921484800c01030315209440c0300703007803004a0307890241c685103007000280030a0620400350b040c12070341c1e001001c0e24026078403a010705031100c8031f010a000008201054400030303840c0182107030380500c0d44159400030110103e000003501d500000c00c203452002d901d10710700001c944d42e400114410000340386e00041c82c4028140c0b6004403462000c0b400e19041ca001e1000d00746072182540141500c2d02401d2010790210300b010824a42001604181800c1c0d00100f102c4203194000001740040c3c8440b18424042e225046410000d07500048a40342c555242020ba0b200070410714000c02c039140080e6140151815840f83c507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 81389965 1250 81388715 81388751
    0x6150d0203010e28080f09010e18090d03110414030c0a030507051801050603060108040813031a01080d0c060c14030414060117031c09170409050709060c03030e01 71
    0x503400c501d50801e003142c40c815413841007005002280001d2140400700e254941c0300c81030184d03440c2055804400a43c14650785c0c0118245014000000d107050b0030808400400101e201c0c1c2640c1071103052040c6040102124003a004450820404210043c201460003506d4001410504030302c9415000c1c7c0810f042c1d0355110700010801942c040d900605000d0729040c00d2041404c0c0340d40c4035840d000f1205c00144203c1ea41d2000722504040c00740380c13844460700e0314101040702d48106250b06e0801083c0d010000200b081c0c403008102d800c1d9030a000380070b4680c1d07600d02e55a160100c040180001540086000001030b409a00c80300c2101d1440c5491529001210030700010f581c8162801d580c03010159241c951828010001d4901420f201140307051142a001c1445589009586e00e88011803490400f8965115296001101454201042c3c003112040130340580201d9110740101080300d410f02d40020100f50007260140200e0304640c0d2904020281078130218020074004010320b007255202c424518032a050b00f8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 81391215 1250 81389965 81389981
    0x1c0c05060f0c060606070b06040b0109180608060609040b01170a05011a13060501052a031209060a09020604032d030e120109080d020a090b070507060906020a0506150d020301 76
    0xc07418554072034031108424500740c0014401c0348038107020010340000a01c2c60f0096074001005550202c0c0031644400140c030110724641203c0f5455088240011906103540c0145045800e54001c0d1344142c2c40341020701c0201c0004641c05000040c0003c0100f2443c00035200c0a000020715600b5503440140e255030700d03030940e03c0c00ea4040f0421074110152111074900603211044e00580c0240400825181c500060028040d0a00344005500c03d00c2002d1000c40584603050b105940d10001d9071b5540d001000124400788080e251070038144100c0b400282c40303100500c1040c405903002041c69081c24659031301c84400c2400c0401d484404c20000401d10541e00c9100c084002080c0300c0c0d21005140c05041080c00b40c0c40f00d02003000651603040c80440d1012031907c0084900c00343ca560405a035429a007034040c0c800d004654818868511300042d21800c0c03200c0070550301e050b01e2065880700000b9a9602e030880c0d071207814000180c5990450000b054144103410900103070f990016110b15980300e050380029007110000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 81392465 1250 81391215 81391237
    0x2101401050a05010807020c1311030405060f1e0f10080613031e0903110a0f03060509010b010306060f03050405070519140a1d040f08031611010b1c0c0506 68
    0x69005129a10b031504240c2d01511085c60725040500d44480001e60340d0340400c0005004070030803c03007081c121185030440507a0350782c4980b20036980c1c1043d20300b180d030765802210741d01e2601c0c41c064003290240d81607445020580c0002085500e640d03e81c0c0b00410303038049019041010342c032103030794000410100c103000951140c400c1e40700c0800500040d040103064018091031030ba880e56402d0386001c0f801900700142000b601d401110740e1901652000111302500041d0300f00b0030f030400d4588070010401070a60001e030f100301c5821009110030b0300e0900c019000d0711004d010f00004520520400c9922901c66030009500134010011140941e507110003103812006002c09968800240400900400040700f00028407240c003078809805086c50032154172000d900b022002010a01010702050500c40c00b40d0420460a401050090382ca0030001812015010350191942c049a01d09100c0c80d000003043c4990380c41e90001502c0d2244030a621408006941040c10703084400c805104004616501c0700d4018003601300c01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 81393715 1250 81392465 81392501
    0x151b0503041b0501020a08090d0501020c210f04030312150b0901110f03040e09070503060a02040302090702060613150b0a111605031f180305041805010b03040b070210 73
    0x1c02d0412640c04441d0b941a80c91240d601807040110366400980554a540c10807006a280d007078900c0006d800c5640808050800d600200d1200841c0501241c28684a614050b09003000300c1040e450410034000d40444911040042c0420400b01e406210f4260313600c1c020060000d40b10980d19124070080c01640c00c01d143e0b2010220f1ba81801d1b503004039082c00d09100c10b500804443d0382114440d5074a10850140403521899400807440c000401c11015025000040540d0030628052406000a40052000382c1c8111520b13400700e00058008240c040c01554050095080e81c0c160a0010001d8051417038440754000603940000303400002c4202524403511295a100024024240b070b0503e8041c89100d41038060084000400065800140c40d04400001c80492005858106071304001002c04002e0b40f4a0303005584064820154014000d0003a24400d804c1540c22a0307168051344200c600034029031200708401c00126003c070b040d10b9035003548040d50b44101c0360103100c0c04c10104203907954007400c1e19203219 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 81394965 1250 81393715 81393721
    0x30b01050a0509010305060c07081908040606091a01030e030d1119020319080a06030b0405150a2003040219030c09050c0703021506060c07180b0a12151b0503 69
    0x24040d072190000303100403610003045505548849803208005007c40070310386800500a410810103d06607034a1030516030000c44803100c401c502925107081150101c030300c6072034407401158030400c6202e5010402d40480c0325480c0c415100c00190020004035480352941d210620221184d9031603405408403150032180b803039071140d903160075482111900c401202e05540040c07009000443c09004101d08544480c03401c541c40381c460740c001500074100b542020382a113a10390100014008001042d050404202d820064183c2d204001c00c022900e5150300e011a070b080c000b1003100d8846081000c0c41c0c019000804010221011445074582160194011200c00e45d000c90100302c100c005100b101d41c00b00c1c00710542450b259540e41c000f9101e641c0d102c0b01e820381c8a121008156103481c0c0c1015102e03484010300c00c5440701600c030704450710b91740c956400b024903860074102c052140d410440c100100b01c070190500508685450381c0d0740c261046403002c0d041d000c0c03075903100390b007900b6800100420460312885d11081c2d500e013 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 81396215 1250 81394965 81394969
    0xe010c030603020f2d0d02090f040c0e06010f03110f0301151202030c04170f0f010e07052e0320030402010f03050105060318010b102601030b06060304050313030b0105 73
    0x128610042c51041965005c043c5070715150303441d250b040d000b1916011a0100030900001e06210000401039040890001001030000704031100324007441c000c1800c0403000d561091410200c041c1240d44500092a8042001483e0700940050041e50b881500c0d01e803c0c80c0c512580c52040750000d901c0701c0182039502c400224056000103603803003d285040401d40c5549000c0343c03600e1291150b4824090070350360f00b03c1c0c1d1080170002401004482d044900640e01c00d0000701a4450190042161600b524040c4110006041c9401d0001c4070b41101c441641c18202c4401403040703000031a1101641c8141500c0c0d0ba120080c0780002d843c0a0307440040b6034801603d07401c190000601e0440800d107800103042c0383c580180455500c1c1400d495100801c00d0000001c40315003011305025182404440341c000748606064018103800c0492604405000c458a0064550800801a41003028880641010160310109010707003000c00040d0b80c0031b40a2b90440e440d00c240030003181280001039000351050b421410040c4054 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 81397465 1250 81396215 81396229
    0x41506080106090b09012007230108040b040609050f06010e040311011815020d060b0405010806011b060b0f090a05150307060206010b160f06050103060b0604031101080a0e010c03060302 81
    0x142000b0f02d00302009504280c20844244034000b050b5050206001200c0d441a850381d490441c000f95140617280c8040e611013600c505182c0002c2c80440004a00341b461103503502c01d9058a12450300400752524075200c0351070713203401001a40341c1518240580b090f024006582000304034006c00e002d18071078100d46400c2c1002403481c0b5076019400800e034181711503030072079030035543d100321886030040c10003255921807401290080c45148020442682815400034030044003074050404c60310280c85440181e0b544000445004418a5060085a001200050201c3c1c001d903c404d4451501402d09042d4540300d100080c0f44640803550764031982d440e6000c002883d5001c040825506405030300410f4100d05140000c1c1d151103050003007581d405c40206800c206440c001c0c46464a04e43c024544806024880c1000b1000d06000d00040d5406414409500c0840c241841254201c94002940c0c1c03038135041c2100116030b4044003420001c5007a40341c03503007060021020300c504914076440381c5000178180c0c0746106026103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 81398715 1250 81397465 81397469
    0xf07050106170c01032d06030b0601020d0903080a0903140a051c0210050a020405040905060103030f0504051020101e060b0412050102040f03060b12060c0f07050a020415060801 77
    0x6100c00c40e2507801d020382c00001c00c038660034801d007401720f082e03600200030842080300701c044aa10340681140f642c08409413940000d054138000c0024003a140d90720401603a44111030f11200c80051803078030301080445d02103800703050b803080c003032030500d141617544c0c0c440681c6056040b5503079050b90010040942002030800c640d4190100c82c0c002e421190000c0c14000e9154007114858100c0e0648030303400203204001d103034101e1b0702409004004020025803401c10594505003400102c01154400502c00030141c01103098900b100c20003803464184103141e1400301d50840078080804154425501c444081200138088010415150b800028900703103030300141d8010600c3d05d030103d01c0041ca00a4140445a4041d048500ba030322000400a0a052a8a0018024410f640c4003400c4100192004020805190490700c0000411205003999000002a01d9150001960122190582002a144a103d0400203011501c0c0a070064440705081078010405a400421010b8200c900307003003043c81810f421560580c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 81399965 1250 81398715 81398729
    0x3071505090c010908030316140a030e0714030c040e190501150b0906070b09070905040302070501200a0b0a0605040906021e0a0c0807060f1d010605030f06010b1803030f07050106 78
    0x140a1711301620542c80e8071015001c100d80c00c0422000030002d41c0140e04814154003040366046d41c0fa000c400d0010010030040800345c009003c0e0520005074203043c00041007409030010080c00390b814048041100921515455061b14000c0303058100741140d44985a281450203034001045806d4084d0b022054480070342c0001d0703160030050004580315110442599107960303210740ca01d40360351105c0e50700500e0b21410f54403804800b4200000c0004140d4007045641c204c074000e072100c2c014035200101c6007041d0b140f9482a484c090380551001c0b0080341084114a40011541c1070000c1c6c20340e20364007c81c040d030740104000c0e2401a00010380042c180d000009051066150150450614144440080a0b14034000000d03181d1800401d0940034030015522206940d4040f040c2004000302c2801e880082540045e00d186907946000c1c0005214100850000c59044040c3c01a000c2c3d0380c240090307091180c009030110380d4585a90896012a82c82c100001d000900010301019207030f400900e4803e09542145d08010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 81401215 1250 81399965 81399977
    0x60506010f050708030a020403020907030603050c150d2d0603050c0108012304021201091d16050108101205030301030c05031603030f0e03011803172703071505090c01 73
    0x19103a10b5012054649a5500c580d8240d40c9440e240d0803507001c4d01603504042e501503250002d0066071b1b601540040708a030f1007241511b100d15068810401004100201250091420418405084099070003180b400c2c8072801224001d001d1150722082c0d800c2c88041e44000c0c10b984440602c1888020819080b107800d003461301540b550b04204040c80c514210020700d10344d040e8408285480c903900d0382c0569000c114801e0081c0510341e503030200c0b080584810301c031403142c1d45888140031172464800b04461605600c003a4602c80d040d4502401150403110040440010721445000031441d640344051410398580203000541c0c50b03506605042c0c01081096011034400e48c41001140c0d000d8a4405c00d0008403038141c02c2c042c03101900d8000c182c0d09000e00d1040290315518040c00c17403201a0036440d00f24503c5009944101580c000c50f80c3c0380303070f182109445034010a806102d1695848481c1c0490704141e1401c0c0e016030b4100706483c1d40d40900031508201000000c0d4a07501001000c0100700940101c50f07001341381017 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 81402465 1250 81401215 81401237
    0x70608040507140d020423070f1101090302031204030e040203161d06090d140609011506051206010c1410020a02011a0a050d030909110414030312010509060d0f060c0206010e09070620030705010906050601 89
    0x3b07940c901c594841d9006181200c07002905141c007841501080c040c001d04290b640e0301d005150240b901007404004004121100c0108558090601a940c032030440541301e2454881104100001c1503444c0c102203443c408915003600c0c80400030704c00c242c02060f40d4400403c0807550f0b68150200e0f01000e4205504115041c4000300c1c5100b03d01070b10303d4100382e089c02c1440100c069424001e6a0070150401241c0c07a2280041141100a817540102803002855000304104c41b1460440c4605141d10442598131120306c15060140e07180c06444113010034424108081d10980e03e42015060740d19070581002001004501042030850300301340081c14080440280d4549580c0c411410240308042c007403a8015480c0c000020080e8072004c40c42004103400990600c000c5085140c194050002d0100740320044c09040000540b000b40001400d000340c940c0000707040d91a00b4074000b19030440002c4a034000c208411140411201c00501c0102860783c0034100114800001c0d06000040e254050f16050401c8052111 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 81403715 1250 81402465 81402467
    0x91503070e0105161e14060609060111030d050c07050604030c020307050108040b18070b07050c040b0a12060506030106090603080d060b0c0318030c03070608040507140d020423070f11010903 83
    0x4c01d62405600492064a101290002140da0424100003d21004818181c503e000b240051100d1280d10115003251103070351010011205002500c684c404594000c1c40341d5070032400719801040e0b0200c0303180c0a507130420486440c0c0521b4440e0550f419004221546401025401c0a000030f0010382000e091030301603401d00d42e4408000a41c01070000070b44002c4040039060003502802400d00500c1031031422030300c0301c071300c1e0a00b1920351100c201560311862826240240c84d003001d070038130000c4400411a105982141d921040c002c2c0900070070030f55055588103404070b10056644542005540100001c41d00c4030700503610340e0201d95240d0032120b404c3c0400c0c0502d05010400008440c82407002c1044a417071000301d080440d240011903882c1e154580110340012403003550002049104034015021a01c00c02e81c0c039604402d01800e851141358000c0c040703c11000240c1016006030f42c0e00342c0204000070400561400400e605981940c1c0880029013441599106079030085940c001c071007002c4020084140161b030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 81404965 1250 81403715 81403747
    0xa120c08011b0e0f06031801050114010c03050a0507020603040803060102010e01051b13090204061107060e03101e06090515030613062a0f030507020a0b1b091503070e0105 75
    0x20b011003008000e109440c02d43d26151803a03405603001a01007a22801c0c00d54005410012103c0740340c180350f107000000030740c0348278081a640204006840d403098400407501e08803425482502c3e46001e001c420024000140c481c0d1004510580c0100e8109459040c01e800081c20344d02e1602c2d0400450707040600b88207180e0100c40c079001c0d40002c203140380c0f5070314281180124500aa0b9a05c40c2d0f14551000c540013070500e8000c00c3c002d4029011100b0b55100c1619101e054803126514031803150164400c5105251035080d40d40801001800d901d9903070649a0f010306401d058485079041044c61680302d005014240c00c685800c031510709006c40161005280003410040c400262007409083d80c0d4540100b890303a14124103003500342060078900751340e004042141c00b070014030442e07000d07000180c0b8007000244401d2020804868842c0e01000385400741d21024440b04608e281075080e203d928004102c8000300d9599007180b494403c1c00110043d8903481e014401a000410090303c090601008210f0f24080c510105 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 81406215 1250 81404965 81405011
    0x1503070b03060d0219050109060c03050f07030504030506190f020405060706180f0b061503060102191110030609060905040206030f07031424010207080a060e03090a120c0801 76
    0x9216a4407680c0c0c110019190b4403403d500039400200c1d900d40248151900407401c0300340d480a0301e80000640e0740703c0040742da072494507101a002840031701c81c030221822400000c00c1c0d1240070f4a000c0b4101901c0f9210a42041e80c1a02d10b2100c0e01e03180100d42c0c81a01d80d070300031480082c4e8100c0003103080601c0d00380410114819800000c00c25071b6900020030303080d007021600603c0c0359001b1803000c804400d18640305500040940d29140b00ba0b081b1007821003c0d48483c03084038420813046c4c0c0a00303c90707281c1404a02c48803c0540c0300312030035179102250640684540b102d91401c280070f07680105850f40f90444a8080b500140c001c0c3c0c81c1c13a42404104009a11444222a00040c480036903480703070360b60500c2c02ca004180813407001d12110441014400c556681c803003400c80c4031054101c44003800700c0c40c80069a8924051190003c190000120721021580903444001c10b515000141c0b40340c0500e0070005502842250000300c1c0c0c4206001002050013070152000000c1c190780e4008100c1c1d29100203000c410b0312130407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 81407465 1250 81406215 81406229
    0x501050c0d0e0a0317030702010b06071709031c020717030703090501050d0908040b09030f0715030903020c0a03060e060109050c070807051908190509090c2503020d08150307 76
    0x407002d00c142c0792982440d8400440d004003914090700d41c0401106001d60040d50221700541c205510141d2601d040f07022641c0041e071004401e81500b240d161800e03800d4122840066240c0903031040c030710b11401c0c030950b010050440e40c3c0c0508070340c0742082e2100c030f040303c16030801041d82d40c801e00c83c803000070b5000203001702560801d00f4680d489006d1040044064542c0c100300415006c404180006c0251550018203040001101619040070007070901d50b80d100c44910915281d810703035046040300140283c1c0601c07081e86c000e20584164440b10004118070300050f52045604d42c0e565610304000c0700040c803081d405400760710000d00c00e90520345210305060003540805841c4020010304902080410080d400c1e01c414264555421802c3c3d038140000c0039042100c804c1128607288000401c44c45c49141100e030a45002015198a911100200a1aa0000000d5071651480494181caa904c1001c0d00310030010301c40e0340205540882003200401ea03580142075920682c2064980b40919907020039440c2c107440d62 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 81408715 1250 81407465 81407477
    0x40f150807152f0a03080a020c06070509010302090d05060603010509030f09041d0a0309030506060102011e150506030901090501060f12020d0201030b1206040203010605031204030303090c091a0301060501050c0d 92
    0xd0060f0401c2002032824a41500740c00030303001c0b0b900307071030002ca6400b038214040d880b01c40f9103589941513001607104844800c00c0c036821050008007644e00907070207004569410314005040030125804039200080f9403134140c5555010104000703c5280034010140c0c8800d04030080c5050203034042d0800e90724011102d0180c821520b0b41c0358014800c514a01450f80c90310040110350030404c480c10090031124240c0025949c80c000d000001c0c1c03ca5005001d0314182101101c0781c1261104509902c03402407019a20140c0d003d40c0301c075400100c60b602c40000e180a030a00c0c1000252103001d030710307103203003111034031390020382d035104038017001c1000e60b040140710aa036940507200c50251954a1004070010215080c0c00d41c0d202d00d29880503800b03600c00040780303441079200303074000c000c1213440700105940c1d0040010030841c4000108024000648030750000c00e252446804c00f890720a444101c00340548402c807803030f07160300c002480f02c6030001e280c02d01650008010a0070810710300a42540c0f46903d905640003910b0900903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 81409965 1250 81408715 81408737
    0xd090f12050a120f090503010203010f05060304020d0804031407120c09050901060503010c0e030c0603060f100e0402030f04061a01231b03030417040e0105130209040f15080715 77
    0x1d018051810500d50007001000a5900a100940603a00030350071040080e0f1a240302160302d0805100300c9068940c83c070408880b491070941044081d070700040080360400c603a40b10010004d91410302070b1018511441008541550500540b880d0001c0342d8805236210380c00300040e0021520341d52845058910514011400707540b000341c4103024014580c4130540540ca03040d500d200250b030100c0e0140301c0780e40483c16200400780e86800c014440c00141e41103540100469510682440c00484042ca0145e03142001d8804d1803c45c0002000c0781c004640c031000e40c0e45000204010899244140705030046622802c1c03c05a503103200003400c06644c0040060303042400c840a022540410b802c0d41c901c05030100000d030901c0b500001141d140e410560b800c4403036003503682d0750103484501d80c4152420f507a03c000d000700c442d0780380c00108004031843c500c0c003190b0304e6400c0005a50f5a111030080d0a054842900080344c0300c411500b5100000c1c05075030000c6a150000320f000d0046c4500d1580301e165400c03507450030f44c01000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 81411215 1250 81409965 81409973
    0xb03090109050d050910030615050705070306050106050304171207050c0c0a030c08070b0406050d020d021c05070908150406091e060b0907140901080a0b030714030d090f12 75
    0x1c032040c28090018810010072900300c640c0003004010740b00041e0703100300700405201c40580c00d59102e07000780c072070080030501106e003158401c60103000c8150142007100e4809580e501c031141150403e0304800c0006000100304410701401e040641c40c3d04000d080900e00d0292080d280c00c501500240c180c4d020080001492038050108101c000b617000001001c052000d0b0785c900d016548854103100741c41c418001d01c04c0c00201c100712a41510b00701c0b5031517101c0310f1925114030800402503200002594440c1d9091121040358460180000070903148000c00117600c1c1000000903152256a41c05140d80c1d5004500c0d02066001113044140c01c03e070311034008502c048840c0380440098145c0c4480c1c0800c0c2d18103060040070701450381c00c101030302c230029985080c1940b2091000c98100c44030308042c5107034540810806803d54400c0012035409544c010001402c1c4414070002810004158000700c2803500015504c0e055203000c2c002d40002c103e0b181407002c001c82c5802540c29407540c1c24403031759559055a1144000788 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 81412465 1250 81411215 81411221
    0x70305070201080402040e15040c0e060607030809030d0606030f11090a090207020307050303070c0920120a0e0115050f060405030a120e19060e0d0b010b0a030f02070302030a1202090a0b030901 84
    0x21f03c0c40f0000d031450b6903110050700803902d0045805456202c1c407903000042118442070402d005510207071206261081c02e0700c050300e002c0f4000d000c0c1000c1d4030007002400351040403031189201628490b500410000502c1e184501070710020b031990401c0a0041042501c0c030358510095004441c14650050713214600d900010b4140f20444e80815007500000070380e0000c0205806088050ba131000604005107007100b0f490320b2240d0500d4210140e03400d420481031110a042d5890709910245c4424081050f602c80c40e503060075100321201120414040760018081868101c040c164016004d5582d941000d16040019640d05926540585a550b100c1c0001402920803030206142400186c800901078118000a002c3d0701185d01c0b07428001410650800141e14010028004075500a060f03c1c0e216420100c01401c20740c024060502817603500d044954110100340090240b00307019402458641d24104c50182c01c0c07080248072a4800c91042140103220381d00e54601e601038403140001180c9aa41d2842c0880c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 81413715 1250 81412465 81412481
    0xf05060a1502031c150b040803030c07023c060f09100c2a06020609070510020f070803030f091c05090103110c01060501110c0904020d020307030b01080303070e0607030507020108040204 81
    0x24104d4203050043c0305034503400c460341208071400c40c06092503a45981d460340d8052030107800d8490300100b0205001200c840d010b0900e0500023000000f032032100c17501c01c08120b5072020310060003058240c01c095020b00b40404080800f42e0584c0c1c0d4528000714015290518401e6a048502c00d0701c9442c1c2c0391000a01c100d078203030403032580f00342e2041e5000b40300d80803400e2400b054600c000030030000410100700180301040c04c6000c2c1081000809141e81000b0402c942e03840c0e0000c96008500c1001481d1803c4038003000802c0007015443c01039a520704289100c07442d4810300a01a20041e880303034904841c9103003028410340340c1110901d000c40d00c83d0071600040700079140044030070031240e40100701d425001c030043d0300800c11140c0988914040c1600c410040b07450b0081c10750740f558001b4100f400103015080400810141910041c103480080b52250b58039003484000780c21a46480d8008800c008007503030084071224881c1c200303c89072402c02001e036070000d0141c819800000d040040c000c0c081000c64031541c00c0000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 81414965 1250 81413715 81413737
    0x51e03090603070c0b01090204050d0b19020f0309060c030112140304050a030602030601120e0309011d0406060807080c12070f02070806090a020a17060112110a030b0402040f05060a150203 82
    0x781d28280b0510050144c600518184c469942c44400002c1c90b000d203200b210100c410141141c06203243c00d854007034020900074080040b800881d0782d12031080d0036604c01401280c1000d2149510390030648011490200010310103c0074460820051121700f0038048045400f540c800c00c0c000c1d61024014031541075004592000c0e4028225441c0402009110b47005136128079402e80e034235030074507645890040c15561004442c2d80a6002001030728004d5104803201c1048030500e03012099010b0441021a04403001a031010002403802001d014401c5c0d40291213542207095106020300b00036842d01605caa814000e01040113011008211228107802402100c0040a488054451510304841d07410303103800059030100d201d40c5518201143e01c4c480c06000b03005800f050710060040303030308001e4081915201d4000503612951503629848040e9600c8040c800610300c1508180380700e003005e10503c41901c1f80d0300b0700d8000032414902003000700e898101501003150b81c4d9908000074103149030400d0741148200340b002c01c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 81416215 1250 81414965 81414967
    0x914090d0e1e0604060804031106010f0501030b04060e0a2c0c010305090c12010209042301090b010908030309010902090a02032e091410060206040f081803010903080a18051e030906 79
    0x3580c1904005018400c41c005d271642d19807074170550b0245444500900826100b034455020034446540300c4d070320108900380d01600c0040d016480b0311046c0001e00c81107601c14000c030384686c07020303580074144500c1c92a5400d107007240d480c030002d03181000c1c1d488010305158a410107507190002030801100300036070040441c0207090365a05240f03050f003140c040c1d801204818041e60070301046003007540c2481d030000c5994040780321265141e400c03c0349480191041418440c10001303410000f0540071003d00085018404070b8000003440581881800440f01c0e009185803d254030610801a00050441c0301140390251914102c1c134501c03180203221a401d00c0e582284203444c1c40c00d11410101d4080c0b0345424001d42030808029001940d6550803039440c2d104071002403217480c506083d9000121000c01911a41b6071131303c0f910111381c40c1100441d003124211032094000030b502c841400b822030341368425a04d107581d505036840100b800b591102551202502150380d5052070b480e10042100c0401c0c003d540c0c419400030105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 81417465 1250 81416215 81416219
    0x2040f060e010b040305030d05070203070507060e0a0b04120201200f01150b030405030f0306130c0c21020c090c040306050c07050d0201050708070c020307050402040914090d0e1e0604 80
    0x14000344100d00074000e6695064002080521580c01030360101c039400f00003546051017214404020f0000a8215015403105000364400240c0a011100c094030307a0341d482c3c10311143d0103400c01200b0b1540e548800f501c0d41c002c010601ca501101818898069028208410a50f000324448d040d00c0f034614960503031710300a020030305000d1303001900148595600358801162058440d810040d4910056030000d101d541300b045034005070200385010b554060001440c4426820500719001c0958410410705800500009130700c60400c1460070f010414900201204c5c00c03031085d9020040e41e0340101001c010b1048d2941000102c46d6080d5078101c1c0c018560140c014020390900c401c0c6c52556170002141119140500740a4001852051181c180b045001382d0380c0c6204c40d00c500c2400d0f01c0551440c00180e07014081c550003c40c1940f682d000800c0144285e040010f84441c50203005110405c000e000420700d900f003042e002c1d00156118900340a00e8a040b24025071a0141b94040c249070394241c10340c00d4002c2008100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 81418715 1250 81417465 81417491
    0x20105040b3105010206160206010302012001060b0a0324120f02130203060306130b04080c0a1a010510020102070b151903051605010309021012020409020c030a02160b040b13030204 79
    0x9901c11901c017a000c41c3c10b55200c5500f14403001010b000b006005920060042001d58400e46080092941240c416034442042204160035114a90040c1c803441e400001e9000c020390341842010003072aa00c40303541340c08140c0720707080300f111104a10400000c03036020b0702c80209100d00400c40c911b409a004207852006500c1c804401c020350011240c580c481e00810000030a1441300c0103c0711030b001d40c080b10f000082e546559442e181c80d00708100b07c01c0107100f45005400080e00500d108000101c00c0c60702d00d5550762400007080b008407100345d4007108590040c84910001076440da4242c1d0024504050b032203e00f50000046036016200e4000240744618054000085c0070303012401c500764034038800d0400f0550303842c0c60054090360400c050007900320301003012001c5043e100e5901001d0214070b142002d854a950303800010142e80054200c00d4030f0f038000081c02c0c000107030104075580f05030301085e441143e00d03407402540000600507449075029034600003807080c0d00c0c50072405060000d11307801082085540c001d010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 81419965 1250 81418715 81418807
    0x40905060109150e0403210f06080d05040b04050f01020c190905010e04050c010e0105161109070201050702120702010519031d1c030f090b04030c1e020105040b 70
    0x4188000245003000f0302c200b1000c511800300940306010095105a2903582d030072100d14a41501034064075044c02c001102107c0b03640601142114002e0700821a48d0a05079500c1c103185d00f4800303c4092200c00c01c07081041c5180c030f0302624212801150f001800d0181800140d050038440e40e14554098068000c50b001c42c1c0001140400f9074040301c504202581c1c84060400c0592816180076115500c442a5090f003036100300d90180c030460041c5021402e00209699107141414074600854201c0110020070100b8140a201990310600030310090107582040c0d00c0203500d40544c020001c6501c000000c000017564003403022594070b51241c04003503100e001038a0723000b001405903a690b043d40c41c0c0c0700c0817551001c05c00050b04216401e0b003c19056141d10280c130303040d4014079401c001c1841454031480c00201140c80310b1a030502c030390f000380c4074264200c43c1c0703180007002d540e1050034446071302110f00004400350b6845030542c0e0a80f505015020343c2d4014840000b203962020019144292000f0407556500481c092 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 81421215 1250 81419965 81419969
    0x303050a0f03060e0f100302030d170a0501030b04032007060905040e01050c0901050c1c020f060106020604050303042004060605040515180405190e06011a1606050a0b0409050601 78
    0xe69000c1100e1031462080b4169401031007051440020700020a03600c035200b0a20a401a19003d210400a82e4070303070100b81030030494038945020841100b48424101e106001081d072144504d0700801c4250305560792004000301c042c0014081202e4a070007103040450744440c2c0c14a41082e0300482d180d0b640d403544001d11180d024002c007402641013002d0124100b07014050540107003601003445060141203401150316402402580700079101c0d000c2d29580ca243c900e4180000c1940c15805060202160401b0510700003040c0c4c410b004650040c03080001180003c070a80e80c020303500c000301526400066203a0041911a004450750280c82e2103000168103410070020401c46106403012910241210b146003514010800b941900c404d6260301e1040c5840d041d0312040c0e1000720450011034201c65440c0b0581100c00c803115160959002c60014858211216020048200300080051510000b424101e0b400210000010202c2c0d480c0d0000c82c0110b40c00d46c21074006080041d0080121b000d050801680e00da1080c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 81422465 1250 81421215 81421217
    0xd0204030605150301020304030e1917012a080a090201171905100b030a090524040b161d030c100206012301020a03110102070f150509010209030c150c03040303050a 72
    0xf01e0b0072002c18181070003070300e21450701500c03a003464a9540f030070f11080480c02d0390540645250444041035446035080c02010312050300000181d040703911400503078000e85000d1450a640f0310442c1e041e0600398441e080540c4507403c0240030400c1d032014401038407901310b1003041c0030441c0940d02c10810140c40110351711a05042e5540240000c0c0c6030540c407140801410300510000540410004600c50540d0b0801841c13644a80c0c202c400c24143d02640e02e18040418142c5000d4407182c1d0103210610444011090700710207500e0801c0c00200b1001030103030466081c54031f80700100c40c103401c0038651a54180f20240d02c3c414054540100402c41d090003d4441e40c003406560405030100303902c00d10171001202130a03070812042e0001c0c0b44854481d1000c1d40c2c0950702d001c42c4610b540d002c011042c0040c0e107050010801521502024805e0a5510031407003d0b14001081d20410303070300c14031104001c0d940000b54100d144e5029942e00c034809070355402241403489031500c0440540f100060000401d5485801400e0070f4550b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 81423715 1250 81422465 81422491
    0x30b0112060b09060d02090405150c0301060315180902040609050c120108070302060301051e040c030c020606010309021c020d080711011107060801090507051c05010810151a0d0204030605 82
    0x1c0202042030f40d41c0182d138281d41002101c0407030001404c00079180741d0894050b0089503001034480d861005514000c0701c42c0070401c6d10110040168607058007402660404400050111500f0040300c0000102c0391110440c5d2241c94101007000e640b100d41c0940080e010803c002d000314a070202c3c10f103246070f0155103d03800c122030000000901400100c2c9913019244e00400c41c42c51646010108540070102060510424002c0718150382c480d03a0f00d118001025810f40c9000c03603244030001d001390400e8030040c40c1a0515003482c14001c01640d80c00c94006221080090704a42c400060000c101001c0000c000100050070004100f814840b44054440d101442683c4200f028088060510745503a01351180d1404108000b0051100d500390790042c2e41c2c0301c035076803504906007280e90700d02e1040f1301c3d20703203146403c01036aa10050089043c00d02411000031103c8205120a602c1c1c0300c202482d401161055054203110640c0045d2000c00c0c5008841035840810780075919140c4900340503000f4401a5103268020744 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 81424965 1250 81423715 81423731
    0x90504020f03010e071710050a0905090a030513030b0a020903010501150219140d0306090c18031101020a0b18011802011704030e0402040602010e0c0612070c0804030b011206 76
    0x1405008448107210002005410b6910b0400c001150001c060034100620540c1c4603501c1a040780c3c01a0540301d40e04810881003060301d01401d101c4c0c8181c66800901145051070300b040091540041d410010740e5043c500b0703907070301d050403043d002c41003403250801810401803000740311240341ca94002d00b4035003001720700070002c0d0f0741d88031049581016102000000f503080740d50181c075000c000850081c0b02900400c400254104280800c03414802c20061000201e030303407013005209129880c07007a407211050a091044400e0140c00426842a49522004007045036100201d15182d01c00e008000e440c503404040901c0300d0800701e106c8441d00c81442600e001c1c40d840c02c298a01c0f541c9100d0300710382030540c060711341801c44c03420076290310701900c0010801d600f8000d003a01e5050440c2c94031710041c4010012640009000c810a0300f8035820000d000700d5061050328240400d12410068070000c039003166260030103c42548062030080315500940d400903000301c00c0c41000003524544207105581c0b841c4a00340c1000800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 81426215 1250 81424965 81424969
    0x5030d030506030a0b060f040222050a0503030d1505220507020303130204050601140a05040e06271f03030908010c0c0506010501030c0210060906031209270209130209010905 76
    0x71000c0300c1c140d03070690044030040d0215100c0406944c000d100a0060035459096201140987c0e104e000c0b468844442c91707210300c4020010700c12400c044c04013280e16030921494100002c1d078901681024110180c0d94501c4440742e4010450910010400a044941c102c1d400c01d10840d90580b01c0d03080c0c00b1b40e250074100020b0310300d480482180c1c89680c07900100170307088a180c0c00713120007020003e00342810b018050400d516040c3d0b140000e07180042440d6a081c1c0d0f00c605080000c00a840c0203031000d0301030140c0c030f84120a0304c0d244800e90350000300c03440d806840035698049032221044c400f01031000442c12400010051541c803541c4c80040e41c0440e0020300c40280c9101c404c07680c11822100242054200c8801030000303611a0b080308000062a20480708100464410b0004a42d220b50220003419a500c80803c00c0055051345481074403054288141003614185004000401400b01c9180740005210860002103007035040d21100480a850005141e03800840900203521203d115404510f40040002d818 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 81427465 1250 81426215 81426221
    0xb1303140610240c151e0606050906090402031003080c0d030b0303091003020a03110318010605010206070206040609140d0801091a030a0204150b030907060e0105090d110105130e0105030d03 83
    0x145105144000070f26042c0740080700c028520b000100d88851980c42e050800589078002c40a03d81c1d040c4a03007104010401c030303001c1c1c101c603850b0340600107101051001590300d0340c4d142c0a90f00622001c2d500941e607a03903000b28001360403440d03400090140300301203102d11032035000281c0c103080b01070580ca081000c6a10302c801c040c0c0d00d01a44180c41e41c0003010850420031140f20350094142c121441c10080b40e01d02d0068141000c1d900101c50034902100c0c0481c3c1208200320034010030000300401c2c000780100742071000c0c0094494100420240040d0385070b030085410031a5084c00090702d407036030364103803004012084801070140c0f00a00c02c00302001d082840b031030444001c80c02c4550003200d00800030b0502000b990b0034400601a00310192890440200c4c001655181d0b1500452003030302040040d2041030300300000904454405401181002401d0101000d943c0743c132800550081c2d00940003104010b04100101c85511503c104140b000c068080d0002d1100030040325076050700c0c0d040742138905600f5940310450403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 81428715 1250 81427465 81427499
    0x70203060f01051c080904060b09130603080403081e0f030414070b18192c0c03070e0310020a0314011505040e070905150d1b0503010b1303140610 64
    0x1010181640c8109801300ca070010346003044c0308a68050800b1900000030f8115580f6038003407a1170344000240310f00c81d40740034524a4001304401800b0013031f179411500c401100c0c0c02140001030410400191031701a00e00c0c2032010030b1604440c0c6480c03da40710440c443d9000320f83c00544049900b45114004481401e40200c3c02105036102c0c3c040090800d446503100c034100081c03481c00c090308280002e08a005100d0701d0801500640201465071580c0f05900700201040b5449040c5030410714108801e0200c00d056190440e034108e039061800c54084982c5000180c14030640c80341c00009548005188010190036800600030411a5001c0444507a1b8541ea003640300b0924030300180000da810003050101c130a01d0000c00790001103d140039030525481c0d0022403103c4030400d00c4010300410104803905408420302a040c0c1c000e014188480181d42a007a018105000c10301507181d0702c03000030400780910703100140748078020358004000d032200480690180e52515016185030036600c002c62408200030410451482c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 81429965 1250 81428715 81428719
    0x10f0605031f060321080901020304020607122f070602010b1008041e030e0f030c010c110612040b04060516080402013006080708010603050307020409020a03050607020102070203060f0105 82
    0x342c089901c00003040109010380c541500165540300100102c1c000c1041418218402d840c8850200d81412000d0000301c4010036040c071030b038010010400140c8444c402d0b0350300594441042c1c690296031010a6440800c4a40031000b281c0c043c0e040d9407555440010880d0308100e215040e501c0b601d0315002c0072400c0c3c688240019070000b01c02e80088491030f2141000741c1d401400b80b00d204213410031360894aa609410369030141c001405c01e20030b0508902d000800750030201421001840c54a448600103040d06440860151101528441d0f0914986078003080b18051a52071201c849289401c1c03820000054007a6015982185801e00146102010504201401c0200d450700116a59603900455406800394580b004054580c00311040504030141da20580c00b0001d03c01003071a0782032140007441c01100340e100d510141c2c180fa0017000800d2000c811180c070301e80c040d039000c13a00c0421400850940310290b4001001480780d5000c01c84440d6065001d08141442141520010307295803105004000b800c1c05060307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 81431215 1250 81429965 81429973
    0x90c040e010c050412020409080c011b0504060206070f020f0d050403120e0306040b06010c020405092407091e0b04060203120a14010909060605040516020f06010e070c0305040f090b03010f060503 85
    0xb0000310040001700d607400d440140003080c143d0343c60781d442440360407000d10080e41c0c2c0c1d141c584218506c0401c4410080044403803a0590074940382c590000d6942e17501402d1101802022170503128074510912107003041d100c6050803100303000142c035801803240e4420310041d1051000c54244034600f038800c0c841443c5244c001030081600d9101c0351106811103002a0156040c003050b29650790060f1501d004091041c00c04002800c007a1405000f050401030424400504081004040010175034000342141c09996880005509440007054a1210300b46a500000300b20000454006402030f4000014500020b18800c0c0c0119070320761400c04c2d8252003001d86101c98100b00344006100e00f4020f9071000000358024007001c540603554501050840d1415915815004581800c900180e50100f109200c4000400c004040643c5081e80b90b240d01341ccc02078614020004103002031b10605200d1000d8030701070000769a880140590701c1c40403034002d00a1002c118000c0d400c00082201e83c40f000d110380030403a18094054 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 81432465 1250 81431215 81431219
    0x30f0308130215190c05100b0609060c010615020a03020616260108160e0402010c03090f080318010e0307031b0812091f09050112060e090c040e010c0504 67
    0x340c5034040000c0260882900101080c1d015035254640c2c005100c2010407800d9490a00c2c0d50101101e4a1610360001032000c0081c40c3c20028200158058080d0361300c0a00042000c07130310700001e40d03074400d1091140e801080400c1d03602d00008103510150860700c08041007a12808083c00a17a00d500c441c10000d40940c000c2c4000403146038190341c803042d10540710f1801140c89c01c203491600e4041d4032070240b41c210041522005010070b4070104403008003c1400704480d83e0107440c00340100c041c500700030302c028100188540b609040602078200e24001d810200305e44000235072a840f44d66501d030001d0345001c440d0f040c51041c0380f05950080906151112016002e406260300b035483d0030200082280040317003038241402e07000900c01c1091101c01c0751441d200e6a26176407540304100300603021200c134032034075141305001c50f001c98555000528035044410a00341079403000d000c2d1280b4401800c05a1100e4880825402084a1800003150041d501402203804005040c4102c5c801400c8070301c02d00d404070204c0c00030801 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 81433715 1250 81432465 81432467
    0x1208011e060302090a1503060632090301090203030301030f1101140d0e16030f0b0603010203090d080c12010e040203010501230409050109021518090c0a080a0b06040b0c060c04030f03 80
    0x3000101c1000d4014030300b469030b607044000c41c0c0c41a0010300000030323681ca40910109070302219514419100c03021021000b884541c5030700100010104240001d0b07000200708100c1d0b01c080d0482c02200f0340040c2902d03140d696a044c8078000c5584e4201c2182c800e030222903541d9072507009550100d100303400507104908241011400324014041e078031100ba40c03441095401000c16000c0707880c40d0080c0d072240e030281d5038542c01881e004880010180c04540300e070b40140100089007000043c01018107205103401c6a454440441d2901e00344102c9201150311170f01c0030700104410102e0000d560060348254020413560384d0700e52040744031207800260b45c5c960f0004807440c1e1056140641010346518080c0c030001501840703a6000034201e1306c20b0310143c030030b442d400706950200d10300d41c001c20030745440199141c00d058502100d9000c0c2510034604071005010f0751502044008d542540013111400000d014070f641e841e198074542d4803a4000242c204000c1c4504800034880c1c2c1d0414040d1811a03a00c0f0301100c41003581964 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 81434965 1250 81433715 81433717
    0x50a0e090708033a110a02060105040c08040813050303040b0309150402240d050709030c0918030309060e0a050303061212030403050c031e0a0e0402090108010e090102070209041208011e060302 84
    0x180c04a00c201188584813000307281d03031083c00d0400c4501c80c0101d5484102490103820200140d00082c4160b160009070f01c503903034120319816440343d886540c0d203664801c01411035002c80f620b41c04c00c4c4d8062001141c0402c0711410a0000c600444401e400ca480c48543c0c9540200340d01c00c110b40094100e04101c1c0d81843e0017043c032000c0810086081d203501d09000315005d0a070101d40c0100c1d11035001407001c0c5800c00c144000c051b40c03d0040e05007403c00b440044036007801c4105051048000404241e070301c00d240710505c00d441c0d0114401e80c100100f82d81d0700503200d040541c0c0e42d40007502d026110f034100c0103003007040001c0044c00078452071240344070600b50368541e2802d44141d08403410b20903540c00f08201c8000c8800084d038142c41d01c600484801d40d2540d400120042c01ca12001804500552040101c41c0e8260b0b00f242109045a00908244600742d0340c42c41c42501900807c440203400c20b000909100070030429200c00b80c03070100305580785280c0fa03a84190b0201680010084440c100521080c20f0045902c650 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 81436215 1250 81434965 81435037
    0x13020d09060e0a1703010e13230a03030b06040e040f110901060807021c02032b020a110c01030b010c0305070c0308040305060f0703020307120504020a050a0e09070803 73
    0x900028001000e92240d40035070354580100b41e40e680001c0a05410000800790b98464a0f1026a40c1401c40d03041c81420410101702800c09030118070502a4801080040703550801450314460122030710b01c01311443c0d2aa6111100c00c01c40110381810041c58150800c54140c80440d016042c4908180c0c4903034031035081c07107000c1100c2601da400e40c1c07054500c1551941c2040b98000c1a40303691300c006525042100900342805100d1050082c00b0800304540e4040c1d000041d00c2c0d050400440b4a84440b040300c104506052402c0482a249070000c42c12610f629044900c0c03d42000ca05003d99504440810044040303030200e0106e00d0105041d00c668001003486000580500c600ca95174034a081c0d900c0743c944260503001030f801145c055210401300b010225502943c40d8102ca21401c1c20350960403c00b00142250143d800c0e14a9075655502c0041c080d551145d46c12001881c010b02462200c645aa1280d070101004031040c105c0c600c9100380000f071501c80041111111641501302d5154040c8030402840d9140ca40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 81437465 1250 81436215 81436237
    0x503011505010e06090303031306050a060e070e12010501060f090b0301060203030c070c0e010e07030c0806060901030f0b0402030c0c0f1f0203040203010b120706031113060e01050c25141302 83
    0x605c422240e54500704000c0d4050514080303410011019482c00c1010b540c00101881504c034104002044158500d00401d034100311941000d0342c07010441804607200c401c130300000c0d6079103600309400020010707040340c000c10413040503640b0042d425031201603820240c8020b10442d8010317403003000002d042401c0c04010b0500c95108a643c441d410396038030308541c0741000a0b0004440841d110050105041d00340c0719030f012400351410101d421b880e061001404034016000007905060302e5940040c1c5000c00c40e440403103040d00040086440b13040500f0b0141c1550404000c2e4140b9114401c09000f0805000602c1c4100300d221a44140d407c4200c560300e1406500007030401c030381541d242d140d00300c001d694280219810000740c000905086241c0302c8014141d8213044001300542c001005010380c0311419906881c19031750320b801c1044061594000403260741c0301f4004140042d005900020343e1802e17080c1c5000d9030090382043c114000f29100c0f8407404c5503a4a0240c183d50101c1504414882c249050b0081c102000031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 81438715 1250 81437465 81437467
    0x906151a340503040608010801090f021207170d09060206090718020c011a13061a0a090f03050304090c05040501020309131805010203060913020109120503040b0d150503011505010e06 80
    0x840500340e8100e1680070007110907420110341805071950120125005044250080c45030310071688036220400b12041000c0c0c0124030311410b82c0702010b0100200307001000000400e0b41135011090303640341c6496007080308900043c2e1100c00066182c0c4005480c40c0200d40d11806030032040d00d040790100b008117044c0b1882075040d800307000b11107108000380b1030032040e803490750701c0d120354860140308001a00449030250b011203464120700f0701c42600103100c045242c03000c0e9518141e0f5030081c1d010585507540c0940c8000c0340e03841c560710302200700600400070340b08441c88400c051044d0003194a0543d05809940580e50059000f484416010300d000c001c94400d4803000b07000081c1c070380349440a0be04040c80450f019242d6a40000901450742881c05000b94041600041c0e000c1004203540004c007842c1c054402c1f072004400f8203043d1005d1000510840e001015014901c0350381c0d00c422020503024000d1810280026440e0b1040060103003018040d00c0c030f14018801c094042e90707003410015106ea4000d02451504440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 81439965 1250 81438715 81438787
    0xf0804051509010e01060b0a0504090f02070507060c0c0501030501060c02040203040c0801110705060c0703090302190b07030906030506011404091d150907090b030604020f0402070203010906151a 85
    0x141d94012903008000c0940040f8190300f5003220b00303080d62140c0c0d002c140c80110810001c00440d52010036141603540328500465107003c03070f00e020b0000c6d02070030f50090028001c0c600300249a50300310f15201d40b0302c1c0c42080c0c403408043e0b5440040d000c0b02c00074442c403000b00389241011001490154001c59005105e00284c0303d0b0301d5200c40c001400c403580c22000d6100740200081c00c03420700904028081d40064280392082c90003440d954024a5043c032440024041c00c03001c1c810414182e03180c5013110241a0803102a9251300c03190500606552803071094101280c50240441d0465100d098030158601400d00389500e03051030421144d000703100002c803944040e0106007058205d00c1d024840035604020800342d142e143d042c02241c2c181801001c0d0b006e11006850404014a65140482d540fa8050f07011151940e04a2070351010030041d11480340005d6140d480e00000c0340801c00710ba881100c2224010810102d06ca444442c107890f131f010410782420300740c0c0090096842c501144805804600081d181214540d5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 81441215 1250 81439965 81439993
    0xc010309050f1c110304050a090e0708030715050601030506030606060a020705061315022a061606090302010f090b010512070308030a050105040f02040332070f030b06010f0f080405 79
    0xd80125212550314000090303d02869600c58020208100360350f028514051802d00010300b611900c0c861007141540b1f43c20304008009060103031400604901c004c0e03035664480b0346801050464081196002c082c6040c1c08200709520078820144190805001042d06032183d208000381c54111810303060442c8144a00490240c888801602c0304004070301c00086460f0401c140161b444104202480c2198002441444810303800c44c1e824071030b20309900c4840a0084204c0208a080c03090700c4070340340d1150450301c1c40d0080043d2a0702c1803520700e0007079000b0004450544910401d9812146e80940701c01c5440740180071a2030182c2084110007038101c00c0700c0706a90b0740e580e0032116400850385840c000741e80c0ca0041000b418140240010021802011803030681103135205800800315640c12112850b0038200700b0790752036004004954140c0070f0000c403403006999010360b038043c0c1c445000c1101d0071034060000c105103500440403c03135a115075445d050703001d449540c1c00700c40e8901c00900641d450b100e8074111140d80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 81442465 1250 81441215 81441223
    0xb0a09120b0403230a030209130902010801030602030408090918060a0b01052b1404050d090308030f100302120109020f090c030c070302030f0304031106060d05030f091504120b180c010309050f 84
    0x1400a600c6c05078444041030b00300f02e01c030409250014440d40c00d0020990060f86c1c401c0103141035a6000381e0050300c0391524200711109009001d903003a04000c1e04d4061006c0c4080b2085200c1c03440f40f0080440703440e9500c0c00903110940e441e40d81d1507804a8400d1082500ca0004080481d42d600c030354414402ca07400c0d9072002d44013516010481740b41c2c07075042c250500051040c1802800d08041c103d00704040c80c28590b6494020a120040c00d510030401c140740458681505c55984000546d0010214020782086070b40c0b0030f008000300e1004a1260003018084416800c000c40800d01c0b07182e100215604517611480c400c03c440e80080ca0480450004000e541c8544070044091130041c5d00079980e5010440344c05100c9440c0c900c014140c14490f1685012503000200300004030745642c0103c07040c5035101c529040c0803500c503500e40b000258290070042004103d40c40c000840c814404d001e61a1412a46c0b04c0724840c009488540c40403400c59006501034000f83d500903084030b040130b48200f040340d241e003a20601413414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 81443715 1250 81442465 81442477
    0x30607030504050f0304060e0108040303200a1206150c080d1b090b0c060103120509040f0209040b0a0f061805040513030e0402040524070c0b0a09120b040323 69
    0x1180d552010300082c0003040050182031391380c10340210325040c03d040002e0540034184484034100109140082c04162290b040504c5548020340352080c5c2c649055001c00da00d4005134000710000d40702c10000410610700b402210201c691804620168901c8010300f29032040c020801612820790401c62041e040d402803090a001c00405401e000c41180c6c80d80008001540c954800203101d4014085201c0110001c200d0740d0449a01100c4500e59140b00501500c1c9405581c420a92192400354000e001d52030b140c00601d80e243c1b04450070403698224400702f00190307010340603444910b0515401401200c0c020705040c00e550801401c4500003a64600004066443c11240b1600c8240719000740c00030036030030941042044404a030f0079400c10b8140400709040701d403030106003203c0380c0510307102c9003058005000701c502c4a81c1162103ca01c158440d00700b5111a8456102b600010701910070000e040945002d4402401c0d034030829547c8030741c886403821207484000041d144803800e41c0903405811144100002d00c6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 81444965 1250 81443715 81443717
    0x61206090302030f040f050f040603021309030207080f0102191b03030509070302120102090103060f140d11090405150a020307090b1e0a0e1e030c01050310080105010e01151418030c030607 82
    0x8a290807d0180300d20821b440c100c09000e981021000e0005a0b02c49500d081c0c001024600016994042d00b022440d100d01607100b200c05000e011f0403410a4030041d0000c0501c40100b004040aa50241130200c0300010768500380d4001079158110b084c0080c0c401d0b00129005281b160032a440c858a940002d002c5c0480c003248004075079400134102e4041d582601505004181011a0451562030000c060082140441c0301c00d10514a40c00c500741040400d0311200c03552280900b22041924042c40c3c07180d07417130b05080280240e00c0c0c840c1c0d001a401500f01c0c02140d03c611110b030f54880181e0319088000d410354006a407020300c02d0403c4a003c40c40082c404000e0584e4100d07540c1d807081c11003040b2092107810051010801c5041402a44000f219100092240305554081c6413481d640d64841c0504620000c2580050f4015401c060000400542100d0342074143e542e0000300c0540d80401003400d5512001401c040c240c01c58080c80381c040c03007090011403400c4030b500c0036094038000010303880002d00301b40302211420 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 81446215 1250 81444965 81444989
    0x1e03270d0c08130e250e0307051012060807030b010b18120a060c200102090f060a0c05070b0909060d02010e1c05120403050723090c0c010203090606090901061206090302030f04 77
    0xc294400ea08003240032042c0c5c5820216506512500401c0d21000706010b6a4020050040500c0d14584071320300e41007540d0700000c000c00c038603610341002c541c8440261209458068010001007000e850480803910441d10014401007806010028441a5441200b032842036000d00079400c00442c1141c040d442d1032407230329900e0b81d540c912546540c0c140340440203407040088c0e1050101e8051070b01c4040a0074484070080780e0058580b400008101c90018201100030200d005030100000c014803032901510055008032410069955203c0c06e200304050b54007006400600b480d980765070303139062000f41e140300c1c07a4100e1000c074022203064480f00d00d0006130424031082d18000150070800e000b0309000c91000317868595030b8a07100c81c542c4125001c0019032801403e10518500b00800e8009040c0011203001c4481c0400075510b0b071401c80381c25500c684046961074000e0303441800181d145001031054005985190091420808103922002d00a2070010021010b5210400c2841e484134402c002600081055000d04 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 81447465 1250 81446215 81446251
    0x3070609020312040f0b0c16030b0406060b030f06090a180302160518070509010306050409060b040f0203010f0303050903030c0a080a110c010507081e03270d0c08130e 73
    0x2243c9803014024a04696a1050200f84109520f141c0e4107001c50b04c032459002d4840e4010501141031001610081e13000d0102c82400204002c1d460303040510540c0116400c2203187d995210000d40e5100c100d9603952000b0045000075803514000c800702c3e030440305030b05c00012a440c1c0003440b42110210300405401580c0072035003d1b0020707000342544030060f000c00c1c0c4120007817042c01503d00c3c40e982c03005030110b42405070129000409034440d6105100070b2070014414050704040b410b005001700a0102c480d4003c5003000c0c9000f1211a0a00849040324070b00782e0781d40c246906c1c64804440d41d420078407042c0d515000c00c014203500741c0d4081008404050190200b66540c8188840162100d00081523240154114110b262416030300801642e88658001001039950b00d2401540380c3c107400caa0258112804020040c03003090360a420010b007203030488955488010810024090b1f40750f01c50340801c0c0000d210100582d0025400e18081e10002c949110990442521140c18030f8012002700e403c4c190b041902d95003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 81448715 1250 81447465 81447469
    0x30204050108150105100507030c1a0a051f030302060c0f09090a14090d020703021c12210203010810020f1306020d09061707111e0115080d09030f0c0302030307060902 73
    0x43c40c01400100c0b2008844020044090050302480001034280060100ca48c005c2c0401b00aa0f001840c1074801400c0c02e5140c2001800010241a21070440d2006080001000701112080c030205503501900140031955901c0c0b00d690f5968032020306aa0004410700204040740c0341c5412030f9000360104000858444000388104002040061203030381941d0202401c906003517000b00d600015290140c03503240e0140f50f00d40303a820303902e0701c400c40040c5469000e00243c0d9189901c800000c80c3c1481160600d600400202c80c04170a90100380034107025900640d07403c4c0802c401907030042c245101602102800c0c101e074105207280813102a0f00440c01b680101e00180c81f0720398001503c03009081181000c004141c0607900c0c0d056032841c0201000c0500000c4941150300900420020001c006480d42030802e0305d00780000b840c040c0c03602c2e500803500d199002001044803d80480c028007120030729601d00c00d409203592600804503c200781c0c2664510340c20040840941c03000d00003848414014580400d900b0705500c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 81449965 1250 81448715 81448753
    0x180605090105100f0506030a02070f111207030c090b120d02010510050a030503091509100e040501060504080a0f150507030510080c0d080d0e0f0a03020f0a08040e040309030204050108 80
    0x81441e80c074038030f00c050130b00800c0d40580c03800090ba174003903407206e407260b841c40703981c80080c80398903400b40074039040e2100380701003084c85280e802c441c0c80203441101501420000281d6260110300004050340c0d0442818072003101d040c1d100f60103042008281451090003d40c05504080b01c039201070005035140c000300a0001c4180e5501c0008100c180c40190301c00d031440c1c642907107a0107262103061180c0075001c00f40ba130b400d01c0700d020781c2d41d5035000510241e0b94030041903010780b02a61184c89240158100707400003c0090103070040e40c1c101d8200c00d0280c010340300c0b20354881c21035450302038088031803004580040703000e1119403203218483d900c80d441c00903090078134a81d1606d00d1100e503031041c2000d60265000300c42c5a00c2c1c8070001002c20b51720004241c0c5411021100c03a014214803294500180305640010f5440100040d00c8d0040754001d07025100c0d41c4891040c4580c50729609480508941020402080380c84030410b02503a12500901c0c0c81c00807540c50354001003e50384280d000490950010002c01c50340034500c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 81451215 1250 81449965 81449971
    0x1090b01020a02010519030902060f0405030f010b011e02010e01060b0301030201020f0604020109060c02060702031203040308090105040c031709040c050d0e03073c08031b03060a1701180605090105 86
    0x1000502c082541e42e40004c00900c00e00201c011080c81c0c41500c03401c01c41c0030381c0100c1a0258000c2800380c9415038003a002c000c42d005441864030a1160b040600c00f01c000600c160000148103a4500c054245c10a40410700c1c001c9204807031046641e140c0b600e9503041d000b0300c10315011740850079045a0b607505d1400020324040c81402c40c54090303080b04090200503a00300d45c10700111403e83c03c0081441e5844d00000c2e0343d5014080d0040e402d401000c00f5580603c002e4070017180f00d54400e031101c21042c0c5441d10418220381003280c004014009107070701800400c54450144503185140e0440601e481254004101034444500fa03075000310350082034040c0c0e840481e014400039405134500a50500b0f4003502d80307440d9141c5203011078020790209242911402d0802c10322010100c080800114026800e02e0310f00c24a03803048405500490110315007082641006081340d000e0700f070083c43c0e40c0860303040183c010800c048c0014404100e41d681d041c001100100aa400c00e6528011900024145480105642034030001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 81452465 1250 81451215 81451217
    0x25091401080717220c1d01030302101107051b0111010e0303010314010902060313051603020d150b0315190e1c09030803090109120f050a030506030319020601090b01 72
    0x2802080b440aa000c008103507003048820381c000140d260307102680407091103504910881d19070311a260060054804c0c554081b14804281040e04c4065801000c0e2000b00030301008006801c40c2c01d0000b40041190040d40429411600882c640032983d130390341d89000d03444180c031801d500500080805c55070b0003182e01c0b03010a015600a11140d40c2c1e041a450b10fa210500008060300f01010b60780080000941c00601459030140040f03580e03040c40c00c0e4001c0e100c40040d1084401d489401211401c0c05100e25259045950141c0401404100b541c1c1e01e8003417003828070f000c0130000e40d18446045542d404011a48a071400e49021410320b0410440c0c8100941940800d04003407070030500c4094403501c000595020b400089294038901c7d680060b8220341341086030f440138161040c0407044c03000180c010b50045070100d10a07018805280c41100090b1403d01840d030008003c41d006101042c2802e000b50003860f40400000c0c01e0300d00c2c00d02e1610100300445002040380c801688a040107000c03000252240c12001402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 81453715 1250 81452465 81452477
    0x308061003061a0f0d0204060903050c0609010917160902120f0405030301120312060902090f180a0c11030309011415060703050c011e05060f010903050307080325091401 74
    0x10003901220034001000042c2e501e0f40c0005800c040b800c0c0c5402a07a07a8400211000d44da00e503540c0000034020340381800b095601c0e0040100322103040c9014002c5903031005040e1281c1102502d084880d10846074608044401da0041062b109102940d1415443c0944161800140ca4020307111588405683c001c209841a4144c04140804540b00000707481c1101c004d80d04900480480e450708840302d19410188440203414060045880c0b840381d00542490035043d5140e0210f00c105c4c80801014110b0384a8035903040391a100803880103440c5070040c00d035110720380c14000c0700725403510140d0f4a180e00481e81030001341d6448100300380d407040c010481500034100e00d400424460382d050000352a8494850000e003401400240074129a0003908034444041800b1890004c800d8480c10b41030140c41c00b191034521030074100d41d00e20300039802545e40e07000381d82c0c20100560a0020b180c2e6000e18542c006001c5001060328201c000c0011a440f0103600d00320340c2c0c0d03a42c842c1c04143c0781144030a644e819008825041c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 81454965 1250 81453715 81453719
    0x60503060f0a090302070e01140103110901090303030b010c050a06020c0106050904050d05070c0b030907030506090f0718140c070201080c03040f020409030908030d06080c010306030c141903030806100306 89
    0x307955400c064000b8038078240001c01076154601689030000035403140402d481208000540303070807905032495141070281c805009001813580001c0540c807038018014081102c00301d0501c00f180c8280e00400f00d118041c10400f82501d500d40f0355524001c45110200c0b46241c0018086140c03010070f026420090805440840c51801e0030b58440780c440007049114030802c40c0105e030762004e20402460300c00040c40509112a039904100e00700070b0300d5441e036000a6416204280125070740300c4e40000c020950003c0440034000a0b800d21100340800201c400141c1c80c41505e4a40d6000040c0c400b601c01405080d00340100c40da07945107880090074000d802402020580014410080424059800101c040e41d048071300213402c181520302528018026086420244800b04101250505540c441c606840f0791008071826085420b00440a5440b507010003010110740c20410000f990010500c80246c0b24020a01848600d07120081c601c18109903005a0008601000388055401c1c00504000052083e1405028146c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 81456215 1250 81454965 81454981
    0xb0d06080708070e150a080a140f0309060f09090c0c01060614120603070b031501030e0309010c03110a02150d05070804230a0506070f09061719020d0c050d06050306 72
    0x20f681c1e0300c01c0d4071804071142c00042e01032140a40007068481e0040c14098502d0f11a0b40d2203584035010082103802010350107140d50b02c01c1c000140b4044411081c1c005614100c015024058560030903c00307000e03a00400e1181303074115500d6411903442200140d6500d91070b602844500340c25500160301c4541880500d92005031140622007c0341c0e1a88505107440046407100e0005c20320700031083d409220414001300500c100403800000112954500341d070103201c160702d00d864030380c1c6a02c1400551400300349040d0131080000c0c01818030007586802a416a9102c85181c1c010031440b507100402d90341840d000107140101d05c41c2034454640c022039585407441043c581659491203c46102c9550211004845000c0c0460f0908000080d20321f40e1150a03551107040c00400500105a4170745100d01192820801058051152103515401008522600c405481d81da504029160741c0e0354075a0303400f503001c0040ca20505d510740580110040b00d55074840d69203035101146070480f031464000e94402d07041401400202 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 81457465 1250 81456215 81456223
    0x10c050a0225032306040804090b0109080604030e0312030a050103030f0507020f12030f070605010303020f0a0c030b13021207080105010603060503060604150e07050301180504050a24060b0d06080708 87
    0x360790b00c407500040340d6138100000d40000b07060612800c168440c1504100800c100400a841103460507001848410404801034034514010b00a15010f5404000018042407054202801105002c0d056402024800e44840752551080307034401074aa40300d0b00100101039000c0380041da8801545015800c000555001404021003104003a10602580c00440307d0900213008440840180420f4255140813900c1c001d0082c0409100c1034016001d90301900080d141d0104680d130f0f0f100e92001202d5a91400c42d81c40508000c030103400b410500b41e0b070540040040c1c6070303900c240907a100719800400c955840c0942e043d095400580043d01010b00342182048140c40c0010b100350440001c481c04101d42d01a414141e501860039804001d401c0c04100900c0702580d041030007141aa01140b16404002d8803d12106040d40e8080c0c0f0000e0007544280d454601146c042244401d540b4102d00240150003007a1003050255041504228208074001403044081c06c6544510401401e8540c0a002040e21b0107071110b880b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 81458715 1250 81457465 81457469
    0x801090b0315070e030f0a060501090204180f021902010b100203091503180a15180f080a1103041409090a1110020a06062c06090112030c05010c050a0225 67
    0x14150440085582c0500502243d181384401400315000098214455940c85402100a540c070741d00e805c002141000c5980220f805640d80b000720245410070610038030004241a440704c65240c0d07400d1003a4846010035100b0014410000c0c0c0c00406c890042d50108000e11a618140b001598020000c4800c103407038003007001c01c451028001075516613490f0640c0c0c888804040d01041424020800c8e07003800c0042141c0d8100c14608076090400208820080c8a00e0200c0076034005080701daa401381a000280120b0010301e030710a1103140441d12404240d00c03140c91500181c0024001a9101c401580310f41420708100f60b100b18000c0090281c418103403503509040703810704140c03406104410351102c41c55008000b80c4110702e40c40703035040040c5c9035a1007643c241690300d5682840408003103001140704640c61380300315001d028020403004040e4a010000c40350421003d00c100c0501c801000c1c0e040114038284501c1c00c0781c0c2003a459581c1d071840304142c000d041005c000c140120070b206c40303101249885c10410340401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 81459965 1250 81458715 81458743
    0x3051506070303140c03040506010f12120e04050406020c10140601030c0c050303040309050f010e03151f0311040b09010e010b0a0c081b010b01020705010e0d06090515070801090b03 79
    0x198910039820304401a1031340c4c5500c207a1102c102424001300c041420001d40c440c1d0b02407000c0d190507036200c425692a008032442091231800c0c5840c004d102088001561f42d0300011141400c40e045030303c2002180954004403000c1e52695400b16000c02415030602804001c00c2e1045401c0142120140f100c510300700015024904055a40c3c541d4060640034816503023041d5008070031a5160300d0107160042c4110aa40202c60040c0c55695043c01c0c20b5025100c0d44500101c005c0180c0818250380b45181890407008040000301d801c0008240703042031452241e900614011104000095100c0d0184010b1750f04082c1c0c0240502440b8004008a06a001009040d00d40b0700c1c5042d50b4071300e508501203510b206040c0b80070b0300707082c00040c107200c010f0480aa030060350f00300300b0024005102c2c0303100166215201d5210700360114210200d0141c040c07070303d410755002e00c1c1d01c585d0002800900c551035251400e8040c0d40c80403044d04196043c4481540c0200ca0280140101d48080c880070520101183c0c48903c880740d518 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 81461215 1250 81459965 81459967
    0xc09060711010302070203030c0123190c0e0d030809160308040608041106030f060f010306080d03020d1b02070303080105100c0f020102070e100504050a2f09060a0801051003051506 79
    0x14800e83c031940407511a41d07002801c4070b4a0301c9058607154004c0140441004403034409140000324032032848142c921410088014424011546030b003000a003038040001e004000201d050480c20b03940f0400310b041120301a940e00034503854114440c03031619110546440d00c1070a038036420030000b1740030411103094030f48510f0000c031251118905100c030b020f02044120f501501c04020080b01549a50506200b024211090915901c014006500702c5d111401030024540020075201032842c06500100101c0c40e420130001888400482e00c21007050200c4c0c0d0000068100000c00c00070302d58007210710b80c00b405040307411401005a028000c0c1204003c5c100041021404d10050425603009011480090142e4081082c00389010565031030000d08a0240d80c0c0300314500404a04200258402d20050441d0051182c031029000e5000300c03106a13007440e440045200030803140e0b4150326504060926036206440310092541800208071035521640c49040816145c901005042d00c0525841850a41c080d2641 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 81462465 1250 81461215 81461243
    0x3090a0f030201020913020a02060a050c04050103150803030109060f061701090906020c0609060121110108060a08010f0c1e0c0227090a12090e0415020d180303050c090607 75
    0x303a000e8081d04090786d80c031000c01c442041c0d02c3d64007070b002040d610113268240c5015589042d08482117600c02d841d01c07014108148010300c0f40303500070340c40083c040c40e051401c1014036664030380c0b071842e550090b000103031410b4071941c0800c1018006c203000c001a00d542e0816240415104d201c03000c0034501489100c0040380c03100004424001b40e035044a20000c1e034881510750502e07001c0303400c655410085c81441480750401200d949003254801203003182c030341d02015005001341000b00441d50000d0150840e82d000e11154000a10b0070000d200300d10024088003004a00003023501400b411140550f060080f40110855501074840d601045801901d40e040304c0409000528465408240351100c40b5000180c4080041c0a032600c4c00040440701c8611400c200394440607a04404c03500500240300e0f00c0d0402c503501000c2000160140c103086c0500c0720303241c0b00505007000c0e141d61b40d080e1142032034420030071118a1564818582c0c94040c6560140d072500c5400d00c1d01c403903e800303d00103115040015125106403d14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 81463715 1250 81462465 81462467
    0xe01030b060a1814090c090f0603090606030c0d030e04110d0603150b03010908120c070c0303170108010b1e0411071a010e06060a03020a090510030204090f0203090a0f03 74
    0x4890102803018103115128000507a01a0a008500324207a100524000c0002020b0518208450041c04003404010f859103c035500d150b030640000d048164007400c035041d40c90f070580382c030b402461080b40da14005115504021003498180f9100150300381c06030310600387c1000400e800213050508003600f6030700021012030703030700f1a000070f07005d020346907013410342480390004c140301a003041d0030f8440d401400d081020701501400c01d401ca810500000301001007d00c04e017041203000e210056400104031015500e045060754801c42d0603070007600114046801c040180d071614120f0040d55025001110082103038106c5000054448142e01c1e04507c2400c00b001e54402d415291384e00b1070460642601d4249443e95140c0c41e04921412441d01c48024189940e40006520085583c2d02070190b04043c000c81c0c075000d580e0204601a41c8080790290501261314000143c0d62600e0540c40c22101c915940141c0310b60805a5200070760f1144014080c8082c014070506c00303550004140e01500743d5100e1500121088030f841c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 81464965 1250 81463715 81463721
    0x31709010e1c080a020f01150e040f0c08100501060e24070c030b090f0f12040b09040207021002030c010b01110c012303100e0610080a020309120304150b010903120e0103 74
    0x4003d00c0011401d0015140c000030300c061042c18807002449803e540b0b1a40c0e0040000302c0c428080264061804180800d60811b09e80c4a50750041b910101d1280c1c80d00d4129160440c00248195201e41d1040100a01540b00004807440c11040318070210055404504031401c03900502007420306180022544100982c0d80c1540d0015680710215090038505040159120f4080034080940350203480d4200020b0140441c0942030314020407a05030030641020b00144180e0809181d00d600300340e00300304030805655081d0100800b47c100e54000c60707a80c00d281d8502400c1d120366030b60030303410f2003c2c408844014150215254a44e520280303080d1805400d51120300320b0b0003825080307400310500000140000c061401200740e0695402050000d06515500d040c405900403600c0044001068140450303514805500250b81045914044034090741c1081071054069100740c030125421f51581420600e5010b89010b14030016070f0900340300c445149540c4517018100d8410003841c00700101c950550039203070b000f58 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 81466215 1250 81464965 81465019
    0xb010504110c0115061407030807180506030412110309060301090b0a030b0903090406060906050304061505061201050a06050702030307060b18010902070614100933031709010e 77
    0x1400134460404000709240150700680110700000320812841015441d00303004840e0a107506913241146591624021a019081c070b041202002d550450001501d07541c0741d01070b600481c018a041d00b0b501c004990040c14003c03801c481001140c03c00e100d4086955112015a0704545010344045140a008000900b10300c07450340000b40000d00345070901402c400c0020141642c81004d4804007c0c00d501c0d0102620041402d224481c0003901c204001800510300f50400c0700f4800c2840c100007090ba4035040050400e4000d07178000e1042104c0040104402d02e4550540d500034965030400703529201c1250007084c6c0720301c2441c40240c110b40d00c0d48200c000b9500c5590baa46004060401141102c1d61512135a5020b980a0300c01500c0041c208182104200f4010300d002e405010f02c054413820315490802200003500c002111524501c035140304407500d00b40980d0400a5400041c07100c2010b160035885c01d41c004007a407518841d4510341c1440100e810740d07000700710a03411100032210280003030120584120913074001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 81467465 1250 81466215 81466237
    0x160603020d0b19180b0f0f01110f030c10020405090c071106180102060603010b01120f020c030310080706020102040303120513140c011b05060403111e0307030e04090b01050411 77
    0x40b0300810040d14070071050742c0903904e0620b961004d92000043c0d200694403141d00b0300b588202d000a641c101461300c110412003904042c10009078034400f00c18103030b06007407036014900020782000585110417801848160380441c14104110308040c200008500b40000080102e148100c0001e0000f0034460301c14095050114020806a41c44490443e49004022612890b6000d403159070040351003440c0601400c00280d006a4421178030b082c200400f0000b8050344124502500d0f401c01011000580c28402503100d02440ca00f6405c10b1450040100c4c07600c4400d5010b8021a481448207000280e840354102200100310302c404640c030f848020300c04c86402c1c3e800c00c0c018052100b486002c10940d1003c28182d00342c09003600c1d0042c5041d4410201101c2000c1e5040041068214400117400a8003a0340fa5001c054040021500307645000e007082100e150110b407070700740260300200f800801c05520202203c00c10000b65130901841c922a61040340403001030040511440d02d61541940b458801d00a6412042d07030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 81468715 1250 81467465 81467479
    0xa050f1c06051e03061504020d06030b0601110303070503010302010e0f0d030e0405010621020307020a02030a030c15020703050702090405030904020f0d0c050c0703110105070818030708160603020d0b 87
    0x1880010310052820344140b50007500144088008540000009103100d0b9000c2c015014943e940c00c440d0000c0018030034940c0c0c4c0541d01340001c0724204a01c0c4100c401442c4106540782c0141448000540300f07590070494076800b94020020001740b070342e010084c1c034112582805e21038890100d90300021004a00a8001070300030441e8182c1005050384162100340600701614100982d07600c502048840805101741d0070014102d1810b40c80010260b035005540c007804502c10344840107000c0d4002800d041800000354009084601400e00340047c40e0300519091030041001c40c54010780c1c2da005042802101d002920488809002409010081c0226151060001c10440d030300c40204800503ca074000b5107040c10501d103054800703085640602e080b18000b05c80000100161840c56440004040c006051030b41042010f009000c0007428220140ca942d90150800812072940c100c01d05182c010294000240c40d881007050b0608400740c14058002c2d55990301d40945d40304a0340c10803001410074000d6103600212 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 81469965 1250 81468715 81468757
    0x120f12150a050406050f060d0905150406050703050402010f0f0e030102190e0f09040b090a0203061005010f02060c0d0c180603140705070c18151502070b0309030a050f 73
    0xa60044551140c0084400202a588520901080b01c20a000b00c9400182201c5000041c0c40e04101418411142c1c00740800d510007240d403240c0c10400b4607410558032001c240180010041c1d280291540144c1c20300e01000340f450a900024000c0018500708004d11880a19480c0c001d881000d031000c1d1170700060300a5688588081d01d008001481c446150005510008800c80ea860503640340c002100307004042c0041c549881d29103901160014000101303a10440c0883c40068800f446168414a003c1842c14030070b91419001401000050b14958119081401003081a0b4020003c0d0b6140903c3c51900045120840f0810b6030114450748500924010200300080c41c0c0e9490340003954480390004011407241c40308001601c15000786000100360501d031030410701501100039a010340403c1618408581c1c144404500701919019401158a10143c0d4000280103901004000020003040d140285113150032400c0710703120f02800c00900c042100004502c0c143c0c101c8031064401012440080b810400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 81471215 1250 81469965 81469981
    0xa020c010c050418181403130906050907030c0c140a05031207030c05071a060a0914060405090d0e040c110715020106240c0618030801030501050a02040503120f12 71
    0x80c1042c80750f81d11a81d2078000c4d6200e580180e000351082084541c08419883e2404d43d2200c40f54a83d030919400544002d010000011040070203140003803125110000d58182045c8c2070100340700004150005060034205042041540440f074440500c0e04400c07040c01c10b103240d4501c1410142c003114054071610001c00c404080d1641400107134026070254800b000b40803039034041a10345005105000d010800700310081d110045007007888039409080101400b20030783c3c0b100c08444c1256005000c00380b01c01420810040d03d4105441055086108100200740e00100c112006014a01d0711510038080d0b900c8061183e90107000301000d040c40414141036441140c2c941da009110b0401c2079907540e00642c20600000b41c2e40790f1007001341ca016900b03110020300c6c000c000b0320140d0f45003000c00421124555034500803a0300d80344104000015074480c0d40c0c0c8000c5945076040040c01c2d10b00141001900718810802008190f800040002c0c41030b1006280c10b444445400810300103010342c82d404e000c50b90b050810030040c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 81472465 1250 81471215 81471217
    0x6050402042403230c0409090302030c0f0c0d11060903030c0d03110a0f0f0c050d2f070510020a020a0e01080d02010c020c2e0203030708151302030a020c010c05 70
    0x803482080c1821002052200e084041e60f8000b481c650000380d5030058640302c00004c14140340c1c400305801600389482d969101610844044040940c0181c0000c02c15160b021010b100c0104185440d50003040c21004500004030582c9008030010305403448441e800b9044e0b221032083d00c8520b040101940c1c0c9804080c011030b0b0b241c080000c600340c000391610406942c2c14010b4000c1c2e03807901401d03030758145500000c507800743c650080a410000501c00784c10541c0d0001141046824480e030025914660407505008808d0b41031a0303288070074810404280082594400006941c4040f10310480301c445000d004014160f09040c0c03502d40294000e540900c0106110041d040103d040314030141c21074072004080c02d412800c0751180b40c141801030700501e8071a090b034505142043e492018214510384582da03130658031041c0c14a442070800140e0004001c110b03c81e41c001c603c0a0b4003144202c034402036101e640c4005480c011031203401001e840d0340800030170103004031075064a00c8601c1800c020086403401d000040d1035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 81473715 1250 81472465 81472499
    0x3150b150a0201093302030103030e060a03142401020a120c02060d05090a0c05030d0807030e10050a05010e07051201120809090703060513140c030406020c06100302030c0d0206120405010605040204 86
    0x170348100700c45400010440d482220b040320703010340d0361414402c0e100081041d80e504c1465294201600d440d43d18450034243c8131518090711640c00030901c80c51040c503112480300d40041600e03041d034100922240c040340000361010004e2100d0301c1c200500201703610000b1164083e000191020034504400c001e6095400104920340034000c0f501d001c030103581c0d4020190344603004120500081c410801284269010b504030100455041c0165080070203134140d041d049680880d0007041c001c0d02d66004014141c986c0c800690000e07403615050f403900240340740030862400d061207800a90341003c000e103414400f0070802e45075030810043c410503042c1481c0320010054140c0d4002e0b580300f0401d2055002076050644038801100000c0d10340e48507141e940d1100381e007003a080104240c80c82e0f5001c100354282400c092101900c00e400740e4a49669180c254010b140c40c00020140d003900034a8240391140c0540d07070310010b594901010b0303814090144c1d1345140481c0074042d03e0744a55001400801c0c08107003a8080515056 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 81474821 1106 81473715 81473783
    0x1120c0e120f0327010207060504060f0c0206040303020a050705040519230906070207060206100e0712060603090224121317030103150b150a020109 65
    0x200316400007200484c0e004400c00b90400d15000c0c420000b03841c00d002c2c4000c0a14034101900500340d44030301d00400c0b0030300268420446680d445000082043d55024100302e41340c0d5030780e140196a55103e881c04032100d01035100080b64034240f42c0700c1ea511030f04000c860860203190004044005001c0e2400c0e5403003806216070130894455a03d103025001380a0701008240c2442c151700c1c02420040d568100e0310454220320280500e051440078800d080da042e100e9042c8054a41c0c50f001d848110101032100c040034140103001450503015403010362100e00980d4200218041c8141c114045130180101005580c8140440703ca001c807202081c070303400310b000002400100c0f05515038090701d0300c10794844003101e6400001401000349612854140c044924014048203044400150001c0007011210303170400030200342200340d503100f50069400160807034800d0411032022154445014010b0102d01 = true := by decide +kernel

theorem cover : BRFrame.Cov 81294965 81474821 := by
  have h0 := BRFrame.cov_init 81294965
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81294965 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 81294965 ≤ n) (h2 : n < 81474821) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
