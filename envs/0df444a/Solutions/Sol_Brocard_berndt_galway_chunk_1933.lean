-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1933
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:12:21.381661+00:00
-- url     : https://prove2.me/submissions/05ac67be-0adb-48e2-a420-6ba11e5385ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 347482014 ≤ n < 347661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 347483264 1250 347482014 347482019
    0x8070210030e010e150106020d051206060702030a0624050f040b0f060d09021c0510050901090c2c06010e040509010f0c051e03071b050a050318040e1b12010603080301 73
    0x50b444921101680700321045060000c10341f68000111403070000e41940e200d900d00b948250230303000e90040192100390701c50810460300d00581d43c00c00504501c50b00458001801060202001c414021400c06403800402e040404101e0307035032010740e50003081d0010746012401c3d04200d00011429041f5a400a034001800304501d11943c5a581c0040b81c0d091003514003c0a9062504154880416078000108603030320802d02d101001c480344d00f0017904a003908001203030340c3c40c40b5510a05483c185420003030304101d914522000451040c5d2410700340c1048041d04045909010380000c08003507042100130b006603100c6001c41d43ca100c00b540f00b8410001c0007042080f903030030b82c90002840d55201c0c114000e02d0001c41160b103440390f0b900000f268003075480c1307448001d034101c00301e43c4010040c40c40304829102ea000e20a0b0380004100c0a0000344000241040d0b614041e6840400304012207911a01c81480d9900c00c480540c4019001010030420810460710905180e43c04440c441c090407158000502d10800407000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 347484514 1250 347483264 347483291
    0xf140c03070303050a020909040f0503040f17010b10020601090b062512050309150705070624080705030331030f11030c0307030b0c1608090a1208070210030e01 70
    0x1d840410720035a030900c000c0e121409010103171701a0340200c59000078150301040c000b0700d80c0000680420302ca10145e07820302d036580c56804c4441c0391991100c190741c4844115002d00c118281b00d01c40490300202c0300715200301c2508038001e6541005004d040f80725a81c2e8618640b990307444030284e450521400786c0d80e030058130706ca40c001d0401030440e0a0403100c820303140c1c0000d080c083c000c0091760303c1a5442d0303005000b01c80009140e85030716200502145c042c00310800291010401500a5162420507a8034080307154078048020349030024142d100b00c0c455002005e0070f10039560048200c41241050181108031000c001c4d201c500c001000084005ea0484030000010400c481419001e581901981842c203902640d10203054581c1d003102d0805515400004c41400084c10b4442200c0c2c200010701509400d000ea066040c03000004965800e503403001000c100b0200c04d107071110402c0f014001c0744442c80c0c940c14003030307032a503caa0080b00c0000b0b1088950440e0313420580d10a5001c403120394100720080c032004100185 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 347485764 1250 347484514 347484517
    0x702060d02040e13050a020616060203040303270302070e0a0605120c0f040225030306090c1101060f08100209060d0f0911010504060c06150e0907060206060d030f0f140c03 75
    0x42c001e104404000002c48840d0302e10203134803d40b6008009090541241d608008942d4000003540c0d41411070b10406402040c22440134600c140e01c2a18002547e000111034500c050102c0000d013000c21000c0041c520000354041105411542c041396030f2138007600e07048481c4c03000e81042e4200c136402c0300096000d0380d124540002c030b110786104180c82044238581148248010f910400b08502a00e40c0302066100c50001e0142a0f8510030f8003174071380011015150400131090b60700195641d0700041206040c0c0304900000e204403c020505441c0d002c00d0716103088100d076124584140321888a0b90b0100e1440d080780c882c20200c43d00c0b030130542410016043c0b48410741c1c005000d5a40d0645a500c00c05040c4545940500701701e5080d03802d80c3d290480ca180e81c1355140409407100780ca41c82504251008005001003071004007501800d8144042d12049081c840001d2500c60001d020070b12078064181c103840400e40100c0311000070b4035580303800e0742d0503507105e04195500292502860140079000401e501090808030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 347487014 1250 347485764 347485769
    0xc101109100503150409020105040b030a06080d090806160f081015050d1404030905040b031c03091b0315050702030c0604060c1b11040504140d09050a0e090d03020f0702060d0204 78
    0x100c402040000c0085c00201c65641038003e003c2075040009201c0c0b0b000703400183d2384c403240c54540414040e44a0314038905042c0b50040d2b440120f45000c2c1c00380101c130800d0000d50ba00090031140d4070740b0081903c40080c880c06c10301004005008000340032503507850100608601410882d01d400302a603040384002001e0340d00c88030138202d0781d0b89000403d80e00341071307e90354980c0030b9a015565034848074100700420008020316080d1031341c184140c0b00c1607540c0b80f540c0307031448541003400e40380021038a495051102441c00303101c000d070462100e000d005200040680190a0300c1d04030214000605568a1000ba4514421940514600c0c070036030040108100242d00840e41c0c100041e0360b070401e44607240002440c070103102c0b1002071030740002030000100e80c00c06e0341c001a40070b4003c1c074203411084031005034241042c01100c040c90000d0304280701480707581005007502c17004100c420650541d0303191051080340c461000d06c1c600e03400c068000400f0f98000400a040d81d90703241d0020191360303031900071980000c002d501c0751 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 347488264 1250 347487014 347487031
    0x3210021e06070801060c0302100b01090305100b010e120601060327150608010c02100b01050f0406120b010c35040b0403050115050d03050702061e0309120c101109100503 74
    0x1d4004241580324040400d00da82e8150000c1502809c3e0264090140c4551042941000310b50180000880c404010f0b28001d50400940040e5024080000612442c03c5d015024000c0c10004075903160980b00113680b0f03044650a14002910b0368049115082c3d15001440c41c0e405030054551900038001c81c100d8035004100031071001c01c0220340e6003028030b081c1c55100002e034001d42c000207a0084904c145800291000005140092134003015040480c4150003580141c0001561554503040c01d00341ca03c00c5400d03240342401c0c06800c07150f480ea40e105516500c84c0e06007030361070910810300f0303515410a08201180c48485030030a445688504500000f9040340c071081e00d0542c02d040f00c05001100f45110b25050341c5020341004010101c80e00c042e103540c0c0c00540201c1e00701004005071400075441100030702025814480040d628241038424900e04000e05100e6a017140f020040d502800030b00090b48106401c40c6440410301401507800725003140205c0010700d41150309046e0f5019074690100055104a400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 347489514 1250 347488264 347488277
    0xb0307060c1a2d0f07030c0c14160e0711030f03130204090b1f0f050d120e0303070602040510090522090501020f040e0c0306150c21043210021e0607 65
    0x585c00220291495000a100815003c110b100081000c6602d04d00f843d81303e00045504002813044500ca582000303600004003e0022400d1291207a07100710240c4040c06d2601c000e6040c005a42c070481401c1c84040c1ca43c1c505070903004040b81c00c5483d10b411200b4016081605540c280c54600100380f08840d0300340031b640303003070b0701102000c5204540c160303064040d210050440a0a004a590340007400d030700c82400c403402e100b40c42400751000c3c1e60801c01030602910074000580c82c2c0385440306006501c5041004401130042c40c081c1400180c0b100d182c000e4411401130701e00c1268142004c05c8100820382110007a01a500001c0e4030301c803402581c2c000300b040303900b42e12091181c0d90741c1c20380101c02404150b41c03e681c0501000c03000d8110b070303103c50090844c0e0701210050b2220911908480500714240031210a42038201240800034805010801071441c94402e0780c86118030f055044ca92480c40d03060740c07640d10031b001411030802c5051003040b040da014010440310003d1a0151105199114070444665000883c0e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 347490764 1250 347489514 347489521
    0x160902041a120127090302100e0102430b010f0515090103020304030905120d0e032427070302101b022806030b0307060c1a2d0f 56
    0x1400084801182000c400c0b00910303400c3c561050402c2080c8a58400207480c84480e4158683c850311822608500c82c1d0010007074a849404154161000f0540c18400b0364414807803203843c022252110744c000d00c0d004403504a02e0024900084240c1c1229141c0d258481c0080020400c220030107588a050784c0f98416600c900c20740d01c04c104500202c2c079450041c003140c1c0a000540265000744c01858004d4824200781100c071b5101c1001c64080c042c1ca5600c0915544840c4881c02e240d40c1228080d0401c0301c060f0050400f02040145240646100d03e0301c03102c050060100043c2c00e4903600a0180c819520507422503003407082d0641c096504c45590109920440417550400900c90281c0004420442c2e04900d205440a1a030208403246110442c5404100c00c100410386200402060110240003652000240f0703105081c01d0618001194212030140b10f8540110000f0400c25284c20038404610202d02503955184480c2c000c0400800d10319400c003101030702001000d0841402d4052140781e214145480030355 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 347492014 1250 347490764 347490809
    0x3804090b1e010f030207210201050f0105040506031e01061a0a080606030f0103062c01060e1006050403080c01091a010905070314130201020114041a0109020406050f070516090204 78
    0x8403021075850104402400a1880034000d030081c0c91480c1c083c0b58903000c0c02c0c91004410428081c201004001130750340702c080100031074010054a000d441d0950b03007000246000ca000c2a40e0b0326003201c907948030442ca40d00383d071000502500040c001e8200007540d54030050801a4504c21608540c0b24400400c5081e800100e981c1003110030340e40716040a81d00050541d1964a4000043c0841040c1c10031428008a00180c00c11040c0e54500704000d000d00002507140c0b03026105012000080c218506c540c245c1076040041d19407001c103540950b0f1f046180195030341004021140140018400148103541c402d6611182d8030a0700c000c14101c0c3c10b40e91007408241d8070044100c0484411002c01c44091000c500800d90303650303500d601c0c1d000e4240f06000008150300c44402e0170311800d004a1301165641c07103a4001c1c645da0a42c240030b5a004140d0316200303500306401c00d14050181d019107900d0303c0310110080380300800e000c0200406940e880b101d00d140854aa02c810f10300010350b00500030702e0b0a5020000c0f0300240103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 347493264 1250 347492014 347492059
    0x30206071112160f0c081506060f0306011701081c0f0f0e010318080901030b011103030615070f0b01080c190e151f02060a02043804090b 60
    0x1044003500038000a00b0101410740c022800e800f1090390341c0b5020b0030004055503003d90400d400b07054012041894141c00e1860b013415415262440282d200030300c20341e5201c40003541c0c401003824140b16102d5803202d004071103100303a4051390362031180e010000242d107100c081a0500d40142000300e288075590031a9080d038042e4070002c0b4440000b204007000c98001840743c4024054454149404540402d00e0032072800c0510715a2000d0324600400a2642c089603014440d02112001c03c0c01c00100d4403e011600c0c0e520380c0401013000e802154034103110402c4010020480f80c1032580f02443d800038400c079081c4020002403d0044171518480c229441c0d540b480c0c00c42004051305a441c00541546040001076041c501001c0c080007000c0040d00b40701e102c0c59030351102c4505030310b18010249148100c458002440c2081c06010b80002510402051080361600c1c40e0a1101520700c10101410142560814030340010881100110410124000c100c80c0500d0f08000307608081100e65601400d42005032203541c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 347494514 1250 347493264 347493287
    0x1b04061215120201080403030f091b05030d080a050405011b050a030501080c0a060509040204051008102c0601020c12010b090619180b0402040b070b24060c0106080d080403020607 78
    0x241040302c40c440006602c18007000d94041c0c4a80307800300c3e0405101e2003140540c0d2410720104c409028101d00480c009200007100300090804a00400812490503000740c09001d003d8551542552520001018800c003504044d4515441c0030102803680e1005a00514507006000701c0360020341040000207440d4070006801d40c6c3e4030b50080c07a0594040c80e00a0544d10341d441600f443d0f4020b6001e00000805903a00e00c0591514030190f1100340040c9006801000d80201e550003260424203118180300c8a00806000e04d041920480d041e04000e841d03880050b450044401d1040e82c1c03221503400300030901801034019010704501070f1400d42440d01d0342000c100c01c4142c121075568051481407400c0201c802441404241202c030740200040f9507845d000030405030f034400e41050311020030010f50181040310f003410042d485034100c2429001480320341d140700000350f030407010b583c803d0b40c1c0441c0160385a2001c1d4000c3c0004c010301421150051060040038202210880301a0094000e01e400164810702030390101c80e5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 347495764 1250 347494514 347494529
    0x5120606090a020c0f030c0a03090b07082b0e1c020c0d0221060f061c1718031b0301150e01030b0709030b241c02091b04061215 56
    0x107039541d5240d4004025084103040b100244104107418205480900c000d0000b0740640c1d0280c00d17044554180a080c6104645c000031202c0350400504021808000c1a10074581d2401c4021211403481071007100301e020a07410f00b250903881e050040b03d8490f00065000c880c44100503150454140d5054181d070ac1c0c0c2da605003c540c00c5032650170484018640507041180d5500050350b144220304015148038075107501290075030060035a01041c400d075403030054044461407400d0034810503820940c1c1d889020080070740c12181d5030280c0c00319480344000007014500105c803501034101c40303101d003c9020b40b6a044404004060207075207840c5a82c00040000d05401d015200400180e0115900e142c0c0c50222407a801800002000484070740800043d61141805000c3c3e00e203201710300304c2400c442030b003502c5804414035154031640712040c0d005110bd1800311800c050030780440b403221b2143e58000c0d044611950a04103480507000000d000308041e40c00441c04000a54080360400200d04000f100e00810800345c061000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 347497014 1250 347495764 347495779
    0x1110a05030a0b0109030f0302010509070f080d0e04060b070305030a15050307031401021603020d02070609080c120f0114150d0f02091530280f0f030905120606 70
    0x2c03030310080ea401084224070189031845107941d4945800910400114003100140d469109002209904201c401c01420030b004103e4000d42ca44601c0d10340c0c0391514601102031020000c1035030f4907a40c450340000c0041c085041450b564100031f28005100d580b00320341c0503c01c40d00d4006500b200011019003c4217940003c0c00a01c08075055849045a41c80ea030320450481e90340070810a100b09985081c0d01d070310346119070001c0c504400030500107402d001c0c141d0040010443c0c1407004012310240060310040000094582820751540c0d410400d040c800081039120079582000f1204801c020b068503034a21504400c0940c1c040c1d01101e40c1044000f00c00b00d400031303101d080036000180c098900800a5034101c1e8030b52190340082c178500c1c404200715040b000e0203100d0300422409074900d480c800d4443c0d407044907460405010100d4480d884220f031030003060164071701019089503017420807a00c000102145500204507038041074407403030f00414a0060340545d82c011615604206032440d000030ba40c1c0c0c092000200500d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 347498264 1250 347497014 347497021
    0xd0c15140304080a050d02090612040209153d020d020f0a15180b0711011128050d14010f09020309070b09131811010f0e0409210c0501110a0503 63
    0x488144d041104003040d4650308001103100d2703944150041000003011402c0701c403286407500420001440051071450904103c00848846035220950120400c4845000e2001c10340b40d5100300207000c020a1800130102c1282d0700003000541c0008600400c8605603080f00e4860400450460712a0320401c401800129809040d11083e400e641080700c01c4005802d0076580700b0301544405aa9040c16036680010a024111590b00740e0020f004070711400e841f01c0366085c9402d1030365402c0c10000600552100081d0300421130141c481344200104c50001407004000e1210711007982d0070f41030500c030070b100c0d20072075107000f90b400030300442140240c0e4424660240130f490000d180c00401041680620885544444c81d0603002100400c0d40c4100804d0024042030b1004240315881d201c2000421070070601d043c06154816100d1855001802c40f0010700c0554005c52140e00d0b516200504040f8104540c0410304024540c4000c250701c4107848201600410082c030010340c0d81140420ba03840f412904100154042001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 347499514 1250 347498264 347498267
    0x81213060f120c080103020102162303010902030a05010c12090b07110c03010e0114010e0115030b03011b23042102030c0d030519020102091e0d0c15140304080a 70
    0x441c0248220360800b00c40074411403805000701d5001c802d524000c42d01c8100103000755641007011004882454844a04440c1070004040010413458900d00600d54280c00182c40741d03d007074000600e01e65020b0f04640444a4510b022400307810384602c0d41c00021a4850041c00c0d140306401880c4a09070050610486900c5101088420100240b40d04060f440b5104d00d0382c0c420b880074411246031b01114000050113403d418a880d80d00031060f131060f0040084100184103c3d041807080103003020780c0381400560300c2c8114000c00d000d084035208840c1c0280102521307102581d006680000034404843e0301081000c0140c0341d07e280c2d40030724055440c0800c44060981208100d1000821740680000d040344e40c561030680c00a804c441c410f4208600003a07002c0791088001000100403400d5090f513000035030501c3d859802003500030b00b40610208024010745102c0203183c07160340d02070044540201e144540c1c00d440b19440d0700041400d907010b0000803014041d10520011072000da0f40125400b124a500d8940c11500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 347500764 1250 347499514 347499527
    0x31205090901061d060c010e010b150a051303080708030609070207031e02060c07270504110906060904060312020d080402150a110706030902041116060f0204080604050708121306 78
    0x200c08540e0741e1a110020341c1d42c3d0101401e40702c41b200d000407808080484030642944c000811503030042d0509071200fa004114201a64030078920341c5803d40d100c03152040742c042480c1c6550300290402400240030410702c00d6440046108240c04c1e80d204125885415003260b48a0307041c400038210680b218200c82d407210f018510030301e0240c0010302c00d5050441c00b05140d4240302940c0c0c024001c0b4020b090701c68a015003455114a80d0300c0780c046040100c4e151a840e030f890444084c0c01054440c00702c000008015030340302e105843c01174201030070800c01d4a440745043c0400012082c1c8000c0940b10305000302c0340c098852078030b036403181c0e5010b03114200c040040040690190400340b130704011301081ea0f00303503520b00d01c04016403401006590380102c0c00200c2e078014002269804840401aa00100000046c144084280740700055006800040d02d025615080b40240160341003a01607001e0320042c8000d0081c0082c030f4805861552040d5808506040651b010502c14081015441c107440d8100f00b205500404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 347502014 1250 347500764 347500787
    0xe04140f01030b07140d05090d08040b06040f020415090f080a0c0308030c160f060623120f0a06050103141903080403180e0a0c09060e06210f0103120509090106 70
    0xa0221459441c007a140104ea08151200100b10340d5030f0041000c3d10b2303001c014100c500411030034502c10310704180d16920041800140824062034941a010b4640485a0b0490b401403010008071400c100d44200000c050640c0341c440e1048802003014003140450000c2800741c1c1d469400303c5500303200e138030310303074032031405070002080130340c850209120304d00e0550304221141e482103104000e54a0040c40a14081c42202c0b03060700504d40d000c4000c4540880c402c0c0500c00f000c2146000c07110706c0d40764010340344010314025514190b1003081c000c0203c0c0004014060b00014140d070b2041d220012801c05902c88030380c0d00d0095a0818149002d80917000d00802d0050402a800c0f40c02468904007030400a00014104d120640c03010105200034810004690b010344608030b4030002c00c0c03414a050030b01d44240140031540030724402c0d10400c0e0024122041c058012292810307441c0444c516800fa1509000d20030060074248030545c1d02e664640c0c01030005501c100d08a41b07042100400410321a4240f54080711441d0490 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 347503264 1250 347502014 347502017
    0xe0406020c010e030712050909060d05070f0b0705010608011a15070c0e07180524040905070201020c06070e091801091401021b06090a120219030e04140f01030b07 71
    0x1c1101c40c0100c8000e006580e01c0d070440b03000071950b50780d01c4d01d00042401483d1841c50100441070090040f00d580c0c5402c1d20303412881c1120860340402540c248941085059840711400044030000015038000c14405402000d000d070340204032042d55200e00a0a0341c0b416062400403901410010449141008451980d07940060180c0d041c14010380c1d0314002c40300380790055510009414200b140e8540d02c0080070000c40000303004000402d00d0840850300552501c04005a2100c0b80d2018029050800040d00d0041040140520050610341000f038003d5100b8401d4140500521000039600340c0030703041c40280948d0103064004a556503440440302600c07507500d81c603815521050a6004208402c601c0c3d4070341d0107004001607546104002e000740c01d00354000c40c0032454220204008020002140115480c4d400c01034000c961000421300320f04141c094206100c00111404448003030507071024503c0c113034010994040100d00b07110b2808080071401190303a00d101490b804018000181c000c20015080681da = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 347504514 1250 347503264 347503267
    0x120501031218080118022b02040506040f090c05150415051c020d06050306090c01120e120c07090b090c07060c02070f0803030a050f0f0708060d080f030a050109060f0e040602 76
    0x1100303091400d4481710702c15031741c0c03440f2036620390820751903c09005202603814508500c00c81c12900d170325191480301d4203c040d1003541d482c8000780c0e41d901d81d6044140b120100300410008070344180f91081e80a0300c1e9000d0f0703a000300c62855208a10a19030404c942c1a280003490b03800d000d800b0307154101e560781d000a03520300500d000d16214400c0c010035070003d042d03110f00d01a000304484e0704007401d052810744c0c001c000d140e4540c4000b58004613642c00c20045ca00111a00078007203005042d002e0011f152008031900b4500d50400054600c40841010818070306440030380c802404030a40002c04c0140001c1c0c15074903101e03440000c0241c580011702e140e22040300d09441b801a1020240d989040703031045ca0480d408030b40c0c550000002c00112107414481c00d40c1c4005080004811070400390054804110014200c900b4000305001240981c0c0d6a42114403100340e202a2041d030350149052a1045034000b0307602d1031282410000041501d480c10300502042e40c684026500203140791203150700d0040700103001650060760 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 347505764 1250 347504514 347504519
    0x20109031707050d02030406140306040b031e0d142a03041214010203011202060a020304051009030b06030a03020d0f12090605240637030606120501031218 68
    0x180600000700319454000000c0e21800a8181a8240f059500d41c5074115001040248901904100e49011840c901d2046a03100c0c0e503158080750003011002400c90f850300c10821780d1094104183d150b03611200110301942c894018000702526200344121040c1640c90303081c480b00022501407101d0603000209080e6803101419000745a0381544e206030403400460408803a140d09000002c800006242d0054000b1883d540c5810201c5a440341e2098000380300c0e070000140982018401c100707407005450000c0060848103000701c0c0c0600581e50345d210482d0140c00c0d0b48001009031a0200c1c00340c0065815402810500e4861070086071801c140300712450038888600c6500c1c510008500c11070780c0c42072007050b0029150420740c1c0101130350340250003050054146c074070050b4402c1d181ca80aa51030242074011106680111681e0084050305500480750340c48440018121269815000340c0c3c2255500e80b21100717108001001c0030241ca000340406018031030113a0444410b43e1180a400c8014885005404030617074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 347507014 1250 347505764 347505773
    0x1120501140f0a061d0c0a05040e0a02041d0412080901061205030d18120e011403090c10390c060306090b012c060910030e0c030604021c02010903 64
    0x14015200c0103242c0c0507510412002443d684601406403d40d040c0c00c043c06200752240d121148001031000c4407229021804186207406502941c7c0175000d2482e0280442c81c0501c0148002c1d0068400da0145445200c240031a0310350b5240c030140200d8014170170745859824a0826111000d02810a82548d90307103030302c0050108140c0f5810000e40c0e11840c059640d401e0101400d00c00e541c0c00283d500b10000c0340c6066200040c002c4407015050007580d041559106903038000503101c0030003c08145205180020422031264004605421003220885130003840713103c02c0c10b040b10882143d413282c1003013108019102202120780c0034500000c0d949400480400c901030f40d95040039400c140d003c031780800d40f40c41c0e003485034024a00a1a4044c170b0f0a1030030107560241017010702d01c00e541d100c3d0f400b10a45c81074810701580761070701400c0350320585010b8951100b0107602c141c024001c1841c0e40c0c0d4100b00d800754036a02d18641c900031807000e01441d0020001d90405000f00300e02441002d40041c100d040c001982c00000026 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 347508264 1250 347507014 347507051
    0x27090304080f1b0a060c170904111c051003141c091a0a0804111318050712082505070e0103020306100b0a0e060d110307140c0601120501 60
    0xea90b4101800c0607001c0d40140008100703002080c0c80c03045611400a11466a00074030311952030760018900600d65414121020032441200d0040f50058180350000006461b02e13401811011302180700c1484e50b5140440041c21030ba410b6aa4105a20320f128080004c51001d2005807500003030302041e60b400f0384d141c0318901c003c0c407008400d1101181c1d035078004000480482c00c1e44200714122800342881c040c194031004080d007030000c10050a28401e91801300f034686840140c0074a42101000401c440c00c1124042004907941410403106440b0354040420910704041c09451410f0380a10301c581807a4159036403000c3c2582d11040c08454808442040001c181f041100c030004101111818040394150300502d420401c00910341c20700407848030b408010390614801150780c2518a4600320b10390039055400501248240d00408009504100ea5410a0944c001c011402940503031501185104003081184507070103811151015030300310000410007a85034142400c16240326000000c1c44403440b03080035040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 347509514 1250 347508264 347508283
    0xf0f0627010f1b020307050a0303050901090c06031d010b0a14010513091407020d0e04050c0706050103060204090b190e15060304150c0e0901050d03020321152709030408 74
    0x40b140c44036a0040e0044600e10030b51640d08052028501e81162511000d0341d8200484000307040540c1d544c00503115410030340c0f111010903070101c0c07501e103c0c4e55a4040280940030403201044012900201180c2082d014072036803503604005841c100020f842c1280c1c00041c1e0500c0302a1606210b01004404424485064200042c10803100c000414075844d056103540704034000d1403035041d90700658503030a109800c041140e0250782c048401007101e943d180078011b001c2c0580c40005091605240011040064540240c016981980c104004400014003080502156145000c0312090a078400340403052001e0000c07a403004946080807090781c101c03400719203586c1c8115802c1e2040700d1182c41d0024015441e0040003800c03c4a86882c0c82c3d41128180020010107062040c00d12422007425803000b01402441a0346141841191010480c88102a07900f80620111048280101070090400d1b02e49403560031100039404075007095640e2900c0300310240c20a00054803c2c0785520090100003908403042101400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 347510764 1250 347509514 347509541
    0x152d04050c040b0406110601140603060d15090f0209090a0b31050a0c090e030405091f030b01030c0821031e090309040b030a0203030f0f09210f0f062701 67
    0x8006003564001c0c3c204417040c0c200340021101c0268501e090750341c01341a2070304544c0441d42c1c000702a1030b07848e04100e00032402c0b05001403d402e00d028402400444982c00d81011d000343c0700309a05a5489400603150081404020003a0300740c503001c106581f556000d083d0843c8008842d008080010019450fa5030061440407106503001c140e062080001008285000f02013051052103449201540540c80380518080c2500404410300000c0c852000030314100034000200024000c0316840f03007404504004240005c1e51100c051303150018010f007000880c5008000c2c00900e901459142600720301603907001503e458008280d90048110a0a0004080d809090808d0045545118910521040d80d016008943c0b090b00725408000143e01c0100484a02203221f4a03200c0e80c40010f02030170031840c01601c00c1d403078004001e080c61090040302482d45610071303059502160002801031503125038490703041d0302c080a1604010040340f06110006000d1101003a04008482510039140d00036007110008009101c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 347512014 1250 347510764 347510777
    0x190b090f07030e0115060302070201020a0c0305010204050109080d080105010f024b10090f0606090903030e0f1216060e01090c05121906020c06152d04050c040b0406 72
    0x2441d150940700311400c2d800c14100070700810b402c018131400008103174490007044c541c0000f04038045a10034030620500540c0641c107180c81985906142d4000c2d0814054640402ca91036000b00e62501c00082c50800004c060303807411500c0e82008011120103c0c0802d600b02548140740a49401c101c0c0d10f00305034103003415000e010703074090100c6403070596080002084030001032800605a601c00e002080741d04a84900040100ea141c4407868420349003481d07020040c1c849450002c01041101054100b1031480c0d01907a0240400c900d1a05c4090301d40f400002e0288070340e8410720406122808040c094401e488411004041c00c00c40307500c5000a41d4810320700380210b03955403c0c1060400980c00d091300050401501c0401c0406c00741d401c0c2d903907a480380d04402580c48580340d51602c100082901124204c3d00910f054401500f0311402001c081c080600350544a0702103031482a21502d404084010f90607101000300044030801c0007400003d00c07004d13151100c05030003004003090391a9104000c00040071141e41d80c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 347513264 1250 347512014 347512021
    0x3021c0605060a0806010e060a03051f05180c0f010e06040f1805070f03020705010603020d0501051e101a04030f0b1015090306021804330806190b090f 66
    0x31022144020700452146140110030f210000000403031a040d01c3c086101d013000741c1c8660002030000d11055000400310304c15480d0042000081c51040030403807080c90000d02c50313619070040280203103a900698200f0360744031500c40c0758507160954141c0e10002040c10412250907001001c150341381c0c019008a40c485404503020041d901c0e0241c07410b4418100108108140d041510008000c118114014002c1503004951102400800c2d0302010056500420703003000407442e0714201d4040c0c5000c07a085e5580c0720a8024503120088441d0010344500c0c41c0d440385804080c14130b20008054030080440c101400d409010200c00602c2258021040034003a182c1c00c01d003840c100d220301400d18001d0300320321450b00140c489400b561781c011100c0742c1a0303680448050380740c04003d075010103061106100d80c1c2d4001d042c40380f801000094104850006400807001c910540a242c0e407a9003100d0b0588540e05a960241c03001441e40081202c0741100c40c1045074002c1485c9220100103550884103030790404007907001c0c0062 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 347514514 1250 347513264 347513273
    0x7060e0913021201150b09010e090912030a050f0a0e070506180d03031b05070b13060228030c030b030c04021c02040b0a03050a18080a0302160804090b0319110a03021c 73
    0x46000800321600c6e100d10b4182003800080541a0040c8c005000700600004940c2006041c064062991403048060b42c40b441d000c91554082c01064503404100e02400e808601440b84030300922a03005001001090350b0740c40e010074800583d00074030700091248810220944203942d9003a403040c0c22406545c02045100a25038000c24482200c8946010f000c0c0400400300050148440d5940c005041c0c42c04007003454190034054045d00c6000a03881040c540c210341d41c04410319518941c0c0142c5030543c2d04200140500c80240c0843c0d15580f5910340c1a8445c200c250441c0c03070a50024041e0201001900c0070300000703603140c0b400340d8010740c0290f00345240118001d4183c95040c403500d64090001c171400d00000e030500400f15543e00760800c0240c00400b001a06401d142e000c1d404881254010010b1030654088a04006450b03401c140240d400e100e05000c1d44451515000414854011041612064800c16035484015209031104e8554100004907800005652060404040c4540031110f0000c90f018a242 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 347515764 1250 347514514 347514551
    0x30d0b06030411061803030d05040c0b0a080a0506120307080a03050a02040b07030e01020309030a05062e06030f06090c030e0c04020a3905070e060307060e0913021201 73
    0x19618040c12003842004041001000405040e43d801c0c2da04c16031314090a103021003600c01001c89035030184800244440b55a0483d80441c1c4500d00405030b0060381030b260514100c2c9031045030410070020b500c0d600440c0c02c01e510740d030003940c001c00000c1c19091110205404203040d900070707800944800c080810725201c40341c1c240c06000d80c040d055540461038641441d000d94000e0245640150400000145c0e034049039008008480745d10900071f0840f08440b055103401c1da52084211450600304003820480112128900700c80d41f60000c00c4a0301c24049800c01d00c3c100c2c010302c400d00c4c009949540314580000c0b80100c40c450303042482c1042e0750220300c20802203410381c40e000c4540d0010340a50310420101a030180c5c0310980076400c080548696080d002d43d04c0140c0a4182c1c1542e1000342c1d44c2c1c6070b0742d2145c20030000044110840b80400344c4265a0350b680810192580e05920034080448c7c0d0f9110301000c00e250038480c4076030041d4403410b0160008a260041141d5407840d22a890160f951406001800610b844 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 347517014 1250 347515764 347515781
    0x105010b0a1b080406030f110408030c0c1008160c08180102010c1106070c020315071107091103040b07031506020c0406051e040504050a06020a030c0f05090a03110f12030d 75
    0xa4031410402540e1021000e104c1c80c0700740e07010543d590b42c880400e01001e801040d0040503546090703484588940c071880d201e078130855a4100d503100309008117803c1e090405038428401d030251141103c5581d4200242c0c40741d5003801404080003403540120001407882005000031325141818802c2d084940c2c4006070840304840504010700c0110351070480d12110004050380c4c00100340c94542c40503480c510100785001840c0250901e07400984080280459201c00c0001604100c42c0c02c550310b003640c2c3c81d5070030304507020050080c3c40401c0800000d00801c0900520607080903440c81c1c00111550f07444000b0305e500d1070b11381100c8016002481b080d032152134140159809850101d0707080d1035a5581d0401c42440c0300300d0f000064000c40c0c480c1c1c0010f045c0b00042c80700c0080c05400900070b5580d1080004010010808102a030f008140103030100c40240b031140003a100c3c810b2000d8040d00100741103840d40c08114a1009840303521150003452207003241c071440c1c6d4030b008008610000b143c44a0b00e600c500b000303485405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 347518264 1250 347517014 347517047
    0xb040c080a0506061002070b0c0c0913120530061009230f0907050903100e1906061208040305010b0123030c070c031410020a05071704080105010b0a 65
    0x1074080740451004500c40b5000b100403102092126a01e100c01d9081481543c00b80c044114003090000000b4408109503000b40021100c034403071580d81f082c0d040070f040042000a020724003004c611807080c0b4011802400d078007555942d0388240701400d0003820b1103d0b88041c00710807119481c60078882c01e030901000d007070032911042c1804107106003400e20425610040440c0d41c1d4090000011031611521000c0749482c0f40301c1c001d03145c1e02803031402c0c540150240c0d1002c1e00107400b900c40d40c10440d00907100d0b882161b458400c0742c0058940c00c1400c0181c5c0c410755585e00d0060301c0399507440d00c001035201450026080194820a803141d1280d18506125086880c60207a103030501c01c4c03407100284102c103072002200c1c0c08500000b1040d102e0312880e03000c560500481070000d10300780340d001c03012040c0190b62800d40c40c00003c80c4102c4000d00d1401c2d0810040c1c2c055010058040b078018000140000c00002014004040d4000c910742401c0c2c0d47d40070f040c29142c0c00c2c0d10202203c04000b6684c842540e00c4480030a0f0035044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 347519514 1250 347518264 347518273
    0x207060f0b0d020904080c030406110d05040501200f06090d08100e070810050a03030e0907020d0e0d050a02030d0905010f02060603060a0509031b03040f050f0d02150705030301030b040c08 82
    0x201240341c100ba03a1038020312503078811000030100414442175405460440c0c0c00c40e905d441c0c85102c042e01d00881c420300c5c1c1130035100b00070107151000c0c0318104440c00c1d6041030796459060b02d02d410101c04016209d0008840701d020300420340103045801c010292103450080700911b4080300c1c02c1006040c01c10050a0b0124443d010081804000d12008117039422001c0c40c608072505da565600b615004c60b0094000650000b201c001c00070a040c0c0c08840c040343c18004136540030642d102c50030305a0751403240300c000501044032044146800c0c5010906900000c0c010001c2c1d40e0203900c5035000904001708070f0b10340f5000c40e001da5418001c07968082241c26031010280014900c80c02c0040000342d40b0301e0010708101c802e032346910018049002c1402911841800e16841c20710403101060791035141e80042c041c0d80042d203210a800101c41c5840c10719070790503c0d4003500064000a0540902500d1041681800b5545000304006400588104001d500a5006400e4196542014a040e00d040d5203168000c100e00da10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 347520764 1250 347519514 347519531
    0x309050a0b03220201090801110a120b0d02041503050118050d080f063d030c09030c0308070f0b180123071d120115090e060411130f0207060f 62
    0x415140f2254400303444030445451040e440101e030105503e4016003015420700c0340c400805d501c090301602c1c3d10b0841c1d032550074445450441a1080326400c1340220b500c00220f010740700260515030700c00c00802e00b409560640e5241c480c0c480030702307482e007110110198602c0318051105000c0e041c0643d440e418264603119009092000c0c0d1010020300c003401c1c840c482d035501030f031040c4101c402c2d10a40c0000390081e018200403240346c400c0c0d50100385009142c80082410484000741c668840e9000e242520740c40880d2171102400c0da11000c440d070b0002ca5080390301602c401c026001083c2140d0742c0030300c280141c10b0700e92086444e24003218255210b0f151000ca100d0907484011500034044e02645078403124625262501600c441c104d00707a829002c25040f41c100784095100c02da100300c107412640c08410501c8814041d50740e42c40038042110204942c158040d0410350104000450312043e072146000000e00c0c0b1150f400d515076011080710306400302c0c0c800255000a41c003013004654001d080e00c03c146204101301091 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 347522014 1250 347520764 347520781
    0xd0606020a0f0b0901020d140402090a0c140c010b061c0c0302070c050f0d060c0e120316140c0310050a140c031b1210170d390309050a0b03 61
    0x9948160060400c400c02c8005013090000354142e1786c4100c2286000e1000c82c90016544030755020507a01039000e4465400040d14007001401a000e010007144da5011103482c80140c5861640c0012840d03503040e5403034032a405060b03500c1e080604007003800703c0e1103d0ba4010750350034118200c40c2c00700103481c103050040c44441c01150040f203110003101c81c250b4002403404844170004208030700100c1700514091170f00c85244d51a503441343d001501c090b019034803062800f815140480e504d004045d004d030b100c80311400040f4009031098040640d0890307800700b12921a40000d0009040c5202412031070b001c181c0e035134200300803800d2a010b486100c2d0400405205a810014031034400303403100600740741c01c61000031000f4085401c4c0b6012980c801c00c4610220a0500b05188030826160040c030a13010221082d01c401d00104001080380001921641c450071611b071112041e0030316544025410428000119041c0c0c844a8a00c2e82403d0303030350f4441da8420002d1810501005900e55880d005000040d406008110254 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 347523264 1250 347522014 347522033
    0x31605010822020d0201020c041505040b0a080d0c02210a17070c0b0313020409080a170f04060b0f030a11010f020304030515040807021302030402090f040b07180b0a050d0606020a 78
    0x9805403413003280748090303000607468003520004407a085071170240124011503c102141054513011181441303621804020440000c1c103c0c05600ca4070f0b000f40b50f0f000c50090140440500d891b2014007030a801d06802400705448000f4581200225040141040e00700405d248841c0c80284040d0f81141c1422450f46a6242a50b180d000345640044008045500100d90340c007000c0c3c82070750041060180b8003e51502c240a038001d400c0751804502480100d812140d02824010300c607458280c1c0e42d00396a510b03a00c5020141903540c1d805a0000361502990784103031405d02c032a58806001d43c410b641c8854038000010003065040c143c040c115001480280001100420709003030a8001d501d001c030343d03519503040034246403244c42002580605814074110f40ba0781c03d5000765200c3c5001f2205e081d0300e03a4580120f000c180904840c0240500300301000a4003c5000d00c1042c2e84400c0040c8032281c8440c0c942c8031000803988a1040000890004140c120051034140110320142c000ea02c042d0116881035911000c0d00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 347524514 1250 347523264 347523331
    0x409030f0c05120c160909080316030b0d060b1206061005091201021209010507031401060c050a0204020307090810110912160f06110d090b0a050403020316050108 71
    0x4028104003010140b007002c100030381810301c8001da05a983c440d441da0ba1075941042d803100360010120352600180b07040d480c0c403032151416082140145140d40b0b103141c1d00400a108080c10701859076411504046403210324851200d0341c0b0504001400c1c03440082008448003032100d108805921401c10013009854144036410a0240c0d820001e80700d1f600f00f00003070811440032103410031b0b643c40400e03030703402400310140c0450003142008000c0205031181c0c90110103a0f0050008980710460040041080c3e511403a0714890581c010780c01d44403600341c590f00050076603005960540000b1070000050090038418010b15030117034400c06041202c964402955182c500402c10042c2c400c2d0319540d5003410000c0c0500c24203060400c10000080c0b50340e01d4482030381d444074070782c020035001502243d41106013550020b4031071540c0310310b52641c404551405611506652240450700c0401c00188400001600c080010108000e007804000d806142020001008a100108502240750319103000f0700101c040c100e1401c1d00b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 347525764 1250 347524514 347524517
    0x7050118020102030f0c12030408030f011203050906090d0b040b010f0501020105091b190303230901020c0f010c0206030103150e060709030201180806090a0201020c1e1912030305040c050409030f 85
    0xf00c500d4119011b50400e1811100381c0010300c0004200720411211030001c600c0341e20880741741300282c1d89444a00d8100100010014045001005a4041031500d00003601403402c0040203405030201966820980000940e0f089501c0b240d800018031807041030418110251a0a10081100f4130b082703207000d907840c080190481030300e10140074802d409458145801000800003c582d51240d6501e260081403100440c0917484480f2078400350704080300c620300480e000c00c10164001c00c1840d410720200210a05003100403030501003182840001a111240039500a5000d42090080d200c0c100d1800c80075900c0f60a0800c150750810320401801c2a003010700d0702c080e030f40c080c80d00c821541d050440982e088000703600860307094881c41c010400314001c00596000901c1c404e83c00c2d5a200307103924061110049162200054000201ca00200a81004180340c0e0760303210040b143e1b1070701c29510b0790f0b15002490102d20940000c2c1d1101d0801040c0038032000584020b00c01500d082001500a44000703004520a121040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 347527014 1250 347525764 347525767
    0x31b09120203030918060405131a06010504050d0f0c050f0604030f020414011e06020f0c01080a0f060329010b07030503070309050f0a0201080109050c04170f01060b07050118020102030f 81
    0x30554808005468508102030400d1145244080b038005c80910202e031510b120300d040034001545600900306a4400981c805c502d103070b09031082c200740b560076100144240d04103c0c05203c0040c0940c0c48102c5113200038094490f400e03582c001800d11a00e4446181c101c80d00030981826448001d464940840b801c0303d420007044005809548009405000301c0380450310130340c80076000031820ba03881017003e00003007110084140a082c5c3da034106036116800c0d42240c515641090009a0165018060300366002d0312030354002803101b20020b43c450454011390400e50310681c0d69103c0219451905000001c1080355074075022440d85001100700b040c1c401c181d4010200318002c40400c1100740250088036010780c0c0001551a40c50000840c41d6494844c3c400681c005580c40340000742c901820f100b094021822584014506130030004100099085064002010700c0364004404241e6001c1c0b1a05010f0b11059481c1d80d03a928141c00e0103030943c0c2001c1c00e4207072601501825000140e030004201d0300100c840d9401503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 347528264 1250 347527014 347527049
    0x90503070b0424051806040201080105100207050a030b010e0c0c060c0a0e0310020a030f0506090c0a020313091517061f080a062304240e01021306031b09 67
    0x41102248015140c0350f100810b203004007541059040b552040024040102030100b0352110b00ba500c04058501a002c1201600140046e0030800d00003c0055520f00413140001e548002150720301501c1c0c1c6c400ea4000c0100350060280c640080089074010000c40d80c210700f04204555110384038023003d403010b40541c0000913900c10b0b543c02040482c545010007402d40e680b059401c10108040d42c08410a80000b0b40340ca10001071180140c03054900400e0b0103405c1c04819502da002c010000e40c8400c91090541c8403d2200d20f00340384404101d000a44480040441c040c40d80b801540c48040c51a0480030112400c11740c420f64080000603016400503508000f114034900c11204841e1066041c2c00110050050790f41b04402e1243c680c1011030074400c07007404d4101010440322041401e0710705a030010a06004102b80d441d902c0e09002c102820301507240000130b986007608514500b243d112800244c403400780c030340040000a07058401c8204224881c0144210009469801080c0f0b100500501d4220154060032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 347529514 1250 347528264 347528273
    0xc210f07080319210f0f060b0d02180a06020c0913080319020d060e24060a0302030606160f020a06030204050303040b0c0c0303130e0a0603020f060703030e030406120501050301090503070b04 83
    0x4003405001903696282d40c2c000c0c10b031104c006003111002004107241010040703540e000c0d8070f01c62001207549281e130f51820100c0c1540214040d41c440d130088500c040e5100c0c131010381551011900380082a0760340040c010048a41c040c0199080f0080914240c1c480e0056003402143c9140103c983c004c04891507a008140710784c84030070081c01400c0c404c007481454000049654140c2c84181d6006d2a5041e11200ac445007070060100010b10780c42149400110600100d11102d0194000d940c000c803001702490704100303034071142c026143c4005009440c02c40c0b816445000754200724107064040c0181d80740c00c1d4642803d010201765a48101c0c8250038200d00002110038000740240440400004001c05880c0d480d00000c911b030404104602400c0980803c040100e08500c0e07481c4615400c60703602030305074498002c5100030800a40c0003c981034050544402c507510031f4803810b10040019101a80f1845140c80351001440204d40d0160040c40c001ea1401d040c1c031022030030010954980580c800790091040d82da031300d0b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 347530764 1250 347529514 347529527
    0x90902010903080c2508030403260a091401020d020601061116090605100804170f0c0a030201020307030c0804020310020a12020a0f0e09061806030c210f07080319 71
    0x4060719120340801e41c18000768001c28a10090604200c02c00219400d80b41c5d0600d10044034490028075501c100000c00005104040b48a44445a044114030080c8241c40400d066484104540000380f800314090007108412565140b641c0780a200a258490b18604003a5440d01306015040a0148a000059000c20200805150000b081000501d000d9a8003a040050030960044910441c0b0290343d640005104206007403142d0341280d20b2404d5040c4501100d801c0da0300c80300413011510400c126030700440034108080c80c94a4880d500050703480c034101d003004007225000e503814401c0004000c248800369038005191040102822401a91812601e80a6584460b010300d0107941600104411000982002c03078626480302c0e07512104a00d00780c1d9001c0040c0110110b0f03c60781c0c421500c511103408580030301c001a034050310240403100d0443c0104001881a050f25940d400702000c40c506003d2103000a02c00c0c00303680800000100009414010541e4580c0104020001000924401c0d20503440c41901c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 347532014 1250 347530764 347530769
    0x30409050a051509151f0206010503160e130b0702060604060f030510020a091d01240516080d020403060603060f020301060c080d060302131a030706090e040204060e09030c011808040909020109 84
    0x18864106d41592101c1c01080c0c0842401d10b03000343c0120710000a990a000c40ca810101109412906803d414140341c1600c06601406410440701c0d500d100c00d002030030b4011202c3c00380c4d0080c0c00a200514114040005803031654110321442d0603207107005c100082d800102d0b500040b146160158070341922150032114002c95a1000381c0003406079401800604181c01658140c17548810414580311143c44a101042200d46680c0700281701001560030306a401c190a0100c10b01c240076543ca410881d481003000d9810941013511010340d51001081000407900c50038500b4030006105509561402c103001c3c01142140070b024000031000a184d6045801690107003001e5075004101858180785c8244180c000d04200c00300300f0f40d02400c60610f07012441c00003001e404848496882003d0325040802122003028082d100302e0300503413540740118225104000d107510070340b020002180c0b680d078001522030a480442808880300d40c907614100300440c0d19401100e098800f03154000c1015001440102c0346c015042c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 347533264 1250 347532014 347532019
    0x40b0a12020702033003160e0a0305010c1d0306010605030c0c0102070b0a0207200906040e1009060b0a0f030f0b070c06290109050306010e09071205030409050a05150915 74
    0x5044014100045c0c8070300c01c0e4442d20280c1c2490340088034112104003071100b40d41c0a00344000c0c2221410310b9912520310000b080c40090140003190341e61340c0da003609480d029513018000c62806400c3d81c01003ca5002c488003040d500f20002c010075454001c015066210140441010080c005420f0213111425012900c14039031101c1910060703d80351110000139007001e00c1c11601c480f900c0319126038070381e0300c4900203410301c4005124080d04d032258400c203c01000c05040c003508030700441c1103049007004c251061400310b40c050400400d00e031107080100010b2166681004078000e448000c1400070910481c3c0040c80258040d0021103145c69044056504152200d03008254030300b00116100d41250001e08488880090300d00102d81402c00c90040d2000036080c05001d80640c80f0000401000c0c180c0f00c01c0e55000b00e098400d841c0b034540c0360003090801c40b14110707040e10799500c00102004110140e100b49a40603041c00c9040010342012319052000130202c00139103118054040202e005406c42d140f030440341c442d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 347534514 1250 347533264 347533273
    0x301091a060d1b05090c03100905061201050c0a031103070801060c0309050303160213111206040605130203310209061903060603060513050a2a091e02040b0a1202070203 74
    0x10116244002c140f80c081c2c14040c14145000c038072400003a40640380143c82003140351041500b881e400a0003040001d00c5254005250040d5042004013803040303078050034404061350740d41c5000030406010b40d55581c805804840d81001008042d550020700c29043d6800313413501e41c0f001c0340182401c80e1000100d8000c25032601000841c201c60f0406c6141c0942482e00c2564521061000e1904e01c00071580c00d40318880402c03500b000111810f07120703003040561021004000040668450000c603400301340e07140d158500d0b0341e40002401018040d80b000c010000c40840401014828801e0007030a40c1024504000c1c05036240d00d000c134080b952a071086e054030602c205044013020713503603092000c041c0c1f55a01c030030b440003458a030106000d403a000e20103405041d00400108004c00043c0c0d6103410800342c1c400c1408000d402c00106650b0740a1400d08500204062200440c1012681400220000c802c890104000340704020070014003140d1001e90703002500311f082041020440c603144101034410490000d505005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 347535764 1250 347534514 347534543
    0x10311060d110309010f0204080a02190801050103140105160c021e33040e160504030203031b0d090e0a0f0209030109050604120c0f080d020c0607030501140301091a060d 74
    0x5042c0694810f06000d0000c0c0281c0c40300c109400201c4c4120f004400203500b00c20101009810416024000200340c5e1a140f1700032070380d07101030600f120020307042100c14518418000c800240c0034003800750082d00480c0c415801a200300e0001c0c051400b40d640c005d015001c55a00092985404050a44200c3c0085d00a070a004991445040e94040b0035100903604c030903d40310444d4118040090b02c0954440c21080300b103d456400305681d0003000a4006030400c0420080400145c5040c406018503401d0303102d80400001005d1401070404048481d030700200001d0b032000b085900e003207814071030f04080202d02c0010320468180c48100070b440b40d2800752ba00b544c01c005043d0100000040d000344035502448107003005034401e80d01250201075441016040c00304012600010652800050104103a00d070001840c1002da9443c80382002c1080b0b5a0308082a5208010480d046103504100140300003100200030890599a0700d03c003046449a19000c20340c00b000004100b1380781d03000b040d0100c60700101d19504045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 347537014 1250 347535764 347535791
    0x1e0319030b060c1f23070c1e0308060406091406090603071707060212130501031112041505060f010504090b03070308040308130504090b060f01030213060e03010c090608010311060d 79
    0x9401ca00c0ea1111a0b140842c038504115000c01020b50a48024011180d251078146d003c5841d02c0c4410410340d00d1060a90701d00b54040300304440e40c0c0c070580c426195040c0a181c803008000441c0c1c501c0c0e21041590341001c00c0c0c40300d03041d4214000c0350f20040840711a400381c0c903814007081c0740c0701c2d05400c003030b00076202590314100c6000e0000300a401c65020b5422145950040c542811050007160b4581d54800418801440b080d8003e4000208500c10a01610304146012801000440080e5002c0e240401400e220b00c4050312603000e0140d01c0303c0251100d074440d11910300000c1a40c07082e4800d03906501e07aa1000d50000ba0b0701484000c00564010080d2502c2d503403039051249403076100c0001511240d50110001a0a0620b07010b140c107a617400c00b8165419680d1481408240c034601b2070b0560416901300b142081a0011081510183c001541c075a4982c1c50000181401c49451302d4035041444500c1004000039503011030082c0c1503030390012001010040381c4021600c076004503405d03d9007403400d150140c54240c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 347538264 1250 347537014 347537053
    0x3031b25050904062f0d0f06030203033c130504180609060e030f0c010b150d020903251d040b01271d0c09010609061d10021e0319030b060c 61
    0x2622020800c02581c001c08540700b1a1070340e10002f90075030028003c13414640d2580440c000c0384504105109500c0806031500d0001d0791084c40b400e1420000490b144e0110b003006000b0130060310055504000b80310404180810040d001080141a0f5072181c03030040c10400b180e00f0140030b00320454101d945482c0c0c03d044d251156080b20300012001c0d860f003005104180703814045040101c8864076224a801d9030941400040d610000810760148103100e0f0660541c0164442903481410074404007190030300b040e00b103041400054400351720300b02449041c000400c80c12000b860448001a1464030a8141c804070881c0808110030311900540c41e040c1841c500444a42952000d440f00f0130036203418101080410040c8130084c003a140c00541504070130f01203240a00441944d041c01164078050101c40c110000785c82a02020400e00142c2040901e00d198885001d10010141c1080e0003542c1004900302d1140f0b0450017080e20b001c10140c035101c0000064486900b03c4050000c103405a9940d9440c0e40042d9205 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 347539514 1250 347538264 347538277
    0x703020c0d050313020d022404170f19021302040311010f02160e070c14030a0207080d1211040509040308011a070b0c070203031b25050904062f 63
    0x40e0061680c048025840354084910130034504040512030480c940a020b0090440e00e01260401c020440000754481c92001c009050b006000344180e44901f4410ba8841c156034034011109d0030361090f1903460041c00c3c00f0030140c0081020381c103080f408940c1c50002441910b000d080e0600c0d510310000340442442405014240301c0d0000b0f880d00729228a4001d0300b00c0e43c03158401150f80307501000c00d0741840403079032000700a80c1110321841c002c641801547c6034044e40e070820f1030800c0050380c8009011032801c0d80510448000b0842140070705440000368001034440804000e050f00c0b16940c84000c2d501c2c050308082507030003820b005070550016107800c1c640034003511401c0c001c0e144800c00c45241c19003c5280241110042a0f0040c0544480d480c0c1010441040d00207034400ca0381400f050145402c02c5518010042900c0c464800800c01c1581510b00001c80448000c0250b4624080700c00074080e9480c0c40d0713802504107901020000f01000703032a040c28512020b45e0800984040440d450304e91140c0200c024080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 347540764 1250 347539514 347539537
    0x140408010c09061b02040c030b0315041a070507080a020106030807050c0103050c16060216051617030a080606030a06241e0f08090a050a030f08090601080c060a0512070302 75
    0x2c4203502c400c01910400c2c841d00300e41094104080d04c080042c2401c2c0c0150060200c0342c14045806002000001d00300554000c1110082072210308201c2441491110451000d4140d400e6a041d800e0651008020b842411805007114500040c05d1207070034400d6004200440d000810191a806079250091702c4141003103602d40024246000b1800b100b590318111502100f005a00c8040c11103a6560305d0302030340080d0300c000c011800040d40348002c2042841602c600d450440b01680301c141c20a018400d0b65515a00b080b5034581c0240f041c202601c0e0440301c2d458101d1022244e290301c82e52412250405070965130002d0b01010700042e61013a5036100c06052500349121510394240356aa8202c195001115a458280c009082182ca800040e0b000c2c00d10f003070304540b107002924440115519190f141c00720342c110480001e0010303c16407840a43c0241041d82100560015081a514107440203a03114030080308644540800902d03201c820303004500300c803402d4a251070328030407515003a90b016000350880c090988 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 347542014 1250 347540764 347540777
    0x209070c080f04030b1008030d180206040e090708010e0307022e180902070506040f03091a0405041109010f080a061724040f031404092a0e0102030403060c140408010c 73
    0x1b070101900001090075a04140015414850f045c00a0005003000c00c400d00719403101725000d0000768854000600c05401c510400b09030b030303007882c6440900d040c180e0b0344240e0480e4940303100002d099001004a81c101d54040701c80361078000641c2032040700c1640c110b885404850f00d405141051640020900c0c0100348500e85500c0c0b420345c1c44d07015600342c3c8a0140020036a420030710002d400550780003043e980c8540a481c0150945440c1c050340580a40f4030304401c8484a000311b01000b040c90580180c0100341082000a41000c6070031001030256424015030720103001250001600601d5075900541c0100321040c01082403015001010391038a13600365180c082c410881017000b201c921074038a100d0155610108901c408100d98402310341d1902d01c20415580b418003000b0004200c020303409020034140c20203055298106440e8885101ca0803103084000074080d84400c400c1c07960380c021007030b40d003141c1c0c100b00b01081980f10b00c06c044034004075164011683c2c03034000c5008581c0701415400f2003100c1d0080d03107804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 347543264 1250 347542014 347542021
    0x80406020906042103231c1d01090204200334170108030307050a05030405010b10020d080a0e0718060801110712020303062d28051206040209070c080f04030b 69
    0xe44002d94001c0650388480010007d45504613207083c042170780740c0d080200014480c41e100c500c1c040c00811000c20f42d140385c1e44039158501035160520918851a14441c407003641c2c0e20340001c0102c0c40c1e002c010008080195003811503d1040d200180304115541e5203000d06030010070746034010f841c09800103060540c81c15041c001090740c80000044038000c11107501c60900744650604112100d81c0f005004568554a8030004882d903154100b01c075080d00d0094024004042d04d8100041034494000c4c9100c0301281041c41044451001040d22010744441038190340f201c1c0d11028044000d0102d1398040b1705250721302039100c1d8540c4c811402403c07501d0f2042120f10117040c04030000301c5c0c0d80d010945829a122448000c103000000000c00d040c2e00f4096103020a050401c041d000040160700c013147c64018165441035045942c0403c50701010191808440d4011070411048805540721740c0140000d00032a24140880d4242e0b008e51080f11206900142c25a5154403510860200380c00034441142c5000030175010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 347544514 1250 347543264 347543297
    0xd050a0b13230a0b180109110f0a06140703140c150a021201180f060b1815030705070f05010c0c150519023103051c080406020906042103 60
    0x201045005040c00030001c0758165202c1c04450000500b582c3e03031111401c2030030002e1700c3c4280601507900b8040e417941c406507142c0c0700c01d00c400e51805801302d911030110303101c0a21131560000d0b14604103031102001e05480d80298034068925100c1406645440d83d008217035180d0166000a821103001c01c0007200c0c103050340f0f40b5901c40e0142d00420789460480d03009170b001030150b0b5600b0005030b00f0320400110040303280d001c08440081151056009098500740004000c050052668207240790404c0c00e89020885091600030741d801c81c0006440c0f8800c2003800a00c2da0f0038000003c100c41100c0d500038000f0230685030848405089034800e244211504100b64070040004245449141c0c480c08552081d419403a401e100404000d501264102002c20061031140d240200300c0b000e00d180411281d00c06100045c01c5013483c07071030701940c1c500b00300b06080302030940c00d9690b900049850b000ba070300020144c0c960f8078410005429000d69080030114108005001401000c1c500d40040014003a455100f0100100541c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 347545764 1250 347544514 347544563
    0x221031e090a0e04050a0b040f021201051f0303021216080307030f06050603093a081f0b0403080f0d020a032903031602030a021c030909020a0c020d050a0b13 69
    0x7030217851500021840c2c00403c02201c10650300c0340c030445100140b04215400a5880107003079007110000e0f917440c0308100c0040000b01043c5450150700c0c06030000350b49150b40080d07442d000c1103084131070282e02180007586529035801e090000395014184d16103a24000b40c0060040c00e0581c011135165003400c000054505240c000c0341d024005a60191101c03024442880c000700f100821000701d40416006222040000441d41103444182130382c406c0e046050030041c0701d0016152035400400c1a40d1900104801d01000c000ca400322a4058030ba42d4031145c04c28040359080c06030040c00545507000080303203810103a0503800003a500e694a10700c104054295208402203034002d400c001d0f0150700c20000b03c60205484135000f00746034401011a1010a01540031800c10182002c05500ca80d00d05203040c401c06402940c1d8038060302c48140114140014010010201e03030450001034020810304140000380a82440344002c141c2d08450044114200101ca110001c0407a000a4800044441601c1c406141052 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 347547014 1250 347545764 347545771
    0x34082b1a0105130e010801021c1b0c0302010207051207052b03020c07050a0305010b0a08060c0313050f07030302100b0603011d101a0910020303040221031e090a0e 71
    0x1001812410203040103559070707440b07841070081541200c01c001480c0184c94100703502030600400090b8403200c5a2100681440920641007102070802c0d14045d12840c0e034054800341e40a9515228103544681e0400f60300a10a01901902d1703405161580c442014a4100810b09c243c4100c08032805048140756502c00603078040b43c0e24616084100b800c032903440c425000342556035590000c0c2c0303629a58070800180840c10b2640b089070a42d4461544940d81d1034a504030000030101e24000d04018038106c0c524159511008181c00c025030205811075050010070001c00c04960032680c21601c0e019100e0401a648419070b00d030030b680441c1010f00400803070070907000b0b99040792050ba81020268601450301d401500c4000c160020400c0c82c140f001961810307039544500c5411140401c01e94900e4500240906131040000c520155030042051100685940707800d5020b20310f160714604c0c2003801c0220b00508602c528016212a0139902001d43c1c2e101d260795004040030041181c41c02c0049a551026050703040040307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 347548264 1250 347547014 347547041
    0xc070807021f410c010216110411280e1008040b1e0a0c020a0c030b010812030f060d02190303020106080f010513120c02121507030234082b 61
    0x22404403490710344900502120643c1c13100150a100d0004600b20700014240c1c401da90003a020600a800b60401d4450814003c140a01c140d00d1300314148000c4d01c1010442c581044410315002441e680c5a00c10003024482090090040381443c40409004061880030744094130121000c00108012a01071803088100360795017882480b5540e00c601c1d0a4004040c50b040070720a5000e0b08421a00244001c40c610b400783d4800d090369070443d41004080c620700760010b8201003104000b0400e00c180b401d10250035581c4820102d03940700f690611032005c039840015804240b1029103003c50040101030301900f11605849200c03007215540c0c51312144580c02d9600540318080d0800e249850140403070700705545c5100250040c1480790204000c0c1d07000c60400c0307040c0c0f00d41d000190801c0c07801c00d0080b41c50464050700408645403d41c01d007003032800c00720804844054080316101410070301d182c06508100c5030100702c42c2c1000e540354441c0f840104810605103401d11908040c103020003407240ca908036102e240c1c1444401c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 347549514 1250 347548264 347548367
    0x303050306120631060c120c0509061c09020618040b0a0b03040f0303061503021803060c030114180403020609070803040b030f1801090c15080c070807021f 68
    0xc4015028184440756850a1350403084505840450480d004001c0300c40880d03a60070403140c45400c103000488031040c80700b0082000800c0b0078821640e40d9004d843d100c041c2c1868008282c11000c800038020280007d0080d00100003080601016031074120300700700402c040d02c00780800b540303800421002c9800c07401609041041440403d0105400110a1312618031a040c000b400580325400f1180d02105040c140c000603800003040744984065914040040f04250b00030207040c100340001c50114081406032402c54480301258004940d2901d444151411040500b20b0b4503040a040c003e441d110100c41051841c072a440d00001e003903c1c00000c41d022504030b01001c41c1591600c603180c56841001402880800381c04844d1000a24030a07c2819259031103240d442656031f1410743e540d414100701e01c3e0440180200c503020000008090022038142c00c0e4800881a0303904098030003e07000700148a007141c144d01540a80c0454103070011000c48041901d030f258491084804400b654080c50040a0b9400e80b150 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 347550764 1250 347549514 347549551
    0x10e06070f240905060402010f1d011b0c03060608070501020601060c02041d0303240609010203040e04030207121103010f0207230f1516090509040b070c080403030503061206 76
    0x11803000c181c00712440c058440800020a001c036070141d9040781c005132501e03004007040c4000c542c2c200c0002040b018140c10943c60040300c107110112480c400251641c148030714048001c113100c111200b5442e02e1548444000d482d2070f102e041aa0045c4818004c034010f92250070780100d440e60002601604030340560750340f400020850790901001c0d140e0b80c81c0032020050081260b11a200040c4050740c41f4407110f204122940514010112200f600030f072640340900410890480f441c0d07800301c00c580c1541c06208910380103480c0d17485e0032440c20826030312020a80301d4101002041042c10502044080d200302c00922a4a40341c03002001284070310705004141d5120007418030b02405050341d00106038400101611074000383c200c0042e090803140075400398071210003010481c0788035030b0548610034042c5a144c40040541410046004000043c1c800380c15040603000180c3d41e1445002d03403940d038941c4034011a031103c5e50703071a000d402500140d403000c2c030074511111014181c4000184c258801e101624200fa030480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 347552014 1250 347550764 347550773
    0x306080d2615100305100314070801090f1109370c02030a02010e0a020102070b030a0219050405010318110f03120c07060f0f0207050609060d0614010e06070f 69
    0x1440c80041000401081c1c041e039410425a0450314401c090a0010360806040c0404024600d18010440740c2894540010710202c12400c40c49003050300c1e4061458850840115241840c0c0161a0310401941d0f0130407010744100140860f50761360341445000300340300c48000981006281c4104584451140c000c101051410841c240c001c0240c2a02d2058895040c0d80c1805000d0252000c0118001c0940d200040a0944580c24415500e80c560802d02410759030181d580000c0d280c050394801d8500000f0040701055003060598101c0700314161404d02c0340b02c075484140014211707405c1841303220b002c24a08014020600000b1a50030500e60f03002400702a4030640a0400c003805c20400c120a41500c10039900700d01004a80005049042c00714000f81059490074400a003a0a0421100010090103002c440b000d2500013171140f050780c00440b0b07815181c030050000305d405800f40340c015100b03103418103800240700010745154601c4c01300280c0e115886a850a000c1c0700340c0d440b9000707000b03010240d58249500884d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 347553264 1250 347552014 347552027
    0x602060105130b01030b090f1f1d100f06020a210e01030e0a020d0c09110f0301120f0203030d0e0714010507110103020717120601090e040209181b030705010306080d 72
    0xc3d00f05050000b06c601d2040c0105106081c201e030381d800d10307001200600200a0032402c5e200c0c1c08018190246210605000c4c6141162020740324001e000c88040f004252407002640703115000d850106104004642e071000003e40e1102c2c0400b041e41c0d05910800b038200f41380c0f42e01903d550840b25036120000b618149600440c0203003011075845400e070207809001d400699600d0b02c500e840b9806002c140401a040950783d40c1190504210f1414102080018900081713503201600d04413941c00d880400ca07900181003e00c000101c2041c000e505000018010804114035404820b1a031180002c45000c0d5442e10000c817003101307103042400c4c00b050040c803400700042d900c01a030b5014040185005070500c03241d692250070002845000c1e07002d94001040c02076124020b84582980005c0900c0d10303018440c6400807030440c07000040c0c8060300031450800000d2036554a084106890703600501100e17031049160f0454035240b00a0355405200780103003000024258420b00a01782070381e0703048000c2e014000d508401030300c60 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 347554514 1250 347553264 347553281
    0xf0804140c040905010f140103020924060a120b06210a020c030a260408040302040b21070509060a03080306010c06110403080418151203020109020d050c0901060206010513 75
    0x4511844001c100c141c0c446010705456284990000310740d039503c02d03440300240c401c130881802100c1c1d80c803401040940e42d070041568100c03200b0310540c48909140000040641d004c07040094002c24000760485000c0c2e88144040402c602084e4204003429003002045014419840301c0c103615404c0b0039031f8001d20b0505000080d001000550300600d01079000341c00909580105030300304081a0f03c1c64008118520004484800d0300c00c0482e4030806140035540e86000d40124000070380103076074a03140c02c04940c81d4a4034060002445503d064044840e00d000b50396034141e1030044901a22a0700003240741424960004410f99600540e89800e540d0b4060044a102000c41003d941590319000320300004615000100051401601460340e12401c0c091b440c4005101d4072135440d02c1c10700c1c01c0c0b600106030080100c6231042e03620358014508202064101240034004540000c1d60100318808c11600b0040c000030801c0e034041c400c0e10341c00c038660303600c1c8020b9845501c2481445d82040c8103480c0f10905030340c1d03948140a03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 347555764 1250 347554514 347554553
    0x203072a050a08070b36151008060108010e030a0c030315180b0103090c12080f070308071d0315070302040b0d050a050709080d08190c0e03070506071a061c1a01060f0804 74
    0x88408020040c82c1f61654140e81924540b088005d040c81701c0e04042c080a40545008402440900d54120103196a4424801031204214001240f041018802c0e00180c0046c031504107046515a00d6481c070b00b41c40024100310f501454641181003002d1350007401103811803134001c0303000f60700e5900d4800a14440150310104031040d15040254402c0c2c00300f01000341480138040d5694258600e4140b8004c0d05408025000c0c4ca0580300c500c0310210b0a0368001465002049585010304282e185c100d420382c0a40900d8001c0b82000002249460642085d54030003880349240c10400d000a4684120076140c540590084084941040d5040c0c0100360240741851342048488044001c40d40100080c2811034000c8021080005d415030585c01d02485c0c104040000f0b840f0441d002c130304c3d2424590b10102c140e85080e14113542c4054200c0020031585d40c0c0406401e510060307020740500c1e101d00b864503000744030100c0e151200c5581c9104c00803920310300c240c0c840c24001e03507a5207840320305460f15250b100e100354065503e046d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 347557014 1250 347555764 347555773
    0x105120a0605060703021005060a121b15030e010f0b030d0c0302150f0f060406210c080102040305060708220f060b21060108010203072a050a08070b36 66
    0x40c1d035407221401130a100380258040d10700505210030396001e0b43ca014040b21301c41c0c8862041401034051480345005282e5001120010410f07400444289100446e446580701000c0c566000301c00607010381180c40c116118600030040c11018462180450f40c40207005605030384400442400e030707400f640f00c0c40c4040340640115011480035441000d080b500454007460403c2ca400c041c00f4a50a8444041d604075008035000c8c802d09080034203000c018100c01302d14426001d420001d100500051151135070282440c81d000359a202c0d141c1c10b0440e41c03410240e80850001d61130000003000c580d510702014641c1007501600701c1440b0010b4450101c4424207840680702a956036441484582c0c5a40c6825000d0380c441c1442d02c0f00d01507440c2082d0400c0c0b4160702c2200345034010020005010352102071400b2040340d19881c20320f00c117407118038100043d80c0c5580040442c410350040c2c4040c403028001400700107102d50800780c820707500c202c50741c01000b40e40030345003181407040c501061200d0005566007064146080c1100e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 347558264 1250 347557014 347557019
    0xb0a09120f02130207060b040515010c0317090c130b03030307050d1b030515030109210c0c09020310210305090f030a080d05130507180b04050a1b0e0105120a06 70
    0xa074818070403290643e0626400566242002a60f024041403003030101c0382000b5515000c501a624609050001c50410118a034400c04240c016200a9a1082c4003080d03807000d498a0f0400715960241085a0382c0301e00070412440318040601e00036a00520790140143d4103584034a4015203850304580f0394000f5003600c03602d0f5100345880007008114040d0040e80c1c00704450500340300c18020400f1800005000c0d0b41070a0040000c14030708905503102411141d0000c17501909074004503020001c407400204207080c01c6100089010700368001d18018061401c194011540d00e6040e0038109001c05043c0e10007074164521407000c22f008074098541440050040001e031003684000038241100c3c0c0ca001c0f15241c0012400e0144906203100340c0e644480e0b44003203904050171984455503155410701c01d9101c2c060078101d417208041038540141105030360180c028069401c0002c030100240c021901010380c40c903520060341020600c141a5410722400c113031200361801c055403080514802000b012851180e8588000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 347559514 1250 347558264 347558269
    0xb010e030f07051003140f06041103010321090806130354090506030c0406061e2309041103010b0c060c03040215031e0a02040e010b0a09120f02 63
    0x25078281003203406842224105010008011038000c5a0b030100b40c901210b288250010b00007494000b450607040c00d102d5616040090302401c40304039240003580c404000001040814000c3c661801c2580321290340380b0210b9001140c0c0d1040a224142582d132086012540b014880c003070b80b0300014041d02e009061030200760a0b890051801130b00e407503000da014003112180000c4031030304504040a107111000c0d41c00c4910701c0300c000040d124040d2b03599244d61000803030366980e810461403503800340160051012a0fa00c1030302030004c0e0782058540300201c404030304003081280300d16030140f5900194240310790b40781c074110132400e01c03038100c2203195400940c1c3c0d01c3c020b00759080c5003000c1c500a2842841c00d42d0f50b01120324440d4100b60002e0640f1101c0c880900500c00140d0f2900704c42c10013135285200b16500ca0350396010850768800d004101c3c0030311a0f0444184401040b66400030301c1640c0130458003c081d03036614400750849108a409a400140c00030700700340110145a120003024501810107002d440349641c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 347560764 1250 347559514 347559523
    0x150d02030115050109080309100f0c0f080307020105060906240d06082b021002030406020d1103070e0904020f150408031606060503210a020f010509010905010501050d03050a030b010e03 81
    0x826240c2a45414001c0143d90380c40300a99000e051604040d50130700c004000420000307050040c81d00f041c0100030017983d260b070b445400749100b20707600044907540922031420321040da640306455800040d402c2000040c21400e14a0030310f4020b82010707110044210b9440d0320000740010100d1000b0980d1410056594200c001d4080c40020746100b03009400d8500001c1e091b190810011414501034840c5195203004254000c0b5024622184c0f4071005a0303641d075285480d40007481070040d2094618a8125244802aa140f0240d80701d205c1e90b032a1200b240221004000110b030782210002d50180364541e0803819401c02e0f0700e03203040039a0188030703d50615440303516071411900039402030744800031714241c0003007800114004c010040c5001d81c0981240c4051401c90107114491106880b0440d10000f013034000c95108101d048940e65019008205504110b03004038045c1140b00815034583d070800c0e001107803502c1c26040b511149685512040d03e40201a80b041d0301910700c403121581032000d00740c1d40c0a16030b1810310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 347562014 1250 347560764 347560781
    0xf011712041419030b06090709150807092310170403020d0210060b0714030d02040b0c0607030c0f0807020115062f0304030807020a03020621070c02010503150d020301 73
    0x40300c48002080ea107081c003920394019108140300c250507400402c0404d40d030509154009109480301202030ba2000820784015031162b1200110061081c0d1020502d5841100903000c2e41043e503846000542d151400c4030380d0b000500c4e01c01d82c24034ac140304034030707092800c00407006480d81641044c401185000c5428000c0e100129022740158008081200055071705110055650441c89000c02800c3e040a1650340e0314051030b00b008103c0506450035500f1100704006480002244042c15503445841d802d2004158008400c1c0030a00c7c400c400103c3c40fa14000e008040c11340416a41d807048174100103004845025000d4074280955680b00134006001c01222040005042e040e01d40000d0300e00103c8a00019080c00e00c1c000d40d280220386151410305401108840840c0c1d04044916141c6805000240c0c4401c21988000d503c1000010840d01601c1c0c01d0006028400c0b0703100010103281c0c2c0380101510018400840240050f03002c20000700c0c0c00039541c90645202a0150101240009030b80c0820308403540031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 347563264 1250 347562014 347562029
    0x309041a062a03040608011202030f0f0106050102120c2104030b0c07020f0117131a0a060e01090c080c0313230f1212090313030803060a0e0f01171204 66
    0x41e031401c00100c00c1c10719a0400e040002c015458a480c00d44010705d07411040c0a658000c0c03545041400640da800c019140001c2410340644180c41050403c0034000c0c07440b03104090160046050b1617031403000c2601511100c22a04010307000e038008020810110f03102c01010300c0210030701031201101080c0c800d140702e0300c20b554020f0b285940328a1030040046480c0c4094906040008040c40051150071180c003840e040300c260461b044000d1560320300803014000c0e58198407182810013040000841d040e400078030440d84000c88481e0300740d807101203031800c3c0c40c010a07060000c9400f05d804501c40022040085512004000141080c0709080c0e031102481c15503140b405081242110810b96255800d000c000751020502c00117124104100d030078502a4002c0c5000d0114040006001591141050080350341c03000341200380b881030301c0e22480d1102c01504103a61807800b8040f4001c01007a40c0000b9011680290341202c46504a0ba20b07080c9814040501e000e240d00c414060a0f030100011070031100a0300c09807a10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 347564514 1250 347563264 347563297
    0x20304030e040f090c150c0605090c0103060e01060e06071103030d140105010e010e04020d06080a0b09100e101a060f09030f03160f02011709030a0e010f020309041a06 73
    0x4030400c0005540f034507005142c41c5450034442c100080c08018192045a029603017000a451030440f081c0c1d5000e04a150160030f1a05044c2008100f0402044100903d4400d0301c0401c4469241c034140300307201c00c00b40213020220380c0e2415800018605a005440d01a101e10103090403159141c0100f811a00201700c41c1590b1074584c3c40101c619800b8006a40c007400080c80e000c2d444c10103280000b00040782003941d50b80240c0c0c1c0000c6c42c00600c82c081d040756018040690807251204000d01c0c202d04582d0301124400f0302405034803503004040c030f00c50086918040880b8000c1014400f40900e040081048040c03080e0200340e4104942056150000900004991050001d45400c44041850b09081d5040d40a04c0682c100304a00a4240c00b002540348617690001c0403803100d81c5161005071440101e1002210391002980d041140600340007004121400003540c52a50b494450390054800d0a00c2e1503400c3c2c0582c1041c404848181020390190100c460541c8080c0d020301c83d001d0104e0120b500402400c50040302 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 347565764 1250 347564514 347564537
    0x8040204021c05040302011a1012090210171e011707180b030609070b2a062e0522090c171605030303010e071205010e01050307050312040b0a1202030403 67
    0x1020720403019031034581c604c2302c2c0307640300d4030400904040100c82e2000184040c1440a00b02c40149900210300b180e0b0140140501c0d0120043c0a04a00d8001d0030440b05851088005142c0d0042081075607014010019a090315900b00452810100c000610810f1944900e0301c000a050b4000c4000f4000c0201c003d10000381203001200303144c00d040e40200706c01001d901c00e100800c0010b582c14102d8814423004250f2000114550350f910000b6000014104480d00c40e60080c420070380d022580d004d4418102e040c0d0b144560070b40008400224045110303640d445030500d5140101d0300c0108011140c4448924000102000d5035691144030354026000002840c5060b1a03d40d00281c003080822040d2162500c030403c00e514100000f95a0f100502440f06c001c14400c0204020f41c0c000c0d481403031030402c60141445039607164801c076440c0040900c1450b100e0300c288980054207007000300e0b013044110049100ca42c9028208140044180c0c4600318680030803000b40404c1030318603464405180960700c681d41c0c1c43c16522 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 347567014 1250 347565764 347565767
    0xc120301051e0a15050408011422020f010f0306050315010602061f03021314130209060609010c060e0f03030a050109050601050a05031b130303030e011404021008040204021c050403 79
    0x103a2030241510182d141c1c50100c40c0d81c80890407002c6920100214201c108140d038116102d004a42c02078201b9824440760a030120428200f20f44180c036213003960340080d440c100c3c489a80f02045c6030043c0d0005034201c9040129441440c404050408906020030810366030720100c0d1918402e0300340440d01082400c01030283c95810720950390410030707011401d4070044400032202d0300241d00c1c1c07200074130403805c201241440c00d4541e080b04198030071040c0240050300d03188500700c80109294004074400d440000018483d0f141c5a4155510313000184e54000c1810402d642d44030007032903032403444100e0340b184c0b08085552a00400041d440b520b080040032940b540b41c1503107402a20700282c0003d051110501524442c5980542640c1d0f01c42e000c01c00d000809070407001100810312800040c448503180c220804010303d80c064014000100050008001042c04110369000d07401d816500298000400c4028844861003104c841c0d802c40d000800c018602082c03444e240a00180010001a0311502c50040000f8103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 347568264 1250 347567014 347567029
    0x906050d36110301050f011203120204090b03012d020702040f1e110a0f0f0e03240c090d0818030106030303050114010201050f131e03020604150204050f13020c12030105 74
    0x80b070705400074040d508103c041368141070014045c0308242d160f031030440c10038103208200385840031002d10411035950740c0702c0c101c2002510200e548240030f9803d0040c801922024140c1240480c041c2c2c400f41d401c202c00c1d004010020750701480050341e10a4580d0b02c0003032418070354404d48110510b90340300c00381c81107080ca503150306171100b240c04100c11600600c0700c12900c41e00b001c000c4031803c0003880d145145080392681500c40500c040c400540602c5074950700540c4c032448000410312520041e500140c1580c03100000244c2d40714114000d608010507010020010b003071a0060510445000c04403c01e80e00c591010a01b190f4541c5d20660000b600d40b0300401003110003001c00002c180c000c0c40284114500090394603e110400340c03814540c61200840c01c2c0c24002101545441c2260203100c018118240e800d009590710300a07a400d82d1042d89450380c0f4001070702e60b403007103508a41c0041c014402a41c0d040082103036820089401c2e114907a0204401d4028200034070511000855520006403a54142014040705 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 347569514 1250 347568264 347568293
    0x1809010e091009030c03050306040e0d02071d01080a1403070f0b070e030307030905010810030204021308070803160308040c03021801060e03011404080304060914060402030d0906050d36 81
    0x45883d148070300b00880d42c40610304a0b601e42604120307030f49885140210f402400c800c1101c0380d46000c0c0c40f221035400307640421402d0407511400e1085a03940f070010100340c1c0a440a11070f0420315441408260000bc140241111030000c91205580c14000a41c840c2d02c0b2003589000107c0e020b00000c2e0802c00c2440d0041040c00005405400035410003159076030280000c04a40501414402100c0001d801008124880b030042d541c01b030015903c944000c00301a0030b14005020300840f9010b15100032504040000a6410000241c0b44e0b50502d07801030340f402e4844c1c0c1c1c000b90080d10340f4001150040b0158444510050840c0768500d00c001b119803521200605210340c0400c4540700740d040c0340c2010307030b0039500c80310450704140c109a100d6981d0700c0c0e51905800401c035a01004008028401004000c0b5501007070980c03256000343c1c26100c4c4410f4524044170285000e004030408260184446036101c00c40d9880002003110f1658800c4042c1c148401d08022281000100c0204140c2008280100100c0d100000e01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 347570764 1250 347569514 347569543
    0x6080103020108040f020307090e010204050a06210b0613060c061a03030901080c1209161e06050d060806090a0c0504140103030c0c1d040308090c01050f1809010e09 72
    0x10550541e4002000c140c000340001d042e40450810341c505640d01440804014060540204000f81c92180c1c114042d41241c407a0601c501161040015424001c143c030030540d28070065825011080340e61400018000c6a43d40350704407100703001070842e0186420700c0c20040c09403600c0315250b06010303107031a109960040c0019280300c1c1d04680001d0b641e03203000084d507241403024200200555a101c8800002d03004444070140c40701100c81c184203010700003040c4109600052420b05410580303c1a1101a5101c00e07100b00d05044c00f000300802c0300c0b40c8940090081e82d4000e000104195580340a031506d03045003500d103400d40360052440c2d2410850300c0507110b0002c007011b81c4c050040100c0c4401d408148101488098180100320642d2000c06c042801d01801034050120542448008083d060f400b4010413a011408140b1038804500b0700e14002400d1035074030005030340b05858041401c983c82d8a41e00a00401d8240700c450783c034014002d9441e4221240039081c50031070a0001c0c074000c05011314014074500c1210 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 347572014 1250 347570764 347570777
    0x306120a0c090608012a210516110a0203030414030f010f020c071d0402010f1103130905070e1e01090e0f0406060608012102121b0406060215061e120309030706 70
    0x1182500786019136180340e80c40c104006900701c14407a41c2c8030300b12420b031140a060b01c0c101c2080410754270761514262400c000d44e948011001c0850000f641c400014402039810b6000b400200034410a540c5c03044140072000e0142c5558541c147c1005003540c02c20084400b00b00e03000703d01801030b00707402c00084c0b00910040040c02d6483e620f5a420818020020b08064100527000e00d2900c1c1c07070b500a548481d00d280707118007100e03660404a100050011513a002c5e445511b801c050201c0c003a0f521440040c1b0300c50070000d042c00c0c1c100c4010740460000c11070f44c0032850b0510405240014460080451551055400b5400580c0307924051400008a4000b500030805000344003005001301088a4034550300c03da06042c0c081c1c1e0200700390000661040c0c0704c1500703040d288140d002c6c40c1080c00b00c100c5850035406003a036084c415a038640360180d881d1603005c0344000a00303840800055040c944100c000f054440090400113507115403001103500303107403000c5c02110300d03a0000a850225080c1080f01d880207003400d141c0903 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 347573264 1250 347572014 347572061
    0xa0b010e010c061802130b04050705040308090103050a110c1605030607020d050703051303150b0303041a1305040908040e0c0a05090d1505010f031707080306120a0c09060801 76
    0x6031201211000107444281c4c1c8036008201107200819903d040c540041c5044800f141048002001c0c004140e200c6000f50300b4100460004c0740900181c0e001c0e6a071124005d801c020742d42d401140240b1000345141c9006484600d0310f5480041c240c000c003126800d8601a007060036061458901d140b90503800680203034005010085087d80c00300c0c0741d44558160b40741c11550341c0b6503418100c40501510340070701134000c4123007000410001c02e2b114084c0402e441c603405001601c124010980c40707008030b119403051070041780c5103418810300007402401c0030054412103c0c2102d40f14004a012514003410032a4030f5000001c05106040000c0d010302c1d03020f141c0041940c078240400f0700040c40c9008481c4000c0c01018510f0408040049090f04503690f071400c3c40040010790703900c000c03255880b00c1038807003910002c0b07803080700040a034100c0d03044840071034211814614549516041c051001039101c0002024010300e03291030001a60042101c1c01004901c402240d020300302a8030030b00b102c10030140140d40f40000743c1503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 347574514 1250 347573264 347573267
    0xe0d030e120d48020a140f040608060732120a051b160515150301150302010e03030c0114040b0603011b1202040f0305010e25030813030b040302060a0b010e01 69
    0x140d54100d12070300122620340c03c1c502e258164031060348000a610103407642010411414200c1000c4141e50212070242103c070483e070500040f180303d80a2503009802890000d40307007038000c000300104c000d0f07900b9404010130440e0940158601c00a0034003981d01c0000501c500d00e50b40c8604081d904110401c80801c0305041c01c640c4e40b91001d12224101d11056000f2985064600500c41307501c800c0e035000300907941d0170140d41e407200c080c0328411110740104402e46691507850b81014403c03040c80052401c1c164114a0440e0015101080076a070002d616100030040740030074034800c0c081c8800031003103003034141198100380c0340503030385848001e00c218000d0380340c5180103030309000307884074405502c000b4180a0b103004c0101003854080d100b2600102440059482c00004100c815440508441049400d4130642840e442c040203400d0046100410019500340d0288041a50300d40208400380c251024254100d0b940d641d01f0318480412981039002d0380103c41044201c19650142c26041c40c000d203403251460b5a0b4000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 347575764 1250 347574514 347574587
    0x70215010807060804080f030f06032514061b0a030e040507080601030c09050a0303020708011b050a0f0909090605060a17030f070c051807030b060a0e0d030e120d 71
    0x20f02d004004400c0003040030701101c0c2c0c0440f0a000c5ca124038040e0340c0c2c58600005442103006a4009010f8810000780709a01c80c2c80f4000515095242080c0c000350a14100b08404211ba04000306644010108144188880c0355105100c04018074400303407178200f5440c01c02906110a603121680240d00b040c0400059130780c051186035000a090900291496110800b2211a2099008150001c4c1405000301c2410340014080e402c4134041402442040c0001d441d507603000802d10b60b0140401c10a00c0386800b00ba000e4080c00f8020b5440e45400544103607141e03500400d0b1011a02c0954265a42d030303040c0a000d0900b01340b1003000d4202c014107000c256540701a00b42d035071b12484c0d0480300b400402140000030058844059002807074004d00740d402c1d0b00140d01c04420551001d4510710013192400107842d8407810b1281c00d4400c13641032a15111200030a0000b4043d40351500f1004404201d0381d000b403a4040d903541c203c0000705456000007000d1000010324054410755807991814048042001c514800d8030800710f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 347577014 1250 347575764 347575769
    0x60a02040b0f1e03090a140d090635011511030d0902040e1b0109060e100f031b0e150403080304080f1e0915030f01140604030c0b03070215010807 64
    0x5502c99403419900403103804105000400400301e180003040c4540180005840c881e501c2c00b5996003071080c030100c400d4039940d40036240d0120109a840100308189401100141c1c0702c254154506c041c11104140340b0b100d494254419020341e10341080c014880659064942e20ba1500c0c0c6041c900c0f003180c41d074071341190349020340d00d10345040301c1e1940303d100119181d42e04007818280c220707000c960540050016055803200440d05250001310052400905203200d003002c2e000460000e01484144070303c1d4030049a01c00c8040e2400014103840c0d0302c6901c442c40c41c120402d5841419640d03a1a0300e083c58804009014580203080381000301e0a020601c040342c84802101d400680c001c000c10380d81e004030802c0203800c0c0a1350000052445182c0000b1803c61408401031505800480c2d04540c21482424040300c6400306903005044d000c4400018400e004045881581d6a070b070040a050810303030307640e0350a00040caa98220030000d883c04400d000080780c04000540d0301e02203100c1c1100c501c1d0305003ca09940c425251 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 347578264 1250 347577014 347577037
    0x601090b060c0106260721062304020103050702010608030316030608060a060f120f030f02071703040e07020d0203070b04080912061e0903120603030d020a11060a02040b 74
    0x20360000c806603440408641c000e02e80c200003032100540d600440c000824400418440c110442081070500b44800728580c2e00355a80c110070400f02003d406030607995108001c0041b0340580d500c40d64040010390000b14119030100016018110b460944001402d80384060801c0065a040c0702042c0f00240f404000c0e03a0384140d071509002c912109420703044002c2c2c0919070103c41b07240078101c28008241141c0d0050000d45004584e0401d010341e4620080862164407a0050454084810000f000074851009074071144c004c1d1040307030611602c0c1e5621660440c02d1000403d00c3ea0f1001404101c3e5100d061482c0c0c0c0d101c906130000d404141c00d03010000e510703403007200d10085c4040300d000300081c2005204c0e0709036403480d40007600320fa100d04403004035a42d94042c281d42e80019154041c1041301c045a00a049910401208007e9030070809803200603200d401d40503260769854001031044441001051001d0059919680d954000e05250104018140200030703015a07600e500421050082629803412201c201014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 347579514 1250 347578264 347578271
    0x110f0a030c0828030b06090a03030318021002010b0307120206030f0910020316020f0a1e030306050301050a0516090509070509030a0609080901141611120f01090b0f0405060109 77
    0x52034444198412641d0040c1d00c1e400c550041c03e040260003102841d00091510204042c0301c18408018440c02100c45496000101e405c1c06e10029200b5002885048001500d00030303001015400a4002014038030b20400503955104010841d18040208500609281400400c07000e05178021900c20b11004009184503070b2924046100c413441040642c64107590f120f0219200d00380900e6146004c400c1e1604c0307a0042c03062404000007004080b401d152459801410004c103494114030140710000c0e0198182c0c2450354030200081c981d02d0a02500c0d100c5d001a0900180038503003c00d1001000340075031040720400409207018841178942100c0280c001c11075040c80f41d100d6000700c000924141034514014800d60410100504104801020702030740007098940542c508400c1080b0501406062a07211620599038a108042142d0306c0d82c084070280d015100d000c1031100303022074a240c85968070311011039030341d155101c1c0d00b402080c0c845a5006520040c8400150074943c0320f865642106020380a005c568 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 347580764 1250 347579514 347579537
    0x1e0903030a08130b01140a0602030c0a060b0a050616020a06110a0b04020d0f0f050706031107020607052e111215060c0d0e03010510050604030618021201050601110f0a03 74
    0x4000920f600850340301c0d01d0030302d40f5a181d4040c2c001071102c007a00b00340154440c0401051560000c42980c2e092040749004000f1540192104c0f405070480151036a0460030702d420204054030b1707500050101e900301358850520b030035107403050140c000d03540d5100c02c0c10030100942200a025010806004190b004001080703070303454900000c0c000c949003200c0103007003190243e4807904202c040090b41000c140280c050f2003e15584403000d4040d6a25071001100e412030410240e00103140040103405035038058021181042003109000d600340c0d0601c600c075405a5001000070000042d0744c015040c0c2c00c48156100c608000d01003c1c107039040c0038082c3c801c0c503e400401d941c0c580951101c200b9038001e040f980049030b144400111029103018202c1c24054025402c0c2000503200c2d8688501355012600090942c910b02851900c4260041c031060045000c101c88106000c4050303920714110000d01a0448000511410101c0014103400c11400410403145c0260320001d5500c0707404a2414100794040c20308804c03161 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 347582014 1250 347580764 347580781
    0x9060b040b22090b011205060a03060504080408011113080714040203090a0615031b06020a0b0c090604030b01210c060e030109080a0207031a091011070b07051e0903030a08 75
    0x8070300c4510311001001c42c40c0010b0900c45079003000241400a8845500b14104043d0080c01d66000722a025080b02005a0800019401d60f02041d841805641c40c20f08260311100c102d0f0a481144e4280c035400000450500b401150300803440c0f000b04200f80052203110703e8040c0d40421000c0f00e5480d0303032150350302100203421460103000143305280e00040400800b1001290003034501c0707030303400700b6100c0c800009103024000c1801e806180c03d5564580080c09030034680d03501c554040700000c2020820120038440c2d410982c43d040c01070b1001d14464011402c45604003040c03041500841e007010402c09004100d80808215240840c2003501c15a00d00071000241005c0440d014142c0b440c0c00030702d683d20000e41c01c001075a001c11542e054074441c0482c4401103101c80410100c000080c1c9414005400c81a110403d1648540c42207294102502e0800d0503c1403640301c00d603403544101d170b03014081a00060024004000c1e0115040c80000d1000503504080201c1c000c80d50b03a000c0c213616581800350000c040399402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 347583264 1250 347582014 347582047
    0x10060c02012105100801140c13030c08030a03050606070c05060903010b0913020925030506011e0f09060906050405040209180c04150e030d0818070b040f09060b040b 72
    0x78406151540034489400303010b000510045803d880030000303581001c1142c01c01070141008150421034030303103101e0300e0b0900000c1d81c2d58041e04007804004c151490000000e0320b66071702d440050040c030002e0368a03041c48600c0036007039400c02410944208010409280082c041208800c182c2c1e8050f11140c2d02d030b14407203022030700402c0d8003541264808030241c10009990f850900d05182c0302e1003075070360130320303a4940c0c602c017915400018120041200380d1200501c807440c483e50041e0713400403051500c007021a010485007401c0700340c982c0014001480355030440710003903000780c803060007040149081c000107441c4c014024140c2c091400307510300c52500002c1d441802d98503206005000645110248140d0800401d4945079038080c1c4115480700d443d8201c0072041e28001c4d8001ea0385408041c014102074580000e0465030300e10000e002c050711210075000e011a16604000c4a406401903158240d40d440c1440c000882c0351344140d10030103005042c072409000c40f4001100740d404449003000b11980742e1086d0108002c44 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 347584514 1250 347583264 347583287
    0x50307031505030f10061208030a0b0d0b16030c020607141602060a02070602060f040c030b1902040f0315061508071202120703050f01060e0d050f070305060f09010510060c0201 77
    0x610607240c00449040300401d0705c207607406000604100095a6403010711f031020001c440030b8820070040c0b0000300740a03003c1c0c00c88510420003c01e100c0d423169176a0f07140115a20140c1c2c0703c4944203189200b4031b450325013510458600c20503a00042001d40740602000f4950301c0044000f4044074804140054001e400544002e0b281340e006204030340351038810100030755854503889150014811900441d81e008007035118075004a400545000c40c190560315103140102c0090610381004003c05000742c1c90f26554800380018042d43c00456407400d00e0350500a80343c0c0449841c2c51403491608004102c110f04000611380141d07040d0803c42d0065076441d01c2550b00d800c602c03003c040c0540c00052002081d041ea05c01c010701c0b0700c03520f440400468440500c541d00a4001340101e801081c0d259500c0030162820440300ca002503c50011a4450311400300d0460904116900c111741c2e5500c00010302806134000000039a02c4132200c1c00070445450103e1000013091031500ca11818440660410401d40e441803140003403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 347585764 1250 347584514 347584519
    0x603020303041e06030908121302120102091314061917060a0f1a0405150307140907020f06060630010f080d02071e0e0c18010906050307031505 63
    0x721940d548100164045210f003070002c08031010100424510702030b02c1008801500801028140701c6035040240c0c0f0010007811ba1280c040410702d595005981ea0402000e00710100c6002503110880c1000b440740e1a0710541788002001c0c20a0070340608081c18280080d4411ba0407680982c0004c55400342c04000d0140d5041150700720070341110500401000240140038040d0034208100d0a203812180c0300c202d801d2100c4080d584052540e25010501d020f07001603411020354080707041c022082d01c0c002480e01d0700380e511540d00159005001c0440d85000d0600e598014107038006024400c082101040d00c030f03140101003a110f2800421403924250040c991460304000d55440e000d14040d4001d05c1c900380325000d200b049200d0304529000b25201c48080380103192145c258004119043c1441400b07284000c941f0301c001409440000c000800b40e6181c1529030248100d0440b8075a100310f60382e940b5082c07402c10040d01d03041c0100c24400704003299000c1c5c00c03a40d0122542ca40026141c55050502d940324600b94010381e1f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 347587014 1250 347585764 347585767
    0x90c030403031e06050a12080307030c180603050f060a0e1626150406080c040207020d020a03081c020403020603010324061d010e01080a02060c0a05120d0c210b040603020303 76
    0xa4a04009512950076510100c50442c1e51954945214010381d41f6000300404a400070b1003c6282c00b4000d8002141072840d906060a14614044c1c1d2402201030941c0030740002a01d070424018048240c00e21540c000c001503804e100b55908002c4410030040001d04924010460025a5480e0360710610f05814038002001000030362401505001664060548034010814010b2103480b0362490248034100440d042d10024041941d0442c04000094210304000c7e80c100c1c3c9003c1035040140d031054260b0010710310550680e521100080d01990b441e09184840d000800c4c8104414409a602c2c1401c0d241129448555215406440c02400020942c0c00180c2441c1c2d900b00480030072004405206503403a4942090050030683e40c49a41800c581c02c00e100b4141a50007034400d24016041a40c01006081240d6040710302070f00142d0f54480c0f40031103420040000b01e40c003280040d00741040b8010104201420b00d4900c0c40e00d00ca500780c280248400800350018550340d11203140440c0c440b43c00c220000c0d03070000e080c3c2c0d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 347588264 1250 347587014 347587061
    0xf06060e0915040302070521100203010e010f03020a14130903090513021303300c060612110105090f09040b09070602060705040515091c03081302090c03040303 70
    0xd6150341034034011a14000d51581d070140314680300725103200301d405a00030079074246800301380302c0341883c01d40e070503a040030b6400d03421001d18408018903254010711800059803513240c806024206141a00310a504200b0270300c0410260360b8010140040d01d04100382a1104000240024401c41c000700f40410220b081a035840706040d0081b1100b002c480d4142c034034500d85501c1c80551001c920800500045801e4409010300c0815855640d01e8070030503441c846c91000380c125504a00300c505400e0b8450000510400030a0304010550040b031006082071103051070700b400c241c0e4030ba140c07100710b40c1100740c100710b001301d08035140d540d40500309034074420058000207050400e81400c034040d030404c44030000179209540c0b00050385031000602034840e0200384e481e141060f00740703410845482170003d0f040c0507900f03003407000c0b1b5240d60398180300310541141d00000c0d801c01d4542d03150190216100a045241c02c5c03403100c80343c5001d615480f40e00381c4c1c00f5601655181d83ca070f5941c641500200fa082c0c42c4a00c5103158014030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 347589514 1250 347588264 347588279
    0x30d27030c0b0c070b0c07061d010b031005070509011809091515030812040213111909140d05120a090f090c0e120a02030f100b0603160c0f0606 63
    0x30705070031030242402545560707078004102c440d80700b840002403407118104000f50b012894040a007002500c20b6502061a003c9415103240302154065203201c0c036503580111100300d15080002032088902c000342031059240c40000603006028802c09541030180c41c03101002800b10f11356100e4041d180070001045030781454142a0000d0340c1d07080c650710002c0e10b010040e00381a370045514800301d941c4458000d20304005841d40e002d4a0201603c126040700003007400e1442c0d006240210010b02c40140340c0c00b516800c00e4445e1040c0c094001d81640c06101c0c0d4000e061100a08040c3d151101c4e000940ba03480c00c5001510b401031a0042e08038504d0303140440410010070150348503040e0000c071900446c802505507110f81c400400c5620f00307408880814104050036105040c098052011101c2400c00c1c3c80d4011903a0b004a401c180c444180007a0f50b0304101440340702c1c8512072040c40000c1c0819038070203055180c070904004c00780d111751b1140e17428064006440b100f0040365955988216078040000e100e0300399070300d05 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 347590764 1250 347589514 347589527
    0x201020c2d0d0b01051e04330311240c07030201091a0d050402030c0d0b06100206060a051519090e01090b0f09100b0f071a0405030d2703 60
    0xc654800214454142114503080080703040b520740001d0f012003c0d03460a402c106a2140015907801c0000b60440c4c100c82d0383c0d54521620303c07001c110f00d8200040c40d9644289601c0d41e4003050000703110220381107050010940c9010fa000240200740d0780e103442e650100303a4229140d9091280c284003001c0000d80034901d92000708850088910070f80f03485c2c038441d4450b9a4600403491020111508a005001700170b0700096a8002135041800070b0180c68054107140e01040741e1000980c01a00c0c6451114207002c0c440c107000d5408204070f0514400303810395041107400240350300e030980f0419100340a01d08000745d008164100300c0b02c1400841030340e0b003408285002d015061041510a0345181c10022000103040c1d0541c1c05803140e826001407290020810a904202003180050f100450400c0801b1020070890300d8440244070a0b000051001d49401440c6440703c80003c098051040181203c0140000500000181d498101c907020010950302043c0c82d602c0d141d060301900c1960000048002d82040c96080407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 347592014 1250 347590764 347590819
    0x608010b01110303070f030b010509090a090b1308070609050705190515040513240303050705010509150a050a0b0607030f02060f070516050304050a1509052b0201020c 73
    0xb2902014030031582091910307400f00f01c4480c004115400403c100d41d03886a4001d103039000e0141455400c00310030001203680400111405000e20f07075034080360710a0010342c1d03080550107003400d03004000f100903586e44c100b09800303200d4006004640761002c00080003420b2104001401c1d01a01e040425100f140003201e07000e04500c07855010700c408a05801856440d04200c405480001c1c014400e40c1d40042805801489881c694bc404407080a103200380c0c04642107540c00c0154000e9440d00d40b03c6d041414082d08480340504050165800881040806061919030340e90100c0b1b100400500f580c0d450461001600100c0e417515030040001a000c01015046007000086804680c00c580f40750307844a6149402c04410740c1e0440c081a000c0c014080603411008200381c5861080007541e041035038820205000ea0126040310031844c8245a004110b41c0d801840000240000c03284400103000506080401000403080d040c14408644040015a4000c0200c05591074007d811000100e42d4024101d04035503041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 347593264 1250 347592014 347592017
    0x118030605090a140105010f0623040807081e07030201141606020a0219030813050111030a0c021c0903020d02011704141209130e1002120402040605180c0c100608010b01 74
    0xf00313002d0f00e584814460103050740c0020029104650030000142e82c600b070312107018a0315583d51414031000c0400314010380020310081c8000c00c00203050504040c107103000000e06040d011500003400740e40c88000035602040303940a081a100401d00c00350780b0b400610424450150300038034500d80c44100500e41e40100302502d010350990b4400e81002a40907420842000702a00003400700011036010f909a0b0b200e50340380f610504c00020b0340b2100380f4107040340750000c86681010583d280c4458103690307014448004c220034800001070058142d0355010705480001d00019000300394849140f011a400348424014213040a1070600702450540740c001c0c498003508070000500d01603c100162440d11030010740e000c15000402c1c480401040c0030b240c4d401082c110360710100b41d2042c80d0400391402e207a44002e00da0440ba8144021131803400e070060100341c4030700d03a00003070003180c8210a006001d0056028150414400b100c440e90b00c80c401816a4130380402c441071408420714001000605a02c1580100303043d513001e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 347594514 1250 347593264 347593283
    0x3010b070b01050603070c02270103050304090c0f020601061211030411040e0a0f08030a09020a06020325050309010807021e0a05190320031b010b0405010807080307020118030605090a 80
    0x2d4109021359800107488800100d00c10300e85034801491b0655026240d40040c00b1a2600d00b07030451111038900b142a1301c203481030f800008050140e44075a02903081c90704e1240c00d04100300141494001d549480501c101010071041072102111050784d90400f030f0380c460b40402501e44900701410000c4004031004925841280b42451020003a000450448129600003041049000c00c075120310000d6407000300b080504a9840c1003a40c0140d41c0d1481c4074011300407540c011038643c47c1040a400e0401400c0d00e0882c000b140841800b0000f46000080391544d070001c0c0381a02e07a03901d800703400361300d000d15481000d01c1401c0e565150075108040003410305d82c054090000c071004d1004440c581ca80084e00c0b21000350005940c8020041c14441d0000389101d800089011a460603032641140c07000509144e204150594403005e2164051800740070700d5014202e20005020020302e400c480c4c660707034817030b061009050004040f200c40203110b200324001c3c000e5420500c01c1c412450000800794035260001e0b81142c8017100e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 347595764 1250 347594514 347594519
    0x7110120031006030b03101d15071106010e1f0f060f1b020a0510170a06030b280e030c010609092907080a020c0d021c022404050a060203010b070b01 65
    0x80390194000c40c1c00042c001d040311094280210b0090190164690a00d1148c440078020010f01080309032502103c040c10320b4010309143e10000c4c2602044c07000b1002e29400100184030a11075400350b2500b0481c11b038080030340d440d1814200c0042010503403140c0146220380c00c00103045078215144048070352640d551500b85489807044c2c41540301d880c140180d00640c40c080e0901640c1420540c00c203e0345014140480c0749064081c030410190401c86044282c1e586615003041000004d00c29076821060181909661204410f00d0400034030000403140c0a9a8450003203100e590f01c00d2046409160004d80280328141d1620b02c4c03540a0f0013010f0040b200041c11822080342001e070441d400b4140e00800b050f0365141d0700d40031401c031103c480c09440c0c810055400c00c8500a4900100b024084d401e54035006800c241c4003440041000700b000b2042e10f000c0d0b4001d0507400c0d13190550b2040700300003444055200e0515894034100070b49000300c0340d94000c121600c00000425000c204802501c5054481d50b0711401a03078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 347597014 1250 347595764 347595767
    0x6170c0a050103183003061a1b03030c1908041203020d0e070b0c0706080106020705041a04140601021905060609070c14060910020c03190e040903031a06070b07110120031006 76
    0x2181f521400500000520a400303000340000003c055000c2403c07020100080701164107821944142e9074950601c10010b4a402001c2d440d001c44520044075080504040c0380c1910707035a80800003064102d003019800240510400215400b102000c020340c4111103025844624030001940b29241503942131003418000074182d40700310041c5041e2052a809441030a1400c1e0034013016041e65800300d904550140710b80152500e50380310700410207842c1740c0855500e00b0500006030528031581155460401d0016044010407070006902c0c1c0c2201090311912541e580303000e400c454040c83d07660010150303c1c5101a001310010000740c014091101801505c1445d04980c50160480c0311b9180e030203640360414400e000c0031812041c8413842e50702c45810140007a4090034001400c4030070b00344d41203000c259101c00160b051040c180100c0c60f1038400703550003480c1c1441a280e412030402c005000b07204004031404240715420007074110000404002140c181080514507c03001142c0044400100105480c0d400140c8203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 347598264 1250 347597014 347597021
    0x18100507051c151d010e060607031119030509040b0a060c020d051903050409230106120e070b070b06040b060f0d020706020a080411010921030509031006170c0a050103183003 76
    0x100d0004203881d103271940955081c3c4282061f007411511501403e9074440745540e0110b111541c6504c00d507905960368a200c41080f04a07000030345824000c2c1c1c4003403000d00c50a5080408000007540490704810b40100c0d91606c40d1503c07001d103860358030709004525540101500b02c00a002520f001800c140042c04420030f91803a00c0003e042c014407003d48020040000600031490000e070401100c00202e01c20b5000e8298601e001500e034082c140141d000145c500604c00520011a0420b0003264207011540c503980c002003990051100e400d0105c540000c01083c038400399412603806c0350b441602552128801036014005280444e001c0d11128080710a210040d8422940c3c00140c8028810014004101a280307503001c0e04c0581084041c46020031800485a604009100c102d182038440422201d040004488903102103004d01d4020381e00c0568448030640d2640388071000c1d80c1c0203103000159a0840c00f260800c21115141c043d040c0c8004055810707107100f08130880f00800f50408101035515800d500220f048 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 347599514 1250 347598264 347598271
    0x61a120c0f0637120908250f05030702040509010203190c02030403020603012306070c150c0f06090201020105060a0f120c03050618100507051c151d010e 67
    0x46480d81c0203910651038004080d100f540c003d400c10440d8001408540b90540d03e4038848124a400a0200c0508850340141340c0c40700806244001c0c402e50026695810441c000d4044140074501c03204c0c00c0010220103000da032000f05422181d10382080c540b50800e141c4030707800b40308203134090b0342004d001807910f0328140201ca018a14403405804540180c80904000344182c80c800b40860000b0440040540d0700c450146001c1d009030300c080542080d844503811180e200140410380100b40074030440700410890740b0b00b0f600302c8024849507410240c110001700d50b94509000000c10445801d070307410040c0701d0317160b01103680a4800c0e0000c000303940303e08040103088101d81c8645900c1540f115428485c81d07030304100b50b460091040f25001d9a8a440f99243ea0070400100d032000020300146015000c0c41c00108400c046240c41e000040245040a190060280c412404c0c5e26541806404201214165980c48600b50280700441c181c44251140d2180509940c0c20a81c050140010000800d104400b80c040760302 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 347600764 1250 347599514 347599519
    0x2060606030103020f04090503091e0406050f0307060f020a0f080a0801090605031f0e0604050a1e03080f130606290315100c020409150c0e060d1107061a120c 69
    0x800e0703040000700805400b403141c2c2100c5a00003400902c04038bc44407401035454140041c1282d00560224044c00102c50031548880c1c0b040342d0790351040c4000c1c0c8001c07802000f920440e01c5d00a0301050010401ea16100e01c5020041c02540c01e07000400901030314001620904086584203803503643d0b6541c039403003034554034020581d15030080e003a94401140e2101c114455159048401310b0858030103148203081c40070480781660f443e044041900304004264001d409540d010960241e80707507003246c5004052007401000d03032071101003150103e08042c8a03000039603244d641c03000d0280300c13090b21102a15041243c4a0704201c050800c140c1481800b08100e054901c1801c0c1c020049040170155001c100b034007143c101d403040070b202e2100104005a1030318050a03500d1070007805484011070b001e0585000300c0b03100c504030f03d0410200c2e020008017a650141100c6448405800c013155291024600701d83c284500300c0018031052030300107201540f00840502c5050b001c001c658604610b02070000b4aa114100120450b5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 347602014 1250 347600764 347600779
    0x201c05190f0603020a080115230d0201111605010f1d0d0c090f060e161409121009060b0303070804051507080a11010e070f09020304030e090106050a0206060603010302 73
    0x403059415500c90018403556540c0401c4241e0fa070340100300038021503001400c4030b9441700d003149690902c4a036144000d292604400081031710851003109156024101c0728841e501c10500c2106580c8a00304c2e8003001c06c803441c1038030802080100180060315071440b074240858030100c800640140581d0206901c400c1c04056a84a00002020440c0340107032000c0413a0f07104103024000c14540c803207101d0b105001d01d92038030000f40641080030a54111000030500900c828070b0f40900302c0c0046d03002580d84d0000d008400e0b1251034040c0e150014071127030b8240095007264454040d440d080035190350401e621650041100b0480084498241502c2e071107843ca001c3d110f50800c12003003016003002141c1e050b4461181d500e030f900340700143da954006a070112203c0300c000b503072038404902c0c0c00d41c00384038010107010202e0080c60700c0b034540203c410703200d00e83d4420401060340c04800602494050207140840302001805580a0743e144e890152141d040141801e0042c41179070001022814410102c0c0c0c141ca4000f030109 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 347603264 1250 347602014 347602051
    0x5010605010212190504030f05010204090f020c190303020f070506040c0b0c06070804030e04050a0207030e030d1202090f030f0304060f020303240a1806090b030601141201201c05 78
    0x554060713000c1c2c040c080c01c100003084000042031000b4800c418540c801c10003d66205d2816101070165080c40030f020b017065204114150811000043c0c03585511501089000c02c00094201540240110710721101d40e803000240c01030801c070340456110b2090740b00d44c184c2e050f1951034855210260107901d401102c16401000803d850741d000d05035140c0d015100c0d01c1d00d02002105000801c0a0307441c04d8413031288854022a100c0101504001c007151207000642c028518002804001040b0303150425a0303025136a800141100141c4800b83d001c420584040d08854810302c00340030341030303a9901511403c1c0c0020b01075030301d26032114404004c0b240551100c0001d5003c600819003007409000304401042d0b808120048002203160750640d641c850001c2407080001ea9614001558054a40c5541c0c298881d4200300d0041c032500c0401c4803c8101d050081e40c4c0c503441c3e01516894030b80100709100c04014900048160982c01e1a030070802800e0f5003510a0f00f9403240d040141e110702c10f84805440003005c102039030180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 347604514 1250 347603264 347603287
    0x20304030b090718050702010518060a090606090c0c0210020c010c080d020d0c09050a060314070513030b010905060f010309020d031404050405040606092316120f0905010605010212 79
    0x6050300500d016007034034005030ba01c1010550000c600c07075400c11400d03158006c0100240c2c082c40350300c1e440040d866400e000018002501c41d101c0f07900400c0050580d5440c101c1e0801d005840d8010f40251100f40c400304690140030f4000341202d0b0030100e08070300c114080e22402c60164400b02e42c0c01929001070310f400000072880d030b0b0b5600d0b59030421802c0c0003000d5403d00094002202c5030080c80d901454039190b4400640c00c086c00d004d5202c040d900300e0702c141802c000d1000e0f232441c044000c15511003000d01e4210785441c0400340e4404181030990001e000300854000102c0c2e01c4103c0d922460141c282190035487c0e44c0071460040d4169107040c140654007181101e070b0600864050140d00c0302d450750300084907140a4a40f00040d04680040e102a69182d0b1764810034030001c2040d1160042c107a06002911285c00301c0140b19001050004201c00740d0008903001140c0218007444801d0034038140e0740d07403d220089280d03101c80004c25005105840542c00c1c42c01c000340f25400420040c4c16440c0c01c0c0001032514164142 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 347605764 1250 347604514 347604533
    0x30b04020618040218091b0f0d0207020a090527060601080a0b2101050a0209031209010e06070b04120e0f010302090d0b100303080f1608041104060b07020a080d02030403 74
    0x8141c01d4111515280e042c1c0d03651903100074070802d102c1c3c000412440044100303011400c2c4005080700310300b40840030b20500e142c2d10241500c0300b40b5055115030f030745c0711841140d41e0040d0091010094101c120b043e0b01280b82c420a4100324495004805078132504924039041110000e000c0840d00c0c0c5d035401483c080f4503554410004540d10005001c008a0610035032804200c07a407950200b01880031100200803a5995001c5c003a468000856100960900c82e1090001e82c8070038001004500a90300090307520066405507081d6200e4420003424292200d01d1750070104400f400885048440c8814802030618903401a4015100341101500c071446002d03050005500961140c541a58813500d0b19090030001a0911400f038820039000104c904028a9403901400500c4040c00320031198600c1d40030016440602031841102c0c00c400e140a85158689050414005d4111040c15411504180b0003080920a1710001c1ca015842564910340060b0788141c103907110b002c0c1017001001600704000410102d402c145 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 347607014 1250 347605764 347605777
    0x903050a050d110d091b050102060105061b07090e0f060c040b2512080901050f04060f0b0409120e030102040b0d0902150c1b090610080901060b0c01020301050316030b040206 76
    0x210b00148044401c0c54a4140342c00504c20603030400d4580c44a082000480b070720340c00f41c0c0c0d400004140800c604080001c1c2d1502d45c1400780c1c0340548000f103180b454008041120900c03c0480d40c0a1380d12660301c0303a030b403940502240e1500b2001072040940e5a808188001205031140d03200d0f526143c00c09080c000620352560140c8504001d0480b01021303145c0c040400b099003006d451184800c0401265070001c050280340000705510f1507a4901410060070200310394486521642c445c04c0055014481e12100004240a01d52107402c01d01e000c050904000f8100001014103440351509105845980105400d130311860103450a0084240007000c1a0034450f00b140740407a00c010040f207035640400f85060a1038019600500403944550102b50342050701701c1340c0c003441903416500512030389050b90106040e4031a00d6540300402c0020f072b0000b2040082948003a02500c420f1481035600c00e00f402140e40070b50820300889109000b12412440e0305040a00800100c03944003604c2042541c40d0f40800c41140c1104c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 347608264 1250 347607014 347607037
    0x160f0c050f030a0809071818050a15110901020a080726030103110d0206030412023306030a0c0303030c0909050f0f16050909040206040504020417100903050a05 70
    0x16201500180050090084100c141402181c498010100050003244080d04445454001020911400900c40900b0140d081c8040e40420001d08080900c0c0c3d00c60b00944024107140101b8048000f000064044084200101e10080c80083c1c0010407000711440345481d0580940d20200400f0700103503802000c2c122542c014020303a010240b0026000c00d1000c0b50440c400c404e12030000050081001002400380482801d69025241c50901c2d0b02040182c800640054110a80310070900191407082104e00303088125040c2685c000c51824914120314403001c1440240703000400000b804500300000e14242c01900b0150246c403007841e50b1015001042040030034010000c2e82c110100d801001401614010140c61071840e0103441c00c202138518048001d0400422a0b204400800000d0381c000c0c1074a200c40b20451b500d4050f41c86510024400b4400d0b070303010030342050021500103110407000d80000e401c5940403040d2000e40c40001c0b000ba0403580c4060009010a40c240001c0008501c41c002801e65000d40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 347609514 1250 347608264 347608277
    0xc09100312020703060f02270307030c080312012120060301062d1e020109050a060903090b0c0a060203070e0d0b0a270b13080a180b03160f 61
    0x99032a00d03040407070300e41c40000140c0e00100040082000314454048800e014890440c00c01140142d500786132120000c00180c4c1140041034400c0c690380c1441040002c541c80b0380c0001c2030a070781e603010503100d410840007049903000c6c04000150061191044000174440b880807000350718155030b60708100e40000e489110000821104154541d1660740085000e4002030700d4226402c200c9480707188070340c0700c01c0203240d001c1d40340341c0ba2021400d600085a5500713241d1803104664143c4201904a004000d80c403c09000d40c803400e41c40000b40f20b41c96100d02101b50190740d4081d062501e843d032040b164480c841030030802e90302040900010580b50350203560020032500c0d006124003422400a020300858079003e4981e850b241051144d00044d502c200103002d034000c2000300000140407810f8100c908a8034000d03080641103000038000d5008480c1803800258481085d9444590540e401005450802104484801c0741200890003030741c08015284070304543c00d0107005080005004a0f990f003042246601449035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 347610764 1250 347609514 347609519
    0xc01030c0c051b1e0a2603030a0b09010501020d05070602070611030702100f060506120408070b0f0f0a05060f1e03100f0f1116080d020c031215030c0910 67
    0x2061041d014001c00002c0c0701200783c6000001c22508601c0d200000f100040d41030364440070f039100c12a00c40c04a4440c41d0300080045038807402071014060410001c1040d000c00800c0210581302a440003800007070941d00078045a880e100166503030704011070702e103020990a000b400b0002e43c02d40c0003083c040b485400080b621185031403404025401c180c41c000056004881c1000100c11544540240120007604c140030462500c80071400754410701600410311010351000400340b12241e2708841c11140d000e95641100d141c20742c150b0b0754555050f901d900c2034485143c0401e102c5242c40c05020301402e0010401e103400404c840401460306918012a141142c9540e2466080e990502c820f40142c600c01c0d0011030110017425907401110a09110380301842e2400e41c81d110b0340c0381d054003503070200281a80c00c4c1002419074141baa5160140c0300308144000d00003d20707107201c40350100140001d50028a444581d688450030014403801039042420341580c000030390211a40303802c5140b15000005904c41c2c801403034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 347612014 1250 347610764 347610773
    0xe011d0609150d140c040b0f0a0b030c040816090b0109030305040e04020f0405150102060609101716030812060f03030901030c0c080301030b040b18060609090c0405040510060f03050c01030c0c 84
    0x81e4400440d21141c100f0001c3c001c440c06d081c000e85a034004100c0302c003800c41d01a2400282940481e0207080c071520b201000103000082d503801240d001e010380030200d40c0c0c160381900c040b050846d21400b5403020700741001380d204103e50290801078150707a030580700c080c206400d2003075030829000c00034810303644110f20710368011050b142d5100b881c0c0146903a0428000c0f0a0f5518000b91504d5000f4201c036015007036202c00c12502c61125841801a1885900c50110514100c1d88080c904610b0070380c11708010b441c2510001c1048034490007030130a21611045080d1070b07500c040030041d002d80041c00c3c45825400c20401c1c0103056219178407090245046081c1140641820348034032003550000d030021a64140750b54244001d002c2d956114540c0b01c071700301e140264000c00c9044040d40b81c0d14007401040c0540c00e0b90000c54a41d1805020301c00400300007400803c518901030602680d200b08135940465024070f00740002c00c0b105142690142960340200051a41e0112200114000c00d284000d01e0200240741e1910070014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 347613264 1250 347612014 347612033
    0x150909070809070e01030809040b031f0501091404020f1525171c0c1b03030b0f0613051908030a03060e0a0501081903020f070e011d0609150d 62
    0x444140c0c1d11801c0354a840d2030030b40d00d4030505800602e25902c40400400000310300c51708440c0124015103012588001540c0403900c0c1407503401801103940707010002012400c400380c0c0900d0413a440c001c806e02c0001c640c401c0c0c48400e08029900a500205c80841050550030300c0e00102d41714a000d4504d892400c00c10791011462070103c540310800350320700348410f90140903103c0404101c0c020114403c52420080c1030b20313680da210365803e41c000c400707855600d003010045c003503001c03c1c0160f4964507180c42ca0f000107240c0140107100c00180f10f449081c100220180d00d043c07107000d035000d20300000d45a00c1340c0340c10441080121484a82c1c260344009442c800400c1b00f0780144040c1c251041c0c02c0c1c402180c41c5050041d004d00d074540c01001d803204285420010464040c000509950091104d003040b01c0f030004501741241070150f56541304586200e501c200255030505040355504980010302d41800106401d09040c112540643d189580580d8010100f6206840c40c410301001d550000c15a000c980596036501102 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 347614514 1250 347613264 347613271
    0x50903130f03050c060909130c05061b0609030405062a070803032a0f0a0e030327150a11160e071101090201021e01090614061002030414150909 63
    0x100c8210703850400811008010ba111484022241c081c00c1c80740c0403020599403040201100400e084002810342401070a204a00c0509005000c8595a4085003c1082c50b500900c1161841e88110000651051008401d441c00c1c1c0d00c00030015480c01c0070b4040f84004050380700c09c00e40d104100314600e4620a0008102180040c070308000556121b1030011000100c2402c003448000c01000700100f41c0004d026a0802c45c0c04142070700321015112111403000710b5584098190184e0140310014080c4072003000c0707144241201002d003800341100c000c80003d0248904a0314904000c5800601c064400d9500580410140e500078104032660030420001044616046900040308403d02000b84900503600c881d034042c040503000000d21511481e9070001f55614100356864904949405804800d60401c0d0130211a09070000018403940349207142100300c000703042e2000c510801442c204462100c2c004411348044070402070040514042d210f0610140c64032482a00420790001c0228040301d5417607080c803900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 347615764 1250 347614514 347614529
    0x20a0e04060c0816020d08040f020a0b0408011a060702010c020123090a06020115061808060114091608060904020d0b18250b160f05010c180302010c0605090313 70
    0x140042c5a000141c00c820380075000419002140003071340800c1d500000c100c485083d45240010080e512424603806000003580e000b0340c808009940060185c2413100600b003a107038581e000704a00840700c0348088540f5030144000790058001d0100c4000741d03014009800300c050040c1403090a035a4642000c0c0e4514419256100764450007040c10384081c20028400d4000d4009070008000254020303c0210302c1a8440c401c0400f0400a9841d40124840b06500300b8028003015007200e215586404004440e0a00c0305009130042c0b40060008861071170600d0038072060426911b80b01065280c503401c0c0a03055130001c0050740c2046c00080d0030b0b40059041c4e4000b42c400c00c20f203122201201d6900702c5450800d0128104040701c101001f0129080c41c640701441402c6500540360740d641c0e084103204206100c0008003024004109042c2c603282400010b401182c0d061100c1d13038030381d080c44103181040400c8040340e00020b800690801d441030009061030784003942000805c0112410884078407085000641e00341c001c800d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 347617014 1250 347615764 347615771
    0xc0916120c0309051626030d0b0307081006080c090103080409111207031e200c01060503010203092103070c0311011401120212010c05030412030b102109031407020a0e0406 75
    0x200c0c06141600e5200c0d2201c06d244035090440c1d500c8899503d0151040c0c0c240d01030350704d091a070481d076410841744c00203013004400c0c4c2d4030b180b0f0054402802403181c0c0c0300c0d521050140c0c03124143c141c6803a04240381a00c2e4481d4840b4105410080640c00518035501c0c0c00145e82410000e040c07a217980da426862095001e030f43c0100351000c00307141a0341580e010345254151142000d00e64204130fa2900e424201002816800f682c444200d40816405401c4940c40140c2651001040c00010100407400d00c0c2403141903013512440307420103914444948800ca8464000400203000000080e1050011159060418001142000e0001268603009a00fa440700701040c1c0f642140c0382c110b013403904400001da21150000c0014403401c90000d041440000d000a001d4003a00703202c0c0d0030070b50080d4400a80203002802040d411405001c1c0a498802c1c00c0c0003190510300c1900590060124600481c1c00190b415074610f000301c06100f8030701c21543c0244500700d921800782c101c0850540203000070a44582d00649010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 347618264 1250 347617014 347617019
    0x7080406020d020f030313080d05072705220912021c0509030703020105031015050703110619022a0604060b01080f0601200a03020c0916120c03090516 66
    0x1a01d89444601250203640001302004541c00d004815290301c070039025038003c015030395840c4c44c0d946803080850b204881440c0005201c0760130303445003001c2d040e03070082c0508208042000c003130421a030442d0711134580e1046088656101070441045901d040e2a901e034008154044c0942d14800f8120030102841d0040c0d10480081604488100c14078041d010305080c45440d0124000c0441e40755085400040c0c1444000004101450360000f03009001b0304007030000c0303501580414802400c4d903100c2e890980000d21982c00601030408041015401080907407000201c40b03403465020310103900042050f01c419100103001000c94051140441880c41c0032030040c00e42450700e40360007c126844244d2082c100600c61003080061405680500e0b04007200b401c00e140030442000440d03920030044141c4240740e005144440d001c054001855a6603950110f901007403990710034520300140010040610001240d00640d1070b10804035602480c04218185000f044c08415500e03591301d000c100d100c42d6404050010f01c00c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 347619514 1250 347618264 347618267
    0xf0301020a1706060c100903050f0c06060a0501051206011d030f0102041d0609130816110a1a04120c03050712060b041a1c0209090a0506150a030b09010204030807080406 74
    0x40a510a80c1141c4d49400d00007012100c650300c3d0407014503160041c2d0349101a01c00d040c0a101554a00d880141c0300b0359032a00200d641035110b80060b1031850048041070400715440d8000d200742c0e510301868500c0c600c100d6444000440d5090081402440100c1084c0904c480d540c4003400601000002c042c0090307904d07442d010040610410404480200750030041c1030040e143e4610b28115000b03814850002035002c071742d0400b079180c0c0c800c014100c4402840203881200304a80d00692511110044a2500c031241c2d2b180c0ca801861844045030900b803010411080c089007a10110b180d2205008a512402d000d449654241c50409140c001c001c040c03140340300400c10001e1a01841180314000d6130140542c0724900d02c400c40a88004c900584140342e20180140140864000400429002004c900d1581051503c40707441d02000101a1058041e810005100a0000040461803034028110781541443e41c6c45003070340100c01400032449950200300002c003281c7c1d1100988451801032803a2399580746000c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 347620764 1250 347619514 347619557
    0x1b210905030307030804020907120911101805100c0b0903190c0309030213020d090803180601120b19060602010606080a05060904060f02071e0302070608040512090f0301020a 76
    0x3029219074401c110310710010703a20204840e001740d0305a409001c40d448007601a15003a1901d0000c4003450b2400d516682408100840081c50100a6800400c448a42041111410115000280001a404010031690500b1004101e060200f840d201c3d000c038148c0c3d9681d5440f588180c512900c00d1b0310104242101110802243c104404141045102c040b02c554010b084d5440ca484080c0c899140311840c0001031000d034044900c0d0710442c1208001204c0d6034940400c16030003d0700e4280040f00c080b000441800c4001400314144c4000690034a05681d056540b0641c400e00188281009201e060044042c1c42450068202a010035000414031030309010380100b107601c0081c604c0c240035083c0b0040c00000c0d100c42452613001600201e0204d9a03154200f40340001e0710940c10001c0100d20925030301c0700b6401140303a02e0721220380710b41d0a80310b6165941b642201c1350300c001c2d10080c0082c0c205440351000c00b1801d800601401070b02400f04455045034a0000382240c020407186004540d51408042d0048480d06 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 347622014 1250 347620764 347620769
    0x1b021e06390601060302130e040c060e1e0409031115010306050703110306040f1e1e020a1707020c10020f060c030c070204020d0207020d0f030e0108040b071b2109 71
    0x14007880591441410355642c602e011303c18901459030000e880d9100509a00784440500724180b16594141450714004955200c10302c44c00c000502c03504038241c01031410788031552600712250320034504160702c02c3c104401004010011014461000740f004180271081c011400c40a60315189000d45605d50f042403400d403080100320004061502d07100b07084c00303081c9200392a0010803d40d000200d00109941c190018002c0000c0c0701c01900c1c00c071044100b228803d41000e04543c12080e11000580c115010f40d1081c0d001e0310305031030042400c4901000403c5110b00855511200340d104580c409090031002c5940c40324031142290050b048440d2200c908101081030300d401c9606080401d28614080d0a0700c2024001d0a83c000c1c4155000240300420038801c3e01960b000980040040501d12440c1c034222400f035141c80c400310301040403454034200c179600a81203107215a420225000c05651418421600c111282d1030108a010240c4103140200d00e000051903c04918602022004540d40380080d01c12203007036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 347623264 1250 347622014 347622097
    0x4081f020c2d01090c0605211501020f0c010504030206070804050607080304050f0c0310020706021b1e19060c0c05010e010c1107031208190c0309030f1b021e06 70
    0x902200c000360260540a081b0f814034600241c8500c420049010340841a607041c00e2500c0d2404288807075102c0500070a4100310090302281d8851070800c40e07807a242c0441c9500e580c0450800e0008001500300100103003c1184a821424580b0f5111000110290052202a654800080104010000d08002e00010400048002c10b240110100000d0382c800d020b61041709a00d4000c2420010000d030781e0161010810194444488540303442c8205a943c4001c0c05201c1c0d071180c00b81030302180b000c2c01003a000c203500c03508046942c42c440b06444072809841194454001c000e030400814000c26028844c074060381c4c007250004505c8070f03070488004000c010700d03496503000c54220300d2082000440035103840d0000d9a20b820400300303d40d030b00c0c8d002e03484440d107001100c5180303401c0201c905216540b507070010601920940f210030112100e548110b50400d0310542e1015014103a82013003000d858619052400781054002d08180c401d45000883e42e113400014202c824480c0490f0440c0081840100c000c0c2d009011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 347624514 1250 347623264 347623271
    0x30801090b04140a0e0a1a0702070e1510050d140103060608030a0503190e0f07240c0b04020a0b070609050105060922030c20030f0304081f020c2d01 65
    0xb440a820042014042883c195545c182540407100d061206010281c2c008050400e8211380d81c0194070421000ca8403030005001d04440030030005550a0701502074010a071020400307140044c14000c4a460700041141488000c0c0201100c1030030354017805412011680e6080f0065142d86072010a5030300c0c640140003590000d108004040f81d201c0c0660f070b07200d02c00c211404400150040f14000411447c030b102c000707a004250103000c1c0010005640710482c1c089103c804058181e01202c20700d12084014030100140301c80c20110003080288a0b0b09400074001008488500d83d100c0c410021507100c55001c440c0b20ba1901700c10000c1c041c081c49141e52004080d9a004054501034421900c031040c2e000c4001142980ea03008101454482c01c29000055448190400030000344411660140d42e105001446849425036800000c1c40c04000da0341144c030244001d200366a070322202c00c03008290200002c0f618503400d02c0b100402007010003400300f0100c00441c0c5029200c0e0301c150b01c0790400485c0310506050388e04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 347625764 1250 347624514 347624531
    0x212030705391f0b150406020a0b070c241d010605091b0915070b0a0f0b010c0804060e0105162f031507020c0d0506070e150301090203061804030801090b04 68
    0x43c5400312581c0c1229500e8001401e00441000480d6008181c0191583c082c01041c04070729241c0005500c2e0045024001c46c0100e0350360214102c40380311a110000b84000500168000860307040e5000f28034180050382c0c00b10f078141c000c2c40950240c1c0303404c4021400b942c0d101c05081169040c04512580c10210302d05c41e00801d1200d040c01914580314140340980114040c2c0b15241080e5031600644021307aa020411305460306160613200090b082d020001900945008424503a0b9070007000c851171059071082c0120704061a241e010fa401d6419a0201070501104022420225203070090a2051a02c660900c90003042c00701140301c88101601c6007480c0d648948000351000e580c1c00900060320200404800304980d607180e0080381882c0050076201c1d0041c6400010a0400c0004540c0318070500682d5128840c0001d07500810003ca41020114030103c0820001400010860b400450744404c003d0184010700d06401e00e80d25940704101c90980c002004d070001400f5600150003880880305e01181d0521289a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 347627014 1250 347625764 347625793
    0xc01050c0d150e012105070e0114011e2a060f0b030d05040905040218090105010302010206070216170a083105131e11120c0a021203070539 61
    0x403041c010203004c0c2d0245514200d4000c0f19100e01040c0507400b2054070001f6964000880415000f8080c6034918070010584000720b501c58086580d0070002c1c80580c8000d002041000e4424141400501134013440d2031001e6a09880e040c080b14010520580000a01c850f0401b041801c80e003000e42c0385d911941041c2c03111820a980441a2030940e01130301c0c0d00040d0b684980c80000c00c003000750003001e00f0110000342004010a8198040c0d41240c1c001c2e0250351841d541c204049840c0c01d143e6036140179200102c1001d0100c7c1c00c80f001417040034000c42d002c0322412440743d142c0c00c49039007003400c0c4440c8902c4034015005058124500065a15001407043c0301c2e46402c210000341c0740c3d910710103101802582c0e10000410204c0c150044a040311100c0c80c00c1003620b01210788200e05a211315444408420510081031040d02000304a640c0d10f60350b44c3c00b600c2a40500c1c01000e0380b603400500350504201d801d100d0744410003155042c8180c685a985441c4512140703180600041203000d01103100d0f0354002d02000c03410320 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 347628264 1250 347627014 347627039
    0xa05070614040902030a180f020a06080c0d0e0a0503071b06080103021e030106030204020f0d1a060a0f0e0a061716020c0d0204021909030201090905041101030207080c01050c0d15 78
    0x26046803d000d610b030340d1941620401061110000019152003803400810321182054071030815000356a48140d158503040141c803020021b0b80e111507200da0401c100754041820313a101000918140090740c40703294654071240d00d035800140d015502c4c00c00ca04819626110b060700402c006281c5030409968562440d00005c500410314410780301d03203500585100d0700c283e40a40c8820051a8020300454072000010744809440c2c00c0f941d80e03240920318088051426054440c0e84007504400100218501450003e0480724410400020424001481c0c0c401c1481da0758160104081c0042c3e03511090030800c660100e01580c14050401e4440d803074503a9144d6401c2d40c0c00700d903d9045020903502030f0070380c0c042e62000c6070007441032021070420000c0f002002c034820741e8445011000c45e4000da8030141040c2d100e030181390071600140c0b0b0003820340010700001403003540a50054880c0c00d0160103160f042c590135150312425150111401002000b00250201100f14103104201000b00508004020740e0308012214600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 347629514 1250 347628264 347628269
    0x20309040902030c090a0c030b03010e0a03050f040306020f070c0b0a021e12030a050105030f0d0e09060a122a061403180f0f0d03020306060a0c05120a020a0507061404 73
    0x8585070004002551001c0140703c0005101800808080c5040c02e6403600a100381520500028100b200c0c1005d00c1c6814014480441580382c003511426000355000e850310362208000c0d6114160a12000010400b01d20107094850410114103a0700e01c01843d22040b1489140c1100d000d6400a0016840726980010440c0c0040c61040c100c012008140103041c1c64440d00c20380381c195804000003000041c180700d070003450407158194211400170029012658441032100d0800700001c21020740d0781e405292140240350014000340c20440d000b6100c04844a07501c5500e98161040100344580d51890114003442c50084050111080d0b40f0b1420588e0080c02540408486520584040089030500c0040749014031001d90103800c40d48041c2d200c0b0200b0342c03298210000c07540d8600560080440c50343c002c2c0204d070300ca42001001d20b40740203981001a2440d4504d0301c000d446503c140303070301d00c0101c4610000800012a02d500100b200000c1d0707140140c42c00ea810b8100c0410401d500fa02031a0200540041d1020f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 347630764 1250 347629514 347629519
    0x6090b0904050a020903011811090f07030f021303111003020313020108090c062209050709060305070e04020406031401050d0308010b0309010207021c0b100f091505040c05030907080d020309 83
    0x8003510f5001d00e0101900441c901c02d035143d4a440400c0f19115040450401c480d8803400f003103000c54140008111511808030b0342c1031000310710720000a22444c400e60050103e01d503034800060508411f49004480104203400440d2505085811810317145488200210351190500e401e500e5807904a42c411081801c2c0d01c8000c1c18495401d011486000e801d20800d0403460003d00103544401034000703400c414000c1100d80401c2c000308444c0119844803203006051040d90141c848000c200d103005022401420002c4c0340e0820400b014801012540d0b0f14001000246403968022402a480007440008100107a00032485031f415200090006a00902d10328111440d11010b65182e030344410f51280640b00b00f1100a501c0301e040c11029141c0b4182c648031070051030045030744da42a03a079a1024180e108040d80100041c040ca0307079108126401d030941007201440c0c1e5604076121004e1355800402c084d6203c001c060f0012400101c1048240c0208100074002480a50003c040c84004e0050203501ca105541c03900b030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 347632014 1250 347630764 347630771
    0x602011503051c021e010b1809061303180b13240c03090e04080301090b03010203090606060a020102040e1009111201180b21070807030503040509070306120c060906090b0904 76
    0x104d00900804080040c039001100c0100e003160300300390080190181c050f00c180b00e400e04c1e90600d00d980409851248030008021b05c941e86512003050407030010148101d04202820340c04105038040144403100402031080c41d2501d48100d4010110b6070461600301c6801c0200040c2c808000d114244403d41014000d41000b100502140c10110340300303401070700104642c00d0302d43e05100406c05030200071812901c520702c0400400d00c40354105400d0340f1080c0c5d8003d0b180d03402000441c040d46003103002415911500e000040c41c050382d07244108800c0c20101c40c0f486503c02080020480b0800034002c1c0380303e00c94441c041c240b80c0a00d1448081da20401030159094000340c0d60051810301c03203076034424000043c00824400c601d14041a0700840703000e85c1030346103185004454000600c1e40c000a4110240d0781e014000d5400d02c1e090806203c14454024041c03c10140c403410b00044c0301401c40710815185024540200041c3d0134610301230800d02c402e82c0074504224540c0310811031150a2019100c3d50502104d011 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 347633264 1250 347632014 347632063
    0x804030b070e100207030b1308090f010e0d0b180304060f18050d06240f0509060d0b0103120f020c060f070204090510090b0109020307050909101e060201150305 70
    0x4580403441c00ba0315030307004102040302509040c0c0001c0c89a084034030030400d4041c0c075030340c400846040c04920140200265801d001280c0140f40460440308102070603d407020b0441d4104001911001c00a9401e5885980800601120000921710030320f8100c1c4640085240030300e0150000d00019107a4107010411980c080403501d071404040d160801490000c090200c01d036110305240004181900140b0340a08098074084c00d00310401d404002111907044648a21510740f0050000d0300304000c1416074020140c404440008104080f418060340c05086008401c0c030b0108000382c190191040d0780303015580300304524419561500100d461203081c140c600c0e600e882a80c4045000740804000c02072050103035607a01d404602d010340c400c0c07580f64001d2440003460b9030794100c150101d200545502c00001c0c1c0420004806050001170030307802001d800002c0049586e20a01d0300d84075190000c8030031007c0c08426003000708690900a6685044640141110262969075001c1c2e42e01c0308400d480b201c46590310001c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 347634514 1250 347633264 347633267
    0xd023c0d2a03060219080601031b0e04090f050106030210030213030f060e100c0906080f010b0c1513030905031b1306080303101d13080304060f1e0b06070804030b07 72
    0x506000b942d10070f100b95250710124904080c05541c2544050010342c0f0340001942542c442c1c0541190000c14a0b4034203941c02c0c507400d049480912045446420035254411000064524080039400c14020340000401c1030a620410007001c038900001c508050050000702e1b060700004001000f1aa030007080004860b815280483c041c0a4003516100c2601401c0c0c07a40f60300c5482c50300488036801069690803141c5848440a507219803003035401c580c46200120041c0407905e4000020200804104101d80c910400d800c1500c114010449826500600751403480d0b040681040c00034000d010700b2000f41000000201c074403410460a000e41a12a00b100c2d010480080b441d030b4007100140c085101501d9803480c00c0702c60600000b811744104040f500150281c500741000c0722920500998a80101030700d0030f07240d0f46030703c03070f11340c00180069076102d90300c0800c114a10103d2085102110145132001d010070030b40c0680b602120070811103c4c1c0255420000440000c809404440070341398081c0d01500f094440700340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 347635764 1250 347634514 347634593
    0x150302031b0304030e150c060f060a08071e090209130c0315060c05070803030702072318040b0709051309380903040506090d023c0d 58
    0x70a101d114400105000625600583c6900d00c1e50b01502c0f041002078031442c0700c0001c5e128481c854042030304400003045000709158002031700a01d000f000625040d440d5400355003490b070140c5c00000d9907601070403500100c8401d84020001048409400c5040480e21400724240c11801e12107101080c2d69052a079500034065802440c0031100c140174101e2240e11008090704a032040c0d03034152110310a400c00090140b030700100b01c0b03105003039503805002030078601046540b074885100b0071860310034070085440e101a01c4510101c0d0b0040c1d80c4040b0001a0b04160910894081001d0290010071802c039009008c19258000045d22900107030720000380c00c030102d0805d1003880b000b4188102015005070110b00c014160901003130003445100300c550b245900e031071120390f65a115034030800350070140074407020460b0318291030f981408500180c401c0341007000c55134003150a40e0728003545013454050058500c0144411a40848442c2010b60b00c000c24089070762111017004180701000d6100980300c8256403000d000404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 347637014 1250 347635764 347635801
    0x1030e01050a09050f010b0a12150f05070318050d0c0f02210d0e18090c2107060c150e03040308130e0730090c030803010503010c080115030203 63
    0x140204002d0034107803003000250801e503c2c15160703403007500b111401080c01841401c00c000030080c4100c040c03d04d01041c1c20107042e5220000d9541082d80a4404040905401000c0300132450302c400207801c1ca0724100c050210740b15222000c0d041d80c0c00718039000001e18000384c00ca22810039070a04d01610589803519010400e101d0784029080441c03198002003041c400090b80c2c084008440c02e96a0400003e50102e40d0000c0554040354403030528000541840c030b03c3c55400d030300890120300b592420200c61002c111a00c6481d4060850130140800d01242c420041c0503a00c0500000c2c5481d19040300c094030340c240080390000440a03a1031780c582c440d01c80c1400420848008550100c031158480305c8022139040300a555203c0c1d103210b650100009000940b08049044e03110001030741c440c6c22018024041411142000041c025855440f011a004140c0116440d4020b51140014554a60500e001d00d420741d03842088560601201c18018011000194001d043c800030900d001600da580c1c10340350003442039114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 347638264 1250 347637014 347637041
    0x50c060f0d151412030307080402040e0d02060403030e07080c1c0c0f050a05010e13050907080f010504060b01020609030d110706060b03100501110c0121020f0d050601051e090103 78
    0x180e29891440c100d5699001c45400c2400600f108009806014900c886001c60514a800c100700190340706000d000380641181c000703800080c0b0018040445803a10034040721100140c4d03c80000c200070160705010b01d2001c681030364003070904d903441c020006550301c88551216100380382c00103042c904a28002c0303003000307040d03001200721404554882c84001101c069010300382c01038001c3e2038041159405404040d0702d2441c06007103003180c29060100200184000b400c10482802094000940d10790308000a0724500d898000000781030600e40780480803606100c42e46819500803100700150301c0d03000300030b072804050141f00101e6803510312038540440d0306c0ba418009040500d07080000c1940d035055006544a40c0310110030380c2105844074019a450344402c44180b500343d00c415030740e4006520442d40e145900e822030f00c0c43c030070082131030701004182c4e085003401e103007100b1020070000c00c00240c07070045640102080c01c101d8139140c69804249000c0601d4406004920400550f20501d82d01c03940c402e40900d1040c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 347639514 1250 347638264 347638271
    0x2100e0a0e1317030108071406070212010b030105190e010c1e03110304080702040c03140619030b04050c01021204030c06211b021b0616020112050405060105011704050c060f0d 77
    0x104000f81540080c09958081d11440401007101c407984541d09459090041c4094103100c0d45500300320381902c180c0700802c41c954a07030000005640703003406241d01a24086060203a0184400045022500c510910001c03036814074010024180d00603054200c0d00404518072819040c1c034260a40c003a0940740050042c0040010801c42840180d00180594074800c54091018801c030711001c42c290b85145000400340701c0380b080469400d190200c6000c6415890301c1d281040d407541da480700501c40504881c1a9415004107080401d690307810301c000380843d041655401e040c1800c0d0f840c1d20318180810b01410083c00f6280c509131802c0e00034107218600a621444080c4090505201d03007212509401408202612a4607807060111004104416020030050301003400c208a44150000b1072000c0d402c03e80c1441203d11511102c42594050540320368090f034010002545054001030213805104503000d1040c9600040c8000100302040c00c00c2003032000c80340e8546503c20054500e0b040d101c0e850030320190700d14 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 347640764 1250 347639514 347639543
    0xf050c0f090a0819120e0a1401020c030307140c09070503060d03110f0d030524040b0a030b0c0405100503071d0a0909140f030a0903060f060e04060902100e0a0e13 71
    0x141d0362103004c0458413920300030459071454241900c0112541494030b5220302d40103010310003403a8412030403410200520403200408074450109042d90300840e416903440ba4400e60300c07020081d04200700043d07000203982c04059032414000040c03450001910680c071650205041200345407142d2004201068074a0556060040fa0000e140c0d42d400c52500c0c8001003802c00c400902c9002c690b002818016604d446104070360701c807040030000181080c0fa42c10b1341c009034502010010078020f400d290700c100c200e081201d980d6070800041104c4030300c0c408d03080c0d810070004004201d1311503400010301803c0070081c054100d42c4105180040c03d29110341c0c000c482901d103414408814801d140c449074101404003019201100040364000d03440b441040c00c11004124085402c000042c3c141e4081130100c80d0300900091019290a104109454240d8054403459151940d140c1945040c00c5203c91081f070074208014032003c4180443c003524128030804030303040038a90008108103940000e03456090b511020000c0f582c030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 347642014 1250 347640764 347640793
    0x503151306120b06030105090d050c15070c0c0503060103080d0b040605100e0405011202060a050c030904020a031406040501081b030309030313030b07020109030e1215070906030f050c0f090a08 84
    0x20b10090076200c00340d005000c03441c00d0806114050080c0b038448081c20311901c1c0c043d030a981560000c8074109041c880c1c3d4146000348910b44a00a00405a0303a548128018603400c28185042950b00300a200741c2000004000054503002290443c0e01c0b08200441e81000d0000000e0041c0016882306421660040c0380d42c616681c030060007403607020700326400c120316600c03100d820400352040c0c2c0c07009410002c20081004514080c2002c1d0429508038400c903454100b04002003402c0e600b1410316038020903126003035400e00070800115164414415101000b0030342c0751603d40d40d40d81c1d45010f80c0101000100c2003034492134074280115142544007808030b96461010811035824540743d40f006442084c18200410541441070040c09030740ca41540d1046c0030b0385080410010081d00b501d0107440c0d0b0707214154525002c1e0f0600450b003441900c1c2500c945030a00d241040140a4544444884005a00e80000c00c61000901400d4891850100c040c050b2200083c03030111307404011540191009120b250b000c1540d80 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 347643264 1250 347642014 347642039
    0x30d060303051908060603040b06120f061b0c2806020739140d060c02060603010e120d0507050408030309010e0c090402010f11030d02041202030c0307060503151306 72
    0x5109090034103d101c2e8500411a0b01c0181600c000398421410404540480c00160341c0703d03004032004000d2103541c2008000d41d850144201415a86a00b1004c104007013010380a005104540ba60b0034a5031914150070380301030710342c6c00c848160512010781034041111110f40781c40035034106510030700c11991142c1a05103107080c1e125a203031104054400034415180044080750316908086c501503403110080c10806141969001d40c1c5142e40c1124a0165010104400c2e00030f80c0c501e20150340280000b424034000b4503094441d00b84404085510003544a822000d5800c200c4600704550400000c3d84d807241d86044840e4810303540550300c10700c03010092040100e410b610502403800c160007290345404103801032054452045901a0100f00d9900000788014013035808406042024030507a0329000350b09480317000f20f030040d8010506c00c1d104c0203405000c60a08009801340d8040840040500501d44840202103200080c856071108500c209080f0386034403103c01560781420b504070705001550712800c441004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 347644514 1250 347643264 347643277
    0x5450313030c0503010e010b0a0b07020f0907110105060a0f091e0204030503030106080a060e13050a05030409060815010f050d03020a060603030c020f19140612070c0309090b21030d06030305 83
    0x13039442d11000e003c82030014880d82074a8040608002d8096103011119001030b005608141d0b048514a00e0640c3d150f40c94048640c45102070307495114074080903403240380c04c45000038607440c0038107a40107051061320114080c6104482c1007600204281042c4840c009400d82411009094107001140101c20000c1c0031018606842e89030340d44410680c0e900c03004034141c95241c030685030415881000b05d121aa20482c40710006400380302201c11100203540c606141d9131103039012941d4203568400601403640103000c60320240f1000e1002d0541941001d4981d149d90350144100ca00c9004d04045480070113009020140c01035030000300c00c104041d52410b001e0402060b03003c1c200d01c1074000054152845c5880d032844441560079a007210300050600340284d0030310311b030000380300e50006052083c940c142008220403031007055161303100c40302031250f40380c05450a025600030002040c02d08140c0c7c2450744507030219140c0300e000180c110a169900d180c100d41544140c00284a03070701e05000c0084145500403005120 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 347645764 1250 347644514 347644519
    0x10905031909080706260105130203041109150a05010e130902010215010e0114060c0c1003020403020402070c05040b0a03050c1c080c07140406060516060e0a0605450313030c05 77
    0x411b1180c01180503802c1d00900400d81d01c2071090240c49090005a4080c560052203200e013807000300b90040000d840603800f1603460742c950309038540d0700c40303035080c101d00301c0c8001c000a00340300514440010005510b00c0800000a046664855824055a00c03c00c203d080018506810816a50b1602c600103605942409580210101c2da4600122400c00000f12080490908064018091180e04000c80072900b04502c000300341d000c1c0400300143c0d99501c020b2440c01e1007010b042810a140009200c00c3e56010400103120741d900b0b010070804a240415942901c004c1120b404e050220703004080c1c600c104a4980103000301002140e81600c9400000c0c20b04103640a1400304020680201c082109440043c090303500010000e000d5051255034601c0da90311038a10408011134041c0300e41840601d070660491007590720380d480c0c030244003200d0351500d07103100a10720b909400818541d01c410344800c0711580364054803080d2070b1204001150300d024000d592100500100104140d135032400c01d00d03240c8000380541031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 347647014 1250 347645764 347645807
    0x9091b070b13020102120a0203180114130302031608030d05070c0f0506040203070f0b0d0203060a0503030f0a090e0c03010311040e060705070b01080714100c080301030804140102010905031909080706 87
    0x1c20b410f0900d0580d941c41226500950ac1d01c4580079010544180790030005044c050390481038117900403c50090030044c0300d6070203007510051450042601d8040c070407004240b9016008800d109401e00802110310980c0d02c10804501500ea040e000c4810700100e00f006130a003007502881074100403000c1880d074015030089089400b100e444c0c001305160658140f00d0135000364000c2050001c41111500a544c1c00407004000100482da44d01c0440c1c00c6601850315098a1000080c0c0b245c4407a81104500c0e0140911100400b414941820310741d14500c018007001d02081010412066165140c2c0c110012070002403003910705c0e0342003d601c040c0843c1c010000880704200c507a000828808000280601152010b14484141500342d0050242c2e061440781004104030600d42c000303020801402c0154020352081080c10303982c510b070414490540000410301c4dc110390401d4843d02c0441c0c070000a40f0121080c0801081d41c031200c044040d664a000381e44543c55a020f440c2c0d0000e140f0303800000024151282229030f1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 347648264 1250 347647014 347647033
    0x6030607031b0e0102070b070c060906090b040515090d140111070f02012607050d0605030a03090b1b07080102070b130506070f0504050d0606180209091b070b13020102 73
    0x55080e075520101d403001401c4180c1580300c8051150f04100c0c5520010b006440c005900c40003103c50a07889410240c0301013130302c11402c20480b50b115070410014000380c54030703861075030800d100c0326401d20440c8501407213200444200c440010307240c1c0403204959402404c0e1501d038002413501c00341c00014014440919441c00c0300460100b11f80c0700c00c607402d0036400f1511807007811081c0d0064900d283c0b0407a05103030035895110711540c6915030325000d50149900c1d031115511030040788075000640381d542e04114000c0d0044681e210020f900288000c2c140c441d01540c032901c44040c00701c41c540907600e04a8403070f00c621450f070000681c18019402006441c2c001c03480c500d09960b43d0855105924100e0900500760741c00100041d906030b108400551403c1c40e0fa10300103141c281d585001480200400c5419140076541d080108201340c68418a007900107900c210079230400e03802100060305564001c04800d280b14103260b080010540391070464409550102011019003441c45a03d404059040c001300d0141c131031502d01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 347649514 1250 347648264 347648267
    0x506011808030d02180a14030601090911010e011116170c030d0f0309061407230a0c0c0e0403110c1807050711031905010617030406050705121206030607 67
    0x1040151207402000707502d0b1035958285280250700001c0e030705480c1d5490707441404182c0d030303032104540c018030b02120180c1e00d0f810104101070500f201a03005429583c40c000d02000007a65860b007035a4074280900b440d0314620789400060b610300112548501c06409072a420301c58000c000b00c500b000392400da403400003018048110603603480002404440e4540c0c04a032160350a50300c5a02409000f051914001c2070702d8005a49040c1901d0540c017080301e4000c41c135003c00404070f6025500d0003001203660180c1d0791545403040b9241c00351158082007001c100000c05980103000f00c0300b00b118000c0402104c4044186040c1c100288500341000c40e8107090f01034100c0565903454412404114800004042c0d00c00d52070b51103060701d655010203022200030b00320311447d84455500740041e40c503d4600a000b02d074854403501e403003801c46855400424400529141545000d44000151019201603040280c1d54002c0341c1011440d0050b00a0350714241440042c80d040e090304000c1400d07015030070035002c0f200c458959020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 347650764 1250 347649514 347649557
    0x81012030c020406151103040515030c130b0306090915070f0504180e0f0703020303040902070204150311030d0c050a030309050f0703050312090307031e0c020d080702150304081e0c030a03050601 85
    0x181c0b944481d41c025541d4040001c1c4ac01940c200d5038013105585445601d840c0040b03035840c103038403c294128020080201c030342801345040b984908040007400049200b500344120407000a0012000c01c00307200c1c1c0a50b9224095021640a0924036140003090380f60b02141c0e2010f8001c15107100aa8020502e0781c0000802c00100b02c0242c9074001c0c090360519051416090007034101c1c45061380d02540783e00340900c10303401c070003907840146010300d614045520814051501e00900d4490150402c201d420001c2d021401c04034051100d69410301e800302d0b0590560424514020900c10038003014051070310000104800040102144500c107002200c040e920740d10190b03141c0c080c0d00009400314090307000003580c1d00307184c030111440c8a01a0810411841603600819211b07204d8280803030310f0030300004420003035240030180c00003000c11a0402070701e145441c0c1e030380300034074050180060041d101c0c001c0520000e1182c601503e000c1080f000890f41c807031300b100034018060181039800e91301207240402980b1010095a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 347652014 1250 347650764 347650769
    0x200108071e0306170c1f080c0a020a0c0e07021612030320070c081501050112022505030a031a0d0305030604020405120604050607081012030c02040615110304 69
    0x885000003440400685400850034030341034402c256a0300300100e0780c50605584809603a441e40001c21000b0f00e007905100c0030f14410301c00700c4004119080500280399110710f625600020042c000740d00c3d04500d01050786882204080142030140c441408201e00c08a520707058820807440c4c0c00c4485101903030307414220035102406403503442080303081c0b0603001c03030b000307800c00c922040c200c0c062180a4450385800c80e0b0960000f0004480380440d803803041000940800a120000000ea41494040d5241c54006440c0da02c1d441c071440c0300d007a004108100a40301c0c0c84800420901042c0711084003901d9482d0598072a40440c441d040464138100106008801754003001541c0f100140c8644500030003501c041d1141c0e00000d08090340303d0740801c40840c45407070f444006006810710b4001840103041625007182000001800502000103442c1000010f141c0341060004031107013002005202d4009050403544050b01b104043e402c6418030b0340000c0c41c1c003000400500ea905040e50b82d918820603408499442e0311851 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 347653264 1250 347652014 347652017
    0x607030507090e071101021c0e06010506120a06030501090f06050a05010501020c010c24090c21020d02030109050610060e0a0506030103230111030403080708062407050a20010807 78
    0x403003090143c002d000800303a4200280b810400e0540100c808103600360307070181d038103109445030030703a060300c1e16502030f0140f28166140c01c005018158109808916603000301c600c2d41400c02c04110104002c1e01c115400790000e10380001c02800761b556507003850314051b420b0800441e01940340c0b10000c0c04645562042c5810b0f1141640900341c001c1c0c40d440111940c00030590140c03800d00c04840c00c03045010000f041c0030314044481902041806407403d2500e10b0004036400349690320115030b00b04806681d12543e6140c81c940c100d0740c0c40030264840c00030a0051000000c028428864207080c0501d46170381350075000490f00e4955603030503074092000500c0200c42ea1403040d00d4000748107000610001e040b64262003901c10b10483c0c46003c3c400e9884101c1e003034a250044140301c0910000c01d105c1850f41c00003030a50300a0060030305403800e040c0741c0d0214a99440100140d0010082d9001047d07100000301c04803998243c0040480d05402c02c1802c00c40060b129400074000441c294810300c105c65400b81c014640f044009 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 347654514 1250 347653264 347653277
    0xe18072a050606011106271e0c19080a0201120b0d030e0405070201110706050a11040b03040b1005031906060515030a0f09050a060b060403020406060e03011a0f1e15030403020607030507 81
    0x1010070100721810000b010001c503001c1c1151004190500740340b848071100d4480000d007584041a418484c0304082000000522b42c5603003824041c3d80400506489030660a10b000880c9480405000d0010616030b004a07603c044154001424103900c40e2020100d68000c135820000e5858010090303081f1401500050190340b0248481004074400b54800d9a020080c418081840c88000c41c0700222a8042c0d0802c5003140c0d030100611060007000c0c2c4802e6402214091159403d50400740020b0707035007800e0301620340d6000e541e0400030104211a00000010039024221403404030020001d026550021155054201e203404003903410128203005404c51160408068103141c6242e881e0207000e403d440741c03480c0d0828010400003005886610a040003000180d40301e0782c0810840d02050f00399841d1308040c10107441c0007510240c00c0d40d65454500e000380e8044071007042980c1c0f81e03903840310f01c0044c2502d4158040d55030b55600e030580202000442c0702d10301c01e5007600c005d652826819400c41350213a5040c00000d40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 347655764 1250 347654514 347654551
    0x315030712030c020d060c0512100b030a09030e060406020a060f090b060d0c05030d0903051509030a030f0e1e070b120c180d05010b010e18072a050606011106 69
    0x40d1290346600f500143c40741350151000e846d02e0003565050401d00b80098000a11121000d54100031207800034401d80107070261920300540341a55020140131454015582c07526242014090311252038040c00241450362502c1d0f84c2e000283d00c0303411035003042c0c0c2d5203404e050720b008007a50244200c0c3c2c00c00b648114100c50b20f490311401e11543c1403401d40100c44950070442c010880742d4040000440001559480082960452803c0f0303080c851b8000715044d10003141001c0c00320b0140c010080d03441481141c0717000503e4410599049010b00761007400811503000d80c5401710710050004084403042d02903a000c46e200c4907961405c8a6092240e48404854404407c010555508144009011019507a0500303803100c07820304001010a602d07204c08441d00c0c0c0d980c51008400d540c1111100307800359000c6802c01d41d140710117403072400705d0f0000820000c200060840034050040c900e00c500c60700103207001940b60181c280c0385031656582d0307019640c00c0d010840c0080046203080000403014864203464410240383c03007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 347657014 1250 347655764 347655767
    0x1406030d0f020f070329150f0121050103050d0801140409080405190f06020309010215060a12051b0d0201020a0f02150c030301090c0503040218090109060f02031503071203 75
    0x210a40c20241103000302d4283d8110460200301e02000f0394003803000001d00b856008070b20101000040b904030801d4211004001800507905030b2000c2054080d210f05131400601c0c001241d0b40c2001a40b9400503480c14220134800d40903590103107042e24030800440707100f010400419071f11450240300b050442e40f014440c0d80701a041c01c1c0c0203035200b2481800410b00301622407000460021030390070482801521103504010392104035802d04010000d50018518000500000070340711904040c46030302042500011130b040e500c5a124040040107a4164200c07000800c1c5040d41c0c98021603103018a925165050555281c41c1c0101800011385d8160001c080f48443c5035200b0340203040001060703a214051204000180d102180207262880152000d1541d079070400c250b89080703407040c000c03030030070003c0600821005851f101c00c03030300c2070f8041e00306078103c96541e4003183c0f800341c4070721a801440c407810b00c038101d85495910380240d4084c40f071038201400d61a0080c028180c0e100e54030310550014403a0807180c1c0c004617 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 347658264 1250 347657014 347657027
    0x10b0d09061503060c020607140d2a1d01210e0109170a02100912080a020c0717100c0206151815090112082a0601030311011406030d 58
    0x620424010901e4809801040d0340c2400c1d07540203480326502c4504ca170340d10031380c140700e0160702003d5818900072881c61117082c1880e43c0100c0b8071040c0700c00d17a00c0d4a1414081e299000c00184500c1282d8180301d16041200020107400095100c1c00004003100801ca10b02d40c05150501c3d04400329040d076107e00c0403000f403160007400604ca44200340e075503203036001d802141100e14911400c4201c101840d51381d100d105402407a0245080d00440e49074501450031001440c5000c404c0640701441c41e091030302c0e4a4805000d4000e00c52014044214070030000d00140e80c05803241074145000089094811440c0c400e1129801d5585c0c07085242d0050300004c00003146820560321801c1c2c510001350204290003a078205000c1c102c0310a4990344c425070500f55054841345440601180900f85041022000f102555a180c4840c0200c000b803548001c02900a4040c0415192110801c05400741c22202c1c075507940d04002e8283c00c00c0b041840c000e5401d00e1811001e448039400c180c0c3c007030701c0080c0040c110300c210107400300c946 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 347659514 1250 347658264 347658281
    0x20c060106080933100609050301060302060d0c05120406090201081810110f0309072d0b0306180406050105090a06030309120318080325031205060609030a03020a0b0a05010b0d 77
    0x103011201156002c1802c131801114461a0f51815903080342d8200b060240015480f948003510070b0b81400c500340010303250042940e490401d101c8004c81c6150325000103503885d02407400e075140728261103410401030100c10b0b0491180b413030003a200c00409881d401080a0084400b00710b400e81c40d4080418209020b00580c840600503114940d541c0c2071400e9003501c0701c3c1c0340c1d200390f4148215a0140304248050b085c0d0007030f07925420304d00c4001d014040c1186800c00d400d60405120308880c2d2170005c400039940d5251800d00c0291003115180c00c540910b458503000c80203103401e0180f10b004401c00d00001301d42c1b42c058030405080d2a05a2511040a4030780b4400b001e642ca0f01620840c1040481d072100c66600300b80c111024083c00b802006140c440c9030401ea00450029009a20100090100c00c18000b10f074200c41e00f14403040c030468000c5450341c0d8400106610f80300e4582e429030075205103a90b6106045e808035151580c640705030380300416034803001c509400391074003070241c2070000004000140d081803455211003071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 347660764 1250 347659514 347659573
    0x13080a1a0a0b06070f020a1203090f0b0412031d0402040806070e010801050d02091b030403020f0c1e0d03090803031005040509010203040302120a0e04110d0e0f061503070315020c0601060809 83
    0x411f00d40b40d9810505140e05407004030b006c2000464240a40c03c2c40507510b002070a22140c2140c01c3c10305d00804809002c04505c00501030045150542c91340300d1107204a0900c500000d0000e40d03955039035110dc2c40da1140c0c220360000000300b1044088141c0d62094017414102c074001000c9010030784058082028201c400b030034449001c0c07a00c0307100129501002d80614070a90081d005440100080c02519060486025525100303900c00c0100b030541040b156420036140c501aa8060900a418541900d000d40760790081c0741c0d81c0c0300100400200d520141030ac1c5040d600c00b0340c0e060105403140c9400d54280d0105503030040150b0400d40c030700136401681c503001d490441c0c0503180c07507981111020080740c202c80d0f03402075004802000040e40d854120341400344080c0292440000c001700c00d1212a215110f09000d0108401d081c0d4030000e501c3c00f0f9804001d40000745420114060010300d964a01d40c000358040c441406080c02450b0000880034003c400302c91041c800e14001c0c0501e00d0310550484015203652161a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 347661870 1106 347660764 347660779
    0x8090a0b0a1b03021608030c0706031104050105092b020423040b09071d0702070f060503151201050708061e01050f13080a1a0a0b06070f02 61
    0x1651146001d858069031600d280807801c00580f41e0303042008444005d804a4413000c00300c0244000c03030f0184202c2e203180380c0d00c030340c164150741d1050003a05046070240300420207540140005d101e07007003000700fa052031480090000051245103c1c81e480d40310394a55030800031414588100c4401445002130b000244403021b1140d8001c0000a1004140d02d4220020906141c41044204003512581c88000301156101c0c401103040380045032444010701c210382c00054001414180e4000390703403280e81c4091031a03a031a401442e569503a01d000b40e401a11400005c04075010a02c12315000d254140d484072035500340b0408200d0088520101e5a1103100e10804c1c038030340c9a80081c11140c20350220640700e071b243c488242c8150b64864a560008030b4900600c00320000704841c0f00000044080c0c001000700441d03c40c500c864046a100c9000c10341c2050301041a08082011a0800901c15200500741c9 = true := by decide +kernel

theorem cover : BRFrame.Cov 347482014 347661870 := by
  have h0 := BRFrame.cov_init 347482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 347482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 347482014 ≤ n) (h2 : n < 347661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
