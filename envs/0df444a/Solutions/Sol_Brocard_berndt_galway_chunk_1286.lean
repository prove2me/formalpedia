-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1286
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:10:32.761535+00:00
-- url     : https://prove2.me/submissions/502561ed-2114-469c-92de-5c86af9aac1f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 231115107 ≤ n < 231294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 231116357 1250 231115107 231115133
    0x906060509150a1707050103020d183009050d03030f061403010e0c0d0308070c05030409020c06090706050d02091903060e071211040e032107020d03090b01050f0d0f 72
    0x120031200c0000000b100e0540c03003c113580007041200a040c0551801c801500603404c09060451501d49920441440300030745000c800b8140c3c00b50080302000d0500e074141141c072450008a0924140805d80c1d1034248035007040c2c03400c0032203200703503242c042c0d1203003c0c102200105030382200c840080e8100680090103100142d00c101c030700c0004034020071901050700e281d2130b07542d03146004003a0404c2200c0b40c1c100210380100400c40d8409800d08080c5d010f80400d54455003198810f4002003d8181d010a080001200403c505507000c80c481c40100703c1207080c6000500203020304100c0d030848a130002a8801c20f9103901510b00c0bca401c00c400c8000034262a844d01d14068140c3c01c0c1c21404a1181480010381c90006480314080b2a03003110215040c441c0c0001400040e00e0210b0031345a91b48810842074120400020b02c105010484c45900c1d8541c0c105039a0003814100c004c55000105400c140c0d071103011900c103a9140341150000c0b03c0e085401a620800324058051081c8050300c66036050544509200700c0c2d8000c17030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 231117607 1250 231116357 231116359
    0x6090309030c03060115140f0c03030403260f18010504060f0507081003081b0d030906050c0702061801090302030d02010225080706091509030324060203030a090606050915 75
    0x10242c9480d0410326079105000d12a101da0310703800041291440e030290303801a40612040001c2450440f814454000350703031145415000f9580700004000030301d85d1103e4a800060290705004a50103891044510b008501a21010003080164081218a41814000e4000002d420004d00451a0a0401c20002c2a080300303441825030a00c0700054174a40705005e201d101d20042020582c40c81d04544410496030413008581c3c00034a118550044541407c200110706185e007070382d000c602d498151414405544000c0d0a4444d215014420741d0700598407076050751000380c0000d006c1c858061440340100c40c0303021554000ba4150080c41070088000342c3c103400608201e64252500c010700240c1078000c0c0e401649840010b00500c00078004000007800d541c000c40e99242c02580c91440300f200040e4020111020800103c001c241d403102c04898006030031052202e0381107000c2d0318011451501d00041c0d03c0317100007050002010340d150048020056551310120107440c02504241c040d2405a907102e2001c60503011803 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 231118857 1250 231117607 231117613
    0x4050f03041815210c2102040e15010e010609060903081617030118110a02060f04051f020a031b0e2e08062716030e0609030903 56
    0x1108601000001c960848805050803180d102e20704120600030039083d0400d098818070601c0c00581e001040568207194010f400854031042900c5c0b404040b00007651344000513401d14404001e100107400c3e81a10303105501034402184149034001010700302030103249510106000b420010401350b0300c0440c4c1d503040c0c4400e03481d040717112901c41209581c089124800286050010801c0a8410070711001030b20145100d010f1100c2141a6034181c00c1007a00260003000d00b103c50441c401c11001114055080b014844c880203520f08000c001001b519000c00500c4c150325031101c800858100b000c20000200b42a48081c8500003c0020f028001c0295005240e8440028200150041c20000400625401c00d415444e5030b11810018400d1040e1400d400710708115904c00d5003400c20441003107003040e542c002029503030600c2d10f02e03000c2e0810543d011100307680038400140010410048410031485a0001764075400c1703081031014810210040c00c2d681c190001c00c0e00420051100c1542c002028080c0e0030811415 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 231120107 1250 231118857 231118873
    0x31602070905010807090207050309031c030c0819091401020f040609080303070f030506010e0303040b0903071e060e061603020a030e0301090b0a050a06031e02090a06030b150102031b060405 83
    0xc01d40c2642e001303001e81c50060700b00301e000308000ca01e00c3c2d0040006a10031802e80342812502d80029084c06c207c80c1540700030309484280020000e40c035200b4001c0e41d04007818155811704001c0420210543d0145030b000400359034072851070038880d003843c010000810700d40080d9035070300407400030600e260018428030005c40d2410801040001c4080b06881c45021681d44881d004440d80d0003c501034a005031001e0306002501d40071448540b014001400034000200c40c059450342c200b424540b52460903800300c44106000c404a09621580c40807410485010b40b6042e80182d13000c4002808070b2040300d0032306c007501321100003010070185c000c11103100c1036001e43ca8040c42d40721418181400d840d5400c00061151007800c0004018003002d50041d9000b41c070240000076869160350341d030010424100da03204c01441c1400b91610442c0f0300741c40c1c0d175603001001d050140100d52441c0c0d142d40003104060000080d5070f00000d1400d0a0713034820800d88400c00c46140c15010340c0d50361000002d840781801e95003070b01c0700d004140c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 231121357 1250 231120107 231120119
    0x1140f0a38060f180114090f0f060a050705190c1502010f05040f060509010b010e042004081b0105040b040501030c0e03060c0a02150f04031b080a121812050f04080303160207 76
    0x302d520945107104a06c0d03282074881d40400110101c01510780f9800002000980500d80394800134200c4c3c0329003601c60658854490410b00d2400c03803c080b0005500c00090101c900084907034203281e00300c4081e543e0b5540203c40c0040164054492080000035003840c1c90100400d004011068480b8140900c004000c01c0c0c072010b01c064241c5d08000f00c107601151902c110b040e02420b06038841c50510740341d10f029407007a8140702c081800c03075881548009180d0340415512840c14100741d000000c0440c090174440d2909282108a9500c0d0186100d824185a543e4801661560003240c0c40c40c5582401015507a407031a2080c918003417500300d00c2c24100103100b01041e0b4810f150301724a681b8010203008041142c2c0d980c03075540071503140b10300b10400e40403d01000c16200c0003e42c0d000180030030b0b100c01c0c4c54204852840d200c5010440707448501c0503a081c0c0c4040342c4d00002c41c02021542110340150f02c0c00d02d0b90340c1d071242020f0b010745c41180d01c0a0340078440002080701d46414003411030001c100399400d40d480c09694007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 231122607 1250 231121357 231121367
    0x40e060420030304050907030204080d05041d090a020a032a050d020907021504121b12110f0a0c030b06120d12090501140f0a38060f1801 60
    0x220010594110380008900025200c81c21540d6a54000c084903c0d054550002c40c038444410346c2c006002c03c2d004101440625010b0000c091407100c0c61401c18146031500d0001e001140710000b058034080b01d00d1001c140250000c2c060610083e80140840381078640c1c92510044954110030001d000114008408000101d00c01c0c100f003c03104010503201c1205031076001c000b0310560141021066118808104d50000f968a065510460245401c0e4103103c4e254600a0300c68280d000b1030025500c100000000080e80c8801c0c004030024030340c0351449440c0d0995117001d2074201e071090580c010340308161500e0b0070030800721704010580b0303c107480d030505e60388500060103040e491000c1d0101d019003103141d2907481d6038810120010050032645001c0350b400110b44a413821a84111080f0300c0324841c0da0308001001043c01c035043d800c81c42001041105450b9201d5440070f02000f41c0440040c00d0200c00f44100ba14500c2d0303002d8484c2031000344100d50311360000b52010b249a00055162162565012221105600032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 231123857 1250 231122607 231122611
    0xb01050c0c090703090b130606090c020a0f020105130806060a08010209090103080d020d0221070e010903080310090c20061902030a090b130b1003020a06050307030216030509040e06 79
    0x600911074200d80c00204400030000a1a00082558030140b07900400c8150840d5070042050b0b0100c813000e40e9090030594240d40346038200811003405d0140910002c1d5001a40651040c3c02c0002540032001d2403004840c40e214220400541c0400c40801050302c2c1008140d00f402000200c3e094500b155407801ea4900340c0c0950a00e55612a454800400204180b400201000c800c1010010715121112049178200c0c0c101344c41c000c00020740d80e020100310300c01815005800001d14103000620300030000c0000c01c0f0541500005240b5040840441c980d0035881e24510040c00c421201400121400b05000301001d40d503002801c4c001e80b48102c806141980400c0d014000c3d01c0e500101c00e280381203284100040d500103450300c00016030b00c0440b0008514045900da00400351050f98120040c81420454400c880c054940303400130008000410050756501071392400c440c5141040364030303680e4818058000703009031070711100c046c41c40300703031080815520200900210400326010400780c942802a01d0b51140c3c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 231125107 1250 231123857 231123877
    0x3020c01140c0a081003051c02010b0901050f100c0503030a0c020d050a1202030705090919060819060e07081204060801060503070206060f0a0308040e0405060c03150f010903020d030f030b0105 84
    0x30800100d115105514040e0700028542e005c0303a00540e26511a8a081c420064104080310504c18618202d5820700940b808048105c9002c03a071075043c40700054407540103140c1c0a1240102c0c040c0401c44c5400350100d0601c0c1038106003a0384d00d0b031410715101c1703025050750418a0f005000d4042d0044825019505441c0400110313903402c001010350052420084d4800b610aa051203014003014119a80390840507200d000203950621403040650341e582d0548100d5007080585402007041048d00f0614060003140081c1c0000740860321460702d411041c01c0c940107402007500380c02080c00030880c0034504401441140c1c0d43e41ea0303650b5180e80c0c9040c221294001aa120300c01600701d440840d03664a03040c0b1005014200007424507541641d265560f005940c0194031107201708811104020501409110741503100c903010f252649186401015000100c44183c00f980c0f2419907400721540a0748205100700c040d5034003a1900c90300d1605c0c1e090190801c102001d44400090824040d4041c0d54883d4080d46d21100f2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 231126357 1250 231125107 231125131
    0x507140306160c020a030f0302010e0d02010c080604051807060201050403080c031315061d0105100306050d15060b0a0503040c090b03191e08040e07030908030103080a02010e01050703020c0114 84
    0xc00320b1011101c000d0160001e0b640000c2000003c40070980103203a1030f01380340c442c1c1c00000c5c401d011034034900c1c14100340003668000d59140c0540b003800150000304032640050201e500280d1941c0f9a03141c0501c0480a83d40003c281c440e521001c1041501580a00c0c0128003c0d10b414526640700946d000c5a40b20803600c0000102d4a82660000241140c3c001003044000c0c44000c00e096444816180040302202c16074001c01c2c00d0100104032a00300502251f600c2c031014030301444039a007028089400d5a421140c003c128201c000b80349080b20003a40e001001a24007808199615442d9041c010401d400640b4103540002d03c1c0c500c000b0b006001d500c40c540c900040500900b01180900801d00701407640000151944c019042c0029200380301a00360340421881000026180e03030070f11007000c4050000403c1c6405052501d41039101140c100000c0c0c90440394450045541c0e40c641780c00407805071010000340c001700d41c07d010034407400e2900364000c1c00b104102a4000c0102580c2d800303624203212070950700419540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 231127607 1250 231126357 231126391
    0xb060f070308090c03100b0109080304031101050c0c03030703030207150c081909231c0903080c0102130323030f0f0a21050a050108160603020904180507140306 70
    0xd002ea41e003503501040f640c042d81e5500c080030b80403a0818070b600d144000c0b02940e51343c1c80145581c0115850b0058990b002c0198240790540d0741d100390b142c44001d0181d0510402003145c0703451030410804000412406816030351148a81e10740a4080e40041800b210b080708405621445a181d0307114081c0b030903c003595412159100c10048105840c0840309030000c03a5141d00141c00895040c842001c2078080109a003426508500001402c00030490303806154603601483e0400c049070300841c0c1009030703500401c00b1941e488411210b54024490a120b4108030103030414000103000041d41d50005100140c00c162003a1288207031100c1d107038428403880d19160001480001e250b800b40c00701a000607003003400c00c59520002845107c80030407030300f4080da010b19112010050fa90b0901e000e000e0046c49110000c081090220703c0882c1d400c0001c1c001ca100701640810310030803a07070380e5400015008c00c007400c1124844a0780c2c02d10548a0b01140103140032070300c2055052805040004916100d0b0386045040c00c814 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 231128857 1250 231127607 231127613
    0x50f19150908010501080706020d020d020a3c03030b03030c070902030406090b0f09010f0b01020d080405030d0e030403050d05091c050a1505070305060303130b0d110a0804060b060f07 80
    0x690320068403908000c04403401060064092261601030a9240001d03c062441c0203c02481e0948009040c42150040c0d42d07002c5025800044001c15035510003400003a03030201429079a0900d00f00244001c800d00fa0666500762034055a0420712800d010740d40c1813058000e003005050343c070f204101119100e50311280082060381103a901458100e03105e201e000c580175480e622812001c500550346401180008000c0c0709044c1000d2090007240c000050040c09652900700001c3d44848000e00e07000305101202000808004082c030481c2e24649002204000700c90149082c01e650340c01a01040751182b142d40d083e50401c03405074080c0d40761010014405540c0d0091205660440980c0002c00c903018858032840300b000598070340d12003900080341a400101440e041000a0549601510050080d0010000344201103104004e9400340c81030754050503aa2034903007485000810b400b083c84034848d100070461038500d5520280d80da004a020f0502801a480e03903104003d03040c03045460010740054100154000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 231130107 1250 231128857 231128879
    0x501080402040f020f040918020114030907030c0b040302090a060e0c07030c020a120b160e010507050a140a0c060504080304061101090c08012702060d1e02070309050f19 74
    0x441407002d4404200a141c55403440242c0e000f00e054805010310108003400460054440c0546040b020500741c0184c0d50b55070000380000a50030040640c108001000682103503040101d4802103a0041454a480e9a54116a906504030b030008a1042c50a8404111100d8150180c10240d5a03102105005a1960207000c4000d6000410480c140b002c0c190b601805039403070000c181c008120301802500c0880c2d2500d464219400300034025846000e8845290309403903441500c400701c4030003e007802c940d21040ca0808a00d04298440020312901a00b519594490741c08500c040c1e000703215110710340702d458440600380d42a0150b401900788961007030000b04001c034410703c2d0b08094080c44000015120006440c0c0704c894040580007251035a440c0d10600c08801d0074040700640c0d024000800c0f00308007559074001585803140e5403146110302d032240c1107811039441e00002110f041100f02021941c491091a000c3c0c000076076441640d12819240301e81c00450f0a081c840c8107666803495040840060416a034041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 231131357 1250 231130107 231130111
    0x150503060c1b0316140607080a0f0603061a0301052202040906021b0c090109271e0f020a0608040206030a0f060906030b090d1b06050a0b0d121413050108 67
    0x5040d8441102e0a481d0040c184000c0c141c110203d007150400341030505091820103056103a2400c242d2021040100390b55110000e1b035000420032402140744011070242e03030050010360300058141c524203888203141400c1170796001c0513800c090b0028019a600d55400440481c0900c844c0400d81c036410381220700524095004100c1e44c2d00c0340000505000a4000941c007151203140010003c1d44040301e428503502d4038902260051071452428400f1900095500d622040e5004542c16589502c1000d40d040015031405070f0315800d02c01002c0101e450742410031f4000300041d44410303402100e8442c030200f0403a2203880c00c5485070350040c100c50300e9500c070b20801e00000c1020aa160000c43c2e51150041001092801407031f0082d80036407040225030810030300d210f08203c80e0080c0314080c4451100d06400b2114060548050302d0f4002c20005126540c1d05c07003550142c800c21800e50351048010176201c0c00c100a5420302c14114095560340c029407030883c001200240300b80e8600016404030f407070013048150301c10f1440315 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 231132607 1250 231131357 231131377
    0x1b0a050d0b0c19270602070303030209030703061113060302030105011407030309080c030d0b06090a0510121103090c040b030c1e03030708030105100512070302031e19150503060c 78
    0x83c500360301c201401405041140c00100003544072400c0c035850a110f9007520070440007501c0c10fa04030500d4030350040d55490003031000a003070507000f0400405a580c02d01ca08401160804028818009410020b110310b030300c001c0a1500640040c0c10114000b40b1902c25a4165201a12240f00700c3c0c20070fa1103c841c980152108070101512055403c00251840014080921000008607201c113440000401a1544081a14000c000a0110714242d5854070548012190261044403545d10040d0045442004018500c011141040c00360380103080c82d01d00440c82898840b066590711b00d900410002a20020030900740c0c543e03c400c00401a501c2c0c01030074500c070920009000028040c5403c042402d40e0400c1800303480c480c01c00320040006007050f0307001004038889868110714050b8029400c909031003010b003d00c1c081540c00700000c0c10241d524084407008200303200824005140c8142c441e006075a0420708811401e041074010f842c1c000301440c0c8042a00c40040140c08641c2c4c0b000f00006080d04021949 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 231133857 1250 231132607 231132631
    0x10c05010209030a0501020d0b1e15190e12010c080a110913090201080c04030c030b0c0d091416081b0f1008090d0c080a0e01090f081b0a050d0b 63
    0x5514540e0f080248070951440f8a0000d0380f9a9451004101110807041e48503015500b540384c0500052100d807041020140f04881a118811640700845d555018000c5000740301d404107a103c04513a9004218181d55603801c807900e109405001d0042420307911000260008104d0135400307e40c0421031600001070840400d902241841411b0b4001462030f2060504903141b2640c88407440291350340300811607809120020210300d050b1966454801008840c40b020b0031006411010a41c03912808007192001103948500344040d2070340c0e00300701103508404110b44201c1e10ac0d1500302941a5601c6055074100c0302100050325111050740ca1030029880748010690b403204400481140c2561a12600c0c40600d40a07500c802c0c1ca0b1820040c003038905a003003880c10f4213102041500304001045002103c03100111403810128900003000142d406010540103994005200000030030803401c00a1401d40b24426801441007203440d800a00c81c41603518002c2d80d40100c603815440000c181d21006494011000c40d4038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 231135107 1250 231133857 231133867
    0x1406090f01030e07030614090109020907050d090b1e060a051c08090418050c03030304020604091e0e01200c030a051809010329060a05010f1e0801060f020109030e010c050102 76
    0x4030508000303480e001190419510118072489662001c000350b8072102048c000c2080103040e80016203055030091902e000c1140000d80105c03880172942146284540c030010362010303400d086170048045580d104028082910b040005106454100c282404075003000e04590f000c1c01407995801d040320030601f000e44070007404100480c0c25440f00d110704100041503001207800d02d4982d150044c1003010150030a44030b58800c0c014040580d030b840b02240c084460b0a04006140c1011040d0016000c1c6103a100c0d0510750319003034088a1052064011708017108000101718900d4411410040c214003c000d41035030950702c20702c0fa48201ca030250008140c00381c4609913140c014941e2800061920000343c1003151103554100c1484c4890103003801030f440d00e69230907800e96060b2a04002003a100405845035a04001c08401030115580c000c9804c0c041c2c900c22003d400e032f8031820250001d061681e080c42504001404025040075891040c401c0c22420359056942d82c0380010f16600449500214540540d55035600f008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 231136357 1250 231135107 231135131
    0x2150a0c1b03020102040312080c030606160b0903040915030c1e030f060605040c0503160509040f0f0b100507081e0c16051201061a0705010b031608071406090f0103 72
    0x80000070502c29400542e40e9821413515900300c0f1444070403c01440658402c0c0304000d100b10041d03c0e40040300707496542d222100c01540102c00e10251720003030411402c1005010302440044000c10035901d42402c20310446410380c0300f04203003481c41c0c80044c040b040401400d1040c4100205220f01d00d0303041c10313140c10800303403079488000d1200b0781914200c85155550404110900b4180917103c04001d0708d0034400d003149024030345d000846901c1d001c00303001c020f030000ea035000b503075943d5004914038245602c08110b841c58842e02840284014440507204645d441c88444000b4880e10845015a5001d4134103410681c02ca4145003421007401038503810ba0409004201e2580d80030444141480032001e07407408050b1900007803180c10202e01c03c251b81b541e4180502400f0300c0e00c17160341000c4201c101c0d800e0f40e0307510207240c20014010590304145503814000d5000f449101c0700301d200903c050b81d0356201070301d5080e039aa030400c00180c4401810160030280501050030381d444c022440160088040c10040381e5018092 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 231137607 1250 231136357 231136397
    0x11121809100f060c1a0717060604090e0601030c0e040f03080403021c1d0f0618060403230c060703080403210e0a0302120313080c031312060c02150a0c 66
    0x90085000030b01e810343c0400500006280a452200c4002040803260800f100024401c0101f10704020b40f4024050110b80c0705c0d122001120002d104003c41001000d2803002e400d91503140a100960704500000740c0841c0c0c1000c4400e05c68080d945c40031a412288226031303000c0d228407000400075025800740c512200000e2052225108001a032650344d262015042081907001440510384240285000300c80e620103902c5010172280c80001c0015041d01a0050740700003030440c0b00b95000104841980880342c010641840410300c2034601220640f0008400c80c41400380c00d000340003002e80025500e02c00314010900918458000381d90200745001000d080500d02d00644130702c501180c610740e12085a01b41815414406141245a03803045070389142002090000c01003001c500250050030000f0354026110320810490302c0c251241c03111051001c6d52a03125544c1d02c440d0300f074141e42d810b00701801320031918404112a000c804248014080684841070000014610350100006001c81c4090641104c0901 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 231138857 1250 231137607 231137609
    0x609101b0c0302030d02070312030b03190602210606031305010b04140106020c0111030d0b18070903020901090912031a12160b0c070605160b0711121809100f 69
    0x1180030840721031540c414549031400c594058011904070520a00009810101081f034289007032601040c801c031030000003402c01d05d840c40080a90a000c940110170032825030058000c3d0300700e40300d03038600c907100140384980c0c40d4100304c810300e90000d010000120040b0b0210f40e000c880a01503c0000740401002010400700d03501031044240d510103040041020a13410405088035440c28a040035404002e20100f50342c034064007022905191302c407800f00c0101d07145c0c126081ca40601c049445452818501d002034007900140c00b060f07003c4c1564900115240c542e41c082c5080c003580c0000f0302442d10390451002c40052800c100868005001d191000f8076550381e900040004c108040042c180000b80d44000c0030842030f60b41e200b2003d1280900c0264000480031400400320b0340a810080e0351080c00400c103100700400744800404103200d03001400451a40448640f5008110f8002c840c180c500d00e04607209140583d008181b100c41d07484503450000d080c50781000350802e4040b0381e0344000540340c5048080e61400703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 231140107 1250 231138857 231138863
    0x80a05071a0f0f090102070302210c0a030f0f090608070e06090a0906051f090b0f0d02030106050d0f02090303090d021207030503030406050601031107020d140d0c0203011a0609101b 79
    0x90b00d401d201c040c045540380f490704299580000c5250503260f9802945801c1105009205010070b00d00e4403220074404011200006c2e0104141e401e2801a0302e005002090081c18034030016807081c4c40001402e0080b4940e0090320344689402441e641c81c140b0441e10844034507042a00014240424003d603107521100c000981550301000c1000d50400b0107000c015244c011f014081020050340d43c840c01500300b0a0754054a0708409116503070760020b21400101e03c00c40ba202c688192001000085080d032180c06010b0480300b030300082c06085055085907050303000e00d541040e41500704101000035850a14450f4918034400b4005400360000310401a0a00c44503500695054000200708001c0100520078243e0104c42404c0130041500b102031581e15500803ca402401171146803685014446035486625816850304100c0308501500c18004016072108002280a50b0074680081805240c0c52195080e000020340b4190070070000c0070401c204000d4415440b0240030783e40e0140c03540004e426402d8028070780 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 231141357 1250 231140107 231140131
    0x71e0c020301230112080f031e090604120509040605060a0906081008060606090f0d0c23060f0a050c01090303051005011b030e0f090a05040b060904080a05071a 70
    0x59140189803d450522248015800c91041c005250003581e02070310b8156146540386100031440ca00c1c00b40703c1d51103500503c080d500c0d4017204019004280c0c0000d80b4070104d221404840c01c0e00e40c01d00040c0e52b9a03041d10300600c4022031490040c40184603001800c804d0300000d00100300789640ea070115446070301a01100000440c680d43c03d200140c0c0045105400c6980d04d40c0e00003110385040c0c1c3d4651608030103001c0e00c2c442c8000141505140c1e8a21002e200d0500e00240044030000041c5400700c1c41d03805d6442410312465119090340d00700e03500b0014040307081c81c010307241515111510024410340e41c0f000603000c081c01001c0c401c000c040c10091240044003480384c2c800088a0815014081d4105400e0f40010f0400c81515880c0e410f140000302c010380310725403500b0301d90b420540010000d040510300e51907042d007008103001040200340c00b81c4c100f140070362b0041c121030f49151125030602041d40030490b005803441c00c040100c0035000c0d00c0f490040139a5400707280e80803599044d10041e004414026103611004079 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 231142607 1250 231141357 231141377
    0x20a0f05130e1e0c031506071707080c030c0601080c04020403022817030a140c0a03031a040c021605010201110318031b0d030e160320060307050403060501050f010c060203071e 77
    0xc2502c006d00790411608981c02c07400e010003030f500c419021218101e020345c04900070803910108540c0c0010f44095910030300035203840e11000052159104424420442c0900c681203078101103051074800c1341c0c1074070b0300a4254041e0414902c00350208106081e1680d1088400c01c170300041c80c61034144100824071644014507680c8802c1c8500a006401100b91002c00060070028080d1880001804e07100207940350602080b4400c1c9020000c181c01c400c0101e09821600346001d0612543e070128003c1c002d10f01c1040146851a01c2d000124200d80404540c080c0d940020004101c6078105003000c0c031080b02600b001c80740b801e85400c103044000203101a040b074807580081c284410054044c0035500c00032005000400c00c10000300c0c00a101852248000340418030b00000590b880d041c0c012075451505000f030031046c0c5e6820441c1e0010b07c682d0291109840302d900e401d00104551030800140f61000405a4072a64206e609856010003907101910010038420205182d1094640544200071145001d8075544201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 231143857 1250 231142607 231142621
    0x816050d0206011a04230a031e1514220c0b030103051c0e040903090515071505130201030b120601080f0f01050124020718020a0f05130e1e0c03 63
    0x442d040c1c22500d1600050205011b0030040c0c3c00c6094070a08090b0132640700a5020707011070040703500c94001030108009a400408141144031008030400e1042090100340d080685804044900303420504585101c0200490034500b00c1c02082110b8070001440c2004502c5140d03140380c003071070380b503801054462404001001408418400b44510340c0000c1004a544459410010003c1e0000d10030b06128035990300030b400505104662143c013506d000b400416680441002115aa810040301154595003130482c0c0c05440c2d4040c011680a0003030080610117030303130080d401540600000700206401003158001101014400c10069000301184000345c0b40c030401d0440f040317041034041e40c00d4039402d031f0401d80104001825001564046112000d440f507030300d00010812801c00f946640904044140c00100c1c0e0b4032228242c0c020007038444107848211442034007001c11b84d07190141807416220700458410410450380e10150666004009403007462074485c42c601c03500740784002641c00d5000c40c20080704011f45 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 231145107 1250 231143857 231143879
    0x303140702010b2b15060321020307030818150a0506030d0c06050a06050a060306060f08150d03020f010e100b0607020a031103030d0c02030918130816050d020601 71
    0x40840e0744002c0c004000702601080590094000310040c1c035918000000c28584410400c1503000c5e84000c858241c0341103040000301400640c04140d541c8189080320000101e0301d40782909200c4555000b860034540a51810340710a000140b0082940d220701101c041503280c28814282140a0355001400500304540d082c4110307030005001d07074040e51040c1c100c5000e0940020f515040641d000c2c00c0401c540c2d0352051160041e1103c0ea02a80d00f101d0402004604503030142c20942c141e44ca41d64803100d107800c95101c22142c1d400161441e20031160303020702e85070640c01d01d803d046001d039000c1d00446405026204000b42110005180000076810040c00c03404a903105006085840004540881c20001da0f80c0008803151824400245004104041d00f0700649090040c0c03150b4903000c00c010407032800310b9071010b5242d80c000d05066200340c5042ea003a0005140203c0701c5e60068801d0410074940e0141c0d540c440308654050f01d10304d400441903075156000502c082100c0c0703800083d03030f90240c030041d4949880495 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 231146357 1250 231145107 231145111
    0xc0d091505071403100b16020a030c0602010e0607050d20160c090b03060c0a1701030f030e040509071211040609023a0902010516050102030702070501030e1207020a0801050103030314 80
    0x3c0c901d5070810511407401c00700302c1104150350081c0c46071355a4000c15000c11184212000e402074000410b00000810f201100c0440c00071607245070028000e02908074410b549034502201c400d00480ca091000e420301905540c0041114146030300b07001794139280500302d001d4136084000711200d45486400001c040100d00d2203400014603c0751400e012850b100ba0004e5110503004103480c04580012880c000b02d40e01c0f0300020599074240d40001c49265031242456070000c0064181030300451105030403004541054440c4911415009024100d000d0400d80030303445001d0410740075107840125035000d0300c0c5503441d0302c202ca00910030315200503075440c2c0c400d9120f4007040d0350000702c404105101d0201500201c54905160403148031407000910352180e4801a5624000c90710400c1e5505950768012003040ba055000318010441c2e60207d411080e80c900046003500e0008200140e25004030040040e000000d00103071001c01c0c4000c1c017a5130304035200c0303c4031401c45009034000e60000ea2203512059803200e46400c240c0d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 231147607 1250 231146357 231146387
    0x1110a030b0103021908090a060c030c1704020310111e090406080313030b25171302030a0602030a0b15090f060705150403021606170106090e0c0d09150507 68
    0x917007040000025502c07054800407082044c0510fa80004400703280c1801042c5003554490303c00c10014050140080080c54985a40004200b1503d6060240c1e000c1000c2c90748610340c01402080c904c1d0200503130202800407040310b0302c0c0001c400d2003281036401006490391040c0b0303c1000c4054444c0d00110402059400950014889802c01c2204080320750b8215005c03815240c10410403160713910703050006540e01e8100b80b00038001c07200c0f180c542a00c50342e000a00c03001c13180505541410541b506168511020000700c0029450303070040031558009030b8560061940100788000014843ca034800105c1c808055020822090140000f2010000d03c0c114000c071604480c10384d0a03509281140d6900d95032800b0b45210395500022003000201010710030031000c44407200145003e0200c80e078031107002d82209590919030000000300320010841074442c0d00e01c01c08480842d80070201c6516000d02c1c0c0a079961014480384442501e60f406180443c1d045261802c00300f075405000540d51621210080282d29408201 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 231148857 1250 231147607 231147611
    0x1806091f060309080904020409020d050702190b1003080c0d030e011104170c130b04050c0a1b0503130308030604051003030e0609010522170102190c0302010e01110a030b0103 76
    0x3440d40d425034440e840040d01c0040c1030008100000703050500c1c690044034000b0b64042e0000801040c06200ca8014182603080554117004948802c01c3c01d036201d5291443c2e01d2018100e2000c200b0120b1442c03c1c00075040703100000c15400f240d27102c1d1660100c40d80130381150380305988510b000e15000d66046c410002c14006541c0204903080594100c0c911500c00c520401411100e8105285223814043c0300e46514018010100c0745500700703a482c503402605101001c1d43c4a10700e480d00207030031000c100301110a0000075070b5070300b81d54401b41c07040010551100b08056a96100c01c0c40085a019084400070011b1802888542c8c0ca038640a000c20081d14030042070304030342c52040c5d102003000035001038403141c8605045581c140c40d40419401280e0500442200d403074840305c0f46450020000b403010381d086c00e854810051801e51034100071054280d100d1001c0301e0041202a06911002511071905220081c2c440d20010900380000c084040c01d4400c00c0700004000e100004407952034607058400e1505819081c281 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 231150107 1250 231148857 231148891
    0xc030e1902090708041104091101030b0103020405090103170f03040308100b19080705070204021b060106080906040206160b0405060601111209210d050310091814010605180609 77
    0x10800c05140030f800c030424442c003140480c0c01c02881c2c0900042c910703000341042044015500301104500440c0020b40d0110346480d900710a20751080c0211810b64078060140c000300d92840d6203242008007440340c0d170b90304c0303082c1801080c901c20500c60080d07001e00e019544012050402d440170a0070160142e1208400e82e0f42088030b01482d10001c0710410000c40c02d0b081030401940c1d010403c1c0c030307a4070078844001c3d40319100140308030803598040a9000d07014074000440e0b410f680c0311501507800003000e48803085942c1c00000001c0051901c80020704100f8810b440c040d03c0c0304060b5461307102d0214241c9d01107509400000c00c020030fa591112032080350109190040805800d0300a00c4600d134030034101e031396015443d00348035144d100c0003801c6c1021991101008840b0503642c0c60700300400f1138200752220080c403c0545d0002070000494000c003a0030501c1052401c00c0c08905550701447c640340035000b42d5507552614800a019035940a0751071100e005c00030a50b1440c41c08100b0042c20b210003c054181b04100000307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 231151357 1250 231150107 231150109
    0x90b0f070c110a05060409060311030d1202030c12040602070b07030b010f1d0a080706081f091e0f09142e090b01140f042f0c010c030e1902 61
    0x1080408039002032500c0000c2c00060302007480c0d02d46540040c0c2d04070702e001400080314402c0754890000c4074000c0708841101c8180408050302d07290076907a100d0005170040c4044050345403541c021030b00a05d00e240ca4038540b010038103000390340501c215010f682d0158081014804d00006926051380802a86030410020103503000107050095101c030801c040140700e03e010a01200e545202d24554440280b20180c0c0c2da0340c69000f941d81e207205008210005691402040f0407009020760884110a10040c0140c12400c0041c2c0300000c0040d0201070402c840286201461584240724500461072a039030041110051800c00d8541c2c4c0d0445401401c0c103500059041e1031010b424012820004013101c921009240c251400c50f010f00908040502512003001c000201c000410692025550054923100415952541000101c03615012848242d141151172401403040f628000d030030035151504d00c1030500c0c42c0950100d08451307503250b0900c04290b0361410b0000c031490801030481841d542c1c0c1190740110394158 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 231152607 1250 231151357 231151367
    0x50903060709031b03080427051f0807151d040c181d01060302070203120a080f0a091a06010504090207060501050117100b07111c02190e01030f03020f030d090b0f07 72
    0x80700e032810581e2310a01048c00141d03200c11601d41c4260310340701440142044100504e90b00e40841c1d032103c2c607516892001034118004103080382280d22807400309924182801c025190704401030071000e080d95a14440341516030f0355204043d50014a60358402010400e4040c0000c0702da02900901c0e2402160800140419080801d0505645243c40c0141e200c0c2803c2c404649001085c0740741c031031880c03004a44c1c2c6c0030541d80f0900e058401d80260154030355603151941b01d0030444044030320142401041c102002480c40024889607003016062411500d030554448034035040340c01031441103030842c0d102d0004006541c0d00103002c1c094540542031619050504101c080c40d00e140e284100d40c2c240502103034980521450000703404c03118101410168583d00d111040f45612007002c4802ca104d50034241c855039230911142a501300790382c1d00d01c0c80746003581d00715100d09214030307109070044007103104500b1100e10b80402400900031005040c1c03404a074251300e601c0d00c1003801c8001408040340030503040030010343c25801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 231153857 1250 231152607 231152609
    0x30203030706020d151e1703090d1506230a0b030f060103060f030605041505010f06080c0c0f0304090e0a0201140c0a05010e0d0e041a01050a050903060709031b030804 73
    0x542e00503078881e03203003020340003034241801d502c01030354a008030000348110481c4121200030700501194456503203d05100c241001c800006203916801072080380314501b030100d0481e54550240006030080803c07000881c1c1906e4031600000c0d070320408000040c510b0012151039144a11080325001845410074084c0807060100509506510500740301142d1107900991010b0060403003919115000760b180d08211024080c141c80885000648203c1811401070cd8400d070790682e5000c9070040402480c11030201c0701034074050f241555090040240c01c60300903041116075035004100003d540c9461070300c3c400c1c004850048660b00110740290b21031400503a400303c1880c46113030790b04003465261840c51100c03920700500d07001c00419562800300d0000c0300140010f402480341865648105900000f0b2041c8801d6810901d40350248400180d468045503000d4006001c201c030311481c0080c10016584006031030040300780c400070003144040c00c080c802d00070a10a43da2800c0c0d17800402582d864038558400d1160710903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 231155107 1250 231153857 231153863
    0x70201080403050a0509030703110102060a090b0c0f090d0501151205030a0309030c02030a0506061c02090c03040224040609080c0a0b0903010906060f0e0709140f040905060906010f0b040302030307 86
    0x20009013040340301e014000b43e4021502c040e0403180a6620791030030a00c03c0d0030310b0406602605c035681c00284011460301a11030042c6d800311f50256551038145841d122504007104c503115803130045c840802180c07103988807415194054400400c1d03010090145040308070301504030643c034070b00b286908400308000008840107103c1c40c2c030380003034043c1035824104c2d80004408002981802480801c070103008000036424010201280c0d403001d00c0100c4801c02060281ca504025005680c1d080081e140e141c4210196038458009042d84d8a4005000d020480142842c080940002400304007171184661254800b00036007031800080034a007ca0301c00040d01140944a4222041ea0010303d24040707450a4004074182a40f002c0103001d25621404160340303a403094007034541044003260000b43c0c0c0398070076842d80003246c200c0c00000d13402800980500100030b030300c64a441d820035141d04423600025420002c00b40320b42d030310030090941e65050406c030103030984040e40240120401808140090b9501204580300140c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 231156357 1250 231155107 231155117
    0xb1203031f0b1b0106060912020f010c0b1602150609060907120606020304150206010f0e09070308030a09020a08010c2007050a180e0a0809040c140a020705090c070201080403 76
    0x11a00450700c1c0c0081950300940c49007400810707880c0394990303070409a0b144150100b00a0000d251034900c11240d0105a118422052401c005048007508001c266040e049006140c5140c003100075449020580909503a80481c440031003146641f06a03060200c0d4640e80c2c415074011441342031002c00114043e401505c0c1511565642003c0360b1b8250048074144154410414284452541d407040a0340703e4101e4495100403440d4040c81d00400c40c40822080e05071151280304245031400c041070320b000c1c1c2c10700400814503889220004000300c2c07030b000041e51141c28168030205070301c0454418410380c00340c0b503405462030360b0400400c000c51907040382035000c1611030150760808001101241c5480c0241079800650490542d91004c03c21a8400c071540400300424030b018003d40c0d079400c000c0d0355101902c503c02782140009018402d050710700b0b5003041a41425030301c0c000e4544005858280241d83c0b2082c3e4010159101102c10407207410840101c5a11040b05007280e410400c142d000071782809001003004041007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 231157607 1250 231156357 231156391
    0x80309011b0201060311090c0a0c1502120a0e01050411010c020f040e0c0a060e010210020901111b040b06040b0f0714060103050312180c01030b040906021603030b120303 74
    0x4002580500003080d8001c0c4110a15692000043d00030001400140e4044400d01c008040070700740705000c240a560011165480c02840c2031048514040100040300d0344c0c0110002c40d110442c40d40040c1a0140080300b0a00450500729601c104031002601c01c0c04260b410a000c00000c15109012040034840a00b0907000410151000403007a110589100d80d105280c2119900010000036140008004c1a22104403554a4070010b61324241304111460041e07101450004000d89240c0203400c0320103040c10500b062000d45038415040c84115494440803101680243c4403030322b440d00442c05085015680c00e890b0904009150005e40b1813084400702c07100c1e0001c0c000007007042260170305070101e801c14161070065840e85001a03ea5001c600c03606072104020000c1620344c82078070a50f0103e031340d824004004801d88100158081c041d10a25079034020390b101c003550003180c000d0000300015140c031070340e80c07419040c1e07840c003d0300b00d0315030001c000c0c014807243c81403948038203001040b29004940300100d50148 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 231158857 1250 231157607 231157621
    0x13020d1704152303180a0b090124060e0103091a19150308070804050a080c0102161809050c0a03140d0207060c0f05010902060a08040309051207090e0f0d05070308010e01030f0803 78
    0x403c400814045c0c0b4401d001c211b105101038030307121320301503000a0004d114440c00d0302c03c1840e0f480300543c00101280078176002003101502511400855640605000c1001034107900e0f00310284806203000e524542d4448208410040002c42109031841002c40030010740003403052070540c5009901006101850002d4074030240180700041c2d8009202c0213050103c425114800382d0740f142070415980340540b24841c40f0508041e581342c1c402c8261204d811ba00507a929081e1404809070060240941b40f500903080c0800c041c0d1030300000c05000c0c44c020740002c1407a5100b0700000c2c0c6482e0b13070010040d04540004c40140700b01070740402c2d5000815001213031051058400d0400900502c03100d0780081d8400340c0095121081500704040701c1c441c81c003030b4880c0c41c0c20660b0381c4144000d080d804802d420258200403028003010310382d507100d00155110b0030300311402c540380515075a1511400146c40400b00d480442c01c902003543c0408142e0240201d1404030390b0651456540143c40c886503600140302d410044001215 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 231160107 1250 231158857 231158881
    0x1d0a06051803070f0b0a11060f04081606060602160f0e0601110f060708010e060901211b120c080705060403080901052802010c02011413020d1704152303 67
    0x14258000f00d4400301645e49280508552100c113010001c50000031100102c00004aa9507120f007000b0011020560744950701c0f00710541c843c560308040b840c607843d0010f011810502c9450080d0903241c00804502d824600415980301c881d5100d02c0304881300700c600f400154000c030b4445403c030000b8201510761184403072a25050102d40e41200e4000d1040e681000081036118515031304031550f1071580f1105846e000d092004d415001d014000d000701c000030078403c041d02c9070010880050300500d0f2a40b2400710703901c2035070700102c4c0c5607000101c04005a50000c05121500202c440102140070040c01c80b54500b0b8049805401148009030a5440c04208103030641d00071400c4800b00d8007001080e0f96003107141400201a120400e44c0c0d03030015803a202c0c07424800350051091400c00b649803000510990740310101d50002c00c060300c2007280c2258912150310005a88200010140400e0310f882d02e031964208000d25044000e20741010040103c9050f000740040000740400200d665820445942c81e903d03048640303c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 231161357 1250 231160107 231160109
    0xf090903070b0c090a061e081f0305060a18030c02130b030a0309090f021e07030306080307060509060705270109080a0305070c06080c032a03071d0a0605180307 70
    0x21804101080107a441c2d4100d0051030501c1c001c48400005e2a201e0301c0403604c0d0396600380c540415004c41c0b10810748440c010862943d00c00d0303144800d200c0103906c0030350b0000b401035030368801c0301c040d0700c07000c00c0c414032076800c1c020381181c0030310301c030301021250389070340340184940480c9d039029002da103810307502400800854000b03180c0240054102d5038402d50b1403030020b100e2b4241d480389014140c80c01c01c4950302a14a4001c40710640416500042e1842401040c110701d83d0007800200c00f03050755028006004213060000d0400c840c012500080d046c03502d82211824982d00500150400c00c0402004482c510204001c851a44500c182d2a000d4207990780140c2d803013070060b00070704018859005041e04060b0711100034011030b485039400e15480c0380d48000c00d80d560f80045e280314846c20000e00024008240781484040c0000101030f802d0960116844240d0030380e88150b60f1480020148820300b0b60301e640e848082051440107403600807a091070642c0050150160000d24072181101c56180c000565081103010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 231162607 1250 231161357 231161363
    0x1b040e0a0b090c030402090903030c22050405010609170304060804060902120f03041e0506070213021606060e0601021219020f070b09090c040506070803040218010f050f0f0f09090307 80
    0x291509003c3c1d165a0340d03400460b412071044024030001009501d0110640b402010b041a595060040c46005c031410004001c126420710800500002080d503114001d090080c480c5494241419040c601080000940070311041d81d2644100010030030513070f2000003103500c10341107000001c50b6150b03803000544425500310b80d01c00321710030611015892540400100100d8140050711a52075040c0c440b1010130080034420386030701c44401d000c140b000d030518004441c0142c4d8003250042c5842d0311070383c110f040403110100541e007613075a030700b018801d4169000c603480d0003000034001000200f4040445096510801d42e444c0c0b6100c0381009000500d6000b04030140c0542003440039180004d442d000317071008903004406082d10600301c4c8400714400344540ca0440d000c2e80c0c40508224504003454445100b154000b43c0700702e800ca01200c2c0c09500c1d41d218401c11501800d0071111501d40540b0f48800c0140001e41440707901e209100d50b4650303407007940c0c4908401d40015000e94421400d0b9560b107104506600a200c2e0203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 231163857 1250 231162607 231162619
    0x1418030c0111090f03070e040f14010f06030b06061611010e0916080f07050a030b0a18050405010f0b030312070e0316030c091413080f040305060a051b040e0a0b 70
    0x40384015604030103403d402c00300399040100045001d04169555850384920b1003815003101c003141c0401c510007081c0d8510b500840d05003402044a03082c0908503000011140301b260340d140e000323108014008800e5500144129500380c00c0548a03107540f43d40409041d4010208054400c1c2400c0e43d0b4062000d80d81001c00050885120f441d09501054020800e108030300001802c03a0300203441040381e0400c6901418491740d4690801d41500c8050b002004030204840d070100204000240481c43d41c6400c060700c904601e004106802c0170b1030480d00350396604417a031100c0c44c00d1003098509510b001003a5203007400040e8100703519072111002650f4000300840d060ba014080c0940c1c100c1c014030844038100031a445821280041036450170b10700105c4240135182c0c18032100000215200c0c8580d0020a01414051030b8000c0c908820360210004641c0140d0080307480f41c00c80000c11140f00e042d8490b4170361101d52000b083e10b040200c1404d044a5214031b000340485018110045100d8080c1a8882440c83e50080d1031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 231165107 1250 231163857 231163871
    0xc040b0a1809090809040f060303020a141603050a0308060103050105030307020f0a0506030f04050d05030c030123060a020f0f030a020a030f03060504050a0912030c0806150706051f091418030c01 85
    0x115000d42d600905d020341c010350814028448104540c03250404503030309580505000d1030550b50754005041d40781c118a400b0b114003024001400640354512004612a100600c0481caa80c54050640f40c030051a00d414146071500401068401000b02d41003164116042d803245551080014400c111940186410000210070000310300054410580a1809402105c00140420f0b0701207a42e444119248030307018a060004114000c141c028101d070043c0034482102d4021500301c081381031500900a4100140d110001c9100ca400c000d2211282050b1440041d500d03000f00c401c80a941c0b032038041802820042000907410545110b03030700940c0070305801403042c040390034402c158070060f04000302c01b9195039001c0d0a030b02c5c1001d4001e2140f00310317441d010b4646402c159144010000c141d003880c140e54400741c40401000c000101544a418403079405102049080091191403010307030034182d001035040602e07100d01074450281000580d540540000980c1c5112800d107510f15040d030054220080c550741c20144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 231166357 1250 231165107 231165113
    0x7210303110309280c12060212070e0109050901080a240609020a0e0d020a0501111e01060305160f0e0c0d1407030f060b070605060307050a030c050301050c040b0a180909 74
    0x40c01d4403421148802110441008444c50708500000220080950200020400c480d818011044044c00d0003a00c00506042007203d010700060002c4800c0340019140c4240c0600d50341e040344a042c040c060075503002c900c0398100688569034000d203017006044000e08403201c95a048001340c040c0141c0003d03000900240f03540c1d18140380070b508403042e000c0106002e142082c0d02c5003000d040c9031103280e8000b02500041850040156000c026504194a040c0100c402e0f00c2505030701d010517952126071000001030b26508d14107019003400c8640d007840055040684042041310401440b4606842a401c85551180c03550b207640421172160300700703410b00d041c205000321008600440041c1c2c8126090744042c0400d040718440582103031401c1c002c14600381410b0144001141c2694082980981d01a0403906116203400026820041c5940211044901c042c401e200504081c081c09030058444c3d24128101820300c00c5224690143e070503028100940f01c00141a0040d030303006000f0041200d400100100c0c61241 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 231167607 1250 231166357 231166363
    0x503030a0809120702010f030e03090604081513080a1416050607031109010203040b090f0301020f0a020d020703110d050a210908032b0609060b12070207210303110309 73
    0x640c0c203a5a4002c103680249445450411078404c203034147d40c0c80d00c0324502140c1c107030300504c04140700603c1880b09100d9900d1a443e00030007000500413080040ca03520040c04c94508031a90010080c0c5201000089160009602c3c9819201e00b50400d007040030441c40c110070140302ea405105100c003080030041d003206080c4030300481c8450048056075000d04c03200381c10520000180c8240c020b80d5005900c10081040050b007008050849a50020440e000da034800344000383c26600b0140203418a1040003914180c603940401c0032034403940300c60001d0708078a45580c0b10850200c1200e400140981e14402848c0100901484050b00c1298003040007900070100780b0001110b07846140c00400802c245a4000c5410500002a5062003610a0160000011003450000003c0d0740850f0300321126200c010104900070b282c0560000751180702491600c640c03060800c030700d02c001c01410110654009990900007001c101c030007202c200c036807001c2880c00d030304503450114018265101960710488011050080c03490001c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 231168857 1250 231167607 231167611
    0x20315011d010501052d0703030510120c2601050901050717150d020d050a1109130317090708011e0501170c1926101a190503030a08 58
    0x900c400d0740004850100985090000307001d020f001c44e100380049001c40c01c54208441ca908042c42074524600e81044054115401c40380046000c20b80711400c012200d0300e50311992005002c0c958180381114242e032290520000300f4058a22400c50840303001c5005401c4501201007090b54900030800f9280c80f40300d03d8020a400c0c0ca081000903c902c4001c86ca0944400f00d13540074650700b458802c0c206515200300941d41040d004126000442d550180021440c05e010841d007944c003030041d4034030761010f000802c00300c08401002080300c100c150560001081e881020384d206d5511210000c0101e454100395103190031010740c070220340ca40c201821084402520301c02800c85184511042c07010f030340c0750b100b0b540303504040e0880308456522103212001d41e8904604d801c801203900d0030010074210b07201c0d0000d481801c4590180304446e0981180c104845030b0412108074521804881000415201c0e4000481084074100c0284642a11000b03400b82c41007a601c0c0000078007004044954400500341d010b4145502 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 231170107 1250 231168857 231168869
    0x120c16060b06451c02030a0804030c0501080106030e061b0408121908090a12090b04081b01080613052d040b0f07050f070302010b0a0f030b06031b12030702031501 71
    0xc118100340e5103d0086140c07041e0080024000c1004800040c400b00004c50b0244080e40e01d881950601400710b80b03040020070295000340301003c412420080090b06010040e8400c1c81018500a00c07600c5458001c5807442e0004d20751405032400c80201208095140543e810a042d02e0040c15038844c0801258801007580044100c184d400685e4044810399100f01c0445800c1c1294001e00805030000d080c821540402800710b0038a44001070301c03100407a070190000e42214410f907200c0d001c2c001901044000151f1910400d180c0035407285404404540482014450443d0141c4c07031b5408a01207054020b0100b00c2140c504828110100501c561484c034413034141c5040d2052150040800e52980b2148441445030965445440c07070426680c186410941c4451030a800319540c8043d61605c980d12540c083c4010318020403410314080c03e44c2000303582070f00e01038180743c802d522034040c0030a580440c40707a01480240c101c45414940e0711070058103040d485030500003545405154111190643c1d1003a0351416242 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 231171357 1250 231170107 231170197
    0x30a140c0910080a12120f06060210200a0c05030a020a0c0b03040302030a08060f1f030e011a010311041a070c140108040210091802120c16060b06 64
    0x403681600300c5401490f004040e46031300602e4400002ca10a200c20914442003464540840315043c181030040350344024405004544840301080415410040e8083c6400209030030460200509801d10402000310018840b506020402d0400340d03010340844030105400c00d00f902d0b501d200c80d400c001d4542c851040100e450b000c800002003181d181d200b003564460b83e40354006514140c052102583c0803030000300f100d640820920309619a580311300c00da5502e8070301c04504c40c04616045400184c1030b03800480c617001b000da2501049850890760400c1901d4007000a00300040c1d49907205410203c03a20841d041884c4202d00703401030100e903800c020000e0034080c1c024944880c4154841040501440d007400140d80002c0140001c42e0241c42c1409400008100300c1c200001c40c241e40d08800300d00594000d40380c05115034007244100d800710900440c9a8401107038103200d13162407070751715410850400100011b040d040d41c8000040240e100c0300115424988020340c101c0a2613207a00c6103070340481e50700d1900b0360131b01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 231172607 1250 231171357 231171361
    0x90f050f09030a0c030e0a051309060b0105120f04290702160b0d050c190e0a0807050d060f0b12010b1801050a0308132615010509070806030a140c09 65
    0x2040401070790f01c0703085640e44600e540303005500c044444807150f500c0543d101d14407080005140d500c10204034220800d02d600030030345000314103150f002c5807255170b045418040c1c10401c3e4445528449d5000d9840940b002d0340791520707184d50034050344d2040f81a03420150300094075030341c00d2801c80c0400c5042c0305036029401c840005000500004030010f481c8928080c0c40d0b000d00240c142490960040703540b041c80201001d041003d616192600085082940343c00710f0b04401d9145110b0a000b00f140000d454401c1c010101c0624100228a0070a110080545000c1c0d40e07240d42014400c454000c4a983c10005019110060000c44c2140c000d1100f08440da12030000c2d02282c8002c40000141d01e4104c890017400c0c200c80c0c514580740c68011341d1003060301c1c0a205042983c081010b40103103510005030501911200d42d00300b0720041451404c04207800100c1c61009440042000380e5608482030381c0326400780b42c00440c6881e80c00210703181c42a0716200503c5040341c06071200310038500042c0c0301100340b41251028225 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 231173857 1250 231172607 231172621
    0x9050a1a0604091104090501110307030b040b0303040e190204080d0f11010b1f090e0a020301030b09073c08100b060412030f0c08040806041118010e10090f050f 70
    0x115440f032002814034581d4407065000386403580c06996114018000490441d40942603422940d00c2103840c100800d0742c50503a5252030030b0074401d0a054030010b0700210b00d8181004140d51070220f004090385607030440f46040221580e51070701640d0042521508031001c20060380f2000d40300c0c0c6801e54070750b00082d8052041d60150302d0140580e81507100701500c2a20080c001600a02d80b610000405d0380521044075000a0f00613503110702984074100380440141c8a5065183c9a00d48100160003104141e00c0004240204188040025400b003651096028400001d9902c0c10707400c60306100c5c01158415461001501540c045070520310000710301002c22400b0300000c00c10400d4021070040240303244048400000003070190b441d401039080e19040c084000e14080d69050f0980e4440d0700302c0b00607a0400c5091104200c00c07803240c0082d00700c04590244501e5440d00340300c0e1000c0414410400c03002400700201c0c01d03025105c7c0040b0054011000284070701032540d01d10701c000d42419101c0303003003a01d0050700003000c0c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 231175107 1250 231173857 231173861
    0x415050705120601080a060b0409090c151b1112010912030908030105040c0201021b031903020301140411040503011104050901050a060206010303050921010e060708090a02010305090109050a1a0604 86
    0x80e901d0501801802c944486004540c0104000c002121003595445c0101d640048403025100424070a5004200b007001d625103081603401d41d034094410400048e868840140c4c009083c800003482c400c40e440100c1c8024100011101e2a01092540010f41003c14240000e410341000c0e00b0340e4010316211000c90400d031400c5084440c0000c024007460400e00041c1300501d0302d5080401040e030700c0d200150914880e002c581641c0c519030b038003401465100003004420703c44100d40090701d20105040c00c40c2035605d800300d2180c203142110810ba2003599100403005040c5103880039940a000c001e00200b0030079600c424000102c2d031081c0105841100d010b0000102c514003000d0380004e885081d4081c0ca8140d00c0c40e50142c4854018180c0c4540c0114148480c96071081215900e01144038048000300c0c1001c42c0c440442c9c20f240c0007920400411149004000e0010782c00a10000425828600011140e445100b81c42c018140c0c0500280b542c012541030109022014980c00040c02c44010300500030784490b020801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 231176357 1250 231175107 231175117
    0x80406020102072a050d0609060e030d0606090b0f13080118050c0603010323011107080301090b12280b011706130309030605251809090b27060415050705 67
    0x461383c46a0b03806010905204000e50400da110309000b003800029a51003505407440450342c0f00b01c1d940b000c2055642c040d81c90048000900e42c50910480c090f0030503010804601c44d09003004200080060b20030300300020301d19050001c020800080117000c07103405045810200510090301d09120f038812500f103528140d0126412203a00c40141c4602072903048030902011402c81025207a956a0082c810b000f14004004199051080742d180307a1700e41c141601d45080340c10701402c0c14002c540258450003c407500207070450100540e80b50315030403072610020300030949400d508001c00004000b0b000103035038948203500071451079030b5a003a41d03525a180300d0314004000c02a1400b50000f031101d03c041003c603030960b12035a005044c81942100001c80f0b80d0300c01c415182c0e9080705a00080d01d1111032442d0000c45582c45019041140050040800c0303a03d5009012030701078070f4821100d5140055011240d000b4550b000042c08107802d41d449403801d800c01464460003040c0c0380704e030141841c00148440d846003084507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 231177607 1250 231176357 231176423
    0x1b180a02031e0f010630020a140f0304110307031205090907030b090705130b0c0c010908151302040207020d030c0c120807080d090f0606030210030203040f0b09011517070e0f07051608040602010207 86
    0x3829652035482d0305c014001cdd1501050b03054094907002101003903991003000500c182c6078a4540c0d648502c00c013030003030584004000004040c5440c0c62107900d540c882c1c0020f50031002a01d00161148100740c1c4a40100810350320200d812040003507515080301c0b010824140c03002d001d0301c5003c40550b89100e100c3e240c2c0405410300c5902d150400001301c14503210248000d260380080c2006081c44481c0c3d0200c0c0004d41124400d4011031851041c0000b00410008100058005121800801c1900b5900c0ca180760148180051030702102140412251603164024103c0d0780e0800e1140103200d00506001c0c00829043c003085c0d0007401001c4240101a010740200d030301496000e0725102980e1003940b6403068410024212484039500c4a06030102000c8026480c0040c241d00c051b6155107031a0782070110301c2e0407401ea00401c0b8603107000d030401008140200b84e065210040c0c0c1001c966030400b600400c1d035500031b5014018420403001c1004501d40e0340c15409000000c0c0704030314100404020b64865001141d1010307140c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 231178857 1250 231177607 231177637
    0x50a050c04060f0e13050603011a100c0f0b010b031f03031e0306030204050c0903100b0f1c0203030a050d051302031b180a02031e0f010630020a14 64
    0x1000514030074100f22651044924092240311450000110005003a42180080940382c40070f0203070514007072040d40a06051001c21000c008860004540820011880c2009021130b40081c10140044142118500743c1c0c041c00040e000d60311903030b030401d081d002515042510000210030303500454180c80340742c081e2601501d503068005074103410366a481403c031000320101030702c1e54400130040c1c40710301801c1d020785802c40342c06032144a940c050500e03003011145124038481c20304a440b81d06456118090b08503040541e4000040301041c038040f4451014210002e415100000e07040700c1c0954031402904d448241d000c028800d44c1c030380c21500200ca41811501a50580151000d80c50302c0c40c0708200101e1201e00030342440d40c03502c00c0c6c0d1808a000070007100c0c843d03195500001008080010a003003034180381010000420281054080c0c10040c94050064809110444030340e000c9100c1500da4007002d03211007084c0c0c1c070300010301280d0500281d01311001030000300d250f510950904600c22410303111910004488 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 231180107 1250 231178857 231178859
    0x9050d0804020a180f06080d18031505040321020405010e010809060708060a0315090b0f041505060607021c030828020904230609060409050a1205090307030c0306050a050c04 76
    0xd100070040c444c1d04003e000c540e4500000120780d4031402088010b04219018158180540d003028100c01e40b01c58009050200b403480500024007100300024518850b0071000585544905d029141940710100c007602948201c41012105026074000f0b1081d02d2007039907460b0b0031a84070001502d90341020f580d41c0f07030140c008000254040c0c1c0300d110110790040c0c0050100c2c00f02c59807500d9044140101c8850702d1805a1100d00200a0185410761580c0152208120316811720b016101d0002000100b50801c4000d81c4a2000c01d032507654010a507104d0580050464000c06c07204481c0e98100202c6000481c0800c8144000450541070700780c0b0001380d2070301500d07404130305600228440000d5029010b210362050380d030046c0c100391030090801800380c811510f030b1074140346c18008100700440c480100185d01c5241484508030005a01260300c4010030303808000d000348003280503003d881740e019a444194040c403c0020000c203103ea0400403104a0b800384404104c1070b04e50500100c1034400444044102401c1000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 231181357 1250 231180107 231180119
    0x30803070c06061809060e0703030914040f14100e10050103050c0f04030c0e06041b030209040605131406030606100f02030d0612060b0a06020c0f03010e03070609050d0804020a 77
    0x30820729126000028102c0e4071384030040c0c00a09201d00c980c1040750349901d590304001180c4a0040700510f41c6005002c120310b90f5a00800e55041c5004241264201d00042d0906440f2901300305082d41000b00240600d440d070031a100082901241e03408400c13002c0c40c200248151585142c1400342800b5003400440e18103220064018150142c56426044030400c40d00d204002600c2c06231001c0d612450315082440e1402d16000c0340c20002034a82d5104500c1c203c258100300358035403115009941141030140c0c450b4110400100245825400207800070300a5504000b8407841354003441c071380300d11904904c0b082c0d1903030024103036210400c07111a40c024520f03080003100c01d4080c0a00890108542c81142c2c5095100c2d417214090f0b0398554441d00c4010300940022040080758043c0150030b12007078481d02d40040c41c00100039036801115004c58000c02c00d5208804007501c003908240400003500044035960381c0280703001c20051080210944042c061421f0741d20b2001d20030754901d03005940040c003495060703003000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 231182607 1250 231181357 231181367
    0x3140c01211d0109080304211e05070c08030a1701050a06050c0a0c061d030d080a0b180f1b030705040515070b040b0115141603030209060310090c030603080307 70
    0x48003501002c5000064007800c1c0809000c1c126040b07200f0180750703880e4181031030305040401c03201600c109840c040414440b8103541c0400e01c0e614014400840001510780d03503030103585030b00c1841c0018200b20890030010808610000c0100700c0c3c10308503034600740303100704440e0000c05103842801440c2c1d002d600a5410400c95100780081d00d00d00042d0380a0b0740f03001c038680c0d030340710b0312514280c0c000740104035400305010555044840d5000501d0082d030160903090305010b40200380c60402824079034200c3ea50507034803400380c42e40042000d18810f030702030215942c2848688841244000c46ea40c1c040c11403441091282e840540c0b007507a0040d000d41d00c80c141014148420444420104001c180182c4000d00200c008100c810740007030f000354050507117102c080d414007920040d500d0805541c5010710001c021622100c0d0203032001c50f00c22044004540c4a040041e18080f40a4400d0f41c4200d90720010100078000c10070543d4100300f040f1807101c0010000360f0b600030303c1902a1081071102815800003030002a80c0f641c003403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 231183857 1250 231182607 231182621
    0x906051315051605010e0111071505090c03030d050a06090b06040b07080702040c0503040203010b0427080c16140906010927020a020102070b0108010612030f020f060103140c0121 78
    0x6402c01c1d03801e100d21040d281c519a0741c0400305441030b0791212081c0440301e40030b00c65118124451078095203401d1150312440c41c010b4000741185d246581c0c50300000e2013054140720102c420344d0000c06603a0f41b000413281c40c002814045d02d4603400180382071000600042d0910492601c08406401541401c0c0b9054a10880d03811540e815205000304100389401a40c543c0720300c08449042b502c4d041e40700e05041c018036007110715400c010303802030f440c0c0002507584000744210308009940b1200c40d03801580315460b105d0114091910049014444c2911010307800203001c1c0548196103030102001e03c3d010190f0b0410a042c80f0641328180131a1101c40c00b405541102c901200b03504c610490100000c0c001943e0240403039020310f4580f8010303540442d4210420009005803401042e0400090040b0f07420050412013000c0e04040c02028003e525080070f5000b4001c0c130a030041421130030251505903950307041100d005c5400795000034850080003180329556000301031058010b040480b42d00d10058000008900030206 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 231185107 1250 231183857 231183899
    0x6090108150a0b031f0b0a0b0d020c0109021306030314030c0d0b06070506072f0705010e0310061203090e0f01090c0228020301060501080f0c070303090f1209060513 72
    0x1c880018610f030f01c040010700c2036117404100d401c803008850001d190480c0c02c1c60711200d04c96041c00c00d04101d02030820054481d03140d5050300059507040d010300c509005054045c8001e411005209520b00201a254032181c101c90017a11540301c808100e81220703009110840d2080c110303d009104c1d0f001d042030241c0c000c6440c120302130101ea03e06500b648845290581c12030385280001c0300ca4203036201f240440414110200001d0502c8212986c02c2c8995503101d406c540681410400c0c010410791443d41c0c00c000301804501c210b00100f20041d2585011449102e1040f002c1d00814440f010014a140c481d05030580308141159015940d642480c90340b50240517514034000861140c3d0806c0d003803000c03074030100fa4020292601001c1d501d00030b03807060600791215584424184000031040045040510700752952021583c20003542c0e8580d645429002001407090107440002002e2110040200410340015140700e0f58440720310b05a9241d40440f5907101d03030500d607e0143c10501003004004800380560203c611 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 231186357 1250 231185107 231185111
    0xb0a091208040e07111615020d05070204230c040503161413110f0d06080706020a0b250512011e03060207060617070303030e0606010e090405100c0f0806090108150a 72
    0x1090441c2d11b030110200400340d03400b660711020411042003850840030103202d80054800324500013406422806195400b90041e0707141c0290100800304005890f42c4140c0c6501099010b08182d005c0030302503040380c000c050081c4611540c80c9200407540d422102100c07000b9200ca1038182d05401440302044085107004d4919072682070210f80041d00c20040c0c20094644040103480c1c6602c44400700a46d0b105074403401d1103800c480014424a07070b002ca80c0845080d00014079591a03204c059032409001c40740001c044503035140100714416641e00000900740340315000b03919078260340c946451022034031a030603e840e036a0b036142c481040045c20303640203021110300038540000c81c00d036207249107070700c081003c02007415940000805208050f0180301d0200004010001014103141c0680060840c60058110910680e50b400004041142c20020750310540b6039208203210070000000040c00a100c0d600c14000450a44000640355041815031141226503003002045c084100049444030781c2c8011300001d02440e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 231187607 1250 231186357 231186377
    0x509030f010204090b1f140a090b070606060e0f030606040905030909010e0f01151b02040213030b0610030e0c04020901110610260709051003020a0b0a091208040e07 72
    0x5034007072000c2d00003000700d00804102414003000b0800324803101a800c40d80ca401100f200b80e20a03520110b01d03840b1707140c8001e0301e40d542c52040109681c418541d52180101703120000b60201006460b1f00110211921a00d41440c40721181d41082200102100c115400d6805400040c00070b1a050300700b020014002e0094034503040341540480c0d907000090300a030404500700b100381b1020076105401a801004244d107140300c40d03410b00e06c0c0103045140700c4640410f280c2c048445031055581e6079049070686948420300030016076480c500913506600c100c404a1060032113156580c0d14038020b009501c0004031881c042c10444a02c042048000c2d0451340103035040002000590003081802c2004034000d2003041d0800400a1a1804000b5001410100f92942c04a0030b0440d210404000482d041600c01250004c00c4270350f035982220720348140c96840030b5801881682c1c0066051200780003072030340c50840c6c0d03282c91540d81c9860300c000d800e00401d070008103a4801040108078910500c03500c1f9400c8045890100303014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 231188857 1250 231187607 231187633
    0x33040504020403050703031403071b0201110312040c0515030402060d0e031b07140303030a0c21090204051e0f060a030807051e060108120c0304080d08010801050f1006050903 76
    0x20b0304079401c201e4481e800b401c001d0007455000420f140c0303c41d4507010550f00d14940000028143d4000c4002207a9001107101c0300021a03000c1c0340554640e0380e9041c11030751a03604102c01c188080303206660644d120288141c003c1040d0516054000c9403c505c02002859511107600740843e56010b0b151480350740b503aaa5075030710f01c850184001d218585c5d140308051503108100680702c6c00c1564507403141c1c0880740d2000003684661404000d40340d02100030680000d011402c00c006544145980c0b86d0989924800004040c1c1e6400552150024074000d41b4100041d50740d841d542061069041820890540071000103918a502c844c45d2030741c80000501a0741441342d03296207401564108200495041d008ad041c040c54082801503030040020000d0000c007040d5140c80c003010f8a89286403084000c501c80010150a045020421280100011011615504444c1d00000c040e00d50a006500c599420800466030520409110340c3c01a8640b000d800604c42c5490b90a0f01e040d40000f4103103405001798444c1d4112 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 231190107 1250 231188857 231188861
    0x212030406050f0c01023a06032d0b09150f0906040f030c0c0308090906010804110d0311030d0e1605030c01080a090c03150c03020304050303061009030c140f33040504 73
    0x1849544850300441f5950100110f980c49509000040b0030902d41035082020400d05000d40d50040e40c1c241900742c1ca80a101f5101110542e0042c01034280301507401480130700200001c0b001000034010b20150700e90b844101c104140c2440503a02d4850b03582c8001c0200d03012402e6145c10707030b00c2d042c8070382048046000d1980d02e01e040302032907900940f600d0b000403036550054140340501c254040000d00c1c00100d54609643e441d118801e540030440d0103550340308204420103001303101c41001103c40d9070842c2c0d00d40340c04480103c060a1011041205401808141014100c2d5808042c041e200700030050881d241c086001102d58103401012039030150b445003114000728800c0c0314407201445c003a000008007100300c4882001510102200142014410420040807441c08401c2d0ba030066000c032044941d0000e010070803244c04002d0b410103003000540740310008102d1040854807580400503147c40490b41e010400b000401166414007008a850500c41e8500398410001341c403113400c08441010381421b48a03008241 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 231191357 1250 231190107 231190147
    0x140414150a0b13021911030d1d0f0a03020c060703030f02031e010f050906040b21010504170a050d0e072601060506071208151201090212030406050f0c0102 68
    0x840c25035202101d442c68104102d900c40500c400d9082585801d01c400040c40f21581c0440102c2c00b0001c50203c5012a14424411904640ca0244042c402a244442c101d100124030a0348941d8a01c90388080c004c028078082620503c560300340d00544000000b0750280304183d03001c58000c80c00c250350b410707031980d00c2c145070305c095401103d50301404c07260410500010865500c2c1038021800d114021718080002c1d603140920151b100e8000da9000c24529000c4000c9240c40c1081c04514840005401c424010341310150320035845240034488088050341c0c0440312080e58800da092072400104104012124841c142d080044030a180d00c040319400c1e0380d900d031000e541d684004e40f042d401c4c40311149030201d911003d00031b1201a1104485280c581030f9260fa9545940100e13043d120180003051001421614241100e9213201002030805c403584030440032824000c001000c4200c1c0302d140d140c08080301c40c150000c16901035483c1500c13010f00c1c1a0304141440c81a421980c43c4c1d000943d02002400035807800000058 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 231192607 1250 231191357 231191371
    0xf030905100809120c0705010311040b03071101060603050f060103051e09070e0c0c0a1202210304050d030c120b0f040f02032e1a0c010912021014041415 67
    0xc541c109100504d05103500c01e9111840c3d900d0034080b581414402050071011510f00b400c1c00900402c10900840742805190700c02400741d00040100f0030b24036000400140740810b100000c005080e241d22090341161000da4103650014800e84c0054559402076000540140c07800303442e000b00c02102c0c000583c080004407a101225040f07030400300005c038400144650050074000002d07041021000070740f950b4082184000c0c08c40004005034020660084c0190080c207034203041054a900c1f000480c2d058141c0c002e8604a0b614030400380c000401910a1003900c0c086110740d51000030103020b4560071005081d811740d9030b41c0d100322004d0705942d0540d01c40c440c1760584d81480700c0160b101c1c5402961907000c0d203100803076100c40d0545a001c0a003110608035400041d00c4141da009090180500c1c141ca400303002c0c180410215629013065582803001c2007070589030f80310360ba600300c13040f03145004c400b41c0c15600440560300c40c00c2c910402040002e8020708500002c0c138841d07000c4480d2141c0304011078603003020681e428 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 231193857 1250 231192607 231192617
    0x14010c1e05031903330e040302030a091e050f03031209072112180b0a0c0c09090507050d14060f0f0705270406080703110405090703050a0f03090510 65
    0x90514141c03c0801d5a203a00c00c5400c2c00c005d110040c1c0ba6010481000b0801101da032134880310350b041d82002242c1d40c2c2c0301512005101860518207441d001e5540e910803401d12010400320381e030010342c07008040c0600a111600802c0400114502414001103a209042c4958180000d004000020784005c0806100d01d14550080070700524020715038411018900402c160b1800b29001e80d0041545e82c14a00b1101d00e01d1700e0141c8100b00c0440040c03512400507003142041e544002113110740513500001444c0424050303c00034010704e5449a03c402241d2040702c00030f00517082004104601d03c2d0111420550342d024115101d0752009030000765040640444100380c04440c0c920500c100c440507a5207080d4401c0d0346085c950b241015607401ba85841c842c4121200703920074400c6c09980c0540365a00301c18020f00440e4102c0703038455100d1400000303130134081c410b0500a0b850400081e084110004070101100d41102c040c0c000b0514640f182c01c5040c0d16440c1c240e09024202c0300005243e2200c0048416000480c1d0310 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 231195107 1250 231193857 231193867
    0x2c01110a0306031101050f03160903151b03020a0c02090406141306050928020f0a090b010810030c0e070507120305070e100e0f1302040b19080114010c1e0503 69
    0x20000c050b40f003134140281000b4091044221400c06031084a8011010b581c051400704248039040f1506407494000406101300c00203072100d54407081d00aa99001900a03114410541e840411002c82c00341c5441200055940c103200e001500304100b045810038007901c00810303070b40c07c064480c1300c2c0d82c40203132581d00c104c2e044205034400740446403040d20703041b1428801400d1898802403540e049201001c02034514642c2d020100000c641d1403d10759914032a01605990409955411540c002c04520041c3c2e0f01040300d00f00010300d0121015102415268000c800901d00380c10038200e0301324404010148400e00c5400c0003101c0120f1449810300d08406419078001c19070749042e28008090011102c090741c041e04c041041600103c2e00400c1c0d0b103021007001d442c0d00081f210000c0000c2c00c1404034110001d022440000e000c43d0b190b940c00002e11f280c400c10440004019034010049a00d140c0910400c2043c804110036442258464481404000e000b550301c1580c000800100070010030498104440351f52000403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 231196357 1250 231195107 231195113
    0x10c06290109090203010501120c0309020306042f1003020f0403050307050307031704170903120c16060206100b07060b041b031a01091202011106040b04020406092c01110a030603 78
    0x440d01603d800401541154075020010b0014609076001d400410f842c0e0f41c0c2c1c04081442640034107022900202101d149040600b0013085500905d820b1443c400300c82d088000d5646429485040050300140040e00b6820904a0440007500a200f40d01030420301008004007040c002c0025040d10b90050b0b001e95510045403801a083c000301415034011080c0340c404202c0070900c9520100b138040c41c60407080756070b840110300003802c010500459203402000442d941c40015800185000344419801c420144a62514000d9030f490404403442d80880c102c164050040d40070b480050031a50307201e03c00203d0481100b800150658030302c00e03241503a22540aa03201e59135070741402218441d920101c0702500411007000001d000203401d010f030000004041c90001c023164820904052040d03004e2040c0d903054186442c0c000a400700548081c0d00c101c0c1402000305070521213110300c0361100043e01d05078540c00303441c091400b9001e010018081c1c2c5556078034085460f60184000034444001c041e40c0c0000c0036401e5103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 231197607 1250 231196357 231196367
    0x60f06090905030a0e0f1305160e1c02130608010507020d09120305130902030c04140a150e010306093207020604030c0f080f03070206160e010c062901 66
    0xa48200c0305030307060000c100c000c41c101000704d9483c601d0b03601d007106030441c80d1808500140a80f51282c0d4200846a0b200811950381f40c3c000c500451030300590028250400d86e0031907518003000415a0310128903203094450f03280300409c1c804d08070710240c81180880c000d0700c02035080701c04070342c4140440e03511901008200c99051001080c1588a418031171050340c103200717a01e141548a868020184240081c400484003042050300c0300429039000c0035540c074548117400329025045881040003022031304011680740d251008071181500c020280c03590020b0081c0d4030452b400320704007001030f044c1030780d038400411190320342c0c09008004881c416645030000d001803010140000d1078407140748048c1c5c0c2d0009000005602103155900103815241800c1052014144080c019450480c024440100003a44048140e10140a54490303009038003500c01a03952f0402408120030100800000a5948606060705600580d240c6100500034080003901018503003800500c81c0200e107440f581142c1d1051560100c0d0381c02 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 231198857 1250 231197607 231197609
    0x9050105040b090f0a200102010f060803040302030615031203061206010602061b120604050c130603060321021f020c0604050a060c09120609111c11040b060d0203070e0607060f06 78
    0x510040c100340717519071507920036400701600e0010300e0b4154501c10200c5031300c02d4000701d509800e400d4040002c213580c3d03001d10b903499000d0310049000f0b0240c100016681d940d0241500c0c809100580507161080e803848485007180e00c0200392640c0078a10080001110000700001800303403000da002009942000c48130601e4040048145c4610381004211000907801a00307007030790f085081600d01064a4807041d800003001d0280143c03280f41e84002140029400c1e0380750b04007400700da004459158a104200d25101d498801104000016a000198000d010040c01911050b5075070440c40040c10064100b070f10505004007940d00f9100c5034000000c680c2070100610481c28040403a06010864074500034100310032006c0f100c030162900c1d98402e02d80f0244519440719030a0803000404440030f280b840d0f003a881004031225000d40d0700384400c9010340d003036003090f2060207225140202018142081c001d107120283d400200b130700c010054000004034003501e03884080c100c050300c201c0c00400e4003800e40c1708150444d011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 231200107 1250 231198857 231198883
    0x9050406320114210f03030426040308070b040606080a060209031b01090612150605030403030b06030603030f090303130e2505090607060605030616120212011809050105040b09 77
    0xb0780c0084821641d20341111110031991030740b5035201e031002c2d940d88600b405605815017000c4e000c00070411080001c40c0c40140d82c074460601094540c150032501420085c0650301005210071800c03c0f0410100f403840d2142507005209590100e40c0a40764405070b424504a00303030890710755401007245d4000e45014405a94843d20380c405154500000384d000820340c04952207034000307103c0c0006030802001a641c01c07402c01c10880448a05000e43d60b541c009050340d0080710180e0000c0e01c1c0400c40ca150f40751000403a40035800060096007026820f0503004c14940c050100f4642c0b52108002455220351540018001414800400045480c100c0c03801510446200314084800c2c0c698400c6110702c0e90024182c480c0d140064030041d4a565140c030382070300100446d4203d503034544110b104100041071450070781e440703c0d086662070b108440c2c0c0d400701440a034001c0301d111860007201140107101025540c00003002c4000300210214020300d05480f11400c64100f40ca0a44851244900b00f0021960030001d102031208 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 231201357 1250 231200107 231200129
    0x10b03060f061503091c0c020f010305040c0519030c030614090105090304170313030b070201110f0a050c030d0c03021801020a020306040303020c0a020a1e061404090504063201 77
    0x6007030000600c000340f0118900140070008000309514200c1040300d4042c40d83c0340400798221070509035018112813640c1000324403805421203003210720b5209000d40c502032688000ba4004050500e020021200442a05001e0b80f003000540007003c0f4480320b9000000352300074600000d181600007840d4068000c000c2000c0308aa0405040c4a1034150010859007201c015074090083e414030484000d0451294001e003074008a00090701006104a04504602814181d0001c1102a00b0040304040a000303452000c0880d8005002090106009000038555070416005482c03801c1c9982180b134088511031b501220010f64007080c1d0404c01c200e02d0341c20640080c001d00080000e0025035000a0740c40700010001401c240d008106d0381e000e62070401c110308020b036000702201c1200b0b85942c80c106000403250650600f07001440700004910740603422154480d8500c445241c60507040c00c0e03444015140c0600304448407a41c82841014621201c00c51040c0800003e40c410b030781c0354a03201104031000b81a080045000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 231202607 1250 231201357 231201361
    0x1306030b011706010c030507020915010e0406050d0209040302070812090a091103190e07030317010e040503030a0e0c0406090f060b031302090405010b030f07080706080f0c0306040b03030c010b03060f 87
    0x20418964143c3d02040902e404210824240b5007121907000d01d03900250000201014084e2200d80d00c00b407440408002c5e6112035100d5010401c1000740d51041c844c0c0c603000044121000b025060203003025511a00900480c1e52540e0b1381c1c140245044050f14074807000d0341000c41c90100e646071864103100200f903c803200344030024078820310800c079100c0078000a1600300341e18541d2155400a03041160781c02286421349400d0390356420013501d221480183d5080300c198202c004294808500c50450003150800011403c503950381d0503080041209611440040c81056410302d090b40e518094140501480c0c0c401054444401003080c0654045800c214a0081c0520801080c03c4d8096003424841307404591a92058645091490041c2064044a074040c0500d410405001d20009003240c21503090000701e070003c0c3e03034a4900b16948641501e5500404280c2008a1922100786000e1500003034000c00010f801804140040c1c5140d22501d03591049946a01690f009441c1c05e20200b688009151030f004914 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 231203857 1250 231202607 231202637
    0x9070603140c0306010c020604140103050108010e06162a030210200f040f03030e1302040b0a0c060b0307060f0201060e040f080f13080a021003150510141306030b01 72
    0x500030030b0591030890210010300c190313220300e098036002500542074070b83c0c032078490491040c400504a40756000c0b0f804c200001806010500c155452640914085d00403500c90f507040c85440308944d81450100300e108003002c00501580d1050342e003c1d000742c098071031003065107240103420600d4241007644858941034503140c5141482503016440003100351050342d10300c8151481e007150301554009003c2c94128070004000c245c0c00c000300981240e030440d000c502c45032801408d0801d07031207907004009413110280311100c0090700503020101c1652284501090b02c0303034071001092030725500d58040e0b0002403c02c0b0489404c141c080c8a0b001c050841c00714003203a1882c140d107520881440041c2c00030003d0f4400203507401c5151502059510000710a40d0300110241d8886019940b482c54181c10391090f05203007030101300707640a40301e8076440501032241c08140a1030311007000128100084d01900388503c4c0a007600c202c8280c407005002035400901a00c02c01c9041110080842c1c81d2295a1414401e017003084004e1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 231205107 1250 231203857 231203891
    0x30a080403050c01090506090303010503070e19020f09120c090a090f1b18020403031803110909030d020f030a0c0203160b0601020118060c020c1f030f09140609070603 73
    0x44560942002c0b6503c04100c920b42c0d00420310715402030521700a15041c02818040400114100c3d5422070171222813a44440803411008020384100f103030605824240c01e0f01c80040e8000d08298003d8003a0f250900242002090518a207628400c1040d00030030345241440c584141c110b9040300c2440010841841180c0c3e030040b0b20092a00060b1100c2140d264500703e1000c441031760350107403080b150032400a082c60050040a0b4001e80000c80218000203807005044001c0a600d80031241c021125440f520b122109100c2606d401505011103400304203c02005c0555900040032a014450000c540c0ca1400d481c0e200704440090500c101150410003141c80e0403180344c11a0201c081d00003821708850b499020060740104184801a00400040c0c032006040c8203e90340f011000007a640c094520303284c503d00c06c00c00b094007480c4020030070008410035224010701c60f51141c10f21003103c0c540011012000c2e00ca051152900100b10714403640101c0c104030746600c3c00d10140c0b006000e02c0c101444451881000c42039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 231206357 1250 231205107 231205111
    0x40b090309130902041b080403020609010b0a060c020a0b2b090f02101110140f060a0605070309050a08070f060203031317120f06010306050a0506160c1a0a0e03030a08 73
    0x403005846001c0c10055551325407045000300e00700d005400c07203213000000c05040c84138112350640c054011040000e0008906000340000020f0013040362620342d0601d4400c0c3c9540034442810781e0420103d102c04242c2c00c40c070030001d14500d003941c02490102d126140704200341640100c040045142001880380014000b240465150355046880c1d02002e44540f81c110b8805125a0b20110340380701d4401404c0b400078280d40030402d5100c0105c100c0c01c60741e03680d620007a0340c0941030b9103507500b0151181d42009454400c1010700f8801d8468982150401d64880018068508540041d9401d0704081710802250700a820001d0040c8540d00146003075181c1620043c2c120075810b00094024140b038181c4040f66101101201c0482e103218044040d6414540452a1401c038104d942c203000c20328180c004282890031040a07011250001c200c00d28242d48100480c00c12500030f1411580300440c60703c0410103604003001d104003a03a64296482d00c560008500400d10303259902024000d4004120000d02d0340d900003445a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 231207607 1250 231206357 231206389
    0x11521020d0f02030a0b0a090606050d0203121804061716030803061311030406151707090c03020c03040308090102070b040b03060d080f040e1006210b030c04050f040b090309 76
    0x1007002c9001d001081c28101c210000800720340358442007003c0030400d0f0b4015001315000e0030081211940301c90901070400030a020103540b5507c000c041c3d00104588600404450940d48400100f101514000c81c00307507001500207070325a000e01104841c40c400e04104584541d8180344e003402c4a00d285807241126403102600aa00403082e007400c05034020040d82000c0107564203440000d55034607041c06d26000a015103404821030301c00c20b903070020b80304026824980c2d400584c40098543d440c50107220400400d038640c00101455000d100a034050751051014100070341c010b45080d581c0e00c4209000908080180e000007040d10004d000501c611003e1205403075010405980180d0405001d0070400941d0003081441c03442c6510004000c20030305103604140740901030810350303585c5803511401c05a0350f00b005050342200d1915002d02d80c0d1300300b080310780001d603696101400760f0b000e006003500460165070007250f045009103840c80030310040215151080e41d100480310055810702c0384400010780c82a240303003030013 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 231208857 1250 231207607 231207623
    0xa1506030f021c050f09060105011b0f050a0510050c03070906030c03060906120201110d050702270f01050102190201080118060f03050d080a020c0604021003020c011521020d 76
    0x51504001d4a0b411229030001180c0f1011028000c005000050501140ea50014030f01c1c1c18017244019200043c46416100140c48820200100c6004030140c28582401914104030442d4104045401408801c0c842d502038005400e00441c20807071030081c3c603c003428141044070100200310030301d43e0000b80030054941794a40843c0d440743c00070b000c030040c0c82c00750480d0549524000b000030300f030701c48035801001f8280300380c0b102600c0030040709410791510404c2c140ca0004c12000c1014000602d0962178020b81101c80a10204001710110040b02e446032040720004011390300c0d00018041e660f010402341d600002524902065111180d0009002c070741c2c10301c01d10066104142603103000d078205400c0000600080d00c10850002d54034104103603110262403d88010484000c041961170b107181c000c5510103080000104015100c0342c0c2441007285002000300101039081c01b09103c0841c0a004441d01080c0c800c03880e80e030f200d0500f0040303201031000940801c40e4070703000360351000141c503140040426240c001c0700d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 231210107 1250 231208857 231208871
    0x901030e010f0e010b01110a0f060b01051b03030a110a02071a0c1207020a0501080f0403120b060a090303082d060a12050109060b0d0506060f03030d11070b0a150603 72
    0x10a02400c6480c2d0015403a5040945036003e80c0380550204142e4a400d80c4c60364001800c004e0300c141c43c5e142c6420040c0a42e11140d6040b0041000f0b0f41000e10b4041b410b1408500d03200301d4460f480c0007071807600d8062145410000a00807403000718040c0201e400034032000d40f0714000112501964864031445a141c840c9140d480904408000c0070680301c800c94240f050700d1841282810b208055440504100c0c41141010004101c5500c6207000a2040b6224084290300c1e840310340f03082d142c030701524400b00f81e11526401900519100d2002512041710769848410119040d80341c0500381d40e0b0300801c1c1c038000c01c070700800350903e01558003101c0c012001030700e2514405031a0507020504404041e008401c5c0501048072110820405601441e0914000d801c2080503281e43c9040001d29100400003500d6a4004804214540b901e02c501c010f0001c0014101d80c68940901413601c1590b203004070a030004440420342e403044c4030304251165405403007100204085c00f03251440c2d03505400c2d02d01a180030580e076146 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 231211357 1250 231210107 231210131
    0x4050406090c201212240d1416030602030415020a0c02010305040206160804080d0f090b0d0b04061508060a0e010b221211100e010c170712020d08040305090103 70
    0x1c0c060704c1000707580007035480805080802100070199004681804180c400240075202103038843c0c407280b8020000c0201c0c240d40c1d22000c100802e541d01010f00d50041d482841003070043d452a8000a5200c1c40e4056103038509428042c003285403800c1c15662031401080b980e1146588003500340d00312982428000381c2038403140040b41c103e0240103052103500060301c04d08810700400074041c004448180084070901e4001140448041902c2500321010610101080c40120090740c06080fa95120200024020200900103400d0390010f03030101d80090080348110801e907501c0a2003641c000821341764025041e241081000c0c415034148180d03004818003150941c0400b00400300006210382c814000c0026070b844540032884001001c4c0b0885d042000040d5400440c1000700345440c686403942c9944801811850064482440c420401c4490807a003050444020f1050400f400d203240c0105601c028286002c58042e01e043c8036080780509001102c3d04010000fa4403200710b80307142800303103004550014490 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 231212607 1250 231211357 231211363
    0xc080c03150a020717160b2805181609060b04051309150906230730020c060f1803040b1305100f18060210090807021504050406090c20 59
    0x103c091085d010005021003111600c4124081c2c042e000d104e4101035500d03804001890441519854076070543c3e02150008a0021540301940c000d1850034000e0444d50000760050802d006070400c520603c1095009001030038181c41080060400041c145262074101400188429214000165100c6c0c0f242e03c03601c1008142103d80007205807032441800b105091f403401d40080e1845281d1455074a44c40c0f4010001030000c03100e800c1c09a145074894481140c1241c5e00340b07a0000402c4c01c0c0c80782c8519440204400418148014403c2c452818007805141c00c0000004403070800c0a00382c0700406900c815880c00080d400301c12601101d424602142e62003c810b00e808009010661125511440f5091510320b119040210040c40c844160340c0e00c0d290710134021041030014594042c940c0160f0258000310310401451b40040b040d00d0180b40e601d400c3c034505078000f400304104594074008064011808003c242018001c410180c02040e20500021800c0000100030103a001c5145007a00c2c000008410040414 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 231213857 1250 231212607 231212633
    0x6020706030e030405040c0e0d05030d0b06030601080f040c050310050f0a1b0f03090215070b390f03190606030207120c02040902060a1107050406061e0314040c080c03150a0207 77
    0x1600d2412701c01e126040c41612500104a920a41410706d00b01100e40e01d03018007200c0c842c1c1c40503150724069440d107802e0200388410040003210b180c04600070100f5036680401c03621052400d100c00202e05403138040300c104000781020b004c94941d541842040800c500f0038461032804050a03203861040d54403200c108a02030b02600710065001265545031074078a210003001002c40d540141c01035202615080d5408007401c01080003132040849107004071820a441003c1d44200409102040d03040c00020004001154810f035010506042d04c0241020514200c2c01014024069424110b00b0308a0980b500000f00840c1940c1d00200660f004800046542e50380c0640001500980225103c041035000a480040e41d203002030f51911440d0b0700000d1178546809a0000c1d91034658030105140c080e07400310700030313008040e90003c1419110350703110000035000d4001c0c0380300b00c5c0100c051000d41880c084c012810114051100c6000380c001200010b00d4420440c0d6154110512020050740d50031203013050521840c42c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 231215107 1250 231213857 231213859
    0x60a1e0b04030804050f1206070e0103020c060106020604020108010905010305070501050705011409010f062702090604030b15040f05070c1209030204050109020310050306040f0b061c0c06020706030e030405040c0e 93
    0x808030707020041c4070b41c2c1409801925815520b00d051080c00e08104800807800d14402502a0701003000102c0c550b10841c1d0207002c0c039070181400340c02c01201c42e11070384c14502c098025400580c411000c1000750740e40149010700401000d04208465411038890342c1c0c031020780d4041c090501000082000802509500029218102c0904507003d42004605140038266143c015880c01d42010401701788200ca04c480da55100009054101c21003842c50622030180d081408a540d2114080c040080824146c03060184605c0d131044103441e20f8132811003080225001800b01d1b0110503d4901041002900301d01900f040d1a0803802d030001e82c1c2a9071908a50070f0819400080d000b03030620000142c16400f0786c014501440522171884044d0340c40340140341d568040bc0343d026040c0c4c0c900c20483c6010400301d00601c1d03001030300504101403110000c1c07490880314151080859500100c001c1c01c000003a414460007019188900d0b06010007042ea42c286541e0380100c0c011244107507038454075141458045c01801c040060 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 231216357 1250 231215107 231215129
    0x100e070f03060602120702131806020702090c030402180406020c03040f090e0f1009021903080c070503010b0a050103050c040515070b06030a080d0510080f030d1103060a1e 75
    0xa010080100400340164000c000320341401c8000c101640049928222802c041500d542808129001c201140212001d40e40c1c0041d6601602610b10f00c01e1001718003454019040541e0780e46442c41408030340d50300203203607025810003030041c000180e80e80100c070f0580380401c2c0c7d6030a503a80c9803414441c00901c01c0010a2500740300018001441011545000048824005040103d000703914021074030703a4172201d44880c982e0461004181d80c660b5651000c0c1090340064405015801104072541c0038a04542007990f4603940440d210081c0c90042082c000600350544c000e0010f41d43d8030000c145526264002c035030505480301e0014400306030040540307005000c0141880c40200900c8440405036000c42e60640d00040690006500f07800d0006890f481507610903441460810354a918100518014121041c91064100c0000e1014010080d43d0840c0c851000503603a20b14440002c0300c121003441000000e00003003070040015541c3d43d8080700c0202c072514041d01c0140c40252800310550300040c5c2100d01c40c12 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 231217607 1250 231216357 231216361
    0x10e040f06140703060f0801060305030316021005070e0f040b010203160201122c031303020d02040209090f150d0206250f05011a060310051003020427051e0708100e 72
    0xa034550040011107a0711b00c403091100c2e0300d9203001c0342640c2c01c5000145c44c80d44204041012002c2507284141312400503c1550b0f01480400a0001519015104000003860b541001080742c54440c0480c042a00102c40401030442003100103512070040040290b50780188842130400c0d6401111582c0e620bc0900508002c00400120300700b168803509c80c5100d9078562000f0a04400c0743e00003084a00c8202050119801a0725590030000361071103048089030001d40070300c0201000d854004407035004020f50855800c60f0b00d49404041b10700030090103000c0c41105009400f0003d038a03904100e84035000090001410402400c0c030051548045003c014000c02045000c00c0c00d1040641c0180ad01d110f80c03441e42017011140104002c600c0c0807d98245003c0312004800300b0961030820a80c0464440c5800e000d81816030360f0440000e02400010014071440340058a48041d401d1449503a5000103503d521080403405090804141310000b8403040c1440f0800c808500b1071000703420001c008100303074803150043c2c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 231218857 1250 231217607 231217621
    0xc0105010902030901110a0207050f2b02040f060608010b090301020705070602030304110406150c050726060c0301030c03080304320d020601050607110f0d0b041208010e040f0614 78
    0x7580f04030341c2a50194a42010078000c100c254040700c02d02d90007603004240141c240b90030003440c40011400c19030302c030096100581d03c00460a4540010640c1c1ea00d540c02c890320b070b50041c4010395944242c46170500c0d1901d0402d200c6141c00c16407450550710240c4424bd150391101021031300a00c16110060050300c222880041c20960000045102d503100700300308081d204d0f0034424041501d100b80503050904a0bd00d10003002a4860701d10108114060011100450340c0c0d2954008906c00510419003074460b01e10a490385200100b15194010560804030307491036140d903d8000019000c0e0000805d03403000000490300f03100f540e10300c0403240b1900c04201c90f005c040d608100c1c0030032b01c14100000715031300490000c4e10b4241e0020130054102d81d8042c003014900140c1d5030700c5800d5000d007440782e5a440140c07114009600d80f61010f811807120310410400100c1e00b0315050a102d46a90a0900030810003503034010b000c41d01e000c1c81c4481e001039215010744d900261a250080140c4078400c0801c031035440c55410800e41d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 231220107 1250 231218857 231218861
    0x20d051c0e060f03010306050a1d070512060c03040210020f100b040f0b10050c15010b0a08090313030b150d0501050105130218010f0908010603050102130801020c0604170c01050109 79
    0x200800c40e44031040400201418420309000d14080ea1102900038401040850300a07000320b544803034541000602608401d144100381d002400b40801b081d802540c003840700b42802001c900b0207842000003401c1c42d180c00d0301310b0300302ca00c401000240a0310303c1250104d001402041010028a12001a00c100a92015015004107c500c42c118812800c09004280408032031141c11a04400900200c0904c451214203031100d038001d020011452281c400c1d54030038002c048240c07a002c0c1c110075044a98a81d01c4c0280104803078005002c1880a0300308210f406100c5020090400c00c890740003410b041e655a810510780031004020045e140c1104111161400b000010b500550503610112024134000955040c10b00c1280140041500c018500c030300302c49015801032102400039402d0b8a010349040ea158401c4c1030035248154000c40d205d80d000305415a0f0049070540c6034018280354002107081c484880300256039008040c10280241c00c49000d4010500e1740d1100311902001c0c030000a118559482c108080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 231221357 1250 231220107 231220153
    0x1404140f070c15050901290d110f0406030503130501020f03041e050402030702100606050a050d05090f0f0706030c080601020d270f080c0d020310111b0a05120f04060c020d05 76
    0x30200e85043d151441f42499441a5440c2c407801030701c0f000320f030340265039000e1440b00280c0c4020760240c113848856005941d00e0180780c01851141c03000c0c41d02c40d00b008030040034940148e000f40d4195000ba100f61010030500200361021517510130841000c51300036000450800e41c0c01d0b0801500b080c000810016429000214444107050710001003001c0c036604d40341190b890180c1d43c0c0210004108000c580c920f16525040140c100c4505030a1b41c000404030000c0034a041060350303045140d80c114a10400002d038043c803e060528198ac100542c083c07402500013034444502c074201600340300704092108025906003452202040003955603000107900c0310074616007610b2a00c83c808090bc60b03071144404a00b84481d03c105402d502400a0090281a1414001038041080400f224580900030350b40110480f1020381000e905c0c22015180400d01814443e081500107a0040c804400411250410800715401c8400f00c418915204a8003c800e1000034226141c0d070f540540180700e03c0e0710409003240c0e5802484 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 231222607 1250 231221357 231221381
    0x31227140a0b04060516083601020106060e120a02190f1a040605030c070b04060e0d030504021e01020f01020d022502090f0403181404140f070c15050901 67
    0x20741a924903520000e40310318042c0c0000500306124181d0822844a458a40030b03210364030356820061031000e41181c450103078038401e070041a00200341c901e8004460491154000a01c0207202150420501800000041140d03d004492001c0d40419041007070000c0002250300a10340641801078541e400301c00d003d20301516152075010440040c000e81000759100e000c0d0f01ca410120300701303440d161041d1403a4000901c65041800204105e80c00255040203041c422403069a00182c1000801012841d00251590b4030090519101c00c2c400980d42309040d058200500300503c58241a0900040b41030030300c9408030850540c004240e00c1054009900078002c8040300b02522189040c107100710100355514103078041d4001c098040498044043c0d0513040c0d90060290400f00040340a070192020340101590243c244029000880c4130140b4190044514954420125081509040d04455103112001d46044240300c0e90020460802100400d40c621026a00301d041000d0b242c501c04141c041c0040d40c680d2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 231223857 1250 231222607 231222619
    0x10225030b09390111030c0a20090f01090905030d09081305060a0815010311030a09140a080304261207030b04020915070614090705090130110d0305041703030103122714 74
    0x410389e0f4101081400d101e071204018002590b468422090010111000241c070b0324002000503001c4040c003030054103c054420f000360366403242c650220940300b54464008a126400030001032074055482211203400c980140c60303052700c544001006130020704440148004a01002c0100180c5221580c0400c17401806800d4040000c810103480c130341c4500c007910008107004000d1020501080240109040c0d515050304282d000c80540039041c80c40e030300900c0710488019400c504000c0c0781035140c080c040c4440b80680f410750070078041200040d0070031015841140611004203808081c014590407925283c03140080e04a001c1c140801d01648400e154040e45004001e1748000207a142c100910170454002d41c45810000d00d2071600680600482c41070043d41c00200c03920761b6000541d2410071540701030384a5116a23586600d000341000036400b15901b10700c81a001880100089030010440303103490802c81c6458440040a00040d6000c1c0c04000701081000c008000081603a0441c4420005604800c441c3c07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 231225107 1250 231223857 231223913
    0x180b0405010b040303141602060f0705010b06030c0f03060d02040216060b03150a150b03010b0d0b030c090c0a0918050a0f0b010225030b09390111030c0a 67
    0x1102c1d242d840359100c0203001543c203240c8400b04240d20b00240906555070006081e0050468000492035088070b4581c41150500084050400c0400d1142100010040e641d00c0d0446c6002c4a111410b4000c410706550601e0000000510310742e12070302e901c844158014011921034171840c7c40350f016440000c400315042c03482c100071801c65180000c1d079820001040203000b4455500c800200000d0044c502030b81c641200030600c082074042022001d50f01174060445c0450300c83c0542c90480054440001c4002c1c040c1d00300450200c0700e0345031015501da01c503000c10242c60f43c50034220000c45040440da400040d014041c0d0f0030120f803544a50308042e0090b0b00599003800b01080904220f0111348850501074050382c408030200140300103002c0342d1407600e0020200c602d0079690307a80700e83c10042c604075078413019508004100303400e00141230307881181031281c7c81d28103603d084080241f85040b1b200c0c0403d01c0c140b02d401d660080306000100103c400c1d8800c07030b0003600d0448100d858000140216203906611800c0c40b104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 231226357 1250 231225107 231225119
    0xb0f09030604050c09130818060712050a0f2303060307080109050109150b0f01030f110408010c0807090303020705060d020f0a18090905060c030c041509030b010609080604030e030106180b040501 85
    0x2c41c085010f1f048258686030400f80c005515002c5015003881d5081b1006104000104400d80b902c5803141c642d07a1610741c0d0b40e45a05c90000c00d2940c4048881e018494050441100c041e103441190160360000b28080b41e603622004000380c0b40c185903034019100d075800c00c0f01010030010190440f4180c640f05030310b080303024035203210040107071059030741000d401c84040c80a4101662184d04030035904200f0f101d0004803c41c0d5910100d548e03a00980005410f81c0d140e150360810540c1c802c1d03005900103224078064001c0742c2561340c000d403640040c1c8185841240003281840d6004899411109801c20504000f40e0341c030701054001c1c103002260413050140e105024400620341055000b800416a070000103040302d551800c03d200360540018002090b8580305100104180320f0003054881003030050380305c64a0003450751601d940c8110050708204208041c6040800040000080c1035070443d60504210894084980100e401410154416603500c4a08021506081410b41c0011070200c41601c2c01d00c9160780340c50b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 231227607 1250 231226357 231226381
    0xf120a031a01170a0f0f050610050313120210091109010801020a0207030f0c051215061c020f040e010c050406031103010f03020d06020c15070206070e09010b0f09030604050c09 77
    0x31080760102d2401e091081c4510f9810340840c0c0e000c0401500020f2a14030003600c0c5086540b50301161030380940e01c006014081c034103c2604d00e00d420451512900d14030788a103040d04070080d600710041c0503040300c45005007094000d204800b00d1154410b030800420100d4101802c551079038840d568005c601443c0089440b06041c0221406203c042c0c000789006851580c0f10140740000000940304010308510108240d41c64952684070406100010003038600c151848583d036003409010244038010b210103900c81c1444480e040c0401640440d003842c840e44061000c540036001d15a100c0c4040d529003524113075a1500300300500190381c1c040d034040105e4001c03050401d07107030b22080c0102d02402a482d035003000103150003807171030412603c5000e002d410290f10341005032526189003034407001001440108003513141d0400c0199840006884c1482501c049900420b0302004180500d6610701310000303107884248440005c48441a0020b011103650f480c00d41481c644902c04031569500c985180800329901e07140303130 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 231228857 1250 231227607 231227651
    0x409050f011511010b060d0b0108070e0907080901090606030302011b0c050303130212010203070206041103010c08010513090b040803070f050a02030924180a090c020c04020c0f120a03 80
    0x45640c031075801c1400d501610340e0f40c4180c0c84140150740310308a1a1450300d030000600b10036030700541c0c041000342e0860005482460010808410086000d2088001c0c0d40d506400d203800c49035a04044c00e4075111042500e0150003215070140c07d071801d11b440002010780c158004d0210f08007601c15040b480c00c40b000100d810004511001d071850740b0a0001c290441c9840c448084001d20083c507803501d0000580f011804c1ea00700b02d8407040942c003c0020401402210001144011301c120001c0102c45103c0c1c10281448406004d128018201840e0303601880d5059442040510340111f01c43d0124609854610a250f004448100000e1101190000064000c80030f07074445054980145040004036801c2c80500d000050380f201583d1251103e6a001090201c004d0011085882170101c007000200140070f90101e055100c40a82440d11000030600f940c00300d2040300700b040443c0c0269a6200c2503a074945025100e004400481c0111840364040c0d01041005202140042d01c3c14401210020f003800b04034960 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 231230107 1250 231228857 231228869
    0x7031b0507030b090d360303020d0e061204260d050a0c0201020c072c07030207200604060e03010b1002030c0f070620010f1104080c04060605070f030302120c0409050f01 74
    0x200e03d28102c1d561520540c1c286154510703c0002012000c49103004000040d0340148c0140c0c01210240c45810703800b00130202052400d40d40f5501c0c080101301c1c00315004000070005000b103126405106441d500ca546050006400004120340380e0b0301945041c802460161148481c0314504142406c6860042c0280c44002d0150409000c0701458003060220794280511110b0514603040800440c04040d129518052804d990f40140c41e80031a107482c07482d820480c00c030459080c4200503841001d680b840c0888040d0784041c603100d070301003500e840400c2c0908968600c0311b5000c080c1c0c904e021840c0342c0c0003010f4015180020100d03100c0781c201c002c1840d210300c0d0318000c3c00c00095141f6042c1c03800180c00d0240380144400b030000020380410404502040301e0007031010341c07210880040c0c100004e840400580b011843d00321403c100c202d06e0044058103d1203500d0f0028520002c40d02100e00b454080e6040e10010301034032400d211189090000c0f00110f9200b405003e27810780c5004041484888c0c5100d10a040c0c8003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 231231357 1250 231230107 231230117
    0x3b1c0318200f090c070305070f020a06031a04060e0a0c05090301050702010203071b0f060513050706090801150503060a180b0a0f1a010f08090115030602031608130807031b0507030b090d 81
    0x3101e1b102118a03611800741614010782e0742e521036005031120390050b0018106540d00284a070380381c180c1c024058599020452003142065800d0100d03030b80c0004e0017030700900744e1030b000100c8041c58071040e2140e00881c0a05e0f9455460705080050302034040d0002c51007152182e0710345111442d184520031002c820260090803442112a5030300c00a05680d22680d044200b10803285c2c41d803100c65840b2450140650002000208100c1c000c2024000c00d002e03c0110f841c443c1c020015040c244000b0030303540c10004001b44c4247d912041030080781c00c00050b4003003186412036680c162038a400c070003a50281114102ca1044c0ca8034040c034084411401620344082040c05030b40b90a101c0c16410f40856202c6409081d5207969503a03031031a50724034203516070800c3c010340c810200580c69182c03101641550801014200090002c10020040c1980b903103008244030700d501c40170709604c0392401e040440d04408950342001c948071515004105100c00013a0300b2044074418042e840075580c0d460fa1164444189038144c2c00456 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 231232607 1250 231231357 231231367
    0x8070f0c02041503060e151501080f0403051207080610030203071d030f030a03050a1a030304090c12051302030c0102160b07063b1c0318200f090c 64
    0x4036158000025000140d08040e40041d101d807584406c8600d030140207503030341e4080349114040780000b107800780e0f0001208518041c0003840c4130018000340801001c0c040d075a0001340003d020140a401990140922024501501c1c5081c1401400800094525620444c18000c41c056294424022a072140f01d003a41c41c18140e4140520341d08028407501007840c1d05006074071901c80340c008200081c1000e080d0f00d9030041154186800301c14100c40b1110b00607500b5008841915603580c400000301d030125030441c000060340303152074901103c011617992070300340c026818101880b080c141095040602140200c068a00403094807005a0f40c61201c001d50000034180858104071841c00300c005409490701900002ca4400e00c0c04540b0148000f0854502c840071091907039401076103588a40d442d0002200038018505007000041e00d41d180702070088000e0400da21030f00d408541d240c580c4955454140d21803040104240050001e500c0751807442003080c012076800c540d048642c580002c03650302502c5600001441c3c6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 231233857 1250 231232607 231232609
    0x6010b030103330e070f08060402011704050a0c030f050114060a06030c03021e0318010e0303040803090a150614010306030c050127091506020307050d0e01021e0c0108070f0c02 77
    0x83e850381d070815082091070580c2d0b40758880b024041c00c1c40c0a410000a40040741c107010454201d14141d821011440d4051020000180d030481e03618402041d440b5103080d01070380c5a1078001d00e000e144808c02000c5546280c0c0000c01c100010229811907071042000344040b00c1d0784120340321440012070781c00d640004004005c010060081c0e00044800c1d455190151800c00001100d001c004075400309138000607400010860b056085001d0b04803801010b00003808124142c05603507a4134000a8805400c6120000206c4c007000c80400c1614001e03a800000c210ba6030309036442c080010030311481400c41003070b01c01081e00382940c420310598042c0c4e544410025001410070f40112a88020301e044001cdc042d142e0703d0042140e4407200e94280042c0550700740130403180d9078801c5584590003164407203000c1d5841403094800084001c100040741102d140380407400542400300407480d1a02c00003100c403031843c200700551800c4901181e502d07000d0030300388c0f01d124a6032985141111041c0040c40d4480c0005c01c030410074401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 231235107 1250 231233857 231233903
    0xf1d0f0c0a02010e0102040b03071b0305071e05010c020a060c0f1b140604050d09141c08041701150f0501090303030203090109020a09050f0a0b06070305030a0e07031406010b030103 79
    0x1540c640b000054051000f444c3c50b089902980113441c1030f01020040102c010752201a426911521000302c81b030f05480e903640504a4013440b84000d00d996000d611000100e50f140c9009040150408000e001c100d00342d600281d11902000d0040d10054281601401c10754000d4135044e0400f21944e5542504004152040d1b01d1144c0c15041220440800440007050700400c01c20540600d000b04040c200140c200740001c3c0c00e110540d07003c030707180010000c0000650fa4070f8078100a0720699010b0344a4800c0c40c0c03464185000c6c032440d0811010a541c072504691201015407101c82f210140084188840342c480c5045418011503100d00f6001841180301840000c0c0b0980155406c910044000b00f146106640007a0452550b1b4102c2a015551001080032080e0060620b03600103038400c1c0c5c10414951564041050f034455803c0c007805200e03001010441ca030440f5401482019054020b44090075201d1a046040000300d01c0d10041c50300c940000403903004640e02c1240c0c12603501c41144020261003011100c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 231236357 1250 231235107 231235117
    0xe150f0609091905091c0201050709030204090201020a02060a0c1a040803060d0c0e01060f08100807140d020d050303071403061e0f0a03150e01090c09050c040902040f1d0f0c 76
    0x1030301e405480c003810880c003c1409002d0150707040c40041d200790755000020345500b485600d0404210380c1444180129036400004040584c1d4041c0c4012601800500050b45000010340700250028400194800c281c1e50040341072080c1c9128413041c03141d40c2500c8251003810002600c0c06007030003000300f004c030f00e062802c141c060b004984114100550b00399201850342503101c0907804000070404030890b400c11580d001b14103a61200c04c81c00c004c043c0c0380c00c02101300c2d6030346840d0148491040038050681d45039a0b964070b503000440e500911094100440d460200c2d201d0700242d409070089000301451b00c44880d070f002c0c10343e40b28107401381c080c008641c0d034568402c4009000d80c028503044406c25044601c1500d9412801020354052100c5902140385014454122500000d1b174001c96403524862100140481e10903200705ca08212000c14a0348842c0242c0c9914800e41d40402601c0d4800100003070f401903840449011a100c90380c0528080c5149001171450b02c0044508101000490001640c404000c802402c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 231237607 1250 231236357 231236371
    0x12030c030c080405030f0309150f0601030e1902041508030d0e0c030a0b15041103040b010512030a0c12050910080405060a0e0a02041e06140f03070602070902070602090a0e150f060909 80
    0x40c9010b140e1401040e101030090322b00c4108003060004000843d60140a030303100d000803070700040038500b1001c4a204007120712658003d05c62130b12003281c0201323003040c03071007800c01b80c803a0030142c0e541d0311500304020000b001900b80070318082c00740181886803803502241081d002e0b40c20400584055943e00614007c510002100c568484d40e100c01110a165240c1c001e58402c0d03104001202c029410a0100040e86055942d201c2c1c06610810003840542e502880490440d94000c01c81c2d0341901c4005d40945c4c090151140707282c3c11034144c0f001d0544042e44200014000d41c00341007560002e0f26264061000e4407404100710445c0c7d07001c1140702d0011f081a0b4017910404610058500506110501802c1a01c4003648100e40082002ca283c803298030700400c0395000c50034110002c00c0032501c0d00318041d40700c0c0d50031301c52a101c1c184c0c0031071303001d0501c8041c1e01202e401120003880a80103e4450034412403090080e21701203061f40c0e40030480d03149401c000b00003c54016005000604045c54001006a4900014007507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 231238857 1250 231237607 231237613
    0x150212030a0908070b0106052107050d050414030c070e0c25020117160207080d0f0c0311010f27080301050607151802120102040e070c0f12030c030c080405030f0309 72
    0x1004605840e0005d8041e11007641e8581e40c5d041c41c024030022594410441e405211511001c1c4514184c00c00101d0308412001030010a866903641000f440c01c0128401050303440c0000120000301c40404034084090f03403880d482032105615400c1c2191014007074848981c806000c01113103100b2001d42c1c10612503850744145004091a003582c0c2020b6402c0605941d40e50f24075001050341403100e50180300910181c041d0ba0000c05d1000e030a500f0080661051244000512008540140c1454415040840c440000100038401d8801c2d40c0300c0c1d80002c064451034008070115082c004000c044a4072060010990000406411039080204000c03481d442004205e03040f000c109071354840d00c00c0d940a2140885e1134045003869801c00c07401409620742c0f000c28441ea4603441003005012258005802c0d68008800380346c032951000c0301c0d1405544200450402810300e56200c5603820130a94035400141074103295640030320a0700840f10040d524810103039001030040c0c0090104505648c80100550341c450800c03c12 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 231240107 1250 231238857 231238867
    0x9200a180f09030e030705010c1a0601052106100c0302060c0306120f0102090301050105010c05060403030911210d020304240207151d0d0b04060c0e040c0207150212030a0908 76
    0x101c50125000340c1402c9003c40c1140032a03880c01d150a10000c0c000700f07400c0c200034143c680950b07a520305902c171032586001300b0f081c400041103582e403144003503035907404110b140702c1580e09800803210090034003115028440c03001040703106501886401c890100c80d42c95001040107443e03540440f0225040140f019030414048202403040403010010100b055540d100010398558283c01410709440d41600701f2818032890074451000508000391a5900c5909454000703490030381d5190002154441e09400341c1e0044280462031140b00c901c4c9040d40880703842c04219420485603483c1640c40780900e1051469074010410580030030a800d007044a441c424920559041580780c40d841003041c0301241100000907000030b00c00d41641924071084007011006c88a40c1c0c2403408076503d11110b5a002000109070544481b14002174070b0150401c42900c440041040c40b00341c51001d0000d68a40b118891001ea49842e803103550b2a041c00030600c403142560380d2071420315654410201801500c00181f08880024007048 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 231241357 1250 231240107 231240131
    0x906150e0114040617161407110a03080c0708120a140409060b030a1515120e0102030106020a05012403140f01060e010303180f091805010f09200a18 65
    0x40140040c000545801051207480803201c122514002e00040b02d100d46d40040300c1000c0d0308000d03555a040d0800e941305907220083d240807014040303424016a00705540d4600030042260220281400055100488500c42e50720343c000c0e5600e8061100d1712034810000c2040540e4241326104410845001d00041e43c98036590b07940708411122658011801d040300171040c17021024050181502c00e032802143e182486041045152004122140040500583c0e02c03c05200c03620b03d811444c0003541002c021900e960f52018040e4480541e000c0c1258a940f902d0f60301a201052102442110301d0240b628080450a5960f5101d24550603130307112045200300040403400c40400d00450018008030000150694910303d00a42140340710015054245130310038040c004840581d000000300d4204103400300b0000d4054824401400008002526a5080c84d9a00c54901840d0300060496841410104244c120040c03c0500b41c1c0000d4103001c0c2d0200c18114100071204500c2e840030003840e05a20002803000c0584 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 231242607 1250 231241357 231241397
    0x15140c09041d0303010302100c0201140307120c020c01180b07020f181005090a1a0105091203160c05101d12061509180a06020c0c13060306060906150e01 67
    0x340b201005907100000500460822183c2d0401c0da04090401c0c06044107294000b801540c012412281544400300008410a00c5000c443c80300c007840400402140d540040001d4440c0d00341054140401e00a103410b005603030301e08000c5002c41d82ca10040074100101036003001640008265200d0703102d0400c4100c03c0c100d41031a214140515400c0d1100105031f450b0000784022103000030203002d0368030b1a2042020511800045040340744d0000d1038600c3e0f07282400d00001d13010380aa0000704003103101c0440d844031442515903920385540e016540351542c40380c0c6ca07020031000c4210306a402c40003030b55124203405020f5810300d84050312200201a01180310010b04030700d02e0800c0440b038010750715020300710701021410200030346e540089548503c05d13402c5000b200e0503a510851260000c08076a40028880c001040c18030442c41041030040c819030b100001012014050401030005564003850240d001030b0003d5103100c0c1e4801c803100649a40d0031107002800a594100a00c50700c1414810f40410005090940d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 231243857 1250 231242607 231242651
    0x9070203041a1207030b03210f0a08090f010204050102120d110703080601180609030308060604031406010f0509060d0206090a15031509112b02030c0715140c0904 71
    0x6800b561152220082015500b10140c842c40605151000748140c43d00d010030409100010700038800c0740e0701c0360894900c44038803402d402c01d84110004943d00446581c8a0001401550034908550074461943c02c003030300301d100e548981ca0141e40160142103407004000301801c1040f02c0c030790b00000c950b0a80b0340d1546495102081c22000518584100600c540e0880c902d42250510104404031b02800e204010f4207441d440c2c0000781c1480401300028071156540310841d00655486120400ba85245848050343da560070f000d40d61184800b000c004c41e6a0508542c0140301d10002485d00180601a4080c4a16a481100c96a0304503586210100d804641c80300b00d1a01103649607400038903c80b403010f100711001300c6900006900340c1401c0d0122005854502a10280159014511901d21000c540d0b03c0c0441501340203080c03250300100070008131200f590080c003202805a030034111412260002c40c803c1f588000c402d00710b20062040890020320f855409007581c1e00d805000010b05620706501118801c1c3c0c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 231245107 1250 231243857 231243899
    0x6060e091f1e0f150b0414030f151006050304080a0f030f050f070e0406050604060f0908010e030307030c0f0206011503020c060f060312040b0a0c020409020d050607020c01050412020907020304 84
    0x11039040d01c00d88120303841103005115400203044101d41c01c00300d8803111841b40d44103070001d582e011039821005a5003442100c4589650310100d48540c10514803520701035000300c400702081040000700154441c01001141e2240b94003030025480c1c00c030115404c1d80c8040740110704c941016a0b50240c0c1c08400500c0c4149401041c0f80b0034000000d15055500070145500031341d88030300403030a000702004a500d841055a05440441c24041070000c4c4001046030000d246501c0b1100c80c1d0f080203416400e601011008502601003a40c0c24000100c0c0000156408198003110000507404400100700c040d84000011043d00c0640c039025180500b400107080c54190140c1d225580c04d0450400d100b494602080b941e0003c21000e0980e5007000c0c0b5280001c01d1340d0050441e03280500031968020300c1155125440114400c1e40248880c1c191026070405030f5a40c54100e4041780984a5200c1500d2258010001d0340c08032004d10444c402c4e0000c4135030074018100c00c0075025806600c402d01c07011455290703e107804c0d4407501d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 231246357 1250 231245107 231245111
    0xd0801061d040e1513020604141504030605070210020306031504051e030d0b01090b071e08040320030705030703060f020909010b070506011e17100f060306060e091f1e 73
    0x1310401060444400f401d01c540d01414030755900c0c0140c4510060318102c80c80245003402310586080420500c1040c480c0c200000440010701200300f040c1540b00500502096003110400450200314904902c81514a61345c141d2007900d9004059202c0c032149648140705006480d800d102264040080801284001006400100c1d01480180080c4a10003460300246880b00714989840301d08c2c141c41c4901354014005820b0307203440080c20780e140166061280d42c0041700303039601d560b2818409419a90342007030001c00428000c20010914000a2030800c2d03d00040250103000d2865558000910500300340c6449141c003030200d18040da80e41d80c4914005d01c00500c8a9660780c14a1400f13505005058001e107090f08100c04d0003401d9051407540703900035204c0c0381c898042c4d15054070585ea403411091070b8040e018681482d0001c83c29818541102080764400e510a2040303581b2500b503002c8042c011a40b031003003070780204d80c4606403408036070034000c0280409030002024109910005080000500b00c207244035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 231247607 1250 231246357 231246373
    0x804061d090114010804030207050901030807060f0e030a051c111b03040e0604021c0c090503190218060111060103050a0c0b090a050f03010609020c070f06020d0801061d040e 76
    0x440e0301046180208456145103981080c01c40c01c1c0d1101c08180090400044000081c2054001c201340f101400008010400030740e0342c0d10f0540040d50014000321101c40c200300c1286901c1000340140607414021074084d5080c0240c02d14100e0f804c0d0000f940e5540003105203010240c0b045054070800400241e0100d485594014a00300c20031940016014103a9590081008100c01b003060b89500707800002c1101c000d80c3d90b103101c00b03000a0b00c0a10200304d8100340d26007010100c03200d8210941030100e5005809031503400c149000603418801035000e0103508021010003045488003071a1a250f40000d050502c21400030346030f45103610b070800907001240c0b03a52002101c036003401400c0a0080050680403241442c05020001248800295100b1640101d4028010032035035502900038101600c0ca910b0f0840d1502e068003101543c4845511840610500140e0003003485440480e06024441c181c2d120b0f43c1241e4a0800115050907070b0700f40d0781c130340b00112440c0c1110710750343c501503101c0000707290004080c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 231248857 1250 231247607 231247637
    0x1802030604050f0115050310080607020a03180b1605010204080d020105090601050d03020a02010305070320090a14010c0821090102031005010f21020c0a0305130506070b0c07020d080406 81
    0x2e480180c034242071005000c004010307864400000182c0131000d854581d071a9210769501e510340d2119504140c07024000c034410071540c42d0740001e2011815000e075a4200d0200b07a2800c14080020340d501400c69612010001c0300c00f10a1101400c8048611030030005140a584590080c18032200d403460340d0041c2d44070000d0107600f00d010040c050152404075094100721360940d401a50f075250520009040c5610f550010740c10718000c0c0d0094805800c0e580b82004000e07030340e4a40c0d2045a10100c0101c0c401e0780401300101c0d026801e014400750310f080603110525120004e8503a060a50020040034041e03c1e00f200d00c41a40d0a01d441525004a901400141c0c590409001d00304010350a50012410443d2640da281e0031658411140d081c1b406240102c1c102410100c0f030301c44060710034004001d4040c41441e125604141d84040100240c003403082003078162079141c2c0700300101d5104601d0f0140c010f48010010076000c0350542c0041000910050001d03640700b101e03a503800c407507400a9010001048141c2200004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 231250107 1250 231248857 231248861
    0x260a05061f121806090326130209060a030209130209150604030f0f060f1e0509030a030c0912140f010905030a08150901090501170a0803070f140f04061b1113061802030604 75
    0x79001f881300d403680317000c061088410308000400b901c2031400b100850490b0303c2e02e03002000038603000341107940d15291807512180703918541c883c01c901850160300000c00300c00708100b28040300708005001d5840c1924684480c0c1039881885010303100500454029400580540300300c6042c0800f104001c15940794560000780c1d4541000520004d8074101003c00c51141404400c88608031002d09000400904005003120a1201d68010203503d54204c501d21044c440710070359820303211058a0480d0320080c0d40c3c0c041300e4240c0d040841c0081942c0d005210a4441c1ca005880301944401c10114410004070b004000031a210001ea008441d003c0e5144014401d440c0d00f80a10700385008004018140e104030b580d50485a888010011000c0105e1039520b4403000307104084080c41ca030a82e5400d00e807102c032034600c99101d5501500c1828007060401141303002420886005952198125008840d05541d0b0310030f02200020440503050290750302c50001c507a03241080d102121500d400d100040e00d9280c07460500003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 231251357 1250 231250107 231250157
    0x19030501051503060d0311030d061409090d0504030201030207141e0d0f0507020d08040b030a0c0207150203030403030b060d0207200406030b07260a05061f1218060903 73
    0x440c0e10b40c20030400c401600e6051030b60780b41503454036104000d001241070060560041c01c1100326458180500091180d0902d140e11211040c11506400103882340c4100d0381d6209044c0140401083c5e09010030009503010f81d016004240c0580011035008407524030141c141000d882c40d415400c854809400302d1004200031621030071300700e41000c01e4014003000e005440c034042c000c2c000b88644007025045080090310000d48000301100441c260302c0b0304200c500c0c00f0240c4241e90900340140b280610003d48000c8280240a00c4142d170b8000c0d51079502daa840c00c40c0070b0180841120740101c000c02003010300290750306c020070360745004070b40e0192074041105440180d502110817451245060020031700103e1a9050303081d800c03407050f09042c604821911400032611809401c1002d959120314200000700710aa003007640f1401c41100d019080000c9405003c0800766050115800200000441024502e0541c450300883ea200212011095120f559000c29180258412800600300000700360550710040b00d01c03030b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 231252607 1250 231251357 231251389
    0xb0d1a0f070306120f110d08120c091012060b0309070f050402030603071217070c090b0103090809010c030c050607111b031f020c010e0616020f0c0907051903050105 72
    0x121031607280c0600c2181c540c4d441d40010b01030076040701211082100700804008440d0340a020000c80d103030305043c080241c0d04081c4841e0042c840680c00582100e07480030071186440c00042c03074074502120f108012648045144909199155507840c045040c2c2e11080196202c1c101c0b40000b041110f09040340ca0407504402da004501231401407040c070400340e4000c00c80c4401e84020003400c4030031303a00d1410b0442c01d00c244001d1105440348d000078901c0c2800a9020094292b4518103410301c00c12000600440403160074000107065402d0a106480c3c056226070400c280c80e030702030703d0000b02030003240d11224209842502c007440415900722003c11a02c0b41030120220310b800b08460003000400c54000301e6100c40804907542d9498141c01c981056081c0e0642c19581041c0c5024000c00150020920b590381d6004142c492a44101c203030b0810b46012440042c0220080071100094038030000e07180240410b80c400501000c0c00d012040c17144180d201041c1c4000103d02d01151b4010840354909020b0294038a0311480d44 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 231253857 1250 231252607 231252611
    0x9030705090c090d1b150f0528090317070308070507050a08090a031a01090b121011070803090a23150402030102130905040b0a02090a03060b0d1a0f0703 67
    0x880b0315081e4000781d820205064402c24599100352501c54012a16000c9a07070480134010000304070f80343c40c510038814242081c1c803928881c1070800d5040d501d80c0140742a0400c8804419112080d914481403030700c0d05080542001c0d00344c2074403903440c0800040c420024131051000801d0350b000b4903500207045a0040f480e41005847d01c8400d071102c03610703510441006090310b100015201e0842e2101044180110340142c186161003c243c40c0c4500c407a40d081c0310319012903041c01c6d030840f810715107601e4818104003803400a0140344140c00001020f00700c2c2507410040c04809001c44800b007a00c0b000110f00c2488564080d022011840c5064186002e21032a0319440c00300b18004074541d0304000441d1011407000b079081010903601c41c80046d01a10805080050407001d400d03000030000d455420450041e445110941f55503034540020108034000c03110317140c3d4802e01c1007108001042182c0c0c403007880c0301070281034014000b501e61152503420800b43d140091035020b4108000100000c07545841e0072062a181c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 231255107 1250 231253857 231253861
    0xf042f070f080918010801021206091306150308041502151009090c0305100b09090115061b12080a0509070302010e280b07140706080a05040501020903010609020903070509 75
    0x41c0ca40e01c1030205070010060203000030940000d958042488200409154041c0b00c1e56071035144081c0070303403c075541d610000c08031000816901c0c580540720ba441500c0c048006480f50402e5110032000d421880381842030804540d0000c404200301800610207408140034052210800020080ca001440b03030740c1190300d88040d418042c043d103201d45a0f03012100b0441000c640300e1554205021250010b61000300310380b244400e45c00c2448020b410224407107200300c410500d0b076a2a1404182651309440300c2108140c20101b05000e0b040c05922010803040c4d20702c280c22500c1e403155035100c07140320b0707801e141201140d20352042094100b85801044e81c45103140001d082d42ca450350b80040d09414800c1d1000d4801c0402c900310300451510402c0b851429007010540c1d10b412541c580c0d41010590015000f614201d1620b00c02050610002500100700c17252580e82060b2656510310580041c500503200301c44a5400f0040c0d010b81d80d80c01d008080140c542a080180d40b4462403023003600c1c081e15548114003503030300c50007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 231256357 1250 231255107 231255113
    0x30e1c090e010b1e1207020607020708061006111c021f02160605180105150108010501050f0418091401052203080105040504061b0c05060c0421020f042f07 68
    0x10a55030140316042c011256030280c0c0f13a50405038002c00f0000e0b0364241d1304c0350820964a13070001d803ca004020a80030344107480d407110030f280e0715460100e81c0c58442d1342026000308121840703103040c44d4410201c03a0075034124421480c4500d4500b1a00500140140e0002d110507446600a600c1d0b00002d015400342140740103070361181e20031082d0200b8005041c1666850002d0091100442010342e031080c40d038000c100d24500141d40008030424000d66a00044040002007807950040d800c84009152030306c0694141880e0580001c0000d20440d034040c800c5465030000c1001504420040f81d0602014001140c245401e050005400021006031040c1880002c015070103c0c0c1c00c203045c14103440c01503c000c90181e8441c1051405041c404107102522604c0c0c0ca00c0301c13921644441e00c2c1c803500748200140d03119629802c02d0115113004078000d0301d1700c80e80b111811303c0c409402e222405440d588040c094542150100000500316030030046010588801036010403103002500d442003940c8005d070148641400c01d00d807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 231257607 1250 231256357 231256379
    0x50403020c0103050403090f1e0501080606120c0d0c2c0105180d02100804030e0105040f05061605101a0409051f0207020406060f030e070305060a0c030e1c090e01 71
    0x41c0a4a051507030304c5021605152090092401520050000c000c3c201c0d6a5607a00d104a205a02e5040310040c2c4010045890340c4551a0f85009803001000303281000031101c0244844003000d40b03c0b51a00e0340030000490b903081c090003962200c00a54482c08410810980f040041c0b84501c0f00580e907244107010700807050780c0c0110584c1c02220b41a01e285080d05215000b05581d4141f20401130750080310784020440d16070744184e865200c0d9101c0c0e600c0b043c0c0d0006040065071703d8000d5001c0c250f030800c0c9a04040c452818400040c18900142c3c81d0011490627039916414104a48800e030400400d407102000b00718265044003c800118003524104004e0065440d042d4544600c41007407040003814550020703d4030710a405490304140c0042041240940c0c1e01070207002d101c035000d240c10210b418410344d03c4048802040c01d00c1242d0b00903020304200e65442c82681d0081c06004c1d9070001345952084008514002000f0300c24500301f45002d03600312490f482c54007400d0a10303d0b03440814048404001444501c20003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 231258857 1250 231257607 231257623
    0x506060f03100b0a05060c16060801050f01030203060102010f0629040b04060c080c010f090605010b03040b0703020906070f0c030b0f010b0702040b040b040c1206050d0b0612150408041805040302 85
    0x2010020f9510f00310000184080d0380c550141c0da210801054205c1198808100940c1c48200941c3ca030545a0b960001915101003d11409600c07803120841c800c900c0d4003039001160b11200502c000038108110021140858415403c1004148040d9100c42d40c03410b00f00b000054035205014469040a00d8003001108903c201d014441c1044039a00b581d0f804c1048140580300801c0f1440f00901c40e1000e88414034004140c88501500c000c0d0038200001407501811080b00d00807904001c0352162a9240c1d04d05030043e500c100705060b0440000c11003c804281101c1d42980c10510520018040c1451420000300700780c0098034039840440400b0041250210b03880c00c885c4615070690f8003084c80854040024002d2090003200360704a4107214001c2403043c0e0245039160194841e40040094640b030f0805c0c4074144841600050100c0141d1001c00ca6502c2d148942160303400c030900c1260010902ca05064100000944040740c5006003c2400c0c003500601e91070000e070a50303402c1c204001038501610000c0d0359540e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 231260107 1250 231258857 231258883
    0xb03030f0910140c010203070305010b0a08040f080c010c0c12020114192307020106090506030705010302070503070503070f05060f0618341b030c080f0c010f090506060f03 75
    0x2c60019560a9003d0781200c1e4103480101201c0c4d46030303140340b600035004c2d601c01c548a40c002440c010010503010780c10416101b603a1829510801c0595942e540c0700300b50343c0c043c0000d0303541003020301829003604001d010300c490404441c0d80c0c400380803081d450120b1215014410b04011341e418641140340300000100380603440380c9050f48143c8001c90341e0720084010b04018400041401c035505640d511801c1e0a40d000380615950380c000c0000c036941e040e10108462042c1d5600e94544c200302010021507109401070103415000707400b520314003c119038504d0301d95809040b003180c941c0c03c04406e140605c4001c0c411070fa07000013124654155071410000103511030011210315043d01c100d6070003007141c8105085980031101a006401d01600300411600c401c4a00843c10010002c1e1400742d812044c0d149813803480a0082e03142c1c95010085501e51398998646c0c1203070308000d040c80824864086840000d000d2104140040320002405540030308120782000c4004000601483c0306001c0a9280d481c00104401c0d403004c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 231261357 1250 231260107 231260119
    0x1a030c1c0213030201020d2a0204020f0403052d1c030f11031602011503021012050f150103050403080412110a080406090501021618021b0607030b03030f09 68
    0x224400c600d0840c03166409444031018804104010707501a032405520940707000740c08a0f6114401040111036280c81c00b404d101d60b04c00143c80712100c000f039407816100d485100402c0581820090744d4400c6c0d25070001e6105483c2c661001440c410b0144201c0c0300704200c040e000345080041061081c80e5680c40200103c0d078200c0745d0001104000e4a80700f40e00c865114808808180010900241d4042082d001a01e101980c1961201021543d0303005100e140d48501082c0708216846255400b0070911001d0403516001b4400741064083c0c0c110a02e200d080c3c4911424601c0c03070100c0c201407403d2101d03010350114460500d8a40070601c00031039002510030707a00a84c0320f01400c0f804542908101c0b0044061118012140f02e540402002c102c0a5000b802c00d0b01c40941c0d41030038040c0d0300d8004907a601001412900713126500743c17040c0f20700072180805503401140344902500d08055480c1e0040ca40b440d04044141c20340012082c0400340e903042c0205651048100c00840c01d00000c4034031072a5600c0392901c2517101310 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 231262607 1250 231261357 231261367
    0xa020c090a02040308121501020c0f090403020f060106020115050108061c1707060203041401050c04030305030405070b0423060307090509041430070b010308030a0b060a021005011a030c 81
    0x101d40754040301c1c042c40c2d02c03415041c0c0b40c03c055640485495419075403201c10015103c010100d5520010f544039a0740d1006140036a015515070901400c0c0001810a50450152070110084c0c05420003103580201031950000460054803940e50518101e203420890402030008103110407580c40381e00741c2103940451385511707170190341516143c04a076540320101d000141d03012415100344034850b400785104500520101c240714030814550303402c0f81c00488805401d80814002400400c1c8120060f40d40700c1e03c07401c01c60710480e84521408820b500990300040d00e20300040450080400c00000400d0404029a140b40c118200301b41d0207009400a030050034020f0310f600e4005424810f481c3d0000a01100ea58252045611084408904064000380c083d2214801c1092100044106001c84243c80d1700001240c280b03074296640d0f0700c069800540803072410b0b0b48078000100d0b5580c8540042030800c00c15002070142c60444550b1805680c4141c1c003810050340c0c0140d060b05c14204940480ba8000c001c0c1c1e200e1a80c0d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 231263857 1250 231262607 231262621
    0x12030e03121e24240a0306090612020a120f1e0501060b0306041406090c090f1504030b0f16080403020f0607020609011a1f1b0609030311031614120915010b0a020c09 72
    0x100070300e9211021127824144005071600c51510725071041c9000b91080a183c5440c4e811541c10305015001c000d29001c400c80f40b040c0490f10301001940c0c034803c802d9130701c1000c0d040c9031074a60030740d0b81302d42103001480f5002080c407040d85001e01c943c0d41e800d0381148448031586040d40019100c02d100074102401520f00066014003580c130060740c00103035140201403101250284806074001c0d002400103c0f500d20314030011070503007031140c0c5c0050f100d0100640e80600c1400c0165040742d400070040c00032819480b952b900880c02c12410303c6000d226a881d036008220300c0c0f9100100600b51214801e01d11003038100b000020365561070701540800d03800c0015031650349409103403c04490940d03808209e1444d0358502c4840804102d100d41158007014000d94062000300c200c16446540c030711041d81c0c00c554020101110044490080000b40e003000c04c3c0420710740c240a407010030600c1c1400104c03411099030704500c02c40c1d48800c1416000a01506004d0000d9043c4661000c01070350352400003000612070f1441c04006840 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 231265107 1250 231263857 231263861
    0x7020606061e030a0c0201060605040e04110a0305010507020a0203250b030c0c03070c290702130605030109060608010501120305040b0c0703060e03030412030e03121e24240a03 77
    0x1801030b60440055a030b29104003407000502c5500031110055082c1840018040d00c100203070380544404c00d0781038600b500e407030381e8888441d000f0700c07540c980100100d01e00101041c820b10070704e1b20450700307038002e415150694410182030482040690b0813103121507030300680d45c0c400440c803071090728005c0380c0b069501d4031217841015107801500700000701403000003640c00030400381d5a054012202c001c03922207001d46015000c0481c1c0310954241424400080c4030750707000741c681a00c40c05005000c4103030004140d83caa1001c00d0a403124003e040c0d600c40d0300e400c01005036000034071a2900502078041c49881440007950010100d10603841110900310010070902c0281009100c20300085600c841d013008280e500844c00d81c0c99400444050740c0c03035510b01103560005070090056101819003c00607500d8070400b41138500d810030024100b030448040c0d110080219261101d40745028140307521849c4144405003031000b480d041045c034081d001e1040540d080007040c040101d00222a9107a1690a0710351125080c1200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 231266357 1250 231265107 231265147
    0x40f062d05120d030c0e01140a090801230112051905010e030a03061508070f0c0302030906070516151e05070c0b030a0612050a08030705070b0109020319050702060606 73
    0x9400302c600c0b25810141a80001c9112030000e194400f840302c0160f120054603405100742d4007a0200c0c5440520803004004d2000800c410341d00c0b0f04064000315240ea2030325003101d0b14407481d000010074000c03004a1a040e5190302034010019507000c03501d085810b03540d19823038010050511504203002c00b040c5081103030039001540a0b40c3c2d460100c9032a103000c400000c002d821240309410092090105484101d4032a0b9589807040240d03445100d441c410005085400d0055103400b038003140024400b400c180d03541e40c002450014041d00c002c00c240b0f01d0421203074070712021592000b44051204000950f00796004200040c2d80600c0c3c03822002c1201000806484901c1000001041e0071040075010130b004601c400910302800a288003084002d03190080312082d90030441c0050f01540c00419103000042d0340d00e0013075a00c80ca00d4907000c0d0a04900c1c3e519107146482c280c2022074080c0d004004c00281141c40c0d1004c540291110005102e1414030030710294480102400c1e0700d002d40030004020703590f504001c011407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 231267607 1250 231266357 231266359
    0x9110403050f1f0902030d180b03010f0504050603190803040812040b010611070b07060c090512030711010e0f0d03052218140115020c060711040f062d05 67
    0x180d450340c1012006034540380070f903030000d100c4103040700142540d41042c85420a1103a010f030090203030107090079080d00d5041301c0c80401e0911041c00c2c03001081c950f107000040e5000b402080207400040d0308040400c0262040145014000d03401100e031a00c001960078071986000c0e0f0041640350b501d48443c1032580305807081124500c08800b0000c00d10040100018586040303502940c0e420700c2e10802e240b100e9071280d420744a680f40241040c010100480c0c8e0580c000740300c0d11128141524504c0e52740010804440d55040321450541020903800f040c050340000c0501694024600540d0040080000502c44031f6003a141c5070042c050b201e03d4500b050301030400c44600c00c003410000c9031765404440320420102c0485c040c2d20456840000501e8040146010303000100710041c5d0048c0399a82091113010b61aa001036021086100b03507400040b203500c942c40141800da0054189801e500d000c0c1050100360b0785840003555201e4900181003002001411183c0086c81100071000c0c01c404291900c5042d51020381c0000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 231268857 1250 231267607 231267613
    0x11103071b0c03030e030c0901080309010e04180506090f010204032307090e0a050f0d02032d030403080108010c090f050d140d0e010810030506070e04141503010b0f0a0911040305 78
    0x203c2450740280204202c48002c4089074004024141400301203d420300c1140655031007840344d4a4150300400180c00a40006000050303c0e0a2807504190803d400c5401624070b50095014001d14a20920500c613084034884000e52038186160340d2040541c124018410441106114440901e40c003402207200900000d4018404000702210a139101c0c03845950485003841122201289070704042100906c1c41c5094001e5806c2020303401d40d50800343c42c502e941c186003543d41d43d151220017001c8000395000b035000c1d5a1f4581550b0400007024212070103400c0c0d0b00c0500c0605841008803214002d1001c0541e9004d482144408801c1c1c0780c24028842c41d2041000726004480346240140c0e0300400f0f51000c0c90090340c40f6029911003803403010540b1503038000907041c0d80014001400141c010103004548030006400010b56010500c111407041e4010f070750103050f6000000c9813103410b1900b40100c00349201c08581e01ca01e024101c00000c0c0302400310303118120040c0d4076985046081d040010a070b400030360300300c815 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 231270107 1250 231268857 231268859
    0x7031e091e11030c01021504300306030b090a150c030b1302090f0d05191a09010e06180606151905040603061a0711040615080105030609011103071b0c 66
    0x10340c0c2069401228041e10968009544e1503200240d5030014114002e5040800d450f00e4440e83d030b80010300001228060078100051100903920700e5070720010011554000380703042c02c5142c011a5900b0140848980340e202203c51400b00329007040c0d14a603510004070000d030b0501008001e40c0540441412691711254030507921140c091250001c00c0d50420441325200c1c058002c000b04404c43c40b000714054a40d500071076001c3c014020780080880c41d41d01645007102141554100043c01a40854000e04281d4494240c1c0000d80700400c03032580c1210719a500ba000103100c110070550b444200801492103001c0f400700c0240040d807200d088465403440d10b06000e04441103010043c00f45e0b0b0141c4140c50010340740000024000003151600003060303044503800d914200340d50311851208280204299440703641c40798001030004032541150790090160319a41c0d5a076162804160030801c000704103420503410103c190b1441d4207440102c0740d000d800c43c10b280000e0400e0071134200d0f40c40b1080d04010418000303200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 231271357 1250 231270107 231270113
    0x103110f030907050102030f0d05040f0804030609140f210d02030412020c030a031b020a05120706030e0109020a06180803030c250221010b0319050607031e091e 70
    0x1548a80404801ca031005642e03038004a903288101ca0300d610b101e2234207005010600b00b180e0031003a0000d0081c0f440d070740e20200316110290554855801281c10540daa610324041018402c81e405030605414081c1c80310038403c0300255101c0480301c04990358000c840804005d14908402911402044140304641300d00c3c0602d0035014000c001c028036000b51007002d1020700c0c00c1c81c0c001600d5143d168103540d0b10320003400c0c10f00000b114001890049a001c5505080460162a0a0b4610140e040c10710000d00a4500e86500601280d0381814034070900e074102515000075885100c80302c812106d5610308482000079507a408290050b42d07810160060200000740300150340c5c14000740c42c022254404a640203202c0311001c0c884540000c0000b904180301d40c03031039490301c01c401950b880c05a41c3e020011030310051507000241010340d108219031700b28244c1c523110001e0000410144d42c0c046e15034201084003040001103807a140710704484a01e442905d030ba5260b42003100e600c040d030016030b030a9022288903070520b00d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 231272607 1250 231271357 231271387
    0xd112407030306061e1713020409080315090402030c270108010c11160603020d060e090a030810080604020405040206041e1a04140d05030903030a050d0f0920010311 72
    0xf01c80d20300050030410159180d0f0300e44c04170080070340c074450322008110b0401c51000b040e000401000003841490b01561400543c413140078100003140320b808156130348e28040061051521124010034010386c030340c104000041c0c6000031202c804807011605c0106203064002c14186a142c0020b10303200040340c2d2400018005015000441c0303501c0346444180c0120845000560f44222600c03034005280c1c40380d8410410507009600904501000c4080800e012380c5030701150a8119080e030b403a084a41c0000c184205041c1d0004034a50840802c4944180d0b80703260492040d640c00700640068402c60b41c03000414110361301c510440300101a180c2c00e1120310070010261044410451044a0313a041d995681c007a01010200100c1707007503987c500f03060390361644105c050002080d04028210303003e00c01080720340050b642c100040c1039150300655629585926400c0c518060b1284040c0580115040105e13210000d800d82c4650601c00c0829041e50404c2c03002e0400403000b070032200038a2090781d40000b501a040103824 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 231273857 1250 231272607 231272609
    0xb061c0b030606010e090604110d020403110a050109050105030a111903090302010b092710020f071209060e01030e150106020f010e06100b0307020c060f07110d112407030306 76
    0x4606642d503540c0c42c0c00064590010b041c4004d0781c0200100006241072401c1d07030003100c985907a10405814451842c4c064400c03680310b5041038480a030b804150040c5480c0180c05031014000a2038540c003000d1802002801500014010f092641e4548444641005880b41510900c5042041014090100b03480c007a0060100701d10550040d42084a41505424042d80c428080d21021006918407074503864140d581e81004800b0300c07028058013850810381c0d1240c2c0090324a5403070303018000341d0314002403810400c2580345082e000288040400104120364001c076810075007001c00c2c02e020655962800805080078000c450399142031460100201d01c1c10790014504130820f035810000c1081c0501c1c1e4070400e580e400304403039032815100c041d14240804010300d0301458002c02c1a00485800c40d502c000098103a1700110000300b01118003103200c0f41803100d5618014510001650720100d00a03850300c81c04000245a10b1841c0201c0e00078074101c1060443c08452900b11021200380d9446628a14009014042c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 231275107 1250 231273857 231273859
    0x12030c1206080304260d0e011b0302030904020d0902180a1514101101061d1602060c21010909020f06030f0a0903110607030c14090f040b061c0b 63
    0x100c0c88042991000c80c1c4501c00699980c00001c504080c17400072082c03403d100280c040100c0c0208040010a605402c010f1009044a1030300c0307014174071125030b0006110300e912000c048a0740d68068800c0004c0b0f90080201c801c101c030280c40c050380c1da07034412000c44094158828003e40002d0701c403080c01000d41f03000f1805030086c0341d10b503c00c0c004001e83c621005d020201c0f07400b03000107030401544803401030302d42114050b1402d105814038105800f10380075501e00311005980b1070b6540131100703524842c0506050720f286a20003104002030140321040c1c48029600ca02c014072040c0040c0b070010b071200201400d0741d20900e10f5406035003058215070712420184050b09041104070700903c83c0c6519800d0518181060321b101d812840c54144c007580d200706512024180e9058150140450100c0310001d0324001d101c654807078159600d0118084280c12001088100303042003d405108040c0241e04803a5180211012805d5080b900450420b0300701d40014014030580e0032190700421101035440e0000050b80190074901f02c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 231276357 1250 231275107 231275117
    0x515010609080c0f060a0311040b04150f020c010c05071502030405040c171306060e0f060306091b240c0706020f01090f0b07021f020c1b030a081612030c 67
    0x95210101c80d80c1e4440002819804004c0c24011134860500d80e0280010003c2441c010840542c0c14401c880980d0043e0421171915500140034001c4603402c2000300109c840fa032034240c6000c02c541c00025151501125400c2c1040a1041414140308040143e04042e1141b850000240c054000002e0341e01e500620405018a0034210304114190095000342c07289184e0000c540300340c1d922011007034850f072001e680840301c4507551140402c0030a012104075220f0a00c074280e81d14076051080404d4a0007200500c2c080595009a41c6080b98440542e140c1c0a1b0100603181c035405012000a503e0103903981242d0070074020b50114a1400744900003920788103c03065a002d840f6480390100209003a158005d6000c0c01e800c008003a1580003451001c4810780c0003c1034410307180c1d0703840d003507444850310384500c41401e02d4a03130003085850040e0303410f01400465072520003800c1c51141900d40425104c46400c0c20113001c0e01004a400f03d00d940601c44a56100760340000c00c2044c203140b29001500600724004d0000002d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 231277607 1250 231276357 231276359
    0x106030c051504151707081f0302030c0f03010e0d050403210206040f0812010303030515010516120207030506011d090c030a14030d050a0501031712070e0d0515010609 73
    0x10802100344007a2484004040d071503e4140a001c142040910001800f00420302034444030041120384520b0090b01169a0030301c03503082640e40c5502c20819100d642010009013079003000181c0d4001282400070303205941c90707643c01a0681c0080d0052120000301c078824003801d030185104652010041c41506e20801001418070f080c07245201028201041450140c1d0143c5c0200d0302159400c010300c103c19100702d01d420714007000e01c0341c07080d1480c0b8203a20490200c0c0d1640244004143d070200e000c21460002e00e02241003e01c040849608011010f0020388640b4062040a09403442804004007a64200040302c4076035950702e01d81c00c1c0d20740c095030400c0000c1c200310300400c401c00c03000f08084c80e00c1c44004000301501100c54a9403000d1070346e0441c034000c0d82c1c40200408500c0450314007503940710b524007103400200ea600d1820030f120320340d800881954007090100100301e5000c80b400c40c01e0307402c07011a2400c2c1500d0700d81103000c290300d04022031004e4954455035005081402c84035451030b068034401d036a4040c00c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 231278857 1250 231277607 231277609
    0x3080d05070f020d081008150105151305120c09010b0c01060501030b030636030c01060803070b0112030302040902030c07111f0e03070515040609140f040c02010906020a020106030c05 80
    0x324580b0300b00701c0068010000e841d1602d0711414401d40c00c041d5140c0220b1000c0d907150007031450021100e402e505640c4105004000c90300c1c0c1115203060000c464482145071403014191440141c860703014841c42003284891016454104010305807220f4006001c09006503140d540049194000031000c414a600700100411254401c0c0a4804040000340041c405521754120080d00f950120684402018039407a00301595900182c803c0c40c80741c5440044d541d58070740301d5406801d44a80750010031a40c2d004100f10000174400c58007907030440b11007075608000900a803908502074800c1d03074040781d8030500210078052810080ca0003030030700511602682e5203402104041c4040320329004500001900c1400403c03101ca0302640d05c03101002c10040c181c0c0c00c1c03d911000010f2290030200085480b0010100e4240003841d0000c101c000500161003004500c061200c00007440011102c9440380103946034104c42110f503000350440346100b0f500030400c0d9210308520400034006d02c094842900c102c41c6d085000111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 231280107 1250 231278857 231278867
    0x304060212091b03070f0e040317150102100605061e0d1d0d08091b01180b030915090703111c4e090306020c0114160e04110903030403080d0507 63
    0x45645c106e90006126191900f031860018000300709909004501c1c40d000e80d190311410613113126250809640802030552000245843e001c80d40b400703a01d51514500b4801d0703580f40c8041d1541c5035032078444481501040c6050024500426503000c9070542004682001c00c00030030354203604585108101c90302c122500c1070464104005940d0003501c0c0d0400802000b00150100000c2030303006043c104034250491580325802c044005030702c007004c0c1600c040103100d480c0805010080c074400c8001c2003c80c0a0908a64042e1240702c40d2000510b80102d414011a640d29002560b41c5094100e013582000d040d010b0404c170241c40300180c0f50b40d2905c005503100441c00340f00311454418100e820400b0202c0d01074824030031a07000f541c00d0404018085082c500200080302c0b40000d04c000703075142001081000fa241107220f540703000501121840035101511800d42c51b801215080d00d81400c0360049140c2d24120b5028a880c80ba0b0004203070503000c0007a010041c044150003c2c14441384100082204c0d68a145045030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 231281357 1250 231280107 231280109
    0xf0301021204020f0a080f010f0b0d0302150406180510110403080403080904090f050703060617100c05090a03061e111803030f0301030605090d05130b0304060212091b0307 75
    0x5050801400810058204440801c0320300001900b00c10380d50340c0b02c1c6c1200d40341000f1156031348a10782d100c07448481c0000712130044144161080d9100700c5070f0400c80c0e6010b5203a81303a03400c11500050168000409005c2e0340c1c1c10694200302000d0071284107840c02d040c0743e52503c810140f0269514102071001c812005110102c4040300e070010401800c0a04641d00d0300020b07800040365030360194a0303100b0301002c621801c1101d107200d131140004040039031542c5080004c0d2920b41d03201c0c1c0d0001b8902003000200f40c8002c186402c250003001c80c0068106516102a103e42c029020055003220303e190b00441080758552250324501130800c620702209031410030920584070b888000c20041441440100404401710700c54811190000701543d0030883d4008110f08150003d900590b84a07071035009103d556501030110240ca810b40e4a042071410401404551041407140b060401c0c0305000400a01408020380c1a1841c048035035400c00e582c0d0410082d010350300d0890441070841c1c0e05030804440220715001580c28 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 231282607 1250 231281357 231281377
    0xc0c030f021c030207020406051816050906030a0b0406083306010c0b100909080714010c27050604060905210606150714100c0507020d0f1a01090501050f030102 70
    0x40d03903001030428120080e421017602240c010384c580c00c1c00b2903242d43d11900d004070000420012541b510b0011118005001002c0c1d0702801d1220800c03070b00c105500e5000859520004000e00410805000e6000ca030041007194044070305401426070210200d4810300400308001d03422030b00010b04003240644455032035000c0d554107010402c4480410001120030841e00e50141c000b0301d06000d584d1b9940c02450642e40c000b50116500040060342d0340c2001041d540e440512048131000b004214141f03080a0020b004201e0001b1a0b03040042540c16a100c6c250030110281501805054031141d0380d001c044d02012080c013034148200c044035030006c0c0514104e50298000e20a03640104a2615150140708180f000000c0400107040304004850106031140070380c9486150030310081c00041c00c0c0106110886401403074150030003008014a801582c0d64042c51102e05802a1071120038811034900131010207090408004c010b030040000040310802980014100c4405030b03190107420503500101400c03840744040107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 231283857 1250 231282607 231282643
    0x10052215030e15090d081f0e06042d0e0a030804060209060f1803010506060408070e0c09030a0c0303080c03010605030a1e09150f14040615090c0c030f02 67
    0x208009038031903000200004641d80a0f611903403d02a81c204086208030b850302c01d6035025500d43c1500359442880c20fa40240c0ca84074210740700409181c0826501854420582c1c440340402c04aaa42d0b07590383e0020218061508103800d48510040f01c0c0030f04210410310480105180500d12200940045a1442e0083d4555a54200c5030380e00d03510301c0025003000c012aa004030061040c0c6200c034202d40000d128006c030503400150821031030801c241c29110001d052a0080d0f070b00340410040c10300e000910409403048100c000070316640381d6000d800d19000b018102c90f494854110102e06100d420080001540c0c041c1da01e4410035501c1c00020303510340c48203210341c000080d03081000030446640e075400440010254140c10010fa9070304038250003070b40c42d01324040c0e0307000d40b928050403c184c03168412100070881c4d820061090765002c081c2c5200c42c1000401c090045501d590b406d0003000740d00180302002c0d010302070041100d80b030310341c0c00100251800c0e54210b011900c04003150303408074000144510340f40568140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 231285107 1250 231283857 231283889
    0x30e18090c1f2a060f050105030706091206020f0f04030606060f090303031a030d03240803030c030408070203010f020a020c1207260d020d090608061302090f100522 72
    0x4220703401400640040401c000224543e419150b10050300e00c8180d0040c0d03008280450201c0c10102200c2040e4001d070320075480a2000c10141342c010100038122080c20a54000305040c904103200a4441c1d03006400300401c0000310052450000000340050364015142003140580f11403060b9204004942c00501040a1410030000680703e50043c00c4500c0406400c4a4a07074080400300340b5101d48980440e022a0f01e07180d0851070611900d4a007440003100020b40700003280391000e01c030713120711010f02500041e40000000406011074082102e03032099000c0d00800c002e00020f40d0980082d00103c0500005009800c6271001e2494401030080c3d140c5034040180c08420b1420740200301005d802e1440c4c000c81c000000140c3d1101d1824041070b54824569000342071281c0c81c1250080c021500e82d0002c80c144074202c1c080c00f0307070303611801c0a100144502070801039540070700361f00040c031143d4250f03280340d0b02c801820300d1002d0455104010b0007400d04522060b4004208041c81c88445a1150250504c0c1005001c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 231286357 1250 231285107 231285169
    0x150209061209011e0209030c0d02130b010c080a020606090c07170c0c0613051804080412110d03030903030b03030f0d020a0309050d081905160c030e18090c 68
    0x22a03a800a03600000044c2040503404482489251628001c403190341c04a03031003030141810700c258000a44116101480000d26038001601790a515000c1100302d940d0394500e1200364043c2e85040c80390350700040c00c1c94a032800424025584d1500300c41603400740d1221004142008100015240100d03400121003104a40020b903488241d0089a0a2a114070a60304a004240ca40000505600c0526915081018180014080c1800c0380b5034044040c00401810800811440c0042c0ea098449511010241014070b080c05515510041081544000c002c00d030a8101901640140b00043c4251002d0003100340c004201522030285000503d00507104000ea01c03881116a80200b00d500b00500300003c0b40e91864955524100380c400c020008684500305100400c02c1014806c050181d0390803061146142c1482525920a034000d0001c1c240a030031145003007010301400804840d45c0001d41000d100d01910060169a80130076203450006000390500000035044c0300c202440e00e4540d03134501d0040002500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 231287607 1250 231286357 231286387
    0x4021c02010302090a090b0306010602031312030509040204060f02010e0f0d0e06130303050c011406100e0406080d03090212011a010503150a1202030609010c1b05070b0301090915020906 81
    0x540032410503a00700240480c0f03035201c04481016040039080041c00c0c3c0f44510a0519010b01a040745056502c2800b120701d00c0c05d651440306d010303214404a40b0301503503500d180541c1d03e0b0185c44900303503106001040201e8410313449424000701d100283d0080c06540c660034105500d40d070000780305a9081d0043c0354036a0769280a00c41091401001030000e41c940f8a500b101703d4940d20b40c3c0c3e00210009000050460a501d0b803d00800d010b004031080000d4040c10441c0001e943c43c6032000d010300501001070000c1e0526030b156802840108030050a4416600d03031150001c004000e4903c0885c4191034050601810080c14824558800c01c440c0f00344021b08096001561150002046000612030f0740500d0030441d03c03020707810307401480c08806408509119204240c1422002040d10086030314203c0f0000c2c405600c4051890954241d9114028110031820312500b4100d0540000308a48800400080c0440095000c6000d20f800f070403080100e40c80c2c024400059110b50940b03550702c14010321210440e10b10380 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 231288857 1250 231287607 231287659
    0xd090605030c0f16030206010302030615030a060b0112090c1d010f090b030f010608031209030304230c030105150315010b0706021b010c0c050705150d0209041503150606080402 77
    0x4421802e184c00c500e90101000c042400440060700321000400460034100300058021281d00d15007401c01c00701c2400310b959041d420001800f55901c405e08214281d01815403215000342c920001d104050380384c1060340c0088501c0c801c14200c42c3e060890100580e11080d2424181c512688800848516001c6080c000d440c0e503141c40c552502401c1c181c080c280909110b4400105012409191a01c2d14480c06032040403000709031280c940c108000300000201148a40c203c0d0100c0220031902d0005080101c600e0a0070503030310584c0540c6420b06100f80407032411510f00000d0350440c02c0f6005038541508201c01070340d00f8840d0001c004000d20000d40080d80715005040c5104035085040e400c0c00c1120845421b5990100202010442003030380d48007800000e20041010b850141c0d00c2c508991070b42950440148131301503e8142055002c11000101d41d01c43e0401007042c401d0510701c40700035841741408a01c00f4044050302c501c0c0c5241c8100012104d000c0c0051034031954000b400000e0219100792140383d07107030b15 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 231290107 1250 231288857 231288877
    0xd200301090b0f250e0109050d15051f090219020a020102060118020d0c0e04060b0f09010503040c080a0506090d081005010c0c0812210606031306021c020304050d090605030c 76
    0x40145003032110084004d80c030700d90500390ba80c0c1e20408261a000500364650130742100c0c0c0030300e6814181d000440d590f260038243c6200d044800041550b1050101e00c810002e907521a031080000301e800042a07040358026000e440044107522070000403010702640d44a0200000a0160b00304400401c000504007094980d40e640f40c00015103041100b81c16101119064400749010a00c001700040f4113040900c903420203082103100003446e028200d100010035000c3e0b901d050341003000020004040004122030038009240380401c0350450301c8580b4144d9150101192001740601c100c81d4013007001849071020030b002d4082114201e8201c1d0606004562214500d00192840f6040c4640010ac0c4a802c101a1016070078002c042a100e00c900b00e80005500d01c0c00701c04400c050300600c140519030745c5d0401141d0f00005a00031038014118149041c03000f038000e040b684103207848401c110083c100055002903110301d00c01c000361641e070071424000751040015805010009079090000881c401d102400038040260303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 231291357 1250 231290107 231290131
    0xb0918040f050d0c052e091e230106060e12031204030e01031113050423040602030a060b0712050a0201060302032508030f180a050d200301090b0f 64
    0x1920b460745808152100d0b00d0004881015000a104081c0941040d40603010f822428241d40310b0388001400d50035445d0750700d41a96450400c010041c0b00645074040d84074900240b501c080c003130308116a40f898084281c4900000c444a807007100e2506125900584000392528203a00b8051014004a4070906030496040d210030440301c99804400150248914840e90380d50710001e00c110001001c0d51600c96045002080920005002a003aa00401e09480c400c0c4c0f00041c080142e150344c00c02200c081c161b01c81148a02000307110034400960000c5224250b03007501031046c565100e400d95220301c210280030780480c0c02e110b60703401407038460401001800d003c0d20000c151281c90340c0010381016241408000400d4802c038004003440c010541840041040304003441c10242e1852220380b07a8400e60021500795007ca082450841d690b004059000d40006009445510960b24054800c0c1c110a00300040c42841d2201e03030101880c05000d088407607a8090702e04402070729402140306a00401070001c0702000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 231292607 1250 231291357 231291383
    0x11010302040915030210170c0703090312090609050d03080f0c13080115060201060803030c0a02010f020f0703080a05010617091005040804060e0312030c0c012901090b091804 76
    0x9142400341110080f00030343e190003542e10310b2041105001003403484106000007100c0c0c0c6c1c0014044030108940c8842048846a81c502d1207250444010900d50030050107114046000050194000c0651068501c1d94880703071045d5071540104950361444020003400500030030000b540ca50b00e00101550400d60041c0d10314101910611800380e0f40c00341c0d40041c0c406070342d540183c0400d4024450240000c04490008000b0b580c20300400c0f03a203911000b030a00c10481000a0308100aa100758070017060102c18080c01c41d1507010318110307030781a40c1c0056410f40001c0d01240104a400c0282e118040c100d950b140c51b403412080301d0300c00d04504024010035603100d0b03002c0c0a0244500b0200ba00459104900c01c001003961182421405413002107070800050181c1d10110302e51060b0303400c4004481d0050b036150a410744034641045802c1c0500040004c11f140c0707000010240350146880768101000b80001d0700c6d00740a9640f982209000d0340a5040b0180e0700004002c4403000d031151201e24940c201c1e02845229441c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 231293857 1250 231292607 231292619
    0x1106090d020907050a030b061303032a0c051e0a06030f06030507060302120114090703020357070b060102120309071a071a130209010e0604050105030a0f1101030204 72
    0x1c8108030f58160202d8400941c04101903803520650440f201c040b00c0080c2001044118034041c807502e400004c081c002080c0c20440e000c000b41482000306040d04000b1040366003a8079088040719241e10445000b410007180400d1820100074480c2030480e805080317400c526207084003c901510300d0b0601c0400b21691001e000c00428414405607001c1c03c4241c0b0090b984d4682c500401c000134205900c5801c0440c85035101c40341c548e8807000302503042011481d015859440740c1d4418517900700007006042d071821082159804034004c0d0b142d99107000c01504d080ca010035590721180101140c440002c0c001a110801407040000c0d41640b616400400c10302c11142c079680000722503000b9500a03111414190b00841040050b58602200b400744800301601c428209a40307a99a02d504181440c01c9542d04807072040040c49201101d05003458070f0350010025003a03540c0d21681c00526520541d000c6008908000001caa141000039a000d1041d5004130401c950f010143ca82c0101d2003082c041441c1015020000095070f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 231294964 1107 231293857 231293869
    0x1223060c07060b090f090f010903080604020f16030e0901060302090607110411120105030601170607031e09031701051e010e031c080106020c040204031106090d02 71
    0x101d88485103080700280080c0610240c11844141c100003032201c10b420110300840000d01079032070071803240e0354040c2070300d6441d0406404150f00b1008074806052950041400000040300141400c0720000001e421b80c50b40c050540000e022a10b83c031001d481c00300040d40c010040c0e13080840c681080ea00108013140240c800242801c01380c00701b039194540f1035401c04203003401c0c80e40d03140e543d400000d91441d20011083c0030b558000d10601c400070480780c56480c0c103200d01d5000c10b4000d10b0581c0d280c440803400b404903c8426114065a482c00820880f803902402425603c00d40f00c4000020000d00c0882030080140e0000d032107504203140e080d1401d141002240100079080ca000c4030300d09096000301c0c1c41c04050141c007000803071203800040d8200741d11410f0707941170f20459030990302d6082c40310081005a00641c0009001d403500e08038028a540341c981c0040542c0c08001d0001f0660031816000101 = true := by decide +kernel

theorem cover : BRFrame.Cov 231115107 231294964 := by
  have h0 := BRFrame.cov_init 231115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 231115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 231115107 ≤ n) (h2 : n < 231294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
