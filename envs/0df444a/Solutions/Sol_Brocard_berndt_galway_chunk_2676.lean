-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2676
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:24:57.483985+00:00
-- url     : https://prove2.me/submissions/0467032e-f413-4632-981d-aa1d0ef325c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 481115107 ≤ n < 481294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 481116357 1250 481115107 481115111
    0x30309030302130f050339010c060507050d150f0b07020a21030f0503070903030c1104020a050c010509010606051c181a1803221a070302101b080c0d 65
    0x13480d03042d03a041010f2540101c0f8046e2082e41e03040c590b44444100150300d55141040340402c16405001c401d0716140c1c07605603460522640b6402e0600143c030070300c0313414810340159855030f0b12038107410072010544440d0082162241039244051080c070027441c0e48034044400c44000302d50340318190310200c1c10460241e8064050207165207646403014003020030351380d81c5500ca99200e00003489000802e41307007030100f5140c031400039217006801e00c0004d0055000381402401895006200c02142d00001c2c20703070380030803030b400b00254011a00b4908941d09009054000307072036800a1100c1e40c10000014024001c80071a81405c000d9a120b003040d02c1703045d9001c076020031044540005d0040c0c86050064404810501c855900e280c0013001407010070605040044013401030020354502800140d16660a860615030380c03094290710140011403070103c202d001c840c105880526601e503101c40c1000380c18244240b070361401d0181840f20924094424411000100e1400d05242c03c264070f6041803062180078000d540031180f8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 481117607 1250 481116357 481116359
    0x30e010624081b03040303090606080304210b04060209120303150a06020a020a03060c0e120106090e030304080306040c170405060907050312041a090a0f0303022803030903030213 78
    0x40c03035500d01041e2880350619200c55455140500300c0c0c503180125145824003c00d8450039407400c40401c000c64010b40285001309442115444400860741280d0001c021980002803c0207580544107a410102c01c01175040042c41ca0b2684500750700f0600148024602640018100720981d11003005561505c02d00044a03140c1c500900c1a4084180e04890903215031b4007500000ba2080c40010f404000507400b40003252020300d9681d41c031001d010b007101c40100b8855040000d91158072000d41d000340440c074400c00403545525000c01a01141c115030040240b5410420400c40400c1100c0100d07604581c1c19240054100c403c40811200304050342c017a2100707004410f060200740540041d443d2b005280050544201c183e8401c00c16a581510030084480d9400070f00040100100d0038540d01c132407280074190207140c0328840c0300041c064200303034000aa0103e10424240203141e810841d44461079203501102e00c1c80c0c803e0b121900715a8000441c0202055200c0ba50001094840e0701513a03440e44120070b69000003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 481118857 1250 481117607 481117619
    0x3080c0c0718091509030e30030403060e030c2518091103061e0402030c06040e0405070e0709170a0606090b15031303110a020d12121416030e0106 64
    0x10b004180c2091302d18040865049480107100e1060601080c0c0c5034444450540f113031820702c4032000301804c55170b2601c0c291300d8210300c1d82d0710700e000589040000754028541c2c8030b00b585031280031038941c003810002030b034420b02058068010000e2247d00e05003260011017800c50900400a1544005400a003441450352030340304d003031803000d4101041c11841a503200d840d80c9848000d041c0d80c1d007400c4428180c03080490301000d03490306070043e1240e00a4006010303142400f03000d001041050340141e2005100020038030811080c41014800c6201510385030a5200391400d240c000142400050300401442d806014050500b240701009640a02988648180325856807000a03500034040c545449005541c41101d4004250780a82180c0c880d60224802d2844c1c0e030710703644040310340b1002440040180e01c1484500405640c1d00f1001d1402c4030701c921016009018551030041c50402c10954844a0600300000c5481d43e1290208030f0b584040030017000c1c840c0c01c0300c42c1c01c21005404d2140c0400301952a112000ca0b41e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 481120107 1250 481118857 481118861
    0x323030421120f080a020c031204050a0c08060f010303080c092d090103021f11060a0506100c031e02031c0203040506060a0f03023c01080a0903080c0c0718 68
    0x12600404540300000a200d00564041c460110f40100040e1407500140c02c8140c2e40d4090180090785404a0341000140c01034208207000c00d45059801d544145031080c2000b04101c00d010283c040da038007a1900e41005000c3c842c4404060200906100c0a000002c01c0b0181d101c06603610142d0003448095040c8103030b4103189110100100400c4020240d210007600c1d0b0074480c1c10300f81281d80c0504046c0c0c0c50152444a0511403006403040e004100000c201104200e40400c401406006204400641d509041c800c01220740b82070320b00d600600810000600101e5000400c20080d4880c10320034090b842801c0400700d007140b10f040e5020f241d91000a00401d00c00c40c496011b14450351141c02118980e454000030480c0b0190248242c1010040100080c030050804400d10070700c07000a40d15000d03032005d0f120400050381035080b40c107113925005892816155a4020f01c03083c2c00070020703402081100d9954500034103082e001000390b04c6150000403100000042000000001d00c1c540e80c41d00c201114881000700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 481121357 1250 481120107 481120169
    0xf040903081902180f0114040b0301090b040b090a240602061906180b0a050405040506060406050f010905150d020f0307020106080309010c02010e0f09100503100603230304 75
    0x5080340c1020501d01c0154401c0c4200c8120003130715a12403030411000d908010100f40d00901260400c42c0304561094040800030243c0040d107203c0340215140d6040c400c801c821100c0300c11130b00744100d042041002c03181c1c46609c0300e5600290213400c0850340a00e0010f038200c20b60450890810310440c134040004d80e07264046036180c09001d5055801c4508907016540c20150f03000790049800c07250790a0300c00354244041c2e0740010000351024292400c0305036600b0010f0121071085600b42c0305030700041c3c10480720386400d118150140004403202d40320380d040c0308002401000136002da00d001340c202030510700040600c00142ca582a1414000355503074010160f030f600d001d400640345017026600742000821240004815107400b002c06a45584000145800445550300c03030000142d00280308807007840c05510703482c10311881848140240071020781340100f490700d4100300105081a50345010018070001c0d4004464a409075400c180651581003403442d918114442c56110000642003004007aa49121400040c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 481122607 1250 481121357 481121371
    0x2060a0203071b150f020f010504150b150405060d060905041b0f1a0306130c030203090c01110309010c171303020a12051e03040902040b28020a110f04090308 69
    0x44140d0321400c2e406044460b00d001c2c20b13005256012507407510320720070758021109116a10440b074100004500541c2103030805c0e2010b0300c01e2031690340c0b014442a018080c046900708161a0310ba19420302c0c0141004901460042d144030f1400040c4004000585810120140c403280e0001c0045060501d00916060040c400303540e000900c1000c0000d500e440c8003a1007003115416129030701900e00062240045503c0181b206610010141c0200c100b40317814484e500200b0125180180d690400d4407001e0301e4042c00c60f0049042180080111040342c1b804000d4944500003070038001d540301d11600e02400e1a84800031101c21303e94001c111134144402c04600312085900aa411034020b940f54180309107010113070000034100f548014007003840c6250701008000081c02070010b4905154641d00c00ad01668010342c0103406288011032a80242011340148070f006c030649010342c09050713031003007406900d40030a150041c01610070105401c100b6100c5403000c4041c0b40d00100208140419454040c040b000c091b1042 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 481123857 1250 481122607 481122623
    0xf011502010e010227010507120c020a0819050105090d120c0c02062706030c03180705100302090f030106050d03080403210f1a011706060d050106020d27050904050a02060a020307 78
    0x1d805c154000c00c111001d49400082c0711404842c007203400c1c1c03000e121440040342c201407403110024114009010320b0700300d6444c0b10a41d012010041c20701c142900c1c0064022180350304480381030181a600300e05802c0c43c1c0b02103407074046800b1251680a40b889104040c019410100020f55180e003041c418041c4a0591800041e0001c91a034005c02d0200324002252551450720040011540385003800741c2e01d8803696044421120404d03210404540c0400c1c0e038403106800300703401180203101b51400a03294502c400c8141e00810206142400113010350114010240512841c2c40124083c50310070740541e0141a40014001c0c3d8030341901350b048008144420703100c00b0144c41c00e1849054440c19498035540c001c0140c0d500800712511003040b000b41030323018001c0e6512520400036800c001b11207008203030007040c0603009841180003482c0040d02203a507402d2610584101402500142c60076802c0d042c0035241c080d1100451903499142c60f80c600392540101075402000407984640c0c10f90700000400c8040e1040d0b40b4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 481125107 1250 481123857 481123927
    0x40f020c0a080a120c0504360906200304170d1107030f08040206190e040e0f060c0309030a0309020d0203151005060c0d0c0201090e2d0f011502010e0102 67
    0x101303500b1a15804200c00018004200801819a803468800c1d40c15038146103210480740201001c4045101c02040c0350101130301d07840c1541c1400854810041c042c1c003000140c25480c02e4044400ca40e5101c02040141064110003007003110f54191810f0f20410381c245001000351018808540d00150087e120031400074a62003000300d4064401e14680b4051540544407506105100340d801e2503503088100381c0f00030404d28070a402e42a0756240038a00b82e16445101828040060b002c045051140080c070fa002d0000b002c005101100344008221882e0f400d440c60f002440d5155480061000c110b0f043c0042e603d4072403858600690000c01031180d00030390401482c811415994410301095000b1104518141d0700152504a074180c094003844154600c14500f0760004c070f450700c11512400e0802d45002004942c802581303024452003e90390603c500c4540b00e100814034010084010040d0305014001c0780c0910a5506001076000350070400d030f07000e1050025501c9190300290f91542c0f104651007000c10100d80d080c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 481126357 1250 481125107 481125137
    0xa021506030c130b01120204031a070503090c0409031209050706020c0406080c091b0d0f0506011e0e041b02030310120c031103030403231006050a0302040f020c0a080a 73
    0x2520802262025109494850300d5403c0e04005101808166044c4000b1040304843c40c4120702c0144040c0d07201c1d580032031aa114108000d005030030b005001d803050020420034000c1c552400034421203440421107011485860915045072001c1c0d400741da004406041c030b4030075800c00c440400c0c4036050760034640c01c4800300c1c0740c24420001660703010b2058070041d030002c90700c61915003050300d2807542c4000345849001c20304030180150200ca0340400d5015402c00d030390b84c81045a2032001d004050f0400c1d0700746040c0203103a001903110352485c00030180e2501448007010b00d20b44503403142d030811007025a002c003405031001c1d203403603000e500ca034000c452911311a641080d0100d48080030b100c00c0014140c01c0507116120b54107542e6206080b00012910542c184018040000050f04c10b84a0712440100c0c8002030009000b010303101481c105a05500034000c505080b02400a503c0780402142100e030101d90218114484085d0040248501611100180500400b610a00c45a40c1c0102150821030752a0b0700c0c0003580c0a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 481127607 1250 481126357 481126363
    0x20d06020c0f010c09120308150d12031404080415030e2410081e030903061003020f041e0f140f01030201020d0201050c09060f13060815030309030a081e0a02150603 72
    0x300941461b000c8000c10710002c40e1046100c00d80c4001c15484060300c104003140041c14001003920200d8400c02c0890151b081c05a0600400051145040c0507a00380d007401d43d2031170071a0003079001d1921040280342015201034400d401c03403103a4181c00c005a4207003113400c95002c6003491500100000301050340c0041488418240848400c8880c910003905a1607074909507040c100140341d40201c000e100500c0008815038013449032034021511070085403690f030310b14030512181e4241d02a500e403056107000c608e61020700c2040300101090400e24000610309000340d900c1c0004041907104234041c0e4280000b0002e40c01074107010039050ba4001d07002c0329050f10b0038110881c2038620846090141403801c0c0007400d5141058009031070101c0c641e140c0b0504141c510056a50078003a140d11440014102406102410076101800a82204194095441c094407040400d0b5141450300c0001c003207440008202c0d00d1201035021a0712000380007001c403561071510180c000d42e201c00148451680701100008158240703000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 481128857 1250 481127607 481127609
    0x3060302101110050a05091207050307022e09090f090b01060827060603160303020a150e030d0f0c0207030804050d140a03020a0201020709050f0a0c050405130213080c06070f020d06020c0f010c09 85
    0xc00001e529200e533990a02414507642e64140740c9040509402c103400604441810b40d00075002e41d01e503000c6914103016881503856802c00e00e80321515140131403000c030b0860303c0c07800d055410b1400c255900b0380302e10072000f4441500f0b0180c00c07048130b000c041c0c111500d01c02140d01030107110110111990011080e1803288040510712004000d640100c42d50800265080d4109407040c10201c000101048004d5460382190301600b0125003d60351344807030301034280d40c9100c1c04000d120035100400010341107940b0001c1620480c043d03c1c0c800d07070340940008100b2805420780c8104a4888050b9084402540f5020355a0191503008a001d805076000c003060607a041d109962144c2007070780203e002030b11a00140c1c0010034407580c1d004200700b0304003c041035a480c1c1000192509407202c000507a100c200020702c0380580302130307000309496810003401000d00355601c0050340c1c10142c11103c2c00f40d00414910008002e54a4004000e11309800426036462a900c0821042442040d02c002403054003040d40b4229411459 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 481130107 1250 481128857 481128863
    0xa230406171f0603050604110c2103150d02040b120604030e060a080c0a1701060e180601080c0d020702040903080609061002121308150403090603060302101110050a05091207 76
    0xb4400003000306a110350042c1d908410003500000302d00e081c21100459581c01091400c03136179440143c80040640c088101030340c0e501c10544250b401c5041202a001311040d204080c00c0c410380900c0004402d640d5a9444a01c1100300184264103d00c13000c1007040e10780004540590100300301c0e00304140103041401c125601e01040355102c1d8034a40c0c40100d44420fa401c02e6100d0400c0102400c80b8100c4d80e080307000807130b01900c50781d26015034144017030b01084258003050510b1701061549405110301d076600455115000311620340502c0e240c00e424001c1c40300900800e180a50306c242400c00007000e05420020190085900b43d9040c0d410351768240600880d044003045480c0160f20142c50300000c0b8524002030511039100b160229039032031b03031a075195241446a014010311120b20f407040c03104041c0c01c541994010203ca040901105146400044d031649a000390701c001e002e034850381280c03c41d1040c40385c1d0b075603c0210f6004200030b041c00400c1c4002801c0403140d5007124407415800303840c1100960160346a1a0b4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 481131357 1250 481130107 481130161
    0x307051f090b071b020339450105040c0e13020309010617100509070e130c0e090c10050f0d020f0c060a050610050a050a23040617 57
    0x960450407504101c0e8030300c1c03010008282d08031080060346d052000d60380c02000814011240c00c500707038035480c42800241c181000d41c10b6220075015151a0071103031100482045812624101c41801c40301504004000c40000031400d0740d44403803e82d604e44c410a030603580c0c250b40070440e40f0310350340c415038901840290442d4046090152900c6402e500d800540d4801984400840ca09a031903490030030344900035a90102c2d036003002014900300403c0d44039055000861400601007589042e019508148010700303508845484141100c05000c4107021190042c501450071006620300740015507102c14101c00124402d2880d05c00341e00b10300c0d1060b000c1e1400008030380c031100d14004d9a41c2031300c4001e42c40100d01c4801d201d014821200103d50602046100c1c4400c00c0c000724880ca0070104110700400000b604100f4001c040c08002c010a50140550b1aa1600c50400001256503410080840600181c00c1406041d00290100d00190701003070030711030350b02d180b10388606503241d0300040c2c0b1004a0301d06208c21800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 481132607 1250 481131357 481131361
    0x10303121a0d080c030f1c05010f03030f030902090903030709140f130b100507050d02060f0a020a0306050a09090c1203020c0112020904110414030a02060a031d0307051f090b 76
    0x45881d0b60035042c00ea01c641d403480d2034080300003405400c2d50007420801c4441200410f4001c00510011940b010400c10444100322942c14580c00441e51a61b03804041c040100d02c00b0190681d500940c00312000f9600106103021038540314160903500c1c0e10803108000040c00d554000500180f101e180c400080e0300007042c045520140f42c2c01c2c400e10f0240602c4d610061526406408001c3d02c810742a8844840d4980c0c4481c1d50b6030355410001d14003035054011030115030086c401c00110050300e0b11060f410030042d400269541032038520032409407c007038110326844070440600041e60781107940004405ca1045804108a6681d80b46501981c55021409000b50b000011300d0703003003588209080313034032508817450042c01c0060280c00304084a40c210811480d200c03000a05001c2402c403d003520080d560700320010483c0003800e502040d40d0380100b07400b2406050f25060303201119449400c1d907524001d04482101c1c0c488100b400c006035a0106a80010051481c0b0550000c4100450003840502c0740c22503900c05542d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 481133857 1250 481132607 481132609
    0x30705040905252f01140a0b010f050a020a0605090a050d051b06060f04150906060203092b02061605060411091807060518180103031814120f0307050105010303121a 72
    0x100c2c04d10380807581d155607992003d00402111400f0540140d04c0c540c400200007264800141c15071040360295010f2000902291074555800944907002e203920801c0803a0300d464640d2010b24103070240703000500c00c2c0140301d401c1c286242e0040c0503000240f805802d00400b014088002c980b0f0b460241c07501500072042002d03c03038545c2001c1d0401c3e001100615240903072203680300082c40450310903030085401030704000b036240700614000c0d070340402510324050020288140c9100340c429811b401480280150404200010130b001c948240c1021940c220b001d48600785414904200c002101c15440c0b44602e80c00c101180551044c0c0007150305c0c400300403006020b10f0341403600540340c80e000803a51030302880d54640e1103090f5403104000c032111074a00300d005203090f5044d403a000d011000c50081d1040c40c100f000008020180d8201e913003000003d810707a401004401000203040c100140c0054082891000249840401105512580c1201e01a90314a1004420040355070169804c480d403064000e0108400f02e461 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 481135107 1250 481133857 481133927
    0xf04150905060f13050f1006060809030306010f02010b100c0c081c0809210d0f0b06040302010302090a0b0403050a0b0916090c11060106110106080a030f0503070504090525 75
    0x19010f01c004846481c156600c517031406032406025040d80d045440001f0a0400ca80a144085e201c1810130032a6454010380055807030100401940c10020080707003201e42c141c001c0d402002540000b070190030004541b80e0024000036000c0c0012a03205540c41d400007415500400d0071032001c51030400f26248215106412a801000075009440c50b00450f1444202c1015331110226850341100c02583c4940c0e000c81104101c030095034103d09004d06180b400030031940d503181150107503a424200182c480c0b070341c00d01241031742c03509411110b01d910000401200f4004005500f0501c94440c4038091401c1d40c0c1c1d00c540684509030002010960031a0302028095210240c00c214184070b002d192a03070071980364101c4107180c4042170f8801c50105101c0b40407007040e03d0080c0103890160032484020b003240102980d004080f00b94504040342000404400300c2d85003403241e011a0001e0051200c10301031401e001d0f2914690f09218005004902e1100041c50051805041190488030215600091840001c035103062 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 481136357 1250 481135107 481135111
    0xf022d180108100b0d05040201020d11120a030b030607030b130917090301020910030c0215011a031305031903230411152701020a1104020a0908060f04150905060f 71
    0x18140d091031003c07913203c05140c09040b81e800a06008226070919000290400141d1001c00c010490901490318042c000020201c0501045680d402e90741c0c819034008400614241d000c80b5810b0052106001156515401414030658100c4800703101520080c080e01c110b40390ba0400070043d605100480003070381c2190703001d801d450401600143c90b01075882c002030455019020301d100030036910040c2d40703403440c1d0400810a10072182c00383d04038203504041c1ca2210200d9102e070501c0488100100252081400d05610b042e242e07400300407640c40c0d8003100e8a0780c1084004010600009140145801a0312407410001c6a4540241140703002d549440e126540f0550380814515080388801110002c120403001c001c000300c11680201c100007490528100010100e000c0c1190304543c01064200045081c4010350704802204643c01070b40c41a0100041c1c444204680c04965a8000e52040080003003034103101ba480386120b910034200042c1803030032903000c40380c045401800c035520020029885070215800c00e0703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 481137607 1250 481136357 481136371
    0x1d1915030f0b150307050105070b062106091603030e040902191205010b04090206030f060a05060d0b03060115140912061003032615040f022d180108 65
    0x4000a516034442500354001c641d021100c03064140100851010300b50401180d0103412409005910f2511000034072034043d0600203404204400c011401c2c694581e06811441c03004105036600010f05e4013106903e80c5400c031010b0a141c0161a051040788151052138001c2d6a810344803802200061420701008042e2000d04030307001407c5183c20b141c08421030702294010701044501c044014036503d0030714252182103403c0c42c080e9042c140804010395524041d6030b408520300310354001c04c3e9107600c002400880c41d0740c071458100d00000784c888180e6030140c201c0714401c0e209404070354150760b8132028828412480b04421000400064988651588c5040103280e0008010109020301d109041c4070f0307080c481c050b181103540300c0304160204201030b00300020a190003032019089102d5411280300404042000b13206862420784000305515540e01d079807100e0b0a40821401c1107441341c4102c03c2079901d21134141e15100e18080d05403170700f400b00380414084500305102da08458008040480c010764806070064008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 481138857 1250 481137607 481137641
    0xb01051902010b04180203070b1204140a0f060b09090d090b130504060e01030b0a0608030307080c0c011d0c03030f04050f010212030412090b030603060712180c1d19 72
    0xc102542c0e5030190408022007030f420404280c5c2c031072041615101c01540304124407a4244281d9001e11280d040c0154003a4010030071996010300c8803042414400000d034010003840b000c600f1070041c010240d2107082c0118065820340390949075151159617035801100b080c00040c8285806010303810400018104030070b40c500281485946400008c1c041d100c46801900380c10804a00400a1040d101c00e42d03074201d8101e0904105003400c101d03e41d030300c0c0c1c80b00030103040900286002048081400034110380003518114020402c1c40001c400c01c2e80020780d0480107411910400c5182c036078511303004c000c480420a11234982c600e414034040900c40d24640247c401410341c02801100403401c0c1e601001184200d108120900c3d10400b240800380c04208503800484003c042842000003a803000555aa04044141807100c0a14000760841020b4990b004c1c0030042c40185220080030842c0c600858001c0e00d9101c40c800b4500b41814881d40703444c0904860340e550020780510000040e26295000b1205c002c1c80304d0720 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 481140107 1250 481138857 481138871
    0x70306111207020307112b0807030305060a030c051026010501080117060109150f060207210302031c1b03050a05090d0c1b0308040e1506090303041e03060e1c030b0105190201 76
    0x83c44041f002440820343d804840045d040c4105541841410340c40ba00c100c0d041c06220f0b0454a825900326924010a07002d844e9141d10303182d43e40d010b030000a000d80d68102401d142103241d43c06076050b8082c28440c05021940c0d103c00810a640c268030100e02c41303030044001f0a002e80c0b03007840315009416207502095030140d400c2c9012404132504040c0102401c180d40040c62100d2510004020b005564800e0202c100700124620001a9001c4100d9500c0421101419040b00d0510411030041800d610f0040c00d0003a14420252000d4140c1c024038032a4a624a04220315628002542e45a000451100b40014850024100000c0b80e0708090011484403801001525407681c1d0358007869842070b00610100741c6103604010800d40401c1015440041c00d964080c00d280701c0e1000b1035903e00450144050030b04000d000c0c1c3d580c214515541c0001941c202905100302841403803040c0d111007585214494100780c1000d4001000d00038000c148400e003040c0d6038a850b12120f8100345041100b58900a0119502d0b000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 481141357 1250 481140107 481140169
    0x21160c0b0c0d14070215090a15230313080304051002030406091b0f0513020f0403080301032d020906060904060e0a06060201060b07110307030611120702030711 70
    0x10141c40d030034098000030304688481c01c2c006401c10042c03c18400ca080c00411805006884004030030708442c4d80140c0282e12206000c0029140c1002500b007400c0892190215810595000c0603100c40015100119102044103000d4a9540c1c03004231403050001c0640a001c1c00091100c100440e0300c2402007060340d80c580f6150314800241c1c0c0c0255001d454950301c8109030418041c480b01100c0801c0e10f02e443d04800c107407601403c43d01d8041c5911505100303a2003c001008180095012901807074980d00d0040c1d500c07600d900e008601500280000e40d403400199450482094100c8018003070455046a01d55103d01c00b5820400304001c0108115003101060081a99940312802034030b000d0500a0642641854651106403c80701e055100c0c07070031a8141802040381f04013071000c40741c0346e54002008004860b90314012034a801020380c0002d110320314100d40c15a46a000c68080c00803548460070488480d02d40c00c0080380d50b4082c0070800b400c242034000508c0b80e03900d480343c60400718110841140305403101040d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 481142607 1250 481141357 481141379
    0x9250801361503020a0b03071e09031407081911090a0f090c0e090d090b0901050c060c0301150914040b0f03030a03050406141b1e0703020d0221160c 65
    0x702c5070302c45422854000b4000c40c605034203c00c01406004d00481d0451400c9403000f0448803403180032683c159225880e040b07006100300c4c444000f842e080300c1e1040c080705500d10001eaa500729071049020754040c0801c0b403109441403d5a480030340381c016101c1d100c402c2c41ca8003003000b240d00c050300c60498036030b880c4a08120000c0768081c22030302174017031304051070040d140c07881e6542481c80c01000e200e1240c2003c00961200394010390740e201580c00301650396840d0007000e00142d489102c0c13008005081d10511040100600d81140150305a643c001040c0b40b00d04c100b0603095812003e6030141450b11480c2d50b03d003400908182d0b116407000c034070050000c1d034103644013408a411984010520000292a001000248812802143c0c26050780302101c0c400e5142598505a617044001040484030300009442145021000311484841030190230311950340c5140d1a010f59103113030f04a60100540201550413101c054a807220003c0700c207803011060300d0611240d807120701c890340202c800c441244100300042a0107501e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 481143857 1250 481142607 481142621
    0x1090608070311131401020615030304090b060906041203140a050d0e0a0b090c120607090b0c0708160315050c0306060f0c070b04180e0d050702040b0925080136 70
    0x191404801c940d817036000a041200040065000c00b00c045010407883e10300008440440d401c40c0c3d00022503541000001c1d0941c400d90f1034440d440b440209010920f00e80035a40340b00503a01c2500c818035600c03401d01110a01c1c0c0107030300c80b24010841c1400440c0120400b03410110f490500d050a65030301c0f642310f40e01c008401c042900d0300c3d002c41d400703d2045035003818601c00e10030904803080000d1009290004008018064038000c00c01c0100000c11444200d00040182e500500100b0701904c44180700b1800070307452269288000d482c0d028484070740c10401d402038400c07280560390580f4618515920b08050101030380c003141088034003d20412401c0e07000c0e6130070302003d0702a10340180d405036141e10301280350407454010360b1320f02c89580c5040300b8900c0044000580c10608549410107030b465001e2070000070010000110003030381201620042056444500200c00c90108860b142c4001c500d1682d00b080b1608142401080d100440c4000c003802240301c1d40504144285140c4a050414801d249200c026100c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 481145107 1250 481143857 481143869
    0x30709060f0609210804030f0501090b0a0c35182e361209180f11040f030b1303051c0e010e0a020a050109060807031113 53
    0x1440d1030511245500c58001c1008090358030300f00d000d03181040030070800b143d510020040c0d440f00c00341420302003014070030a0341d008542005500c200000309080c81e6000c1e0250f000c1c1251095055000200ca40c2c03400d1241206e03028103551070482a0200004d41c4091140c4240080451124210280707405820200302a2044410101c442a1241000506d0380760003525013850060340e48500c03402c4046107a0000303c036100c00b2030760ba000c81c68540381081180070030b4103010f11400128132074460040042c0003441075000544561100030070300c0640f400881d51440d2500410444204c10b80305007403240c1107a0004601041c414900203041201a50322007541d0384141e210440d040044901002449449044141d00141c5070300038800410155a00802600c104100d900100b181c0a1500c0e44000d01da07400b080c1c1002d0610000c12182c03000d01001e5907510300000d012031054200f03c0003c11213510911000e812202d00341c03114101500c80311020b9000e0807c10791500c0d00c80b4000c2c014684000303180c240c0080103080c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 481146357 1250 481145107 481145111
    0x70809120f0d110d08040503030f040804050d2907020316050123041703061f09180f110c030712020a0b010b0c0d0806060409090303091a10060315030605060f030709 72
    0x40f590b0180e00700710300c884d0308400340142c50341000003003800442220303031180804840202680c0c03240b42810003402a500700f950004882c01040b0200402e074000301603c1c03600000c8089000071840300341039041004503126030050b002401100840c01d41c581c490f040061040001056100d01c6889500d00e07401d803840d00c4a0f43d504650103100c00e00644000052680e4082403002d4903525007030b004544900c00f410a02002509000c0c0711410710703131294010101622071094152a00c400110825000e443c040401d086890300d80885924148184000c441c0d16002d10009141050000e48600107056200800c0c6820350048224071400110780341d62240c040d20704181850b46451204100314903002000e0048024004110148a100e030b85800c2550100c0380d041001142d201c009207411406041c2d12030004002944882d81010713030484007044180704807403513410718003803641e5407504406841d0084048080802c51040520220304a43c001369408080503004041014246011920300b60082c2c0c0821022030b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 481147607 1250 481146357 481146377
    0x91506120207050d0c020d150b1201091a090313080604060b030c0307270515010206060d0b0f0703020f0a0305063c030f03040602060603060c070809120f0d 68
    0x35000051003629190a84046060030020f03601c1c96a80d400c000c1c0a04c0a1100c2150380404640e158a01c1d54900781c1c1c000c80c1c0c140003006038001c1030085c1840ca842c8034803404003880d401850f080c0520a40c9021a08045011500c00700d41d158003440d15000303000015240000c0041d01401030524180d0001801400e0043c495441c0c60704241c1d00325100844028072a400c14000b201090790000384040a848a848039a480c0440c46041e81c4008184103170700740452404c041c10031581e80c070f2090038801141000c0c1c00340d0f4110341d81c21302007041921040320010320365252603012170069011a009075038031180500b00180b510515101082c035581207004240c000980780c50401c030321030810b010301e040c941c820924655031030b10440c490031080c03020840c2c2c07403c000d810a00032003150307940030040710400315100019240d9464440c0c10007074507242c0450b40340e0b001e4403a60010600d4002590100c0d0100d03600702000a0908100c04100541000d25040c0c42c0c2c0349104202c9140702c00c900c18003151103d0096510f500c580c80e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 481148857 1250 481147607 481147619
    0x803130c050d29010308030414100903020705040c0f080103080a1418040c020f10050a1401030c08210904055209030b040816030e031c270915 62
    0x129030503d82d41caa00015080040000440340d00a498205034400400007000038000c080500d0000c50031260741f54141000c00c41028150080b50709415100c4c00c1c0d405111140228409541444d440100400054049001000400e40c510301074001c44a01340f030101c3d108580441e400c80e07a50014914400c1c0303600d0f440c0c002012881d15215000920003d400904030b0254121611604e840ea14910400a00d413a0381c0058442d500035401034001c2319a5110706061f95842e0300717140f030315044640110354840c0714840c9070204508402c00201a110724007200d1901c0c0038090011700000d4580500800e80e031a81c4404040c8407014504070316400b010f2520609404125140122505a0740703000e5010b507840000003444445981c010011b0050340c0d0850b03002c2016840e9468040610b00c900a000041171031039196581c2010b5001d00d00b030441d1401101200c0081c400e04811000c1d035800c62442e0004100000108054007840403240c0c5031409204003500f6516540c1d030410020b0b10000c076174810304112884014014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 481150107 1250 481148857 481148903
    0x6060b03090d02070308030705070c03060609020a1814101b050102090f01031e020307020304080105090705040c05090d141009151104120f020d05010c030603110d0803130c050d 77
    0x80460070f2004020041c619241c3c00d10510000d4849410088005010400c0c844000c900034015540720008100c129a202500d200030342081c141d8900041092600350307056aa15504441074600c020f10070450f8202040c10440485000d4409000780100780d6501c910042d9809100c041c013a008600160383c07a00e43d04100090503c15030340c001d05262a16200120200c0825034001c002e50440d440103940351206142a481d500842c0c3c03103840c0c1076003030a080000031500801c0000c203e07042901c003030040c0c4a02e001c00b5180da028003014250040c95071100f65001c510b600c0601a8080c1740381c02074400d2032003045440019615070003016109144450042005c4074102c0c419691a03076101c11000742024100023000140c0e1112140203070000c02000601c00c295951500d00c61040d030f44c000c000b0001c05c0801000540901742e00e2006a030000a01146854241400c0980003d401c1d405812a0315540d0788004000380d07030500003c1951014441c00010519490b0001400c240a008030b6070411106880444562 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 481151357 1250 481150107 481150123
    0xc02031b09090712020d0809060a030906050f01150c020a050307170d02010e101a060d0902031c0c1b0e0f09060109200a1101020301060c0515040215130306060b0309 72
    0x286030301002042003c4d0280c03d040240c00c0360704603031040140034241440e8105008400c83c2c60b600c401c00056070b001f0740303030503902201d0759a22400d41400542d5641c0c0481c1c10050003480b42c1d05100c0011240c0f084a5481566103054052000f04000b5040e5141c1021070b10b0a10f064020051014011001e9640400b0400a03144a070000348002d110610015218a41712030950407a0188a515014001c1107101c2034900a140c401c4003402031900e881200550308050f001864041e03000740a481036049034600c1343e500c003118052554407110013405003540c0340300380380390b801e50f0b50348980503c2c610202d07000500c900c0840c01400045503048040c113214100504241043e40040845c074500b54414000590380e104c040c0b410f804070300e041a120381c0e81203416104440c01402008040d480080045402c5411000d00c030700d6103000d001101c801c0d2003100030103d031f1103e0070742c4c019501000d030030a014001c00003030000f41208103034891050603695482c3e90316015160302d600503031040140401048841ca01c10045d241c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 481152607 1250 481151357 481151371
    0x1022b11161e0c0e040816030c030305070e0a14010203041a070308090c01120506031f051506030c0f03090a0519150516050f0903030310060e03061012030c02031b09 72
    0x2c02d0b070070680c1e03aa105095641c400d413004021004005424001c440c3c081c2d4040100104000e071112505103001401c0015410301200464a00008100780520401d29500c4400010300584034080c104116031030030580d03a044041c1188003c0202050a81c06500b0207200921080d03c01502e502c11890045c01420005220f40360385d41c0b0440c205a02e527a07100300d5100e903540800200107150380b169804a420240305040c4142d81c0100d840d89096070144581c44103204000c0a02d0101011130203200b042220b101c00c4d41c580c030b03044005004014055030290001d6401c0b41d46401159100051603171064100307460410340d038291440030103454051140d04080182c0082040c0001c000c54038101d01130300070809185034a101000000300781c55551181110403103142c035900404407622803810100340303c0328003082d00410000581c0c5160005580c14001001070140c0185244250141d040c091804a54011000140c0030031403c1d84c0c0f0100562401e003d040c0481c410300031515030450340d607401d001c3c140324060884 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 481153857 1250 481152607 481152653
    0x7050709020414090c030403030203040f0503031f0605040f030209310507060c050303040b0c0432030724030f0203011211090603120f0d060f0306060801022b1116 71
    0x1c005c842c001c20440c0e51156150030010f0722074441d410704440f00c007050341005140344000002d1001056002042003050301d450300062454544410045178176005920480444800105d401d00040c50451030056201540000113020702d440009141c00ba60031003085540490480e0500070b0500c002440b60401a00740c0703003031075540c94000780e60349581c1e8880108090042000e1202090b100882001142e00070881e104c55088e000051040b01c0d200007000d0210034044400d0046480d030a410040340520454003810601022140f200c030307048841c0d40c040e03201c42040682d074840c0c0300600492403019501811890306000b003018564641144200011000d040c8580300400401c030306658009900312259824603031464580300b04000384070740c60007607034550342e0700500f407603404101020070141c810304581c01039005008140e44c50181d02c0c200d00c140414030086548400701c044030302d42111046122001e002d1000901c2c800740201d07807031700e50300519a07028034903c0280341c00303050001400d6508104107004c0c420b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 481155107 1250 481153857 481153861
    0xf03050105090a0b130f050d050a020609060103030c12020102040902130e061504051e0907080906070809030f0f120702011d071202150409060f030c140d1104020705070902041409 78
    0x5600d500c3d001c028aa59001e14085d00d1301c408003d1a030a0319000c0b26401030441c7c01031400904040e07c59000083c2d13020040c8901d40005401400000b00c60707040300d4142d16021102442625504540510310003c0f4042d503400300300014100c80c4500c014a404410403450041845c01c0400340001410090041c62180035910900c001944007001210204c0e078084030707401429040d901342c00c0d105880d0100c131143d0201806c0d0400c034600780c00c950914403903030b4204243c990780d548141c82034071180303801d65844280c1e43c0140203003955854002c0080c0082c000640d85e0a0a10750251034681f802d0004460560041c0d4440440e08003014038050701800c00d80042d4054081141848031408644541c0703e000b0f0f102d10046840d926092402030105c4010346a00d00090184584960305c2c01e41c400120b110803560049640e40004002e0301a041c00c0307848000082007400480c1054661505641c10524a941d01079030030888480084c404000c20001401079880140c2c41e45e00e80b46070a008901e82c801603c1c0141c0c1c0040c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 481156357 1250 481155107 481155113
    0x30f030106091512020901200d030c020a150c05040509150103060801061206180c0602071818030c06020c0f10110a0c0f05010f0903050304020f031c23040f03050105090a 74
    0x500111844404100146c4640d0080f00403102e441e00554280350704034500e50407000702400031881d01640b2526850034400300034540c10481c0c0d03509081502800c0c004400c001c0004c40e04e11070f000345108121910701a0b041648900c002103020300183c2e403249080c4003045101c000c40d45c150184000130084030b00200840d500c2d081a0302c45040e41040d008094030380e2072038402c00c251041c5840741141d64016480d200225116407021b542c0350024080c514030340201c485040082c954074060190680c3ca500c008118402c143e60f401d4441200440084908507001d100014004c101041646d03d06e600c40e00081c0705901042e0303503100440d0450594500307507800c2040440e545542208000041703960103c40c80ca03030100c9908100c6c2c010880031506203d19410200e2407030506600001030b5000c0ea0080b6604180d082d490000c00d6035a180c1c21900045d00c444084150f000e20b8020580610404003039000c010988520203e00c0701540d1142d005206020b100d03510034024050240311b055030000110008011011840e1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 481157607 1250 481156357 481156367
    0x360c0201060b120601080115022d0a08041805060f0904050c03030a03150f15180305060717060405071d060c01050127020901020c040e0124080c040b150714030f0301060915 75
    0x134041014460f94482b03103801d04501d0101c182da0f03038214905403076a941c840d10381a24a0f42c000d1044031144181c0402c6e029a00702c00e845001c0c00f0700001845550300866500500c103a9000080c8150340a019003200141e054034188001c1101000b1a64001044d03561001c80e0054040190048040c07101c00f05400c1c40400d82d403068510b0341c00c0b0f09086c0310039036002d0900340d6a404803098000900e1030003480f062100f000c1d00304600414201603a8901c50850740c2d028184001c03903c0072203031507000860190702c01c0d5a8100c10000d00e9091503001d800d0300c0c5003200141e5524251442a44981c0d8140601e20b07c0010488004a500202c0c03607a005040d4902082100002e40e00c2c1410303034217584255170355054640d40301c0302540000702c02d035000c0e130721200007070352007060303002910b61300c1c840d011032400303460031760318070340c9003600ca04666188001e180800e03000360f5440344960f03500701c1c40c0c04441c64004024120401034041000e820410003c8400782d5696061000040c4030f44a190302081d006c100f0b00c1445800d00344c002c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 481158857 1250 481157607 481157623
    0xf0c03100905030d0f020a0305061806060d09020303030c0903190f02311b050705060f060d050601030f03020c0f090402010c060209060c07360c0201060b12060108011502 74
    0x1800340031a480c0041d082c6982540305090b401e075a098a0f01c085e41e909001039030003405050301135881c100484c0c0c2c0c0d20014020220501c0030901041c0407a000000d0705450954080c00894040400004000c1c0031980400c0c6141c1c025601080d0b03000020418031110b14042041d052898a450240840841c465440002085000c400203125050412001000702443d0200c401e42c45400510b1129518a4190800c010840301100c075130358100780300e10942d449000b00201d07120b26910000414035582d400100144600d400740156030301c03480c000845404900b0400041e400b23580104a910740b01c40309850064941000b00c00740c107005402a00311042607076581f0400c075611640a0034018400e00c0c607460038200a11940102550000b000301344548240c1d40000c440090300c4084014510420340d05940c40060240e84400c4048114607452441c1d000c0400d4210495000843c000841c64503203c4a4403040785d0020144140701032281e401b04180703903078055456401019031001010000609840c0251038400c6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 481160107 1250 481158857 481158883
    0x1002041d0406090b01030f03120204180b0d06050702340302120c0405090304051927020c0105070c1b060203030c0c1f05010e0106020303060a030f0f230f0c03 69
    0x394000080c14080d442d081040d601d54040103501181d0303101d00e00301060044003c010340001e100343c1c9804174044258403c403411b41d50b1160203022460311055000c0003402c4100c1506821400341064100028018041c082c069082c0d0b40140c100c4941444000d074410147d900301c0350380c0b0000c00c0446d00b94003c3c1c418017401500d80585000258901c3d141103d8a40040b00c221160020b140801b040003145c4084040d02c2900c5044408048082d001100654480c02e54044c540100c04804048075108014a1002460904100c0b005d07050030200a002403c40342d0407900940800c02d81c059890030021a011010302c0300018201540c0c0c030600b0300134000d41c0c0e4000101051084c150004943d030020318100802e1181400c0c84040828100c403040c2001c1c043c060a05c249000189100001b0403428008420740344600310140ca2214460f00c1d42d100c080440c0b071428015680c0350200428100070a120343e02da9401c41108113842c105040c04044081d1034100e26901190058002c1030142c803140c0d17000b190075120104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 481161357 1250 481160107 481160159
    0x20a020d080a031803050405180405070b030402190b04050a053703080d021b120a2f010b0f2704140a0c23030d0819110309100204 57
    0x51900e90640060051075008504c40d078034440c041e420582d2000080054403801c0e61048103034031460900d6240e8400c1640e00500c0d40e013048506002c408074007800307117138070500040004001e00380c07110707600507401c01c907030000300d00c0520015042c091420400c2100303008110696003402c104e01e0000058030794412928085446040601440c0580003d08580d4005150440440750b40c03142c520b80203c0081d4040c045079400e0030910004070104440c007058800300e4001112030245040d440050403503164030345040c0b00a02e1940301030508205044a582c800003100150000a241148078080192110f01d10301d44600c6240710f441c01c031103031758142c810121001d0200c03a119495500c461a141c1001040301000c01494405c1c084100c050150004503001260060112000c42525110380c1002e140d1409100030b405034051038182201d54803c80d1206e51044500024151050b40c10041c2016514841d948950030300010040c0031003041c1c1481050180740b4900702c114603041ca00045a07207000e482e54000e2005036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 481162607 1250 481161357 481161367
    0x41154040203010b19170111070b0606040f080604030305280902040e030a080a0e0319270f06020705030d090302100c02091003060c0c0201230d020a0801060f020a020d08 74
    0x91002d400440c41301200912820324208080d060307081c0c030b206134400e854043d228044002030060b4184650f01e00362140b203803214a4101e664490000042c000780c101d98200c10108400100800c84003000f0000d0140301028040740c0c149800c0042c01d90f500607041d0709809405000d8800c00c46010f05040c6807072909400c0101d010462030000a00511a00301101c07840e000009080651543c8695030364421014080100303c206c000000c201c3e0380740504035480171403020340314040c14a50b009082e60880c0040e2401c0c2101c5d141c0103018036a001500d07507404000d90341300713484040c82403a8041c08448080c200c150024656861510002007207500c69100203405040900c9544030305074850900c1103040b0341c014005c0c101e070342071031191800100e645110940c6c0d0145000b05400e2800e10410721012000e805958241010400b4421524640850a1701d050080020000b2420050f039500203803412031201c3d2200f52180d0301d00784004d0b02c0c0c80024440032085400080741000181c0c0c44116000255801c802030742d440d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 481163857 1250 481162607 481162609
    0x9031a34180305030a090f0f0e040305030c070203071401030b01031a04090516080318030d09051903020909160605070507180e0316060b0f13050411540402 68
    0x81c0c11581c0001d800c0d0700000410340d24040e00700708084110346002c410002000ea880e04440c402002178000e1284181c0c0d0240480d011030f200c2c2001e190040c1e9810110740c41c0440c2a40020700e817001b654483d0002001500d080c00c1a980c0500c02c071900300d802807d01340083c041ca0003004a0b03007c95404500d00c55648c1c1c000f42c4050010402c14403c1c00d09840000700308842d103481800c1d42c0c0750010403064490085c02c541040e044c0c00d000c1a81040c246954844011040c144070421101049100c08081c107145600300000c0540e98072451180103000d8000608910340d002ca280d894038110a412100c01e00c4010003402000450014180040f0f4021100f2003400c2611101410b020740500c0c1e504080611010503585411140d406482444034840c4604000307a519500921014114080000e0b078440008110b015241d1015000503030700601c1a032041415407503c2001440724010003407a110f0302c82c28003656020749a00c003a120014281a0003401e0b800c000078074000c051303461407911500521701c0100c01182c11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 481165107 1250 481163857 481163897
    0x6040219030b15090c09061e0d0204090207050622060f0b1302271507021302030f01181427100b03060a060602071509031a34 55
    0x595070211982e05141000348010341165140d400300ea110b07100c241d011403aa00108011a2450138000d0419810500310354041320990b400a840481300c3c840801028201681c648010b0001d8a110580181c5503000341c108940340c59401001041403403461041036480d000000035102440313510003800310f1000e000940140c0685641e1910300e410600001211015030000d4000d00340c06d0b4060302c40342c1e407101080c003031400d99101d425821a030000c1b81c0780c0c2c860403140450001003954500160045168001514004089a0086881c602000c0240d070061113041000311200b040203801407010700003440350303440310118550054501a410309900d4811094104c2620350301c609800110155003981290900202c041d12001d60301510a0103440c000035030300c1d00c0c184030b40da042d51030a50040c0512400e21940c80b81980c88050084c0501c1a084000000210008140a0103582001a512441c14501902d02c0d090040c2d07407400300760031082451420000c0311540d0014000d206494403131780c404102106c4102d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 481166357 1250 481165107 481165109
    0xf020f04140301020408030403290f04141b0105071406181203010b0d05060315040605010f080624012703021309110906010311120708010f03030e060306011b03080601080907050306040219 82
    0x91020968030820500000bd89296407040b0b00444110035039101c0e204030b03d40c6860f40104001008000306150170300c07a501c64400b92021f144100283e040000c0b1401043d032910400b12444a40602054264540d4200c00c2c0315000c181d882c0403100300d04650400c0252402d6000310030300511569034481c0014540d0707074204002100c2e1402200c0d40a01c80c01e150502d4000f03003d00340188224892050000107000d02c000485901c45c0080c0300d04241000502000d60128640c04031449041009008084481c0d00491514a01c00080c00080b420729526500c1449040c00240702e0316040036290421240100700482203420704a2400c171341c2e079003842c0d4410700144c1c024100304c0350a540c07040000c1909500c0301846401640100d2040d141d51038aa03989844155810340b940c04001c0000380321107810303d1207041000c051500b00d00c1c141418039804a01300b09404a5001146094000801041c00d000003940c0100d080350f04081c081015141103420500460b60f40d4401420090003408140d1001e107000201680101c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 481167607 1250 481166357 481166423
    0xf030f0d0207390609030b16111615050301030201021c09121109061f110a080a02010f05070f0c02090408040b03070908010f18150f020f04140301020408030403 70
    0x151030f40c240420b9880002030218030849040106060210301c4a01904200b0b0840e030384046580029911007580710b260030f144000d601c040c03181d51801c045e01d1300401d016000d2020b0a01d00c0744440075203000002d8145640daaa8002c080c01001c000500c0541d902254158043c04820070900518101c2181204d80b203100368401c0c50620f10f0b0b603ca00e0100840705812207400207007220700c9440c589991040016441e4640b0340710140044d1961030000180c0501120900c8615540540d01c118060b0746a10145e6030100d9017100050b50b580315822180340c0f441c8601500b0250070f1910f4095150346c600007415a00c1203110291044144100150812079030000f103030050010440c4450303c0782440100a814902c0134010b000c0b9550a000d41aa101c100310302c90303290003071640c0041001d1020703142c6800c0d150400e6000d881101035158610006c1620b81d90004011200301d000c0d089640307501d44503102d07001307218101c28144264010441008052030000541e0266600120000c244a6090000d118100986c01141c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 481168857 1250 481167607 481167653
    0x120510090606020a020102060a0b0a051314070302070519030914040f020409020c1020070203010906151505040312110703060f0c0801090b150a020106050a170f030f0d0207 75
    0x85080b40d8003207060050030b4400e808035141a11009214401d5880043e4441c0d0040b42c840402c10180c504180d010702c180466600000d02c2c03001e00b248848502e24202d9440d804690005411410850100001d410010403822903030305405059500421000b5a4800c1d0a100101100d2800c003a540c0e45e4480798512120000440d5181e80d1a40c0f001c0194020a504044900030031109039004001c034001d0300b07141c00c2100008501550754900b540386a40010509030307095962900d180001032201d200e5840b003c0e0380348240090701c1b4a0442c1040b440341c000c141e40c00401000344000c0000829000311120101d001e070905020b00d0024880703607454901aa800030301414100107828070000d01075880511a26020b0380d42000581e06c800e114004e8030780c2201c10a030000c0815a0314801e0940c1c5d80080c025920040c40040f43c0c0656035400681e242c16540c0001d14401401d038807500c6035060404c0306d4451207034460055403c051007110302d1f010a002c0d81c0b4000e2900c03900020500100035804203c5d40100c04c60f045c1e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 481170107 1250 481168857 481168859
    0x1b03120903021813030e1c050d0f0801060c0803150d0f150c05040302040b01110607050307080a06180b0406090905030910020a0c2108040b09010905220e07050301062408071205100906 80
    0x481e03600e40301d109d045404546441d031040038880c0b2460220303060b80c035103032101b00c100c048031356801045a0004041e10717807204001c1400e4a20395a0180b01501d1140503c411561080c91070071300f0310701a84200300c03511000f4031f050424140e168210f01074500702e0350100d03000030b90740074413100507504900c450742070700054040c0380700f007018103034204010358002d440c0c9130303a415031075503800200100f240e100b80210502d40c0e05074155041400c990b41c00035004440007901c01308910340e4442245080da040b2900444254001003084009410004d80c202103000d11840103000c0003155440d103460225007406071840303003c1141020102c80b2004e00a000c0c2d40b80e80415400c0c3c0e078540da1030840301e19803c00090140003404410000400b072a18840301c01c960080e10262074035011200e0744401c01040c00300d80c41525030052200014940d034080c03240070010017914412074031100d5102184400d0082d003c2d0f00320300380314015042c41401588980401e8100b071844400140b541c80b50b170298980000c6903441100c0190500340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 481171357 1250 481170107 481170113
    0xd0e0904050c1c1403070b0a0c141303110406030c06051b19020f010f0203030a1a1c02091605090f1201060f08100203131b03120903021813030e1c 64
    0x507005699070f014240002500c014810b4554583c0324861b80601114505000314440740c038694000c0c080c000283c1442460045c510300d200b88250031220282d410340c0000c0c01d0800a006071341500544010048600300501307821961801d1300000c07980195800c10801090510b8034052650340c500040300b0881c1199a2600420403c0814100c5460100e0290b1041320903800c0950003500d100c1403160f1290069411543c40140d4280241541107050304a80010200e42c0f100307444d04103008030744c800ea88814a0511850f4014404683c402620500c00081c0d041d2081c80c2159204080c1d17442d088d02202c00b07260700c04035480011060b000c10b041c0362010303500e010700c001100c0118141c40300c11583c43c0c100b55504280e14400c0a030480c0002c075914181854640f410a000450800c19100c0349041203040c0c0c2060368980d1140f0009644113000340010908246044c000d62501d028072002e0400c0180000c0f4561408034500c03180030292030303001028000c4d041000d10765550340155005804625180310005640242 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 481172607 1250 481171357 481171399
    0x5070203160902071205030906040209060f0d0501020306011e08061e040e010b0111010207021e03161e090c0c020103052503051e04050304270207050c120d0e0904050c 73
    0x4100719004005d00f03507480021030081c0c060320302c6080d10102034000c9950b00d40900c200144c00800d01680f00d915041c054040d44d4644500e030304c0aa000d0000180c80c0c0c90020000360072110900d60288180d00c0795040c0c0043d1980c001465688505c0940320f90101c1c0300494907020020300d030103d100c2d03030142c1003d0728072000e4001580710700c01c164001d0f0f851707942054120b45064200d2044e0301c00a5004418850011007940035100488041a000713012500c103109002c40d0701410064507003007200c0c1100c10144140080c00c44c0d1100d000506404402085007180c1514041c002040c4a00028103040c1c554000a00200b40004a015a44400428454502021040140103001c22103070340700c0303402c1c07640d86014000030007a08c080d10955202d00250700c0d103030502042d40880350b0442801304000d8002c81a0740800c034100e0010b008081e00c00c10080254644070010043c0d1490600d80403400356100307000240004d68400c0700c64070b80304001c2c2c40061151300d460400a003059008801250015000c504111803c0040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 481173857 1250 481172607 481172617
    0x4091709010215060d02010305060f09071706090c0a0c02010201062c0a0905060103140f0111040e34030b060a05070219060f030c0c020315070e0402040f030305070203160902 76
    0x242c0c241d503600b00340000c004000e0b071030540300160024a1a28084c0055010354000d039000314004003a10140a0000c00007200f200c821504c0000003043d40c0c884990b4026200c00e40d680005040300c0011591501d41c100b60182c0c0140702140080000c04085101964001e61004000e03041004905040d41130380301d521b035205140703811021544098100041c210750307114410101c4651b07000e4050700a1364039548454456040d0b285460440d40030b00c10b4003c050060034454154190710b901030b0b00d07880d10f2400840100203480203010541e8031000c0c4900341601284d400489090b04141c2864038642002e50030205e0041ca0380c091056040340d400107811076215001009440c00c24400c0b1280d40d1007200307000038010011100c0c421040030400115003140006e00035000441000464500f40c0000c0389d4940009140014502c0554009980c03401400780042d441604540b1040d01500d082d0324043c64205d036180d200b0030b14440501042000319800c0c1c11541e05219801c3c180310581c403440102034031180007070700a41c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 481175107 1250 481173857 481173859
    0x7330605032b081902030130031e2609010e030c07270203040b0f01060c03140a030b2215140d080903030a03153204091709 54
    0x1030b6801c001c4541c400c86040034801240d020912001c00056200b500d010201900100754408604480c0c890744880384003843c001c00d0244450391040341c0550013118420005401c44441c45c0000003007030042078100d40040c078803201000415054050002d1308481c40a4010122074901c1c07070031010696030b5049014002d008041110081010200c002c002036035a10420001c0304054000c0502006000300c0402c82000303440e0409594046c011011900008980c01141d0440e2612140c0003031190120001480e607026007a103003019899001c064038058001580003d5400c00f8a1001403088982ea209400c000c108250140198120340340780a030742401c03500040240300d0f05901e044040d070910a811182801250040040ea0b129040c03408207000d91140c86100c2610421030401c452516510200000d2042c090142d03400940d05003103815003071012400c0d40c441d090f641004000503007885040d51241c81e83c0d40043c24001c240041100100d07000d41f90080c0c01400381b0310b0300000d028460152074014070407414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 481176357 1250 481175107 481175113
    0x60e041406071b050703150903110d02070e0402030a0c030f05060708010506030414070e0a02072906120703080406050a020c01030e0d0c06021303050309090106140733060503 76
    0x1500212595150000c0b55903800040c0c82005140701d08000c0b901001c40b0310700900981d181c440c0c4940755000384660a08101003c40d607100034001c00c7c150300075904110840c01002030000b040781a20f000350303504902d008007240c40d115400401c0031950104180c050f00d6600c809520044d55807814000301c80801c0b004156020300840d000a100ea03842984102d050b10001000941551180e84a00825507803255080017903105145002c1421284810403d2040d050301c8405656078040e40350440107141e84038020507070b541100c0640c410940328201e20503070001d0191911216070030b410103400c1c500300c019070028000502c0010080399540d40180200034007603840c0c0840d6181700d0a10011000c032440c0c8a440305172900115410b0b00c0152280c054a40d085010300740140c1000c2c1641d041c410741000c1944111090703840041e41c94aa0b0a21040050041c0794900348041d03200a5018140c10074410050f00070700303110b46100300c211106055100c5400d201e2102950b81e501403401034945000b484980100c0b44284 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 481177607 1250 481176357 481176383
    0x1f020105090d08040c030f02060d0e03030a1503020303030a05040c03151b08070f110724030513150b0d08031303020c0f01021b01090503100212010b03150d060f060e04 73
    0x140c0035946203400745a0254107024098a0342d11207195024072494100c1c3c4c07009c0204600314050016001c1e0303070390307a8a248024580d00d04044000004076240080e04440d424407040d0100090303603012069030b40c8280480808221950f441c03030209002c1200740c10040421484440e65400002c1c5540048070114100a91b08010320090100f80c1e60001e003140ca000004e001454659041c510030441c0d01000b4014804880c11180c5030103d207107519440340100c01420360840f5a001070300303625010341504455502c007100320084140d1100c28010391002624508951208440d4149440b81206202007540140b40a61203003042c105042000c40b541c3c3c0c0c160b00511038200e04010910b0147c2e801419030034160000c080d0b0361080c4002200400ba2005000d0500c5045400000da54900307200700e001d88a141500141d8540401003411442130068010410300d070424030400904010141295505407422600740c0c0152029240110290814164001d1090304042000511500103407030507000702d21031a010529a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 481178857 1250 481177607 481177633
    0xc070509100506070f051c2d0225030606140f0402270f120f10020f2514030d1406010e0918030316030f060509151f02010509 55
    0x1a581da004507603000404108a00003d403100c0c03a4820800d21550076a00c0510b1400001402071007440361a00104d980881207090442c0803a2001500d1611082c03ca11020400b0000030741d900c501d900300328032100a1150914940e24042d124000071a44510301b4050503459050120b410a10f80c1405030265020116107040ca00d002d001f551740020f0907410720f42c01f003451803403403900c0c044107454003642204410407900001d031959102400f0041620009080c1c83c40304480c02d5251100d0702e40c400c0349081c81401a060b41400f038034121813540c100c0c22800d1100c490344001c600c0c110780303d80d40c0040c02c00b000b0100c031101655020015111032050780f41e04016110380220161006001200c1950008100d060031465514100380581e41083c901010106c0c05009401990b1842e0300c181c541c540f012407481da13842c002503458010030035422320b855000d0185900d408c0224110103000b60404480c8000c09c200403120791036010850381c210003d00d4a25078260000dc001a008140544010710180030329845070300e00b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 481180107 1250 481178857 481178881
    0xb10020c0906040b12010501080a020111060601080f09010e010c020f0d0311031b160f11030a0528080f0711010c05030a03050c1b010b0a050d1104020f07080c070509 72
    0x40e0400c0a40340701429507075002044000d050b440c0104d40d01103510103a00c094805c091207294043e1224034009c01b442e440a0001412140504029164036072007002000300f10b907030080069400160f01c1c0c0b40d14017291103400401e40034000003084c5401a6180c0392025402560000c1d0a40c2606401d0040d601d1044820b14101d003680c60501c41c007140710000f000440c0580b030075548841e046841c80348407241401000c078204486080020340c15940305030b01070040024804001d02110800303c4c200c0040c10402910340e200e84d1a51800c01400c2c005100220144507025250a00c2420803940308001c1a0780c0c503c070700700541560300011015180842c1000031244e455004402070950035400400031070500c411487c0403405041e006045140180d0103000201d91807011007410150220880008104a1441c006000a0710515440b10740b15102409001001c00c40f500005402100165000b5a07a040300704c105102502c01c11034020240b104c00500b2031303200c20020440605030741d0308480d00c49058546d0060004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 481181357 1250 481180107 481180123
    0x1030c06020f06010b0703090b130e0a0515100e1c0605060d0503040b070507180c0e0415170309190f0504020a0e06130e16110d1b0311100b1002 63
    0x2e201d0b0721040051094a1241018144c0c46e4401d18251191586809070f080b40307074002001c074001c4841303042001d00220b954081082c1d40009208400c2000f440c0000314081640c10749003c4e18000e4231101901080c09218108100b1404405001140030314405925001141c12812080c0c80c62031529000c20380b14500040840314142d0803500450a01e8103200b032a51030f50380b000ca0211080d200f059000140c3c10304403107814010f820203d000103080c8604500150024034030146051007107260001d102c0441000040f0b0400f90384006017003440d151440301d02c25103140318050b9155880000c4040c000050034003001c4000c140d54070707003441c0750701c403680d900501050380543d0303000e0030215a0000805030581041c4001e00840f2a08103000140c0710399031540582c5844083d030b0000e158900654801ca01990024420100c004000c0001e04450744505001000310001c842ca1003540b011050380340c4107041c07044086907000744045007034510f2000c424000030300a10300c010802d80034000c031321158100c050001c10740e00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 481182607 1250 481181357 481181383
    0xc120609070519171005040b150f0c03040b070c05030d090f0308090301200c07060e1c030c0b10030314190302030a09051f050606041809060204031a01030c0602 70
    0x1400c0002c042d0400603000300c8406403008002204410b088a688154041c0380240c04400076221654103250a000c1648d03640040705000b8895803c558000d07107000c9085078441840340c0140c42c1c80d190748010080c210b100d5540007004080c1c0202c0c1e40014403000c000114100c6c9c10480131944103441040c42951807002511030002030340c1c03886404201188001e4010080404c0043c000261000400c405003250b64880030030001c542c1000c90042e001c1c13201080700b40017400300350500d041001070000020f48074000001d100d030340c1104644803190070940115070500301107611842c009407034500b0622040d01c4010314401a0001410104140403143c00e0b0821620480c80d1201104002d00c1000303400e40103980041e000100b031340d503034808040109400b0b2240c40807000d0814004041000c60f00800c1d07040c1c4401402840c415a42000100b0110003124800764801c100c00c000400d10394142d040c50802806a51b00160035513440b82a10180c48100360b081da41642d110f000b103542500d0b02e40c002240c1c2c401d034041e641 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 481183857 1250 481182607 481182617
    0xa05031f02090f0306090607020601080729090904060c0206130803060d03120c1e182102120a021504080a0b04061d16150e06130e0c12060907 62
    0x1031040200e50000c241010000d0071a06100c10b14601091402000f220006403542003582844025681840040d006050442c01890424107201510032030f05140b40d240c1000c400e800200e000344042440075101d2031080142100c009240c5428501c2c0507011441700d00c40140104000250303145401c101429013190883d002904681c1e80c0024441c1c04450501c040d800e00c28007000070903101c4468068907686080395525103190000e01e481c144414030403e0b400c14107202d4111048403440c0050070f110401c0310a84107010a400001c406040380b8061403c1d40039410044102007901c0709034000131b00d0701006100f65152960354002c800100041e005a000d20f4507c1c1d0080381a01001c550f10590068000c0e00030800000d0b40340c855030303009070580101054645aa0000c02014140000034100c500060403601c0b10000d20132040390004015034000c1d11410b100e02c402080340543c04003d40f5a410141c005002c0c0c03200242007910300c404650f042400107402d8441410001a401d040420f4032a0140340396480d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 481185107 1250 481183857 481183903
    0x80d0b0604061409030c090a0603030e090106020307080f0c1009051608061621200310061b0605040606091104080a030f05070f1a150306060105130305010504060b0a0503 74
    0x2004030f103500c45000d10b681403040c1d091000c01c80d915200d480e800341c21112800148686185400303484001c40340a0144520701c03070001080300f00c2d0080210317184180e21120b0990307100e0042120b0207150048c400400c205108121142009444030340c40010313000c2c041c3c000c03610140320415038640c0420312405021b00540045011030b03942900e6039482103140c90340c3e0815201220002025212501d403e001c01c12480c0d88070001040c00468030b008100240003500c1da080c4c558540b00045001c0c0720f2240c8952810800110f000034548040180d071040f000f070384090b0610580c145030a0400c084c0815010741c1d801140382004040c1c40558940c1250104c2d00d24074090001380d085901d0507254440c44e081c10b803061240400007840000c02d81c0c0180d8003040e00c202c11020622040b40302501582600900076400707413000240f1600280e50004031503910110919055546080c030703069085503400c0c5680004d00f01d40c280b0082c0810012079421041100e1070a44241c020555a40c080590341c00d05140f09005084030401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 481186357 1250 481185107 481185137
    0x61803090e0601031e06030b0603150402220e06010f1e1802090603070207081c3f1b030c12150b0c1c0206060604260a080d0b060406 58
    0x1680690141000078205c17403030b0314100d00c0420b0f0356100c286000d030391002d0900c10405140ca00640003007059008202c80701a041c4078038004c81d0090406445002ea5029880b034041040003008501800098180440000300107642c1e500c050a02402000a26411000c2480c13400030260500d001c00201410020500d089646003e4201410034144100d03002c0000d0111522400300460256280341e005100c800e140010090810511030280003507002c01c0c04c0e1a66044d68132800400c4100c0c2c03100120f240c0b259410f9000424240c006452100c11054410320201c074220aa00c646803500c0d8143c0150002c4101113411000c80e4005003403080442c3d1a101c245240c0e9589500110100315911760541c0360030b44a4004210035040f04d540110b59900620446602c0c000100c4900c01c0090b00740002c01d100d041c4403002035454020781c0940031031110940a40d0a9403281d403400701c010001c82d103060351340d410b84606010302e20794840440c0c1d00da131906124104501d401c000c070869040b030711142d90700f18254551036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 481187607 1250 481186357 481186379
    0x20d061506020c0312090a0b16032d030e010b0a060905281809050a0b1905010b04050f010203130605190f0509040c0507060f0605100203030405120903190b0406180309 73
    0x40072290003012a40c00072036023041a00081c840000d04680b1111060300c245801041020440380700f540c03909c00b214070b6403042c50301d4074080828514a405e0204492803801070060040c1038428801d5888000301c8400030321107402100c0ea80c02c0d1030341914003494580c03681c030051803581c00405146030311005001040021b000b41c046a400e24040c1803801040000c00d60710342034901f49060006440c0c4040300020700840b40c840415060350803011341c0040c400d0b503243c41c4100e0621b0003a48911070195074810000c1485038428001c4445c01150078641503103ca8580300c004015400109503401c8140c410028a040702e4050400401c425800350b60f128a059105000e00014080c19000c900034080c0c103100c01c4001490600a09a10060001d0b0011341d06280104000b0070601da40c0c004025904204184008200c0118031000142100c0024694804c031400220746404c2caa21003c0505802d854190002c201021508a0044c2d01644050249086225140c950320a4454005000c591011005c011002c005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 481188857 1250 481187607 481187617
    0x4110f0a080403020709021c0e0c0d080a050c0f010204031a090604020d0c0806070c121b0b04050a0b04060203040b060a050f091f0306140703140a02070609020d061506020c0312 77
    0x1a106440c0c800360345d0200031b82079030003880000200c028400191240c0c0c666922424400e4030000c801028500c22200129445020032500986051070010302e903200e40d40520129005c0c1000d41c0202c8682c1804254418001d403c80c1c00200c0f40e01c0900c1078148000445040528002d40c5504041e181ca500c8a5080120071009550221014600d4910010340103c00b880a6031085c50700c5d403581b5500000529095428a00c4034580d2414042015072a5a20104d45d10b280c080391303544591804125181c40c28854034000344440300805181e2204e0401042082540103103006500c180c0d2010307016110ba82c2000910360030360041c19007115020808039a44d20340b881560341c1000000c258111441c1c1c01d110b0340c0a4001d0103800680f48152a811140007490a4101880c3e0143c000d04d0308120f5020261150b019014020b00104c3d107081e000320b107407801d00c803840e071041c094541d004108112072240c07841e024001d400400d14521820010303280020781c0e503001080204030701d00010080c00c0340d160415524110341e040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 481190107 1250 481188857 481188863
    0x70203011b02010510380409051f1401050304080a03060302040c05070209010f0b071407121a07030608120a0e0a0801020c100204050d150f0609060504110f0a0804 71
    0x320481d50302544040c414801d00c0004560002c100c500c0d0500741c030542149140e1240c524150307242ea0100240704c01d00c000518100109182a190b80300d41c0484035900c0c000ca42140d05158980828480380151024034088040c0c80c0f1508039800c03d5071f5001c0722030707011395600c801c50114408200007000035071300c440104601d44080c180000c502d91282c010508031000d00c0ca10718003046002602138190b00d0400b02071401803c1128181c0302650914203401128010843c0c02407105288103006a141e05040c00200043c040d6541c80d0341c14008207041009010204140d02c07103c840140b004200c2d070798424003901055415540c020206402e012600c0c14a40d840182202c08120310036114840365501d64501100401c00d0b8400540c80b480c5a0100e80e00f0700e00c1004040801c01c0c8104000c02007501c45441008800d60004c80760305051085c0d0b10120054144d1480d142807030f42c03038124085494025a80044183c440540c1c1c03c011074407803405080660f21030005080603d003000e004081c9000c0c4aa0380340c0b03500c548 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 481191357 1250 481190107 481190111
    0x2d1e0718141c0b06040b0d0507032603190e0102090a031709060c0307030f09080a020411310816050d020103020c030d050406180f03030b0f10030506091e0a0207020301 73
    0x85804404205045060b03412550041c020302800001c1c5001d006d11242c10b0350850310304801c94110359586655040324400140603d1980b410740100e51968202d101034000d1104a0b1030f0341c0d1421003400380c1540006080c69a0081c41c10401000305c1e00c05200350750480c9006490050b14a04584030503481e1202d1107038010030040c0c20000703c0142d0300c86074050501d6000340402903840e80e0f0b051a01a14640c071120400080000646042054840c0010003040c0c980e0140c8000807505020f144000f1783d0f00c61107842180c0d82030505071040c44400d00e00c0e4280114162900495142501d68881c280c5031043c0d5540314445120046c014000e5103003800c0040c003403c0c414100146850581c003c040d003550422808400c1d00d581e80c00401043c003106004968041d100b502900c05042c07041d80e1405004102c4031380150806176105503102168517150300c41032400000508010a2480c41c000003400340174105c2d00b090003020a00042600300040c45125100c01003d07101c540d006955400880707009410410b403c0c0d91642d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 481192607 1250 481191357 481191379
    0xc080105041a092a1801170a030203040603240308070506010e0606070204020d0b0306010f03060507020c090705090a0e0108030d0e010902010e1329010e0111062d1e071814 75
    0x5511040c1e11710011201a4603944d036503240c44860749046000003400c90681e0040c5d80d030074000a0380172044805a0f2405d0500040032007405080e05015080c00303444502d040788018000c010b02141001424060742300e0800c8648a0303880e10400205c059064070050780010042c09001c005162940281010780b10003500040c0c0f0302d03c0703c4006860504281d200103244041d5803818401e0100c140545640510180000c00850600c1380103d00d440740010300780c008101004c41c44180c581d9445030000000e18044601d444556104d0051a84981c003420520030014682481c51806030410301403041c02a405071940003000c4488800d100c809500e49204c48022556078010a400303002c0e89a880004195842c4107045003100300e030003d0000c1d00d80d40340a80c1400800000d1101c101000580a0350040c044041010840ca1074840c0c0c00da821500c01400540c81503150402c48140d0b1460301c5a02740c086040c0020043e9298040c0c10f4441c4840381e2520300c581581c3c1c100034480f501940700c41180112025100c00d101c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 481193857 1250 481192607 481192609
    0x11010c0b06010c051f05061201110a03051e191d030702060a0516030c1101180b09010e220506060307020607201608060718170a0c080105041a092a 64
    0x21030041c0441e03144071b941d81d0511002d420710300c03100d200e8041d03458000c000450b0a035500d10f40c0360056942e00c1d8101a207500000e040d42e2484903000d43e40d541800c141d8405828480c1a00309a1196883d07092002c030701e480f9409000e0440002920803021400b00a03529056032502800314660040c8854410300c10104614074002c1944ca52a407004d9000b42e03a10141c6d81010714140e0605902c0c00d800a040021341c554040c1c10441c5658000d0885184805590340c601c080001070750080000703000540d0107001d2071103044459113013000c1c150fa405e0860004110303941c0c808003007045a002c1a00d0180059005500048107280542c40c02e05c120340400c0202040c18000820903881d2640d58030302400100000c620400000208114072508030840c0d080060340380b00b9107017103507000049903c100d00d0810b6222200c003031004000d002d501074031500a6070a40c0c1c201d483d4000300d40604000e840c1100c08081d041c52071405034004c5145140074041c001c0250074562035079031900c203201406018112810509004201e25 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 481195107 1250 481193857 481193893
    0xb0406090b07050a1205061e010905030d0306051201180b040c1206020705011104060e0105030a0b0a0f03050d020606010c02010807020c040219080a11070f110d06050411010c0b06010c05 81
    0x4a5000d660752955103600340c02005148040769210170502d9402c000510406543e01440c81e4000720117007095410010b55400100c490381d2180d401705415014141c60014100d905801040a4134420b8a00600c28000c1c1417031242200c1c0220040e840542035000d51340300080f031b4400758640090060b10718403081030f22100441c002400ea00401c60741d107079000985504103c0207010b08203100c005004614209880c0c05000342c07410004640141c10888000005420641031ba80006c80484001d0702140348039480d13231749040c81c6911502042e50300d449409181c80f1407920000c1c000e4461741040e9210099081e4990040d641c281c070150001d410741c055408140c000b500c5510180031503c2e03800f06d44800b803290320300d4044c0020902401d4840d0040c20807451348021462002200d5800342d01c007003e01c09850071740c10f0041c48640741404090740080b14078070350024011b8a030815030096015141c0c0d40010f1005000640d500410740c8401090b48080b103001500711360055016a104a0103a410b5400354450600e03e041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 481196357 1250 481195107 481195111
    0x30b01060806040c0f05040510121a030708011119050903011a0406050a030206030f060d080f030610031e0e0f0601123804110d0b0a05091203040b0406090b 68
    0x200107a000320401c1182e150134000d80b20860700a080051010300300c0c0c90018118451401442d02414440781080c642d00c1c81014900700b850341001c400c2180c08641c010341202c00307044004c20351003803241d07010201e80c40c0c2d070604c5603a00003000040c010785022507200210211190200c4054207001050001e400ca80d1402e0003041d41400c5000d540811201ca48420801280e2554004c58019211000103200580318001120780108040c8007280d681c1e650840080e81c440304120008201d0003010506104103251500918007503002260406510070050318110121012245207004640300c507100100440803d601403500c50940c6026542200d085050092401c4000c6c1e10540101c0350840010080c89140070001941c6201080c407405104404214407850002003414601a07a0701d0a021400700404540030040a0001505c080d02200302410094500441120300101d09418600024842e00010862002d0080c2e054103860071511769880d50450000c1c0104102c4085a842000201140d50764000074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 481197607 1250 481196357 481196369
    0x30a0507230a14061305100203040c081614091e0615040e06150910080c070c090c0206011a0403030c021804050604110f100c02041104080102040f17060c13030b01 71
    0x280d43c038140b00100c2e526101004041804401c410840c03000010408680080400e1011b580941c41f038690303080180000710140c0c0100d895114002004140c8045100c403401199180012600b85100a42c240b00704840e04950a44000f840034030f00c940c450682550b190780140303001d40f0039000340c80c0419145410b6071194028020746126a81000b90328a00a03004400000b40f0301e580900340700c4843d01080300034a842100505201003040001e19100e216020b40315030681080001c00c01d10742c0d0f1803158000300348500081c00140100000400d45c00502010555940203800d4281e00d041c1c91520304844c858600d00f4100d03481006c0001c803004542c94601103078000c0d40500d01500c1c01c1e0500785440402410003943d600e00820030803100442650340e201c18074095070114100390a06210502c0024010510304038107840ca040041400b1481d10015170180c415100700e5481c288409440d03d1080042d030382089800c0e001540304000141c03804410703030080d002e103941b020701e010245602d903501d5a0100800b41c202c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 481198857 1250 481197607 481197623
    0x12030f0b031f0f0b061b100f0605010818031c020708040603140a090c0b0f0c0109060506010f140901030914060a050403030b060307080f19110405040e030a0507230a 72
    0x1e5290040e00c1c8070303200c04003c52240030410b001050012034440c1c01103043c500805603001003501441c0c4d509200307251905c2203031082004209440c41075900142028020b06000500050024100c0c1c55640340750102100c0541c011800e1440b9866000000443c00d46103c05850b02403042c90000b0300380402510145c0044e817000300d56641500400221008001c0c4907103240f83c02c00c4000c01c0428183c0851200b83c0303220b803100310b0340c44034070107050280c911841c1034040700da61810b402081440425409107021300000d907266204249108001c442e80d4100c10303c1101e03641020013090a00b98081d52000c0e6000788504464100c4046080d0080e0801c6400c84038030072000e844400b080109681449254201c1c00c00722201815030500c4000280380050081c6094130611003c030100f9145500e00c00c201c0d45025080c8028050034031404400702043d0018403500c0c3c000c5040c035001000b080004025501021050381e9801c0c144003d980740e00c550f101800740a251841d180c200b201c800e0010a20004000500401e05 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 481200107 1250 481198857 481198903
    0xb0901062403240b03061c050d030b0f0f040b150703090602240723040824041a1914190204050a0b070c1d0901050105090412030f0b03 59
    0x58260340700d004105255160f122924114411210344200035544a420919101e94405020a4080b0b001c0c620900c03845210f541600200403000481031081103080c1c0c0d082c440080120b00f441081d0f51804c0c0c22950005110021444600b0113900202c481c4100412004d80d411414903101a03e5100c154282c000401101060040c1a01044039026a0036604400158840840d140309580d0070081d100c0410070070383c000400d40554054a412400058008002d96900c3d42d807420599981940c00c6c0d81c415092a1140001d03030080417040192145401c00000c0c40a031101140010000c100203091080e94410008d481040c0c003043e2142d45480010201009200c0c00c1c0308441c1c80d0a07130450000c0c0344016004000500064840303010610803129a07011a90300c400c4540381c41c100109403a005094070081981e40140c1105080e20034900070284203000b000b06980360014822150360807a0041c040c10113080c414007482d817083d489009401f010070310000e0000c2021001a041c08111a5070341050040120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 481201357 1250 481200107 481200179
    0x120702100b030d0c11010c08040b0a090e04050712030516060504050613200d08030f100f05030c2e0801150e0f01030c050f0706090605220b090106 64
    0x70855940d01e000701d0080502d01c0705924010302020182e040101006090380180d10340364019581a200f10350300140464a036500e0303505501c80b5400012003a40090103602c40010404201c54000740100e8000c401f400f4650304108409541e4115540c0c2142040801c2200c0014486418200f080447c45080c0100780c07030034142040c502c1c148015062418420000700c811002880c80b01000c0070b0721980120700c86c0420035990001c1c940c0d8924a1018060759000010003003699500c4030759031301c6205000742d88100503840b446941c2542580d805a00c0d05580024410700c030a10700040829081c51040032416007030112407202e0301e50744214503000f00111f1103910061141c4407115201c0003010040c0d141031080841d20b40300180078420ba240f000b40c18540d888642c056040e2140044880100407102c0e2079581c0c640d5840c03d01b00501144605550b89440c00340401d030007110a0003d0800240030007820030003c40700d9144c4000d0000050b050490542d41d4000015415441030015152181021200707109404106 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 481202607 1250 481201357 481201361
    0x9070e090d020d081005030f0c03060912070b0a0b040c02010902040b010e01020703110102013306050906030f090304120b04050f012c010b090a0b0a150c1712070210 72
    0xa41452510780104004003038459001a01c1e80f000b0007285001840c0352242d5602081d00686070b0001e0350103000e00a01c400300000005044c0c035903500300b0350880c0c1c00c03565503130700043d204c818040e50041c03504400c11042c00880c10060015070440d901c603034001921078036000084d0450f04080100c00250b511021400e041d4509480740400843c800e0030002035000740b40c1c00003511400d007030000504500c201c294140440c1d00c03d6200c0720303c1070541c8000c003052441150344884240b90030900c0015581e410000418030780e1140f0240c0307600d0000030f80000d01b992142500ca0f9491a001802181a0f01c0140700008084040340030f5020341c640a1020300c03060b8101400e05605140d54040001d00702d80c1003e40c1b41e6a0030201460009120380c0c0c030403c141b0040c406040d01ea001d8804405401c0d80200b023081030044c80c41066000482d480c0b400c0703403050f040598079036040d002128071954841c0813640c03014184012070002c00400d80914190340f2264503200000b0000200300a0648c0c001c001640a10760440c50308000e8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 481203857 1250 481202607 481202611
    0xa121805011a06090f120f0604050f07120314030604090204110d0506030a030806131407050901031401080c060d090803130506010b0702100f020a0b0c030717010b0703050a0504090509070e 82
    0x10b48951380751141c4a004a50313000c140c0603603240204d88145485444034000d000c1040b445003c0000c2d42c02d80d00786410942c1e074900030403d00c03076aa070051642c0010240100d5802126155154a6004e20390484908280807600024010358009407107020910050b616485603030950550890480d89a004100111003140d8000344414081d500c0b1180c0f80001c6504071140700c0c1c1c010300c111065005444507a07141d8020f00b20042091700880e0440d414050840e40040c09843c0a00e800e07a0308100500315042c00f035074208020702c500c0300c141c1c1007014041c2d8282440c00040c640c242c0c4148002c5008446952160142c8d40103c486031150700701c1c08604000c0207400e12106005208141e000e608001e0702d0740000d100450405085414481a20601450301d4001e0141c070180340d4000d000c41d4014503000c228641c1507403007242c41d1000144c50f042c00e5a6180303914080c42e410b03a01001e006504204403950161103d030302c480c1920b0244241880000780c40710280c007070700380b18590b40c501070304029280c140390100c04880 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 481205107 1250 481203857 481203859
    0x30d0b03070305060c1c11030105011103270102280c05100203091e040903030e250302041512050304080115120209070323010f14060a121805011a 64
    0x500703041002c5a0b0000d14140c204045803d05a83c0b21010900d2401010b01102c0d8260110704001c62450030010003000345048590a07210200c1403507240d80c0301500c03442020380d207000c1ca0425207020381400c0c0c0340008450b0b403540180100ea507030025030361400e80015100015001c02104260342074003080a110510b500502054a1801c0c0ea88003414020b900d0340030703001e820341c0a100010f0203107e1f80200e600900034000700c040c0040001000c1401d008020742002c2021802504c40c9881c00040881d04110400102c0400f2407440751040c215402c120150940340c81c070304040e48060310045135250607485d407062410300c43d1000303558072450004407609560100341640b03c0e924520344100020b040007040b207550590304a07901c0c001907440a80980050800d0400b0f00d8110184464160312a400862114180c41d1403c005141c1180c3da103c02d0702c0c0301da140300c03081078104030b09000900c14503001da030b14014224560710010034581c0b003107403a000c404280c1240c180ca0581d1904901c40080c400604d1003809018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 481206357 1250 481205107 481205113
    0xc0a0b0c0d0f0b12010608030d020901050910020d030b0f10030905070801051602010606080105090a0b0d150603020310050615130e0f01030308062b05030f030f0103020a0905091507051605030d0b03 86
    0x40f03483c504923220f004504100341c00c00d400044001d881c0e84110203c0f078042030300134240415401c802000030b66984d03442c900341e03020a160500c9800d07a464180311200d4a8200100042580031000204030050b0900040444e400d209801d80400c06560a0180d14801c05402400b1b143c2100c002c10001d007500c101e9448401030207802c000501964541d0700342d180e4006440c00001c1100340c1101c021400a002c0d010b4023420071101c0c1e24005503250318540041044a00841c2111050284000c4900c222001980ca0503440800310f54440c682010040c003410040803480132420781c0a540e00046650a14111a8040c564074224018401c054100308032581195040d03419074155150f03600b4500c8c4035861244401c0d0031055011840c000c010003002143c01d5512621005034980c20000c2006140c0c240a0004034461580351401080e421401d1203120710690341c100c000c29480c0000030507814205806040b480400504001e4001d070082080c2c0c039074107110310031001540d9400c07150722043c2c11200f180095500c01c2e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 481207607 1250 481206357 481206359
    0x40b09010528090225120507081b1b011803061d011e050106020f060105310f0e060f0112020103020d05090c01020c10050d0f021603020c04050601050c0a0b0c0d0f0b120106 75
    0x100d800380c090000000c60308106548c0e036410b0908013554000c4407100c80b20454400d0f18a09981004604d201e1440300c0b4541d25030624498200540d4011000100f02080c401d51007010800310300c0c0c80d0411a03d2441d648040d8402001158100b03013035800035080d1060600003246d06a8a2045600c61240100818800785c541c82c078441890940310365043c8104ca00c5010403d0b2102c14610790ba00512003020540d466006589010145101c00b0300352095008500718a49140c4006210340464680d100d0052620005441e82c2040d80070322000c181c8113016410564248030b249161a0607204245c09081000024401c1d40c8007000021324042d1100c2840340510003490034403c000d0740110a4400c0c25284040c0801c10b40069000c1030001d000d050202510015948600801c2c590089495103040a003503406102076614000103448500c100b00c111b40d4694440080d41c004900180f0507103401031b45030541d4500d015403146100040e103000041f02210359558490346441494001420410051888001e005507 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 481208857 1250 481207607 481207613
    0x50103120804210c060617060406020c030f041403010501050f101b120804060608010603030e1c0c080708010e0f0606090c190e0906040b09010528090225 67
    0x30402110950060003501404030b001c22600b09204022086862500d100142c40042c00400032961440261482031038a000881d08036074805032061380051080050005480799510a4004d600c1041c000302180002c2c481c0e6014008101300903c02405106541e0342008007035001c050840354182e003c1442041d0f800420000c4e51640c80c241d1752040854101600291078000712150300c43c00501004100303100e160381105181c0d41042c8514000c40c0110020480d00d40c84078903090803107055001c06004500f00d000d84840d64580b9560150041c425100d058242d090f050f03803581701c500d0641d0000c011640220205000d004024489c42c00750000410060806010820b40c440d201c0385c0182140b40900c501c1c00000b002c1c032030040b046441e0410030011400301f000c41400d00528070740c0d00541035482682c101c40070548602e030502906800703013001803d070360070341c1d282604002000c110b40490180350164003401a5074910005600c0006140c42d990241e941c070401c40111000c10740c2800d50a0300394100d40400008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 481210107 1250 481208857 481208873
    0x103050c1e0d02030109080408060f09071202040905011407030e15010b03130c0b03040302010203040c17071401021006120c06050f03010e0621070501080c0c10020f070f0303020703080109050103 85
    0x704001070398401d9400d00c0303600201c0d016003c003140203024244000340002c0c03d40c03400180640b048031701540e80070958945c0f80780961a003466105171030070744256805107005071405502c803103c032038412000050240f40c410754644e5850310444070880841d55801c0048041c03001400203648040c3c0c20103070700404d507041c01c0b07486800f800094120242c4d88a05400c64040001c170309650320150006925944e103924051400074040e42c4204e07404c032450740860000194880d54000f0b0012403000c6035018082e060300b00b40d600f0384819203080d003181c118030441004c900b0f0790300c3c40d119007000b81c0010309500b1103205185c18208403a4401e64410010014100212200c400c20030307007560f05460319450b01e607226485010000c2ca998100b003002c06412000541881b0b60310000044031004c84100b82c880700d041e81d407409e0300a203071402a07101da20144d4004050024849540394020900045004d024070704020064552040c286c05000c822000b09500184c20410f0540103803185004004250301800b4960555459000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 481211357 1250 481210107 481210159
    0x13020a050d110c0601090515040509060708091c02070312210203040201050d0204090e06070e010c020d021305010e0709050a0b040506130803031306110405010e06130b040e0103050c 79
    0x18459641c503038030742c407920190040b1015032000d0000c0311220f503116015a0010b103c01d0358810340c104125603100402d41064020389102b00c0c01d890192500d640e17032480686038101e0042501040c2d000d010713400380c041d130a1140e07080900c000315801407140074103500e00001001d031200d4a4800780300340e119a620070a42d200c94240c0166403600300c05602c2c2d80b524801a5501e0095016180f00d01d03002040109a0036000d6100c0084c0440b444100c90383c60b00c90f1442030340d8040200006a001402c0b20300040b0141c00c0c000024025240f025100b0301c48000f03820043c000300d071020382011505944040c28001c505910950b840050a070449401c01e4403890b0481d00c5040348110303c5114081c800100701070b6510700a0f061a100204040000c2d01c1c3d491801d411031140e0040000b10850340a45031034072150b6551100c0d000c1e40c0a5800607110300601d0000c070420001590410190910300895640001c14040ca0000141004241640055080e5411443c19030b0608a03e059014040d44458090701d611f444241080a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 481212607 1250 481211357 481211377
    0x80c090609270f030f091c020a09020a27051002060915150a0e1f0b04060806030a0f050604021002061b090d0b010e1f080a0201050d021b070513020a05 66
    0x40c10044168142c10b02c20f441d003603825039020101d90419900103d0000f030080400440d402c1c00e03081c0400402002c4010500700103504500e950348280700102640e0b009010130612814120501a01c0c40e0895441d0908020ba904145540420800c0390303040102c80c50301d220240340081c14491500e8001d19030394810340004c01c158141c41401203041400d1902030040d003401d003d40300c2c501483c1c441c880301c0801c40c002c1d15001079160282c00021034080149001c1401e680c1062074540ca8541351800844800320080c100799898040e405c0000001052001c24441c0103101d00b000c1d04444c5805d004002c480c4003030340088401c0d50005820004904401101003414100c640c800507195400c010200c0c030211005940180000440000816441c9030806100c0c400c02030050b1403550145c14801d402a4001288a0703010340c0c1d07100040040040d0f02030070203042508a03c850060402c0124078a008600c06140e00d40c0210b504014000c0c04a414200c007030074288a031110041d4a44692400000c006210b070070480 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 481213857 1250 481212607 481212661
    0x6030103120f03060512060103140304080c04020703021905011a0607020d060e03040801111312030912080f07080a021e070e0c040b040609080709182307080c090609 72
    0x741c40c1680240e12103009005c01405502e400d01a00e074089a940e0428001030b0f51409007054041d02d07400e000000c4400f80c816010180c0940380c09201071001039005448101e007580500141150382c18240e103e0f48100500940000c03071001001c607050358850041403056030041508100031005603c2e0742100d6421130ba808100012000d0788480c0440c198002c9400c1207400d54207119680304025880805801e10b620b070225012801c6948500e01c1e00e40444140340107011950010b010401107440c140300a44680c02441198039054403003448044540c81203404075001c02000c502d00407040e504202845032510326800e140e2180211410f52507035218075100e40701c20b40b0385650005808000000a03030f0000c00005504a4843c0d407a03000150045085001d100c19500c40c00100142c5521103001d0004904400030044250502e40e8503668015080c40b0004451560180803407501080108003900040101c04050200c1000101c10840451005030050f4031800c0d13120107005115042403e0440c4182c2e4010038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 481215107 1250 481213857 481213877
    0x1e030a032f210703090b3904030813060e1212070201020c06040306051f0b0f090d0b2a040f14120712171204080a0315230603010312 58
    0x1c03182c541d030102254401c52030303044018004510b4040e0006a02c1e1446894203170650b40c0c030100d034510b6010104000591210320403e0901c503903410744040395401e1481c1000340b0300e002c1e140d4641d040f0940c4401d02189045c40780003400c10070141d01843c0640380002c12100d900c080000340b0b00e810307074070380f242c803100008188001400021607001b08826184100007428454840d80d407400c10400500d400c40e11440340000c0150341381d441d51940b081c44000d9440108109045c495210035140700c41e00201c10103a00044074031041008034001c440018420340780c103288402d00c410740c9460a418890ba808485845003802d0105010010201d103891064402c0300c0d55801558802400080351440e00e1078650044d80a14600400c0d141c1448514034421402100c44050355400309445035010310950310022400f40c80d16021900180518000348144105440c6c0070400340c003201803015110144d540141c18032100243c0c2d0079100528605854205501101c0c114190362654469002109907021707510108001148 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 481216357 1250 481215107 481215127
    0x914120d0608010e0a11010918050103020102070602060f0a0b12100e07090603020303090d06060f0b0a02011a011b050f07090501050a1a04090506040912050a110613030305091e030a032f 81
    0x4000c0001e00709c01c010508200000303000180104028041640140a00710001c0f8806000042e0207000c0c120311020303400503030b0702e06001100818885d079000764001a00e14609407601c07010451484403c000c140c0001d08107052000361468404180e000d9280c60f803c00d02c040000d641c010081d81c0c448502a03c54600c00c00b410325024005100c2c039041881100b261010124484014601404400a69030001c2108050024a203101c140c1c05440c510b0014611a820500038002d10b200b16601034442c0013152171140c81e06c841da505042445c1c014506c0146d60b03600420050cd4820320200c001c3c01d400c0260100b1072810998000c0a21440c0545848640c9500c00f0403070390b843c1d541c4190300042d00124050340340640c9d00c900800c1580042106400205c1c0e0201424080b5004104140241d206c3d2054500c1c01c4c1c0f03959402d50150800410003c51802080b0542c52003220210401011600305006540d407080030100140c03c5424030003e00c042603561304011508100c3d56260080250305074140161989220f134 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 481217607 1250 481216357 481216367
    0x3180c280504020a02060a0b040203010e07030c030f021b0606102a0c09050604050f01080c12070e1611011b0309020d02032d0a0f0201030914120d0608010e0a1101 71
    0x1501c039a411510001c0d40413a4590b0110b810b9004e0b060545081c495114080101b2007680020700a00c0c041168a102141c41a4001c0c0e0184280c2c40035800c0100305800020b04100480e000044c0c088a03411407444130b618400024060f035a0310690480d417901e0b1710003403248001e01103c0045c10944142c5044800107010f80305c01c4a09205856100250303c032002d4407408088068a0140d9196003da805d0030081009903001c0f450490580d510400107001c40c0f904601001140c14102420700050b001d02280460450505034905100390a022460000e040e1a000010b140d019216030906480c1d25003510300e08440401c0e006041c60300d0243c40c000c24082c0440c0000b0703818a0041c440254184510b5100d01e4441d1100b80201241880040c00107200c18039101d100d40e1a0380241400a0081e89007806138001903000354410105540910200500e5031002180c5901d04810f03d5845222080e002c501680305900d140a61005446200001c0c491540507240d1f140c1d803885600e100500c20b007044100146141d22030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 481218857 1250 481217607 481217609
    0x20c0d0f120f1a0409050c0f0402070b010e04050f1c08100806091c030c050417010b121f06141002030c0d1205010803070c18110a030203180c28 63
    0x1400200040200045140e00030f0140799003e003001c19a10034891040d19085c8145103c0726001409800c00301c0c0480108480c45860307403030700b503803080c0c0c04d000340c0002c1521040c0d030034080c2440039114400d0f41401d041440c03801d9810710f40310800b54010804080036014945a085c900342c0c00782031902080d01c41c1078204107041d016030841c030b00c28801c9404018242400203909090b0216000252403001e4030400220161482159440e020075410081002055984080b81c00d502042900010390392454000068561007850340e80700c030647c044555149408100d42c2507108100264104020248c6440820398401c94040c0c02980300f40e0450032422201d0703009000f1551440b1030311040e60f00145040d0805415422161030042c1ea880c5880008100c068000085540c201d800039200c42c41949014038046660a1015010410a4544030701c20f00124008003e0031803402c10b514056121b14056031610100301c4c420b500b01c10076900803c030038805500e44449c00c002080880251314000b0301403c4110701d4140c41 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 481220107 1250 481218857 481218887
    0x3050c01020d0509010b010f0228050102040510021b1906120906050c0c061b0405060f0d02070309030209072f0a0203032b020901050d0e0a170a03060504020c0d0f 71
    0x140002c0107013045066005840005007602c446132003402004040ba61004c1446c05d803641c0e055014400381c43c054212600b1030701d60313228400240ca000c0d01d0384042682c8034040103100015a000c02448180c1c000300e4018031982140541b54080d0701040510f02c5c0030054001d00c650000c2c0704002d024028a03102c560411313103206400038001c0c0000e0804858180659005241c0301d0110b0107414013245000c140c0680032160a120b8041041c106420002041001d60040d8411001c1400400003200800418005007000071f0194880802d4149180140010305200422410411010940c02c103101c0ea01c5034080f0925841e483c50103d1140d0b401601d40303160100c00030000c3d40c10f1001081d08010f40942d0403401002c42081e041c80a080304140000e0310a80c041c0b00141da000c02d0081c000d00c02c0b001c085500a011100c03620080311100729040d158013240c00c0c0125040007040c2d40014002000700d400d17000d040d0041105075001c501c2c05200492050700c0710717006c0c0d43d01810041403880f00000217118230000401658 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 481221357 1250 481220107 481220111
    0x1218020f120706020309031504020901051504150207061403061003020d0906020f0a0207171002030c04050d05070e01050f0a09020711060a0305070e06030412030b0a0803070501090219030f03050c01020d 88
    0x6103c0702d01135601d0300915141840780c843d116141c034001c554010050700036940901540d103d85d017450108050210703000c0d9003a0840005010000c0d41614040d0f041400a059402400e8002d050940003088050242c05134802101c040051000c02c3e2207198003420110501d141c0141c0f6541004600380107000c18040140c0302c0307400801c0302c94100c040040241541d1040b0303000c88000c6662110b21900f4400004242015074003d800042c08042071034005650113140c40c80c40901e043c0d141d50003e07918012400c3c0544081e800581d0078400305200d000058090501180c0d0703120950260760020b40c4482490003113000da1a00030a0450030030071410070100180c10b00070555a03d4800941004008100c100d49035000105080d41074040d5041036412240601e800140d445041d4100701e0054005e0007888055540040c504007001400d01c0d0b0a0010b0305010344075100100b0b01000074010030041e035010056a42c004110340108100203114a84c1038003602d503250600e9030311815200d061500a00801c0440c5103101c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 481222607 1250 481221357 481221359
    0x61b0309090609020d0e060408040311181302210c040b03102f07020112022107051210060905010f02120f0306030d03050f0126030f04061218020f1207 66
    0x40c04d03006015080e0b00041e040040a14100c001942c80304280c40c090300300042084140081055150b070009405009032034940000b0307094003c81b034000c004862480030001070120600c21880d207006004041c1203a802176003130140703044810340e40b140d0402c1001d0b840759170b0f2030030042c220b901c0034841c254904c1480303141040b40300784500101904442d0042100c6d0211074800202600c5803000c0c00b91104a501a5502a0b40300003452901009500000c1408409503455070300307121405c070f03000f4003502c01d22a070b54a480d1501c10f0507100303401c486000b42c628200300c0071208090200d02c1e8005c00d04400c442091918160214121005038285141c8100e410039400c40054800704411501004500483c810f40071642c224106003412801c0314ad050310361070500c0807600010490766000905401030454010070486006418100300c03480c651090060100e414404217041003103580001c04840b541130340c44400d0042040707060743c9180801540c4402442011488200f0380942c0f0380d10345072545000800203c0d4081 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 481223857 1250 481222607 481222619
    0x3060c03050412020a0f02012703030f17010b030720030706090b06010503130204050a0e0a0606050f0303161205040503160e01050d20030a0503040f0f0906061b03090906 74
    0xa8481200c050301c000d0034220f100f0881c40d200046001103180c1066802203101215401140c0c1c416003070840d81c11018a1030f0840d101c000300b120104004501ca61a00510001002d070041c1c0984224990510108a01c0780108a80d806520031283e20030250701c1c00450a03040000c3c400050051080303032280a21002c5008020000681e00c00c0301ca181c0244c8800e05160307540d40044440d484101d4841418210941c61100181401e8129030f0b0086c000d02c5010074003d0246414500c1c04041e40d10540714584c07150410806410301080d0b0100003001500598582080001c18921805403250020701c40054008401300042c800c03002d0342d001e044000c00342d0755500310011401480103a0b070300034580e00e050114000a0720385811006080015801821042d542050000100c070100300205210303098007170030100100142007480100064409403012100a0341084000c54200c141d9400107100eaa11b48a010f01c000c0e6000f9081111080c0038904915512585280c11640c00c0c44503840489003500305800440d80d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 481225107 1250 481223857 481223861
    0xa03020601060201060906140d050c03010216021504051c0f0b07050a0201060e1005240f1207030903050d18020603191b050901120212010e0f13050601120c03060c03 72
    0x102d481543c000e010442d16110349104a4080d03115881c101300c44c1501400040c1086206180310500400030350b00355081040103c2d0a9910400f5540d14090840c405072085140021034107044906500b000341c109800c20b40424441c8070040103403c280303c4810170361400c100071641640c2c18580d01c40394002842c1000305000e005604440c4400002d07500f00500425201c0d03400e9009407180310107031060781d0500d240030240205403001e55028803828141494003d46048507200502042e0462203030300b80c0c6c60030340c810440e25000e00601000d08050070f1a201d0f10200c6d40c4842929404903240e0310004000d100d040c0203844240e0020402908a08003004000844442d1100000608601202802181121503c61100d1007280b200b03100821805d1240016a511440070f038901d110311410b0040c6004002c030030000038007209030700440205032400e040043c00c41000c00c0180e0400d02c400d020b666200820b5403102d84400b014041d40b000d1303c0f64410f0b02d50030300c91641800002150004810400001d0302400100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 481226357 1250 481225107 481225109
    0xc01020d0902090a0c140c011d070e0a050f06060f0702210c010804020306040b0603070306020d0c0311090a0302040216060f0b0f090411090c0d02181e15030403050c0a03020601 77
    0x8801c3c100000043e00c2010540120204880c040c1d598100c1c004524217582403982047c09101038640d61602200f150140c5180b10b074000f038100d04000c000395490710f03c0924082034000c10140f00b0a04020034410740300c110000103600184111110358440042100e000f0b5039009214020358040c081841c005000c103090502240c01c1584c01c02a6081c200a01c801500c45a001b0780d0025010361003140002d012030503c44c1103c1d0801001802e90700c2156603502c035031040c0d80107021a03015542e0380b81c808082103a054030030a922521805841401c00c580c500005070701015500c0064025500010110781c801d80308104118207603444401002280a000004d03002400c000080b50f0088140070150340c82403512aa406104aa0260340c0c8035015540f20103101030800d02409a603e000c0c2c0c2840510703145540d0740058802080c80c500c5a00c080344642d07007000742d00b0000c078400c0b24144c0c40c00c05000b0001d84600441140750000100040d982e42c4652404803124404d0700b100c000280108400ca0b0101503011414078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 481227607 1250 481226357 481226359
    0x1103030a0c0c0f0503030d0b0f130213060e100c02031f09060501090506131a060a0216050f06180a0510090e0a06141002011d03041d07020a0f05030c01020d0902 70
    0x802c210348903100801d080c1001c0c0503030355059200b80300a55040582d50001c1c4802c800103090f41d140b65441d00045102c140d2590441407101d5000304c0c1c0c0704007070810100c1003c01001c1a00d03080d80ca080303400e008200b0451440d0514020001140303608001e64804110b8210b4040355000c0004030803114000c0000186084030b0704441941c01c00d4000a00050305024550041500510251040f8680394038030000f8200c4074003120103c401003100800da603032000007030300e050310040d00a40984030a0030121011280e05402191045000c1d008012250301c03500c090f150070700c061941c0d09072045594070002d1141d40b415031110f80c0c400031b00300c2e13540c1d80780394401d52103002c8840d02c511804054503018030250036111a4080c400c940c20205181e014145130066a450410b11140000034510f02c603000740d041c0035000508600781a5100003010030102020300c0c443d101c800080001c1c88203e0911490081d10b403550740300c000c1c0404d40220b2035801400424000c650480d902400210740e11941400c0c0c100c007905282c45c0907 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 481228857 1250 481227607 481227623
    0xe1002070209011e0b0a020705150a020114040b010b0a0e0d03030e21031314070905100e0c030a0c090b03090c010e031b0909030904051e09190206071103030a0c 70
    0x360240c14404013100c000c1400120301003030b81880d0300e080090300305201d10030840c403400000184a031104c80c0c541358660300a9a2a5035515030010000c0c2c2901d164040100c0b030607065804000110b40700d01d00c05030540d0820f0f41c1d0a981c9064000044407204410006164841c491000b26410544c05510a1604442490640307050050002525000180c960303078860001c0e00400c00030b40c00030001d0000601030fa00c1180d0601c0306428aa003100e241600541000c4d0b00c040c0d982050219050002503040d0060840040e441900e15006002d841c9030300001c0c0c070400c1d6198032110418101400341007020040c00e00c1c1043d80b62070385407501f0301d982d4900078801c0845c04110008000c80c03403424041104d05502d0110740328484a4602001400102c0c9801002e880d101d000c00e1000c4c0c145544c9a000341802809042404502051780920100c9094005004845d442e404922003e0301000c800c404007050b40e03011104180c80321510b0804481c030044071a84240e050100160900110750003940c0d0118860003419a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 481230107 1250 481228857 481228859
    0x91f081c050703020d0c030c24050c07020a090e1903020303071416380a050703060501080c0306061317070b040501020c04050c070503120708130b0610030e100207020901 74
    0x195036a10440350b002e40141c11500c220740340c0c41e006514901c06544030349002808007609850344455000c0c01d420303a0008414000140350012954020240c2150108501c1454050107a0020300031104a21a009080c3d0316036042040349102441800c10b85801c8501d8841a10700905d00251a40d1040329050046507451000072802018030003950010a14418000a2079040352500f40d2400780c8108465010907440200b00b0010340035040c40a414080d000907203c05040c12408202510002000c80c0b04052500b201084039a0307104001eaa0414071f002c1d02d0301e039252211800b0903050b00c21414026844054800001055a02044000a01440c00c0140c2e2405621448848241d01c184d00c50f490041e440382041c0485450594091600104032881242c07500860356102c0b07003183c01907044d12004203d50030821110980081449901401507a80580c1d0080c3c40e80d624945402c001c0d02060203000f408800280c100d00a91001d401c0700400310440d613516009600000c081d40c0211812070140c034130100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 481231357 1250 481230107 481230163
    0x121e02271005010c110d06020a03140a0b030d200d11060702010e030d0e0102040e0705070b0a061206020d02070b10180e0601140a030c030c05041107050c091f08 70
    0x940003602d905945601011000342c40d0a00340e20022802035522144a81130000059114130050003d5640c40d10007240c40c502c4a412007658080081c00646054105511820300340d40100f00c015519410b410400e210031a9015158251200c103540307000548500c104202600b074020201e540d108070003104460840e9695071040b800e0394402d0f554804180d00901906060070100c0d0402007040700000300060400c2c0d036585650844e02c0301540c0f0a0302165000480c070341444510300c0710380c1c2d202d00c00000a100c001d2a0841d2014100700d4000302070842503001c5802841004190102e41100d60025000307403041c1012894001800304d14480d4298400c42000c0c01009000c140c0541208504524042c0c0517503881d08042da01c040d14040140340d03022040800200000380700c0702401014600a1031121801c904040520080310041110521103080900c045c1002070350004010796200300079a4480302e261110003820607240b084865003581c020300d160021882c1c1c03200250400406440243e20307091034030118 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 481232607 1250 481231357 481231381
    0x3112508161118270105010e0603010501060f09050d0201140304031e110703021002070b0409050405010b150d1d010e030c0d03061a031f0311010f0801121e0227 70
    0x1846440300715125500007824400c9401030a04d94620008010120b2040114141d085400036085000c129607d0020f1084908003445254094202d07814400c28503590804081c01c06880d034410b042c455121051090216407050200340b44245075030224a850b418103203001340444c80c000c3c4d09503030301407450842d00b420288140c03240b1001d41c4d00d0780041c4c00b03024190703000c1c410505207402e0030000354071981000044010307c07100240007c2c910401c001401e403c0524044d030a5440084216204d000790090800a0740c45043c111008501c00314800980c2d0724100c91514084d0703640c0302030000700d0b51900b0034111310010080010040400ca1700c09480c24a0b9034840194100e406a01640c0304990120501c6200000d010005580040d2070228039903074a4108201e100990b0000d80040f02c0f000403503403144541d560044401c8500100070b042c051000c0d0705004e03503582840100c65002c1c0000c131591282984612410101d07803582c030307006403901d034001103103400d4070385c180d13480307c80805100d040c41d030018040050007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 481233857 1250 481232607 481232629
    0x709051507060b1903081b03040e01080708070632180117010308030f07111605100801080316080415091707030b0c21040b0a060501031125081611 64
    0x30942c1000d005d0850f00c92214680244002c489814800c0c10740b00341c017a000300301401c0188048600a42d141d81043d8145041018030f41c41039900b548400d0003400211b4000c210304940c903d070282c89100b0aa0f0149500700c1c040201400300004640008401240d800024495003091100f0388030400c0001c1c040c801624040c40074400030b007103401e0510118800040e00c040719508201d80f0f1070452504400102800c2c201002191500d6181070050003c01241c140a000003550803003034107001c0c815602d401160b42d26445006c03a00140d1404110000c01009001401e0782e0240c0b00345064880e902c0340c3ca00b00074140c01654040c03010f041c090551554070310200010700e44140e0b0360001c0b010700c06403900000200c3c190061014503150b02c0001c0e14961424001c03480c900d2156014410300201800c1086d00d0b4000c80b00755801c964105801c12110a400c1680401154090719039030300103042e80304c1400c500c950325191000000b0206000016448800d210846138407940c80e000d2081456100ca07070204115190a030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 481235107 1250 481233857 481233889
    0x60a0b0403053301140f0301051003080d060306020c0a14071d0615030702010902011209080f0307020316080405130b011e0e030a030206180c01170709051507060b 71
    0xa400b410511281c000c0b02c1030b0801d1050f1982602ca03200c4401520004100360410b841191004d080503000f403a1000071000c030000164002c22060900c8040c003040800c0a0101504881000403901814807240c0d100000458200714210b4072004280d002070341391981524251440180c5890024440001040304011030708040c1c0001d0b0103403640d014845488800420440d4005035520380f1042c0060f85000a40c403400c0594000107542086100141074413a040e02356929142c0f80c180708400203001c103004c031005950314111807a126514588101d1131803107140096a0040940304404041150407006401a294200c0d4151920031142c89a80100e419000342c060000d42d00c1441144003001c20002c0326042031007454496444400f00b07010916107841068100e0060717026100b000507a100a010481d15126004080c10b80c42111400003807090045081440212041402051426003d000024010680030f40011407180807800e43d421030b60800c07501600d1240c1001c100ca00759281103d105200000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 481236357 1250 481235107 481235113
    0x5060c070e070c12030207031d010e061305040624050a090b0703030906050114030613020f2e0f0e030c13021303020402040f031a1501030c0203070209070503060a0b040305 75
    0x4606044440d01c100040e003036606004040c25014086a4030140180360001141c13009070b076072120b624005200c80484282d000d0703d4078001300c07130b20b0b01a0b80c840d40c65040710300203e900715143c400005a4119011150b0310403603005141480004112503030a50803040e03200c10750300070001e45000c20402d4400d4031514401c1d0002a400c2d920511404036004080c0c80700e03600034a40048c078100c240da900c4080b1070082c0c01c519a80c0040c4041c500e11854100030b201e5101d0745030351000006180b81e502052010402025182c4241c201c2c44c11048000304200044142218030f8080600301c2d200c403c0302030912018900403400141d000810f100881c01c0c001201c42280801404040c50b480391060140003d400041c180c5100c0c444810b00040075942c0e07400944003802c40740880c10102d074a580307020300c60f00010008161203510b0034001c1086000c00f10100c3d1307030000e01c282030100d60141d0fa04801c9085104110000b980140a013041c084500d50002c00385218100c01ea41c2105115207907078a40030507018511000b030003a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 481237607 1250 481236357 481236359
    0x124020705010503280f06060c1e14030406120b012d140403060b0301050619180e03071a091f0c0219030f0810050306040636050705060c07 61
    0x94854002143e02c0242d000401d205c0d0100008003402500c981200c0200e03060b21055000311803c0b881c401d14004051506240c5410010707070342d41c803c1c0e07003c040341c140003805e246054490a10901c140d4080120804505890355213807030780d0010340b145100ca07103d001c5070703881c1c405212038035400f0f65260b1040009070607050402198055150602070300e00301c0350794100141c40d0751152010900f0005000603510402010a001c030301c400905086171001848035104840c48800142884294884001500d0062126407111610040301e10b001d0b05400316400558800014101d0512444481c003a046901c46100d001440c1c9403500c203203607100c044204141000d8101c0500140c1242554026410721a00e401034400726160f50b03602c4480b00c1040c0c03c00390082658100070244066110700c0706d50b440107043d20700919050501c00402e544110052000304540d540f06603c205c0103503013250780900501ca23100012010030382c1210490b1003062451080310140310740500400e0516001c0207846515020710b00402002d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 481238857 1250 481237607 481237609
    0x5060a0c02030c010e030910080c18010203041221030e030a0e190803040807060309080409050a09081b0f01020c1c11010f0c0e0f01021f0e070e0124020705 68
    0x1003045121140030752204000151940200307005043c8510198405580c44001503400e0000158821100710100b04040e82000500021001518080c0440800410242c11003c00503403031841a60070075205910070708078000810040100700480c58a0700404081440320b10305050f000d48403030708403170040b07601700f40b14007446c01d80b2851500340080741c005d000c122004604011410010000e8001030a83d4000003024085010b04015200046c9441e1804010801d4182c55003001c50182d806141d80090f110004141c41840540004140076000f0200c941c1e00d40c0b881c011911059221a030840540c058010005c4058406109482012188002926020340b01071302c080300c40d906000086041c0503e00c0f20004203001d00b441030000e402d03c41c1d4000135000d0441a40a0b008082400342c240c45801c421178102d580b40d83c0400c840e9141c4003400c00440c9015503130410400075100c95046104c03580310304d140c005421680c51440604a5a4200d544000105450881e00e0700003d003068110142e80401d00c20891 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 481240107 1250 481238857 481238861
    0x6180807050607080d020c010207020907020708100f0e070b13050f0a030f02060d050901090b150d03050f16050106060f050f0304020f15070302010b09060a0602190c27140405060a 78
    0xa075101e034404600c3c117070300d0388402c0040b60000e20760295240c1d40802c0e22821814512340c400c0c1c2201540c001080c4451801c5601139450b00200102c011a07520f0300f003440d0345040c40360040425528046c00f07481c41c06482d0b00011000c0c0c2c0140103121908a140900002c1c41e0410401c00e00d00d035600580f181290505649a003881403802c104100d0b0000401c100094459120740304090080303000360000f00d44030707580e4203100100c0c1002070a641041e108081c451140c079a06c40321141c41c4076615013480c42d12180003240e00c035003074080c190b80b072802144122803010030010190b00660603254561101224010700541c00c8886010b200d1003584015010404600540b602c034140c040a004001c2104403424545800c03200160007080e42140940c0d1640d104c40400d1828856071a03100c01c00743c47c034800051270020000d617910301a4100140c18407650303500006000442e00602e0142000e24060620340c04090b07203a01c9049450750503034602514080688030075680ea020494041c6030001d0090500307485442141c80 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 481241357 1250 481240107 481240117
    0x130501061d22050d090807140d0b15100305010e0901050403090b090a050d06020c0d0f12050402060c07080f0111090f0f040605040f200a020d081806010b04061808070506 74
    0x400c002d10000610000f1810807200e41c0da59800d40e00c030320f01c040c80d22440700d2078020f0a82151000da41d207181c0201554440c010031030341881d04040f0081076902d951008041c6030320501c60407a00440c081d0480300c0707002d4250b04031504070307154219041c402d0350300e001a150803108140c40040c00503088040c2000442c002402070103800100422000e285070b44c410016146680040d01250703043d80100e11744048403410b01c14004c0c0d180322410300c4d540305410140004c01e42c4448180700c42070a580c0b4404241551144429a28911514401c8403c460b85441c061a982c4840c10a03c40d903660070000f01420b884054819184032100160400c415008801d0400100b0b8141c0e000113a082035440e5800501d50303660f8003075840c1c401d0700700c0b000048203180d001d0143e4541c160000d500050135010800a090140e001507034040e40c9049190003c0726813203481101140c0391004040314a2842410004201c014400b40140300b19040c5440d210f42c11501213800c24019059441200000c1e00706040420450400c3d2000340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 481242607 1250 481241357 481241401
    0x190c090e0a0b04150501030c03021f0905060a030e01050903070b0106050f0a12180605160c0c09021b010c08010f2c07020f010e030417070b03010306180605130501061d 73
    0x21400f81c0d04c0352040310850350300360700543c2c425419100c100194205251140301d100d05221085c4031800e83c000c005030440d001031140c00d00541000500c5480d02e0310a50114140b40030a078000c4c840b81c2449042e06542350841c5500b0b482c001020800014a24050000c40c1c146150075040941443c400d039034103980c04c841301810340e40c0c0a0744035040c3c07003504590022a070038903501c00d8a00080d10308140d4440c0c680421519003030030902c00c4a514410114a0a10f4803608440710b4400141e40d0301010984030384124580303600326100c0c0d8244660b601c003854100e403955050728035070b404501c0910381e11258140200440c0c0c140c003410080c0010209011341313282072940c3c1d1090030360040b9400b10150700221070031144c1d83c020b090380c15000807401f840342c04010000000c01208180040511f1401d08040070345130300c0706110041965641c1c9080346881007908060744150f6800050400051614040904115242c884119525482c254000c00c07240301010034150321940400401c1e21542e91003c50098a02c0702050035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 481243857 1250 481242607 481242623
    0xc0c0c04022808070e1c0803040507050d0b1b070201051b0712061407020c0603010608040201030b04020a05120a0c0c39080f011b081305190c090e0a0b04 67
    0xc03071080d4500a0358200a145581c80307070b5107850001030080809040c401c602e4030420790244e0613008030a109480000944e00040c0320755a07900e030740c980ad074502a01c0d544115040070700f149010051210510841e882080d100c4068200740006040c502800d20613610000d02041342031058142503441c1c901c00d9440100c01030b0488150f25207412104040000030700b4216107603600c0e5810305a082e55448203c0307800c00f9290000300180f8002e03400182060005014101c100900b230800a81961300c6078110b16011180a4421981c4900000004180d503100340302c8107407811020400305001380d00510070545a00300310703a0b8010159110f903440032780c0340f2803c81c00c0305000072004103249800400c18060b03000702d4150300c0312190601d103005000ca0130210a9401c40f0300300d034076155945541488105a1080c541d80030b24019015507510000310403900360320003020300544078000c51f024055070103144520f009409180c1041455603501c011000391380079040000c85a401246403080014501500907800511620306 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 481245107 1250 481243857 481243897
    0xf0304020d080d02090103110306090417041503050103050c01170109091406070e180408190210090501020901030e0604020f1c0f0c0303080a18030f05042304050c0c0c0402 75
    0x19542c11900201009600107030b002522050568240c441c59028034800e0000b5402d51911038001640360b080100040e000d1a804650a200000c3c558100c4000c1d1800b01c01000ea1342e001c0840050046c0002d0100315481c3c03107170354081100c03036000f000d0f02c82c00354481040064090b820151444040c02440ba8110785400c803000c40c4c1c0a0b4010700f84219446600156529407440a65404100c0503840090b44464903556940506c00421364500c00c42d6820881c0e24a2003446074040803080b490b03c1c01c58003c07550307201e1410750360b1810403506400428425501b6030b014042d05e4001000f003600d451041e14004d50014070700d6865812821f0a01381070380020f02240c1d9a0034914841d4840c6031007000c0180c411184803150007014020103030001640c90700720600b1002080001c00e03c0408086d140c000b58409410320008092980c4603d105208480151500c02007840000c0424165507414071851100944550308100c005424400880e050b240e880051100400003980004144002984a201a0211040c4400c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 481246357 1250 481245107 481245113
    0x90d0602030103061a09090c0f060708070c08011d03030f0406020c0601060206010303080c030708070818010216020f040510140a030209070c0b07030c27090e0a06060506030c0f0304020d 81
    0x102460003540110004074061000d2021700e041d03201103003ea40d100f034004d5810b00c10403000c0090782007030200c001c1d80d400041d03000d0380e000110079000302800103180220000300c1c1400c01528021700822114503100030b00400784000c828010413501c0902c803a18640c818400692030018450109421038002c120051904c0d002c043c19a09102c001d030800c00240c0c0c420f4004104060b0b02000c082d500c050200802da00b94207082030024030180c80507000004001006000c168045c03484034000e00d07842108802199a0704a00c030008058195080c016840f4040102020b1a10304160007000e00c0b403108510400c040609200c0104410f410014540d03420017000034020006856680e4464000c425584890b00483d40c1854510380d0f2210081c850002c243c201703252000400e412081d80102044440f4484d400e00688a201c500048019801420164184000551081c07030100708590720b18081c040501025883e6414400688400d68009003500c02c02c00c280c040140c90301000e10b4100c0e10080141040c10302d162 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 481247607 1250 481246357 481246361
    0xb0406150c0c0608160804021206100810090b010509040807060504030c15200c010e06010b03180610050d0302011b08090114040b06040b190306060f080105040c050105090d06 76
    0x49030340004561454000028441d0031422800200101d2034800d00c10301e055140031600c652005058414446074401050449d980c440c012444031059030100c407410310300012030f10038411851042013124000e0014800e20105507024000c4c5a07900000c280da0141d1800d801c0c40040c0400078800e41d2a03030800d001072070000e0500e0003028051400396980d804240c100e820050302c014400103800314068a0440b40e0080340390210792020402d0041c00200380c071501702041c00c41c09440e80c000c2050b0180075240002c00c501c51046c5c00345000c4c4c2741c0c0040741c0c3c0071002d8801409545500a847c441007060200b0010061480c10524a5502c18400d200120300c031900d5281c440003900d000030b020340c0031400070310400804034401d2003007a0407070715000c0100710030307041648400640d0b83c000741c1520700654407001e000709203491348a03242d500344841d100e40d100381c15640c0c14000c00528a80c003410850200d0b6501c000303909a07050080324044c541008060f11050728040c01500d0030344c0f100c5003080e00302004800700c1010074854 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 481248857 1250 481247607 481247639
    0xd0b06121b0a060e2412040501060e09060f0c0904110310031101020a0f020f0a05100e011803150906330f030308010b0a0c0b07020307030206010806190b0406 69
    0x105201c910482458420010325400c40e80040081190042c0680c800ba50703880440640c0c8178481c1c01c842d50a10301c0480358000340c8105042d8800e03450300441071008200f01580844121000f06007040d45686501001648805056a4414610707062401043d003c2c880c0b0002030040890040c070000c0c170f00480003111240313a00111078501880c0c008400c1001807000108007012484000d00c0608001d2074559121616241e00c030324040d00488617108042d03110340329040840e001d003d004046048003208031000500c0c1c0040a820b641c00102c4d5051034000c03204206001005172684000c420600c80c00841440d002010902d0041c5c034480d0722080311400407074900c0310f9401000000d0304d51b455880c0700c0f103800040501c665444201180140c082c02c01c0801e50201c4824152644a184280e5480c1d45080489000d43c07541c50140a004841c001c2c0720300307075030000b006115152107a003e84806a81e03c06545460f401d0171150f640410351034100c0e008102400b50701c08040010001c0000588507181c0d100b20400a05c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 481250107 1250 481248857 481248883
    0x806031501081f06060f050306130212151c0615050406060f021501081f091a04021e10050c010608060f1905091b030c04110406030f0b0d0b0612 63
    0x102a01c1d003810140f0401e19690754464041405240d24202004142001c81d8140c541004004408517200e40d80d1001901c1307024081010564440c00303190850798000c481070303c0030104049410200c1d903003401c10f0071000d00c0360310201c0203107440e590403038035481c0240100b00303032440c54201c0c140c0001c04c0300d0703550344510b0000d418156241e015584070b00d10082e00c0c044c946944042c2c190791140040100d1000000c1102c0300d502c4c40000c0d45158020f000c0010050883d010300101140280c0600107215111541030501c140c1c0226510303600200381050001d110250311040c03a411841031044088000d01a6006016144030302d000042c03000c2e81d90134480d04014060703e98080c0c038200e14080c01107440b40c07068098549460301a0400160411159540da14480003490a0003021400d1480d02c140d5414081010140c3d0b01900503c085009440710301d4140c1d20502a10b004240b030000703030f041032400c40d11038145074450162500207481d0307441e1551800c03140c4c02813007561321900d241101c094064081c40a0104448 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 481251357 1250 481250107 481250113
    0x309080d0f0b0f04050112030c080706020a050d0f050f010e09031e07051e0a03122a02100c050f032e0302180906040b0a0e0d0804110409020a06080603150108 69
    0x1410802c54540884240c8a101da42800c5c010710292820703800701a0b1240d403508180c0300d440c0d150314000c2180c2c0543d0700003401c51840414103c107103a420400a010750046c00d04108540c2c11183d00400c00c860068844400c0d404a000061100e02c101010664010300303440112800c0c140c138101d800e028513105211415650780e0100d4500100032081108180145581c110001c41c007004c042c4240e03494803801400b50400c5048501c007151034140c2d6201c03076000102c03903240a40e495106004c03402c1040e00050218014880c20480703079445d009510a0800300e040b2699a02c0c42c1800a15806169410103415030420003440544410040b4200031541410038481d02184206855030040000301c2c0740d00202c0300c2000c4500030070010740c110302142860307005602903010120b644601d26444014011802000c041d03101d1121000b00044c0c00001440c8514402d00303140000128240603c0300362542d060b00233400941c2c0710b07000e20049002e415056441078002d421201c0b00c10a003103408032149004e80c043c0c40b081d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 481252607 1250 481251357 481251371
    0x12010e03070615121203060e150108010e0c0901140f030709080106060302030c03071d03030c0a0b0c0a0203090607030309150921091403100501090c08070219030309080d0f 75
    0x40c02440300090b5404072a10703066250440101e6130707828000300201165141c4024006560107070b4003c0000c0d00d81d6401c080040d291444118040301a01c40d241800701c0e100c2e81c00020504004801184100f07140c009007810494541d0064072100340e50700300840343c0300081c08402000e03214600034500c211425654441c01d01d00d009a0542110030a4003c2000c1600400800010070b11000840740c1010461416001c0c94a02d0800e94030803d0010031000d80c140000582c0443c0000c000900002c401d000d007100d09800c3d207810000c0001c0d44200b1015101507001480080c54502c3d0a0003c0c0145500a05002c501041d180d6907003100320410181140c9125613800229040c000c003034030b000d2300c583d014107820211881c80390406403c15800d44609560b0544a5548c89003d032018081480241c40b800320501055031159801b074064030180b00400001078841300002c00c3c0034800902c4094a40e1612003012141029450413406402035950a480310842049a0100c0105900c245003072801d00b81320005003e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 481253857 1250 481252607 481252613
    0x70f0501020a090f1d0c0c0f07030303020a030c080603060c0a020708030309011b181e1d01031110140f3a060e0a050901150f0609050a030b070c0212010e0307 69
    0x98880d54100940510700ba1001750014466124065004120000c03001e4944909400701d61402c0c614160343d0005000c1d0780400410140c141d0007401e8081c0c0c1644080c0040483e141c412a180002107540c107074141d01000200b0f00c00d256220013406840c680d80b050344c0c61617448a00c45455544183d802c0141a0b64452411074040f0042c0140e112581c26840d000c480960f00c140521215000d6008130096404c04031950600301d00031118a01c0180b80000b801c40c0281000d0050080c007000c2480140c900b10801004036440e49030a94240c0c200711141e840e00030300344203481000c0059030803019080e00c11800400529020030b00c0f00400364142210b0f941140640d50181030a85040410002d0034401141800814411448a20a95503000c400b5440c00034496032000d440c6030152012440001e498031440d180032508040362014103042d680191a108446540d03a418000c03000d595100c06042e1a90b51004281c1c01841414894515400141507031004002c441001d82100d40b88402e00215a000050440030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 481255107 1250 481253857 481253879
    0x1603050406090e0906180f1f060503030f030c0c012007050d020708030d020732150408160c0b04060905090c2b0216030c150501140105070f0501020a09 66
    0x6040341e280c0700041401c20440c203545c0c881024081e0242c0d60400e010b0136100c50300070007000d00c245c4d204500711440300000342075150b58000361142c680700a905200021500d07050000840c0d0f44601c00c40c400c940303140e41c0c00300c02c80001d8100002481c159500c8060101c040c1d81c640e944000841020214995107014501e806860b01c046041000190740000004000240c0080103070f40e00014581d80c00760355002c040c41d199620b0303003000c0040810441d81034100c0007800b4100300c1421f031040b0360350115150b1058092644110040454000700707017110410100e6064100708540c0d0074070307e120b441480e11294527604a218241c000e90046d000042141000300818034100007459000301001c80030925041610f00d204001080002c2c0c400e070050680382030100840455030403100da80000d04c2040600c501c01d450010001c00c441042580da51001011323140e0200e901c0d01c11070f0304030380b012095880260888001921203420070329050718035209034140003000c02d20078002441d101055036075260807541050b00c5010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 481256357 1250 481255107 481255109
    0x2130e101d011407050d0204050405070320070b06040c030b0411030a060b0408060705091903080d0c03021c23010909020306071107050105070c03081812010e031806160305040609 78
    0x701580c1460724081d40f0f800090751880d00f0003c1807170203e555201408007680a48100e030711090700030b4600700800c80c0302e07a45640015171201d0358800e89810610f400e000041203003e180d8014149040180200710907240036401a03080402d00c0c00c1c0840d5156031540018110381c01c20100c000e86032000000c00c102480c180c03160303a001d031610034010307410181884c02956130340ea8024030761402d2000000701c0790801e51743c0103034090130840b270760320340811030703512460102000d800001212a5503030620800004140c0280241c8100600c41050f030380a00082520300f03005020041044600140000c800800800c081c10916001e0040804041286403241c0706051612800512060401c540c2501101c0398031400b00b030580c115002407a00a88a200d5801c0c07020741c5240c0d80c0d20050449500152103590440c64034403410304841304a0700c003030f109840b6400c0d050a940c90010f60304115041042001e044110040c15104a1030300a0702d0b0f1820410340d5580c05014a80c41c003016800f04102140801c055980607407508 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 481257607 1250 481256357 481256411
    0xa180e1f15080a09020d141f0b030d030b0103150305070e16081f05062a01200310050303030403081603021e03040f060c0c030908010902030a02130e10 66
    0x80407440721450000c01006001e0142405251101c07064425956480f00c500e001c0d64102c1c1101d0f46c0d14801072001c41d981c10954451025040e11030300c8001031785036a8800d0040100c07024002d030407640c4c10741400310004e02d01100018180340c2d403403a088040300c1002441d58091032090000342400ca00380746007100d0640e0300600f00206189182c0b81190710581c04071030305400044040e0044052841c01c0183d0045074016003041e900400c02185404ca0380040b1a203c0541a103142605481311484004071400d1707034642c1c4c1c5018000d40d010841210b89000d40780c002e65000684044c00d144060f01c54000904581c004e460a900142d480c00911044002100321503504142038241140340c91141d02110301142c0200810418080d00800040c040c01803440319400740f02e501c9181000400700c1c040c0301a10202c0302000a0b000110001c4010a035000140701d000031454004008000440c4d16508000843c1d10034078000701072319292239110050700c0c3e0800140c682d00c00c00c07a074041006814010709010002c0106054 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 481258857 1250 481257607 481257629
    0x40b0a020105100b0702090901020f0d0f150503060c0d0b1005090109120b0105090403030222080705030f07090b0a030b0a050114060702010e040f14101511030a180e1f 73
    0x100b01c0e040e1311008072401c5036410b5803034050959800011078024012481c111610250000d80400b845001d42d0017460722013402181081510070910304d400c099002401050341551191010520390040c0b00007820f0604038107000860301c51850000b00344001c0300e882c00d280109a01060b030b2485036821202c1e00c1c0203014209507803c4603812603240c00c000001c06109690060030100c0118083c14441d070101c904070344140c880c1c100c001410340042d001c1500148501905c074050040c0108041c600400c582c66080d01c0c81000301140703410b0141e08001080340c264a19841f04440000000182000200c2c41c461400c0f9400007860390301d0316011421082c44c0003080c034400e041c01c005a80c0181e81051741801904003d440005011a0328183c420013070002e10176001d00b01d4100380c10002c10340c0038000b1f914155038440c1900c10b5555204241039030310549180306480385420501142c1001d5201c0d21203100d0b0701e804454442d0010750750301e100130059003040c4c0305c0403400200c5004240c80c004504508500074800a402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 481260107 1250 481258857 481258859
    0x51f0201060b160f0804090203101404020a05041e081507090b04030201120507090b0c0a110102030408190507030c09020a020d05040609060e040e03030f0f0109091104020717040b0a02010510 83
    0x1044195001104010300d541c3c43c44d005032042c00711243c252405045c7c040c90465403400d1410207070f14030f01118460051a06001c040b81086418180295000c00d500d5445c0c640c20300742051101042d1700d0700710182000c4142c2c5900c0c002008002040f1110004949005440c064100b4400041901748545c01103103074080c0812003007006076070100900d4240d0301c0150f4001000c0d140c01d2003c44081429a00c4030841d41030100340548a00d0010070220151072103254010b04040341000107a85a001c0c62281840d1900641e031007450030840340090b0044144280296044c564a076034902c00201803039000085060f501065403041c40c0e03010007806032440d019007042401c0c246001c00003045039240d8020304c2d040004100d103c2030380752100e4002821701c07003041c42926103903e055410a00b001204a4400300e89a030b809000190f608110b00c9072a0040b83c220120310320100146050001a5014940031100003664544402d001b030b0030034020b0720150200781615542c80151031130003420750f20080c00300142207041c454 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 481261357 1250 481260107 481260127
    0x11e030c03030e03010e07080c0f2b03050705030a1d04060e0c090d080d0c12050405060c031f2c062812030c02131406011206051f0201060b 61
    0x251000460303038107107000c0603c00d4100f0701003800f40400d00c291b5a40c500c00d120000c505a40c02283d074036160441524001d118150050810a8405850082ca02e0300c1c2d1220701340203845990031982802c03590180c20481e14080715661814a140e20880c0c000001440b10900490102421801000c04900c00c440a102c0203007400010205201c015080304046032000480c49526210000c0304040160400c096681ba03c41d41c0130364802412003d450240050006403208426403807600c2440e01880c2c10800400c51a920000d01c003046074406403080742c0c00080801000c4a200e1004107110240186524032a014200c0e24040007030545062565000480c000081040359264008418038149943d0300034050b90384204400c0380c407080907410540020b5a1611034100345504100342a0f0101d01c02c3d10301d6241d84078980840012079a0040e441c01c291104c00010810030f6200b0f1014a40c000030700740002403200d0791400090002c505000920680783c1007150b9880c00c0301c0e02881044c0050280f078400502d0891442 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 481262607 1250 481261357 481261373
    0x50a050610030513080304110103050105010c030c02061308061503011d0a0221030c010e0c0d080304020405040212030715061203121e0e100b06040f0e0a0906020a0503011e03 76
    0x912007080580e80e00c0003440c01090704140c3c4c910f00d0f8004441c2c1d41c0d41e042ca403e0181c207070801d45d0100f0380402e04100002030507503c281002d12000790181d85500031106140d08020580d8400c134010180f14a82d0301011410360340621006000d055aa00c415100303415a1041c5401e40704144103240f0710042080010020710710104a904040c2d60481309082254050b4104589020b4a01600410b0380b0002c20040341d840015480200b0a00302c0c40101c0301d50b90200310820040c00401c82c030007071105506102250050400e6007107146c01901c001c00c54030b00314803203886052440c2c0140000b81c982c07034140341800700840c4291047c0c1019010f14101d414020045440240271085040c58545071950341d1171a0311040341041c0381c901340c4070258003000c2c41480c0c0004c0d6020b6692036a445070b81c00030740c81d19402068520b400c03412174040360302524410101e1464104150305500e0014981e03000036403591400800251240b00034004420309480325a100c3d410a81269103140c1080040c20410715804010b00129801c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 481263857 1250 481262607 481262629
    0x605040b12090102070606120302070801290a0b1614010207030c08130302270a0b010e010f050f12011706061807022d10020f0a08100f0801050604050a0506 68
    0x20100c9803500e51a0701907040e00a105403c409031485207000c1021540052440c0c00030a5140030352b080701c1d045074031001c032a4200e481d100c464070300400092410380380302280014440c1c0c030f03040300410345800d0b0740d41d41550036042c0c0e00564a0005042c20f2090032020480303400c144260145414000714144241a6006030500c4150359001c0d018000101d0607000e54008459494080c0d58040c00c8200311012035450014600c003441c907000303464400f1000240c086045480ba107001d000c0141d540d02c240c45000b01c01540c0410b051214182000002c000091440e0207240c01040328a101c40300181007585070a0458000101ca011780c48541e412000601c026585c4014080c04488610011041c0649501070185d01d81070b91540519500c2e03010340e0844440c18603442594140d0980f140a4400c51076494216200328462011002d8031441c080c030807010034a20038256035520404200400000f1030310341840789001d5940d607000403250780d101e4080011f00d09081c0a05034000312000d4090115007021000100b07c0c0c414 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 481265107 1250 481263857 481263877
    0xf1002070206181906090504050a0c02120901020124080712030507110a12111c0312020a051201080106090c0c0818010306050418060509030a020a2604150201060605040b 74
    0xf0100c8800650303924100d90710f20a000c40600040c9256440d1000b0f01134542c5032080900c114680000540d0000560065021900d00380c0e000e040040c404400e0207504c0d4001c00305403411503685180740c061880a41456656646220009140c05490700901c0c5103006010b401c01c182c05040810741600298008041da00865800403c1308034081c0c0c0b0001181d40704110340e01c4504510840d080b440140103c1010a410f158404d0702c1d00400820142e8a488811080c1c0c00002d002541c191a0034841d4000c42d4090901491175203407142c9000b00c00c4070800b40c00602a08800450707555214208000310b00751185c04c0000c00d445c00c0181303043c443c0742c445105900030302d10504080d101c08400c0308070982c402e600000142100a10030131000c1070500840c07069407003444045403500c1c0f40401080c0d030301400205440f825080303503000304081841c0703035690004034800f10710315072070701404000c1c540000c58220041c0c0042d080e123455500100d0b41c1032000a0075241d66901c50002d0080c100003c0c407103105600100c0c0c1d08004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 481266357 1250 481265107 481265137
    0x2a02070e040206090a1404060b0c1f09020405010e0f090118140c0603010b0c0601081903050a0c02090c030403120501051e13020d0203041a0f150d060501080f1002070206 74
    0x19442c0045a0b0302d02c030b2090441c0c1e02040303011000c16101c1c0003007a009900c100c1600c003001016243e00da80700082c890483c01b85003d40c07141c000000c42c809420008414900b01c01c0e00412070300019408501914021303009603400070045070411080da00f0701e10b5000e6110300160020310481611641096040041d0400a88860383d565410400810100310b0f085d90600050522130b0740e0740c1d54440002036134001080b04045405100000184010000b0b0400b151400c40281101300100680c1c040e2640c0e8000311100b424002000c0004015943e0800c80d41d104006040419640c3e2416103001091080ca20389403d903000d10300001440643c0300c0c000e290107001c0b90103c0e85011140ca10300091071b4206440c0c1c4081032070b40001141482c142c901d40185005910a60032081c0198019122010780d0004940d079400081449000603400100003009140c5018082c0c4501c8a105180c4c43c1d02090752400d8000d0515903110316001d098800040240001760483c54008505003a10342e030000714039100d19038210312011 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 481267607 1250 481266357 481266361
    0x1603020406361401020f030705070909050f0106080307060507030e0d08070e030303040c090b18060402071109070305100f0308031503030f13030201020c0405040b07030c0e06040602012a02070e 84
    0x2d5030500410000e080c0038001440c1c5583e940c400e00c21078907461142c20b40180100b003151900e0803030000035a0a62584000030300b14441c141182c2100900400b401910640300d008149c90903200f0078440c1c000038002d50005503990305003600b441c209489010b8844d01c2003610342a01c2d507a01100114031b003102400725240069881d02c9903441118a10454802a0780c10300001040c401004101031440f400c680e682c480600c40c5c20b503480108030222213000214800c3d0002100001d200b46800e0b4010b1084510603c14203d1010410340418554903048600c400803d03501e0301800082c094280e4501c005045009080c142181547e40f040745501020f0148d410102c8400c0051f00f2540d02171058800e2500c9010582e03480d481254602004d021292100364054001e17655424028100341c0120307486660841c2c1180c0140d00c6285040f0001c2c613861002c002001811540002c40d03a031428020700040116030700101c1e100c55030103032900094203c40c84041c032849861200851403078020451500f00c2d0740c007010205071a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 481268857 1250 481267607 481267667
    0x10509250f26011806120807080412030c050709181401060b03040813060e0f0118090509100f090c170c0603040c060f0c0201020309060706090b090102031603020406 72
    0x34000c5914000ca482c00071858a0900b400014a074122403c0d0b10150858035844e07100001140e2103401a81c91080c02190f0710f001244040c0300900e50248511401841d20350303644101500c40e0102001200011408100c540901c8420009040680b42c0c0d05000c1010441842e90a6510180d50000600c854840c91900078500029445900140030030740c107541d0b991401f40b40c10006588080c40201b00880d4040340451020b00c110000c00a03241c0261410028034010001911000a03c954180d04051203120225080c403e6000d00d50140b60b0304002080050a48480401600e00d604641e8a042e0b00e05942c031004a070403e41010202c600c81500f00b070b80c1c1c40b8807130b944030304080841901c607401c85c0000041c0f0040004480141003124030750350703541c8030030b03550307604100c0d154603004001030f006074414000b1017490300d420002485041e00c5900c0c00203104e001565192100e100880d103060892354048200b0224036045a05d00900d4249031408501c0d05040c1503024045030000c1081052446241c266000b074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 481270107 1250 481268857 481268867
    0x52109100207140f030c210d020607020304090e031912230c0313050d0c03030b0613031202010e010e030d050c040f06080408071a10090c05040e0c04031a010509250f 72
    0x16814018210039a07e00c06010b0300c501102007007400c3c409603c521501c04070042d1000c5055401a2016806135180619102c0300b00090030350882e249185000c100425041071030f0000200f40076840d2600d8260031700310380c6e100500407500c0800030080005040240e1100b0004d10880e0305a001903084119501c80e00d5040c1d90310501065031200038810303ca000ba10390440c54110094088041c42513405011286508051056034042c04203141d21101c0e4081c4140002401c480008004500d540300004040001c482c54509407126045010a030781c0000408403c8052039010f441d40c0482401c0c4814074180c9820145144550580305e04020005500003140821141380e0444000540101c201031030606180c1c2110f0461005861f405072040000c50001200892409401d4180607140c1700d80d428145030003c140500c050052041e40010f0301000003200048034040c0400e0710084d21035502d43c10b0740c180414030036218006424500708054031407800a06800e0245140005000d510b03181491070540c1e02c080e90 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 481271357 1250 481270107 481270123
    0x3060709050904140c0d1406311b03081c0501030314070302010227180606120402122a011409041a040e01090b06041b0c052109100207140f03 62
    0x250151403a59460140700b030080d080040340e02500c003a24095103a0861a18028484c0030300000c001300040c0c0c0b020060700a1000c001d07102c0d03015040482d81d1040894ac041d5031081e068008882e0703c240031944110359820b8150440c81d800c09c3d00000c10095045032800740c00411100f001c1100300303000140520425200b0340540e031581c05d8003081148a880c400b0800740620781070310949402202c02c00360311040c60843c40030280c05101d001d0020781c0b600c1108440f40c5207080c801801a60004125080801e01c40400c021a6142d40070342c2504a00020220110a15503440e110400d4100011561401c0341403002e0000c07584404411140002c0030440c0c20007080e241c030308008545a00c030b80761100064229206400290fa114422040304030302c1d5440c0003c00003203548800d011020b454004080a910a00481000001600500032a42c1e082e10440c0c420002d88030f030f00d400c0440d01902144030081d42c00c002d80c076100d0307254050024100c02401e01e0764041e941074090548030700c034034000606020b40d0785003481440 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 481272607 1250 481271357 481271359
    0x13021f09090c2c060403030c02120706081302010905030d05030108060705090109064b09030f020402031e1e09010905060c090d0f0506061f05090d1a07080603060709050904140c 77
    0x281c5179956410042e090f080400c900b6801002d5206404c4a03c0e000495a00b045d0b5203144c444a0981c0c0b55016084841e80d5002c0c000c03410302c04d0300381c170100320380d0360420001c2c03d03019007641e81d903a507036040500701810140050040010b0144c28414451980e8122648401b500e00c5850023a95010304455440c41041402d1a060302030464802100740307210700c4641d04981c0d100050680c05110041920880304079800d803001401c440b071140301a400529180d001140c100d0004001c826640030840490b58035a20150340154071040c0285410120840150305a640680504020004400e045d2500d949407800201051452840055210110f036070b41508402c1450300043d035611100c580c2d1520b20740e0340c0c1c0c7c01d840380d41c41407402c0424090320b84801140b107100014075640b00c50400c40c40d50180f141c00300850000b19581c0010b52003105400b90451074042c801d801560303d02d081403d0550170305040c1440544500c1c208406101c0c20701154499418036604294480100255030340b13074440560911050b450b0305 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 481273857 1250 481272607 481272619
    0x60c1e0b07030f05010515120618010b0409200d0e1212010509011202030307060225030c020111010509150a020c011d0d050306090604020313021f09090c2c 68
    0x2000348a5855889950021030910013040b143e41c8a6041044004101901c0c0d90100740401c217941079986c0001005030446409405014540542819a0314480e800d8206616040d4049410882d02d41107000c0c2041840e4003a02c61000b4404c3d0752804e1409202c2d46004d001c03115296444126850810400e0040012104125545540500c091007a4120003881071a2150000c18004070314661112241c400702d80d070007402189021500e90f50345000e0740000130740b10f04240883c41d50b40080d03112018418100b9101e82c3e1072001008a520000d02400043c18443d030040e0314040401803000400100e41500305e819807045080fa40e00c031141400a445403811014840d42003044e140001f8140e281d0203480741880b4000e40700c081c007031140201c640e4081148ca5540c000d051074049011802c0680c0196000b10301c0880d502849441030300403840b07101c151510211203503910015540002d9000d400d1001419500c0014044160f40080040403000001a1801c24900e81440441a0004103000c203081100241035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 481275107 1250 481273857 481273861
    0x30309090c0c120917030c03031609050d0b070201150812160c0905040302071205061308070b071d03150c09060403050a050604020405090f2503080409050a15060c1e0b 73
    0x4c0c040740362845031246506220910b0010350001006030740ca0040048011400c5580e4418408100e01200c5000d4090100d5500f000c40c07252641ca03000c07850580074614140e864180000000d00312a000215150564000c403400c0c48101c001091184680d0a2414540e880c0c481000e9044004052000010484101c80e0b0b00040c2c04006900000d100303c1c025002d4410040d9505440460031070800002000ba81003a400503a060401d00c03460902d4502841c00a410f000b0317240c0d91400d101d0001c3d80c081002c1104a00700041c10054401c0d10380340c0c9003056001c0c00c03884008a411091100024100f8442c00f1404140340d11103843e090300b500c0c01940c101d02158034940381c500744070340c442c0b000b41c0d8241d000e182440002100e4102c000340c1c85030120b440e20000d2020011103005040e40354001f134058000e4042c010320000101e00c40c40050000350502d44d8001500e403c00e469800c04940e45540d5a4185040a100c1084050380120700089030507000301540d0700300400c0b0b854929050855640051016041d101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 481276357 1250 481275107 481275143
    0x904020d060603050906040c1a1c0e10020a080408070305131706061206060f0a180203150d0b0f0c040e040501050f06040e030702060f0f1b070609030309090c0c 70
    0x401d03811144182c4040000d40c591040094490b03200700d4000d001c60b04a41000c01c81c1000701580307074004080e0040c20f142080010f80340e40d22002c07074150417040c2d03650309c0c1c54640d0b5000c0c0302486a180303203840078102140740035881100501f204400920290500001184400525000ea4100c501011942c0400d036441501c408017002c1404241ca48900c075482090006074450802c8444040c501d11000c0040500c0d559180070000e80c1c47c1511101a085201d40e54001040140c000c120049104100300268070b03440c1812050282d10460000544102a400c0c41c804c082560070101075000a038440c15103810381e5450841107a0b83c4520703480404a503040800b00303c148881076100340c2c0a4240314544551036100c0e20200700035502c500105503025002048500300501d081002400e10000311000a4109428085c000f8069004481d205254041e8003089a0061006000f200042c1804d810a1400981141c8005050081d10b025900d019036913484a10300582c061520960300380d621443c50a03503c6070b103003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 481277607 1250 481276357 481276361
    0x30203010c020706090501080c041203021230010f0b25031706030d120b030a120f020709051003030c050f0604060f060b04030f060b01090807030804170f0a1103030904020d 75
    0x31040c400018401740740410158414680180160140c200b1103040508080315003451a51200d02107065100b510303580c140000303140c0302a10f01c40b5100f2806103d003040f05500031000110196241c1c250900301e00042c007940d200040d0803010364000840c400e85035010098041c0341814141c07d02503108000515160406600c904078011031240600e000d107a64854106040d6901c550285003001706200501010030b0410300d0f8050000d00d10001c04540303c8910b01e846004c1a00d600e50443c80000308400c8100c0c209980410408004054422040045260a001020400358280402001c0112201219040c802c040102c01c039081d0391002591a2810b00d440c054004191010000c0c1060f41071200c0010203004110507101100c0c1c20012800b4088140e80d1480c0041c8542c82c005418040c81c2017000ca01140308020b5080a18424281543d0755802c220403804610340041080354160720001864503030f0fa401007012044030b6800101082603405500001e4154051042025007003172020800c84072200c1c0503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 481278857 1250 481277607 481277609
    0xe090a05041a010308090a050415090b0a09020f04051206090a02010509180702061f030503030c13031502030a060f03020f010809010615120c0c0308040b0a060b1603110f1f06030203010c0207 83
    0x444543c007647c0c0d966810b00c0261040e11840700352407484110200070700c100710381161035511402850084215140d110361000c036040701e0244001ea41e0041400c1c040c03800c2c000c6200351482d089000030140d40c9000303841c0356610000090300074100300e008242c0c103240d0740fa0304511803a81e081c41c040458083c980600000d64880c0121254441040c0140a8a48044081c0d820000303070780e080b0002d1071a43e500e0400c0080164040c0c90b100c440350031b0200001000c90b503640061440e0180001d400741e582d041103507402c0140d8280d600100340001940500704010b981d400c40c0d200404c03000382030003030a036903401190b1b9004084544c0032120b900a01001005850f0b444060041c081c40d00d4030b000c10807100d0025044030401b803001c07801404151450003180100c1c00f10030000e07078001004000440c00c1c6e174440d603140c1c04c680c001200d540e2548060502410405800c0300358190320720504402000e009071941d04555131290300620403a0800000030311400351035842d4114101841d00580280704c1c01e080c1ca18001d6440c902 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 481280107 1250 481278857 481278859
    0x6030b0603060c0421020316030803010314120d050403030f0c051b07261006030303020426030306042307020d11030c03070b090102070f0c0f060e090a05041a01030809 73
    0x1910b400034000e002004107940558654424080307181d00c010a441128601040c400c1e40d0503c00c41c1d8014208108a58100024500c50856039880c1d524503d00246d1000fa9a10290b1300e070340005d10415001100e02c1c05072045100510b10104050b104e50a00b43d000701070002110110381d00303091000480302e410500514003040b03086c07d020a00200c0c20310703140d11108036000b10420120b0400003250380061301860340080b0448041540c501c03600944103141154050741c011070101e0740114040118446209016142098242602400034a0840b109850344401002c4c1440b0f02c3d80d803400c020300c05450324003040b48106006000d824604110300b01079607035280c1c1c80001d000202d006540e8010000b011080d06c0c800d2600000071030502c8080d5461048010380140003c0266500340030200100e606601f83c910003a004080e0f061a988c00d013001402c0d00c030b459400c80e109220904000c849c00d0380795010003a601c88642100080d213a05c662074401d20001c186da1002e10122014000803040c40200d400030310219070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 481281357 1250 481280107 481280113
    0x90f090c0307120207020307050d031101020301060903060608010e2503060f020c0c0a0e060d14100b01020d0302041a0a020309061801021c1d01021c09080607140415050d06030b0603 79
    0x143c1c041640c142d104e0044025007541240004211a043c51406041054401d0a00001000706107042da400c82e00241d0140c0000307a4001010000e0103080d2013480d028004010003030141504180c05155101a55580395800f4070703c0000d04034042c0030306c02c1940082c5a0009061140d107041c64034500203500b080740101610b010361154000304d803400403040c60480764801c00c00301c40d0341c0c0d4140400c032004658480a0324010034009042c80c0460040c040354994400c951000940380360401e000a00d40585981c1460516204002c14000880c24849415900180ba400581e84840c02c8108030704602800c02c08503082030003c600b0b5040500c0e08a200d00c065842070f405c8456560880602e104d0314540144401b012035801d04408030071441d29901c040500e181030044421600319409140501c00501400c00700044000f1014041d9000030301110b0303004031051800c10900c070480039003101180b09511412092a1403036100840d1035000304282c2d02c02c07801d15401040020f64a06020404079422111745220340 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 481282607 1250 481281357 481281377
    0xc010f090b0c010b0f040501030302060c0705210309120313020609060702102109020f010503130c18180302031c060f0e090c100206220606030c080f03091005090f090c0307 75
    0x41464407c2e24100d0f41c1650052016454100f68000c16500c10f9409403139031300921001c0c20580303040c044c20407900d0761920381413076a82c54680300e0b032400e20341c1c940015200307c01c041003030120092000c1c1d2070b00341e0781d07804035090f40d5220301040c002003a620400c01d000f500030580c0d00c50381c424181c0000c03410542240084c1c5030100002c040307203c00704681c0c040100a60190551b20900007551180d009190f00000303000034403281c5031458848009020556020055601340c2c500e14000e0013400f8010b0101031741b100b8003d03100180c1d07030f40e401944901a140760450071500100040c80b4600464020384010710040c020f6035101c6813940030030f02030500106e03803030302c210f1190303121410084c03c21041c4203e44c08503c1d0301412241e00d698000350001ca041c6221821035403018012840400ea192042c2001140700c0c2c4511000d1038035104085080400d546072510294005224000c410b0705e0b184d1441c04200340c6850701c16501c522400001c0c06451640082a03040803c0d60100101c0400b080b0042d400340045407507007103100c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 481283857 1250 481282607 481282609
    0x70f02160e19150909080d050f07092c0c0f0c07170c180603120c07030309051203190c050f0a1506030f0821131b080c010f090b0c010b0f 60
    0x43d5800200e5400f02040c0d043c000c200c09035056210801d0b0f58420440c162421183c8a910000d60f20140c0d50032600d003208a0602c08900d1b041282d5400500f50a840090400c80c0fa91803a00c691038141440201c02140f0360014003401c1d0b1680488000b03c200e0080b42c0c0d10741152040041d55186140101800704403502c507040012000000d02a00000d0003c200e038100300c0107240281c640344030161180d07405119500da0101e21030966800342900d20074100083c040c9503d9401c0081441481e50300036802880b981c058100b144c0c201008407100d1940710070300c401c0b561680450480300d00300d011101420310300803a40100e072101c8010403294407060192025450110f0b42035486000c03205c140c440108403001e400048800200c882014114240b270310601e18411104407840c10320b10f41e6085800618181c14804400100304014543c18401c880c1c4110440304070703080c550040e690b440c03030b2051141440002a10102da462169030b000b800f9188041c034854a82240002c0c15001c3c04d003010341184240180142d000345 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 481285107 1250 481283857 481283861
    0x91d0a0f061a0705010609270206090d060f0c030915090c0b030c0703030b06041d0c1b07091a0f0409020307050604080706021c050322020319140105040b070f02160e19 73
    0x242351250352501c0c5034a55401c05030318049a0700a4100c1e0000020701942c210f55550800241c0d20303034010b00b804105035101040d00d4040381c0d0207030000000e042ca4001903c010a00d4070220016007242c0e07203c002400880703410012031409850780074900f035090000c104901c0802202c054811941b00782c0b000e21600240c0c00410a00d80614024140d4280d00d00c0e003809481c0300c03072001580e009014030b451240782541c0e0428402455125044413400d5a004d6602046030741d4407032050b8044001d01c284042e00501101c070024030b0050b00e081e071044c4540d0700c4020350000e6650500c4440014040240400d82c0c1d581c0d582030710340d2146080c3c030404000d801804079160005005140141c0b11103c0c1f96111481c0da50f0328902c410862041d4505500e41c0025201c1d440016142084051940a0700e4007625400301c20910744030103490104c41118846074180001d110000c1c607030010007a0030841d42d084c9030400700c0c1401022132a0000402d4041000d0303101100001c0d140118070702c0c007805511036124012803c011032440d442 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 481286357 1250 481285107 481285121
    0x109030206070f050c01111309110702040b1f032418020f0403140303240d0b090109020a030f03020705180606070c1212091d0a0f061a0705010609 64
    0xda0400310008403032520403801041841d005050107170402003010941421100400c201460311503000484803c0c11090801000003407582220500c522020080620542e010b82000280110f0b02c9980440550f9180c601c403038443c1e400700340a042610070160004000c0d000d8041c800008015801c006100c08212140640c252030034140c040c0300c503010240c18038000307500c4003082c6d0b03807081014400071000a88901c15883c01d080100011500d0342001004c0c102081d0810305001111108400150201d445650b2078418650704030f01c1c4042503680703004038140940516640250b000b00305490110800c000d41c1c2e24040f00500a6007211034194840c8113209982c000725203c0101c03041072500103595450040c00034210a4820002000c0556032068406100082481e049481c0c04100c5804955035070301c051560b0081102c807100166a0001894a10541c40007500e04c40c0456118032084c001c03100c03250030000040c800144501e010742d546549020080e08030120484d0305500b0b092000610f000300c3d0240321 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 481287607 1250 481286357 481286363
    0x41b1d1507020f0409080307030e070e0105010c060e100609061a0c07120305070b07020c040506220504060b0a06050c0d03150e060a09050703020c010b03070620160303050d0c020109 79
    0x1600d01038294080040600b50f00599035441521020908001442c40020354003d03802600c0100e0f4080d00044200e081c1b0b400c640110550b0409440100403503a440340b0142d00131600842c00140d00d40030002800c0c1021240454068440d0906900065540d41a40b01608499182000c3c5514003107500700740d9042d100306c05a5001c198440b03a024041c44208005952807148242881c078582051669009a20300003140c82901580068620401e18103050141e03d6210908803100d0030307a08101c011040ca864442c0084180c00d40d41d460008041000c544e01160400e0b07401040c0440840c0d540c50000e280354041389903601e440c00740d254940f150368001d001346418003040c950202e15040c10041c40c0c41c0180e0008262070341c1b00021040c00510b220840c0300340c5000326495500542d41e034410010007800d5611100000e8001d81c010f1904100307540e03012a0681000f4821108000c401c0c200e04030041c6403c0c1c0040001600e01c0b9aa1000400c15411034010018892803010a1080010b204401da003240c6080f400a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 481288857 1250 481287607 481287649
    0xd0f4706030a1b09090b03120d0c02070503030d090c0f080304140102010b0a060216050111100c120e0606011101150311191d1f060e041b1d 61
    0x880200d1512401656200c140b040380000d050424410304051030214031003100c0441e0b12010184142c0340c05000d00b202c800000d5000784506100031012190798491040380329101d6640d40107200c201e03482800044001c150080840f41c03203111030a8568014008840102d03006070701c42200240400c0c0c0784408000b2115100055420140341880b03203110270780e0051041d0304655032901140d04540c0d8044241001e006158010410304000b615400d2041c025074006905102c540d400040c0800c0c000074503d003101da451580031455194548080d40e1a200100420b0802400c080a02240c140001081403060009a0b0303649034104003908914222000030198180c40c919422091021030308901420003842800f900c00c010755195400c002c4800d241603004030300c07582c4e03408005100c111001d840ca5500002d5410440d04080328038450641014600d01c00c16051182025a40040742d44c2c41c1e001c0640d0810400c44151001440300000701f807481071315615480740390804000701043c201140d10f0f2606440c1c092070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 481290107 1250 481288857 481288991
    0x3070b06040b090414060702010902030705040b010c0f200d02090f0c040504090501050901140603190501060b0c0c04240b0d0e070e070906030c050f0d0f 67
    0x9954091400248440d070000d8541c0c0e0000303620303214071205500c194001e25440540100c40c0000728100a005441e600842e81482d1400b00503076408141003044070012280080d942c080100161444c0c4074101016000300340154008007801004001c1d40e00d0040c850284210f09c8010408100600c01c007010080d41140f21200050300340d40350b049040c2d8000d000d1090082c20295640002020344111810484c0c159440301e081c020070510900880d081a441341d641c40c01c45141030030220303694903505040c04a1410f8422095004e0000a502103c09002c0920030aa038400d002216141c0e5002d00300329650181d8500340105030001c58425412039400100309051005034038144800e88141c000390400c04c205a610700c03007100348003810040750b001016242d041c0c2030300d8544074001610980b10303039000009043c00c024001321403541c00f2007210411700da855001c0d91100c83c07069109004084c4480901201460104482d070314131100810040001c0d1000542030b542c8800c890400d200f22a021004041d00250750a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 481291357 1250 481290107 481290113
    0x6040813060206070c0312060302060a03060e0c0f0a0c0609020310050103140616030e12030114180f0610020a0b0f09100605090a0b010c0602121509040f02100e150c0f0604050307 78
    0x90b044c7d141e003061042c0801c0032602da400280090340301d103080c10b002c26034410042164040014406900503525110b06040254102c0b0307410003403041c0040f000c02c201c0c2031110202046203544c00b1662481e000b904940e0749190640c040c5006000038001a26148405802e2600424001030201d00c10042048104403010a0308001c0c2e000e425109820400e500501c0045c440e2246624080c42c000c12a040f211228104000140580140049405406403620401308113182215040d902d80100c0103031080c3e107000224190880c144007407200c00800c1254050203000f00b204e4440c905e68090100c8600780c1e49290710903110f0404a808604c00c45030000d640100084107482c141c0d00c201c04080043c10014140500e40d2380348412a44948201b041c88030250080c080350860300c4d040508000d500365603540607410b0a85928000d108081c50080c4580d10400180502d07a06c503025141c50040042c0c000035803040b9215241c09590050907015505100c0e220521030480c40002c0e0681c00785170090055440d0540f151 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 481292607 1250 481291357 481291367
    0x1c0b030f100510090509071a04060e0d030e0301050709050f0f090c030618090102031009062d05030102040902072105160606150f02060619121406040813060206070c03 73
    0xf01502107030440c20380002015249030240c1c910602c840c50161003014108640c000a2000c1240c4040341c1fa40140700c01c0c40380540183c0340c0c80c200310040701c03008081000352034204c80d002c07014407001781c00d542014240898150081c0020f0309603002240e1100c3d9484440c0144040d000c085141c2540c405140004102001c40c50001560080c402820840c10105160b800b105140c40a4403140c20b20ba60010401100d450000000d4018014042c000d10145107401078540001c8050f0701c06035800001040d091034080304520650000300b20140081d500d5656409c080300c001e41120409942303804402d2541c146140708081c0021b01780b072480d15030600342900010040000640610308498280e540d9102244904c903049020790b10b000603a80e02e5151000b8044c0080c01d100001e064940540b0030307510303510a0110010700ca8019244540c1002c40c4d90320190505002440165201a00c2d500509040c031090041c094010310310103a05044111491703a4408080342d0703503401200d80d100007926000075200042e00c50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 481293857 1250 481292607 481292611
    0x806150717220611070311040b030c1c1b06020303010b0d09051b0102100c020303070e060409021b060f060f04020a0c05070609151d010f12021c0b030f1005 68
    0x211803550500e145400810b51070700031a01d1048440700c03801000c00c03400d51302c8200162019280d2014241051550740c0e20344880700c410710400d1080751240740300344164804000f00703c0182d000406071041d84000e1500c02d00c6e40803040506854640c0220044d009254213035020400302c4215a0040d441c580ca00095451642c010b11000c003219a102d0142070017052013085000002d101940d21000200e115030b00281c42c000c040402c1e01e406a00380310705c0502c821f40120079a80e101d8a6070034a102d0211303502d0001909840340f6040400050700c040f0b0a60b80710707080d110052222188500442d106601d845d000c2c03413070b1740c3c80c1118159407101c0401440f20140c10150050139500c0700703604110454094954409042c101076820010018032a10300800841101014144070901c46041185035001c2c0d4030342480c4400240000c03581800840040152058480c40000000001c041021511445400b00c0c4880d1080301c40c444244079414880b82014500c3e011620320761420104c00181a40024004130101800d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 481294964 1107 481293857 481293893
    0x507170a0b010e19030b090f2a01020a0c03080f04051e01030b0a030312090317010b130e0106080f07050c0a0803010306150324090807110108061507 65
    0x134103074502001d494000702c10032556a10300d005949458102c4140d401984101030700d07240d001c0c51002407106070b0544424180c1030b0041d0003004a948000001c8003400100b2a0a01000015480c10061690419500c082c0c0c2c1401d5580000840c0d111580b45140030303402c82040741581540c1e141c80f540014900441700d00c4403cdd411628010f0408540e5205140499524012070051600072440c500e14009413050595603036841d461035204070303040300082e620204198040821a0354150380420f0595200396510a041d65a0420b290f203500c0740501090180b1408200040c08814244042034002c1d0084510075035a500d5407a24508485404800c10040c0000c040e0610004080f1003485d610700b10b0082c01068640c001211000c01003480344c0000306074880004102003040135030071400d0503480098036822050b60b10b103403e206901888014002080d04100400000201c01808203950740d21 = true := by decide +kernel

theorem cover : BRFrame.Cov 481115107 481294964 := by
  have h0 := BRFrame.cov_init 481115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 481115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 481115107 ≤ n) (h2 : n < 481294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
