-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4231
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:57:08.374048+00:00
-- url     : https://prove2.me/submissions/cf4a30e5-fd3b-47cf-a823-9fab2cb74a6d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 760791366 ≤ n < 760971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 760792616 1250 760791366 760791377
    0x31e03090c0a0b03040b04020d060c0519020712020f040f02040b0c0c0405102312010f0b04140402220507030b01080a050c04050d06090203030703170f040b010308090409020a080d 78
    0x1841c4a252030a00101220744403010a40f450311359032104040302c00014001c0c2c1c2c01c0180042c0003800102240309154080140c1e036640d584032080e60b0078107041e15200c6004d4808540c042c02d420300014030000c0c1007c000990444074034040744000404507000e0607901418120081c8080740000705482440c2c000c12903481580161100e0300700410400088490070785801e580b030715076082c0c00c2c4100015024088a082e50a20440f4040542c950008400301c40001113955165100c05513400c4503d414064402e04c000c044405015946c01550400d2451500800c042e11a468680080c4405001c804040c40e80c011045014401440c2c21a0b010f00078000000c0428009600b00e80061001e8000f8450395000e00301c40e00310303585000d10784020002605800d180584210350388014034401a902000108241031082c1c840b034600d44200950100050001003100c0c0d0340ca0010420000010340c03518480e03040d00d60110460381ca81b50000013003001403181120094010000640100300f00200045540c0c51501d0342d40e88 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 760793866 1250 760792616 760792633
    0x303030b03071509061202091e040605150a03021605150402010f020102090f040b01170406090501050106110d051b060a050a06050f1804020d02150a090501080c030a05040203031e0309 80
    0x48400d11a6900d90940007a1020200f800038510071404c3e9481b01590300c40c00f40c2446503803000202c4e005481a5045951041544125060304047c001c40d001000d04651101e080034445214843c81d11a4001c2031003099030029400650402c294100210b2a4008080360421342083e13400a170a81410b40e01a4045007101500b01e0300c0c2403050088030040e40009d41400d9144840b00103000c0a0801c031400305040c40745018220030420851150ba134407441c000c4402041151150604134211201030300036a0400000d0350248060303400002c0e0000301c24803149003035580c1d0144c40810004030405020700d070080c1e01805d01440360145554002c24003940715550b04000b00c559510400c4400d00e06042601c1e0064901500c416602502c5030605512900117400d1a0a040d801d9002600801440e500342d40440f401280e03c803102944550b4000c05010700f82814019402c2a0040c1c181c14000100a525955191400a42191030500941e41400c0344010200d2012039880e44c0308841c0d800440c0e1403100f91040c00c05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 760795116 1250 760793866 760793879
    0x1062403090c120b060f22020c030c012405030d050c0a020a03030509010e0901050f09180f0a030306090209060409022803060e1e01031509021e0f0111100c030f05010303030b0307 78
    0x8486c451640003040c160700b0a1005240349500740c62001c440e03065690074010344215150603c01803071040c40842c00090042440b05651005840f01c0c84003100505005400b408245c4000a0750b55106200c0c1c28442e80b60703100c0d10a00340c0703030104a4800a40100c0c5264000081542081c0500f171710880c2600e880c401000d000c424007200e94024802c265103d04880032800706418106883d80c0c101c80030a14000c01215140c203401c1c50205280041250740d40407e00745824141d052284038090281004150702c0d000c1c1c1c3c08000348850169001750b00d41390ba8001620290052401440100722000b28200c144c0462010006030050105205151041030744034001611180f44052154001848001180b056400d5480d800400301050a0701d0310355940e940803280141e643d103000f0003282d090310b186281c1030f0303907904080c04010300c0d00464242c10300208001104c00321002040f000743d40d0060090001d9600d85d1204120042c0c55020001e503203d502c1e00001205050f416004054210400d404446e0240e03511760 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 760796366 1250 760795116 760795129
    0x80f0906040b150307030506010323150c09031623030319030222030609110108060109090510031b051516060c050706050a0e060901062403090c120b06 66
    0x22401402e8041840000b0001ea4031010603514118000d0300b110303801612075031464580301382a08282e0f03118800311446005551070162108000032840007506070381144102c911400223025000f002d06c03900c040344944e002c0d1000c125100c004151072003001d20b00c0f40d6440d4124000b00e60215801358004440030540202d0900000b1078195a000d06410080c41500c0c04007180250080414030101113a400b9108484052403541c80000d10300070070700060507840c1d91400750561503035101014141314610040000603070304464910b088031007800000ca095075807000a0b801900f4690002084444040c03403810560100c2c06546060710400e669044000c050b041140b00b0501801c185c071150130f0004501c4400180b0282c0003854a520182030880c2400071070366440080d01e00c102c0d4403d24072580c500c401c0026400c00c011072900108100c0003000407a09080d41c0034401e5030765903c00f4400707003110342190b00054480c0e4400c122150f08180c4801040c3d444271241d8050500040007550000807103004a44035242c02d9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 760797616 1250 760796366 760796371
    0x51003023a1107080f040e01090b03010f05010612150f232202071109250f093003020f161d090109052d122b0c080f0906 53
    0x1180c60760418100d95104c12840d80b0510030160407010501000604003584400140a007910000108150340e80c0c8044c5400c4851701503403d078015040c5030042000e650400c1c0d01440c034001150001c81c0d42c0404503c9401e200c3c405901401031140e101030001500b00c40401d0b034242014040c0f11900d16006c1941c20890f10350344440c05d40481c030405141c02d5500f080c641d801000740340e1080041d88007012442000031310b0b5920840700c6800b600b00c040c00c458140d00381e02923142048461801d1600d41000e8070350004162900364040d13207080341300409900d046078030900614069588040b9201148401e20b1500a44903201a6103010080c03188508820345560200701c0f0f4001d540100284040c0d03e400c021a240340100c0140c02d0350901d56813010780d0004204180450352054040740c841c0e121310496844507125801c0c0c1070406481d00c0e01706000380d4001502503003c41d40072219001402c80c1c4d60030010b0240012a4a40310001640342c86e180c58080303941c0d008210580f0403900d8029500150f0f842000b45621500304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 760798866 1250 760797616 760797641
    0x2a031c020c060d06030606030311010c090b180f0904050304031b0302010f03020a0302090a03120f0c0809010804080f0408060f0105040c21020f0c0105150118051003023a 74
    0x500404050304082e030203040142c0480c60003007605681c90300c80d0343c100c1d103041c0c0080d0001051070540210840090240341c1c4580d4076850002c403100d10700118030100d03000760340207948462a600341d51502917607400366032109024001e1020b4101d040a15080384c1d254040d1108a81090002c00300a8403001d28445c442c1c00c80383c06131110b04200817150002c900070f5211f01192030034954280801c0300c01d0344070301c1010030165108003100c5224901e162000703000300c1e0942010404005801903407000103080c4109482d110350017801c0071507543d100e07807070850320354050407004c1610804007150005003440c0024005008003016035422000d42d072168140003d603400d00758085d0118039401f0303d02864103064403010907411a0010018100b40454540194076400a02c141c2d00070380d191801c0c894040b8410b00c0b4a11124800d080c80400b1600b0020803c40d0014a0322030b0f240b141444405401c1e219001c1d404865000f03180107250100128080580c0004604420f03640801a414002141c00d10030745e8031440455a04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 760800116 1250 760798866 760798873
    0xc0702040b030d080a02030714220803040b040b131701020307200307031202090a0303030501030524040b090a0803040f21090e0907080105010305060a180b04060b01022a031c02 77
    0x2c171120040041c1d032019010004010f980b02529550b001d030080500022000300a414408007950402c00804c02d6040d084981d0342d4008100800016505104a03801c030360001c020b11f40c03038054040c0d112198500c2584946450010b16075009245d6106500440c41050140c60f091400d2100c0b88000049101c2c030f14080c07005a00821041021901402e0520008087c1d01d80252805c0e400101080d0041e01c03913401200440c0d2204014000c200d0140303c0c3c01084140481f4248400f1600e1040720342054015001900b80c0b40c801c8081100c0e080c080c4140d42030b440e00640c15a58034286440c0c099404000e9800c00c0c0e84004259084803034480c070f02c40482e03019103500c0da01c84001c1d90421362407081c00e40b0f002d0942e0500b80f043e03403000500d001c02801105e00950141d0702402281c6851001d00341a00c125003204581c4025840d809400195001100c40d001600010000f0303c3d5061180140e11b0801280041c3e00203c00d890380c1c0c810b00c52001051030302008070690589680c00041c400840c803410038010900c01582 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 760801366 1250 760800116 760800121
    0x305070e1b0a1b020a08030a09080705151b010b061c0b01030b0a150215070906090b0a140d0e1605031009050a0b06061b030915070b01090b0d0b0c0702040b030d08 71
    0x220b2101c48410f641e4001000c0fa1030301070343d031040c0601e580d026a0f00c50300440d90990040004810034849407006000c16038200310070800b40541501680325696120416600d03c400000c4000025840100d007a0fa0142803556100780c910180300c82e60824540286a860524101203070552103400749100d441c801514610485041c1690740e13020414489446046100d2500c0200490f0a1050500d000c0c801d281c40308070318035003000350050000481e500030011802c400c01417080f02660061445040b00b0507041480c4e06d810340d450014010300810b001d1448144560024400c174200801070b0f2a04560040b0101c0c0c030121a1840d041302a503100c07e0003e45541c0100c40c054020607520300100b9804600140f4091400714050f078a0b80070058808504c2c003c9074804641e24010f41490042802da81e150380080c1c41c14450b07943e542b0025044140203845030a92a01c040c100d0b180c4503004039040160740118000054035000f0780040c01d80e0000a81640304500f402030220380703410040707580c3c0206103987c0d9070300c001076 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 760802616 1250 760801366 760801397
    0x1707150e0a05120a06021815072d02120c010210060302090c18030706110c0103060b160c05040603050a0b01120b040305030907120803040c081914070305070e1b0a 71
    0x4020a4203c84444c3c01503614020001d900c03440180b01c20043c81c0c0e651440d03401031206015203103982e2101503020b401d0400c0810301040c04d500c2c02c0c0c034412102c0b140c4440190000d04008401c0905614000e400001c0c0c90201d2905100110b001c110074242a0f0031607801035590706480066030180e20010f90000148408a14410b2410000700800b038a00c101d10303c100a4000046840c002e46a4000c60000d006124410310194003408084102503091030140700180c03c000140c10f03140300d40b850b503c10841c4c414896008002014000d0310041c20020b00401c08186d0301c0c2401500c0c1c00c0c2c0c08130212a407a1042001061340084050b00030022a00041c9039140e07135490b940e0940ea664009001c10b500c505c10080d0008140c003080d40c141c1c0e81d662164480945900705860501142c45c1c0c5034100c41e50039002981c4202c1c85000e00d200181025400c15035920b0f14104c22280e041c142025500003400a0280110104481e46508041c900903805010140d055410410662419000f151440000201c058005c90b13560b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 760803866 1250 760802616 760802629
    0x32403150a200a0e0d1b03050609060c07110f13060b04091d07030b040309210303052a220e0403021c0f260405060702070806040206090405101707150e0a05 68
    0x14030344500d0784241011100a0008014030352580200c4681e444002000201c4601b2f105594004200350201d50034a040b540c2c0350b0960390fa021050b280102131807070b22100907550309403030f1072540401e104007000f4094955454441d0740d4424011140101d017491110541103011044441080c400382c2c0140c140a4219a500000d214000d0001c0d400c01480c00c8004c114125500d401d4818040040030310314040100b0b16000e000d40d00c00500f2004101c0c40903c07804d00402090700411000303000d00c01e001e540da10740031424036042c69040702884498056001d000c502400c1407134882d4001c0e8001c1d0205c851042e0400542c006001010b01040c0000e901c0000c10b80c64036000703009118a02401e030034260354085032502021035241e400c44040e00c0c281c0c002d000344400207806100100103071030344001506681c5002e4011400612808441d540543da503800002c0c88000d010079091301400b100048140755003424004195a51058006e0780b00038071101d1440e61185000c1d802403100044058001c15104e4580801c0095 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 760805116 1250 760803866 760803889
    0x105030d0e010c082d030f010302091803030907140a080309010e04111903110c070b030603010b1008060916020a06091e0c0f0605032403150a200a0e 65
    0x50068811a200000da2500050643c507a000c521a030000c5c0b08003603158448500215110315400310030014040c5200c24013004030706490301074550084d075407038100d02c10010150501d016003003400040f050001c02c00011641404a410710401c00c01d040c24840d04000c4121020710500c0100d03441004005141d500032003642141e00c900074400500c5c90400e071038109141e4480a402d03424904d410010200d00ca805204807800341044000d82ca00300710749010901c0d6101a10b0003051100c007808000600203581c2500224015180a010b10304403440358000504032400940d400c52189810000190701a0040806da0b00c0300846903005003000070090301e504c00103080c0013a0594440001700380180c07001d07c0e070103101d0180a12440251201e02e06c1d208940c4124502034000c4420000c00701f0a01a90030541010306000f10003520441000101300d40000380381809810742c0a204900c13800c10070400072920361000154140b607242c035040c0c2c50300302e800c0c07443c0510070041c441000c5003400300c00c0821420850201d92 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 760806366 1250 760805116 760805119
    0xa05130b0714070506160e0303090103021804060f2c04030f200c041410030b13020a03080c010f0b060a03020a0e091326070b04030c0b04050106090606080105030d0e 72
    0x34400d00120002d4481544245400d881550150003030249041070514800030107840380c40c00a0380441201d000a4481c0b0400080034100f40c0c000c070340c203040c1c41a401400018007600500802c070190381c031031180e020360b0741c0c03803080a442460b83e030040c10a4944001002008242c280c444044641e43c5a4059640c60003043e11401003000383d5046d041c4840510082070412164000280005641d8804210030b55000c9800c404034801028207000b00c48403658800f03000d0303a90010400c40d01d50f54000d002d102c40d00385284080e50200d80103400000303119980b03000f4512051000002d21030034502002c14000d840441d07206e150007200c1000984251480307a80500600f41386c51800160020140000401c155030503136642e1700040242c0400820030039a2410096001c860b140160300603910524411a5030090050151000900e200001d04151003800b4402d2020b40c844444c00a03428642841d0303000344410302540760003c4ca400c2011802501881510341241d0004000b4003004280baa021121080380e040c056 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 760807616 1250 760806366 760806377
    0x60a09290d230a2c07090506030f06100905090c010e06030c161b0608010b0904090c180504020f0102030702060706020d06050603010602010c1d03031902100f02120a05130b07 76
    0x150040078a88200d4000e0404034404902c0d0b218885124074042c41c40070841d4082082d05406603d82130700030070b01808440d02e10200103240d03510387d4046401c080c07206140e414540503840c01c020b01c40c139007000c10500390340c01c0803002c11050341c48038030391991102c0e401d94107404601007000c1c0d0110b0b40b8200008640c005921341d0f0540c10070490401781d003114a0341c0382049480c038100320200700c601111010454000e002d0b5140c0348441c0c0d490071201e1095442030580c86401180c42e0001a820701208031071800051881d020b4803a0641210381070040241400d4400301e2058100442c144015880001030f141d005030002c000d2803511615a881a000b94040309110705402d4075460000f0703055540310081e40c000c02c039640022a50b1080080001c1c01903109030f01210325810b1994000da00c5440000944212481c03407096681c0d14000c4410036860651134100318400d06003001400310b44600990060711039040e041740c0e0300103151503030f10607035041c3e5808455036400701501e1203010011482d1403110641007441070808 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 760808866 1250 760807616 760807661
    0x30c1d120a08120a06030c0314030708040e0711010203100e10050324070201060312030507030e0303010b0403020f06160b04080403020607031d030c03030d1a060a09290d 74
    0xc8a00303007803480506031801031000c6100c0340ea002e041c60160b580005006010030800341956a01f141140ca1804090700700f501c6841600038103101001182c0005400081d10b0307031102d80d180d03480f5154070b000720b90f030100080551480c0e28a00e281402902d0250303503c248202042800c141000c0c41402001b4400f80f070010200c030002405450a104419100b220b041a0075042c00c0200110090084080c0110085a240c054200081042895101d407409040c0c5000724194560380821006020007800304400d81c0000000010350803c0b00c0d008104981c800d44040c180c06590600b00407c0d80100d010040704810b0740204000012540c007030381035005200d0002a4103154990300407959070340001000b18046160085003451000b6512400000800200c3c01018110300d040c01290316805100c0071503024030313250002d00c000d4000c02c401c0d1402c2010302400e40f41d100c3d50300702c4008140114174800c1c924142009603a0b007100900602041c10b812a981d2605480c140030b64031400020541c40100c40580350f0b20050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 760810116 1250 760808866 760808899
    0xc0f03101509151419050a09080a080d0b06091012060e1b09030a0f15050906040302120c010b0306043e060901090509090d0f0e01081602030403080a021c030c1d 70
    0x5805c068420141d5900d0b448a0b801c40b00030785041619002001d0950020303c04000060018084403001da00303036600070400c9101d0300d010904078000d114480f0742c032280c050413002003a80d201201d0484940491801d0060507501c2e8012100b49506540b13100c500d18480c0d502420122102c4024003100340d01038100c4d840c2d0a01034a4001c0c0c00041081c08071001c0c03020403031443c00c010881c0119600410703108050009400c06a60203503583c0300c40318144607081c001140c800d803403100c00e41c4043c02c001d01c003900313413941e51509107071088960040960984035009a4003a00750410305a80e1480d0442030002070140348800410200049070700220000f9040105900010426071100500c080c0146072481c0200806285103d019000c038801c0c407180c02c10404651441c11407aa441110240c02002a207a2840d0304859240308034114801c540000e000b0002c00100d402c0026800600309408100c0164160101e04e00c43c003048058503861080b04d000a1407aa41c100a0502c0344550320b01300d10401403040302c0004540c0e5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 760811366 1250 760810116 760810147
    0x201021c1112040303030b10020c1228020901060e090c07060216060c0215071209020301060302060f180607481409040203070b030c0f031015091514 65
    0x10030724420b480c408941041015054000c0004281c82142c200c0d0904d01906402540c070650150490300c0380e0100c8403400305401e130521080744404400c030121030f050307d0811319040078440225800c80c00b80981c8000003a4442c0304d8111030302c01d1100202600e0070703626400c004203c180c000070010354215034208428900d40b42ca1124011f0340c0740c4070310004140100c29900103800d01c21035a01c5902d042002504011600f980001c0446100412420006010085002081c0100800c0e04001d41000e000142d207440c0c85d2410380074041d0692598100801e400c1800b09101090180300030080c4030401d9070f0f2503101303104039013110790740c01c140b07080d01c031095030000140b011140b02038401002807214040781c000e21010880140d80c9280c0c0701c00351141101070030990301090389d0b110203105800881d5804008540003084032412100c000303004420303844d120f0401903140141d1854034400d00300d44805c2c81c00202e0f00a405002454110f8144260300080a4980740e4192481601e000d0010303003013441002880d10301c0c82c40e0b6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 760812616 1250 760811366 760811383
    0x8040813030b01051201050105130c112b0e0d14160e010f080102030108071202010516080405090a0506091f050316141203031b04030f03030509190201021c11 69
    0x20902c0516951406090003e00803c2c88240c41041e418a40144420f49440d9282207003a00303207580c0012240005034007200c00d561000780d0484030340641d14041a02220840e895801a107182c0d4560f0811042e82c807080c0c070700c00c05010045030020070071069003000c906e142980b1140c46008009503003101899409001940307442da0001c9a129450100601c42c51440c42e84840c0508551402146954100608183e50388481d10608400743d9502e9042d90031a403144090710701d103941e0000201c0b0b50900a240c1010b154115010307203030244d0f0440300040c042c00e5040c003500e070181c00080d0aa003500c0e100d600200b100700c101001458905a00c000c1c00050360780b03041040044048031906018505400c0c00d9028021a00d0b2500c118885c211441000c40e50744000300481350858608480c0019105001014004502443c1d02c00b6101c4036201960034103264148c0c20884c8240080c1b0181c510421600615181e044c4203840d020380164080742266203448801c030341d0940700013034078146980c4180304102990701e00b8a84 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 760813866 1250 760812616 760812623
    0x4080f1b0420030a050a0506031b1005120a0204030203060a11070b090c03030a020c1807140901030b1018290c1912120203070e0d0c030510020405010912080a0804081303 74
    0x40e0750401c05490420710801303402c23010440191a180c7c10901b03c0100040c5800d5000303114040a89504444500031401c5400440c001d4400780301c5441d00000c0d5000a4100f44001d03400f0f4051a0b00091203600944501c0300b010211182c2681400c1ca06d480782480c60800602401991103240b00f940020b03138080010b040920b15030341c0100070502c242814085505000d2902c4419200c01c3e8040c001119000002000c6c0051030800341521282c2480049010300350404049030071050240e0003141d07155100032600b00440301011119151a9106503610503510642c102c1160081949082d1b0a0510000000c101d640d20b08011280000310071000f015000b1f6001e4000c6075018a16144202000d810070310b280042062007008506624002c03102400c803110021003244901c80f2078070400c08000d02c4500b054040c5800c40d0850319250a1640800001d500030701130503000ca370242c0307000900c010304920341c080c05590006200d414049032803415901400042d2045070f424105011521441d4900e82c0c140006600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 760815116 1250 760813866 760813871
    0x4090b040b031e0f03030c03060105220f030b060d02060a030b031e030909010b07030f0e120106090605040e0c0f0910120602030402010f031b1b060e0304080f1b0420030a 74
    0x1442c090780e46000074403488800310385c10034002c01810150340d1096950000d030a00742103035642210504840c890110094490109184d207501040050103142404180d034482c585024450300c54a0802060b03100d041c10095000e1010081c0316050b034466003121141d854042d04131036040c880003080200151840c20718040c1e9600128040e0031301e00e030852405004010712160700345090f5068a0080031400c000c500d00742401410400c05010740c54010000c020341166100801116445d8818140606124480c1503c240c3c03e200d0410724a1401244c0601c041c80000c1c070186907900c014051246018009040c240740c14112040020603401c86040d00880c0380c8154001a0f4900c2c5c584000360041160b0350f450000c1500c0c1c45a84016030041c9100501c4400803410001054041d0001c15900c012000e100240100d0408018480040000000d4425070b00c16009980c01d809186010982e5600d144000425440c0201c42000355420254003035444061510350010042a00551103c40c4d40d00035139004007481d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 760816366 1250 760815116 760815163
    0xd0213111b0d0f0c15180f0c0e010501020c030303370c1b110f03010f020c061e0f070f03091a10091505040b120a12080a020a0504090b040b03 62
    0x95000c00300c07510056080c02c12030b0b10441d803521795000d89040e1145a49515950302d08100c84000c800e00303038800117a400a01310708241000c0c9841c0c00b8000b00ea2180c03a00210588001141e1980045103c074543c2002030700450441d5251400c04005a0300001503070040003110300c54030002c0600c3ca00031205070031584404a0300c9a05104010010b0410303000b91a1905d144c841c542c03001400030302c61101400c0e4122209100c0340c10440001c0d00400c40040307150b091900c00610924540c502080852048a5418000d0300030b9101008030001e0b0182141ca1080d0041c0c0140060185170150350044040c13422480c00081400c010b59486081c801d040c00301c03402180703848040203170022240704100090207540005200c601e0304043d10110800d028051188629116030302128a80c540c1d9005486410155044400c0e10702141401c40c3d0004940240c20b00044041d000541c2c040103500840d00e01408903030b1140d152030301c0d0481c0403005041890b030302c0781d1242d2911601030203a0b40800c4a200f42d010b1548440301c200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 760817616 1250 760816366 760816393
    0x31314030304110a031101050306040609060f0303030e0a03020c150d0207061a15030105040b06070803010909050d1107030308191e0c0c020303040618080106030803060f0d0213111b 79
    0x4400d0110f041d07115a0301d0180910010354819100c0c90050340030300f07103291262510700005022b4200d6030010101140750110000e01c8603c040f0403082180e0080c0c0b010803444410660080d1908a40180513015901c03c85806807241408071140c0c0714207603850015402c21a140c00341c88240d0303000710400d0b52803036103c004e408070320504060011500402240c1d00380d050600c1d02c4203003a0300e010510400b4456a07a48000b00059180d001c1110350480c0d020b000300d60b603903842d10048402860101020344080c4180c0c6200000345000d402c051f001041c00c50300512159141d035070202d03600800181810030f03410310b9100540c02c2c54654041c10b0058a0f20092011401d21009a410121424006041c2c00c2241060310400035031004002caa09844d000d160000101c0a0280301c04940300307441d40441c0300e0750318000000040c8050b00700554001c52049500c102014078020400009007009030001c4d51000741210720480503030b641e911000925010b02c80341d03400d0400311400e0045014a400b0340c41c45903004a044088035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 760818866 1250 760817616 760817633
    0x130f021e03060a0e0606040803210f090c1e0616030e01140d021b060915060a150c02030c10093305070309090f020d0606090b0f031314030304 62
    0x240c5031500000d0071840e02c00c2c006905001680300e8841c40440c250081129500c5850403140500340300030480e5941c410340c1d4003107040d01400d515221f0742a96483d0214040040c0c3c0e000c41400341407464000c15112481038204054152800080b0b890b0000c010742144007a11084050003454400ea804e04490300c000d802d0260034800b040e180340741000313030000c07101c000195800b09585c580c0901000060311441242450b9010381984c480000c41c41c0b0480c3c040007030144000030103d1344001c03245904849034686a090201c10290350159010034007176403e0045803203109a0049403a14001412250301002c10f00210354403a00240a180020b80321040c140200c11000040340c4403d144c51800c19064042c465145101490302c201c0c4c04c3c2045000201c64040c14440c1e074081d4050319a0350700421180b9420b070b50007402517000d6403200c42502d04210300002d481d8040e81000c400c583c901681907103801e0f0310803605c00050380014900d54045200380343c001c020680f5100803103c0c4421010003144d4904113824003400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 760820116 1250 760818866 760818907
    0x70b03060a0906091a011404030609020d0605010b1e0f040b0a092c060907270e01120317190e1203010815150a090914011a040b09060d020f130f02 64
    0x14440810807d1503800b00c1881240d044a13040003000610b84100d01c0061144a420b0b24058440342c20840003049403050840140400203041003128101081440c2284d000d0080c400746c2c5011708802d00007001900700c544010200c0260a14003010840d0720b1350311555803030b00c1ca010364903094010040e4402400350b2307a60303a95801403c22540700300b591500c240d00410780c88503c01e8a06500441d11405150f58540300861005409414480d12066844000c2a5658030405405500081160144400082c3c034265102d004075140c542c0416203401031180c0001514440c5070421191060a00305004000c5603009140070b0040503002c2c0c429855511458034110303d0140ca455601c541458094969076521014401166015107010502c1c0c00c84c1c0c14a014901200302d04c0000790f500b004000840941c03181c1901c114900100e90030090b01105605000f5254012102d080d0008042c40000b40545440450ba01488100030000c0c00c0c4110b041070301a068901d21521442c0058020400c414103000d140c8155a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 760821366 1250 760820116 760820119
    0x90a0212300403020411070b070201050f06012606030c040e0d110d120507120507081f060801050d05032a0714030303040210270e1305070b03060a0906091a 68
    0x10311104a02100d9080c5200340d200091240341d4800041d800e0a9001b010f440c000c940081110302c8924120300e020f80030b408201c40d80c0240c1780d10ba41c00a0a950700421080b01c60300007800340d8165400044070300746101040a880d40750706103d91519040785d540c481c01f80ca00400c228002400e100b4003142409040074007201001e01a40d04103c2c00d000c041540828803070301142e16242c01040c40c1e200c1c81416a0080c042c540842c812030f040034104051590008100e600544e6400900302140800820b072100c800181e00515001400b030f0b50040220380341c11960001098040c01c262854801c443c1030f01070100403014006110080d403c1c80c0c2c28050603080c0160002031410307031099000c00c0000d00000303480e81b00041c0021300ca0f003400502c10708110300c41c2d204041b13080903105984078210010030074224030807018450004500019400140d5050012100e50320555001c4000c00442d0708040e540b5656030401440707182c005040d460000351041d01402036100074405104000780c2016980c0c0c054510740720009989 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 760822616 1250 760821366 760821433
    0x24020c0d052508010f14190b0a0303020d1e14030a0e0d020a03030c021b130b1011190809240a03020406020c01021605060d2003060913030c0b090a0212 66
    0x610340ba040c1d800c1c0c0a5404840790144040c01f030a1301ca0004000d200307507640c07541c104050071004820103800090714104c00c1c0b199116008401039810183d00356000c04120744000a00c0000d0a108281070940596088050103602144a82010b0301c09450140241a14801a40608e10003401d041c1c15200d681c4180c8400d00c0074003e5001d1081d05454042e1008006502501101080104050040e441040301c0c03403008048241d1040003180081650b0a020005a028080d0111301000070341d8000d806d5440d0307507020505905007000c8070704002140032905212480c009603c2000109100203000034a124449910b006813103a0078240002e24041c002d21350141958440103100b080480000410801c484089070308950703680003600103101806c2d1707064010400d240317060881c0311041d0140c0081c41c0700b10360903a400b40b070b04c0e5142c00d4450300c849181100075001c100e4052920001c95100c005c1264031000343d40c01c40c2c0a002c51940070490f154203100c0d4010342c9411410741525400121500c1c4441101d13462201b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 760823866 1250 760822616 760822631
    0x150e040507060c03120504030203090a080102160204091506030c17010b130e030409060f050f181f0e1303080c040b16030215010f24020c0d052508010f 66
    0x140d907074400e040c0c0a09400d00150031080c00c101403203a10040ca1004400005002c1400d00d407070040c1da6034004850303052003a003001c8004501c903401442510402c50301e040040d00305808580a12004003203000c416100446ca80c0a02540d0030418040c020045200e609080728903131030015400c2e40c4050441100c031051f41400805082591070000d1104414041400003030b079030694800d6580b0f144203d40c80400070a0a1070b60000b10515005d030700d24220b51060302d10002d0114050200000d0705443e0f031204056160203800b003034205d14614294205014030201d0312a500b6221414501c0302607007102c61204000b40d00c2d5140c800c25901c04c2c42190011100800b1604041c10300c0200071440c0211560800c049a0b0101d14009051003001902c00004070101104820750310354000d12009401070041d841c0380000c3c0a4080d200b0152a01c100c1954004e550103050241c461a00300200381c00250410385a511800461941c0366143c80d4041d0001d1135000c2c0441c005600d80b4030030f5429589501c07502050139242651 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 760825116 1250 760823866 760823873
    0xd05030f0c212e1701020307080c03041109250f0203040308070c2402070605070c0306021308010e010605010e09091e10090605010e0a0905121606020c01150e04 70
    0xc0c401c1c00e00128000b500400da45003200e41c0403621100d00d2507440180103e42150705019824100801d64200c0c104807203828940c01c420744d00343d1205982420000c0d0171100020f00c2d1035203c00141d50070601c41c80c403201000d4400c40005a0070a400c0e1100d0501e1540c40b11003514104c9102c024905032205410400c2c40307401100c1019450f40035900c000380c09954005554010070030304403540405004140c407800c0110903240090441008004c04500c05031040910108540e4014419903155551146030741144900710744e03c1e48065008004103805a0517008400b041d092020b000312050314a4020001804516020005062400580240340074103080400d000f0007074000b00b41c2d00701c6150051254614218141c66951400350641585241c036458182d803441009041d4218070304840002034040b815403940c20110f001c5495440004010754000c410984101082da0050004642c0d00c2c40014450351035034031418280d901c50050040140d6640401c402040c44901401014000000e4140400e251594 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 760826366 1250 760825116 760825147
    0xd02220825080f0601031a0c1b0115090b0a06080112080304020d080c01050a0c1107051005040902040e0a0e0307050d030518010e0714031b0405180d05030f0c 69
    0x214061240300030100d00c1a01c81142102400416802c0d00f100c0303c1c2c40c07802c0c041a844220a02084440403540c0641c030510f2101d01c440c43c0c0c081c1011003c00c5290403404040c0608003e0144a4204595200c040c40c40044511035030040003450020800b01d9603054003010481c041c40550081414030031010014010340020083d07510019500400695aa4503a8000a0218540400c00404231000020340c4080d80e241034001ca0b004140000c405d03c0380300046003007a281050380346134074100ca5100c260100300d140317856800ca0741d4583d003600300b5500d01626043e002c0182d0740160404a04030350322405100c0031742c09511a00010a003581c02031410311100fa920503407208074480300c07041003540b114041003a075003003108401c80d641c00720f600070414802d1300740d601038482d081ca100300401c1c1c46010306055040c3c1408244140503070705201010203184010340400c0300400b0003600f03200c080002ca803502405480208480680c003100b6407a030300d0701c030326044c40311190515008004650003102404180100380040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 760827616 1250 760826366 760826383
    0x100c0c0507260303280606050304030f1110020909070929091c1103070f060819091a01121101050702030a02040f060303180f1502010e030d022208 64
    0x20071040103000740da00d9200045020b0310341c541d402800004103101c106410000403000c81100f58900401c004850360182c1d048440900c61880810307400c00c0080e0001e0320800645a01c4020b600740130340080e46d0961890324002011900101080e40001c042c2020b19042031203a42c0b01c007032460840340e26420b102c1041035804000c004090080c50b80a070b8244040c1180c0c0907920080381c06407503920340e1440c080c0c4024402c002d00c101640c6e8801001c01452841c10302090f20b4041e5080b01d040c15441c0c5150031012902c01000520f140d528003080502c1005400c2c160017004000380c0100f4a120b01c4610003200503a0768901030340129000c3c4401080c080018005190032104031000f4205070741c440c181400440d0405c642c1450081d401481c080c05c880b0407414541c4200103481c0250307208a000c2c803080c2800501101c082c051000e8100061030200001034803c01840d0b940075807480082400054003210906c1d54200b10f1a101d506a004600041d00d4840c0407a090011483d001780250824608424582c803400302c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 760828866 1250 760827616 760827629
    0x7080a0614072f100501030b06040605100e030f030a0206040b07030204060905040506130f1e0203090c0411040b07030801050f0303070f12090e01090b03190b010b09040608060702100c0c0507 83
    0x2d02030000303038543e11416042c5401c44002559100342c4d11681c0c8000408003404100c5120110401040b42801d1600c9013200742c40d00a0a0700082034464035060b220480100165503151140c840c101c10701400920192134a10042d40003001541001e01e020816000020701c0311081610501003044550303442980001115002e0310005036a8071104085041d8200044210a03c3e038100f1004250b0b10001ba400306101d01e20081d070300100410081820002d1344001d030b8054060754000d108108661030664448141c41c08803400085c6071550f00e1202034040d410040c02940402d94600041010b401c189501402c0c026080300036514004441d03443d0b103202104807901401e046200420441b85502412100010f060b0b0707e04016031541e5900303542006400403895850103030180900d406a0182a80280c44e491a030010705a40580e08180148400c0d4115070500f03580705440b0303200000c1d259401d00189016440f10340c0074100b180f20760f1620009484172002c0c0360081080101605c404210041480382c02d0b05d44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 760830116 1250 760828866 760828907
    0x40b0904110d11121c031404061112090303061516170408010e030c15011203030c020c0901060e030d0503070e0d0f0501060e04030801140a2607080a061407 68
    0x1c0d9030600910f07000c60200ea1a400c40c102001203121190005110808000309026040601d10228012800c0e240700c0c07000c06050b03c0510f0b02290010303466802041c2c2c2017414008240c00d003004881119040744003a1900b05841c0c1000007444032505204030070f0208841c142091620f829800051180501c00c5a44040c124030002c019941110495008680c014400e55000344408000501c0e00b603203a44c000c940707440992241070a48a2000150620303941200c0e07400c0e0103240004203070b480560280202d41c12400850081c20f28508084c1d035649006806808103994910310524114180340c50718000408200500c0410303c2080492544a1060200c868003a00d41391019103061409000c03c0c45032502c020140d509040c0b010495a40596015105d58001c1e51091300036680e81c0203960014017110074842d0800c0e4008000c0c00b03110681303c00390142c0c90b10034040100440d05000d43d142020000d4103c0341c1c0c1074201031405018070003680100d040119083e65016884c0c240450041d080020700b043d031402011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 760831366 1250 760830116 760830139
    0x1b030a02030703060e0907140a06090510030b130e01140c0415020c060a171b03041e02031006080c0103020c0601150c08160201110102070f080f27040b090411 69
    0x74481e4000e240285005d2103000001d09040d4101601c82d41940513800742d04c0625040f00107503241c40500381c0111100b6031650500da600f04010b03c02000c0350f4980c640e06141d21910110b0490302d902e07400e0505401411000240a102c50749042d081d6000800905a5070000f0010300c040c1308000c408840c200c1e02c0d2400b805d81602c650f01016403d1030140361840303503c0303400031402a03a86500701d00350320703602c0300710312049800b50b070303849008401c51800044402c2115038140005170009640080342c44200708900300703a40302c01070282e0010340740c52801003201ca0441c4d252034042001c00c0040026007a030030000d09080d8240040f50741c465a450105200c1d201514006403410702c0304500644140c249540c10028280c1e44225213900703e0403020407540708038001021200314030320f0b021043c400e071101160310054070034604500d62078103409904881c0d04012400d000700f0000042195042500c0850001806003411070307000304040000321031035210407034003c807400e00400000410061007503010003401c60303083d41002d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 760832616 1250 760831366 760831381
    0x180601020f0303040b061810150507020d0c0e1003020d06020702040b1305010620030a110304090e060a150b0304080d0f050c0d110f040902090612010b040e1b030a0203 73
    0x118100d4114500750000205000034040f9407031010340f042d4001c1d20404003c0c122a544005000e8003190350910101d401c85090203242e040a29003884515546800da003010306c01d07000603e51150b002422a40051400b04c00c000740000c1c0410584e02c02d6120701c403010401e18540101d000182c6144c0000c0c0410b0340019030904555a40d4450511460080c050007400055582c1c40701c0244070a00034100420726000c0401c0d050b54442003014144958400618240100900161010107421541540900080c8004902c1030300900c90303405104005001072200d814003000302800c540d9001212414200d0b0b410003840401c4000003142d0b00680d100b4203032541c480300e40381d844006101103d40b81100500304002d2280c0c101402c0058070240044800410411310244d00e1411607100d5031801001c9040140410032070400b07a0741c082c001074038019000d1442c3c18049606101d02403002d800031103003000045000c2c440c403619480c03807562001300c4101001641014009052541c04024005d000036600040000c680 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 760833866 1250 760832616 760832623
    0x60204030c030b0f0f0403092102060a02030d1d031207121503030f09031101050705030705010501170706050408031b15010303110c0301051006050a090b0f0405040c03020918060102 79
    0x8580101152194649a00c0c000059800a0b00c01800c0300e104640800c41d01240e85c64814021a899201c3c0c01846252050800c2088804a075140d0741d9144c150110003d07031591002081c6400c1c155002d190f54036188100701003103941c60384007003841e0724580a8108410a00004036034101384142c0c8100400e0b40c9840e03003150034540c0c48030703080092804c00c0340c503a900310302e80d501c20301c1907030b1180e1a091070b200b60b0703040c00719030405e07440c4009413165003483e0716406503500070300c001e1690030301900c180e030b25041d807540300c0c1c44c25680c007a880f4400c3c1440f424440461050700b442200c0240101d481c00300e240510b04944d984e0307640030b00c0d2408814100d45448104083d1400c00c0b0104508512208005a541c0d5038100034246a9810004030803601030811400160303d010f00c52944a01c0c035600c02105400d0403d01e04507601e03044000c194044c403010901c0842c4024131707407015003440703255182102d40d100c1c10003081c4810749144089110074140140050013442d601c001d4032205582c01c1074000b803000d81c1c6110040b0b1a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 760835116 1250 760833866 760833869
    0x50f070501060909031b0c050103020d020c190210080c09090a090203060a060906140102280c15030f050f0a1104151107081c0c0303110406120515100c060204 69
    0x10342c6001d0380000e041c4242e8016800683c080d44030808081d80e2007501400110280d076004254040d0010144102e40c0280d000e1f203840c1c0c026100040c18404104285c43c50414541c503681001080310742c46c1c004600c0c26a4038070403224568600030302c481c10003961181660051081440c40b0305140c100080c484c3c00c82d9800542d44940040880b034035410103520700c40c0100842d008031000c181c148000410918048078280d1002401179004007101c5680600b10560512a800942008202000b610012074041c601003006014003a4001d00b000c0c41d02c0c81c010f0202e54034021840040d80c02e040401100c482440403c2e84e214001403400b05460020001503552841160040010300d21910b0050f40f00c81d9025504690b201142d00c12503a842c1e448131007183d52a00e01c403612854141c030030304a0340c000c0c42c4168200c4030100d12a080100345592070300301d095000c0e009034114100103855510f00c10141c402c18002c0e1604035600039114100440054040741e6054004a10070003403200100087d070400c0341d164102c80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 760836366 1250 760835116 760835123
    0x30a0b1501050d09140c031c1202040b0a0f0807020c09010e06030a080c03070c0801200d0e150405010f091218080109060b09070801180b042003061e060406050f07 71
    0x100d50b040c175005544241d80203034400f01d48a400120304040c103001588842004441005c65428004001c0444690319004500d100340c1c3d4080c40006040c0c250032000e070680c403e854440052000a101c0d00511010005003001c04550200060802c59243d8124503410768010b03102100442c5d84150100349403803030034807008194200004509400450120142000328031510304a0303940c41d5100c40c15401d88011241c008001c01007064000343d80c01c101c1004090402107040081941410020b841e406d00f0254071500705001d0800d001c01c000c0000a201e0000740fa0b01c161400c20560f20340b511003d081c044440315440601c042d40640c00e004034031f00480003004001c00402488540814a00720010b81861620f450080303800c100800c001c503001e100001c4c1620004c4a0900210398859043c00290681c0001e068206d6618044100d0894448098440644c80c51a004c0d50701c5c201001401104100c0c282078901503403407160086455a284402c49080b81c01924240342c85607001041e04620f03208084c40203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 760837616 1250 760836366 760836371
    0x90102240c0a0c2a0b07050d05210123030607090306180c080304031a01060f140903060406051006031e05071103070c030c090209060a11072111030a0b1501050d 70
    0x15501d18800c0802da1041c0ea034440c40702c011051740d55028540d14042c141000389541c2008500100c420f2140303002d0540b80c094048044490074440d645850191000e80118003800c07a4038038420109030307182c0c4441d56010702c241c0091880e8039040780000e046000c5804003e086503107490f6851002d1802102c40c0700d200d03400207811a0407030380e22400381d942c95000e4030044404500c00101d40c041c6001311f0a400381200c6d0f50780c94440c1e00c01c00a100c1214500685040c3c20610b10041c04002501e88040000e40c1c45a4070814000540e820440710810b0008406d6004808044c18801075580080c00c041e41c62408a034400b402107520f03120650140d0304c2c1c14208800507002e11012410b08140080702580f4801c40e4090107110030500e8596240340140c0c414902400d40142d42003110103107a80c4240e4202d0111a0741300c09803607055458144d800d200a4a402034084a24003054507032081c008030074240342240034128010101002d0310340e220710580400900c14403404412900145c4181d0141049990000d40120b08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 760838866 1250 760837616 760837643
    0x402150c0a0b10050904141203090a050f0105070e01080402150a0c06051b09010809010b091614090d021207091103041a1b18040e03090102240c0a0c 65
    0x2a1a641c40c0d84071000c1c0c4003600e041011501145080d0206410b03110003815050007a0fa4985880e40c03045038165141020384280540000d4981303603030000c1c0d402500342d180a444101e080f1306240c0d2a0880d22000c000e402c5e45041d06004900b41c11002c03030300d1f0442c000e003081509641d99000280b0800007085603000300303590001e5404503840c0d00038400525240300390010001c1303440f01048801400d5003480035641240080104100c90340c02203c10356400a444000810711042c1480444c0c00410103461844009051100b0801d01c642c0100400c204040c0060186003001d0114000401c0040360510181c0134011401092141220070700c0a000034009800e000e001d891085812058a41d00440381543c02800121041140d4804001d00500508591b04940d072808030620404195501543e8802d06401050700c1004103901c5500503170328204400c1700a99102c0d0003400003e4204004150854448031340200c040c2c01170540709650030303042444403040075140d2428280c00d4031384088401018000360300d40c0e1300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 760840116 1250 760838866 760838887
    0x60c0c0506160b0108060603060c07050f011b031d101508010c051e0313062d142206020702040b1305040c1703040e04020303160501021e21040215 64
    0x30490203403041c00036803d10707a40c944440ea180e100585069615820180108a4603a2030b00042c1916900070003d0751220061803c0d0b0608450014441c10342c1508140100f030410368140c403c2e0300d480117120385c2c510b40055101b40c0781512061090211440f450781d0311040b07c0031f02000e00f071080190030b940c1c000b04030107503101c40041c0c1a608003050000c480c244002c80f1900d00d82070401603a0048140c2d000d200711018440d5034410251403070a0300b03c05140a1b22900c00304801c91130542403034040c0c1c1d140c1c00040c1480c00581340928188010042001c06142500c0780300311065140c42d003040c4642040c001600c9561600c000360161004c44240780c2e01c1040480d4404e200701072b550025020b00d1180c1804506141c1d6031a5800444003001e07101c0c6180e800031b110030407211a0583c00345038050710040542e4513000010400000c0c0810000041e41c0580d030110380f84400c0840b4014180c503011041490303034184090b000180f0300d450880c0d40720a140b164120003217411502c4003680030782c1380d1400c041c280341c68010024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 760841366 1250 760840116 760840147
    0x51903232a0115050907030504140d08160c0201051611090405161a04120c08060f0a050705070f061d19030318050c0603071e0e0102061807060c0c0506 66
    0x10101d101d510f401c14900150780852100001c44074054003170394036580da04070141e000b00001042903c000f000d11b030a175004000c0900a00b843d0004c01d443d00041810607622001103c83c10100a10601881c1450f00300540c0c0c1000940b00d0800c1350b00b05140074443c03c0d10744491020061010f294011701c60b00144400c015011955242c1e08802c8100d009000340c0d034082c0040c02603807281501a611170b04100034440041c1c00116040ca05000d04d1202a031256114102864a0790031101d00094040c03010178081c0307241c50350103441c0e08492039203815801c0a441e82c40360100b4034130300c0d54000c0910f9518491903260718008a070b00c10009506009071188083c1100760b400090325110000c4001130301d8803210f03242202803401c1444400f6045801020100705010900070300b076101800c000184030801e120001840c00e00652030581481070760702d403040d40b030180002a180810103040c440c1d5032402c034006000002000a0b0200427900d46d0718010101072083e080070b240080a90b040f13a600604002001d501208811 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 760842616 1250 760841366 760841437
    0x2190e0712142a12010e04140a120f021905070f050d05070311310f090308040204150906090b0a2309071205040f05190323 54
    0x801d00090041100949003240700700c0b004080080510410b401440b0103500c10241c43d0b0f00e0243d41c51030125080c00b0f074400381c00268880c0480566140c20481000031a10301c19111443c658010561030304070f540c031440848003141413401001046a10207017000d200308020007840405c0c55150403109401c0c00c03e561550340601420801040d030100018403400c114500c1160030780c0203006417035880c0c210758444c0300c1d601c0c40040103648054200c80144161244011b1a40e40c091072030703850140000040a401d05444018144512191070484000042600b140c482c9030301c59412240000c003100c03560750300951090309421018219103070100c0030031840120380c84107a40c00011100c2e080303901c0d6190365402e0000031400f104003103803e2032082d42d00d05041c4505c1c050f80090090610245559540010808580044070103941d19862103020f00701b0301400740082150750301000080030301d1b400c0c0c5440107440c00c6919950320361600038180d81d40e61850502401d07594aa42c0c1e20020300f6552400c00701181000110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 760843866 1250 760842616 760842647
    0x20309010b091008060c0c1204080f0c0603040323250605010b1603030b040b060d0f060b0903070b0702061323100e12011e06030c090606050702190e07 66
    0x442c2c0109001c14060107194049075041002841160380308401400d20341c110500680103071142c0802c2c0c040d425030b0000070b04040c03c000002001c2865116003090700e800f0000c0c03817580c003400040080c4008030754001d41658100c241056005490600744024082c148200340829510700c980b007590361110b002c00480d1100c6a802031009100c01d0344c03200c10700b01e02407107030050200100c4c440502c4400003074081c0d00301e0300f8140001040003981a0340080410901d502244818015a03692001000002c0f668440c500181c003c06100d14203186001e0042560341030903005e80e181c1040082a458115a1000d040741c0e030b070681061040d00050340e10000201e011011420401088501744c908605a0801c00316140045a01c1c5d5030341d10a1034000001e10484469115101140d5502da071012141200765400c0090341e07603070501c0d00003907032851418000d00801071508540041b5040100821609921006036880280c046515201c004000725079101c0c1d40007a90312958003030101404010241390041007403400a01c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 760845116 1250 760843866 760843879
    0x1509050405130c08071d13051606020f0705030706051c020f070209010b07030e040504020102190c1401020304080a11010c142a09272505010212070f0213020309010b 72
    0x120380c1344c801c1d11074446014000c0c509146603d558030b0f4011203040345401c81e12040901e02019008c1e1202400c100c003682d1f088195010201080148590410062000f40c0140e806040c1160030200044d807507003805e204003420171801280241400c0c5041041ca0b05400d1788070070031940d40742240d21881854000e52800da00c03404050000289068000c411242e01035410b644600c21412b002040200600b00038109a0443c0b24408108800c440480c80c940f1209015202c0c0c00b8010b468000c03203035555500407c549046400511041000c50400520700310f031280c0c80342c1c000001c002c8010040b9112000380d94045e1854103100c420340c01410300400d066100c62107505120909a04801d05441041c860070310161700520802c001490391078101c10600c00c1c64401007600095105039203299842d00c0700400300650721502d070080c00000d01c2148004000200801e0004d42054003001c40c01d50054002e081000d40305500f41c00780c860440d5690802e05480c4580e114085480341005c1a00c9402001030300c0d00e1900a60 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 760846366 1250 760845116 760845119
    0x30605010602120403120c020310050603010c05090a0308031b040e1504060308030f090111040603140a092102150903072f0415030203060106020f1b09011509050405130c 74
    0x51010034800701c0c40c1c4600114611301455a540c500410700300800850422592040c07883c0161f400380326180502100f0a00411300e0300b4030f1000c244c2102c414007070507c14440100100600d944451503070b80126034000100039100d60b90305030101761104007041120300d41d40e00054003140048005607141e0041c640b524501042e10702c0e45061104452540c00003400b05c804c11300c002024234522380500c0f07034412801c10021881b05503104111341540c11070341004012a8940351800035084a0301c103015480145400240000e17044e0f0f4503003c100700c00360001c40a213160b03c2060350820500030402000029104c51000000d807a188400c66200e4000800c125407442440c0c2a264030380c141d014492112045c00d2142c8a001105041000000c000c400c0d4a003c00d8806e5000000150750103001c09802004581c010388225901c0c0d0b048075082641c0d01004000107213215600703d000f501da441200381034035000310044155001d050001d4643c0386c0e1b00c0d480281d00609140811501c0c140846055607064851000d400516 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 760847616 1250 760846366 760846379
    0x1212010806060301150e270a14030909130c050901030b0601030c0f09140d020a030812070207150c0203010222050f0a080c01320a091e0e092503060501 66
    0xc6400c0d0810140e05c00c280c03102031041e008070f5080f56400c21180381c030f002086503002d80064040c111440b4104510341214441c0002d00c102e6079007251108002d800030b103151070329080000c0d1400c039000c5d01000303c400048681c1d60821503c84600700c0501801050b00f4240e42e560300c0c010401c04811203106d030019003801a00f00000740145005800c0d01c2c05503d940c0841030804010003206020589425404240d4060303401c05078403508003c6018500030318149585000046401c160420054002030443d0300c02541040b040c04250002ca00c603c24501d002a5200014000a0f0280c01a180b442c0307208103041c00700d00c21001640e0740074011500d054944490391561181041071107240e601c030b50089900464102c80896225444160082b40c61951140c8652602c0103a0141002400145412180009035030141d03560000c4500c0e00900740061707030081e80c402c1111044400c00c2c140c441c9100c48200f60010a07a0302400740021751103d410050300d456902c03207051040c1c1c4074044d680300c01e40383c03149444000f141d074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 760848866 1250 760847616 760847621
    0xc03181009320a2012060403090509250c060507080709080f1005040305040f0807090b090601020a03030b01020c031f2007030c051c0c060b06030105211212010806060301 74
    0xc00a4002c040c0049003c5600d541d8401031514404011078910154080120382c1d445103c0441414a0801072040e842e03e40b40261000c212508140c5c428050780040203605c96500b2031110b09507441052200d00d08400820a680f0003481d03e60041a89003440100035006601140c003d205603c2951841d0f02169150008c0747c982c0038011403814181c20041340c80c68948503581040d5000b5209282140c40c0640c1c0e0341005035104181e82184000d074102440810183c100b5001d0280c4a01088454030a917040400010b9a100c0e03460000030141601c58100708040e030300038850ba000100014082da86040c484000c4802d0724400c0e4104400e100b80780c1480310441d0150401d1b84078140ea00090050716016464405a41155011400b180c10703100c1c2a54000c24029542c200942289142d1580e100c890344e41c1c540311080e00d000b008528041d0b4001e00040001c0da031000d00c0414400440405c580f41012104c04090800d1845103144500c140002000c0c40000404070314039048943c40c1c0213496403626400f003050309 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 760850116 1250 760848866 760848953
    0x1c020a0504110403020f191d1015030b0d120c17120f040501022703010c030c020d03021303060c08040519242d0b06030c03181009 57
    0x1d40d5030107000070b100600b021b42100e04003080c02002c015808000001c14498a501600465403031910868510519080b032508182c01c00702c00c548400007517052121001a181c1c00308580010142c82c1c3c00c076011587c41e08500721a040b07030454001c451610b0300c5107010380a000c00300008c4031910810300c201d02401180c80155451104400f68040182d01c0b460340020300c5402c050000d9801c0c0d582040740c2c02003081d0490094120b02d003c104804181d05134641010b007101c0e80c8025440038141000c41010009078003049160407480c031400c0058584c005040718400300c45d45134100515807454405802041a0042641441075109508a40a1085a15054240c905010001003128a41d88040310031035401d03680a2074044490074000922904803003400810000007d1541c8182c9120a924074000010b401404d00044042d5040392940c142081c0314032551100808800d0380244003400f0300700d40c1000b1301201c035403885500030a0214440e41d041220385000c440d05803c3d04013400c008218081030110004a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 760851366 1250 760850116 760850141
    0x40302061947060a030902061b01140901091101180306090f0b0c0f0301030609140d0f0908031e0c1c090f05090402030a0308040215070b0a060519061202091c020a0504 73
    0x6007050f40b003540580c086c10301013404130f0740000309001000c07000a4040040048178034550010458000400722124154000b8001c14403607410b1242c500007107405a1019a8030013802e282c4403503060a09441e00d0310b88169504001e102c02d003804030702024800500100c0111500446d646400b90b150a007041c8001c0c030901c4cbc03100c90380160a000400c003054142e4010804140940c0051056203081d40a10342450801c07482d01e804141c40824602c6603076800603042001e85032038001035240c43d28000c680d010700110307856400c00201e000200f0181d16003007400f091203c0d000c080401501a20b0360100a0018501801039110310400240300003682c0c545182c410b0300454029000d030602c00c4850f2811112031a00030800c1c1d822030541c0c1c0c0e81801088401c0000c100c0503000e2200103030a0b003009800c042c2501e90b40c1e40480e20440908880d5044682c1510100d0f00319100f608001c52040301003a0441c010713000c4c4070741041c1e00080f00c00c4c0c0c00b40481e41441070012180e108071075403440c407600c81c004c100842d1540c5030980b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 760852616 1250 760851366 760851379
    0x30b010207120c03080a051b0303060a210501060b0c0d03020301050109090906090b010b13120305040b18030109080406020f07140f030102090613031406040302061947 73
    0x8000c1e000000506003612405a01c00f040c0950700c030745a84840782e00c244060000900005044844045805031b40f800d080c1d49036014500e1804c180c40000c03200815802414a081000c0311050580f02c1c4092041c03c00303e42c0310000740500c0c3c0e61402580c26a80050154142900401805000c0188203108490603100305850f6107505a0629844200800201008813855550b4204000100b00504101802015800070b02655400610364403074844c007213540001030503000b0a5000c0002900b0905541c2581c59542c0e5045e1615200500300f00300c04040f030020303034055181c2440d601c148201c1d0800bc00954181c2d408a03049000c140080c15501c9030780384910032a01c441442d00d0a15032510070642001300000400141c10300448400080b0a5401b1101600c8028100e410400404c80140303444e16800025502800152a082d107003e9241d02c40240992450b01c6c611007910400d50700c4c2e83c010040309003450b090903250302003955003020308244200410700c0d40b082c00c0c82c8400b0303488007440710035503030100034100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 760853866 1250 760852616 760852619
    0x10801061e030902190b04212105040f080a2f0f01020c0414060f01050c0c090627041416030602030601030204240f173702090a06030b010207 62
    0xb100101a000b4040f6402103d80601202502c604207a04d8060300790951542d55440c03800100030a0000c2c0740c00040d24003102c1400141c080340b0038180c400400d501d41c40800c15078075610030045030644190740003501ca02001560210b149600050780002c5d8030320484c0448079030040090717000400c22044403140f0a1101400000c401c03410a0103143c0c0100c0010b00490f2071000c2680002801d40d22034500080c07503400b00100704041403a09585080c003541c42802c2c001c1c9041910001e090319590400142c80c0100c0a940c0800e02036202e40b0052201d02e0446010b03196662243c070701c448a01102541c00351000070040045034003452000c80c04800c2c4070780d01d5a140350310300c2c515560040a0b4000800311814150309010000b020301903a51340400040301509403010821040801404250342140800108a15045445000001441135a0300120040000031400e020310a400c407001c01424100150711068400b40c40503628550068940510b040b200258007035280c4d0f1044045941804820380141c0c01640d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 760855116 1250 760853866 760853927
    0x1060e040228020708010f0f0f020304020105030a05090a200108090105100501210501170d0503012105010b10230903070e07090b0a050d050703090c090e10140601080106 74
    0x40c20b58600b41c00d8015a440142d0700c250041c210b4001e07403002c2c000f403500e403a01400321840a1140b4464524020760450444c01c040c0c0000300507002c003c0c8002161a55407000c07405504081250402d501d500c01c80d0520001c10b50b411440100418038422400300d07640e000814451714060107a54030409003011900f61052034503004540d201e43e030341c0000c2950008181d002801d41454000c1d24060003882991904103103000b4001c6180c1034030a620036081010a000600003a04184852a015034403d4181c0b6842d407280d0803d2801080940d000d682d10040a82c0301070400c9402220b54069442c03801966801d82840008a6035207102c3c001208e941500803980034082d4031581050703503400122600c0c0011a40c0d480e410100e4482c0d10a15002d03010540208a15110040170301486034483e480d032405002040103aa0b0328913207200d2500804501a444281300c269088081255501e04140c000c070a00004a900c2403603002424240c3e03800340001e02c400000325986000340d4a100703941c01d1401d01c4c07031188100c500e03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 760856366 1250 760855116 760855177
    0x80f071e05032208010603050718020c0606010e061c0b03010e030306030604030516080304031701090911040c1211090109050105070b0610090503010e0c01120e190318080601060e0402 80
    0x40420070f14242824001c254164240300e04001b6600c900b000f003180504107a08204812a91181c0e0503100f80104040100520f000c05c115030000e0b03080c2002c54000f4002000a4158082c42c1c09042156440000b0b1522407101500031014140d0154001c0120251204901d03449100440303079190580d11850100700003e20610007090794030020080120001c2a80ea500101540180c03401d80018400d15041d540c3c2c2c4c1c500c1c0c201240100520042001490b825a440341c160b0304040081c9440746a4440f40456458080e440c15040719050000070400c0c1000503001d0240da0f0400901c00d8002081e000c004111035000313030112282c041d000062500180d40312001c0040c0c65100b009050100242d50b0b000280b07584090113444001e015120141c108800d0940c00140052140491804464100603001c20501c07804940c0c2040c0000103a1280070b40c40041c2029603200501c0706d07001d07619258403000002c1e00c600200d259416100560b032014a80c2d4a0041007100340d0081005180ca08400380046464103496175 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 760857616 1250 760856366 760856407
    0x609090f02060306180703150e0402010c0b070e0a1211090103081b01022803050c160b0c1e0403121e050c0a1209050f10050a050d0603080f071e0503 65
    0x1c000c0300010440703c4a045a44900b6a1b040d40800d0b154604214100007111038680509441c0c1758040042c0351a0700024080c84028101400b40c054107004581c0c91485000001481d00000d046c1508007683c0e00c00e100040d0350014000c1d01c002c699482c25800518110071030758100ca4100e40b40034180340c9502d040e4080c440c50760402d00c009642c200110540310444040190083c9a80030092200a801a101a05132640202500745884042110744115080034004031100e030b4000b4208511940d425001501318030a05120004c42201d49440300039840d84e0a004005507031040c00da40300c40c0b1150700c0054030100058503401c078010310300015850304144580040d160507501c0408585081049888800800551142550002d07401d240c092102e41840d03400e441d01d03403600f0346149060305e5074080020b1190040085e490200903001070b4000700c003580380c0c0000300610b0b00410701c2640c5881026000c40b0366030110000f25140a011003c11882e40d1080e100506130a030000003451914460350380408020506 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 760858866 1250 760857616 760857619
    0xb090601120609110712021c1b0b0a060303020d0201021c0902010203070f050606011106040b0103060908040f150e060c1507030e0303012606090a030f030207061b030609090f02060306 80
    0x250880000c0d220f00d01e004280c0107071120318031a9594400c5041c003154044140c0103c009561002c600d03440d04004040000c001088103281c92180482041c0d00c908101c443c0050140c61303000400107000d90b0700744940c800c1003140e110703400700d8400600c0403500b6401e030b0007101ba810500440581c0e6080c10540160000f400003881407060fa4501a999070341d040f21440520400d403065801841000201d580040503180c00d00c0d070180003024607150564881d00c2c40070050000078552500ca0311500100300d403030415140682142c20786100d0031903d400c45030100c90000042d410026a000303955098604100e005c0380e114450280180900d603180c1c082d10000c600020b01181e080642e1071501032480341041c00654082e1507190410901803081100400d13440f41520340880458000c8424000c47c20f1000981d285201d506060400041004080c10f400a026090001d03210070f06004810364144a500180b0300a0100358400300283c94450504400300c1c0d2080500510701d0071050a0f82c0050f140510145922050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 760860116 1250 760858866 760858871
    0x30a030801090f110307031505040908041e050d060509010b060702090a0b0a120602041d060612040f060c0305071e050d0203060d0624050d0305090105030703090230010b09060112 78
    0x5002c1035410b19172088900c5030000e070f42c80030070140342000310b01440000c10007210144000d001c180c540c0c2c10284954428454280224042200d008420700c0e400d400625000f40402e20200f140c1c200031025110449048549510701130301c4100501c2e240040c0c482e4a034000c4d2a06000340d40c0d180600380103021079403205501c464403040000c0c0130f407011541000715510841c2c0140e1a5440d010b1410010000c80300b0450421048200304146a10344605403520720800780c0704040680c13034904100000c0d1141d0b130809000c0904002e02030000c2038054000902501003540c403101c048034050112045d0010381c207101400950100f201d102c512110b50055a00302c603000f070102044d2803559481404403905501c207010050303081d0001084208645072890024881520184004a541d0350028054442c82204a05000d0040041070301c180c42540700c2040079a02400c010030303624110041103130722460002c01010142040c0802d00500303034180120648404068003454840c0c441200644400204940020f0000e6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 760861366 1250 760860116 760860131
    0x141908031e07030f05090703030f050a090e0f250206011211040e0d110c09010e040303090f060b0f0d0f0209072d0f020312010b16020d150b030a030801090f 68
    0xc041c800c6040c0210b5094500040d442071000480094800042407220150010340c41000400e8201044280c00708013031034801d648015400c41079411184139003100d20382c0c80f54442040700725801d140358180648003203080300600d814242c40340a10344641c101c04c0001a040a8010041d41c42220f001e80c44c820311884d04500c030304001d200443d0890f4103000105019502810500e410690003020315080c5d080c010014100001c10903020420304001841502d1440c0f140a00040c140752180c1e21012586a000180c154080302c14181040a85500f060a80c03050030000c040a4061400854413481700754440c1c00c0c61044034064007000700c154001000d01c1e0500100f544099688041d42141c407401d003191203c02c1091f076440c89402003024442d10b501c0800c0d5070080044903a82c17110700322a681160406804244e0340c01d100c020015041d0311000f0000d401c40d031106414810080091149020400391311402c100707107400d01d410561344212820b00900031410450041c03240b810141c1200250fa4907008000c5a0701 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 760862616 1250 760861366 760861411
    0x50a09020603040c0510050c061902070f0501060302100507260712080108070504060e0f060111120405040e01050c0d0e0c0d031707030c09060e0a0503031614190803 72
    0x10b0b80200c4088803070804109083c041803900d0841508054580d240007401c10914005040c1e5442019101c7c00b03540c8200443c2c0444015541c048030150b40d8040c5800b241d407011450585d0182a85000c1280314100b55041340606520520a940c8030343e42018440b404459a041086c02149200030014001e80c1d042051f040895440340400490000999681e90950700d00140c0c030f8141000b6401051086003411801c000380010709400c1500007900a981c0c003034a48031040180c40e04005044412000d0041c5980c2550400d00b5001800c204e40303081d242488094200c0e1100d5080b03540172141000b2903c003e1004842c1c025072030703010040b415000c80c111104800d58000042001c03440b114200e0019005182c004890640c00c01403680001d4242414482d00760301d07100140c200c041070b026000400c1a04820031099680712510f0000414015080c0da950306443d814840381c00003210301c150707081d05080554850751400010050103103580d9851490200e24599a100c1c421fa00182a845801c1019102c85020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 760863866 1250 760862616 760862629
    0x611160b0711040209300d0513140d12050c011109100c110d2420070203060c0c0c10031a041406040207150219090b07020112050a0902 59
    0x142a185035059298441442c1200c450319603445418021401888059440d440341440884a1145100714440000d112071090001c4040d4499011062042c80d03020500c864026004181700b214007880319070200e44414400901070b03440c00d115604012800c58040101d513034100c903050b461000d0718210346082e030303d1861300703096888198007100040e8000565011518050107240d60305c03001d03800c0481d80a00d19880c0d244e0f641c0f1004180700c0c0103001c1c480e0803104100d81c00c6018003180c0c240015123417203840010321101c000c19490001c4842481034031031000d0049107141c140c0e40d409500400a0030f8550391014108020742003000811034611505e060402e0654511000186d100c56542c5d0025035038046400d2044000c01240d46d060043c0d140c04c41602400d41d0408186910040544015a40344d00c03502d4019111010413501000062001c5100740c041c0c1c00003c00c0e011a11003582d61103070947d0700c400d44407010b0310039041c0003404901c2c0d9400005141b08190040da41c09241c40030f00103140c07616038020070746 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 760865116 1250 760863866 760863869
    0x30b0307031505010e010524030603030705031314010206010b0f07060e060906071e080c091f02070303090b0406212405030709140708042105030f060405060109061116 73
    0x1c60b0307034880005000070420f40c0c000a004103812181e07013900c0c1d480d00480202c44521400c2d02c0d4502000000024003275102002240d4116601034110303a9642c1c191000a03e0343e00960080d40030408802003014099031000440790706841c000000540741000c01a05452543e000c003204444854403512405692074081c040305100b680e90074007618003460702c03403001091080c40c0481c60342d13a40d000242c601e0310658071422042c0e21103000c40da056611038181c0001003a1111668008950031000107260704020f6021401c02d08072071003034a0ba00079407074881c8180e03401c5005501841c0001140c81f10000c800b892040301c3c03c803640076a82000070301015080340c0132940078076107410840000c207045420001d0b03040401c0300800030700e00ca1404220719803180000d4280c40070054680010000c2a00110302442203130500c000280e030707170300001c3d021191423110050555041147c0d407048658a580000f440c03401e150160034803c41c0140e607809002d501340401502c0601502041c100b181c45001c60f10306d10050342886800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 760866366 1250 760865116 760865153
    0xb030331140103060801020f0405090c12010303091715060f1302181207030305030402130f05011205061f1203090b1b16180c0c02040c031a150307030b030703 69
    0x40790712248001505071181a8810090b580c030420102e50100c00d0781080d9410b45108940c1720f83c8649070840030341e901c5e02824050780da00600301000081019000981c441c03c0ba003c980e1280340350b10454040d662116910842c40c5000c1001e00001089481d140028808040f0002c10400c1503c000e41861402c80e0002400d100d14034041d00e10004c0b03149007074521894001d01c1c69005101803400c42d5070080081c04040c0c00207000e05a6151000c18480e40c94100c00c440c3c1d2740b4240100040d680d01c1e01030b082000b482c0b00c01600c15006040124080c4446140115882c0500c115013860003407500c1c50b10403c41290000c1907040150800d00410100380d644024100c1d441114206101c16071a91082806d0410260f0b540441d40743c140f40030403c40c40403060046486004800c00502801c10080c266101d620000d002075106140c000c805044a070113a00c542216181c0380c0c003001b2031420050510400001d1140140d04000f402d200144d40180b0039000f400c0103080280a5a90a0b41c0c3cbc0c1daa4606803051802444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 760867616 1250 760866366 760866389
    0xe1201060e06360415020703030519022704090b152806050f0702042301050604030825080a1e0306030f030c061806021902010b030331 59
    0x421450101c002030091610450010386043c441c0c0d403020b448035162450460b800c02c00740001405e100b41403c0890040d1520301c401d554174009890010010082242d818208014010405000380d16a2080ea010000720200005a4a03504443c69038030040b002c1d001c075480f544070302ca04000a941c0d441d125000f80107900790316400c00100c80c20007003c40b1103a00f0344e094000e820f41c81501d8032070031300c20307140201c40a50034940e98600c804000085244107108010790480e0608034004203070903c01011050040b0070102c100b043da600d03082085102c0c45130b0310024220950610840c200d0703c2d044201190280d501c030b18890700e049015038602c610354012205607000301d00c0c0d8400c20a0070442e65140454444401e19003006850300350380d107052a01640e0f01d000303400c016010300000c08005e42c42c0d00002e6404c41a850079a429a403502e80603000c0d6201010f212001c0890580440042c0d00500410120310401000386040c10b9010142c0081d2081d03028401014581842c5800b2440501550407030180c120744450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 760868866 1250 760867616 760867621
    0x31b2409040c030b010c080706060e1f1502031e0d050c03090105010503070b072012010b120606150a0210020712180f090b130c090608010b04080d0e1201060e 69
    0x1c00c002c4440354850341090506124003000b09a0380000100c0f4641e6001038010f40340e41c2241040402490144c101400d44216102401030083c41d448200321410304080c0c1045589817900c005003042500c6810180140e401446207203481c1070840c103044000d801c1c3d0742d485401c08507c0c3c4011002ea03032040c0c0d00700480c0e080010910100030301c20b00580340074200580c010092a4501000054144100ca4001e8942e000015020200c207141414040004400030101c0307280c0c03400106064001c00c0c1c6459124030602d480189080100c4000c10410312032540101f188120005610041e91a0784c011039421303003140258111034038580b03494401750101c4c600480251007080254880a00a11162400030400803501801000346034007c0e4a1001030722503480c1d01007090014100812805160503418114603030405049200c0c1550048280c0b0441b6030710b607201b50700ca99070740c000c0b14080d1213140201021504025181e0501900908403103144800107402c0141d001c0129000e182100e1980d003252030f10111b08010b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 760870116 1250 760868866 760868869
    0xa050a0c0b0c1215030606060d0e0d02070503210f131a04030b010902161b0806131101050313060b0a0e130524040f020a0b030c0a03061202031b2409 65
    0x30940d8441300e1403002419a20f030b4140002d41c2c0f014000d00d8240b00b00d0001030445000c0829800098440e040741c4115074a031820102c02039296400d40c02414000d12404088c1c1411010300e90301c501400ca18218601c0c5440300d0307040c401d4401e03402845000c028100c0840001008031740b0300c2002e40b40140240240b9242c42c01c624201803528410381c030600800340180f00303040d656203241e401030895961140103000b0b901c00880321510007031003c2d88000464000d1608100c0500141c00c03c0a80c0113200303200200a016201c0d0054580d8041503d403500d41e464800d00c078000068260b4080398481c01e000348880030300303540c0d02001894110104e0380d031000c080345c8644060420004000d04c10ba4003c160152007002c2c01105015030482000400181411201240c0074040d92034150b116000380032a101a16624070700000d040d07040340e00002c50240040e28040001030807047c0b60010403802503008010389800140c0c0d00c03c07840d07152900003140d980904151b0409850300070381d8502501c21a00d0034003054841c90b4620 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 760871366 1250 760870116 760870147
    0x1d01050f0f0d1d190203190b0610020f030a030906060f08030c0d03020405150d02040306050708040c140a0b1821060a05041208040611031e0a0903050a050a0c0b0c 71
    0x1941501e20380c8010110034003040001c10008843c081c821004c50303078004180002481d010b101c0c1d0645520b924000c0340e80b4280030b1841c0078144120310030346034201c0c0007410000807a6142c920300d00030700705c0d03800502070b12070158840d03040300780b801c0d010300d00129049403142082800311301c0070340c044003060b1300000392403061000901001c0305510090508505061070440810030b03001060800c99040342d0001094014082254151340207560441d404000515017000054103000701620195481071f00300b032001900c80e40100300c0120208001d00b2140d0b110b8505150388080f90000c00b40307001841025400201c690720348503002010403000f10904007c0d24421403d0b942020000340c44001050306100400012500c0d07604028044c80d03840c500540203135074030704002009042e0030300d150045140c0002845442c2c0c50401072180000c0c1244429040e5031680f50080382200d0b111540140030640521242d01e007503000c3d20103400c43c40180d0a003072251b00c07503960b2200c42c1040d0442d580d604407400807507001114030305a03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 760872616 1250 760871366 760871381
    0xc0c0607080c03070c0201030e0d0c1b05031e0118061d0f12030903120a0b0a08010c0903140f150702010506120a0f0204020903010203090f06161d01050f0f0d 69
    0x504284840303081410b1400000d00c0003c0034072040c415031400840459200c5da00ca82041d110600c01e843e542420250000c0c0030007003c030000d40c4e00e45c0c80c81a905500e121510101720071120000d005000e0200140842d1610500752a00c50515541c1c9170100c6c000c4d005888425140c2030310864000603808411601070010100b0352859803150f070300c01500c5000d12100000c122140c6c0e868a00010740384d6660222507071440c4200c0c15007400705100e820502c0740304410381d000714204000444d610070700907844100c610f080b21140c03042c100008005c010b0400c08100d00800031000400c80e1410340f1040008940402d2403c0742d05c400440302104135000704804a903082c49000c0c3c0200f021a10309460282424000e0369074044d086001e481c00b107080781c4c440115079542c2e04581080030003600a54403403620300e20168449041e070b0000b0b00035000d070300002121a8600340c01c040340418980c40d4180304021011002c8411040090200d05001c0100001400301e03d012000e044c0c480c0021200b03541e2003402184c0882540c03200c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 760873866 1250 760872616 760872631
    0x180a0f0c05070219050a0b120c030408120a0f020711040c02210c0a12020d02120316030906020c0715110a120e0d020604060c0614010e0708040f02090c0c06 68
    0x20005005882503101d0100e881898040304d544002001c407501301d40910400d58001c903400300d046440024a002c801c0094695008201014642036490f54203c08051000b1200240b080200b000101c81c4c0034a00e507045a0405107186002610040c0a050001241c3c050742095400910204400c13059150900500000010318406000c540215141a4082880f071104840c0f40440108445d07600480400c4540152a00060081c0074140035020103901d030500380c10383e580140200030380341000c944460300b1079020340070403080ca9041480c500d104031b009041d070810403150b02d81c0030405c41250600800ca50300107080a0880a0350200010402600003030348001580025006003c080e40801c8080118021810190a10b40b96018201d000071341036820f03403800203600c40320200c0c000c181340ea0302c000c04040441c411101000041c01240960505d40c074248680c0381c4c400c2c506400901d15038807601c20990000d1003603041c11020f01c1035500055003203c080300c100005e040003054103644036004220040c1c12104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 760875116 1250 760873866 760873871
    0x80f0307080306090a1b1106063a06050103050c011d010f081509190f02040308031501050708040b030402100c0c05011b140a0203070b030f0402040b0a05180a0f 70
    0x465503a000607074040104080d110f581d00c5000030710b040c20180c2001580c42c0141100516034003400300b02a000304000c5000c10140c1c0f10320340c0015a00d0030490103881041c42003503401100b2182c80c41035510802e00c41500020400021012040011018050303135000e140300304083e0810114400005009403180440d48125141b40c030380c5000540d80000c081c284481540c035140301c2a07568080d5206401410812050300100c046041000c005183c480c10410201042001e102d0247e03c0412002030340558003011380b2606c0100040303a0842d01440720000b03071079010f04000d4286103142e01ea60a040c0c100354006002820000304100440c64104000c04814040e418080dc684600d501c500313050508a0055034188440080d01c0d00b001c041c29420b04120700d60010220a948540350130031520303203010340003c9001c2e11401c0004a0840c0c81e01c019203211b140c00b0b04031a0700c00c2d0740c2c80d020000a800946051900320345205404503840e140c409280701480c210b00b001d202c0b2414840e06810450700d00503108020301d413 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 760876366 1250 760875116 760875127
    0x1305060c030709120c080f070e010f03020a170c030304030602090414010b160203030f0711030709020304080313030e100309031728061e08010c1701032009010b04080f03 74
    0xb60004900b90913a40d1241d1501e104403558601008240c4141e000701c0001c0c842c0c0b403140300309144006691341c2600e03c27100441041e41da0307500c07070440243e44500009601c0000c0c80400d1041c503070a0f10a031400c00c00000304035000c0080d0350010a056600980003961826000580714040342014040c8205040702ea00c1340e41d4544d031500d20141c01e80d003c3e0404120804180884440644d5820410781e0004800419401d07030300d02040c901a801800f480714020b00238015102e000403620090310a41e4400da4204110314950743d01c009043c000b10030417540c100c0138031802c000350400340d40f540111341115032202d8400040c880220300303001e050381d00042c5c03500700300303180da2003c0042c2244441b00c21000700405180020950071603040040140c00240c020040705000403002d880d541c00040e0016084803a018000c101030000c0c0c00c4121903e0001c3c0442c001c0c0b0420356401000010181c3c0c2640c10fa20150170031441300c403028040015a8020283d0003030340705020102d010b10204100b80070065941d0b0111f00110b00e40ba = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 760877616 1250 760876366 760876381
    0x1e061404080a0809101104090615021c020a0c0e0a0b040c050f090a0e07030221070801170f01060b0306010f05161b030b1303120b0a15090902031305060c03 68
    0x1441104010b1041040900104d40c07058410003600a11443c40001032059101041882c149900140b0540361140c0c00c0102c0040d80c01c0d854114641c1c41c424a5014040d5601010b1104005d510726407003c8045100d00b4402001107480492180c015200300c4042000b07030f0418034030580541b41c0d1980c0303c5104600d040040440c6c00d42007011209141c4c00e41d05101d4540c84910700140030044240e20030181c00c00c11030104142c040c2d1540c01000311245c03025541da0111560310866400b4030341101c502e00800c420900500c2043c2d41c500d4000c00c5c2c901c218048505401d00b440d11030342900c050350f00640c12030b10040305100941d078204081308000051481c009051035003603102d01a00c80c103420300c0034200d094000b518400d14040c000d5810051034010b86c07101c229080003a8040c900040d03885098001808000d50480e43c105070380110784001c00c0040220030700070700300808103802011032009074040c44450100000c3c0300c030030f50010b94030a10181221521107162030826030b003011401000002c00c90020070801078003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 760878866 1250 760877616 760877633
    0xe0a05030627010f0e0a03081b0a08250f0807031116052505090618040314090a0b030105091f090c12020d0218030c010c0b090a1e061404 60
    0x2500000203607190b580d40c14144500501c40f0b5820f00c040303541030020301034001d1000296054040c0c8070f5544c4105640e079202c07001c40d42243c440041a8140001c108120000b44280e092a41140c4081c85c0d0700050400480c810208441d00212400841d0a848041220795041034090394412200d050030301a15060000b04013152007884001e20440310700021041c24450200302044410000d6440602c000c1e0000301043d1148265218a0f4071508070703000000c000b42000119100c594450744068481070f04c4a540996000f8851103418408100c00d03c40300d0f4455039400c0c0c402008007500c031146662541454180b122010005208100384040d41c80c06080c1c29000d15681c400b00c88440c0300002e90302030781c1e940484409403000003101c03500303001040340c0074103045e9607004000480b1883e42501c400800c3c4000d241c0c070742c00382d40340e40e030b0105110b003400102044843c00e5172544072111400759040c2030b400b0394800c588030030801c00d0b00d07480902d914441d0040141c94403a03c03c4c85407400b049840b080c9040d681e810a07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 760880116 1250 760878866 760878901
    0xa091a120c0d050a061d0d1704110d050d0c0302010b091006181e061d15090a05120a1203050405030a2006180705010309110603070912030e0a050306 65
    0x30202c26100209001c028031804c24a00d90000041c46103100600c5640d1b00c0c440140001c80312801a01c40440d03810b8040c0007100e0003156400d005204540d100e4490500483e001421590030000783d80d10140000c50034400c01010304000d0b21003404130300d81410000d01711099202c08600030380400051141c243e440110f6a000c0350704520b0400348121003094421504031466120030701040010b0409510340c4640a100c0c025100540d40c1c40d04107005071201145200200c20700181c1101d868980c2c0c0caa00e46003140149101e0201030445542a56204080391401c003461511061075003240c150740c0c007008a9604010b8000001d442d0074001410b060b1500b5403207128148015080c01410b03403403521102c9003068891031041040040e180285080300700c2980220104c905400c050050301004071b01c0303601038411440c40c0381d005a04280880741100030b100d92680060510824008070a03800213051031050540f0781d01610a0740c8404909a00750309205001c030301500076510035000750341003010107210900b4881 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 760881366 1250 760880116 760880119
    0x10b0706050702030c03030a060e0c2107020703080403080a03110c120306040b030a0f0c0812040b07060612060b1003020a0e012007170615030a0b090c0a091a120c 71
    0x90561203941c020f9195124110a2513520301010082090502c3d09074841030071103100a020f05003030317951802e10028502c103040c0d5214404000c03201050003913291200c102c1c0e00600340d00480e40740329140e0300d80c2415504964030441d0154400507101000f075501d401340001241c03c07819064100466503070b85580703c0c4910803010707030406400f00005104e03503030750b03003000010403006010785004014508014010101140c003d685490230f140000424000c000f40c0c40c3c015140e9101401d0525003000064540c59100e4141942d103da03c1e201c002c40c101d8400b100000486124840006020203444144140c41d90307000100010b00d84140590340303400d60082c40d0541d030f005091821200a0f05000c500f48544003041e030900c10184a03074180400d50f002881d0410782c200b44900700300c0d4036594030f1141c880652544502d0f800e4268105160800004820820080e04400203c00392191101d5010118200d11015404143c503a034507065480311417822641050903440064604010740340101d01a240c0c2c41d50640c2086 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 760882616 1250 760881366 760881371
    0x1401090303090303140904060303050703020c06090a120f140a0c050603040c090e120c010209040509011a1203120a1b03140615040e040f050609161502160801051e010b0706 75
    0x15100440403000c41b140c0d060010700c1040540c5e1207040040c815088860b007240544a1407084848a02d40002501c0c010800240800802401c5c4035004000c2d0059480031a5540d504203050400601948141517012070560b000b000003010304c0c24070240c502015400540240b004106000c0850007041401e021346500c00390200700c0c80c14400300d140c680070000315901c104500101c0c00b40c8071100190020062100100e50521464a448910300d08994a0a11040e1b0400e00388a081c42d06090401101032541884400d0b681410750101c0c0b2415070100844500364415595114040d6050a840c0c02c650f0316002c1d07180401c0741c0c1102680d09140c411011b00b90510451290095001e12480a0211000342440303900c04220b80c10549801d0b40c2400c03803210700700d605000b40301c0080d0403588001284503644805005404446162514401860701c07004080ca0450003520301c00c030307004008030a01200400c2854000a11440d0550301100301c0b0b0100e0700c100c1618500c0000420140940c2030a40386007a0b00407d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 760883866 1250 760882616 760882637
    0x2161413061d0631140114010c0302070f0b1903140402011211161e0807020402070f0b040c0f1e090c020712050d0f05070803130203120d061401090303090303 69
    0x21308007100f00901070107a054010485255000c82c0720030080418940d4030b043c0003c226583e5038603540da00034050a035089440360201080303580300d80c24042c0d4450090060301c5c1c4594489400001f1910590081c003944000000c00140c080307107640c0301d0500000c0c00d00d0304001c07004012214103000c03d4090710180c100000400c4908490031540d200d140c0c0c4a00c064121640c881d820b1704e29103025034011034103583d2041035520350300702e0007846088142c16540c0040d5092402040781d08102c004d410035413058071480e084640050000b00340d1850301e801a4003d2005904462038640207000a14841d0019156000012400349020500030b4042080c0e4011007404070781000003100c2280b03171002942c4014403064400502806001c408192045050082e544040d03404d802104251110320074080c00030040da10030000503a00e40c00d0084007401541c8002c09540101141944a043c0380c4c04c2010003900b0340359038079001c01034140044580710942e80c007030900d00e00161131524090103030171451201500b03000d001c001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 760885116 1250 760883866 760883869
    0x4030f02070902280801080a03080a090c081f0b060d020c1005161b030503062718010b0a030201230702030304030b0717040b1602161413061d06 63
    0x24501c060541d644045450742900908840d4100c0d2910038070b4100c1502c1101408014810850035069810010050450303c10980d4200d40d0b0031001003040344025680e06078100040c400d00c41200040c16490000c01303201c0d40c8a0101e600c407580490642004500e0300180d06540d445075030955a10034404100142c0301c1400c95003d90404c0d51202c80030b40840e10301020420714090401510144030026980d10420a59110048101100810028002c03c0301440080c11502e4640494192082c3c00701440150000305980f4003400e8000356500308407160000303032410000c0c1e02403003a8445134104850303104c0100c4c81c54001801120106521914458508003200314040070441101c46103035010b41181c2d0b4840ea20f0420440c02042030380d807000010100302c1c9002002041440f01c5004641080c000102a00d03805010840c941041030a1015030013200342a03150307040745030038560041c80500c407000140d0040c0b0040001c41d200344014120100d1510109012203580c82d000750151410413600d240384c03521403a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 760886366 1250 760885116 760885123
    0xa0903022109100c0312021c0c020f0706030614180403030203130b131103010b10051303240b030f0c09040c030f0606140f031002180a03030c05060606040302010804030f02 75
    0xd42d0540000e10035140d4036199510095242086000341da40030310400400901000f0b9224000480f8192a4089040c1506151661203109050014011074001b0441040341f507040000a81c4144046540d502c810028080c29400c41c01d2420400c689a4039480c11a50359840c07100f2024002400f015408400140101d09040290448540003000300c0c6003860701e6816204080380600088407040c68010010303503142814007643c080480018a416070810242504803400c0d00148624424a01400000800710b1101e4040040c401803c0401344000b031b400310383c1070084c0c89560301e0b024001d5011111660310ba5402084086e4450b0007120702066a864a082203400c40d80180c001030032501e5140c2d030309020005260700a4003113940002500d00085202010454108440e0741d4180d012340019210b1f500d10661035004181c0d00c400300005086006014010039941d080f180c008402080300480c000050100c104005c03540400c003103031014507217403c6600091a114002d8401014000ea11121000e039500070b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 760887616 1250 760886366 760886377
    0x110a0303050d15080f0a06061205030d0c05090402071104060608060a12050c12010c08011a1803010e120c1b0f0f040b092e06141e0d0c03050a09030221 66
    0x700c040b201c0c0340321408007007616051b241d24100c2d070f941e140130740004007040445010000b4035003010107541007001c0389601038043e150804000041020070040c801a540e103520243c92400d000d1900b8245080c411010f20017140c000b500b0650034402e032203007040f60941d90340868000380d541704514400410200c3c03410318500981c07007024030360044006440202c05441544000800001c0d03a45189541e40c0c6c8030820340b0050107050703417540116020042c0b2111501c0035030200c8541c0502800000d0003030703050403820b410704a0a607aa80c850250005003034015007020401415114510180051070a040e0702c00100340000004d0130328010312900d4400c40351a036a55115180300d00c0c026198000f640fa00310142d108001d842d001411040f031316540038a031103030700041c840700a5900c2503d90075070344682c807900e002050f0401d070843ea4402d501988054509480d00c1c1c0541441940d03c2d402140381264000081e0982d0b100819020005242c00da100020990010740c19614031410f4891044001c10003a40d00042d1144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 760888866 1250 760887616 760887629
    0x21306030c060e03010c0e1e01140705060708010906080a2d050f0106090203060f04110408070807061d09041112120a030b0603010303020a1101050c0607020604110a0303050d15 77
    0x110480080c080b900800d500c41090004c40c020017201160540a42c0e208204031006504003004080144058000720004104070105050191440c40100302d600e46a601c400300843d015002181445000e40d00000d21601401c503030b2a06000c004c1c20004096a1203c59000161180900c0901c0b01c041140351720048021684104104541d504681440303179440c0c03046809069070398a440400558115148266030080394000c241c03090411100c82008040d280788403120319021401c0000251021040080f00000d041d03036030140c41c64070301d003020192074690304d40a101d103c84809200d060703580d50750f01d07606503000c0e500400e61035071001e900012032034107910707002c101d140c510500c460305444801d504041e02120050713950500c0f00c441441e0503c03905000078031004003d40e0003075440034002501d052881c0c030010b00600d170650030007403088041403030b001060f144400540c01c2281440140705070740116154030b440566a030b800f41461940c001b0000d1041e804100600ca548091540d0078102c40242c0f14005c120 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 760890116 1250 760888866 760888883
    0x9080d35040f0203120f040308090f030d0909050f0c1b070b16050606120a0825030e0906090106050d02180406030302070603050f01060504051207090501180509031602130603 76
    0x1c1501d007002d814062454180d10a110383c4188004284296007103d52082c0701040b224145495a501e14a591300322403e21540420040043c0350141c0f8100010481272620b40e43d80700c01070303142c0b1011208840c0701402110003032481c1d80c10450080704220468044040d11002c80c0c001020b0064001c0c10b1180f00c0d04400c808103400a80100203401c0c01c0403140c01c2d1409882640d80c4c2c1d4403018100141d100c442417180c207084d0049074030000400d2640c40508a040202140000e45194040c6000381c1540c040c0340850114040882c0c5034260b040030210b00d1350200c401d030b94409040d418120003a140d801201c9140603411f40006603031001055604c429044414040d0050011f1038480c90040d440d01e246020f903400117071a24001030f00108000303400314100e03550b40c0c80e2a4645420f21041c0311035400030310007414061190310000030f1244541d1003071500801e80060404d182403ca01410300541c1e002510a08a5520a00001c0400c580582002c00c0e020750494103080c2c40101612602d000e0001d6920241c007125 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 760891366 1250 760890116 760890121
    0xf0a0905030f0a05010f0501030c150203210103030206340c060504080910090509010b0f090a080129030d110a060c0302042c39070309080d35 62
    0x10b800007021100c00d40f04000900001e0740030400401219002d03c4054500c00f5800001c02011300e40e403100301c10149261054074901350200c1002000c0b011a190025020645240100141503040c4940d42d001860003652100f852140401812041d08801d030014500c0000100000c896004112044440c0e80c03008041c402c0b89442d007800905a040600140d00a1410504000d0100d01c2001860281e6070020040704559081a079000601c0e00b014800300d43ea20300c20040741842d40d565404200040503080300220719003000c1140d00000d000307081c43e800156180800c08000c990b4003c1801008014a07280c0034024203101c0080340d18004803d44098059490305400100a89d85500244243c4140c400120880200ba9580349130302c001400510703110314100004141e1042460b00e1300c0201105950320000e540d81c540f1085101351040c01200b038812040042e2440c10150008100c00c01450344402902c0201103610001e0160070401c041840703005906014445004081c181014961060115030061803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 760892616 1250 760891366 760891393
    0x1050a0804080c25090b010c0803010608060409060219030606090e0612031309153204020904020a181d0a02031905090c030f0105010b040506090f280e0c0f0a090503 72
    0x24500d5005d1140130504140086004d540070390482d40c0282d81c4442054516840e01c1000c0b20700c064040c146952058592010360007081c3e04d40094210040b000d0107181c51a00010b40140407034242e540444240278099004100900880c5100da901c100c0c2550300d9080210400e803018254812a080896880b90360383c400b0501d68443c0d07000103220300c14a40314a900035202d0008a01c4611504481c900700c6403170710420b850125044448542d2241e010704003604008107100000d0598205620210006101401129032948010006401010303103244824078154200454150280c1c001c007040c0d0b800c0d4000000c900f803452b00041c07080d41108038160400c410308100d0004e90719107521070380c064402e00c9004010018080f06128183c1215400a00c052500e0321345001d020098004451302c507440400d0a1894480c0d4580004982101c085080c124614240c3c2c03400b503000d445c0d06034110000c00140f0304100402d03104000c08580c1081e0f000460705450707001d40601100c00920f1508156014001c5c0b81240214 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 760893866 1250 760892616 760892683
    0x9031606110f190311030a0902030c0a09150909030c0839010f06080d110f0304080607020f06040b04031d280806060a12030912030e0f01050a0804080c 66
    0x10074400c100c50062005000c4411401d07905500040c442000003000418041e00300c3e0b51008808c00c3c400b900b50b503d030611020000d145080b03179a200043c09a10703421188020700c10708421002609103480204001415910000d102190004005025440024021406150b41124841c402c18881d01a1030b149001c02d02c40740c2031106903004501c02c2c0d030130074100c00441081c0d40a04d00a0f540c0f600c0c004c2c525168603500c21a06800d800082d2442801a07401c100301104042c8002d01c09030151000034012070030054030092400030491a40030301600704205100016142141054115805151400b6100c0d842d000c04105040511312880d84081d44003c869401030001c441e40405003440d0645441c03440e61149042d495400456038654400c802c00420b20024040c0300e4000c240c0ca0003842c01c07007001c6072600e0f40006c8000040800b0b4001c200d510f0440603551501e401e0304040da241c00c2c6001e80c14070203840c030081c1081401402c010009280816403020204c01013100e6080150f903500d42c0780c911000b44c417118a1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 760895116 1250 760893866 760893877
    0x212040311040614130f0e07093201060f1103070c1a070503120a2012071d040b04020c160905060409051005130f120807020609031606110f 61
    0x42c0d091101c000b0764218001c1400f08203e8000e0548101c940c0c81c46840e800401c040420329503100d5030b59003e5180c01d881000114085c2c01c400800140110b5080d80300074a082e00f00110000114030030100b6000b4545000c1c0c1c0c2030468480c0d04200d01d00c0e003a10039040c0c5104e03620500b1105584000708244081c44044152f0400f110704042c407104100c0c0803170f42905550b1280301c4020b080c652040003a841c16076144801a54003134401200083c420514080c2c04150042c01103203141d021202050b000e994012010115400810074104100116201c0e9100e20180a1049002d80300d03907500c0c1500e07442c0e51140e404440c49004032005413881d808200c60109800480d500940403200d10301000510581014424003580c543c00c00001c1039070b0030074103030000c000c1d180050422545486420701080001c0f4490b500c0c0e40303803502c0b91240021003c0345200c0202442c800818010855000906211503404080304841500a05160b81440f520319400d0440103095075518402e40704c10005212903000901001910 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 760896366 1250 760895116 760895119
    0x12050a0e01030213050607021c030206070806030607080c030603010f020a090602010b0a0303050f030c0f0301090b1f0f050a0e0901060e090a0b0109140d06050702010606030e031201060e010212040311 87
    0x200c08400080c011800ca0203030b1802000724800c600710034020383c601100a0125544024200402c03d014404002d2910a030884202c026900071001c1c000800c1d04068080e500581c1500204280c1c600a94003e119950281c02581c20f4040000403660a4800303412444284400200c25540c0d042200d0000303200410034032554005501e0600c2100c2545844031700c040441e60155183c6041082d0300c000300c0744c07540c400303800740320b03004000c20105007408148400342d07000344038920300001c0f0340c031424003031080300000c084210070703807155846140007c0380d001507c074034003201240342ca640c07507882041050355540f0520410940c454541000010019031141010486d103600303403040c0071a40c84089010059960315900359000c62800c0700c0034000301c103030202c88803981c0320300801c1101c1c0010107841e40c2c412203c059506c00010f03516420203100458060060050785c000e500700541c034008540c40d80071808201330040030204081c1070201d14a0341c0c800c000041d00078584082059881d44d5900d00350010309610001c1d203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 760897616 1250 760896366 760896377
    0x210c07290403181d01060806061207030906050f070903080a0314041112063306070b0103060b0102030c0c0607140d0503040501110c0a032a05150c032401090312050a 72
    0x8139070b41041c0341c0300400540807070304252a0b030b90a210068034010b40c028034154100d4020700a111043c800100820b004102c95140003a00c0901c909080c01074a6004107880d4080c024003040c001c4041e44400c0043c2280d80090f407160b103c0e5143c003411006891990080b800c0c80111000b44028804541c10308a4595800c4584080329045620340c81d480e007404a892041a41c1d0824242143d42c3c483c010400d0300705400c000c00106012a040001e0f0150041e030016101103081238014802c1103c00d10600e11041d409000850518075007245072584c81e021252807900030304000c03034140d0401c820b0007064a040c0c0c0900d8103031940c411403040700606941080f1400c7c1e91641c24011310b92110080a0300311640740304a04081c0c05402c20a880030707520000003290a5694003440146156003150080c41c800403107100b040681503091080f41c00c0c1081002c00b400c50351000b40100244114190700c40e101c02e50a0700040c03250f8603c04c981d400180c911f00000e41c006000b003000b00020021680d8441c0003410940d00c15280c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 760898866 1250 760897616 760897619
    0xc021908060a0c0305100b030a090b0a020309070618030f02040b09011701150302060406210501120b06030601050f1309081614070e01090b040e070b210c0729040318 72
    0xb1405d03150150341080d502c0202103018030038011007030010f65026070b04140c0820025101e5540b9841c0020840300c1450407540442030240740b807030034020000207140500d00b450810502d5400044110410310004200d1070702d201d07008046446641001504d0b03c0300030030504141d03070b449085000e2044c070b40d01914900d5103445c06440000340c0c0030b12280c054a4001c0c0c90241410b081800541c1c05040102480036405000c24107210705902074000c0d02d01814824107400507118840c80c0c81202c005010344550300c42d81144d40103004544400307a10100f0b80c042161402c02c890018000b03200240400d980203814203100048541300e0188c6400500c030140d10504000942d0244010700c83d4582c50980620030031801514010040350740b450300802c9102100900c0010014079600b2440c0c0307090301c03541c40099800004101c07081548450b41a441140d22150740807291841c00c03901400891007544c60040c211654480b483e0549940410100d5910440000f040c8043c00d09040140911000204130724001d541c0010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 760900116 1250 760898866 760898891
    0x50a09090b040201110a050a14240408070c03201f020c01180f0e01080613050309040c05070f0c081c0215152107051e010c021908060a 59
    0x1001040d58100c80c000c422038449a004403110040307810082c1d25071244846210204a00307000501c2550320a01182d843c2300949144541021070200707004451820007441d08106031410280b90380c0c0b1a5000c0469a80d860003460500c031810700315040a4918640c80072542d41980c0350402d941e21400041b10280652520303206049401c01c2c4501100d401a003084d02d000c0c0d12940143c0d0600340b40c2d80640c04414009440d44a51000d00c1100d03804840245009401040160746c00c1c46855040083d450700109604926242d00360b5a104000d80940181da64544890149210320107407820540e10081100c0706240710b0900203a00f0403140940d40550181c42c2d0b034210507498000805410060a80142c540c42010143c00741c10f445006040c5440c20101c00e4bd0440940d54000e408500000000001030814141036400c6240600d50742106000d595440f042041d070800d00c64800040311030910748040c0600541c40883c4104540d002121a42c000300b00020400550205115105000e0954200248829443c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 760901366 1250 760900116 760900121
    0x100504050702150a0b0612040b09010509030a0c060f020c100e0304050112180209101409190b011116030521040308030c0f1204020f0d11060a0c0602040609050a09 71
    0xc490320050391001296068070104800c189600449110000400c07045c040003044250b4800016001c1058042c0f04100402800351803042c4c000e4001002001249088501c0070303900c0c480e441c44802801a0494141c0401c900d80d003025101550290007591110b1450400741e41c0c6201c402e030920203107410810030100f101800001d83d01201c2c01607541900e000501050076009240b21804041049d0070174400300c0c05a103601e4041405100307a4202e41c079003181ba0403081c1c5904a0400c1d54076100b44000c03810700282561079146200040810040042c4c4410140010785601e4123000381c2c05080d00860441201908040d80071004a034025800d603080034025440580f041043c540d40e499440748244020710100340540701030b50b40078400900592070304070482c000b1803860704880e42460b412101041004114100079807524041082540c8041051010b9525840706030b00550310240200b00100308844480e21400b084449180c00c00c7e411548d50381c640c240105030300c120303010b481d0054014640010b01000c051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 760902616 1250 760901366 760901371
    0x30c0809030d081e07050d15051005190804050c13140f070905040203101e03330207021311040e010b0901020f0a1101120b060d06090c020a030206191b0810050405 71
    0x16031b02c9070301d4140080b802e0401042124802e1317807c0700c4465070101e659201c0720b0140c42007120f56203906440d2280070304401600d204554030f0004000c04441408001400081c02145070701c1c0450303c50724040704066900000b000f01003040221541c410060101580d90140d155000300e506031349007144140ca40090105a101c241c1c1c4ca0400169120400c20250030161201c0210030354412807250415960f85502c601040d06402c560f110f9007000d02d82c054207041c80706183e194420b001d00c2c01d41c00e118858001800c01c110301808040b042d41c036034a4000c4c120801c07408480162100502d480d4243d45c580e45040400c1d0882c0c12564051321600b0185d880d00344001429103241540700c0043c004c81020200111100040c400000160540302c202007602d659581001d002040e800803000207091b4680a41e00060f00c05111540701950450680300001c03940c08601c2c250704c4503103d52028002d1001d40c0c4041c0080c010345004c07a4018030b03d213407078084e46a0301030443c9024416070400b02440584400810007200c005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 760903866 1250 760902616 760902631
    0x1806090f060c071a19292b060501140612010303050f070c091e0213051215090f0d0513050108190c0203130f03030903030c0809030d081e 60
    0x140040c00b500300c200c004084040c402d03154a503155400d18209103400100381c9105620b0050b088030600405807911803449444208540b021264001d407090000c0d81d001100c589000e4034010b102c64a2008038000340c094030402c2c003040301410134106d0500400401c020f02802e00032000d0803c0c100b025180c2a0180c2d0040c002c940c40e110410703407031341d5010794003944043c0040705520b01c140000c0000c600703080c42150043c80e104c0d0300803031848032140326001ca002d0030401019600f031051005954005100ac1ea030700c1603c005480c1f540c0c650900348582407412040c500a07015200c612410400d100c8004520308a00038031000c21540c0d000e5484078151a940900e5440d41070316074550408000c650b11884416401141120f580b44000074048160002e441d042842130000d0b900000752680d4075040000c83c0001007041d0b81c1c03c0800d460540e500140122010f101c003030100100c0e15907420911032510304841080c00d0050031a40c42d01d04499014110780021248681000070b00800e0344280883c60000798400d030035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 760905116 1250 760903866 760903873
    0x3f080307050a170f0103050606031f0f140a02130608160e0f090c0a0210110f0a050c0607020d032403230709020c0f0d0909050c0d051806090f 62
    0x1945801200c1d03940090680b00104421014940d64030a08404554000d030a000b5800b40300e5811800d020745070050151691380640c4c058001d40903100a400080055160503410100d0040d926450b088090b00703034114102581442c0e08188060a0040e0b8000c20076000307500c0210a400d981c4203015908150708907072081001014403421803440380b180c02d03000941c400040813261100c1118000c134800c500d040359a4032103184000303915920701d501000100f40564603070201380b20490107808008041d024002920320441c801152105070300b1700034020b6424900d40720048440c98030380030900a45e210f421400190110307182501000129003030024940c044e0f443c40e40403024051860380c4404050880101c80140c01c040c142105050080c180809001488000400340c0c590105500840c1412481844100355a002203d080c102641100750340c3d085a000c4000000d850313944541c034044178800c04100c581041e00d0f0800300040e4105101402842629400880b00195101350b4699071703910f50410300f95265803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 760906366 1250 760905116 760905121
    0x20c0106090b0f091e041707030201060e0c090102070e1008031201060801060905061902010e070e06030d0c05060a0506010512070c061d0c060705030d0c0c05010c02060c0d0209010201063f0803 84
    0x205c201e0801350040d118800d4140040a050807034030311904080812030050b5100c08080041c038480b02e518030707004810144024908126880040d6441e42c035481518080107004d80040d111540103241c1000810412095941d6441004400e0b203400d182402004041803900c0d00104c1c0305072040f91541c0036940c01a054901d42403240c04c00441176920f0302e80d40c00440d07488020741c03c0b440a003840f102c0024032070b000c00c1c5846d41c1070100c101410002010810300400003071700d6103040400c80004151f074008455113030002d0503032518401210184501d200c04140c0034488010301000940c04500129803074000c4004200080e4100c1c0362811892103c41c3d00140780e40701e041ca00d011840d0800080510074403a900b100d01d4215045c2d015420f444840c1c2c18030f4080340c01e0103440420700c00f007070203081c03180001407026001c546000ca0b009640c038050f41c2091035460354080354440b4264000d60140c0007030013071443c2da01501080f145802aa0404c0d481a03100f02c480841120309071207103001409000750354020002c0e811507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 760907616 1250 760906366 760906411
    0x81b1207060e0705060d0c0201051609151b030807020f0a020603010b0d06080a050d0f0201020a090e07050d0501080606040f021c0509030d060603090b130c0513020c0106090b0f09 78
    0x401e10702d100d0010a00403410001034540d2184020010303104481004600050030000103821540c00403d04440c01110304a65110554048259426038410100c00c00003185208800c641c400840070440b003e01c201810144241a00301c031840784503024a908840d45940c0c090700954990818103030003500450305100501c9200f5400c000350080500c174880000f006942c84903a14034000028000741d5a503040401c202c42c01030360100000310710400900080d8034020a40e040103242100c00c0c41019075814543c00401c1d002445401210301204041d0014000d40d40c4071002d4a44900c405d0303070844d1189180401b0442c10a03030500994281c2420094100c1e135038099091400c01500b0003e10b580e805002c2000361440700c80702803246201804690b5000640341c04d4915100c035a03075101800c0c080c0d1a100035030322030001401c401c02c0181a02d5055400038180c859000d814400f9024003208000594201503000c80c00c551603030300070320313080c40100c80b10400040340e141409a44201641c0050107550000c00070b00c8030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 760908866 1250 760907616 760907621
    0x5060a0e0c15180603010b030402060a0c060c17070c030e0d06090f030909050c0921010612050309030d0f0912020a1805060907080c07060b120703081b120706 69
    0x2018034200544801d000440001901a244548001c1d50078001241003440003003031000e100701d440c078140d0350f4a15650412048003100d01000b00002d10500000481c00c1c06144600b2040b50229407009040c801c84201c0840035000780000100040c42d04000e0000130683c1c0d12415005803130b5030300740d115100b45034050001c0c4001c0b001c8070304040c1d030850348a2501100041c00c1011105072a400399442c000140d0402407404180c80d00600b103800c8512080c41000c109549098140a44000c5203000102c0caa100d10407140c0503005a5002101d044540f4480d81c3c288003021005068064040382600d40041e0840401d030356000001c20404001940084284448140100080c10060006054007249a0b40d88251075a26100e40c41c0004002e4071042400f02c5414041e40b00c58024500d070400320703c0ba182146091840d4081e9030005441c01d034940142c0030184d02d5524000b0300d640ca210042d138840c5902c9081c000032230303402120103000702102c00c29034002c20746021485080c100d0004540c10f1518005440e250f02 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 760910116 1250 760908866 760908881
    0xe010b0607060e330702010b061c0f021305030c100219061103152724100203090a080f0c0618030d0306150504180203040317070507110d05060a 63
    0x505104d030705032850b05040004100c541520716280d0344650150082d44151007904044d2804095a0401c12509017580d160000d495000d9104401e0340040c420911661004c0c18522140300f46c1d00f44002620300740038a00344607290640343c040d021030340c460644000f070000440403640003900503000000480c1403503010a05122403180a03c50100e04156040c11070001c6500030341d26501c1c5040010280419401c01d1181810492212058903c81448070100b51703015440c014043e40300488032041d605801c070740005070400c030105d019042c80744494030f0742c001944c4e80e031080251600c03a1509050000e58004001402c0111407121809003c2c039900d803809000b070395008400c5101d030b02c1100070600b0620340c904009040805207107540110702c080c0f0317110a241c0b581700300d60505402c11200308002c3c803d01c04008064845a1035a850040c0c0d40e550b181022241c110322050a40781c00070840d030510a569a01001071700072980610025a002500c0204107c4400005880102950001000500b5040c0c25600401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 760911366 1250 760910116 760910141
    0x1719050312061207060306030308160905040e030f07050a0615060e040216240509010c0c140c030307032d120b0a08070303030e0c0a03030507060b0d0f080307030e010b060706 76
    0x88003d0040c9103182014079542041c4c0001e81d5600f02001410344c0700103c180c00207640c0d01031400e080d05012000309000b2103801107601598480c0f464951420b0b0030412035070361003001107490307456200500e07043d91201ca440c0019a0028204500c80001c504c2c1c0c404080200c4501d03071100e031062110881400080d41040040007a26a50400c130b00c0c4c040b81c4100145c5d0070901038034005244101e000c616036421500080c1c22081168505840d050a07590041d0207803500c03e41006882c452419203e043c10310f0a04100e00780c0d9014000403d0a000301908070031010604503030044000c0d90240703946040e0000710901d410f10000222103075000503008400c0c0e8010404a0800b03080c40c2078803500c55140e203182504a50040300001c4d5035110320a0a0502444504c0d1a4141103440340202480c1d134174018628002c400024000c541e4500101030560344030003202c0320b01741d13100c0c5048080351150304090ba26501f04035001c101181c14202c0c08030002e401882080c064490050145040030340316111a0000e112205540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 760912616 1250 760911366 760911379
    0x60a05100306050c03070f1d01050903071d0a060605030f01051216150210060e0105010f02012c0f12030c09120115170327030313171905031206 63
    0x840442c0b12400361510403030890150396624180b05034020502e5101c4c66140c4104480031607220102c03100c80d0304d141c039219400d2074070030303181d03005040041e040540d0b0340d1042c1d03002d800304080b04c1405005400a2441040300c890204070f1556511020b031074500c030440b085140160450014042c602d041c05100742c021a840003295030340e494080e100342c80d51001d6000311444ca5242084101030a60401c40c840c01014a0802481668507141e0a0b12180ca010f0081c1814404529071507251303a4400d501003d40708a6122a070541c08420090740e03d109900300b044c4030003a000c0d069800785040d10004890741005424103000b460b549d25692090745035000407480c82c0e4803c460400598080509008407000200d13981c444100385490442028070076540b03000b503d0910380042c040206804a01c1d10b101d20010213510070307100c0760707076011001034207502c250640302090007621039002c15941086503145d499282c0388011a13004000107104840c400060140c000c1c41d907882000f44042c0d1381c2800c5044e940101014054 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 760913866 1250 760912616 760912619
    0xd050406090209090c120c0f15070b070503010f08010c091a0720090601080403020d030b010e030a0501061e03021c03351b0702040b010e030f010203180c03060a0510 72
    0x440303c080a840d01e8182c2d9009170840300c442d2803c2d100ba510112074a00c014140e14425401180c2c681c4084011184180c001e64200550a01d03034004130341e0110780c4011807840b5490001c80c06401500300f03000f400c0031100340c4200850801d40500c5001119117140d12904111841d280481c4101c03003601c21407140240e81031106000142c10000c0c41032102000328a14600c2c944e00005202490740010320380c0381040030003020f000109801051468042103a0b02d00414117011001c016500541502c4038140c00d4130070030480f4018018107500040a0f540703038182e0ba905114503d04210180303441400041d500110741c0200001d0340d010003000c4244144241000214100629251a601b200904d103c0c40900202d100440c20008c0e030600031135201e59403540c14040d43e131303100510780b030b00f809840c02c020302455650b014a02560301480d1180b4900e0001821034100300a4940e145020750400d03114404c80910716240d0302c010220114010000c0030010f0001c0030786595908455024001c09071201c0b0b1441e6000b40d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 760915116 1250 760913866 760913869
    0x60703020c2121220b0708090a0209010314060f1e0907240e0d0b0c070501110d0f0608190314070f0b070e0d0804260a030e09070305010b0d0504060902 66
    0x600300b0407880d550941400a1600480c0a2413801102ca00f084418482c2100c07400012114114560003c0036403074944a617070f80e5070048a28050000601940c442c080c040000100301c100014990070312030700d00940303410340c451b0802c131440702105590149140ca14010101c400c8407250004a40c05142c3d1030485c0c04103076a070503200e0340782100001a6907111580c402e5191740c550f000071201c552102e082e02e0107240c10026407141490f45078050700b103084040c00010141c0078000250807603440c109014000039035845030070320078100800c61002c83d403c1003820860000b1b5002000300d050f034402200089101c6141107580d80442e1440091761000320490400d000c400c0200d0001220004000e10503a2001d0807030400d42c0c405420724024101701440340c8940c800003400554031100f503c1c00c4462064071141b1003078000300201c4804143c1c80150701d0381d00c40c00b9104000d03d5405000c0718051441038401e120940c40b00b500480503100f09014070710142c0c1d001c102c0c03d00c2c1011035520541d40180034a0300051240c46990 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 760916366 1250 760915116 760915147
    0x1a010815040204031a1e101229011502010204081033090605040c0c1410020c0615060304050604020f06160507180e1002070f080301090905060703020c21 67
    0xb5182171080ca07001004002d10355450250280d03580b5040700c0c601840c281d10103405005080c014022003c007100e0340d40d400c21202150180c2c0c2104161a484000d001409980703a120b1000d1143c03400390203110005040325030062003286c0666000e00f02508030982d2018009002d044160340c022000c0c00900549040344c081610001e803140410f10b4031800f00d62510030801c0c141c401e103401462003149481140c0c1512500401c10b41d450941c400341d11907160700030010082c24180300d5210344100d00c5c000282c0c0109401c02160840c4191100e05140f0f19980340e013020700c50b1360301044500900b160f001c00080382c09440c04e00ca004201e03e80003006986800c02000712450b100160320b02c2100c82d031748041002e000c841005090301091406420301002203022104403240e44842c60345080702003548c0000c9490a0000000003090605d1b0082c50203035495035620f103040c0003009140700c00e48450240d40d011a110610900881703500b40418001040040400310743c08554081d5490700001c3d249003040b00c4500c030004034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 760917616 1250 760916366 760916393
    0x30c0206090a120b0f1b07030809010f020f130630060b07030206161b08090d140325020a03080c011d0d11120a080a0902180402041a01081504020403 65
    0x580c0510064140840180702000014040e0740501c0c403c046c03048480d031401d0f0180c1d000c29401d1300d401d940a407501c104031030061042c041010b4405000007100250648000000c01c031700039400c00540d200c2581c0302401c42d42aa0280307036945040310400b90800c0c10700640f0501b1031401c0d17104007000490a56070b0328003200303a50051030700b1030150300b00504200c840b03429940b101450020500701000b0300340a2015400305815203440003001540c0208140c1c80c0b0b40c03142458490700d00c0c0e1021440301c140031301580140c3e59810290108a44048004002d4480c210030004017008070b074007030901f500d6103086640c1c410558210080d8041159a503540c81d62240e42e0102d18144404403180180c40b1843c03401c034000b05503401d038540346605603004242802e038036080b802c21200244a80d19011a494944900c49800f81400c3c1001961151b80c0c55007003207494901c0c00361540140c0c42101e0801c181c20078507146540c40642014141d01190554000944121000100792008040184014a0f040c0c40f0b9a81d1824070080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 760918866 1250 760917616 760917623
    0xe18100e03030c181c0b154603151107061e0501031514061e0111030406020304140f09220b100305191106091219050712030c0206090a12 60
    0x408880d01c003400300c01c030303002a00015407041c0c100071109004049003810100d4402d80300802e6146a852032341110740e000d60001c0d1514807a20f0703800784155419000844181f4001a64030300c035a65070980820a0343e101d000390814041072800d00384203280e00c6e094014a0401c001c51500d102038000341c19265054890240603604c2140600442010001d42c0406c541803e4240610701400340c0c00d210185d03440c000060348007011098507060024074a0012240000c10f030b1200303101c500c0007141c04a078080c0c000c0301a00590f5240c0c0d00042d00043d900c01045845842003c1c641d400c100583c0219015500030741d43c2e4511294116030071900b0703c00d81d545000100808844032503000401003018410070000340014040d5550040b2804000d0360300717440b010204898403461501c6800b00007440403040e242c000742d9141d1a00000c040e43d040304c3d40409240c1f80301d03c8900d02103841d0f000b4a200407623181d03180c1d0b01342d420081e01642c900b0889503556080c030100f03a03c00e00074a98491150080028600c6800203440c1d0650311 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 760920116 1250 760918866 760918909
    0xc30050a0b1b1b010f0b0a09050a020708030703060302100e06030f0c09190e0105060903030d020d0b040f0c0806010f050d1505030616090807030308060907090e18100e03030c18 77
    0x48000070142190001c203c50744009081861b4591950b9524503141c00307403100e0001c00a04c503150140100c00a00c1068001040400048104115107415230f00c000c04a0340291405102c14007907001c01c03503203502410070440e44000113001080d2039030241c0d0354180e40028418001c0e4034040e04007000030000000201040e544c952600414081c2010b400d031040d00608041e2807031030401075000300107922400f030418582049a8003003282012164140c0140342c043c800a04104082c0c140301441202030710b03030398041001062604006ca0850b5200d070401d00102d040315611a0704001169040c80081c0c401c180b0002407580c854a401f244669081c403211380a5143d03031102a013001081035000d040101103512800180c0c02c4560100042a00407240e15403180089600940650710860150350910060b00005031000d55242000260303e520240302c04414221400c48609000360849001902c040c41c81c441c0c0d85030801d0000c5100c03c4040001b91031443c0540640340fa85280c0380b03001c52009031000e0040440180b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 760921366 1250 760920116 760920157
    0x51e070309052a1c030f1803150e0a0c050f0303040308130e09030c0604060c1b0305090f0a050a0e04050f16050a0501031b0e0402070c30050a0b1b 64
    0x3c198100450380004243c1c0d0100d031204c61002005101d1505990107001c4c8940b0391502110640b00305032001103101d1800e6809100d98503800c003101c0503030041e0305031040319240c00703182803100e0000135002d00c2c001d40c000d0144410300d0900050110262640700180d0700761005100100000b401c0d003000d40761940d800c00c0304400a5151070a102d0b0112006451146e9039007081021541ca0480230440750f80c01031f00018085023031501104100c5031070010481e107402c0514615100300400d41e00c4801007035000b1088644000d1041d884040002102d981d22940744d004a04400c10001c0c0000700b030801e544a4020b0058480b510440d1841078107200002c294201040c0040109202616001882001512003841c04001e10740c940780703080f440c0d07a00100751107041c0400071086d01d445948980403150003981c84030400742ca01380e942403049087c82c081d00c05102d420703400c080888200342d4010300c3c0c207041c03d03007010052020300c0e0039454604401c00301070050130380d034041280f41d9846c000d610340003005840c01c110720030090704 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 760922616 1250 760921366 760921423
    0xb1302010207120f110a08030a0309060b04060506160201020f06040b060109060f050a03050901021603030515090c16060f0c020a0203010614011d060d05240301051e07030905 76
    0x4003603034000f04a54040d0003509408030b041203840d02e00c0580e1102455104020400005000039019801a4000d110024a42103a0b90740364211184031032081000340002c0070700034108415501c060003030507041081440000c0b0b120780310180c012005070060064030380d013003000300303800d800d02c42d00716002c3e100114040103010031540e014500100030b021b50310b051124a21201030080807445081550030405450f040441c2c1001020350485880701e000301c500050b020b07102d290141c083d0800310307010740d80303401400d07607201076400c0002645100c0c500d01000c140c40c00301d055043d0204600c6a01042c2d0b1b40e030b581c800c81d406a101e4940b142c09103c80107600100849152441010700390340180c0c00102203800d030420040740c43c0e60030000612011202e25890080000840c02150040c0140d4030344107030090400051100001012801c4902150f2322501d201d1038038000170505003030301d00c10f48825000400e107034085a01c1540c900c01e1a5007184d6940b4010400d1f0606880e100c4c5884c14071a0596109045143c070903c41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 760923866 1250 760922616 760922623
    0xf0702060901020f030f04050c040c0e010201051608012d1211010f020c060706020f042d0308090607140114060a0602010b030c101110020703260a0c0c0b13020102 71
    0x840c4075900258504500801c004110f40805414004066035010200b0304000f420321800000d900064000c00400d510050001c0200741110101e5015501c2d100210384605a0170609045134800c07500c1d0004240d203001411007654001d1a00101c203081460220403051003010301407001040c000c221484191518108410705c500305402450600c1042c142d1188103603008140e0341c1070790b442214605c2e00e40000d0704041c0064801c40d4420700c2c0310f074400100810301d09080b030049012420305800e100b03c0414403540c1a078005441e400007401002c4144400d05084c07400a0051080c0ca1044406029023408064840c0c00e407055540000b09202b00f16040081c14100060010018005403009101000500012a0700d030504908424010f101d1500014211070085c4101c4080c15150000c44020450000b0800002c0d00a40c100f100000c41e01221000c0c144a400302e107024404584c13800b0185030f103460038818002c0c03c204811034140701540c001000480c0580148034854454502e80003a841000d01c002030030f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 760925116 1250 760923866 760923871
    0x50c03120a111201061211071a0708010f0905101706181b040207020d02100908121812070906030c0e1b0d09020a1a0c060c09010c030c0809090f070206 66
    0x1030600b81440000d01007036260b40a01c0c1110f5990400c0000100b4030000d400180035101001d41c0913010009000b0200801140e48144001500d0003203407650702e0306002100c0c81e5000307104140c0101d00c50f02041c8044011913002304c0c2c00c2000802c040d0006540e45801e8440c07800201c809250f40e41011040040000901444020310221207001d0045030130303d24000c0100340e50175400603000380e501042410440d22041380480c90b29400a2007800c900d54824402003c16110307004050603809607202105484112006680030300100000d180c1143c808841030118242e0192110394042c401d00c0030000b818620b44c030600d000f440c02598140d03051070400350031040c100300240960700b6440c46003000140000c804415070b0035890020a001c00d00c0c011034000917072003c486800015021441c3c18819060424040003406420303040400c0da8011764803032509a109008002d0000e01090b15071141c0d60000303218540303c04074103219184c4581490010800300300d01103030459403528105170030b20038040b100e074040001c03ea = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 760926366 1250 760925116 760925141
    0x92c150c19030b040e190312090b0613110408031e030c0f0c0a240509061902250606050312481605030303040c15050c03120a 55
    0x40c0791000c00190542400050807010007015514841c8480550700c0d034100040b01144c080468200040805c55140142142d010803004241407002c0c1e04070400080c010418017507000400300326560f690105100c9840742d03415046082035a50b10190000d030740d00304042c00207172891130000d6840b52500d80f500d05086422403880090a0303070178030030403162603000d500b00d403d5602c0c400306107500c139040010024508118180014030b42d54000c000085850501000301254041c2d20109004580318070340d13103507111601030b00c0743d0744440d020743c98410846400350014001f920020180300da1b40e003509030324602681d0b20070200b11060341e15140c08106501d01007090150400540402d140382c00c0f640b00019503101d0450061840d0a01046266048001a6903011100941c110700601d400c1700e604000c0380d00c80786904001002002c5510021400e070400100f620f1203250311484285a95013020508008400001e102d00204071080020614585081c0041c3c054464504028a107504150242400340c882004000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 760927616 1250 760926366 760926391
    0x13050103051b15030703021c0203012705040c0b030601090801050f070f05040b03150a0302041401031202030f0f071118070e01050921031b0304030b07020f07092c15 72
    0x2180c40f4400d0340c085030381040043c1030069a64108116400d40345415040300c0c25550b01c003000004154014206442c005090302821003007401c3c1c7c5006100803030300305450281203460300c1d000901840102400442e040f80c0141040c180f4140e90349849801e440c02101c4244038440c0d50f06c1440340c5281c110a12807a00022814070505250030705502c801d0900004241c88a00c244d6020300e40c0b00c980302c0c102e45001039030b00500305110920031002d50501801c001e110031141c070030314010070300342c03661001c0300380c1e017078009880100762808102c0f140100241d0000001030314000303a400a080701d240e41c0c1c070200c1d407800880b440c840596131070071150150000e0000308116042c401e040004a100e940c1e80455011503a402700307501c86080302024a081d19502590b08000007854010700b00050b004e4002000c0c0080300c2c4601807507a45a44d40460403130b120014170003012981c1e40486070500102c0c02075001018900612546003030400910481c5c030004250010000340c4940055080701258010143d01036406424503400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 760928866 1250 760927616 760927639
    0x10b0307061e030f05070302130b0405010c020103020d1b080702060f010b07030c15051009050c0906030105060313021e040c0f08010b0a1e0e01021b03071413050103051b 74
    0x150038101030b00c680c25150800075105030030a500a40c060003c20841e4042040b451402c2c103800380003036010064185445000031f90000306901c032030084805450341a591410030072030990064010f504841c1100409030f86548803c10441d41e13800d8000382c0c040c0d003651020a54107003083d01074149100508014106070400005101007030502d0120b51a0b554180340507407420415042000548020180c00a5494200028060044002440201941d140060401498036000c8000301a441803460680d0064070910040155180c42c402955124591100c281c4807824a6800151555503441c0d01012030800d0b080c00204600b41445859084e8155081c00006206056409440144144035400010302e000403044495441a242c0c1841080444907400640c19100c1c3c0180641c0320700800c05005104460303d1540440030b0140400d40424042c0c080d02810303080c101c0100c203125200d4181e503041180c0740b511040041e11882903a00a50040b409003030018500402c51603100f202d1001144119031500b00b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 760930116 1250 760928866 760928879
    0xf0a120c0c030f0e10081806010807060c0302030c1f0e010e061f030c03060606080601021603110d0213050f010b0c0309091b03070f080c0c0a030f030f0e0a05010b0307 73
    0x62030748005415080003a40001d0701402243c1480a100502d60000001900321000c160441e030818080e180c000143d0800c52a600780256968000b44940c40d030303642c03290100f044050f008100f50441940240b050b60f01d8441d01c000914030309100d91a8034111081c6249805031000c015100344040c1042d020000d21010b4660340005a50b901d016084401180c500703c41c59080c0c4400b160103000440c2e000304400f000650740c2c1000300c000d00ca14402c14000c80c94080c0002c2180d880400e03101c0188200c1c885010505003552910364202c4134078203100d0342103000303402c02d40056070701c1c615000350b0300190120209407031170104219103c0805c1a0720070780304d1007400d20405c2402c510100560b4010f04059a4101d099a03030322403074442c20800c1d14060942a41c0010511407007a43c0050800030303071507442c1c4420060740c84211001e01240725074030601c0910380000c1a0400003074841c2c1a1090000610f16000c01c00108441801c1c0c1107030500421807110ba40640a1203013000028010020520000c13030140c56003d02d03221 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 760931366 1250 760930116 760930127
    0x103050411040f06050a060c0c06111f0b0d060c091a04050f040b120303041a0f0406050a0e07090b130b220212131b03080d0c1101020f0a120c 62
    0xe41e0030721072601da840c00d400082265000ca801002c00504003d0f4450f0786002c0a4881c11000320f054401510ba4200800d00380e0240d03580400701c83c8090003c10841c01d4240004208021580050308182e40340e2501c121255030740c13071461807454026a400a01004907050107002d400d295845000401c900e03840f41804080700c04181c404131001a6120804a0101c2000034018900340300c11962050002180350380700750000024500c01c41c03207155440c1304002d10722450400c0700021030303031a0ba01050400c0020001540b5400580c0c200c18082004103800f001649091305140ca03a42191424968855501d172036803614001c40844d09440310410081d001095002c110801d06081c24403c41b501c1e82200c12410038103542c1116110504007041254606085041e400c026a40c10390a0382c2d0aa5800b81c4107220b206988807140440754400c0b411440c1080d03800c070a6010786107180b094010f0014002101c58a0b000a0005050300301c8a000001c0c2e80f80c0e0702c8107000c0c01000301803510700c3c183d92504501d1401240c004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 760932616 1250 760931366 760931393
    0xb060102010f06051e0301060803211005030c270702031c0b0d060507020321100e15040b0604050d300f0302070f06020a0f080c0903060414070b0a08060f01030504 71
    0x40b00560001103040700807c0c054402a440501c69100000b61110041d0401a03042c0d940c01c000c500052040c1c03680340440c40e041002d4014164503420145085c41c00e40b812460701402c9015014003005450303400f009400c00f1040464000001d07810000e500081c0744c079074250701c0b070180d2b0030380303004210540003140803641c44059a44020802d6075144041070880f8000c1042e038890100703414014450219140c0030000b240c100341d811007541d15955401148004c034131040207124101036500341c1c0005034140f040001a1884040c900d800c454104004207094454050b05801c89000768040c601c2e101002c1040400d03520004840c1003e0300060304500078082c1c0c0410b070784130300b80d02c24030300581c0b5000365081100c281d060076240140f806d0b100040080f84503411071880e1160300d100e03480b0311002c2e40d51f00c0c0514020384140c030011030b4503400040004001a108102440202506004a07030403952a80c51031206070340b000c1042000b081c6204100310a03490103a00c81e902404082c40c043c0038500345583c500c6002c4000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 760933866 1250 760932616 760932649
    0xc060a0608071a030c090a0b09090601030501051c061e060f0e0112120201020f0a020c2d01050d180c0e10060801230303040f0626010e040c09090b060102010f0605 71
    0x4989999074039415130304c603a48007c0c944c646c119a103410680c065404000c41e41c0c000d00c0380f0302c001803040d80a8032800b4103e880240400050f80c84890502c2d48041c2002d4080340e080d40c5d01c8a40c0682030400c1c1c0a809d500c41c404042c0080c210381810340100d01340d0680d601910b4000010001070081d400148000c4e801603510030849002144a400242d0282c011104507441c416800b20300c0340406c4d036000440e64000d80c401c1d00c1058010b1640b10740d010080d18032419114421002900c80b00701948580001e0041c0c25848070002011000b040d8a0b100302111020b0564035203102d018144402180e05800c5600041015002c0110501d0014082c045d03d2051140741d84051030203002425820000402c40c030308140c02015250365030744a030341c0313907940344980e002d07402c00210f1906204d00d032175102e148800b03000140005000d003240e207002d803007504c1c101c40100100d03500100088005195552030180301c201910a0120405031304d048000207084446a2104041d01390030b00101308916201c12600b00e014a00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 760935116 1250 760933866 760933919
    0xe0c07051009081222120e040606050f0903010b04060b0705121303020f010c0f080418090506040b060d0501050403030b150703230f031006030606050c030f1308030c060a060807 77
    0x100d03c6003064a9000e502404440445005090760400c40807003810801b01e10540c031070a00c5100184107000407500c040c040c0c000810310030090002a26652405440944e50080003c41c05c802010302050a9030342d5a4020a903c15000c034203141009070074807403140900c031460300035801c0840d106401c951038030251001030700403500c060507512a6485652644040c40d00030742070502d1013049142c030000c240e202d80b154080004401d0b0140342282c086014809400350001c1c003c00d026215074965005031040175040035801800d140244000403400c0c018103210700c0c06910002800780903c0c050004160100c803a4103000d0004000f9440025045030344840c0045444103801412240c40e07000d12014800c407410941c220001008016800e4182440304080d140d072a9801c2c010b44e80d540c4410384250140c41000c060681040c00401c0c001d005036000360030000c280400702012a40c0d113820a85c11603001c200c0154440e040b6404000b0140c0045c051b14002300fa20740c008020052400e03681d800c54001c0192007210398038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 760936366 1250 760935116 760935121
    0x515070504030605040c0e040b040203010c02070b07080c031308010b0103060f05030604030f030e19020315010609060513030c060f08010e0c220e070c0b0c0f180a0e0c070510090812 79
    0x1b200c1502240a0000d8150b0041e103400c0c2418806c40181081781e04900c01e40c01c050891100520100b14502150301929400341056060b0391403000c15007040d009104e0501c81031080141d13403401d9540250090105030000201070130300c27000050584109801c03020703801c800c0075001c11407034500040083e40b064061400002c09481000308802400c0c009040200c6c611803010003507600c0503100c020720070309407003203049440130000003e40c0d10000c50240306000106480c8041006040c1c010401031040e414800708990405459941e16908050550420800201c050b01f240b2a4240c004003810b01511100001d0040c928040b032040380e9611070501442c07036100034600b40ca0100e403405013441000c2c00000c0348812040c03038403447c0105651480807060703d003c003910000c03034001413043c0103c458510341c00d10740300d10f070030a42d0032850172801c540d00940c1d4000311180f0b00000c4011b904030490b80115030309213005540b0040d500f003140c502490241c01c021450b00c1e00c0a0303040011608001c640440daa03c0002405c1903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 760937616 1250 760936366 760936373
    0x32010507061104150224040b040c051e04050718060e010c023703050c09090a060c110f0c09070e21100606020c0a0e090712050a051507050403060504 65
    0x10242c4481c4103410190108003c0b50f9250828200c0900c8503c0303600b105d0302090040c5242c00d08a26005910340181c20706000300d008650104a081ea05c1b9000c3c2c44c0314140c0c1a036a801007402034840d00300800030f200130072602213002d241c14042c498200c842482e080408542ca42500641964a8414070043c098021650034183e4005d810398030105400a020b030b03c900c0448141d80740305114800d0102820041e4806103059140e25803038503026a50082f0080c03002c12460703401d0026100014011814921a204086001a62902030514001030035503c000c140400e14020910f00141c00710840354641100c80700700c1c0117441d01000d00f64041024680740d085200544081610288400140f408442081c0030041a83c580010083c0ea940307003d00081000d213a40d01c900300e88944044180681c0a0145c8000700100780c0c181142542045641c070503903056641e9450002144c0d204c00100311030907007003201d4402c14881d06000d001c2c0d10502030000f03540d551401d00d000400e10f1159010003458141d03a07501080c1071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 760938866 1250 760937616 760937621
    0x4030605063a060f020901142107110f010603031e0e0405040f0c09020702190806040212030c070612060b09150717070803060f150d09020411040f3201050706 69
    0xb00c5800c090100042c458403c4050081e40c401d0511a01260800c5040a05a1001e2044944161460b0b54402c0c0401810380c0a43c0790190280008040003014041900094414003411151880040c000104c00d49103203005070104540c0ca2010302d40034000800140d825800501a010b444030454001480b40d4461038804400050144003800d00b0004d000e002c1401400c5e50f00802030180211140c02c1002d156985c0743c9500d070068000c0071240d0f00100c0104005003495403c40c2e00340380505042d41e09081203120241e00d425001e910240016000c881055003d640c01d00c1140041d01e9078104192074030705240701241c8500d4071411540c030800744c00100d2009101082c07000842c5007c040303030010761b92200d500380b10a403034005a940500c6800b6212001d1024034108604c140d4a20955103c2c0d420a5052038070100180700d0068141d0f00a9240c212054201b05500001c4c070180c803440103d8808c81e420004a1680c4064415401280b14502008072040c600c42d08103d4200b60024648140e46040a00c1c00b00007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 760940116 1250 760938866 760938979
    0xf090b040204091a12010b1c0206040b190e0d020a03032313060e0301020405031e0f010606050403032c0d0203030c070602010c0815060409021b0f0c270a02090102210403060506 77
    0x2d04010201d542837500c500700448034031116a41d0741e2010403444040410003440c000400c000e60101d441d1108100280c0511103030b100600c1010080e18402240360103200080e801030712601681d030306295043c03150ba500f0041040300407800750000c504160802001c25030700c00000d07185407803488607035080c0003101d0800c00c11150651a17810080c420343e41d035400040e00c0d5070810701046001c224500119110004100c241804829080c0c3d203003c88030a9486c18402d0007026500186e03014002006030580345603080107a50002c190b59800001c403054095001000b170180940031020130300c113201c501d840e9a51a04c05481c1600d6410383c0050351915001c4194900b04001e00000c0354038001c682018485000109500884a01c20780301e5014100c08140c1040c4600c8009088014001c51040460004d010603406052040c0301801140c90b1f06080b0340d0806007407078840c5803040c1040c400080900800c549809000d400c0841a16403107089000304034881015001150201d10340c9600303610132468050302003800c46 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 760941366 1250 760940116 760940129
    0x3090d0305010e061c12020604110405100e07030902060c0d03140408270d050a031119080714060a02040801151d0907170102040e0c040f090b040204091a12010b1c020604 74
    0x4026421446c00652283c0741107906851a41078010342d03c180c6d003468061640700d00d00c004400d000040c10540c2040c0d007800040c0c2044201980c0d400c3c10f00051302d0381030082ca0150805002841a800c40d03550080a03243d404907010b80004201e0140400030700c1e08810342d83c03801c0140303030187c070780d03148010703024100c600c040e1811f0360300c0002112040d06004000c10420401400303951807000d100300307003030000c2d40d901c50703502c2e100695003080c90009010904c0340e8090b01196100d040c1c0700010700c180082c0302d0701d494000c7c2d4a6408541e40010104581c071402d1054044010300c010340d82d40550301d020baa696010b10034283c01540300601200140113031001740940b0029000740719500c411040a0402603000390810701901d0b004120360400b1403901203840c419141100d00300380d80c54515905104684d07002d84480384009800a80902020440020700ccc003038541062280c0d40000340404112003045042d0b40d81c410710210340d0b450008109015114081e500c10321000345401c18030301e40014404642075100326031240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 760942616 1250 760941366 760941383
    0x9020f04050705120708061c08040306020f04061d0d032607020d090812030402132d051f050409030e030f0d021501060c140c0a030803090d0305010e061c 67
    0x101d00c0c0c100000c2c01c80500d28400d544c1d4a540c0c1d000c001d0ba00b00c642540d500b41c0c01110080442540e001e104001202281714004540c10550b8a03a52a401e90700301400c070500080300441c042c0700c001c0d8007018008480e43c490242e0404141c1640c007103100d200610b20091708103e08060704541c83c0340c50004038000004184540c140c0b620706114025181d141d041d22050000d51f4244002804081c0051a104000842414580303103840f00d500708030042401701c204460540d100c222a120900c4900c1d422520760010103206c64032000c01c40201d104951004080007000510061085201c0700001c00990a0b213200785c0780091780350442e04003696480215005c4d030b641071080c1401024013680128400c0305034950b81d0200e4a2489560900a03090b03182401840300048c0c00130100808208810000c0101c1c05d0310005881c907051050000ca4040c0c030035078006440244001041c084040c4007081096440d0015207002c00255040824164034800c1c081c003502e1043e020000c4001c400313544414085615a071181c8071 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 760943866 1250 760942616 760942621
    0x81e0708132a08010b030304140102191101080919020103020d0b041e060e070f0507060e1e07060c15020c0313030b04060f1e0c020c0a090203060a060f0503070309020f0405 75
    0x801000082850b0919502c0101c2400061100c00c14058080110030003006181440e007000400520400c0050001c0d0440c0301d500c0b1005003031002c00d458a64041d0013030842e0050070000301c00240508002070aa84901c1d4010364200388000100c042064401c1d0f824070300542d9900384c03003000e00e01030501035001c107a11525010b1480082d401d0b40303400c580c08001c0325206000c080c2e55a00c0b0b40044800848001c0003184140044949940c810401052458816180090b1115a4481640c501058002403003024040a0011070305c1420410409006110300d2811710f082042641c0c810312180c64040d01c0f00100c6030045120404003600340240d80062001c0310502980a50328200342c0c2c01010103980540709140381a0312032031450124080c80b041c1e40500c41c1c206940c0d80f5400c2603c40280540c0c28041d045000f203100080c1a99110360030000100323155940507031242050b208220800510790b01003000d22100b0014010070703681140641e0342c001d00500340090003004500200301064100900c03203500c103151504 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 760945116 1250 760943866 760943903
    0x1060c03271202040b0607031b060204150c060b09091e1908041406091c030e040f022101060906110a080a0815010311160204020c0d03060501081e070813 67
    0xc400d016640216130a108104041080c040684124400940010300244034000484107a0404e6540310307200710001403034075031380e03001d00030302d00c0b01c4030550800203010b104009050200300e000d0041e20100440d1103144504150703501555644541c4082070085140c4a00d0441101c0140424140245e290101429101ea40d2038266004c2c3d00c10f00580c614040703000190801d40c1081d0050300e1a080016040680c800d8104c2c4107942c0500784402c0440c10415030040440300c07525030340180c0014141d06078000d030304c80010310000042800480c0e0303655102c0c0010001001700651210300482100d40b1400c08030900034200d0092424401601340c09407020b1800604006402d600a1085225220035901800c48454203001141692032400c84c104003420b06004445042c900c1105547c021440200014a40106814440d0800c10007014180100c4e541c1c120812295030041c00c20303036010f000b050201d040d4a044041fa100d9100b4080d19281c01c004036500000c2c1c609a9004403018819000184c42c0d100c10000760 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 760946366 1250 760945116 760945139
    0xe0f0a1a09030f03090a0603020c0d1b1b0932090a080f120c090a030227090f0c090c071212020c06090c01090b04051003021201030b1e01060c0327 64
    0xa500c14012011b500d0005030187c4a40b0030f44203034510b880040e01c0c030341ea2462001c0342d6100013181414000055107400c000000e02030030b684c00202c0040ca206011440c9000e02c004100ea03000c911401c246c0440c0000a40c200c0340c400907000c85158a404446802e03190080c9192401d80c0d8804000c1090340c00041403200180c414001d0048600502044c00d070342d55422150001500500311303819040324400809000525003104d03902c410310070704440b4410107a045a80d0701030900050701c5858042d0010300660030052010300881c644401d0943d00700e906070030440844149485000c1000d004001904c0b084030032203100d0a003041c90707090300340c03c1551185100e00140752500c6040e031321000a8800c01d21010000c1d400389032110100d503204480203040915180500a04801d03421541007010350030001801920440403506020b14090102c0d0100e514000c402e03540d280e100c010100d0344c1c3c8030704900100b1015030f02c0620440101da040c60030000321800b40002c0390741d40c1d074004507480b490740070400007007402c42221 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 760947616 1250 760946366 760946377
    0x1211030307051501051f0309050f01060902090906032803050702100e03012a0315031704030507050607020f01030c1701060c0b010b030f1305100204060e010e0f0a1a09030f03 76
    0x10410358050b42d0307032901000020440c0d0aa080365070100d01840301c40780c0b8088e038049648180604180d50340a602c0345401401c450464100f00c03403c0b17038080381041c094100802540c0c2d2110094009016aa280b01d020320008942614903005603400310100c002094484d4040d01c1034690b004d01000703050f440b403003c00790800040d18035a6000b903107090101c0d0105214450010907a4044da0313010b00d1182c0d9001d000b20060851401c2e141078400e5031a50010001e141480342242d07145550780c0da03945503030951a040c2d0800c2050360049106400c14000c41015039100204840e200c00d09080011720840c45e02000d4440b05c03021440100c0076034040c1d00015006070050401d164a0303101e07510b910116078a4032480348803070006039103c150700090300001640720540ca140e482001c0d40510102d03122507048a065109903481604040001421101c0703119032035820030340b0b44411030f404503000e003215161a0040381450380c1c00e21501a0112602e0302e1240145002c0044601140c0007405032008c500114210070740d81c3c1d100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 760948866 1250 760947616 760947643
    0x17070f140115060e0d0303090f06021908060a051309020d05070501020712080a0315090509070e0901020a020c0f060c0f010501170307050c06090406090f050406110403020109121103030705 82
    0x3030468418402c0c070302060003001d8803a9a11040340152407101400042c1c49020811014140e6400f06480403c07080c040c040250380c814031002d44e07620342c114016562041d0541401e401c0c00020824420555189034459003074a400b615803c045070700d03511500b00541600703080690032000c07000071001840230110720182034410a0702210552580c403100e00c62850b0602c01d024112280500c01040c1092007034000b9a48124052400c20070282c0784d41c10001160700c00c3d600c0c1405503029002c10000f88042c03513016a0f0207404900210705128036840c000e9110752100700040d100380220b02980100baa1560203940c0d8065000e0111185000400902c600900d0300307001d903d070014080960464001c60003c1180c922582c0000a0500f107440b14050024a03004480c280b5805600c0f2440400d02026a100e0010440c0ea080c501040c01c2c18503040c45811980107480288010400700024000b603600f008014084402c04d816803c858422803d0030030343c6a810316021541404005006024820000343c1c80c020f0542e07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 760950116 1250 760948866 760948871
    0xb0f0307031a042d020405060d0b361605220b21060103020306130f0b04050a02060a0f0915020d2a0b1909030c060b0414100e0c0306060717070f1401 65
    0x40361401c1017000c1d074a07274500612080740700001030310b0403440141d5207480a80e218480c01e0300b4802091410705651280d020468203a020309a46000c01c4c1c2000010340042c0000d54038420580c0030380035440540781807080800d0886403500c000e07610a481c0c0301c0f900b60380c004044103200344010369545000e0301c03440280300a03446407083c01d010800406840840704400e50740020b03d02100b180075540d144040c1001401500c080c001d03c0f0301140507132110070040c28442d046540e4080b00160101c0301810645890b0098100140c0c080f036581c007016000550360f40303400d04031b0401c0001c8000311800d49001d038014960044201d900d03601c102041042c02d40c09030303000c4c40f5005403500301d40f00b42c1c0c20807404407408501c0c0900011901580e4030003043c0640e001d070302c42050141010904200c01e1140710a00441034400b5408981410302c100400c46a00034080d0f0050083ca98403442c5041160029805001380700000e000d601420b5940c00d061b040303000454000a0b40700240e4584080c803410484120704044024008550 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 760951366 1250 760950116 760950121
    0x5070303110a022509020f0702030105180304050d240c02060721050a0b0901060807030c0305060a0302100203040e0703050105310b03010b130b0f0307031a042d020405 73
    0x608401a00d074250750543c000d1400440004601203c001c4030659802d405140c41008912590717140001c0c0b0b880901c3e100c1880d41d0710400e20616003125802000406c01034140400c50b2191030001c0122801c40300121404400a41c95080c02260341d604140c070500c2c040401c6c1e011512460707054100314807480300da030240d0f40ca03540d56007800e4600d0011002084002025104461001c01d4554403e0360450800c000002e405149003010039017194080c1c03c10300c0450300352420802455818002c4c0c000a0a00385414005801e00c0400304011341b0389800300900c1810341e032049400d564402c00c00d0750010006080c8980729401d108001400901003030140c14010202d07062010303440d02c500c8400706d403140605180f40a40c0380010002d44014089506c02960554a984a81440e0b0380e0b4010808071a00c041240050201c90410800c8540041105898043d81205801300040b92032101d0355450301c469802808000c0c0da981c40e00c00b950b040100b115604108030b4102c0c11f5283d05044005a440300d10030385041040b034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 760952616 1250 760951366 760951391
    0xd021c0c050c150709090e06012c040206031b0403030e1306031a0c0f0408060105041821030f0603110312041a1305040501030f060f0605130c021c05070303 68
    0x520036070400780c80ba64842d088030038030b4440007030015500686518010741c006498a209000340d41a14000840f540d010748018404200e4500e0b420158001e4200c146c0d0344850b00c0102c0c22906c003401403002e84144808800142040184038442201c00207178807140e50703a680c503890040c08001c0d903168541d00520301007800c020512198441c010641e90022500340c15050500c07120b081c3c0d04402419000c0d2517405021a000741d100180c040e101600749030380038110300c1d03041500780000c4440741b50500c0c0078a18990b84200c003044614840d001049111348440f0345003070744500260040c0001020360001d80e031800c8070000a000c0d000040c03102d85041101034078140030200e02c925810780500d0094540c0427180b940c400000070b0f81500201007140b01810021080795440000170200d0380300741e20943e4068140c581800800219128114000782c203108100001782c145008551a1411111044078441d920010b00b44018020000d01e80304040b4003030340320507010801100a2181e000f945044021034100342c03c100c0107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 760953866 1250 760952616 760952627
    0x70e0405070b040b1b06040b18100f14240d03050418050a0b0301140106050a0c0b15030f030a0c0b0603030d0c110c04060b07060c1106010305070e0906061e04020d021c0c 74
    0x11f01d401100c02c04e400d464840c40d1112180c200445070b100d030f1141c3c1c44d030b0b410400c0150180a00241a803800003c102c0840d605040c1c2d1110010314241011512141103031409005447d101d60f14a4190b41c1055030350701c0c03417400b91250700c00d0fa004190940c4504008001c241c60b10f4100e00e01c280c040710800d001c0e250810050600f43c500340321003c00950081e4006001940c41040503000b9201180760034142d080423a04c81c070843c01c40c19121041c40044035640c04009013020045648915820b1300254500505010005e11404144000410b10389076030011949aa80410648a102ca41440d040141118020f8083c00e003031440c14900440d8092106408003074685071041e281160400600d04ac50404030313170b880c2d1009203031400c0588103002d440703050403109400030048507029503c200020100d150074461541404c02000740340700c400c0e6105604108480d21228200b004442d41c01d0360211060f42da19000402a00070750154010191010070900c51032050511404a40d004400c4204801c0c2c0380688200e90 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 760955116 1250 760953866 760953871
    0xb04020109060c11100c0206030f100605120601120603021f090816090906060e100f0e190e0c0d0c030204060b0a05031303020a020d0b04170408070e0405070b040b1b06 73
    0xd881000041041070620a040540008140ca4030691b84000785c3c1c0001c5007030f0020f4501005442050080040700707484418000b003d494181801410301d0b10130b0b014540300da040105494104054003a00b104001e1203504882c002d11ba00800c41e0000044040704082c141159805041c0068612200000c1115000c500d010f03289070702282036687e0354100100c10018105240c42203402c19550240020041c0001044a000301050f5500c0202c0520b424080c01c1126441d0304044402042c02d01409800300d400303116074464031024070004c904111000317200c0d814185002c41c0c180d00031860403016000c0140c10b24001080e244201c0d010000c042d25003a00380c003603010b115103d03000b0070380810100721240f8504c1c00c1030190a12a104036100c805461780424024040c03041d0407108245404144020403103403200e0a603c0d01ca03d25800c40c14289400d0780d0070365901d45482030140f4020307035901040074050b0a0015070064405080681c2d6902d64030485108207a00c980f032a5001e246c42e8080034a04060041030550 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 760956366 1250 760955116 760955123
    0x321501030c020a06090f0807030207030506060f1807020703061b02010617190c030606030303270203191109150102210f0c010e0a0b090708060c07170708070b04020109060c 75
    0xc0f80c4600d658601d401090034103425111002c0480d407400c00141401d0003070060364801e80c081c8c00540d00d1441e0403460701c48050300c818400c0340090100b80c2251980b01c3c20507841d031001d08410400e81c031490410b0b0306004003070300050a80d03428603000c280341001411601e022140560300030070101d0340d10000484908041090345000d0b41000c07418114100000010b40c021038003070202240019900e542d804102c0e5a9a8412408280c032a9000c4490443d16154032202c0c50300d40000b06140300d0160700081c2c4440800e500540c0e100c1c0503d5480f030500040c412070f1183e001026003061403d04150491440040b8620984c0303006125401290b026842d940d010940b00d2842220003600300724560100e11000d07045000c50718015982e4400304100380004003c1989024011101401c90f410800300f0b0505044150308804159403201d820b2110403040d01046400064002d802d1002051050030009141e00c1441800360029401045070002d006202e080d150045100b600d400203601d61340e00d401d40d81c4001403040903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 760957616 1250 760956366 760956373
    0xb010909091a1b120f0105060307020c210703081b0712170f0a031d0304080a020d030c0c060503011509140f060d090503031801150603321501030c02 65
    0xc940b40001802c10341c10103542c20008181da10840310f00d403a9504028000451488407005100c600114100a03501500c0d082d1400c3e841c511f0300721030207951208200070700780c054188503007204240e045481c1c103168640010415a82550360700d0600712169000150008188803001c0d03a00419250001003035022110604c1080c8441a125199003082a94440c0e400380c0b204010042c1860711080d070401440302c0b160319180010040c05104440c40880e0010314102c4655000304410320202000040c0502226070446220050414518044560941d0980b00031700025811402051840c0c2241c0510706135415005901e40180e407a03482111902c81511500d4010101c4a08201603030609041e0001c00c0d14002e8405890a030100c120391007140c0500e0030a0710260000300601c400007004495100b109800755000344034000c103030510401c0800b1588142024140d40f00341e0031042d070340104081800c0c485446021629070032101800344058108686c5140d15600b180c00904481d80030384101942403044da4001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 760958866 1250 760957616 760957643
    0x3031222021e0315091f0605220603050312071d0105030402090a0e0607090602160302090117280b0906101707182009030607030c0c150b01090909 64
    0x81100b03102080390081d40500440b01c0355a2140181c1000c9801011028020140980c41c0f00250030001c0d02c4100b802181ca003010000c006982e80c5401d03c0800c5804184000c185008406d407410081400b5400100580404144264640e18860266106480d1511036041d032039070541e0102128200460130f1404620140081009410903030b05d180ea100703000413400281041c00d211100d24205e030842e0800000340b240a0140081030381405050241e03010340704001945411680058a10041401401c210740c10200307040707180e0801009251f4a4148006104030500c007640b1803442407010001c01a14660480408a000c103000004d80610401503150810b038801d04100075442c1d4030126040407002841aa10041840744060300c141c801011109000240000206201c0d160880501c51501c019041480b00d8016500d0200308260f00850503d400100810a03507015141d03950038101c060700d100b0115920fa40850ba10b03500201100100340c803011103181d030710b000c12010342e864054010400642d0740314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 760960116 1250 760958866 760958899
    0x603030c080904092a170703020d0c090507180510020d0f0207080f030a2a02061c051905060312070b070c02031b1903020321090303122202 61
    0x1d442c901c84001c10110b590304080d25a140c1714226031804400c4841c26560400b0b00300c0780780f01d100d8001e00900702d114444035820350840c0e441d94180e2002a00526035080c940c401c0000b042d4a50001d0079940d141088642041c101c000c142490101980449001075503001c14a45401070104c15050003a0b4001c00b00c42d41c0480d01183d21800a1410030709611031a4004118010b0a20078160411000401143c07100140e0300c006114901d241951900e03601002c0040110242040c851404c4580590f0320036520361152508104598103040712501a41ca09018050100f84405140c0031010344890305100c075483d0790b0200f54440403003029203940c00e8010402c0900050001c0e024a501070054103042c081c2c900b564000ca13040c814588005a400f0441c3e09100d04285402d501c580400118901107010303490940d03010070341d44d28400044c000004034480f030310f01c00500c1c03040c00c4505807003010f01076070785071450540c01c0c065407481510610010b5010b42803a00c03101070807445041916800406165201c5035149 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 760961366 1250 760960116 760960133
    0x10f05041103041113020f07060501060c080703050a0509040905010902011403150f06070605070203040303021605060a120b030708012c0703022205150907030903020d050c0709060b0306010908010603030c 89
    0x300700d6040138407000e601d1780040640c4040d060200419180e680c0d50303070709840c05a0440300160000340078000801c0c10080422100030685d000f2941c0343c14001e40d00ea0300f0400c180ca6901807144035642c09030a103d10f00b0200201900702c0e5103914400c0c1c0b118800040c12160303c0d206800120392100141f80303401c1110380c0e03034501940030601d2000c01500c0545884241d0310f0b10302c10307a8411a1000c025910000d81041015070411451904940000c042c040580c10100068407038882e503c0000204582d1101c0b0441c14090341e4403074000b05100808075400c8950301c0c00283c3c068034040490a4a00c008429520b110320024103c1f01c0040c04014041c0480d5800c0d54204407240c417640c40e01500002e45222100303e0343c22544a4580110202c02c10088039210503020004801e5000f08410304150401901c800002d8001131a02e80706483c038104a03440d4400700e260a40341c19000d81c0301c0a462400c02a00181c942c3d40c0c0d0f0000c40c050315003a40c030004613580301e0580d682070340c501d03120090004110b081090041041d11 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 760962616 1250 760961366 760961393
    0x1211071802131508010e07030506010f0305061810061b021c0323070c08030a20240702070f03120804030c0206180910061e2105010f0504110304 63
    0x159028880b43c8900d985482c0811841c80140811010401030103034240820049500c1046032506104519100c0d000900158640d09441d05241c0c03541c02084541c2c4d00c0d0306415075040320454040721103151403421050200040c1c403c07000070a10380300e09a140003840d00c0c88038404940280101800c03031109800740394900000d180035010403006602c0a0b240c50107041c04d1052845600140548403402802c011840c005658020140c650080000c81c0324140c10a0141d540f1b41820f1020b0010002c180044a0070062014016264203004080b8461810701c544841c0707010300042e03401c481502d83c890b54410241d90283c003020b00315521540c0201700c050702c540ca030700c3d500602c40c0c6400f070b08200750340d0b0108125803c41174211402500c14102004d0034240314080590014502100c1003074289001001b404d484a150200c07402c00c04590b41d41c4591034081c1035010b12260801800c00ca8030000c40712310100800080c01644071800c07140d20b00203054940750040e10003240c1258105807a64589036038032030291021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 760963866 1250 760962616 760962637
    0x10903020934110c01032a11030d0501140306060a090b0f1e0310021611060c03041e0e07080601080703090b01090902120f190309030b041211071802 65
    0xb002e08107410b20b81104800002c0ca440c0f43ca0b8910f03110500c41c0f0711410000c00b1643c4c113042514010340d000101c00b400d0030002c84907400310801d03140e160420390f084600c880d541031054501d210024910210001582c8018100d4000e119031903100c00f40202019243c21081d40d81a50114007a08184801034403580700041d8200c0082c001f0751140d103d2400b103400c540c1d4602c5070b0018600d410200360300c5070a00344581c448150307450300308518190b8104c01c2c580e0100d0f4105005003800000d94140a266140c502c111a802c101050840f0340f526603444401e0443c0454042c04014840c58040024102d04811441c90207251242c481c0e80f2039950b98001103491103c0101003000301519401c9040c0415510915a07028001c0d507007001c81c200007240140120104042c00c910b0700c81c0d10190103080d06c0000880e15041e484400c0c3c8504407044001d08040b94002d10f07903080a840065401c0070301041020700070200748140c1075500e40e0980b10308800f515503224100b61113051242d4403024039007100780055a00030311580d0326 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 760965116 1250 760963866 760963921
    0x50a08070c050703060c0816090b0c070506030c04170f070302040c20030c2a060912060f01060e062a010603170301030c080a1104092405150109030209 66
    0x400d84400f46070000c41c0d8001d81c2d426075610343e0300718180d071300800050707020400800c0c0c1d1640c0004a030000300030f0701c05807082d041009000300e1511101c0c1c806110313040c004c1800409464a17070400844524459000d07100341c1200385403090708800b0300d1f07201080e00d28403000254050121b291441d02400080c1540c40d502104210b05044160100000d4070002003072205000c00964440c0110441c4900d008041d581d1480c05c659610150051451818042e060380c12060b00c5d03441e01c895840021610b80200b0308100c01940c003540c010464031178525540e81d412141079076500600007000c803051103818442c4a140c0d05240740402050240d4810b8405a103060400e80b400001d041e6640c2d45400d804590070740351610030844000010418031410b401c0c0032000d0f20264024041d250201d40c3c03058a0820300c8031085004545400c0e1400600100092280030030b41d00b03507055001c800030703c44043d00900c030423200088015035030f030208442035200300342e4002500c3e07000d402d642060311040103801034032020271aa42c08010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 760966366 1250 760965116 760965137
    0x1e030c06100e06130603060903090f0f08100c02160e061815100212130e091204210b0705030a0f050105060d050402030102160f0b1f0302010c0203070305011806050a020a050a0807 78
    0x112944507120150703000b5902c0000f10307424510b2400054507564451103e01202d074100740b103080f8dc0032400703001c41703071030a00001030500c1e00b04010790030f001c240c105a10701110381250014403000560782491148100700c46050600024021900b40100c0c16a81c0d9694200c055510390240e0801003d140100781880c0121901c0800c0b50206098642c0803030700968400400c0c50040001810181c80c65411a01140141c009486100141f0055026900c01c4044249400d4660801201d5180b440b148071a0000074082107407078045805081c690060754a01c05041c500299601d02c03221610030241a100c004010344d281c500e40b421030ba0701900340540181d1341550300700141040d00302d80b4030b02c1c0421144210300b0010202c106040c69441050011b040c40d80c03402c44070081c901d10102210040d001d0700c1e424240000303407000c9030011034640400d6402c020f18962a040020481c8440c00c0c10744450113108020611103a90b40c000c00005900400d8000000302da02070041e000514040e5141c691700c0301d001e00d0a0170300f0a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 760967616 1250 760966366 760966373
    0xc03050d022b0f141302220903050901020c01030902100e060408160303020d02060105210a05060903040f1208041a0c0a0b24150a021e030c06100e06130603 68
    0x400c06038104089607a500c20f08510035030031a010b40d4500e1350903001958075074940140e24802068041c0c8000344100d19010302c0100d004107156141c0301200d030300c010400011559250142442c0d1003915518058810000c02d080150322034060f55a00c598098489503003021162416607940c0140d15459a12540c1030101040404040160111403100301000503a01842c43c100682008594100601150001c100500058403400200464000d0724040c8122440003150b0503400c02c0c0350214000c0c1140120802d10003814000006803003a01c0d05520b42c55011680d40e641d03403c0505144500800c401c82c140002c102104e80a0004650f038100408039500c1c1103520143c483c14000381100403100b10b02110144084450400945641c0e0000c80c10805d1110b101000000e811050350058401d0402d00007a081e00c95130320034023511804000c1186ca08450602e941c48240d2290000f044a00d944e104040c001030005d00050740c445d0443d0440c800e482c441d901c90005000e100f5905030300d10411349440340c1000000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 760968866 1250 760967616 760967677
    0x209040e0102070c061119060207050307060903120e1506040b0d0303050106140406050d0504050319050403021f1407050c180f09060115030207020a0503031603020601060c03050d02 79
    0x3104120000180ea6110302d28100030030030740b250400001c02003042e400394054800090f6031002103c20f10070a020b001c0851600230b010348940880140103000218420741044416000072402c00d1080e00c580c15642024a080c0044415402c24070752541c0c80040d082c0032403038401080c550000c00c0a480401c0d0504d5003c08103603181c4906204500107070352100100a425407004c1c590111a0760745508078a01490300500911398061110981d1900b0f54440c0070404004081049602a00e410100d04441d2a0051009007907500548000d9000710f401c46d40026284449401918461081d0f0311904907002d0112407114054200c0c0004440c28440c0b803400149594502c5c1620086201d0402101080d182050726841c0300304000d40f00d4405a80800010b100408040568144042d950b1400503242c3d1003a00015450404a40c0181c2c4c2500000402030402c00c0036400a148860194085641ca41d03a02c200440380c045111202a0004005005482e90352203075030000c02030303900084902c8001d44054100c0014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 760970116 1250 760968866 760968881
    0xa0b13020d0308180c010e2715030f0102071e030302070b0c070510090b060f0a0f120b070f02060c2a0f070501090f1403030d020c0d2d05030a020904 65
    0x40f40914003086072031070900282c031007080c0440000d0601a83c003680080c003646400d1801610030011040d800220b0340329103130030103082c1062604a1105081c04154400c1d10f40003040c03554002d0061321003110000905008a0b001c0743c2d8000b400c0c4489680d152411506004804001c03401c040d000c100380c0c0080340300425038900690b00515695510030891a0491134a4101c02125500710704180001c004104a0350000c0c0d4450070944598030003200c0032002402c01441a00b03d00301c81e0500780004120070030300c3c582c0303c0240b52068041103216124440c0a0b904000302c00e120b03100503032280300011000c1382c0c0b80300a80001c9401240c3c0700d8540201c9020101206000e21a80482d640f08404006d42d20b5003c001c2400141340a0802c041c0031810a040c28000401901510302032500390020160651001c200315903a903030784000110341703031481250060340b00c2c44180902c100040140a0380d880e448164042a142c3c5811003564110000c0303840c00945198100800702d00c00c41d40e080c00088e1040d190b5000740c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 760971223 1107 760970116 760970123
    0x1c08010f12030e060a17010806010603110304120c020a2c0c280504261b0904150b03030c01090b0a060602120309070b0f1b0c030a0b13020d 61
    0x46d4504203c41840d036070080e018800010031440c045180c2d4160350150b9800e001c0e900704603114107480d00058402514034900d204200007258001d4044c000001d1014010032180c41d500c01045501c00a0300741c07800c04040c03100c0c16550b00072100c8241141c3c0400f1a280aa00707044801c00e51400c218201e03200311401340720000101c1c04180c05001a100108a1f61050501112600518980400180e20000141e200b80340e00158031511000c000940100b01400349040f83e5030b207496540113220050301c54800303103569001310351f1662400d00007012009088800031a170b0703400303524142c40c0c280d000a1501c8400303480d041e401c1c4115030f4046020302148a007901c90b15102d842da0141641886029480788443c1e02001801540d40c0d4500c6010b01800404000c0c0d06001100240075151107024041e142541a08107001d5000020b601611858010716014880c880301c180a81c0031802c107228400c0d042c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 760791366 760971223 := by
  have h0 := BRFrame.cov_init 760791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 760791366 ≤ n) (h2 : n < 760971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
