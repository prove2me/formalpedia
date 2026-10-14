-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2670
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:23:38.088175+00:00
-- url     : https://prove2.me/submissions/a076c64d-d498-45d5-a178-605fb5868b6d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 480035971 ≤ n < 480215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 480037221 1250 480035971 480035981
    0xc06290f0307180b030f06131101020109020a030303051308031003060b0f180c07080703080718061d12010905070503060f040203070605090d050f060106020f1b09060d0804060224060112 81
    0x180502140e400c9214103004600742481104c404a508c400c1f8103440040c06100c40c41a80d40350000e00080090348440c0d0041451100d079400f000c0d05250315140400c00a421004019600744d80240e800d6840341815090300d00c040f505444260b440300c0c00c001e11040c079450401003004100200400324510307204908602c149005008016000e40302c018404c1c2404104044010100c40340300765580d045d2450304150107080d9003030b01ca14000503803011b40000d20141380c011001c0707080b110031300004c41c01c0d0007020000102c042c3c2c0d16004070801c2c2e5080207544003c00c02c0004181c2c056990480c1500c6c0075035106a5043c003400c0084030040d5050b80400030810607640100300811401e01d01402041822500382c803010728214440795810802d038084401005460303818003070340f4a2800405c01400841d0380d82181c18004003034082207580f041d050100440c485581f0903104003c0d547e448400c6030349440d500d2801075211140040300d20088003030f1101d1100b44081020005100e054161241a5088280503031007000380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 480038471 1250 480037221 480037241
    0x50603180a0519020120070e0c070206190e06070c090908070f0308040320030f0a0e0312040609050d02130e101a0411040b04060c06290f030718 63
    0x401004040c0c03000c10000e2010040340c0d10b4038000300000f040c0c0d902c0010452621095843c03c03034980b07200700a5120401285080869960400101d400e840741c807031083c00c9105100000b948501f000a0003103d070364411401910b0040c480d20303041c0e01c003c1c3d14024807080b449804001003590022100c18059006242c0c001108a40200d44a6003410304641e50030000a0390714406a0100e20740e01e0400c0304055000701214111409005188445030100e280303143d417805468135491050b080400c10b01182445061290711805005003214200d540054104416900c60302400c03000658949021034681001918a2019940a05007020004104074580003c1c4400e04030700540380544034003a60082103600540003001980035040c10200c000204103c211183c1d5844540d46075400d010030008218220207443c11114a07040807034140300360b4500000280f6074481040204c42e0701011801c034400c0b040f0410f0005010564000c02d20948220815940d4205e910400b090300c070300204c05031148207681c1c00ca01c0c040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 480039721 1250 480038471 480038473
    0x20102071e0f0e04061b020304032003012c1606050d0908040f06120504110d0609060f0507030f0b0306180c0a15170c190e0409050c0a0602010605060318 67
    0x70780c0751400750b1994091988244101c141c030b98188001c1c072076548942d490603210101d004c105000101e00183d1240950300c0040e003200344400210f80f6400c54507200382e40c01c0c00e00800800c01c503005554102c00081e01e0105121081881c1d4420344009000068400000381084a070000b0345072800f401151646c0c0306800e006500c0d80c5807050034002455410152004d00b11212034a0443c5041ca9002404885080d80804401d0304102c140400308520358090180110240c50f034120103189418040702a0450704402042c4134640000041c84800e00c1e4081c4e809100709607012700ca82d28100043c442601e030481d003501c2c2d1682050001c07034880d881d40c8441e6103040c0c08000544000c2415000040d081c0c1d00640d0108902c2120340d00c1c1400a580c2c0440d401044668041c02c46049081100c2c20301c1a41c007901c0102e0603152041d2142248540c01908410420071000f8001d04c0b001d042032504648031212000b400d03006680860001c9074060060044005450001d4121800e50361807100e441907505440c4512422 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 480040971 1250 480039721 480039779
    0x60c010b122a150c0f0109080a0e010c0c05040507020f0a0b04021f0f05030a0f09060501050906060406080115031404030915090803160c05060a050405030c0901150c06240e010605040302010207 84
    0x4071702400c0c0290150280101c1125032a0020080301421358010b0490300350400c005180b86000185080030900305454003940c0c00210350759500e0050785030840b611907003490303032041c0800c01d001c200082c0f6106100398403d690300e40750b0000036140d02c40d01c1c4007071036107280c00320303172a4240180c4051141c3c0196901100d0402c000c50171124642048080b602240c00c29110946c5900c01800281003442d100c0e90000d10070f54015113000d1619000400210341030251480700b940c0c10740c203c1c00d5a44282c0080d83c03840001809407000d41064039016214a000384104400a01810744510704a8000c0c01010105c40b8290003543c03174000113240080c84061000411111008000b1b40031403203890303540203098520500d8503295a103038101400c05284c10090f00880d44070300c905d04018440d0540ca403440300c83c11312081c1400b0080e4546450300002524040700c1103200a004400c8601030009106256800c482c083c103135490580e6200c0a040758030348290300002e40560b000c0c8008014450400c0c80b50048842c440325103400d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 480042221 1250 480040971 480040993
    0x101b08040201050d020f130b0415030504031416061d120c0a0506090618120a05070203071a070308011505120411060706060e13030905060c010b122a150c 67
    0x2040703821401041d1046d00000c2440c2280d1003e40e0f08020280c000c821010381807d180601d604001e4806c8026981015101c40202d401c02d80a8001101140503e4408648684580146803201c1d400700301c041d5515410030900300c054640b503588481c500c164440180a5074014001003420355884868000c40510800e410764003c10b00c2403000c14010100c0001074070507420000d42c0c40303602201143c207400f00b80e044407107440108080841180e5140c00d4a04001c0c1d15043d0500001e4203010036644040c0c15004801503105490048400805100e4400d40b24150b483e602c070405903203500300f451401008607000b0001c91000c0e481484a082e070051207046001c1051915201282090708040d104542e031649840303090140480c0e1129650f4055040c61103441c0c5e190107501c0c0100903404612581740a1500010043c00c00d141c02e40084500c00e1002d40010810120483c04c1c07903603415881203c1850703458100c0590f2050030345101000e0710750b030001d0100703041c0110f50101c42c19a500c0240c4285513481001c0c6618 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 480043471 1250 480042221 480042247
    0x71208120f06150a0914040b090703021b0a0206070605130512040f090e0709020d0207020d2003060f06011b0f0c060e0f030304030809030102042402101b0804020105 72
    0x6208a000034544040790404200748038204101c02c5030030031a040180603072a90103034010f41810803140c05461080310810404080b0b40188120403195810201c01000c2115070f5825400520724503d0401800d05502000c54000d0707103802e99000004d5015808221400110b041ca800a64000009480c1c100124071142d4440e440c00c507110b80c035980d00740e101103003c0014148100311322000303000130341003800301659551031a92104110f0103100000c80c0c0c049028102001c156064543e482e5000d0706171100d8143c2c6041030500d0f08605000d41400c18649007124810303040201e80c260065045055120a6483d402c00542d214030341d2125003940304d01c84201000c00314010384003440c8054064004c51000c5802e000e00141090444626180209203071348948005440003c03c442c101d80c1c01480b000d40710141e0ba00085c1c00381c4556409200c124500c91981c40e0303200d4401000c690b55420315002c40f00d103806222000c00545034980c0e0182c228a100c4048a01d80b0f5002d100b00d00c1d071040c41494002d142501f0940b00d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 480044721 1250 480043471 480043507
    0x5030d0c29090c13061202010c031211070c050619050c0a060c120b030f0a060e01021603050a110a02010e040b03101b090e060916021606051c0e071208 66
    0x2d20320b15030100440c203086043c050040404520b2042007486040c4c00d08802035052842e00303030001d0401407098101030034548a40655640c0d41e03201d4406005c0d4888503400711119411900c800d031187d01c0072072800195454110308683e042251080c8000d8000d01080c0b00380c52980008500c00c2c40c60240c190f908002400e40e1040c1e03c0c1d60007803925035000c1420402141c0b0112140710090b02c2c000e5003e440040c001c0100010395100c2280c0c00b080104051445c10a01c40c060300400d17001c00c0d9101c440081003c2010780010240c5402d1140360744482606540c1020503540da1952400a13010039050b01ca1005a8149500b00c0402c0079800b43c100e50703110001c080c0900440c0c256102400b14108444203181009a010944400810811180520341d04284c40001d540d52000382c4501c00784503000c015400c0460003808200700640c1e85184000c0d28641d1024042d220780d100b4040350210041c005900300b600341c00c40c4070311510507949400500c403807420007101d116400d064142c181c4a00301d092000d002000300410403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 480045971 1250 480044721 480044731
    0x60109020a030e15061c05061510081603091e0305091201051b0901020708060f0109110c0d050309101d2109041d030d05090705030d0c29 60
    0x141d40380035000c801001c0ba044481042c0c441e070805414511502e0100c1c0e04075070040c0c4101d61079608486404011410342110b04002840741c00b0301000c000c0c0c400007102d803c0002031420394203178a0000070000101d43c0c03880100d030720070188507500010050041c4242d006819480c80781c61003141d10b85262000d840d00811039041140010400203c00d503050401c800d40925640317480c80280100e00341901311115840c1d00072540f6080a00100320301400368800c110000060105c20f040c2d81a609200c2e101082d480003d0080c0140345090070010700c0e84038180320403190a0541480a880900000e6034111034541c0b028213034102910406143c060b10403424815000b03030210040b40310f40c4905442e060a8100305100c880c0d08043c4204400c0304102a803500304441503201d04640001d80d0380d254000b44000381d011180c4440c41d031302c00880d00407142240b031342c031031409030b271054045071340d1070342c5d5442016610344213030402d0000074003450f12410000303a40d00c3c68888060701207802d08000d03010b490f41d014010304045503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 480047221 1250 480045971 480045989
    0xb030a061e05090a090206270316030803070807120608030705010f02090a030b1b0a0c03090b0301180f0207060c09030b0106090e04020f041e06050a0b031b07050a050601 74
    0x5081044401071420004491040c400000d102031414000401290000300070085968480704800219130301d65048441011081c1c2c481c004031113810902003408040411603a01901c030381c5140b008100460140d039000c90f41d208660524503a0b0b80310301201c24010140280c400c0c08000d4024004115581c0174017405880380600541e2100d082c1d0518038203444034654494500c600c1001080240c3c0c41c0c424000003a241c004c450119903844600c80e0000b020141c025841d0781820100e0420003555010389056520f6019903030321200980c850f114003e2038802881b5050562840d00801032200700e10390030800c1e0180c0f00c0000181000c0d0f05032160002d4444500e1410001072002406004102c071741064940505820710b42042a00e0420388480350064024202038800d030b00360180760300981d54a40140d210050b050b6000072441c2581e10210014150070700800d8031444000c0ca0108080c0250800e40b4401d42c101d0240c5042000c1c4503000380c21a91043c40d00b520036000308070740c090206504100c0c1c14020010700f4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 480048471 1250 480047221 480047231
    0x901032012010b04060206040f05150705070b0f01050f19050303120702060c070f03080c36010c020603130203070b04080c0a05100e010f1803300f0507020103060b030a 73
    0x340660224141c00030f0420031024441400300503800074a66512a0f48000e40324144440780c18241d182c001d44000c07104420402c4410410815444001b42101c1c1c0d1103200300f0840c030784a10050580802c0c090041d55048900d4890036a05441c01814003e5540d1440d0440b0644c0b54580000c207046521500c0603086842060041c446261390401405500040505080f4206000c0e83d4428840099540001c3c08211548012407101c641d104221030345120007804002e00138040c0041d600c04001d4560b4038038141c5d220228040340c00e50040302c1e45001c0a0b4000d2a0700d15541d182010130460240e091410b0307816120b4890b022a002c14240000c0000d00b6492000300034040c00142004584442600507500444844c540b03501c00d540c20a10840c80c1c1c41c002d09210448200b0715104a8000400300044048044140400418400c0206a40d0f4401c400c00352501001010070480100540c1c545800314000b03030700319000358800c0f48958040c00c18284149404a6001e40d40c0220480c80d41040d03500c1d920442e030390 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 480049721 1250 480048471 480048487
    0x102070308060312090d0c0e13050d0207061e020717030903160b2a07060e040b01080c0703050304080f0a0201052a04090906020906070b040c0506030c0d0209010320 72
    0x101500c1903008500700c0050051040f00c3e132035140540540d8113124054140140c0a40800c030340c022003a0050860001d0403200c030b291014141030091403081c015105030003295801034906101040140c140c0d06140c54082c1105100d41102d01d0b4040359508040442c0150030010410b45544102200c1410a110055484003081002c1600b42000b80c10340002c440c000751010041041d030b00382a1148460915a018880040c449000b682102c8240f550507490042e20800f150540c0c00c4140c5044046003078030300f00400c10303101c40107485100c81541c40002001e010320500000030f120384010360b406449403020500344420030340440c456400001c120b4016035100e00c10450007100003c10515032481002c0020760020101c10100440d204600620051a850701070000c14000e081d011108a01e1024004655888090810028040c002d0300c04071800c5102c01400151031500d101a00c0c000e00342c038140c4e070385803169062a10009512117244a4141900c0d1031814404003880c5100481030714041403c207640b4024 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 480050971 1250 480049721 480049727
    0x403060228090501080c030402010201090b010605070c050405060619020102071719180527150907050909060f040f09030503070e0303181014130f050d05060f131401020703 75
    0x14040ca0707001005041201048581e034000711341a0407440e81e034400e541e02d868600040303001d0400c80e60060700d480c2d4104000240303154824010301c01c0b54040c49036065141c0e103d82c1088150380064031b4040d81300c0c0c81400b414108860351144070b11f000900740001031409283d5a1102c6c800031302c420391170341c80714804148000b46d48542c40b802104c01c8614a02204560203403000f1100200d0b040c002e490003003000b030182105841544400041d0982403103004412403400030200844800c0041e8000c0c01000c0c68004105e90b903000d8010313240d032444000d200500c560f4580090016032903451032441e40c41915020b91000b003150b244a4002940d01035500c050380c80c5840f04e00a4801e801e004840e0b8020b0740100441e00d1700d01403c2c1043c050b0058100c4070200c8403040080111030021307051005840c243c0001a4000450491200d000110381500100800c43c1c0d40d10300c2000740e00f0340c0f41c6401510b203411030700c00100c2004054044551005856800001c42c2040e500c40c10207004143c0c01d0803000380e500103141800c3c160 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 480052221 1250 480050971 480051037
    0x90513020136231302030c1606020c0d0f08010905131a0603060121120507150603021804211e02030d050a0203060102100b180702030319060f06110304030602 69
    0x48940010701241003180041041c04c0004d4802d038040b1a80407004c151080480d101700c034040c0003110b0100a8542d86800d02100035800520b0f0341c4c1c0b280c071030100c510391f4060040d0107000403c0c0c510b45612180e030b072815060b50081e05000b800f08880b24400c20141c0002120700a00418401100c080c1c5251881c245041c145007007010f030065440c0006503c68010f500158011400441c0d42c006528052401040400c1d100c1c0d0050450081c1035211000340511131041961015003104d000300c4080720044100d00c00140b500310248d03000341c00e001c0003041d0b400201b00c2d01c2c06070510170825440c281b081c80c050080241034519215680c80b0050b00001088011040140111a0010184017045166050000020b503988240302c00102d00d55441d0656690030b5910034505954400040150418911700210025120392045074074001181070404000c1d80e1400501c07400040c0d8290051034010365050220649402c1036002d400302180c4030400c4040001401070019080305482041800c8401c01c4c80e0360b585420716 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 480053471 1250 480052221 480052259
    0x220b0307080426070305090402070b1f09020a09031211011d0f1c1b050102070f06050906010312121d072405030a09020334090513020136 60
    0x503124400f440300400d50070202c90b111681070404903520681080403c02134058a040034007001690020445034620f5641460a1140c20448610300d181d1514184000c90103074281d0b500000b84651414000107444044420114041342040c64a03141c2080c3d0300781c252611a1408044040901c0001c0110361040111042c00010400500080000d0405500880e058a108401049800320508840d952035138481034421360440c1c0259552915414003a952020021301185d01030324000001e007850b01d01150035070603641c0c81202c1002d200c002c0c00c4100d640501400580c0d00701a0790741000c460981c42c4000464410b058500600102031070720614520311003855051809e00355504109882e81607010080b241e000c07100700c60002c0e8000150000c01d180400011001c01b5802c004904803515402c052603582c40e50390880d00c070181040d11015020b00380d54061782c03460312805200c2900c134010340c01891001d500d0151410f0089501900c1c05598008218810000f60120007192040c007400b40700005520080e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 480054721 1250 480053471 480053513
    0x30309150901020d1e03020f160303020307080a05090a0611090307080a0b0c07050304120303140717090307030c02120a0b15010f050309030702040906020d0609050a0c0e0303220b03070804 82
    0x43c16914115603100680d010b05c40201580000d0303110403141820f096904280a01082003203101107032501500035401510070202051200000a00ba02e4003070081900c1901084050a00700d0b20030359610300a40308080384a05e5441041c072184074540c40130800b80307005007400c0b401001402441c1c103101c554608003404844d40e4100400c41c04011540c00012030702120305448040c8c44c030302c0301c0d402c04500a012000d000a028280d48060040403680302204490659101003c03c0341d90300c0344112650b4a115000c4000c0c0803992008801c03000d480c18103c0042c1e144112003c1e20091605541d407045254411922807220780114101495156130012400007100043e003025840c60400114032a0349000701d070b200910031519a5002d104000030303a0103554034500b0700c0c0b205120660325003003464043c1400325182c1410034a440d009074100c43c03040003d0358854001801071840c200c1d0458201032054808580001c090825000014090742968000d52003500b850f0b071882c00c282000d1034040c0000b040d8800341c0c4c0d29 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 480055971 1250 480054721 480054737
    0xd060e01090b0a1a070b0a02090112020913020304020f0306130b060a05010903080703030e071202040b0d020109060c0f1709010f0815010c1505090102040e07020a03140702030309150901020d 83
    0x2072900d07100f4140c8240e5103a400507442c1c00c182050300010501c01c03540700508040f1090140300000400760042c0c0b112103400d882d6031550b52800c03101c91003203016400c00568080340100400c0b16074002640250341103400500752810021807100401d15042c3c060750100c1c00c0c6152070110030b081c03000b0b10b1900d50f0400003c4030306580151074a0300080c80c1e8481804003514141c400610401094000d510858030001498245c074411030361303032458081484442c2001c4c3c1c003072030500c1086071091401c052460680b0f40e050b10b4200e07984d8213100041340d101c0220f00088800f41911010780022a1507011002e0301410720480b0555242c8145000601010071a1942c4c8140101c1400b8401507034100c004100e44c1c1c840070301e0403a805000c00e0400c1c01000c1d24201089401d2494102030104c1d4800640060065030540e001d60805034886901c00ca988022082000d00002c1e50300511128000048004001441c0018200ea09000200300000c114888800300d2016004000500300d0311ba50301804821a50061402c240c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 480057221 1250 480055971 480055991
    0x50d030c12081006050c0c030703200a030b0f06030313030c060e1e01030e07050405090a05010608070b0307030b13140412030624030e0712030e0a180b03120d060e0109 73
    0xd0343d0903c0c0c02902c003030100120344100ea840080241d0b040340380b001021130700e00c1703a80c074108405542000e8413034100d522551481403401d07040c00304100b01100d40c0062900380e19500c95042d0807802134050140d65060200b085116140012484102d01031400303518520030091030700b540a000303204500841405144070b111006402505216000e650f6803082c20003241001a80c0c440b54102403d0342c20441d480361410701030002c00703800003801d2043c052041c00204070661300c1d0721500e60780c2d00c01803164a12107402000080c00a620075004000c03036000150212800064400c840401d80c0c41c6070f032103c100100d4107003c00c8144071818500080f22001401c08025003418040704280d40a1290501e070001284101c0e0320410078401c0c4c0c017058a00322440c040d11403030b584038820032201910b503d1040e40007440c4409400e0240c034000220394100d900580d00d040301c0204680c008030203003010740b00da650b25005410542c80035030070600083c101d20140b120b0018105080464501c104c03081a0800e403405c9180c006006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 480058471 1250 480057221 480057241
    0x5041e1a0a0c0f08191a040c090e042a12020a05090c1b07051810061b060507030b0307090e010e0c090c0310350a03020601140a050d030c1208 62
    0x74801d4080c90f010b1055990441180c2c1724900009011170319a240c983c41008a0710303501c1000e81400d9044400340000912160704450722002030040b140d03e2070000300030400196a5000601101086a0621210b140c000c000d1400e43c3e070f6182e010000302c203c2d4401910841c5040c80011001e00800c83d404d6034035003065011210315000342011010f01500c1b5004070109454104580c0c03004005c0200f8640000c2d400500c0c3c2010900c00351000640141040000b0500034040c54000d441e52016900300500050561112809004040d11940a055441302410f64a480c03d004003000340001c000d002c160380c6a058029030031280b1101054455030842182e81409903150700da02900590806181c80d240e4442062180c01c0230603580c0812000d00b03000e11490399006000302c00034125200300e03043c83c001680c403010041d180d402c2e00300002c0068002e400148044420503040500000d005803402040c16103c0c00410241100f003c0160085444001d082040090b146e03006c2010740a149001e80982c1400101c1d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 480059721 1250 480058471 480058487
    0x10501060504090e0703020a0609051e0d020d110306010b040501020d140a031508070e010504060e07020604021309022706101202030a2903070506130905041e1a0a0c 72
    0x440c03c002c0e10703001e41c0326a0507000c004640c09550001c2c40e5040b02550b4030406030014105224080c01400f55841d485403040f4008403001c1050800340c00c20710345081c0c503820071203803603507034002110740168010440d80c0c207032030401107540a0140c11001aa640c2c1c00e00380068a4040019109010442209411100c0440c3c00c03054071403d0505040100d0148000301103104100034940081a0070b105152000031154810040075040381c2064900302710013900d840c41700e2007804003200d09802682c444000306005040c09440e00c0c3c09030440b4400010101c96960009614180540540e14803134248a44400186504210160130a00440d04001b0f0102c1c41c0001812017800c00031000c20507036020000640c125801c1d00114042040201d90f5402c0135518000c014000111102942c02442828400320701e5007007800840755048811200d8001c054500300110300075020081040325484016042d0680718911040c0c9038600034030075140c0c041200d82c0c100220000f42c0d002010516501e041804840140360031a41c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 480060971 1250 480059721 480059729
    0x230f011e0204061b0c0815041a0609061203040801090f150c0c1202070b03160e0108070c260309070303030b0d080304120c2906040902030c0607150510080c0102010501060504 76
    0x60f01101178140502c4403501540b001d0300e94040e00900310300740c401d8020602c0c801c504c1140400c0005c03843c036600310b0031180125801600222074802041d490f1030104c80d00c00c81990440201e034641364980c00000e0944100c039104440d240f100078007000810031480c2c040c600100004504203c2d02c80c400ba40145030784440000a4440d40c0188400e1190b00d1090195001510441910b130707030b036810404462402120010740106c000307a148054111950300c00d505441c05600c480c1da03183c84000c13076030b03c981c0892030358502c5405041e041c0321000c7c1c603108100740c040c41c4586090b0028081d0030303155050190546074600c0105115003031a040d00000a030000041e0380c0c1140d001620204241c0c9000c40a8030356030000c41c40076100c4e604400d201c80304041c2c4a007004c0d600000359811803145403208003d220984030364410003076064200c400076454506051000d07026035406107103010510203000300766400701c1d0019991000076100414003030001c070b4803c214084405e1001c0c4000c00407503142c101d00403d203000ea805 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 480062221 1250 480060971 480061007
    0xd050303071d04152306041a040e01090605150c1b0414011511071203050a0c0c08010209100809061501020c060c0c0406060f0507230f011e020406 64
    0x10301248800701c8201e42c95907500010700200f2094000c00450144004188580c40580303000e6a40848100400700040850b920058105c50401d814510f180c0c51003614501c2c603d80d28407003800001010010b4044040c002d089004001464500b800144280001c0310049031010301d10411034040c0240700094071441a1321030140711076100388100c0020b0060300f400c10080090000c0000003180640008001c540a110300b502c58100507120703070304120744504182c492040c4413040c50012002080c05600181030490b118030780855660840d90f03980c52221940c0c1c0000002da94041000c07a11400d0458101170070315218200201e29107400140103654100c0100900b65241d1a400c230041280d00802c020703222807500912207600d1300c01c40d842c1540d1b1800e4221032903106504040000803101d00034000d000d0000b50790ba0702d042c50f10000340c6a02c2c074400c100c41c040002000603108060b0f10486c0074000c48013104010700020a03407011344a803a90205800d0b8102a59440c4100030411840360403011109240309890 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 480063471 1250 480062221 480062237
    0x60411040b03101a0f0a09090804210606090b09060d03030209060f0304020910051f1b030216050901050d03030e030d0216031806050307030902041104060f0e0d05030307 74
    0x10049400740c598400c8480c0c041c800d83d0702c40d07506500903801000e07401100342c4401d1068001e40e020000d00403400401da5821540040c2c05103c501c0040d0401c11400e806850700b80c0c0b409944400c0303000303500c2c0c8080b6068a00c03041e84a40c901081000c0c0070b00340c020405a581445408001800101e0076000a02014803a403406003002c0c007098000d4050380c1c0071110060400707486043d903013079410207503000307c40813817007184070100241281a6102e4040c056030b4000e0104000c10401b0f10038103032012020403400d402c0c0f00a40141052000070f8600010085221364081e080b04c140d40503e55140d05901d404c01032080c82c0800046c0407986a41060140b00b541600d004204011071040ca1800c6206200224403043d00004602880780082d03107410707803003e1007651102c45988040b0f264071a00c0c15a03008500010300c0400c0485c8000d0b100303401c2001401d0008000003504001d506c2c3c40840340c0e0040e40070101040351060000c4007140c008400324820001070310622455107880d0717035240c0c90340b100400c420203000d541c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 480064721 1250 480063471 480063503
    0x1050703021002040902070611030108060c07030e06030a0f1a0f011b080f04030506070c0b06090705130305010501090c18060c0c0b0d020315180103122609070e01080604 74
    0x8200d10700642c01250030840d0b0340c2d40c0b0b48035400c002c3d41c0001c2056451500704420407800340882002c4034126904070024042076164440c1144451340b01080c2030701080780d801038034209603030b800c0011401703a1540e900004003a50001340c82d01c244ca254421709076458400d510003402580702d51400e045980001d00c1c0011190462820104c4a4004801c01a01c0d0003404213035901d040078007800800c2900c2c006d80403510703a555070b40e408445000b07a40790001c1031495120080f41090600307400f12900704846040490501c048003c101e1029455035005940503074450700104010000351251000b03180e020710b8441851204800304807100c0030319200740b50410400f008034405001a1030b20040140170700465242d17a95001e0051203000c1d401c1501c080d203410442e0704007450289880c245440c00d8942c0e42c50b41e81d001c0d81c038586900c1c0301841d00c1d034015024412000c01e03000500d000c12094540074400790181034001c1c00c0c007c110500c0c1c0f40c6903410440c040200e000043c005d0002c0001c01548c0b00754808000c1a00c403200d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 480065971 1250 480064721 480064723
    0xe01030507020f070b042d14060418050f070e0603040803090703140307150626030f0a081005040608030d020d0b060a02060a111c02031806010305100e0c0f0105070302 73
    0x4207030043c40b8a8040c0341c1011030b0140400b130003401110381070104060343c141c1120b420351042c00d03440d031541030880b01014108035030502184444508540240f0380c0341400d6841c1c10070f1401d010100c0e03003000304950b11400c21240e00321850900d6000301d041d1902444e0010000041080c5100c0604090244400803000810f045420803c0c41c01441e4030501c030f202745170f20280e01107589400c50b400844042c400c9000c83e040312000391082e01e0450345400c40c04071403048025856403900b0300601850360f05010400140d082c2840403401020259003d0391955114a00800f81020140701500718901c00c81c1090030410500e000002502c81902da400300050340c500340f91100000415031211507940100300441c0c0c068240d40c010a0240c407500e1041002c1c031803640341c2c40d400503080c890030452840301500035800c50b03c40c1c0940e5016550110344141c503e014001c05284461a18109070b10440d0703107510500500400000c2405008180703681e81005003840c2211000044c1a4415400c1c19810842c010400d40c09142c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 480067221 1250 480065971 480065983
    0x50c03180a0314030c2a120109021203120610050a1803020d0b070e010201090213110c07030f12090f060509061201060504080f060105091b0c060c03040b0603010c0e0103050702 77
    0x361150243c4409010580a030b6100d402602a0702024026285a03040303009003484035850701e240c0714620b078030b43d104280300704407041c2000314200e070f502d40d6181508070050700d480b4200042000c94100854503800d20f49801b9540410082005000300c07009001c4801c15a0442d00740c078a032180d5070604c41141c8130030b4804040300e451035070300107580195024104000c0c80010100703d4001c00c04d90759150025842d41d03005a003602c006000c000d410005051458001078007550201c01b2800010050030300c1d0032400900b0924008654006840416240700080708220748019001311031056130402c039504031b14140c0700256100c0284290000c0c0000000c403500e0640d074010888420b0187c0311070041c0d142d61102002812500a80205612440b41102020f4900800a100350403502c00421913900d550750782c4400d512501d41c011165107822411320042c0b00003581849918442d040001c0891b44078034203402e011500c0d9402400d140d010f0317458003e000da8007903408900998041000c4c20b02003415281c018003286800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 480068471 1250 480067221 480067223
    0x509060603090a051b18040201080705090d200102070f0308040e07120e010617070f05100c0b0708040b060a031a0403090807080307020406082a0411040603090c06050c03180a03 77
    0x102550480400c264081d444000d01a0f01c141c0392200003510001406e180c03400190f0b4064003040d506000141c0d4144160300234010300201802c000d00780c03d004d41c1d039201041c41c1100029201e040e100041c403182d503410465000240501025041540e00d1340e2145421031050313024010000c81ca8100003524240070f01f09a00a18203050300400a054448044070b0003018240203d035804510b15058280000300004c034034081e541c911555004007494130080112144a212981c03052005030005d0a01080b0380b003111500ca00300d01c0d11903174034914245c0b07088800908014020740c401d100f182c0c41840411800d4402004480480181402d5038681d41020f84502a6691108520b440313555000300303103410f02101074044244290703828019039803502207103500c0c1d103c010704805001494210b205141400b9030002c418042e0090000102c0041700078046a8560040d00503001090b10f032611320080100c0f0380003210007081203182042c03d081c20030b02469168842d0358100e403610341c0460800d5000e41c2d03071120040011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 480069721 1250 480068471 480068473
    0x40c03060b04230601080a290f12100608010c0c0f030c02040614040e0118020910210312061514040806011e0602070b0306090403051207030e160509060603090a05 71
    0x1c4003103202c804611030032213016000a180c0d001080b840d43c11400760050600f030620043e10084a005520b90506d40c2c18003400780d00c48640750301a0722544a2042041e4125080d00203030080241c50400309042d43c9080c0d1003146540c1c5002180d121080d40020b4240d8801da10140001c8030381150700b02100c1e00d507e00500a580a49401000283c581d8080341204115030f06880a100206c000c0d1021400ca0b01d142e14140b40d0304445003145001490300c0d5140c6540b000801e908004c00544a9000c034190451010004106c0c6184401311010b050300000401e043c40d119500c24000b0038241410510035041003491101400101e042115400e01c00c5010740340541030080031a103803982c2d212035003c010003801520900b140c0704240c1c0410020b10125108060b01c04030380c1d00c42e1854650409006050800500c15420000280200e6800011032001d81d4020b0110707a50100740b1004410683e818000d803038003000c0320203401140811541d1243e85510354000001c441440d200d03580c0061890518041140080003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 480070971 1250 480069721 480069761
    0x10c020310050702070501171602031b06040b0901021309020307030f020c0c09010509090613020f1f110f07052707080f1605071b050d03030203040501050906040c03060b04 75
    0x40c40c0d80c980c0700b40c0c070441c90f40d4205d90840f80d0351001034402c03480e000c0900107070f981280001100340306460b02402ca40410342c41180e2038525040200f11008c50044186012508a40140424080c06a20554001d90103100840c0341040b0100c00200000c40341c4140c0e100260040001805140070b07500901042c3c0c0b11440540d82c038241000e0716071300c40328500f00c050701c501010000071602c0d0404000d05407088092070006c16298803441d44040c0740c5440601c080364480074440e03081703025495801200c060441d03061040d40e0034126000000c6c0284006000c0055268051110911035800c0001c1c144110391040c5c45103036050080750302e4040c006c0038102070350000d00d0f40030742407060140e8400c05192285c41e94a100ca403c0e6181c000500d01c103400100d10f00c40009105010440101d0640c0c07030391500040400c82501d0f82c90b65202d01207103c0241015064001c60381c044208001d002086c0034072a40600600c000d060503290903501c1d100c0703000080c000034168542d1100c0c280d16984039940700c140340301d0055009a036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 480072221 1250 480070971 480070993
    0x151106070f02190b0901150303080c0f09040f020d0516020c2206060c110d020d110f03010609020d150803031303141b0c030615040f060306020d0b091005030a11010c0203 74
    0x4091003911240c62940c82e100d2201148510300c01f41300d0a40ea030598400551751910f00744401d0b641c000440d00d0002140810101907035076554800d01400d0207041c4009600e4102c158007850440308c005143d07080145000251900c1a0303804224851024000c80da060482e14940281c074103680214400400071503e0710300f01160081e0459059801ca910402507606003042803000d00c00c0c01015124001d400107641c01647c00082c00020140050480282254600340c3d40400068255120341d4007683c4090b074000b070a03c2d5030804078040c801031200440310b8000c03001e2800000a82d41d110081240b421400b420f0300420070144505002001200200300c801c2e00d8a0f00110101c800c0841010412418498100d0300c580e181402300e0500d204d6250341700582c0003480c0020500c8043c080100a000303415580e020302100292007440076255801c1c050400281040035003090200000c40038041682020540f40104200c0c0e80c0050603407003144d44888145002d682e800010b840e181c0180c900203606014505c080d03c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 480073471 1250 480072221 480072233
    0x317090c0d1b24021606080c070203070605040518060f040b1201090b190510060509010513120b06060c0c010c0204060512060a060b0c030702062a07151106070f0219 72
    0x1c0c903507040740d4402000c001c0d80107810b80c2d80399045c25105584c03055101d4200b0109001d408600d0780500c0350030302c1c1450704015900180c10032007545c0005002c40d0011800340000e080081a0080545200c60245020700b0300100242911113481e07003486c400d03a2640040040c5440340c0c0c009403e030b414020000e102380205464401c5284008685041c4080c1c062001141b105c4140e01945001c0d00c036110690800500f45101294643d00001e15a03051042c10082003080b004100c046100030420294402d082c100c1c50b14045071481760150029210302c0d010b008440410300c0126035082c2c0d41030309082403085400e5520214001e04801c1c0c0c0540e41c4522656054002c042d800300721284900680407003000340039200c215000003405808102d240c0e0f58018412100142801d0340204020000b2a00340012400350b072141d840350701010480c400d1a500042c03410050504a61030001c611082400c091401c041e07008142585c6660081c4000700700111000e121030600e00901000a00001d01603841c09210500e060107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 480074721 1250 480073471 480073499
    0x90f040c21030f090e1f0b041712040509011e0521011d07030b09010f02030403020a0b0c1c051005120706020606060f04030b1b040603090317090c0d1b 66
    0x9502240c520021002e100c4d1052003410141d51401c00ba05550380c5600f8828100c0008070454600d00c0b5120000102e00f424110020740300514052240a03001a01d100b400c07810700741c001c4126040300030248018807041d501c4102ca03a05445200c1042007420f6016610b2080780c00306944015002309078001d40082d40c20480f81c0c1a254018844000d018003503401503a5002442111590010f6802100003840011030414015400403c000004107403070090152007822644280e0701100580c0c0325151601c00c1201005070998070030780340c498440c102460503100304020b03000094102100c60b1b451000811003100050448098031000d005021024440b4000719910f42c003034040e080251140c00b002801354904181103da80c400007006123801c00d45141d9841c181c4a001a1540b01e0b104200548242e44550260140004003119a00480d04020300d040243c42c0d48013604041e64444c0101c020010741d1000024031200508007902d520040d400c460910b541030402c010b1000c000200e0103500002c41d00c403a0750742 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 480075971 1250 480074721 480074723
    0x30c0e0a063f120507031e08061014030106030c0c050a0b09071202030309060705070b0a020a14010b03120f04050603090105010312020f07061b05061602060a020405090f040c21 77
    0x2c94010502401202c110501d0000c00411410b40d0020010816100324003411550703100f0b040c170103243c0a20034005000d84100c00c0900c0c00050351541003200c2c2d8605003981c17910300f18450420750b91068106050740d00318401405a6014192105c8540110034420a69200065044020b445903100c081c50002036001c02540c0c503628521070300c0400b2881445500c00c2403150340e4005c00071440e05a01c8014000035411400c002d0780c590141940000e0760041441c020014440072380d01034215a0443e18000d81141042207012003260715052400c84161030000b0b050381b03190840c610540d00c074024414a1119489276400868120345c022040c06141103054025a050324462414180e461000c0c5400701e96074103260844480960000404115442c0985c000585030b109102411000d440c00f5240d4515008082c1e84907004000d180c11103086042e4140b18064001c000b880041d4607083c40e200003da9000c43c040c1480d4114120180441c0c208035101082a009044801c1031022990341c490100d080b41461800c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 480077221 1250 480075971 480076049
    0x20010f05040615050303121017010903021c08062101230903071505090703020411030403020d0203030c18030f0d121515030203130605090d090807030c0e0a06 69
    0x399810fa401e8400a21405441e4050000c3d418011000c00000c84444d000d0400b860b440f034100e0002c268003503c240100e20311180d440001c00c001c01a1300c2c000b8a45030711071042d08030003600d00b074404850990240f501798010b041142e802142e58034401c41e820070403191141d410f07055031900e0003240c02d04016070070700da5030003510782d082551030b540c1c10400303e07100d102e148001007240d4642c0d520710360031007007980c095900801c000703045a400c56100d070f020800710390092031010384411000c02040b0815604012245040304144003031821814071b444012a41c0c084e6050742d00b0412301004030311980d61400c11504c02480006401c40d903201b030540901800072040800022211800c000544103407500101d0b001089444000c0002d50741c07011100101c0c000e4102524122100c00b8002c00003010481900425004901d2100545941500684d010f09001001e600c44240b6030401c5400700080340207100018103c03221001201c646a564042010041c10950848810701400e0140d80d05000c4840c0109403203800107103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 480078471 1250 480077221 480077231
    0x100f27060e070c21200c0301090c05040f060303050a0c020f19031203020307020304050904240218040902090708041b081f0e0a0312060b0301080d0206240120010f050406 74
    0x904d0011902c4403c440400702e0703414480300043c2c1440300c3ca0702444100290036a11501c03030010009081d2045c102c803c1e6060190342c82c0a0041d49014172903d90401541e0340108519481c50f507029003203003e000717080c0d410321941c41d000b50155111840080c0c0b0340c078001059105560300d007419280d80d5415038082034481100358100d583c44303d130180c03089078000c40d06600254205072070603080000f207140c001d10850b094010110b03514241d50302141d00000c4400b0310800503854905c840010300c61301921a0000d4441d40c201900358001d6225901070702d030441c000d460004003d030b8850820380740780ca8446681c20704083d015200050049408944c500740d41c10703450717070621042c2206081401910f682120110760b982140c0b91a10000b400b0380c107080c0403a0140400030990035600c290900080e04240d01041c0c0d0b0fa0068018819610390502007140e001e4200c3c00d1600703140500c1c10050b01d080c54002d8015043c08104204004012000036502c1e68001216000f44a540b03490300c2000042d017801d03201260300c28244 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 480079721 1250 480078471 480078503
    0x140403031b02061b0f030411091f2c07020a020a050f010512071107030309080105010e09030a0f032a0840020405040b100f27060e070c 59
    0x20412001d1858007075004049984510041440001c201220354000301c6041086031400d0740514007030b41c07050b4001c803d0462a41050414030142400041c000b900e103004407003450307601d6480c0410b1801640c07460300821000502d044803045000000130203403240c00580340f08001410340c0c000b403110666442510102d941c00d5647e803c1c0208694017070003c9011600a100c0e614031030401d40c2c000e0764400c1c818581082c404e071102c83d4072030904501d600140c0005800c00001e200703461090144500600d4440140c01c4d0078a40200700310344034000d04aa050400503509212030702c1520036004071800f802c045455101135044d01500d000c030380c11840d406501107254400083c008001120440030000410034413051076054599005003c8041c05451b14170458003c03000d400503031618800c042c0308134410680442c4030b0400715000c0702c0c4044d0740d40c030405403040e0f5100c00b48842c0300442e580715006a030a0f400004ca0802440f08038005d42000d41141c04508507400803c000c0a621110f514060f80c0140f0300140f9000d12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 480080971 1250 480079721 480079751
    0x313060f050c0307030902030109170703030605030a020a0614040f0b040602010b2b02030a202d06070f170307030b040501080601140307031b090e0c0a0509091014040303 74
    0x1190b2956110070203100042c4401d000342c0021030124402800020794500c2030741c4041025001341003a4a0900020900386c0070035070140b2410015001c124001d00041c1e08683c00035040080500560040001c229801c1c14242c40720001d44018280780f0902002042c0c032204044410740040c030a490056080201d030fa00d05041046041a82c0008020001041246151540c0090a1003a012130705803086905d401c01051000840150003041510602c0c480f800140c10003400b5034140f00c0c42c0303042e421248200d004111410405003250b030802d82e2101c1d00e4101d41e00f004c04078942615030140c4440c0781c507820700e0305990800c07004510803902d03500d00b0800208414280800c4841c2405000800c0c0c0c030680043c4031010a842441c60f5440b40107045407280c580700d036a000001f19003a410440da0000c6480309000104031801182000030414009150820400c000544960058425140505055004982e11820601014581701110039051024002d80c0c941956098000c66040c1e0000f460300000d0555210 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 480082221 1250 480080971 480080981
    0x25150302070c1418132f0a1203080703020c0a05060105041107050c060904020c16060906140306040c02010f021602040b0306091f060905010303050c0609030906041e03080313060f 78
    0x24011302103074066030918080002040c8083e141c1e80d9421510184403000642c1452410701e2842c460307803e1645081440300405400392101001c0f803103040f0f030480502042031206a18032095400d840d000071580c8450b102134009105544075801240217100c940070130f010700010b00030304889050700e04000c5200c104440d00e2442c010800000c102d0b4100b0311101030a0301c4c0242c0541640388000700018601210000c211380751241c042c40c20103592401d160100021900a90702000508080c10301d00c00c3c0c401d145590500d6440000d103058800c55550301d0503038015100754044815081c91540c210768840c050142000300c0741802030102d11881c10503240d20f6032030801103082401040f80c0e02c0100410410380c482c00c0c86241c04a1124600241d892000003505000c50080798001c6001351101d65075070040075005414403000a20070b204552003003104413015250001201d0803580040101c103030f105424001da4100340b8050307001420307181011043c40f07403a15000e407080c00b003144107050070000508207071b001d0320079a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 480083471 1250 480082221 480082259
    0x1c050105060405040209062214010201090f1b0801060603060e100602030703050319060308121f180f060602030a09060207061d21030c0c1225150302070c 67
    0x940180b00410050505030080c00001000070186802c0103946981e03504071095146962a1004800c0010030200c3d40c0a060060031120a01c02401540400e40b0b582c00c15403000365000781040481c07442c1140390b500445100c07003d8800c0100a000c4c00e56034001c0100035254500a07620900107030703408207000a840c0c6094900b00d03241c540103941096082d46040c1e03030b160801003014205403400001200082c8880c41110007442c03048a00d991503030281e0151032000300b002003118091182c0c4503409070406241069140c04c50310807202c80c2042c2601d10b10083c0150104440d4000d515013452004a5510f0b004000b60444c10031036603607003525507a21b01049a40701603078402d030300205007091500000000034090300c1101c0c00000d446200d102e02e01054112031406e048013050010303000880d400e6441d40c1e0034080300310562002c175822060020032458030351311814080022101c0c00d19298800441000e00c5c0341e4400100302d0342840410046012a010300613501a4108441c40c1d440f503a00468030b241d0710b0001e81062 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 480084721 1250 480083471 480083479
    0xd051005071d1f08090f1006060e0906030a02100c05010f1a01050a1b080c0307050a03090b0c07050f030a050a050606011812030e0a0f030c09050106020307080f09010e0a0602031c050105 81
    0x4a0741d15010380d844c000181200c1110b005604080f1742c01c11013003103202d11500301c180380090300500d000d00003420b1090100706148203200600500c42903a038001513812140303030100c41c102203452000d4001e49044a0140000f441942040a0408039842580c4182d440450b200044d42d00c20980b800111213601c01c1111031400304034100c810300640c00c00a480305a00710722684080d4908002e440c84245581c010b42d030200c655038424481c0300b0800d036000c04080300804a40104ea42850600d52015898400300c0c0100ca001d828082c6102650f6a0200028040c954000c001e9403101c10460500940b116001c842240c086a011069045140c03010110740e801c0310742c6483e0125255203203560403618520482c0d29940c0c829203140011070a0701560113a00d00443c841d144007000c070743c0b40c500e8400607228143d0251040d500301307100c83d002040340141100d880f20f80c0c13030300901c0e501e4101c0001681c1c1c0e40c8200060707a811210259000c5102c640000041c542e80d082d40c0c102504d10750410030355100740c800034000d83d500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 480085971 1250 480084721 480084769
    0x5210702130c09050a080f07060e030d0309111906030e0d0f0806030109080c07050f03030304122102030106030f050a05151009050405130201110313050d051005071d 72
    0x1801d2940da0002c2040500b510700903022659801c0010041100c98201089a4011240e01c0c4988101003005200900312420f200303182c0d0300030400003a110b4000001450916032142c42281c1007125103500251212001082c1803010614402c043c07451240501601d8007207440d1840042c607500d800030302c9848514881d55201060503d1120844802c50007602f2160075640300c048007030004030488040c00300201151f0041180780c3c81d04041008204014000e14080c0d0010014400459100d160321100c6a1040c14000521840461000c100011f12030708412058400710000c1049a0705070080382d01c10440e910b01340503c0d1a068a044115482500c4100500c100d142c4194140c0c100f0701c01c184100043d13801c14085069803140400c05842040b90f10b21180025000704600f1980c02120b00d01e10440001d0085003407020b4541d604200344030314080c0511451405800100b0403208018503003454000c21010b004d24200607501506590440d200f560403640c0f1040c607425142440d154180070140c00e202c586c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 480087221 1250 480085971 480085999
    0x30115050c0a0f11100e180108060a020304020d0f1109060f0109060e18041202070e010f0b360306070e150310030503071a0c03071709100905210702 65
    0x440108001403c5400a61010304114250396030000417010340c0c01c0751100c1d5035001708101040b56240c0300c00144203050190000521900b000001c032036510000804d00180d40b6100c0d400003c40801810000070015174488402408000c100c4804c0107624100759244001501c2c2c02040050303aa5100c0b41c42800642406030400459100e2046c2c04840c2201822007801004241c0c0207481c10802240c0944203080440e4048003a03580c1084144020480c4c150030b0003540d410071801c4000100355200c4d14094a001050700720000048c14101020072500c9000700d1803540c180034042902140c1803030744520038022880001c0c44d09010300d12829103d00024108080c110260010014942002c2c21710382c2e045240c40300100c002281040103100c000d0003600c441c018a860640e1401e508000208240d052035800d1060013201608a00004032051b402280070650781d9500c00c0b410701c1c0c100340c400c2000442e0b04040241d01844008102030003242c070541d04145182040d100014054030882200035007000104003408c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 480088471 1250 480087221 480087233
    0xb0406080a3005041509050114030c0f0c0607090e06060724060b03190603030906120b09070306030c0b07020109121410060503060f01061e02031e030115050c0a 70
    0xc1c01034041c50103a05480c11400201c285040014403079a0200e48005403d21174003c0e403800c00136070880d107407a14010050806000800e5620f48032070000c11100d000c0046400c0e40350000035224400360448105840d6405006059a03035107050724081d012a08810b4041b814032002804984600e038050640d40c684109a640e160041480d031400d5a543c20b021080e580d500280c0b8000e400c020304804a25503141d00309408005001c207054a41100142c0c03401c032007080080d1f0400b90403c201d41c11801d111140040890380c2e840a0010a0201390748051018104181c0540540c070210969001f1016840c0e05a1180d1075842584540c01019001c02c0900c402040b14000d44a114510244201c481c1d40300400313203081e070301c1c87d200c84080d51201460320b0b40401d00060a04001059125400c000041083e515260003c0c2c140c12103c054003400815440d044e100103402002110100c1445d00100301100202d5070510300c45800078091814000981f0554440390742c820410b0f103001c01d10100140030886400d83d1a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 480089721 1250 480088471 480088493
    0x1801060f060c0510020a080f01151403060103090210050a18080c10020a0f0b1501020a0f02090a09020306010f1a1905130e091b0102030708040317190f030b0406080a 72
    0x12070f20b0348948080d01400800500107000102a00d886800c0b1504100c0380b07034107050704140c2269190100c2e0120b12200d250344181c05105d0040006d068958036260980107c02a08514a0286d04881000b040803d203a9000004007041011641c42c600d83c01805110502c00441d18410100709501089a005151a000d43c0110410f40640115504501140c1d100b080101c070800c0c066070300f04048403c01044095441e5100d07142402403010300142d080c259148244a4005a800f138001c141d483c00180c4000c04651100194540041c01c40c1c82640e0b640c40d03500c000305440d02031924a10040c520404060812606803514000c0107407800e000ca04260b241165150000d1071812281c000302c00c00010205d0701580c11a001e080030801030040040e001d19900703251443c2c52030309e0741154420403010020654010075a0144d980c0700c0c02c5c11815908010100013603001d511100741c2c5100c514003003a408a600314010b0340e0180d0740c45e202400040308500070401269a20721420300c054116000e071000140c0140d1f10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 480090971 1250 480089721 480089723
    0x609030a1709030417070501090611100e031e19020d0801090f110a031401050a051311040306181e0b010603181401091b21030e0303121801060f060c 65
    0x88900302aa00c0100d05034517030702000039401d2604070060a1002d0750b8007001d0b100250100c2e04141094010003103090750f88240e4019035070035143da24186000700010901c00c1351130043e4081400800b00140700550300041d48800c000040080940642c00740e0140007040d1090541440d4640503135680ca031940c900050300410040c005130303590301d074403031400102c6802c0607021000e140d941c0040c0c0048070903001020148103030802c0d40316081c0c5842c2040f017560350262411904800100103d29141c00c0b40f0404201c0c095a0002804a82001102d4045944103a0980d43d001c2c0913800014020002410981c001038070f50901500300c00182005108079400303900b0007180145180e071040c2d404800c586030350003007403810080c1c1c52186c0d45941080c010301c890400003902071170001d80301c0d50001303180c40c0c2c2106010080300030302504000225480400e141c06520810007030070000d03007500d680701c1085000c00d811a0088030013500800c1d01c20b00c2c240d400001403081030159011961040003484c10140300f6126014007400c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 480092221 1250 480090971 480090973
    0x2030319020c150105010f0201060f0506220308190e130507171f14030a0605060a0308130314161a04091407020105131e0206090402070c03050609030a1709 68
    0x202c0604100b00511500d19110080080c02541031030001499001c07084201e00840e0305200060140941e91403540e4100c07403040345d03001e43d41c5440c0d06808503428150360040310300c101c82c0c0724000140b1880a000306034841e40c40da5101550300074480d045c3c910381c80d0b2007540c40d00110b81c0301e500700d00c580300d9034000381d000702070707401c00c0201c00f032020301c100807034650844040e03aa441d501ca0b01c00c0c00c2d2180e400c14210107850b04981039951261403d01107562a154241c3c081c0c034060702c80f00032401c1e07500c4d003035062800f07180c00000d40f5a5440c0ca9489683e580941b600c0701f103605010768070444150324400325051a030280c0791300411410914089540000d07100c5030b0400d120401c0708000026464001d4440c05100c0c245000041e69a407800000103802c4510040c030ba9029211489100000110b90f150803403100f4800030b0042110110302d00205405020308070480d03402c288002000403c0c0030302d5038040c408891050044075055994040b02503201e000394206031740460f00300b0f4162000b13050342008166008942c90 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 480093471 1250 480092221 480092227
    0x90a211208010e0613020904020c0d0f09080c0d03140a0201021e0702060d05060103061809060b0303070b070809191401050c0910030504150627021c020901030603080c070f14010203031902 82
    0x40000b800ca0b401411000c440d5802f0712002040990008409546400c4e50708200c15490701e0400040d0b01d0b44440c40c002c0d0310440c0186202d804141c0604d12084070f0a00241400f42c0700d4003141400381c000c0d40f018071000d00030500e9100743c50110491b441102c000b6075004e02070701d00f800e66159400c4050000039040c14141600c035071000c100c80204440401800c00b40000106500303035141001c3c811508100e00d914005c0d00100107102c00b04003201300f0a034008509127016409a910400da20b418070034503d4070031080348041812581807242c03213901c050600000380003c002030b0f2601c0c1100303034452144080503034201c1200d02004200a000307601050b84203008040d0900f000d070721320041000301c51094200c2c0344404401e82020640c14100c4103180309243d9264404c502e0264641d81403222210541468001e1750b400084540e4980d00c01d03084a0000c0d644090450745a031f07504150251100e2180c001d0208580c42e4680024004ca0841000c158450041c1c01451668540040c5100400c09089241954070f40030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 480094721 1250 480093471 480093487
    0x3021b1c020d0b07030914010204050907080403091d19061404090f0f051515011709101b0f0309080405043207170f0606090a211208010e061302 63
    0x28083c51446000560707000141e446c1140b910f040d002404d102e201015030b01c180030611441d03d864029941014160805400c160340303a1070300f124440130680180c0c0049160b000c0e114006a130155403180188880e0200301c2c05022401840c4003104c108d1701c115410b14544003521400c40c10990300071400c090080c3c0342182101456103825003c003a850004036017591140041c542029840c42c0026002100680c1e05c030b50801c420750000303042292a650340e485000c50036011440b445410031540300c00d54090b03041030000b0100b00700340c00c1d00c1542a50b03125010400c03250000700442c0c40303032003003401352648420142d092904000500008082d10504070749840880c41070f40b0007084030340c500105c6020b015480c0120503c1c101c68020081064001045981c0c1583c406210782504425022580034806403400e60700c450031100000c40390540c603400600d00400c2490b90480c0040c4820703189000c28010003038a00801e403031020855050009100c1c102d071040300040400c90707620f0a100380b89518070945070090300382640 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 480095971 1250 480094721 480094733
    0xa0201021317060709030b150105090405190b0d0c09020309071e05011412040f17072919090f0204020d051f08150a14010803030403021b1c020d 63
    0xc40e41045510780c1c000b20b40a201d00908200daaa4460703141e16140c0d03816840c503a25400c40400140c6094007880300260313400504c1c0d2007107094a061040051040c00741d802d101c4041902038100c40800305115003031030f141c41d00781c0c02c00c60144a1001d50001d28038245510785040d0300c0080d04080c080e403d06011340303100001c420b0500c4406820a91601c90b6000040e85007030000741030a91000702c000032280c0c051104003031110101e0902c6d5805500185102c0c81005140740c28808030350f80303203000c81e4041004140c01060007001000400c25421041c404000403c14449900100c20b080b02d00b14240d0b10b00140403640000300d40c01200280340300d007036400b4401400d98000741c141e07040300c205141000d1340c640410041c2410038240c007103d6102000606842404c1050094030380d120880c40c0400c012040c80810b0009186a02c039040120f9070720880708071541c50b64625501c03640195000d4006201d101e1004200054004044801c0f0300c00a0803041c040c001603c148900a01307103041030303a00a50308036a000101e18 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 480097221 1250 480095971 480096007
    0x501090c0810060609030c060516023f19110a060f030515010e0411070203010608070302133b010e030c0d050301030b06010c0c030804030b060a150e060a020102 70
    0x81d030050069104070001d0750085400341c2d84580c04004030800104089140480d60005072002c6145c0340c1d5403011040c134442d0907030a0041009400c0008454452000c1d2100403e0884070300c154032010007800441814605089a80742031002250001000b070300f00203107420110000396108542d0313020a0180c440000c0c02420f69070744220085000401d410000680c10301c142e070b9204001c021842e0705440c0c0c140000305401a01019140980c0d980e8200c100c030107541030b0568846030760040092001c50744513103450707854000d0b900c400c90140e840c1c1e02c036030500c0c245d49004110644622480f0004c0301049000c02c541440c40358094000e1007400c800c00000c10340030a000700800341d141ca82c02955284810340e032980c41e080380c8020b2441006014001800000d4042983d03c0d0000d400346030260421340503003001005070f640c80d8030042c200c40000a002081058880c0c8a6101c0c030700c00c9845507001036450b20580002041c0a948030f0005000a0700003000c1c0c42c0c0304024081c04a442c2c4001414009a80503100b0015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 480098471 1250 480097221 480097229
    0x3030915010510021005060d06020c070911030c160303020c0a0b01053a1a15090a0501030503120910110903160503120a050708030106110709110a0c0501090c 69
    0x5040040d8004284000c1400c1500400c01500c02618200c407510b002911a207001a980c40e221340c481c00402c0c40b80d500d41003240b0800d504140c046607114084034000d603071101175114001004d4100103940081c040300c0001d60748180c4854404a14108903501c0c106403415130128202d051541c24042e00400d5030b0100120550030348150740000c0d91b94108010003121030300c1d89142100290400c0000c401c0041350019030b1010341190102ca080b5200141f0344650132484c401600c080d0500d03848100001d011510055221400098984540c0c640b6082c0c40c580070399009001c042c019030f01c200300e03403158009110410f0b0382c0040000c09a44040901c03250050030345069080b110840c5002080000c41d524040c07004c50224990740600c44d03046843c0c000402d45a02d1803848644402e000410007101d0f15000c0c0c0d0403184e40301d81c410700b07940c1d9075030b11030801814823009981c0010b003620030100046109415445901590860344a01c5402c00300762940072511070f80d071030f00222542d54031040e10b5400581000721200c00380c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 480099721 1250 480098471 480098473
    0xa121b0b190507050a0c150507021b1504032006031806150306010e071101021b010e0111030a1802061902210405040c1110020a0318021f020f030309 65
    0x250500d032600c1035241012060720100c151420050002c0260403c00b240d000c00c41c02d0030a42d44512050038a00da0901d0780640c0c6a01260820040020302607000c00d1a014008031020403045d03210141080c0080c4400140315540f1040c0200014008102e40b040c44603540850802e8a0a41607049008220542c00941e24105580a045010305080e40c060000b1588540b03c112200c1007500a80000f9554010611550380140004008035801c10300c5664080d0250204800030342d0340710340c4540c0651490911020610655180010300503104c1c0301800b07814161a1240324581c190b40b582034464005201d508158129085070740207038001a22070300f001c0d1503242a15800c225400c108100e010342440440045060065050b0301c4c0310390011103200944043c1d030b4003980c000030400300d0362505403000c801400d001c084d148207152502040c0c1680340c00500ea18003255034180140301c0d07038500f130342c0c1d002c3c169a9000794080a2943c1110440031400c0a80c05905100d20458082003011028a41582e000395000511 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 480100971 1250 480099721 480099743
    0x70c080619050c040b07020d060e07030c120b0a0f0e0106080705210307030e0103060905130320030f0904060b070b010f050a06020c0d051c09080705040e0a121b 70
    0x4a414800c01d403005080c52942030001e07151810b42e164080c0f0550084801c0c102d07012a02c202035468003a02d40d81126401441001401e14030002c5036940c3d50b581c0300444588002c0c1a0220f01001c1c42d80240004651245820f10700e9100c103101c150107031080e10000091640e407492520f403c04000d004041c0146601e20140800905100034400e80da000c0d800d4604400c00051508501000000111011140c05140c031000704510b201c0120701401041d031202c2c010740c0c2028140310035040840a0600160306c203807150390640c078803101c851840341280354403603449030418803c294808041d8001040281801000050b007182c07581c2100e500b43d00074030760548148480310014019160030742e40070303c0505000c44130040b9803440c01c1c1c402965a070a544901c3e0095003040c12050400c2400c00420001c60218047e40800700e410b0080105550030382e104451042c415420006440c1c14548600e00c240e1400c240a81009240d6480ba2900c0d109600142820004021000c0d030520748070304688881c0314886e40850803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 480102221 1250 480100971 480100981
    0x6060703050901031d0a1b080d0504060309020105090909010b0405180d0809031e040f05030c0907110f010606030b1305040b0c0c070906030309050f010906051b0111070303020c1c0f030b030102070c0806 88
    0x1002000d01d402c880623603808450003803c401e81000c1968201c40e038a140104800200b0310049442c0e01682e03080030b800c008800140311102006421603004c03107409480401060707445000e00c01d108081d1040d1510700b50060340d803115034030f44100704a940c4069010105c0b441d0079107001c0c084500341540d070650318100801180c1070020f061007401c00300041c581180148046402c2c04001050450081d005009003d2151004460000103002e0050f0190b0308000801900b0740e1134030007074060f01c003003080644a04600444400305401d1880303114042c0703410449507065a40d4000955140d6030104201e47d00d503104018001601e440700e0b00a02003e1403007a0380d00c2266038030702814031138200d13003011203941417007044407080c40130399840700540e0b100a070702441c40d28403001d1281e0b50600514a0007507402038690b0010350f80c000d143d055001003100010040488080321059540406c074014429800c0002441104102c20704500c02c1d00101103200000703000514280027682c1e403c52030381c100d51001182e074104008002c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 480103471 1250 480102221 480102263
    0x60e240d0f210f031a0307031101030605030114040f0213060b0a0807030203090d0e01030e0a08070b0709140906040b0d0f0b07020c0112091a13050606060703050901031d0a 75
    0xd102d00b070030310740d940800c82c401001800c107107403061945081540e01c204a4000f12482d24500c1c1e0ba0301e90260668400b103031207081c1010010200184517002c281450400a010f0805114140c10b490b00d944402002e9203541e92202d600d403101c500182c3e8084070082c031520703041285208280007442d024400e03968440d0810b50280004500802813020f1610601c1044028000071458480c509214070f04558081e01200058004044810070f0f1480ba1090160392010800c0e040c00615242d8010400b142e00703591555421600c109150243c101050f1000443c4542428415200d0b0380101c8000c002040d0603900300d000c41d01c2000e04210981e440240106104148111249940c1c1c0054992010f40340c0e0090000000c0d045044a80c1a5400c060f034075481b0505111a4407911240d0b03080d40c00300e81d1b0302400c05001c2c41c1d20102504000f503505005140204010b03141c80d00458001e15415151f03035041c5421140154010441481240780000081c00ba001d141da00500980c3c0c81a0f205540e20301040703498a4003d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 480104721 1250 480103471 480103493
    0xa030507050427020c1213090e030d020306040f090f121d060f0c01021b2401050f010207180213080309090c030a09050304180b04060e240d0f 62
    0x410144002040306200700c040f20f2204400b80a42c240080c802e0402c40201d0100030304c640911784205008080041c204003402d0001084094042c2c0c01c40f001d101c2d190900300c0100c3c2c10204104085a1041004802103141c94018550044000b000021405610000441507500048048070f103101451101c1e001c20500016031801001e81d40b40420404241c0714044003032010f5901341500c00c0e940480c08041012101d02260003000406000f03540b00d2054015004200c91a440054410b0003410609c406103280048008441c0c90040803d00b01a46480c06004203c0891213950b81140512400460052810000c85c410b0065503440165030f40d98650300b2031b03504841a00041c00782d400c1044500300d50799540c0801900103011048450360780e1101d20483e03000700300d4604010068040884c0004020042c0714140c50b40500e903110610450503007034200002c40e22940911000c100b44031010601c90104024000700c003060304c140210480c00004000f90080501101c102d0300c4d900e0400ba841b040008078180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 480105971 1250 480104721 480104731
    0xe0d0c0618020603060103020d271505060303090f1807200a15020a0c2a0806160e01030f0608030304060b1002030703080c0d09050105061203040f090203060f060406050a0305 76
    0x1549a15021036000490f01c0c0b1010349054109600840c1c0d88100d131070305500544009403078a0303100540c10009401c195090315504002e03a5468207460001080400c50300030f07240328000050103145054000c500b000904218894410781100e040c4403500c5154546a60a5000e0022070320794544090a6410241c0040c292038512000ca820800b030900000790062022911540300308005a00d40c0c0494804840084a4080c0900a0510b03140d01c41242c900303024512424036000510f102c5181d80f07501c150382d5074540640c1d014103114048140d403010a446000710754001041494042030f100b81a1508005480e5260071955440e04000184001c000c214414001d0b10b270029aa641031043c85200007135128001c0207005000d204810001901c0304c400c4804841c9641c1c4000c40030415034804c1d0800d1030080c070301210100c0c02100a070701e808000780130000540b411218001540c00580382030100b10786c0030303401c05424180c000382000c0503035446a07030b044003500142c42345943e0144c0700c48203654001c3c1665000f400c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 480107221 1250 480105971 480106001
    0x15030b01050d08040b03090c0f031506130e03030f0405010612081b0c04020c071e061b0302010f05071125031e05030c060718030c030b090f0607020106050306010b040e07120e0d0c06 79
    0x54be281e07085440000081d840403084413403164828258400c68080e0400b0100300301c16020002c1000000280d510f03c4a0003540907100030032440b07840382c006400285404601170072648052110040c80440305201140c03070011001074819003041e080201d03080e80c100307101e080d465070060324060000e010b4810100301d00f0503e081e090000c4503c0d0230030282c440600c0708030030003640c043c05c0040b074240760003500502d500a011003401c2240746030010b401070059100408d810221f00a00d0380b03080d0702114850344120481c91100a80440a2860361346c0c4110140c0f00d0b01d41e00c5c440c200321034200003141c0b050010b809540030f040301601107894421401070108080825036100045034803814004500b80e8030528058942c000c0e00421031742c07203800310a85020880d21414040748680c900708208194103400020499500391308482c0d01c0e0340c0303c00030400e1a0146015034a91350224600142e4807034480c00c0380a0641800010009500c034401c41b05a0130000140e0400d4046400c03004050100030b20391203424517180b80c0365 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 480108471 1250 480107221 480107233
    0x8070503160506340f150605011d010c170309060a090f02060304052a0414090c040506060705030d0506011103091518040e0a020415030b01050d08040b03090c0f03 71
    0x240c0012640e00403251110250791500e00304c1070300742038540b804618403040302c09a030902408502d850380d02071584000c22113012903012220f0014080500542c01a940140c4500e010000f038825040768500008151a04000c1c20070f5100c40403901040422100300f40318034102e0307036030b00d0310540c070b20720b406000f40004400310310300b180e0300c0d0200b0005402000d03065030486266503292642c1c10308903e000000ea8454000304008000000740101c01700c101912182c099500b880034401d0020401c002a40444042219400c0700714419a0391500ea80082d0344000020a42400c201c003035140c8926540011800703080c031959aa0030b01c603c9680114a828100d00218000d618252a0348040f480d414014000303404c21a20100c0e4210b6512020500c8910398034000d0b1041024403405d102242e61202018001e9015600c0d21200007801c4d00081001e80681381c10800403a12071346044c080c046402c42c800d03010303166110148400308141c0f5401004502900000001349011414482042801e80031f101c4800c0c4aa4001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 480109721 1250 480108471 480108479
    0xb09060111030a0302130b0309101803080c1e1308070506160b06031213051008010305150a02130603050405300309030906070506070806100c0210090503070807050316 73
    0x200c500c016081d10b00961244110507000b92800d825402000b10f80c00c02102700101032000050b448141754241005100d4007004450404500206290240c00940d021000440b010346500080074034107a03034541d0303258005110074425400e4100500126103402d03038040c1002040c0c0708121102c040c0401300d42c41e915282c4074103e0281c030700c5560782008080042400000342035580070311610004402070500c407a91a5041e0040312104580c5025461003003003060704268103103101e008518180e030f6100700180181c200e0408400324928005001d4811190208102c5c1200d84200003010000e102c02d45000c82c02c0d0070a46080b50500c113140c50030200360a01c092213001000b22600c0300311103d92a1150382039070f9403591010141507100b003003c2c0c0354000f04002544001c0003400608144215801e9030f0b0b44200da1100402c1007403220f50b15111100180000a6031400340c504080300310030800c01e07400c01421280d5a5004641040115803040c505500102801c00c1542000c0c42590080310020621000346810 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 480110971 1250 480109721 480109723
    0x30b0f0a1802370306361b03080d0b01080609130302070e1608090102090f131509020a110105161b05031303150203040f0303020d02070212010b09060111 67
    0x188801a00c00e92102c00350440d60030380254140303040c101c0e592100e000f507030000006100c0c41080d03120407502c0900d4600425101460720400b51852000004140341a840111703a05105105104040d94403600d04001d0948040700000c502c00290b108801c02a01c2c2c00161112404807000d018403d814000300c0400c00c10143e4880d91480d80c03100318110041000c141d2820103d1030100b26400070800d0407c0102070151007070310707403d0070203641c15a951400a01c0d42c90340707001070a038094074011941251303861000c5030640c0380c0700b164043d015400c01c00004c0c8441d082003690100d942d03298400c03000035900084450505901101c040d022101c404000d004500300340904400f6076a461070440200050150418107600e050b0079a0001c454015080303949400454542c035014503010300c02100c0807459030503c1c02d40c08006000b5203104035000945000c088140e600c2c1038029503c81410b80c028694200490001a91076034000c1d5000c100300d03400000c640004200b0704c101003002800e4241840304802c40746201c244 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 480112221 1250 480110971 480111011
    0x1029090f010306020a0203071b17031e0f070204020a270302090f07031e0b0f010c050d030507050903010e160b0712050d060909030f02060c0c0307021e0a030b0f0a 71
    0x43e0068006a0317540c00e0b6402242907008040c0c004000c40741b0841e424142d99071440401041e6104e4583d0059060580480b40759240308000000d942c0d0081014040170310b00d04400a846807968a031050703450605154000b0301268010b01961000c5100c0304950b1405d520003503841e0b4082d80408945920107810746e000607841c508001c0941e41100b174803000186000d40301c1d400560040e03542031740201910300c0000c1204050504c01d0410360040407000080140c0d981318030f410942041e0094054018034140d800102e015082c003c1003401404020481c8402d00c0d10244154408096440050000f80344002d144404072107140c1d22421101d00140500382c04070340010b011040c42c0103d410410f5580b0020400c28000c0d10b0154404140686081c00440c181600207103600000d40c50796080d00c80031ba032100c020042a0003103042c19600c0794828400900142010301689054241c100300c000821100800019682d44054204880f0050103130288195640d111a0103500b210a542007813104410b89010703010107807 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 480113471 1250 480112221 480112223
    0xd03050a090206120906072c0f06030c07060b15160c0503061f052416061b02060711071a040f0f030c0602060f0a0b040e011a03210f03091029090f0103 66
    0x11810b10406a480d0f03500e89c04c0b14021030300900800d0712490b0038000301e410358121240a403000381c00c0280c4180a458006802161101e008501d0380c101403001d884d5404009070383c3c20464035800e80300310105961ba0304124842c82156a840000c10005081c091403c902005a2100e40284210700c42c0ea0704c0c0045000902418501c40d01940d0385503807031f508142c41110102400502040d1610340c05d940c0c84141000100803c0d07034282c00b280c0042d1103540003100c919482a602c00d509411400d1706001c25901d033b80644000d05800c90800d803c141e01c40500004036040c55001301d5022501404c100204941981c14500800b8140043c115518282e600f0300c0390300714010440403806130703924880849507880d1352280800840703001c020046010101c00e11f8004030b24688071070307120388120200b074410310b0041501d0710b100d15101c040103400c20000380c00c81d00d41c2e60005844400c4030b029550f02c4c214805180d01c40e0066044d000121a102c042e802c3e1080d030f1301d4902c448889070054003400100003500381801c407418112 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 480114721 1250 480113471 480113537
    0x4060803120c0c1e060402090708060f090a020c0709050114090114130906090f0605010b0a020a14030c1506011404060e10030605131413050d03050a09020612090607 72
    0x3038404281d01c207003403c01c803101d1101350410300c14000500000002d5100e2080d0320959074902c07540c440d018160b504240407610365521650059190348541490201c540e00085000405402c0c03a0303041f01e81c1c0c0d0514025070800d0a025135248010003409900320700032404010305a40038901c65040c40a1564441c19254030030f8000d80213503c1000c460b48240d0300459025400035401c1082e940b0a1618076071843d0b8201007503842c1c07800d00001042086290080341c10768002d0b9001031031501065a0b608000a00190090071103010034820980030781c8042c0080103009000ea00b4000c4d061400400140007151a59810702000078140300c24418542c0050000e039903000304407100000914441d200720003400031500065008503080500c00d0300d201031504246255041402911100d0f078443c0c1b80750900d600c46403030251056000c443d40010127802580800e8015169540c0403405550b0358010814a9012901144041503244200850103405002440e0071240503d440070003411100302c801d031540c802c21904202 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 480115971 1250 480114721 480114727
    0xe1216060b0922020a0f03061d01060f06080c090a0b0a0f020a020d0f02031e0a03120c0806060c010e010515091302090712021c0219030b0d1e0203060906010504060803120c 75
    0x4d5695030320384000280940c0200f04962030301c07031038408051301c2040842c00c18040c649002d520407a0307040c02418281c03440340328034980391450218103ca000700c010b440f6080320701040040c01d080d6100c2480c2d103c054a40c00e400c45642d05002c480060050200100c84811034001c0e40e4200010382c1c50f08400103642e904242e0f08850081c41d400000d081501d6088440044070034810529800403000c10740605441c02502c03201001d203900700140d03040c0e0f000f10001a00103058040001d005182c40d030064005003082100014aa02d0302c1c0310a03032708550050b07990611f200501003a031001e910b01200d181c0d5004510045113226a0256030110b04e04601c042c2120041c00340b01c01c200c40d00a101a07060f5428082c0c0d07000c0b003120500640003004002d6010103110780f1078108240d0150441d501a00404175100760140c040a0550503d0b100d29000300b01d505014210401144603110150307a0801085005a0f003a1000e0f01c0c66500d00740030072080701c50700d50064038160410301030700b0710751110080700c9030784132003c2c07403100359 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 480117221 1250 480115971 480115973
    0xc1b0c0314010e1b0310050405102003070306170d080a0e0a2102011407020d050906040503030a03050a0b030705150901031d0a03090f12060e1216060b0922 68
    0x405042038140340300507032203400c80103c1381401c24580340850380020781c01c2c0e4101040540584064400071503028200398400300614103c202603902004c2d5081d1041084040d012062280782110350040e602078001a8a580342404030942ea680c99480442d443e8000b0b03c5403008171200500031010003401c141030540e0f582c1c0c44e1010503806020042c090303a40040100110000300e10050740e07010040b14502e0040d07180681280308103024070480e50040c904d50b00107200c8840607410458941c3d00c0519110b4000340207000009032501d08001038185003015460100f090300c1c3c40e0a000088a00e455440c51003640704200c204041d8035021044c40801031040c100555403c03020340140c0142090780b128102100042008410010020440720440c1e0710a944595032035913280144ea029001390300841c00c3d02040c0c00c02c1580060003e40c0000d040304409410b0381d1b800150310100345c04a410072441d10318620840511700c0d0800140d440341c020700782800c4a035400d19080c000c009920241e0400b40d100c405d04c1151038410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 480118471 1250 480117221 480117223
    0x30f060b04030b1b0309060f1b0c0c10090609120221100b0901030b0f0702010b0907020307170301121e0501050a020a18080607050d02070c08010c1b0c0314 68
    0x241030a61515903440e0b03500e251203c1240411a000d6507031242000407002d83d00042c504507405950884020a56501c91039243e00c002c410241250074020341403000c480f059400350340545142110a000f8080ca8064102403060880c103071a071060801100850a00031150400d0b042c1c0156604641e0410034095248082645201001d038851550380d0f00d10030108a40c400052080100b0156036000c0c80303003c46030000c1c07201d203240a02000b440300c1003100c005503400e035500042c25070150081c800851890240700220784402026511030005820001e0500240003c2c5140300307101d8401458024903541c5440c0e6483c0c0a02e110a40007444143c000d441c004050b103500c02003040e0107030001d00030401d0b4200080c1c000700079800f001d42a004290141c5501070030700e144524001c21905000050140395485420403100750b804001e00360784003a82484240b0108062903401f5000d0260b10000150b0802450350143c610945018a030200c401407101d0303000001c0000115004480e40104100c0d44040001e26603 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 480119721 1250 480118471 480118481
    0x608063f0601030803310b190e070812030108062707060504090e0c1503130b0a0e0105010b07030e09060a120f020112090201021908190809010b040615030f 68
    0x80e041481550000b0090080020066014910300702da82a43c01c1003003e1422a40e046210b01c2c030f1404c10b01d0b4403101e804170346810400c07940014441d007411080c4008034410001c94151989180c232542c8402000d101d00e0780204101030354008000009820b56140440f410742d60346008042200fa400740408007458a00c2c01d403290030094104a05607000151110801030007a08148110075a450900d240041c42c00004608a07500b13101c054101c0c0e0300c03000f4002e01325540d94009820002c0072480348120340c0204015080a034011040c500c00492401119603945003941c0040e00f101e460031004009020000303401440039050341406503560982e5035500000201d08205c5c903840801c02d4400781008400b044000c00704007480c14400d803100300e462180188030070100c5d01c2016000307003d41d008000c2c044240c0f002c400d0800e01c05100f03940c103a00d44990081114081c207403100d112400b169030031044c0441400280243d13101d05c032003a2002c12859240c44205044c0200244da4901415503651860807214455000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 480120971 1250 480119721 480119839
    0x30a1103070308030f1905010303020d1812140705090108060403141b031e030c0f03040f080c0639310e06040e0c1210090c060806 57
    0x40e151249840c022545c00c40307408907107000480812004080b41d464952144e241a01d405a00602907580440300540d4840303c1803001c80181a012100000c0405290099020842c42071050800700d1804504c0c4600d040266000a0710400347c0a005014a880000d10b0990041d0585032100084618070607070720540c4104128180d03000e40c9410301d605110000402400028600d03605c0301c00304000e542d01d8104c60b00040e6071400580104001030b036800c54070300d0050358016000c0c050700d45420030159035030b0711a54403e01580205070070401c100005500004c26040c00b55440591942042e1816200051241c0c3c1c1c90380807058101001c501c4840515001d400b4031030381005a502c0c502d04591404540b1048016841540b40341d0f1421800181035050900510802e028030b54010a04060b0704400c101034050711f0405c0030b0851184200a44090b401c502548203110700550300b8014142c1403d4009000000c01020103002c1c2a486c0c4000311441c0b49600903070700341c4011030407070b041c0c1300541e680c804410018881 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 480122221 1250 480120971 480120983
    0x1818130602190c120801080c0d02030c03060703061508040308070c0f0b0705030a0c1107030f020105071b0501110d020d27030506010609061b020114040b070b1f05030a11030703 77
    0x82c0c010301c2c0741c1240301c05480d980038007400740f02c3d10030b0a801101c00c1c0c0002d0082c40e9290300308006401480c2000d0a07007040c0144018255441e518001c0c0110b49005400c40d542c2000170f4a500013005401c124842d50308148507503103801c03106031920362030252618502800741d41c1005006c100d41c07000d0065910003070320000da10a81040050400000080003a00103882d520a81403a226419101c20b014880391031200d520b80300500040c40c40d40c1c6a842e40200c0110302641400400c11000c000100c17041e25420400c0319a0351844801d9003054001011811401d00c411850b501c004d11100c4100c0e0005618080c850039843d0a06c2202e100b203035141350300b025100100c4c4280780c41010200810401003039aa05859550b9a0b08a1240da142d4044866207080c84440038035842601001d0003551007080c0c40700384901480c05032403815a0300c41c83c4030201d0740b00004c1902c91006040c2448028620072514410305d84a482b082c0200605010019458101c130b000002c201d0501641005002d880074480381c0c006541102c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 480123471 1250 480122221 480122257
    0x12010504030f08090c09040204090302010209060f0c0c040504020d1b180603050d0903170a210b1e2101090b04120206071409060318060702031818130602 67
    0x441d02600e903101c841e0761400454601e40005100e400002007003400ca50b0024030341c110356183c5800b408001c240120040c1c0c1195001c0108044c56110b007001050304025011485a88880f4001054104008490b000d4440d904040c103000c0582d40b040000c02660350890b10300041c0f965094074907500b034022580311580465441442810501050380b080003200e00a8003611003407280700d9400c482e0038103207010040200c200a0040280c40b1400d4016140c2c06070300e410110181c0480405c500c03003180003031860015494443e2140103442c104110805016190509101040c52982c00054603e041c080100044c049603100c00c0514144250003125696030002c58180c2c250034035003020b010101c50041e909025108900209608520443c21071007080c02e07507216103040c05924420020b6990000e000c0740c1507004028000740f40110140040c6000d8031080d002540e9400114002c0310582a914090380d101c0e80e440595142c00c00d40910800303038407039000311551001095a1820000a010325280045107030300714 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 480124721 1250 480123471 480123473
    0x5220503070f030b01051f1209020612090c030106050109060f0909090c05012a1e0c080c01030606020102040b04030f0c1205061509060d08030702070b1c0c0f140912010504 75
    0x20003442d0a5038012500280242e8844080c46a040210039200281d1985040c20301e405a00c14401140207450900c4c0c0070030403d01e190001103040d001842d404100c1c4040c0b07814801100020403120401c450250700070b020980ca0000003900c00355440c42000140400f10074450040751113031000f40e0181904481c100a44511400d00c40520039990207240c0c0440c0413080701b10700c0703e480d143d001400503151411481240c002641e800f6400c0c80c0c3c0c84200340080e101d129079480004c40c0301c030004010308001801041c00c01c840c003000406032012a48150296441080144203540c1c2c100102c600352900405143e00c4d0101a15084640000c0d40d40b2060384600c07108003002c10800082901c0f0700440901c144103250107020000c02c5824031050ba001540140e40c0c06e4403070000f490309000346520a00c9030056803426590340e440000294000f0324110302c0042170450303000001199100742c0c0c40054040c0380c42c000310303138070803c000d000c0c0000d9804030300b4581404500f00705c041d51070406201c07040360310341c4c001c0c17040c0d0410b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 480125971 1250 480124721 480124739
    0x1f0803070b060a030b01051e060a020c04051e0114010207080d0201060f1706070e131409070e01030302071206021903020720180a1b0f02010509060105010522050307 72
    0x100302400c6400907580000b168061030328450b08001d4a0f00912420981d03464141000074030202401c1c0d8040025840d80701c45025607442014159403006600601241c80c403010800085450091124400c6601040d8130303022a1a40d86016041d140c83d224485450340410740180e1070410b140c1d0010613548140154000c0b016410f40084048580c5c4a02d0740d5200c94503031034400c0c0307042c03d0000004a10707801400001d0400d441500e2940c810040601090300c480c5901c4404400d590030901e010803103107407002c20300c09100420041c1800902d40c5010007203455046030780003074880c10340e0310074240fa03004001d0124080c045290f0441b10788110081c403404510004c00030140203900241030560f8405005020304000e078100f03603004040388000402c61042014101c00101034010058501210581d8802400c22168100d1841c10000c0102c2e07100d5079240715030414001e0075545d000b041d0989540141c0e004100998106060318108949055150f40200c0a525000d41c0403a05c0d92065600d80704240001070341c2d8070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 480127221 1250 480125971 480125977
    0xd030905190807050601092003100504020d0207140312040201080c09060d0501081603031b03120f0b12010c081503031c05010501020f03030907053115090c0e0103051f0803 75
    0x220440540381180e1f690361001048488040004901d0110001582e0b42a03460301c0040d9030208040c001001c0d401d4a41010508903000030f031202a1240e40082c0c40414032540d402c1008100080d11700031460881c02244a00e488040a0303c001c1c1482000c1c3c000c11148a81030059808070580603020545401c0c0b5a034030600a44028401c0650a0060542c0744a01100046070071003504c0c2c2544480145a40d0a208145503020002d402d40401c0495040301454141900030401e60386900032010a80e2207056041000c040103074828409940e141195010030300341c01017401c990007100c0600c101d0890303962401207411482001d402c801c1040310710000185034005a48198140c8600380d0841c1c1402c170240d029169640310686114840d50b111680c00c102e5441c0c040b103000d8003c201c090301001e00d40341141290444c242d03d45030704070313509031290031400d40d01e02880e045000404500038244024414001c0c040d00302001e040302c803410141c40307100151400010384000c0d040c000800a110351000d0703070740c115261030b03070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 480128471 1250 480127221 480127223
    0x604050c010e12060403180314010209101b11040908130f05010c03120c0201060510080f060414040609030e10090807140312090117010e091c020d030905190807 70
    0xd80c9030050b80300c5500f001c0c24003002c00c544840051040d0f0b251a1003e80791988101c9a0b4040c03010584000710020700420f0191903d80c01c0c6400142e00c84845404000d0000c1902c10607100300410b0024104480075610040006150001d00f14401d2518013404030340902032511f40030304482c1c0d0016810440c611110002e5003141c00304900d00c1c541035181d000444e07001c2e0341c00401400040340c3c01510081006247c2c040e0803072141c0d6000000d1490303542c90110360185034042a5101180703000c01003002a1044c40c08041c2e0000d401c40d01080040d108140414503820040c0014000503a41c2110309c0c1018043c400018074100004c003080010310401000030100c52240c05402c202e80a0400001191b001c2800c0c07101d0681030003805003250602c918041d41042e04150152030400241108822201c0e0041d12814060700266002c8042ea1401649841c5440c40d140c2c80f50308181201101e07290b08550102d081800c0b40d906181c040f81230940c50914615200038498800e4809018820386401c10244000904140b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 480129721 1250 480128471 480128477
    0x30406110312150f150703111615020c0d03081906050402030c22030c03240c08011706010602030f090a0b040e04030206070201060506030408070317070306090e072904080604050c01 79
    0x203011100603c00301c2c5480d2917101859031020300007180001e0003002008502d0081780c04840142442c441d803901451026803000e14041d4640080c0c4200030303810300400e056000150f580b2200643d241c3d400421b00031008102c003095040c50403550510141d15008071008080080040d034a03400c140c91600d04507840b0419898000404400d5402d0415071815036004681d0000100c00b580d034a1901e4401c9140301201d2030f14100c10b10460043c400f20744038440c08001d02110760710801d456041440810141d1a14150903600e03034403503001081480e41c000b04072500c11000d141810780b204030b0880410110070b0300e5088003400721804036000c40c0000307030000003920460281d401c07a049070312010010381c2240d031176015694010004200003808152800003c00d6894030900e402c9030324120f0b030b5000850310700c005c1c1c1d00303800082d41322201000103d600307010300800f08014101030003032a840d00c22000e046030710760304207040d4554442202c1041c00c2c040e501610010320707021050f205c0ca840c1c40c3c03a140d620384003425516804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 480130971 1250 480129721 480129739
    0x7020f0d0e1f09050109170303060411070605040b010e010b0c10020a030e0714010315030c091d15012907020d050304050a0923010605090f0f0a031505090604020303040611031215 78
    0x400707d181c02c8070208002141003d10710f90340341c0b0414040644032444101c03010040c1045203100180c41442201e11950042143c407070139506040d00440014010b0340003006140007440350025000300841c103010180e0106c0320060b500e00592600750083c001c81c04100401d400765201c0081c05001401c115890050241d0b41088148210b102c0c041c44008903000190410049160900840c0c16036032011604214048000350304021004107a80340060070302046090890480042118200b0720782e1184840040160740e504020032195100c0450003400b001a204034001c40703c40b01400344c00d101f1180a804042c0c0300d112072585070341c885405403c0e5590961b40078810903078440c1c0c41e662650700300c50585408e070355103a10380b841c00d4007002041880880c08642c41521100411082d81e1070010000045108000c0500101c07581c001c19411030740014440c01003608103008000040c0d402204607400d96001c1c0c20806d82c04414110424598000c044a00020108000501444003540c00001d40c50b00c20443d11074003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 480132221 1250 480130971 480130979
    0x311100608030406081f140405060906010e0d060e030c16050102030702090a020c07150c05070510020604170409150305010e0106050604050d021302070f020907020f0d0e1f09050109 79
    0xc642103485140d0094100740024442d662140b000c458001c03d410038800d8242e507210b01c00703c1102c5c60641c0851100c2084006160f224100b50154540c4a401190f52a42625010002900c40580701c01c0f80c510400c0c0c3d45410408003c0d15502040d07026641d402241d803600c00412800f5a58810b5855a8411441c10b200c001036030740c400421507034001d074050a02c0d102c5d41c590407000c9004e90000a283ca8180c0204440810084904c0050014550f0590381c1d4041020250501c5400c14401e500414080c3d10200c9032285401d0f0002001c0d0b4200c0d500141c0c482e0000022407000352203001d42d401640c1214149918005410300c215851820f40380180000c121205600e206a400c0f62080d00c03e154008105110801c128501300d004101d0b6580083d25035184809a11030510484e0322808082710350740384000c0c40c0b8081d0f04001c3c080340d40c4000240002c1c01c180300d80c130240594680c015400c9204101d80a010001151a040940c4031074101c0c0b0303110136061880341203000d403064900707020300c50028880700c1d0700003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 480133471 1250 480132221 480132253
    0xf0a0f03050711071703252609060d0b120105011a070807120c060e06010312030507020c060a0509030316060b0108090c040c110a4403060414040506090d0305060f0f010e0d0311 77
    0x304009000b0096840c112270f80e0306000c1c07a03420000f4040c3c0100e586881d028080c2e114041c00280740810000005019814a140f0a401946000c44038003104030610081d00083d0324502151040c581001089010060044040328000f059503002441c55042180300b080442c0700050310f40c142d80c4500100000f803e2404070450840b58110341000043e8040d4003207140b0760a04000078480f4030403619180d031130304a0301001301e031a5a00401c81300c400d81c80010460300521070103115285000d402403038110014101200140d039512460550b00388a141d40d40392001516000b064404074804010701078585607540390400e40d03c0382040588424000790450303240204c6c0703440c43c0350700ca904078081c103039046152441c4414035042e9000200001c1d005552020a611940811603416220b54855401050316203010207001f424003a4542c010400d01d0300b018180324080d80d801c00d866422800c2a03801c48401503000e00121401841c001034150858070b0814014281503116502c0144200750f4030444180502482c6c0701 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 480134721 1250 480133471 480133523
    0xf060424030b031509160e2a04030803090307150504030e0406050105070b0c0c0a140706090f090b1f02010213050916140f0a0f0305071107170325 64
    0x100f5030540200613444480c1c4001014180c100070284119030703514880e1108030f50f9078000d50b0886020001040b04210901e0003000320b10341200c68800b60704810f5800071459001d01d01032800010401c40c00400020101e000c100280c0b80500e0700402d00c3c0740001501000400142002e035001d9002592002c290320040c105800307071404548040c0c1d0786a01e08495921081d01002c000307400a10003c03020001920102001c000d01c2100d60b0240441101d1481c1030f001040c0382c103084d82d00c49030030310040c5041001000f10b003043c40b900302d450441c2d000c9013035018140060002c655210030390340d40a80c049205000d883c2d055014241c40002007220803c3e158a5204010f02c800c021600402d000d003201a003202540d12401001442c0c070450401a0b0410716101d01c41c010070740028502d1030010304205010403243e90306001c0c80d50010518201683d01c000b01140c250b4a450990190440072404440ca1000044040084a02c150032422003c0001070005028181826100d20140e400030145444241e400c0c0101807070b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 480135971 1250 480134721 480134741
    0x60103050a1518020405030a0b090d090f050105070f0c0303080a0b0d020915031e011e0b0f01140904050f090c270712090309080d020c0a090b0f06042403 67
    0x301034810b00e840203d41d50325080200c11104030f81c0030301001070300f500d04201506600e440780d12100060719102d25007901c0d20085500035030400c0003854080102d0908200c202081c3e078420b1174640c0d03407641542005011b103d60204010403d4103004000010b2641c4907261030300a29408400b4890414494104106100c0c1d030740010b90701c40c144034040b40b400b281c501c44001c03102d400a0140d446100741901d0130300a52181e4000e0a0746a515130400419280d210078a400c2040902c100c2001403070050b0001c69951000070301d1190500442006064101512341c0c184c3c1c1d40100c00810901c00e5240c64002e490108a058a1040051141d681010a580b82c100500500e000c0c403400202c002c604280d09010f2041000b909100903c0305000900610451030700602d19002d000c0d072a81003a052511040510744102101c0440854100b6042d1007000d6688903000b0f001c50b0100c071008504031410200051920422200302c81c0c0c00000040e0008264110f9032080c0c1540d6040b40c105102e03612101c8095040c0c0341c507451 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 480137221 1250 480135971 480136001
    0x2150c030417070806190b0d050c0424060c050c10080408030a0204030f08120702060c04030803091002130906061815031103090c0a090c050a080a23060103050a 70
    0x4002d02c214400c101c515601c207405241103070302d51aa0742075861305029040c0c9801c0f4240398403d20109208241d4000c5100c00d0304161292603070002c194980ca5114042062217502c655201d220749100c07022800d190102244008406864860b55080040d040707072000d00040b6494018180d45803114038201440b441c2030880381d2103240044c1e5440d680c1c421258001081403461030f50074080031010411424424025512440644d0382c0c51a4910755038401e100018001e80c11907104800b0060100b403500b09480889038000129900da8031948030302814000300c4440d100e145480030600b40030009011000f0000c8030600d000400c1481e8589000304d605d0340c901d0031144810f000d030764810800c440414000714000c0c01c0d01d14000489110102882c0b9041c1e009646801e550350010b000d000d61482c00d69403c2e0004c3c11010010040c140c040c50001e4814021f00314440305010000000803c01145a040543c1205070b4105484050070b014850340e180403825190749000928260004040f003000380700d07000301d03034070480 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 480138471 1250 480137221 480137227
    0x41806061d0112060204080304030609051c050f13170114070201020306030304051c02040603120f050313030804051e100c1b02040209060d0e060a05160f0f270302150c03 74
    0x320404120006106040303940583c2040000344547c0e0034000341018500c504000303c2c0d0040c2a040c25854030f40450302e215030829062030350202c165000300440d041940102405504d4050080c3c220407809016488082c2400707003007486910b18041984014040e4180540203119621a004100d00300c0c007013100c030160164801c00c001c2c8501d290202418804110313803080025a28074a0b804282981c0d1998030855200c0321880c59400302d280c00c800050100c441d00d14106080d49000c500c00d819682021802906010140011030b09203c014051b1078030310180d8481c802d00303040e1600d404c40d035100c07070b404030300344101e450074503000d041380e10482800c2c4d40c00301d41000c0360241300000c0c1c00f0031000f90300c1020781551000007001040c005034868000d90450641c050042c10b102e00e0036031804825105c00030f140210b04c104106502100c135402c40c3e24000d8035049403420141200c03081c8001e8500c0c1031150b56803505440241030300c480c803d12550102d800e0345e1096886c10903050710941014142d00583c03402d00c0540e0400c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 480139721 1250 480138471 480138479
    0x806010507060f1b0e060909040609020f03030c07031a06090a0f0204050406060203030a050624030c0f03090c01090b03090c132406110309060316030605041806061d01 73
    0x510003404103680140340010315003c000d10502d04880e81054840d0b80381c410342d1900030640340c2200280e008036500b52000d40c034100503600003511f07504008100070015940c1c4c02e1181d055407100550500d4075000a81129070300d041c000308072603481e000e5200440b9103944881003400c3c040d0000c00400c0c000c034400f0f02004020740f03030fa1501501034106881c444104540c240000203050f510760055200030040354018582d0b90500e0250342c0f05441000380024041d400d1b003180c86c071300302d039114aa0034450420b80d100203850380c40307c1c04040118840d80c015404042c50210030312410010102c1d0448004409803125511680e941d803440b4110b00040b10f60340b50a8006040301030300c0b8145080c5241242004040025081c00f90740c1880c02c81040060703648044c0540c85905100130b07904045141b4108000038015400c00140500003500e9200c02461161080c140c2412016428004c1c0c02c400040c0000034014070070f0030f2003d81c060000c0c140d01c1c00d0030740314103050100005640701c2001100c030100c141c841401c507450f801c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 480140971 1250 480139721 480139727
    0xf010b01050d1805031912060308160302100516021902010503060f03070308070302071e42020321061804170f030103020f0603090618030f040311031507080601 70
    0x140b501407608461981c2141030000304e0500080c00c0e0300403080345c69000f40480e502c2c000c1c1402c0d5154107000c1d40c1890076209101007403000c800e40381003108503213140c1140c91031351038203d0510313a5180803900c00500f010b05000307100c015a1000d0070360030907950849107000c01c07021100044001c0114080c0c0072840c00c20101e031807130070510b9091a00301b4014007203d000560740c0c0d4881005a021031801e50050300031400034021410298080c490710809011a400e11031304010800290075a00c02082d80d080c92802144150214034880001d1740460340641c0b0785400c0b40050001c2d4890307014003183d00c0c0b41000042050252030710560070764090340010380340400c43e10101e02d02800000001d8810340721603006c0021016052150b100a003180307541c1801c856102e51540c410702c654810070b11000c9105003014810002d2003500098020360011002c0c4540e00c5008801445030705510500c080030000c400d00141c04802d00040b481c44560341403081d8111a020003041e8a840e00c40711056440200040404001c03520070741c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 480142221 1250 480140971 480140981
    0xa0b072414070c230304180207020108010f030b2206020a09030b07051e0d090209010311031920040b10030204180603081207090510080609090313031502190504080f010b01050d 77
    0x70113803044901c1c054903460002d0803210104840d2a15903000601e074402c41d60702620719401042c0381440310041c9411999420003843d4001e11140240411b00341d108080f04104d03000c6907005400460855496444e01c1004000c16220b010584040700c0c864041800c213403040f8111044903020301826405c42c5000e25079030b4010b920800303490807010780701e900600169660440050007907120300003c50008504006042c00c26007000f51050b44403e107001c101007c01ca01ca8640c03030600241800c41e0a1501d05000024010208064a1034010090f074519244403034155000304190385000090005801ca095241820b5036034a0000919612080c019010180015450a60070004508056070015203030130214040c280203881800001d00c10350700303008060034902006174012509038040c52030041d1104209032104428030004003407006620042c0032413020fa0341902c1d00c250a00b41446008401200001c00a400070300560005005841c01484c4100051241424443d07042e128181024900215040100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 480143471 1250 480142221 480142283
    0x804120e06040b070b221106070c3305031302011206061106060303071a0408071205041d072703060e0304060909060503120d0e1507120b0a0b072414070c 67
    0x1488c02d12011002030741c001c155202402069500050010b0540d0650000e5900658400a240201c4035030742620755210003225400414410424105642c03440104e42105404803982c290900c0c01c3c0e00401c0c2c00350704c9a0790080c01c03003580302110306580b200030070141c40f0b12501e84000e2002da03104050000e01c01e60351000d81d038413a00500486003014202d4031400c4c101206643c2c606d0000708002014005005c0c1c42e511f1807040c1c05044054059450302103009003826152075030040002c107500075141a01c220040b8408086c55120f40240070324030b600c40503d95240c206001e90340209414032800b1032000458850b400403658001e00030100300c8140890310b041940100540119076413210900ba01d040402c101c4031108903101404220549402071f4020a01032503081e01d0023a4508010024000e592002c0c000b02c180d40b0306000c0150740f01030b10702d400f140b1880c155a9004048025044861408665502851b00c030000401d5048a940d50207108170740e003503090030009000d102070500d10582011240d03001340040f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 480144721 1250 480143471 480143479
    0xc02010e0d021f240f030c0e0415110f07050a02120d0807030b0f030a0308010509100302030a02090a230109060f060206270109060e070608070804120e06040b070b2211 73
    0x4180c8580c04ca09064094210740d4403440d004030100200001a9030060081c000c6c030300c55416504250741e98003103904088616001c1d09c0c0d140c0801c4605c4030212412208000b0a0000726075440085140227038035941581000e0744a03803000004605054400b14071b060304940c0958511005030380b0031030300b540180109151103801001c03099031500c498034204000d502075070103515035115940c5881d0030440074406c01040d0030212641ea1a0400041c0c81c00030340090059811241c2c2d20080c1e4642c900c4200400641d0382000c91140448214440700c54942050b81c145c440302c01040c041c09440782c40b800c0c42690944564001a4481d4000840d21001e102440b4000704d03040000e960680110b62059081d00d0710040d0030742c2c94540d110b5907442440340c1000b240005003d1410080000c0c5040352015000d1135009001808414000086501152150b0788d0000708900003800d441e2030704e071202e000d1041c0350040c1c0c40c211500d18417100400c0781420405408000b4030440c030b0b5070788820402c2d55601186140e003000f0311900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 480145971 1250 480144721 480144761
    0x828020d2004051e01050103060612110c1e010f02070c03020909011409030414100507080d06030c03030807030f05040b07050a050906030c090a060804030c061d010c02010e0d021f 78
    0x2030b07540310b01a00c1e004960340701c003400c07001100c60f114100c0c800060344058140340c604001004001c1d00444550200c1d5078241001400e400b28480e00c1c03e50740b08880c41400c0720301403039050780c00381c1c61814288441c5001c6e10000b0000c01d90079001c028101d100f0020050100340c0e00003c1000145040c00d00540d1158040c4004521140c0d050101001000d0070390301403500b500003240034041c500e8159054a46404106ca080d00d40c1c41038114043e26500c2043c030f011300020000134116442500340d401c03041c0103660012000d02c4403982d9007002421303054243c5508000900b0515917154041d054005d0300c1c05075810003024040c1d510769100644040d880400310405110b8280502d100c3ca47e141005184103c5175000b94a0350f803103001041100081090b0801c00034002c81c1e00911021907170103034a0104c400c0d0700c040001080c546259880c0c0403810f08402070340096003848407500107a98103400800d00c42944408442070761f5034940301680c484500191410380c02e1240c6546615245540e04454000400c2c8801800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 480147221 1250 480145971 480146033
    0x31e080c010903082a040b0703090f0f06110c0315060111060903030f1008060c0d060509071d220510050603090a120507080a03051b040828020d 63
    0x70a4903801074099001c00c0c551810043c0d00170b001e0541000d283d00c050107440321a654409001060301580c000c541080300007140ca0f908140c0185200300c00b4069001e03098500707691358074804124039401c0c004c01c00000c0c2d61b04044203004000041464900e03000401504480800c2281c113004048010b03d02070400906071480c0800b00c03000e0100e907000344818405950740c0c0c074012503400c05c189006401c803e8503c100d050f0821810201242040d0030610221509580e112144c0071b04016042542000da0302c6030342203090200703541d00009007540361110050490304000d1500100070080c4140d904161000c0480d0748a1080c0c0103080d8045030744109048032205495845d00c02040440d0021510003151707038040f108100600402c103800707a000f101c0358079269161012680c2e40c0c062600070000d540080c507132a0400304003550311003084000c0c450711411a56483e1552072501c00e0340c1d0820200c0ba50040c5034006082111408a251000341c6160050100e0a442041d0b9581e26034400700701c03403114410034000d200341c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 480148471 1250 480147221 480147223
    0x60b04060303030603050c03190305030901090b070302030a1a0d03140d06030308150d170307121a1207030309050904050106051804031805100f0203130905010f0906031e080c 76
    0x1801440c083e80c0c00184003400d51605a00d0011440a2948a54850a0700609108a140072200e00aa062030450b40302d40780c42c0d200701d02410f0f201c9001406c2c0704441e000c03c407080d903055024500c15841c5610910030543c05441c01c01c1c00c00071050400d80c00091412400d00428046d1070811044061a20170740d14280803003a40f0411946503400450001c0c01e48410b108a0342e01c50200c24011a0f0101c03020035422500359145d920b40495840a011146004000a42101d000c2d50f4521105508090140150540180080c1801010b60005403184014015900c14460002500c0060700d5064483c2c825460900301001032a4a00410484041d9280c1c600840c03192075a00d020381c400d42800c00c90211b0340c1031070300e005041c1c0c0c0302c0d81d803e00000503c10b00f0700f0080c5075501c61b08114120b00c40d080400c001300506a0403400c6225910603d018402941c00000c0c40c0c01d600da0041c0c1c12038100182d412484c03500d520030b42090b189076101c00340c1a0724075200d00150700c0c01c0000d1441512031261501a01e0288181021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 480149721 1250 480148471 480148481
    0x1110303070302161403220b0d0902040b04060b0c010c03050118091e06021b1b01050306010e030a080414120a0602090d0b041226041707081c15051804060b04 69
    0x4101340d600003003000034030101c24180f5140b003204a41887d00e040707030405800d80e85a0159001e840e6110362280265800c0d0740369a44600b4080700090014030120b611646000026070009e4400307500703903191541e2301004034406d2152a05880349007603260404410040308030080c20090304107981a81c82c0c00c02a4031100842540081e01612501000d600c0320b000d00680c0c80c62442c0280c11001c0c41d0860850348181401c0004040c030304100034284541ca0340c541c4e0004840c00c1440348030964041c45020301103020700691102520464400c80000640303103400701c0c140040c15400145080c5c059010001e4000000d180c0d07000f510b158140030704988102421503e58881c0c02c0001d036000d440e80e0404032003e204195015000304c00114602281c60381c0002c0d9070008408903140107001400401c5007105000044580c403003103c0003150004241c0c1d8841401c000c4120328058800141140c15292014901c040352036a031052040354802042009001d4500364a01f2242034002c10072034890365140e04c44c603000e81d87d500c80c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 480150971 1250 480149721 480149753
    0xc0d0f11041401080c131a0904050c0a0308030907120c06030c05090907120c030203060f120c0402070506070906081e1b13030c0f0e0105100c020d1a060111030307030216 74
    0x61086401010522106c00307000b543c2c10203010308000c940b2403c00c0304c100c010384125109680004246d5a503050180c00c0006400381c0c47e45c404a555000028004243c000d140611101002e54400e641e8904019080c011690802032040340c8406007002441e029500418030b0005508019162240140001d40c054000301c4210020914000354002c10150510800c6940d41480c00c0031841c2d41032401c005a20503075441c822030304ca482e1740201350314040402d00840c0f113102c5021348107545944140c90712503100c0c1c07000c81d1004000307144101d0001d5064824480c0314001e02c0c00611034020083d104021080003c0000c100380b4580d50014010191511200f0003444692030084202c42c0c41c07030441c81c0c01c496501e2554801030880303096003003e10101000d07100030350442d001156003503075454490382c00391421a42c0045c082c0d4002c90a10740300c8280589014040d0f000c0180c0b00e1000c015580e2a40151100e8000500035192030740148000b4040c5030103980107000310141221421103000c2c06656110507900307040c070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 480152221 1250 480150971 480150973
    0x6040f05010c08090c040915050103031112030601080606071e030504060e09190902030a0c090906050c120a050c0408060115020c150a14040b0d06080c0d0f1104140108 73
    0x10048090010a12030102100041c0c50a2252400d1514100d996079203501c4025109030380d0340d00100200884078004a505071144e4009021941c1d490901600384a030340340e0320b0850360149840003555485800c00f201d2040205842e0380f00305840e01c0c41400882d400c2000c04440040c107051107404a01d00003a00848541e1287d90b80300e40c0c0d00e08099000302001802684035020390041000d0010034100c00002504550302040c2c005590903c41c000203140c100d00610243c074a52103c40041040111500300042d060f000c0c41d810721160b1204800c0000d5842454440380211076680c0c081003155219800c025081044580341508050301c442d0181e041080130303848070311101e00140d02a003805d41c0501051210001c111810b02d400d451004c001060344c0b182040e1041040361404c0e40c1100290444c0607036024001c1e1107032058444c1d019140c05401072005003ea81100d11035035005c0400c80c5003030780d0320358480d65208000c04181d131155650055a10b0039003080541c4681c81d200840140709080340c2d001d0080070040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 480153471 1250 480152221 480152243
    0x280605130302190209060402210109090b1605090f061e040905090f070306150909050c030c090105060a030b1807090303180b0307050d06030b1f0b0306100f030605030604 74
    0x1140281c038103041d40f50300c0519480310301100b40c0542d4607400c1c081c4c1d1106040d0f40c0981d441a2180120f1180c400c50070780121060040700011075442c01b294480441c0d1407144100e58030b2501c1d8038000360595a0310141c0c050020303e08202c05100c50400b00711512440c40c02410f010f090a81c200310408400b0303640a9800721020001c00c0400c80210a40281034000c0300a001800c42c1da0181c80030f8644039492030101800c1c1c10303210f4070020410704503000303d43d0040001c21400c00030b40038a0b00e4a0354441405024261082c491000a42203615000c400c450403108001d1820303192800c0d40405801501101d80702940c416200b0b0303262b201400c00072507030b28869166950395103800ca045280c068500f400c0c0502c0e10910302c041c440d0a0041d00c0c61602142d0b004034503820302640b0b80d110413414134007070116500000c061001140030b11020b0034500041999406107040c1e207046d0241c842c030480c1c130707070307005c1102d03050b51102d40d50032141d140600030344901c0c8074011585400f00344d33581c460010a1500c2d1040c0e8045807040e281c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 480154721 1250 480153471 480153473
    0x6071502030c180d020f060313051504121e14090603092a0603010509091c02030901090614040303081906141017061512090109111228060513 62
    0x38410200c0740382d800311000584c9a1498000c181d544014141040c041d00001010030b40e0014074101e861000c0340d205085560940000c1c0e10100300841c2590101c68026003410303010260790280d03044c40c102c46003212650090884150007201c000003241e205c1c0d10320400404c14440592102c900442c46100960010300445010001103441000e881c1c0c03499400341045010114503985810848e81140c1e412a440ea08507107645c003c4600304000d10007803800910540284002244d0040060310100703609807156002c1503075816080d2244d20100c007031400d04510400c024400203000300c0e600c0360040e4071a03240307500c001504d05841c01240c000b60403c20341c0f01c030410428502c500e0854100e8881c1e0b250f510300007601040c030741050346120b2009017545100b1441c1000c0b8a04080c0c85000782c0c3ca51134a00c0070650039900340b06041c7c60003801d2806c010f46d0f1a809504500f00642170440c408441069002c00500e00c4e14003201080c1c038222007220a02c6c110300c46401d0041e000c2015406481e002d0511031024052141d16 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 480155971 1250 480154721 480154747
    0xf16081f2402150105040203070e031c02060c040515030702011803030b0312040806070c080d0609090b130309090218040c0206100e070906030b0a08010e1c03051506071502030c 77
    0x440c00714002154819090a0f10040820030f0440c1112820382c0c02580b00c1e2a41041501c45014003003030b40b0381510070181d555510600001da40205034005070240e8496403240b520340c1e40b4a11650281e19084009440c9c40340c1c0d60342101c0c00540d40901c1d43e00c0001030341c40c090600f46400300100101500040c1d01d603200340742c0303918040c00f40c25115040c00011629003480c1c049800c0c0c5078240188148240507150b1440401c0c00309400032a85c2c3c100500104016013511003048030003c02d04108152500060f010005981e0134014102020039a0103440e04120545888088000303980810381c46000809014144019501c8a0040c401a0311003a000f6000501e8000210301d8140c1140d800200305244803024000000c0e0412071040a8030024540841c80c140c110000c240300c0040c0d68480b0320590b203080301100f40b803c40400d680500400c0c03403800c80c2e11415205422400d84030b0039548108920003000501a44e850680c0040907410701c01d101d02051348086000001c101d07041110120454880000d0a183d0100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 480157221 1250 480155971 480156029
    0x10150c140102030403171906170f03030606070219033e0603011824170706080112150e07050a0503070806060103021308030f0904050f16081f 62
    0x80c0c448000c605515007914004c011040c0704149502c81001100810098803a881411014a51940c4140590350381d031860b45481c010000140c0c42030380070b06103c44643d00c4011044038011280200039608268140d001c03c206060b40f078490303075090070350301500200040382200344a61003500841d0102008044440c44000b110034890005000b4210506440720f80c1d444105480c155200c440465040500c0c038076115006040021250405030b84c803052000ca14205050726000360b070b00c1082166a820001e10741c19136210141d004100102300b0080062000b540b004400c045054012001041842c0380c254000c41100e01c2541303c181c9580142d0303014015030038142c180400034802900240111807400403a951541005002d5604050b00000c152503041503175601e00c00540110303000c2c0c0b50745521280010500d50f00080b19540200d0500e03001892410b4510016403080c240c81c038200c509140d0400088800c040f0003803000c0b2142d01d07a07005926280090f92055000303040305140c4082e80300c500c0070380065004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 480158471 1250 480157221 480157253
    0x280309060c05070308071b0f1101091d01051c0f21020a0c0e0a020c03040f0e0a05071704140a0320030405030a110d120e09011a1210150c 60
    0x104016240000f17603c0308209601c02e1891401d441451090303c1142e000d6180e481c4042c00f0740c0c0450080c4024442d03164a03441003c07600344c8407690340079502d007940780584180000c44045800303070354010065800d0035084140c0e0302001c4030030200100d003030b55a45002c0000c4050295420304801410a1001302c0d0b5400d682e2040078180000c00c14003181d0360302c0289440c214010301400501e50004078144c1c50040e010b554a403281c840560b91160303201c1d000303948010070a10462012281d00f03000306040007072511489010300c204d42d032001d4224003607100d110035010028104951500300c181d070039500031006004001009201c1e40c2c50110070100d400c0d4295151095014803400d40c0c00c02c220401032035500242c00410250311040b107040c86540c2400141d0130a0300440040c1070141c5080c0e0075801154003041c071407600c01084420840351707601e03031a10341c80801c2c4007065169600710800429144a658000d01c55101021081b060382071500c840640041e40842c10081012518807051201007080101c088001c1c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 480159721 1250 480158471 480158477
    0x20d050c0c0a1106070b0115120212011509090c050918060f10030615050702010318020a0909080c010207060209030f01050403080115030e0703200105040308040506280309060c 77
    0x507469080554454402400003010040800d259041c1c689581d802c2c1c0b060799400600503000c1c2e695440207803040c0c0056148400024401e045007030402d0301c00c1d200741d0f44101c803961084405a03090108400c0c04201c4c0002d40014001c000300b0005020050303010307240d005a45a516261580e600c00c040c4802554035001d0510880018010021140c4407920000c1340c0c4101100d01003101001540182e00034800e54100c6002c10340745217600c540403078120000740040b034404e80c2e0810050321951640d804410303150500a500c480c1c43c050802580d42242c109003e140c0c0241c40d42c502d00f62440c0416422641701410031034034140c003c0382040081c6000d000e0101400124002400f4038506030754010042c90050254540d001d03082c6414191461280c0c0c410320384042c940040b02c081c240c590504001c80181c040030000015885075620400b03510036000c1d241183d038441952802c090403c010031003960024a1907002038181d94441c00d0740044d00000e90f00031000c09490010344c206041c18642c054545120000c418 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 480160971 1250 480159721 480159727
    0x10905010f0f111812010504060b10020607091a0c06010e01141804030807030605040528020f0d1d3405010c0615080a0503190c150504080409020d020d050c 68
    0x10f12451804960b84043c1000f8076011042400c2d0001d100300c5001c081d140d0300ea41c60041000304110b0039a00c0002c02d49001c5801120442c20660120382d5950111400b41c00103942c1c60041014074000c46401111121141e01d0504200100000501e0300c002680703c0c1c0b10030070000700100850035aa1403035082c8048191076010306104481e43c1152080d00181001f8208448040054010b43c41b13503212070050140208180014142a11002d000038014541c0701d203c0c040c813008040380b526491003200c0c075941c03441c5201e50800e20685803a400400103001602c0060b86445924880c00200380805420400c1800030384004c154051103d41d000a0001109184070701e03110001d0040d40c0e00480400c6280b40d0204000c41c1c40c0c0c2c0f0100c45041000402c0d03000d07509c2c51240721046410040d000c00034020000141c03180d0168842c1c401000c54114a800e540900b503486400e600034208541904803660160060800e1890551f80f80b507054100c0c2c0c000b40640c00301590110b045007012503107005050304160300c0314241d41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 480162221 1250 480160971 480160991
    0x20405090106090812070c031401020c0d020f190228031202030405060301090f151202010206060405060a0608090115060c051614040213030b0703020a02060f0c19020c03010905010f0f 80
    0x45d42d41070320489a00103c001150b10030400005200307002c041d66001c40d143c031001e004d106055000c0e4004403400d640c540030710ba0301303044411710001d61980c04200050052044422060042054000b08181a60000480c0e12a840141002c004890b081000640160340061031402c110501000ca8404141103400c108401c100aa4810f42aa419250131301c00001c0e50b0410130314410020800f06040381c1004000160016410b8001003008040034000c3c0c00742c0e400c5503651006c01048690071a2800d5000c2d040388000e010035841100d041ea8480080f03c00015405100607540e040c4a1040c5c0c000c2c4006010a82013100700001030101405281d03844a10390260f50401c0c0d1483d4451200191060050b035000c01c103141000c001111401c02550080a500204d007090301000b8007940c803803107980c405031040300701040b4502c400d0260280304100c1c0400d034606004410941d509800b01e101300d020300f18031032208484207d541c01e10914062030300c0341700006240d01a03800ca0100351242103805209a916280400c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 480163471 1250 480162221 480162223
    0x15032d090f0b0924070503060f0a0305010f0e012702120712031403071d220603020301060e250905060c1005090c0102150604200c01060909030e100207090905010204050901060908 78
    0x4c1e03040b03421405c0c0700d5141e03601c05012424a0352404441640030f031104e00b00009000f019841000300401c20070050107121741c01e030707415802c1e618809101400c07210903074105034407403400c03015a4825034070083c5501603114100501911b002d070290001c500340c0d540d0000420415801c02c9070070000c24003800d5102d0640c5444400070b000c88510310708008210160110380405952003030b020b2030544048d040319201c5124000304900040c200f82c0000c0b03009618001021074410b104490291103079110b18684021810101210713060030305036100d01740074001c0d0020003103181d9642c2006000c071031805000034909881031040610503907401810000e00e5070050030100c0806d0740d02103011440d8840850588211761641008070300149006502181c0e660b0320800c02480d4410020014007180707010034000c4c003400351105105011070303014150040200f8807141c17003048c5505100e02100040c400c1c03801500c01c025078800044040e03440a100440b07550f540010144403d02e030504815001d00030f00c1c5130420541c0e04040040f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 480164721 1250 480163471 480163543
    0xa110a1104050a06030f1b2112020309060d0207080f0703020606100305060303040506130b0c030403060606030501120b04140f070509010b070201022a03031315032d090f0b09 76
    0xb07018a40071f000404540031356100e1a0b0020709040c218441c40c05030341200091288403a5400b103800380001501414010310000607035142503001020345141891001a0034000d43c45100308651840c8140110320882080b400980f0005010f50090b003042d1809408028108604211000505280070309100c0251800415542502d5090301d820b075232001c4607410084039400f181d0103050540030019002c0d50410011029000312807055209101da03a85810080d016203000340940c1c5442d15500918802044518003201d0b00306019880560440391201c40c0c0a0610f406030424101c40d5201c9041003003d8100700c0c1103035005100e000a4a4100601a40002d481c0d001076246001583d038403c2c0f2840051241058092002e02c004044a540302c3d071a05800714103040c0e91040b60b04112030801204803507401390240f44207110a1a6002c02e400c03040a84042c1d10020090980d01d044c2e075291102000981d0000c0036400030380c01045040c5140c038190034220301c1e0050750766071300f01c40070807a520a4480c0104a507507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 480165971 1250 480164721 480164723
    0x12030711010f090f02090106021504081b100e0c0406031e0c0b0a0801030606090b1008100b0309060421020a170d050a051006090501140a110a1104050a06030f 69
    0x40d5040a108428440c05000342c82003403003003a407401121000b0082c51a004d0b0900314400d840c100c450340c0e40ea20060b43c40d205a080420656000b0100203000282c19000078049001c2e2096004ca80c04001d00c00b5034504040810070344902550f4414120b000401044640801003088900303020842c20b40e911501e02c61500941607100740060080318081042d41c40e03e540c041c0030316a83e00d0743c0f901c0c2d0383e80000301844820303c001d807040f515280011079203444030b020718170744584090203200310495410310460301140010700d42482d8842c48400410b05640e4a0001c5000d090500c0c01401e0505080c100308072651034003000d014176100584822000580c020990740e40e9250031500229102d10244036000d221b20039040416040c2c3c0c0380004222428486038005070045811408101a098a402c402e82c3d0340c002c94040d5030b0100d10034103815150703081c9800040011968500e000036600c00700c80c140c14a44052184c04458044440480b0707005401c2c544075055001c90034000c1032044a04d96100c80c4507014140704 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 480167221 1250 480165971 480165977
    0x501022d04031e050705120102031504140f0c04090c05070c080706090909020102030403080304141b01050f0d02040f0b1c06030f020603090114070306061806020c060717030106050a11120307 83
    0x91440f0038400140300700c400a00c0301a14100761804490345c40c0303000b54000c6800c00344000004840344010f092521440d5074510b0620030b00d0075103881e1460500d410200080044440c20820440841e03040d0807802048070306102d03515a292111003519143c0100801c82c0c01003410303544050010403025500c000c078182118400c4800241c5c0c20003600040341144902d8002134002c0c0800024841000f040c0040b80290b4185501038410200c13000070301103100c0b115004040d0000d40180303d00041410010000c041c1400403440041c40c1ca5a1418114200901390b03211003039222021654240c11003040e0401803405030344000c204001c500b990764071805140303603d001034002c101c00300014055030801d500c049442c80c0094000ca0142c44c0111004020784210300035000040d140c2410021401481080030301035804940150401020640034070072590000c0c44162000803020034929001c100c0380b07000b540030b802e00360f6400341d90755004580506400368001e04514142e0040310140c1ca41211101500d0b0001e200c2d10b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 480168471 1250 480167221 480167273
    0xc030f16020f03030103030e040c110318040e190b0a0207170304061d100b0301091518060204061211090904020108060f0301060e0414161a070501022d0403 68
    0xc000320301e007801d44648601d1a11000001000303050308a11109142541107609000000340d800e0210303230360300003052946803d60060000320307801c0d00b818a04400c2c004000d00000f601303a04608420745032100c00000340c0720700e68010b0103110900141c0580d19900c011502419440d04595130385000c00300c0000c0c2403400329144003202140402c00660031501040c10024055203c008100c01c01c1a2034140703800b0300e0b042d0300b45000e03c02c40c15030406006101e11140c01c010040074000780c80700e0400c050300007548a070400700c1d00d441c5510700003180c1c0e1015001414080c1d903019a4410041c4511f011074600140ca11b0f1003d10078048040300d41d4503642610786c069828070b8100344546510740840c6c01c503840701e131b035199142d400c01802003082050a4002d0340718500440d2090050075560414031b0302d071040d40700081d00c0815910b4084c0150708102041d15030a002032030145240078060b8807050f003260480203030351440c10038840c03c2d001c010048265150410f040c40109500e004c0c0b03550340700800001c0040c12020000891 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 480169721 1250 480168471 480168511
    0x9090a0504060c0f0905060f09100e0a12020609060a02010905030a080906070c05060a2424090e04080f07020612060a23550303090603090203210d050c030f 68
    0x62000d440c007000000d0400700e180d40340301d24013030522203040be0302e540245403d82d800a190204182c51446d0303d6009408249000d02da24184501c540c0020300100070766403034a50150001d07008200a20418000d542c400d0380314244003200906003507000e004441041305005940c00032820200e541a00038a1014000505007600c0324480d501002c4500c0d28004c40798a800001110341240809203241161010340c2822038808000a80f10b05001c1d003d22812820f00000180000e090003000b40514444100c6890610b01e260740040c0180d0f00580740300320031040000502407282001d07200700002e00038540b0000c250f10000d44d54460071085600700130740306080d4104040103904000288800185850340085046120f140229500b0910300c0d074140b110f224010149100d901c80300d103154040e00d52580c0c400c00b025141c050100c0c0070b003c2c0e0000c180ea02d400342030303000c0044070508c2c2d207056400300d0014480c6845800c4625482e0494100a08400c9591010001c00c0400c8040f00d501a510400382d81250042e9900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 480170971 1250 480169721 480169747
    0x7030b011404080102040614190c0501020421060515030c011d03010606020c010206090c0108070311090d06050601020c01020c030a081e1c0c05160b06040209090a0504060c0f090506 79
    0x81c032855a440804001800b0034403140640080080c1e03403598640d481100c0c0204d16550641c481e6102d1034070340500081b150300c00c203482103031040d01150284002608040d1220007010049254003110800300302d60103042010800b45010341c4ad8001072040401e0030442d081d8021075201c1014030100c5040050a21178030040c11009e18040d000091301800030000c0503200e200107907a03040d400b00d00a002d0301c5032400040003644006406640e01006039078040d8151506802036018040300403602e0a4824140b00f001e8007038880b81c2e40380c4081801400007007130608100c800a41061410300280703046410243c1811a107071000521022901d600c0301c2115503038058100c08407840c49025100702c0d80745000050810910080710f030300500074407001400700044030b404203065403180f15192460704141c85850700040800c4529482660000011b0400f41c5003400050000724240e60444580c0d880aa6942c14841404618801c502c2240030741d0500342c51910780c40d00c0c0500407410f02e00c00c8a02c14800040c84200007a4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 480172221 1250 480170971 480170987
    0x8010311030109200406050a0803072d05060601030609020c19030e130506030705180622020f1c05091c120e03280e0136181407030b01 59
    0x41c02c64a10b030031003518004c0d150824642c84d650036100724109480032500b490446405002c5030b240c44001c601d41042d669400d08040c2050380040c04000043c14104060006171010b00300d46445003000d0720451400200150403070710245c00c40b4803e0351041c0410712001c440092084120400701d904100c0065a81c40c044440c05404115070b9080900c0300707200c010910f0540c00040c0120000c806407801291614140f0428460003403c4010b200001d0000c9184d0342402261036a802d12417050440d10690345036042c034140e07807003084e0300c440302c001c00501120300b4108188003110f0b0304000ba5083c006410311035001da58a1500f04040011342c00c012040c00200c0e4010f501e83c0503c010b0351a424003500ba8180c1102f500c1c0e4100113540b6050402c03031910b5901c4405203000f0038614141039100c08281c0c802e08001100d0704112052410381c45401c070881040d410362038084108800031404010035040e400c1149080c010784540440298040c24075040244244400b642254403141c40d147c002074000700740c40101e178801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 480173471 1250 480172221 480172223
    0x151309020c07063519050907050405090d0f05130510032a022d06010f030515060d02130b04060b030a061d01090e03190201020403031e08010311030109 66
    0x26100003254004800040350000880c2e1007511a9134036100d6803a00100340b191003424601c11912800400c1c10002c0f00b11a0781504407020b0701ca241d04c42c080f003407800011100182c46000d215804450200020b00d024003580c2e500c4a042c80c0584071000c3c40e01009402440c8604141d07051100c041703070b40300b12244808013580042400070068005004180c1c2e01400601c49aa0a0b070382c00c3c40804c015610340c041020310144c0c1020380d98001d04208068290b1052015461714102c80d91070951511807404030310400440740680f01403c5040745036469440c1451925881555808203030100e0010000d1559840700d0003d01142c040d982d10f80340c580500c1d0710304002d02c42042c4540c0d2003464240c012035581e240001651080041490411074661074101c0c8030304001c0226200d0b00394845d100e005201c101100d82000c64075605940403203003800c2c00c0d42c02000200402ca0007040043c1c0d0301003010014541d01464104680040e02040b5002410303202e4001c00f01c04050102401c2581908203505050703c095000952407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 480174721 1250 480173471 480173489
    0x9100617061515070f030e060909070302090103090605240102120405130207020d0606210804090b0a051c0b18031614030403320312040c05130c110c1513 67
    0x5445540303171920f0078110002c802e400154030311001c58900c2c140b20b812a0310010004143c03445a035903180c8110065407001d114181016150700907200003030341ea4050a4010505a44040740b0b44015100240241c6078103032505046600c02612441100c0614045901347e440913102c0c4040402c107058020060f10550b071009401c580321502030014002a41c0c0a02c00756a80404001c10090903180555400b4500c1c1801800c8070b102007008201801081c5d01a015010f4040c2c10f40000680d10000900104d2014007441c0014030784441500401c003001e48016409070f4159180080001810501c40c2da81c09203603481d03088042e0b01c1da991418840e1400305030005048410840e035035a5100e21307122401c5411001c400b20b141c0c42c1224202e8400d1980ca10f084030380c5041d0300095080206034034041c4201e05000c7c000f519403030030414000c182a15801452240b1101340d045c04a5101030030b03170000300161232400608a16805c98100d0303130410303603c5001c0c8581030031042c1011034a880b556140c0040c1c0000c6a403040b0b01c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 480175971 1250 480174721 480174727
    0x31712040b0702151e0702010605031209040603170301140402030f040f14030d0b011b030f18030c0b030609160909020d0e060406150b0304030e1003021209100617061515 74
    0x103501c1d100c160800b01e1752601200301245c071403400507403d9810034054a94550000030540130008900009015442030052010500c0765403525211403030004824503040f942c80010050100340e49412a1b15508035094804518518200c1001120107401503c01419000070740c040b0400c1c001c802d2803903d0008407020940c0c0d6070b02d01c6e2070710380f000419410650b41e022408141009644d9030400d035100d40b03c0d60701919601c01d003040380d40c01140c0311448010b131603000144041c40400881c10407101c42000c0c0c84491203917543c900f44802080300000004284410225800310207110441d48045a6421207110705000341e01ca0142092100c041d040408101d5000d204540810040c4130071a0003c000a8440703821201c691a19a042d6080f644412240a07002c00c00c14006401d080c2494040310b000001e07545001401c081020100581d44407080e200c441c0307983c4c4070089500e1030320124442d241c002c06061002407444003880d2080c82d02e50320001c09e84018107414020000d0382e9255800340c141244540031115139 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 480177221 1250 480175971 480175981
    0x15040f061401080f070b09091b03090c04110c0c1c0f050d03110a0f0e04110a091401020a21020a1a070f0504081b0a05060c07031712040b070215 63
    0x90000000d210781d806512604100c0c000c42c1d41d012525401b035400001ca03075444e0490070070510540260191000c4000a48004440203142018020358051410301d0094186009814100300c1558190500ba0480d80c008000d500f130b02c074100040d4000b031b405c0140d8004640040f00e401003a4483e40b1080080c081030503c5002c24108039022540300e100070140d490410110f080200341001c1d900079200c01c039021481002c0e428500c180203044100301c103003001304003107800c02c51241c2000c5150490010f000c00f10700c0000c1d06019004050440309400d40e401c1c40144003494075a2a4881c0b10919500d10b440078100c5041186000c0380300f800b400c41d0031600300000c00b45a002c01d40c0f03903034440402105d5400000b0742032016082d8040c410341c1117508807032a80008066800a0710315010300c106688115661081d0740d4800000c0a4440901400319448400041c0028501c0c5040020204040b0814420340440230444002007004076602141c0064101c040102140d0307e0b01c1060b46441d525184541d055034034082009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 480178471 1250 480177221 480177251
    0xc080c0f150c041d0405071d160f050d0b03030403050d0c110a0b07141005070c022713080f070f0203150c0301140103060b0a0f1b020315040f06 63
    0x1ca125044035072000141d46012030181c01c0e01903401801c02d60504440541c1485030400000340c0c02501a02c241d400da541d45030354482c04100420a508804040c82d010002400e9900c02c81070480c0d4880d0a118008000006004025108a10b4100c414503504c1c00780803401d881c00c1099070301031680401284c08079010f0303500140424814200442e06006a00e030350190030f007002003004049401071041c450618070107079201e80d45440c04100e2000c451046041c0c448000709503005950040605458000300b03c642401031014501202742a4a100040b0003001275142011b04a0540c0c040301e80040d036101401d19140c8000c0038420b1001100080d10041004e009110204200c00511842281128648102001d02c0c90b01d903d42150401010001880104074444407a0170b88004020149400191641c03551020a107a4102c0e001800001d291183d00c40500307070b003001e00c40c060ba00c11080c4014402e6030941c00a580c94421024070316202d10504081420010707285140b144240d40803070f0030711911124030450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 480179721 1250 480178471 480178483
    0x4030c0b032e060807030e06041103070911180123040e0105041e151703031e2401140706141e2a0403150f0614010c080c0f 54
    0x800300c1c0c4100c0e02603040422a000e1801c02c0548a81c001c6908640c40c20354180c800400007800c01040c161641403149502006001041c030031807043c0031404800e10340005251400184e80c03c001d4a0610b09547c1c0004c1d03883c24006d031000204180c817480c0351040c4903c01280c109040c041a00c1000c501c81e04100d043c40a200040c00681e078107141139544503039891003008140c0e005c0c521402050706a04075440f0042d0354903041241c08a483c07072440c4004c59900c0d00c00011000903039560502541003c0103003d0155414400e010441180000b810014140b603000703c0800303a644080d40128500c00d11071011075034012004500049640116181c40e101a4200f0f4406040416000c01003e040c0e140001c0450052000484810140c21284600740d60f0f002c3d213110601810750012200030707078440c030070030032a08900006102951142107003185a00360a844801558402c1905401d22030034150184038816850f4004641d5003070910f44880d181180d0f08003130355148034120303488026028580c0b20726892200000c00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 480180971 1250 480179721 480179731
    0x516090b0c011e050103050d03020f18121005040618080f071109070f031104060c02040209060d09080705160e04060506040b120102090a050414070807121505011128050304030c0b03 79
    0x40e1a141460040209e003248140040540924005c0c0440301640c4144078907591a844003610382455901c50303d03481c918100000304c00b8020305880700100b004100c2c49000c2c0410f5120006180d0b10032013010765550685014084c560103030508c000c6810341c14098081c9151440c04400b810441c06410490401404c80f920031811002090911041082498491080300e0854005035507809400b940307035081002a5201842055110b02c0c01e006c07100103502d01e880703030413003103032140c15195a5581549091410322020180ba40c81000e5000403c2140d00b40082c1000d902641c40280020030342d9409000500402101000a800242c08070300881c03601e030154001c00d0603403411581800416a2202044261015a50758514000c030990119014601a000e65500124030b0b0420b000c43c0c00c40307410f00c0b5080740c044440d0904400c4213003104000ca07581000b40d140b4200310b003102600b100001c3c60701d403c20b06d42d001c006054001c00c400201c6400e001003403040d40d002e036601c80002d02105640700040c081540040e56 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 480182221 1250 480180971 480180973
    0xd03091508070e1c020316080d03060b0a122d0e010605030309010311070b0901050106030c050304050601050f030c040f05060109061b0b07090306020304150516090b0c011e05010305 79
    0x11003104054041c0418502c5100700d6a07560203104240810b224030030003100031114440c005400a080165030511140e0741340400b0070301c0c10f5580341c5450303100ca2608000502410034149886802d2000c803690038200d6000351101d082c0b600d10303854114a044001c0c00314040005d05820021420a514036120040001c1f040c0000780a2024aa85c419024200d404038800c41d80c0c594820441404554040d411141064a0540c41c050502602e5103540c5660441220b699803603940d500700510143c1d426200300b0b51035000300e107462429443c041d501d00b603480006004851046c215222450401e513010030018000c0340014109000700340012801401900068511a011070000100412818491030000c10112819542c007400f041958461044140f0040e20340410004080070200c0032845500040d401039101d9145100982c1900000b00300b00c82c3c001d4042008981440e080f200500e038024800e0003075070003800385591341b84030110344a40107100d042c1019074401000309000811425960007641240c3c0a14 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 480183471 1250 480182221 480182249
    0x61215040311070b04121e060207061505010c0212030c0a08030105090105010806010504031515120b0c1c0506060903060124020109080418063b010f030206030c090d0309 74
    0x480c010f9140d800ba03026070005a081400104540804088400031541c0106000716101303514405241c6201002d030000c0d10007a40005007001000f100c0c0c0708030b0f103400991010180f4140e05203c0000d0010420100180c45680c81241304100c1440030701c1280c2c41031400000700d1384101f545281540264100b44070b2588101c0c18800000f03455402412810f02c5520142e4981c2e15080c02e641d22940d40010544112410075507444513150fa1261018055028040e07a00a400c94001c1c1c520742800080c00081c0340c855161414003c60070041d100f0001c06401c194094804200c995545004c617885000340e103540c1d03905205407400095254500458030640070100440000c087c2c40741c4c0b906030300388c640c01c0740001d04040c000c00040243c0c2c5a041d085000541a0b1140490303030a5481204001c0f41c64400700c0726141d500c00c0c0c510124801c0c46852915015200c540c40f4024640c50140b158181922a10000e8014a4000300140c0c0705ca001c04111048a0700c0181a081095294100145451003c0c051802041602 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 480184721 1250 480183471 480183497
    0x501300609151d04050a0821071806050702060d09060c120b100e01020c031c0f232503080a0b09250302132c15090612150403 55
    0x2c40c01d42c815212042074240349030f500e241020004103c010820b8501d40906401800084c1c04d0000405484010f900c0048203d10201c0d1101529040176003c002801408098060000c8031520001c1c1100d1050511030307201c0c096400490942d111301c0c00030305205850000c2840802c14240c0c40b24501101e05e94800d90624240a81034045484070b146d0a41e100141c405046403030ba108110000031840e0601c191051502030001181c80c2568592500002511240c017585065502c0b0321134240c12074040c90405808550303d407690310401c01c1442c0001440c0000135441d501142c0716241c2c04520890342c0b00d1034032211641d08008220791026200006040d0800c0d4140d4010310300082c401d40a90644c00000c0c00408080b110102c07005950b02008050603028081601c1c41d4580e003800b1002041000d0700007a101c2c1d4110843c1e81c4140880398009920340d01f0405022485d03c40c2c1e600c0352542002690111070713540f03c040000302c0000d80c40d4a81c1c4903a2040100c40d00d04c0c5010100110f006500c641ca5007008c800340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 480185971 1250 480184721 480184751
    0x31b08060106050d0504020d06140106180f1e0f030506070e0402030108060a052706061017180705060a05070c21030c06091209030b010608060a0501300609 68
    0x42807050b03030000707002030000111301d01c01c503845140c00500c0100088200c010541e03800b419a020300c640051030034203800c0100325180c2c018200d42d0311160303801a01c1c0140d40c11320044180d04078440c000d20442110f170080060146060064030005481c00500c4040f10039a071303180640c0d039400c00700d40c06000101440080602c0703061070700079641038602c290060030440e5900c400041c010440100140d10811019903203203071260000051289a03d00e600203800d19103050020b10000b4011110310703208000000702c902951041c0c0002c003941220074131030400e102102c0785c1001c0b4508031583d00255404070000403034003a0241c01c00c005021031032007940c034005d0322170340c61050814540c00d480015610b11050243c05000038130540680c44038520402e40011240710b161500180120400c84080100b8101c00c810310034000d248040d00d0041c0928503000700581f90500124a0300700035440713070034140003680c0c0310070b0002c03a0354070344e103001c04098108000b800c40d03d8240010702921070780c17051101751882d1020100280b0a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 480187221 1250 480185971 480185983
    0xf0c080f0303040f0f0203070e1501080f0705030f040c090f0c020f010908090f010c0b011401020610210503190e0f040203010b07030503090703050706050310232404031b08 75
    0x18025104c00c002241c0ca0300c40e500300f0340680030120303450f001d8104042011000c8868007800340071121900d18001d04907a001401a1001414502010300c040c01000348641d48081241d41c4100301400d00c0440340c0711441c01d4501d000aa401c4403403003a00704080000b000240354021141300c0005d9084400d80307010401d180e404c81d0300025011307010080400c0440100c0c01c0a0744422482001858840038503115502c50120000003a04503101c0c0c0754400c06444403079a410421a600840030398070750705200d440c0c0041d4041022050300042c0100400c44410300030b000c801e109407160b004421550380c1c2d9214100714010f01031101303021501c0c456901c0c90781800c07446c201882524162107034001124030380045078909581980008210000c2803040f082c1c00f1001910a0000d2001440161501512800e0189910004000701e80150710007100c1c10054021000341880501380e0050290752880c401200a10422689040c4501645595a0008002040084140d2040c213204200c120889050b501c42c081152140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 480188471 1250 480187221 480187223
    0x406020a1b05070b0307020c040213030302240103060506040b060703030510120b0a0b03030403120905041107030c06050a0e1506041b080a0c020a020d0813090b0d031107030f0c080f030304 82
    0x10f400082d0512494180c44015034003c0c0c41401100c0b80200d0702c02c0000d003a40c0c8010720076140055061410400c05030108400c0e0ba43e03001141d488243e004441c5001c03c1d0b00c0c0e4051201508480d02c802c04180540c2362580154a00749024001542d0b502d61410302401411082c1d62810481104150005000c1000d507103080b5501c0d401000c04040e515460a45c0d03014048695046c2d81c9400104000000036002054100d100407194403070440b400c0c5000200421035155a40d8410364500403c0001c000950113030b02121501d61201d80040c490319540c00d02e5006103542103050f8410301c10115000106a4400d00710361085008031010b11440452510b0440d01004681400012801000c0824090805c54010140c0324199204440f8041d1103900000c0c0c411a29000543b011440040e00508161200c4440b82c00703840e0f044802e02c1600d1b02032011440c10700f8182d0010382048000a40c2e082c0011050080074015070704807003c200d95040300c1c141034040360528855040316102d205924002ca110100c2a01e12407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 480189721 1250 480188471 480188473
    0x1506020102030907061d10110c19090f0b09090304090f0603030e1003200403060c0801081b030309030a11130902132d1e0b06090d020d08030406020a1b05 67
    0x213a45828019204c800500744515041078242d800c1051980712403001d4803a41e10117540741400c140941c0415030034031100c01800c50182c40180c20300350107181803030f00750011906216400a02412940300602c010501c1d2864143e00030200014089040400006001980c031401c10070803050000c4100181112017501c0001d0120b400d40c0c00101c40340c90080142c0940150a04022840900316580c03010b0900700c51500c50341d030001c0442c2c181b05101c5144682c410302895030800c480c803075050251030759440c2c0c1080c912852042a60410303441607141801030700c8003d0b1014040b141440c5162400401d082c008900003800741c2104050b1024900c600e01646075010780140201d100314580c00140e0000d801ca2540d040750350105d01402c2041007107980000034602c80303207a01c00034001c020303040740c201d0031009403000505607130906d04021280d0791740e8802c075400044200c880c00e070040b00074804111050300d00c80000e0081c04010041105100c4107400401c952174040e5540c000300e5600511084210070310007009011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 480190971 1250 480189721 480189733
    0x203040b010303140f0a020106030b010e0f010b0309070305011109121204050d331b050f0a170a14010509010608040303090c1505130504050408161a04050115060201020309 75
    0x101c0e005003140304020701c0790311130340b4030b0003110091444c102c4c1d102e10031180050f0354901003003090207010b603200760151185985d048540d090a60400380001300c107004d541c0764114004041f90140c8400c0010307038002c6074040024024406107002d003d84980103000e074680103480c51801c0c5d42440390042628442c2a0f0824110360403d810b240a00003001e840340000c44008a004c80184a6107009440a10a0400799100002500b1442840303606841c030380c25801c55800e00e080c4601c080d46820200f91244440541400d50b2241110b880842c0c15101000700d11052041c02000c1c004059016042a4454205070102d0304481e640d400a01001e00780920501001440708800300340043e111703400900382103000325540c8c00003603104d12105130344001c04100c5401044001903000e02c0130b500c00d0741600c000e20045034201304c00d29090301d0b01c3c65903205210901d141f14940143c10b000b080341032550085109480b0b00045071070328040c900701c3c0c000c014004040507210240980010828414002c9034442c0c034016001e802 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 480192221 1250 480190971 480190973
    0x60e091002040b0d09021c060b010e040b0f0d02040207060e07150503010506070605060f030706110105060405060901170f0610060206160915050d05091608030705070605090f030706030510090203040b0103 89
    0x40c00d1700c4a041380d00400c1e031034407000142c00c0e440044181d03034046c1c100020082c00000026000710144844a4016070030101680e5141c0e03101d40152403944002d40d000310b00404d035880010024400e03500001c204e18507044200b00ca00c0700001d01e103000c1c0c4a8000134001d140c0d0303002034140c903207000034814260b018008000700c800042d0b45400c00c1d0380052000d860803140c0040c010009040c0340540d040040001d00e249050301c04c41c002402801e030000303015030b030402150030001c02207000c0307802c140100d40015039400807504c041ca10070000d1001c1070610038282d40b0181451241c0007c0d036440303886554014480c00c0c021440404071610901604400703074940ac5003080c6007a15040300302e0010b80100003840000d1140c29034444d5540942480782d40444003402400c1c0d03080811810f0029079401286050780306000302c4000440008a003401d07203c250600c40e4503550743c0d8000907106000ca0214035014061148000703841501500030358014920b500201e100c0c40e8480743d07a10304038042118040d09804440c00108 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 480193471 1250 480192221 480192247
    0x307090b1008010326070605090105070306090501050f0105030403090f06020d03060603021201270908030604060f0b090105031329090c010215070e060f0d06050607050a03030b0310060e091002040b 86
    0x1700321914450030308080e6191603040031600100c9000465035115070400074180c3d41441b800f0080c043c6254108017a504000125242c4004824064140203001000c24145402181c0840041c000310340d0502060703460360402500ea060000c40540030a08008010031010300a000b52444046190460200c0b81e184c969603021503125031540c1103d070707800508202c50b02046070048a00850040c180b05130750303042c000140001c45e200c40c2c2c03114190902c0b10100303001c0301c43c0310b50481c1c8142c1401d107485504c90b01e8516a003a040100300d1001400c030b8451030b204040708100c103d01c40a802c4246900c840982c0d41d03021a40d42c4501c146802c090050300300c4000800710494a43c0100d81100c0c02d07180410400f4200408102c0503401641101036150011507046201d615a00540000d80401d42e07906050200696400341d403020b400e2001400d06444008501035518100403068407000c500f00d05000c1c140e5140080c0c240c0a01c280e0300d203c454007400080c0c440c421303828000c036012036985020140c40c0800707040b840 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 480194721 1250 480193471 480193523
    0x114070c11150c1b062106060904180302010506010315061d0409030203120c120a0b0d02100f20060403120213030606060e0f0906040e0c0307090b10080103 68
    0x8039407081c1400e1a201c0c0044480b00500002c0c0c20070780003005141c805042c560100003850b0203643c441c01c02004070000c80c1d02a0a401c010303400103550b04a44503194507001481034018928425000740c41d01c40d00111500c02802840b000c94000d4008000503207400004400392170320b01102c000072180340c0c00c041040c0c51141006020000030304d6044103011908000090554080c0801540160f101003080e55030100c0b40c01c1a65044a00c002d4420302c2c1000d50440182102001001018087c0e503409024025403500400c400b443c0750300415002d603544e24200e001d000580c11901d907100080d481c01e00000d0024940b0b031110140300c4400014407140d51141d40880340c042d0941c818401d4541c0a1101c2c1e0070510044c44120040d602ca1032000c92400e01f00741c0d000b4480c0782e06600b880e204d00031402c14140303191503070010310340c02510603500892540b04d000c15142c50300360f8044c1c5c50b03605440b030b08200040641c004c0d03101c0168020b0403a00f6055040309075400f15049442800301074034441c855a03d8088010381341c204 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 480195971 1250 480194721 480194753
    0x7020618150108030408150f063304090e0304120209060a0b130e06030d0c120203041205010c30091103060a0b010f02010e03090603041a0109020406020114070c 70
    0x481d03260310500c07052040204000e9000640340c0c0c1c00807030107008081c8140a0620701e00a41043c440c2c8174942140301141c03001000e460030740204041c2c1c09040704082820b13887d1360b0031100d0384d0094501c0c00500c480d07054198414850780303a41c03a2520760740e64a130041c080b00702c0f000c85004210110400c1080d408014064001900c1c26034080100030000584c48420310103890303801c6130171444c4185140362030310014482e9402484644240c0059010821036508002c403603440d15080f1811250324840c07440268510f11a03a004143d0101c5041869010418150003c00302d503c81540d035408000040c0e044558490309105040c40a501c80d01164501c403841c540c84030801c24090b800311001107000802280c280313101514400c8a0640b501c0e0032841650304109a45080781c4144000c20041016010103601d034000c3d40d01841c8114000404034043c4452011051403108a443c04540f203565a03942d040c00940c03040c49420050b50901c0c41d02318a83d0280c506040c49a00c0719103c0d0031851580d0380da0440c1417445001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 480197221 1250 480195971 480195973
    0x181b0302031510030b090f06010e0702060714040b13051503011a160f031715031002180a1502071a0a030e100c0c03090b0307020c0d030c06022106040507020618 70
    0x30204408012442c003034600b030303000380214000b07c1d9080c03070424005803c1204100030501c24030880542c002207041e4070039490310340207021003140909006c4a100d40d50107080f4841c03000c02c810742000d03080650b030002c50780112032000d005102c006100207140403d100310540305c041a4200f498402d150001001410503511300c10001044c2e554a015000328940070550009220300d8002020310080c46103560001c01c00c40000300d82d80030940c00a40ea546001d2942c10343d00e0b03000305041d0300042c4210709030310755910000c214003911a129403034404003056514050380144162480001c0304907076403566880c034040a042207482d000d6056010b0380075001030020800503200f0038100001d0304a03a84100d00b80e41d4110b641e0000400704600303009041e078405402805091000304280194541c00061481800c40b0586401d503080c1c886003400d0720b80c03080042000e04001c0c00000e607443c03c000102c6141541d9401d004040c00075440d110288422107004807000341c0903038000000328030002041c1010808001da580 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 480198471 1250 480197221 480197251
    0x5060c0304091103222f0901030501020a0206100506040b0f07150605120316030818010c03020d0e0312040803130c0b0a022803080712181b03020315 65
    0x51841c22030f020700004074a144004014848076816865200c40f20700c540c0101c80191a0f015103568400201703040403c20411101c55140d8650880010b0361001170740d00804800f41580d403410024080d41c041c00e903110040c010080043c0605114039240c03c2951005442c0034101402d000710105c5552000707480b42e9200300d00b07100307140004126580180240400000108181e032030303c418080c1c0460b00480a0080d904240004c1d800c0b4064119400300760368062071300401d942c581c00302c842054403846c1c81c170170415401c1500c0e04280d1a01500180b0b1f00d03560081041000d200816042510381c05003801d0501d00b40c28803070120740440d085d403010f160480c4450f1900d11314080c0d240d48a209800c1594454203510344d001c100c0080140e014000d04202c12000500702c010070034880b00902841c442e02e40300030300b8030003503101065416100b10070091901040e9001003020141002d45210780041500302120250785140401c04038210103c1680116a4080d000740b5250400c11445035501c00e00500d85102c06c0d440d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 480199721 1250 480198471 480198479
    0x3080919080f0705090a020a0c0f0c03080310030516061e12020a1701050d12030c0e040e0a050709020a1b060e07030b07090e0c040504020a0306050a14210705060c0304 73
    0x2801460748980100008264a9144c0b80030321101880040c140c0c9122071040c8050480310382c0148020750826803101041c410301c2c006240c003c4c0d2504140c0c00c043c0c50900040204640440c0d10030f4107134141c90140086600060100c401d204460301203020b10000140160071007004c0440746d0364881040302d000d0501081403400801c1c86000c070b800846611300000c64541140d03c0d01101060f41134007401c001e94410100c07210549460100d00240c1400314201a80d410580041707a00c01c265444040740c0060080c010368410b0b2084903034a8580c1141034030a40902ca400064201c100d00c2244d0080c8480d8407101e4280d40c4240c10609461041103054400d2520343e085c84013580c0342030007140042d5124014040c85414206001041c4400f260400402004d500050204082807041500c00300c42c400c49001d0b80d2064151001c50103000c25901264011703808100102d400103808164000c82d660039070301203003d6901000c1c65001c0f4007803000902c00d142c105003400c1c08181014402030091400304422a4586591 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 480200971 1250 480199721 480199723
    0xf09011b05030612060907180b011e1b15050a140a0903110f160f05030604020609012105070f08010f030809120d0503010515070201301d0d090308091908 67
    0x4646c03182c041d4101180601410f03405400c03a006075010040d042214100107000a0700b0825081c2c0c0e03010b13000007404480901d00c0d12441941150410340040c2d1404c5a132146070444501c84107510080d052810400040c400e11450300c14036462588104915105499880050380103015084050f000c00c444034458400100c01000394081143e03030500200030001c03441d401c002962081da0400041d003040706004003c5130b036000580350f8200b501100c5140c0d0711801c142c0143c9801c46951291070391141c040ba25201d05111907408540304580a440c0d1007541081d80700202c070f4502007409165200ca0703100c0800d102040c00200039001c4540c01820720451814a0490030345840301d00747d0740c8000140b000005107d1400e11990001c1c41507003a01016080030000d03400030b40f4228107851354650000c003424440030848040909841c200d1380d0413000f082003074100040342ca114228031249940c0da10a900070780071114030a90740c0b002281c1d000224a4142501c40c0204031407448043e03003911400700844004101703090 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 480202221 1250 480200971 480200983
    0x110604170901020a0f20060418020f0d15050423040b070507080d1e05010303051207030b0a0f0509011d01030803100515091008090c0103020706150e0f09011b05030612 73
    0x1002d2414106c0c0c54691006042d0340c60820f02a05018680a0004000e46000154040c0c240940c0240150b1030344050b0392801c0c001e0040f003c910f444681022000940f046600308180705554083c0c5007030012084455800c588800300e0202c100d030104240d8001408909140c510031340202c2c0300c0c078011340b6001d95500c0f51061030700101d0b0368003c041d0380d82d0301c11400d40d0f0070782d89036546100f48200c09021315890358074003800324041c0142c04488000e0308400100040d1199001e40c500660050441050070b4950219650290309400b03100c0c0505003001c00881c0391903481102d9880190030441c0340031039a081d07668821540d040900f004c0d0080603904400b00792950752181500c0b05c0100700b180c02d90cc52646501308500c40c034002d505031042c0032100060114400001c035092402c6c100a0034007607550041c03441c00310020038403c20705105c40704100303101196210b02c0300046801541401824055616031004117801c8920303040c2c01c562203051144a010107607024401450b4441c80080102105580201382c0343d041c13107 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 480203471 1250 480202221 480202223
    0x31809042909010e0a030c06091a10050f0a05062209020f0c0d0e1c0305040914090d050f04030f05010e0f0c030f011b051b07030f03110604170901020a0f 67
    0x80c0d07000c0811868000034400c4502c92a0b48100503c0d50102c10f4030050310508074048003414043d11125040140a50071a0891441000c0b0074040701c5442c1c029030382829940ca42c0074691181800c2d482407091403800040c0f01054a03002031031249800103004020f80c00400410900b41101040f54001840c0c0b400342c8003030b2174850b00f04400b1503541e01e42c2c82c601c541040013680b01e40041c4000400100e2094944002100d2044801080955569514141652180a00c1d840182d543e0304140b5850740380c6000200003406903081c40110785a91201050076a0b0600404d010f0b540383c0c02e8144810400b160394191410503160141e000010005030740759003e8108841e41d4590040c2d80c2c45103500e0301d11814200000081c00c40828000c00c03034914400300e140300c40d0306122440340401a012031050b0052a801032660760501c1680116640640e076490320611a800046003a000320344054195090b0100c082034040c81140e01080703105188030b2200b030015035504810b040301c0c118420006201d000484010f0410070f41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 480204721 1250 480203471 480203543
    0x6090b06100315140d080316021615050d14100f0b1c0e01060806040507050108012112030f0c08060f040b031504061509150803180904 59
    0x140c60039a00348030318055190044010545010501200d0080d0210603030305460114951103114160034000a0320041503400c0540301500000501c00c290340d1011903028505855000d880400780070480500b0454402c1c45184015034800520603010f40c4035200074a4581c003410390000d411580d0b00c90b00514000d040b1913031000d51034041070622100c48030000d500b0040500400c80c514007981c080360110000d0302d000460080c0c1e515083d4180c0111020b4020501601c0081c040b5500c62070309040c0690341d03400504c900d60200340218008105191000c80c03010241d1140c0f200340902d420141d40c1c0c0b0140041106840c1c01309941d603241c20b0300c0c44075180120000000196107014103070400a04000106400008182c4940c0c0390000488080d1008a024081c011206250341d4023030f0348600f030040141a142814200c9010041d0300890b102d2410352240003440f149408100c489526424019031b64030440038104003404201642a405251000e60154494814038075414003c440010201c000107001c0d4194440b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 480205971 1250 480204721 480204743
    0x120807052502030d020303271e211303060b06070b0403090e0601090f0b0d113016080a0e0d1101050907050616172a01090807141e010506100e0307090203090a0609 71
    0x1c03018050b401500c203141c601c881c691400bd50b81000c641390a0103448010f0407640c40b29060001c0d07a0b12082030724482c03a0400394a00551502d45401000705045018030012210a0360129445522800c1c040c019039044464619070f0754104000e50138140c111000b100304032600c40302c0ea00c01458881d009003868811036000d035808041c1e50000c4c520000b00e041809520710a2100400c00100e00d400480c900101c401c2c1840046901c5543c541000351500001d03030141ca10030721b80c1840510307504c541d081e0080304400c002080191600959603854051921030594421000d000c0805c00d070102d00380c2d8504c1e0340d22810000c0c01ca1455048451000c0d040142c006079603c81313a10081006c8050380941e121205074500080000034040e1b40c96400074002d0f40c50144c5040711514040010260030841d0038010818041010b00240184c0d42003806050308981c4a8003c0e20756003030090f0243e014a44a2103240c00080260020500f03000d1041c00940008100049600c55107514501061030b134070404c1c150398082e10001d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 480207221 1250 480205971 480205993
    0x602061005040e0d0c050328080906040f03120608150105150406020709090204020409051801110901051c06051005070501051003120807052502030d020303271e 70
    0x8000500359010794040d500344800e020701200d0202d0b210b90030084500b030103a035001d41400e107185540950201402c143c50002152001d070714506407a10000c02050740c4001c410399440c2c1405440710015a0700402c110310700101240060b014014281c0c0031280d54400091603075036406401d282440c80c20b1115100c02d641c1c001071003c0d052140c1075520800d00500884d00d00341ca0004025901c0f4111b00c0359516071669002a41d003103603030b1030301103a0041021400c00e03c03160809074a142e020440d030b070005030301641ca409880364142032103a06441010805071101810000d455440103401041148a1146541e480c9404106660317444002440010540c0c1c8030350705c03a07010345095030844601800407800c41800940410000b00042001007458910746000e6030b450701d52035070a980c05e003c0c1c5064074568007001d07a0844038003d00d010001071018021402c840c5c0001001400740e0700c0b07101c180c40740b4032074808042c44e03149400c4960405180c0206190111008007a945203c00042071041c10080803d07000740c41011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 480208471 1250 480207221 480207241
    0x5070e180108010e150705160c061e020d02070905250f0801140901030204021b010513050c0a031106030c1c290a06180302030304030303050709120206030a020f0c07060206 75
    0x44c2514500344d0042002c840b04244521803403000601d04c404000000541206400804410000341c80d4007c541f004482e85170000505000201e4007011248081d810591026510010b482c0c40400200e402402c0481e0a10400c1009010010000d107020981030341480700c030b800b0344c0c0d00301c40b90701d200d59a80c010844014240100341d48011390180c19400c4201e000c416143c0e071211501411680c0c12030740182e81c0c420040388010501007404403080c655107410100301030b03c19240342100f40e0510507800d90366188582c40400100b02454007000d060003032070790848195030801000640e0810aa291103030708000c6409001d0700500d003640003648119480d10b107502c6a0741d4000c41c1c2c58003910040c40d022508442c810300400c0b100311481c4038200c01c2099440702c12501d28007023105d40000c2d40c0c0141c1030740d40d00c9440341000340c041c110603141000000e4280c040001c50303103001c10312010400ea0007801385203551a4400c00c08042c1d04800762220b201a02040a039144d02d1041000a00502c0e0a8010741110b02d440c862038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 480209721 1250 480208471 480208481
    0x11090a051e1302031b01090b030c04060f020a0b0703060e0a1a0f27160801290d020d060306060801111207021c0e150a02030d05070e18010801 62
    0x4440018180000d004a8003400c18000039510007012014107595030305000750032401840c4101039054091021440e43c1c15045440007981c406003078840500c0c0c10b942c8d02c6141c0700d03440101d54068100d003003800140400340c81820380d034010300801d10440302c4240c441c2d200c6110410b0700381c176030901095491100300941d250000201e60320900c898010031024483c681600e41d542d40c0300071124800c0c41d10341d00c1e00305c0c1c5503585900c010658284009120540903560034072203001c0d4080e203a240c5016000c182c0d0314045445004142c0c1a91100038040ca40c6509091b0160000c0359030f000c0c5190b00401c20b20030308800c501948080c000c9640407800101d441451410401c08580c0f960b00b221040307905103800360012036260350440b400200b446a02c061165180a01281811f009000c2403803841048548030f4016580820020740c6400c044074200c8450944141c0d491080c4141d000d5507001da0000c1c4001d103954000c6903c41a0f202410b402c040c3d20792031148001034503d060211503601d01030000700041c040c4040034460 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 480210971 1250 480209721 480209731
    0x5030a0b010503040f1104180602030a0e061b030405070509090a020a142119050d030b012c03010e0709020a08010b030606120c0906031003030806090c0301060c0813031109 75
    0x4a00d50b06168452543c0c00705e107448081c04108201c140e11156440381d510203400306482c2d0201d00d00d010107900d0580040d41c000d4a40880340c601386000c07200340c0c003008603465020700c0e00218005d00340d443d1000300445641009105854601908000044548408603c0e611404409025100300070103841040745009554100c1c4406034003010302500c440d2182c100c411403079a1042150950004044101c1f07241092020707100050000d50880b41003006000280c0e02c030340c0c00c00c0b0b4070140702404000d0011101a0380100750300145805010303d03005e241d2044610340b204800050008158a181c00e0622460300707006900c8481c0d05175000400901d03490b4001c021501400b0703209001840d6007070020020300b050040034000031049941c440441c00c1071081001b01c50000c100603142d141c481c0303406400300840308038520056010400c000c000681510301181800c2c400c43c100301100e811a400d10344100c9400010007011103c1090230030140170700800390903041c8001c51103a42c4c81044449010184a804040500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 480212221 1250 480210971 480210977
    0x617010803091c020409080c12090105070f020334050312040509101a03100e0712050601050913150f03030206010e06010e120c091f05130e060705030a0b01 68
    0x180500c1401104840140d1021590720411840d114840182075000ea04000e520070710b030011032010461103001810045540d43d05403a52040e1010980c1400d115044038540016410412803000603c042c9101c03d5040c0054111410102ca000b40603414141406c0c00a000d1543c031a0269400c038131821110018040c00e5010b480085003400c1540d20b14000c03401060711800c6003100040c4441c800610100041003410244590450f00603011145640140da000c07000748441c60010559030103808003103014400d05d94440658805060b803003802042e014001070704000042040d1512a6103402054400845c2c90800168021030445503984c00c40142c1c1c01382440110500042010940100c0c000e41180e407040d2400c0c3c80ba588100040b81e4041505001c1540131065200000c0c0f2a800040d41c1194020103603001002034a51920f030103200341181242103050400c2000c00d20080c1040001c140104140d40c50200300020354030611030a0640031100e06002420110400212881380c1c00b84c2010b41400382 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 480213471 1250 480212221 480212267
    0x5100606020718020705030c030a0c0201020106141804052d010b010809070312090b0a0c05070603060f230319030e0105070308010b0702030f120a081b0403022206030b0106 75
    0xc00310580803c400350300003983d03030380c040b81c10f04c01d101c0b041c002c544982c0d044100740d03507941306d000501502100d8000c40580c01907180040c0410080042d9035107a59107400140302c42460440041c0d10b400072040140125070034000c0f200004510b801d8002004501e040075400e4103200c4038000c0700c540c21903004c0051a07040191074418413105540c003064402c140c80e00302407490101c030003208060b1882d041541c8880140ca2001440c1d210580e400705680141502c140d06840981d5541c01086068945d0350003414007412216a041051f5130b1010144281c1002c80a20b00701d0740540341d00042d00305505405148000d03040301a03400300b0507074400c4003032004130400d00b82541003003e207490080000c5414080c160300c950340000e020095550801c0307400c00b406a08400c03a00194201d80c200587d68100b0b40c801c90107e45041c0c0490388982088007080c052480d04607005080c2031864080001d0245459401d0b500800c2114150344501c405010b080099070141c070008806501d40200100404007842c0500280341307a44c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 480214721 1250 480213471 480213479
    0x61101050a0c051210050d150b01212d090c0803070c1203051201030c050a05010314040206071b03120f030b0d1202010f140403090815010e04060612051006060207 71
    0x4003050f41c043e00840b4050900345d9990303008119140009400980e8446420f201e000104800c0034015001040c1c15503040c40f864041200540b85140c5806a1183d0039040c4144010031029590004580f001180005020300002d05c0e0f10440f0f03601c083d8000d44129454a4600e8180004c1801c0c2800038140c00700254034102054a4080c111003240c02121000200c001c2600d06051103001560600340408038004501e50b542e10341034141c92854440d0501403503466100284660113131040e107070303032004011800c1195550365080101079400304a044407004414100e6282c038035513a45216020358842c100c4140312450600f00900900040740c10b40f405c043c24404800030079140c1c404148890b82d0f2003403100c41c5115403100c0076405844002064840307145010f14100904009500450089000f034890420064441c0c0500d030f150016444140c040480050040107070860390411039034064020900092110303140c2e1016011107440e8201036656500850000c491420030748250380040140d40002c00c115454 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 480215827 1106 480214721 480214727
    0x624020f030a0903080903030c0a05030405010314060f01031e180b0901060f0b091306060c020109080601150507060f0e0f07150e13090c061101050a0c 66
    0x28510340d040390100302004030b40c960200380d40d41c100341c0e07030542e204c0382c460350310140203d501031008100c50100b4a2041c02003000725846900510360303030341c41d2a0005061b61030403500e031a9642101018401141e884103001d03026104282804258454040300001c200301c04141400c81d00e038180720021f60b0714080090740810751441020910801d4a900848508031003050145141c100319880091082c00b00100c040c158000d80200241c03012841c0c0d0010505840c1668481ca0110307080403080c1c011982c1280066001d855184000c0c0f0966151503603685100c403c286981050140c00901241401095049240c24044100c0240700000c200445603558000403158240940036445000c2407250749404080c003940e000b9a500a41c030302c804802c20030510340c0a449401e400d90f030755034588000303a0741d1a45a8000d20080d146c110300d082d2410303440380c29580010302d0408070510304001c1008080d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 480035971 480215827 := by
  have h0 := BRFrame.cov_init 480035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 480035971 ≤ n) (h2 : n < 480215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
