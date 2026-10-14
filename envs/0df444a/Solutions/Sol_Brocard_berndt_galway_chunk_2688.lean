-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2688
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:26:20.768434+00:00
-- url     : https://prove2.me/submissions/b83169fc-557a-4a06-8425-77640cc6043b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 483273381 ≤ n < 483453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 483274631 1250 483273381 483273383
    0x120b0906060108040b060109080a1a0705070b01061b050f0d0311120f070201141311010306060e090a0b030d0206043804051024052b0501061205070f080703 68
    0x16010b00000e40440c01a05c00584c1040f018148030b0003c0b030700c8441c01810001489411351b021840140c05003031558104915550000f010310301a81400c000b0b40c2ca0070142e020601c103a00810400100b0031200b0b400403122120040c1d48a070403103807401a000c50035074941414103e03010110345005008207600f0000001c079101030012a800d807020b80c0c4c50064a07044e408000c2e0150f011590fa580d542e02e03c984e501d048a50085040e120300002c15a942e02c2d001c040d0081407a0160704140c20000d080114a4002089006074042103030b9010311035460b002c070000240b040080c1c01d80d0505c41c40042280050b004200140518016003c5680b01c2d620214075440518041d103440641800462140802005400416400506c54010303144580000e21088060345d06951000003542600c051120719416a441d000000b010141e64054100405120001d41c000080302084000c440c041041e50400c002036200342d01509042d8140203408c4d0a40c10001c0c1c0d80c0c04940102c0840e034210250120358400001003040032a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 483275881 1250 483274631 483274637
    0x603020c0d0804060e06071805030304060f0815062109010203041e05010e070303050316020f2a0310021b07031502090319050102030a060f1d1f120b09060601 69
    0x41c000d501c80031140d10700000c1054a0f00d80d42c44102c500c254000388501400303280c40e9503d0f103030100f40345200125003501542c0900e200380e01c104010407060381c005100c10410059400c00c0080d5030b0310311000700620301d001000d041e405400025031848240c003002a2070070951034a8203c1c00d9035960300b400c80f403c071320041d14042c0400750354424a818145110180c0c0300e00074400c1c0b0000c00c0032018008054070b444165002180400d03c00b104210313081c1e031010110308121100d03200410502c00d140d14066200c0300c1980c20b5008002d582d0b003400b039000d0341040012244120103000c4503c100d8000d0143c00080d0000c441fa80151655081c0d10060007800041c3c048c00d40790410b0400304160020440303030b0000e50240c1c0900750140140081c0070154400580020789040c00349001603581d28101481c10b082761202c0c1c024518242e5100821b001e001100c20303c0000900c400000c8600f20f4a900b00584040f0394045645600e108a880021880d4072603102c501e46c1051060084040355100d03100c030329072200000ca50b03280c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 483277131 1250 483275881 483275893
    0x306050618060c0f070311041a30030711010504030c06080a060302030118110a210c081009030201050106051c151e05031504020a09020d060b220603020c 67
    0x140d003150756681881150028010343c6400481102e480c1003001600384010b0300c0c1c0015504000b8003c801034400e1041ea0700305e07800c01c4501c080161180740041c8541c0524010703898a00010706480315140001c030321070489036071554031240c82a202c41e070308c1d030100500315014015208214010750080303040c0e40540e80e1004000e10300d0f5042a00072200c40c98000c04130084607403030360000000750300c0c02e214010030312144d01500c109000c082e0803c81204e201540b80640505048a410810105000c0c60030303105002c24100000c0340380141c00e1051440d42030750008051401032801d88000b1400941c0400c5001d8800c0d0000e0103981e0b650b45068030103015080303104441000001c0241c41182c115402403552801011010f074005484103220f03103026050f040011809031002500f4400c914080040400070114a1304801c11403401c0d07408641014114410032809a8000c641d607212006107402c604060109600d416407103030102c810a4548548000100304240801540403803483d10a00031030b610b44120f0801480 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 483278381 1250 483277131 483277147
    0x30406111507030902012307020f0409050d021f0b0907032003010b091206060607080307021c1e020a0206090f13060f0f150206240306070504080d03060506 68
    0x440045224400000d4040c1d05040100c070990205418062102c43e82c0019010240d4800582204503115076443d200814400e031924100001085481c0c1ca50305540e070314420801703007010401810105400070700c10f001e01c3c0d420305045940010141c42c0d2054a850101641003600d00341c1040369140c150258200303005c10002220b86000303420840c54048140450815059a44441c003400c0c1c0003a00620203108000501c0591450324000307414007e490140038103094204000043d80d1842403540040002d8404000910710310b0091011000b00c0218415400c040d86d50000002e2a500300c01c0f440c10804425051240741c000e10001e04901c4484c0e0140c0410f107031501031030402c440860500302803648107102c407080b401c80c844140120002851245181e8a550703040800d0b034581d414160308124000d849441034202034030303800030746250041448040c0c2814041504050490500192500394142c0324a00900840c558448010811100550240d60000c8295041141510f00e14468254010800e00c1b12034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 483279631 1250 483278381 483278387
    0x506041101170a0203150603160e06130602031312120815041a090c1201090908040b0c07030302011803081609050a03060e010f0204261e0601080c12030406 68
    0x4850308105041c1503842a040854011180c5011244503000307503000700520800c0c1c01d50b1402c1042c803c0c0211425810351528000380035210031101c4091041150002544080c0c0e11007008540c15820150307400e0040e07584441c3e019550b40e2281000312080c4500c9800006c48840000c1c07805580b59008441c0320100142c00f10466514030040d18140d145c500c1402107000755540e911802046042465034000401c1c0c03210304010030310400078940807001000700003048d5a0412a4003050548110310307030024403c0010f040c00207031030240d50130117205802d000600072a240e00000b054000c81e4460742c024400c1c09840181002541144c150043c04185240e01044400c03105101c84800c003032480c5405070390f59581d040010340305070442e4400c0c2c91080d981d00a5070007a40084c024640c0d00407040c43c0962034640b901d05c000b880003c04500c2000003008921001031003920502034000f80390401640d1100c5080517440150301d580080c403451001e440342204c1780c03000342058020002000080340c06181440d180a10035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 483280881 1250 483279631 483279653
    0xc020606040e030c0f0f0607020d020604060c0e130911030106150c0212031209010510050d03031e02030903340f0f020406150806240a170a0903021504050604 69
    0xa550b40d80418000305001d24000c0106000c0f2092507001401d06640d1450181d08100025060008642002845020254000840ca600035034001b40c00910304511600489203400000764071a0703c0b400034400000400c3c07054100b010454012400c0000d5103181000b014200c1d2007038030508201c009410f0b00140d000f406103400c2640c4500140000b240040141c10039410342d4024400c12840391184802d21070302003024415a0341c041ca64407812509541008000380514003044001010141c40740d40310310300c2c0e0860905030b406204007000c066407241440306040392280c001040320b030920302e003581c3c1250f0b08101c40110180429448141c400c0c1d145059140c050740003254100030f071a01d03420311b5022001071301c035131007000010071a40d07496803401550020b004101100182056214000e51000c2d040c0f0654041e0501800030f018242031562401000416a2010039405055200c444044104250a101c03a00003845031886942601d00404d016030866070103080a983c0030304241d21032070000d4002901d074001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 483282131 1250 483280881 483280901
    0x180e01061101090209010803270109050405091504061b081005060a02031213060c082e0302130b010f090e04020f01030b040e1513031202090f19180c02060604 69
    0x410000196008a02d0b440800c7c2d0141803d5440041c1264118907011700c01800d1a1201d15103007881c00a0b040000c01544250198912542d5514086a031400081080c0b4150412201c00400203140ca41491b07002401812000103041c0500104581e41502c100e9030707d40304121030250202c54505100921400e5000040c80c28150320041044500003080f103c032003845198003031510340405a0a01c0c0031010f4030040340e203440038030102d0b00500400c0c15140b1110854184070111160103014810030841c43c1c80e00d644d00207900803206500580d192001c2d0f42100071401020f80303448002c102811011905a03100d07210b0305e01e403500b4010200340145003401c1c4080624030145030200c2c410841400050894280c90081402540040d1803c8001000214210340c0f00003c00c5841d044d000d603503100a000040c4800d030050016a0010f020b52103039030766251107080418098003d13800e00d486a041030180000354007802c2c00c00c42c000c075846d800303200e018041d0b0000003107294083c200c243c45070b105100180c052625 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 483283381 1250 483282131 483282133
    0xc031b07080601170c04110735032401050418021b010903030e0c0102100e030c0a0b0a0501050f0a0b030402040908130e060402070302121c1a01180e010611 68
    0x40e000603528010400035019004014081041105000305a40f0b0300c20040340180c080c0b4203040d84032440c0d0a1410507960301a420225170f0788540c2400040b407602009007400d4410190b895280b0030242d40004029503c41c2142e0040240102112400d08540761448404240060401c000510101e581c030340241180c03040780d000c09424000845000340d8220881d00b0389485aa546030014002e03d0f515010359101c00508501a08009400c040000c4d200e1700240851401b0300e440d4542101080420012607a0080c4008182c030064000f40c50047c1c6e0344d400c291542919a4108400402c031840c00e00c0d0401c1c8040740003000b00c84090315003410808940c0004006a9100f0396810448022805c80740c010079040f00b07481c1e41c2150309800e1209030b0201e1030b00078200038022441404010006900012440d0510b10725640b400c4c1c0b00d02c450101410500c2500c1441441d041c00d000700315400300340c00280300e42c3c009400d0325881e420301d4030f4020030908070f5540d1003000c0341c2c05040d030010080c050251803041c5034107905c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 483284631 1250 483283381 483283393
    0x2070f2106150329150d0c0509090d08011a120a2a090609030b0621010606020105100e070806011d04090c06030b030a1a0c040e0403180b0c031b 63
    0x14901c8454031180b0f9000703682d001d07040000341d5110700d0190301d070741c0d1125640c2480c40414100348111205a034260340c2c240f4002c0c3c260038100000d1000380d100e85401004018071003c0c444c68200c0a280e01e0f4015540340c800032031034013070010440c1c5200e902030411100c40104083d0070401c107040c20941a200c05403007841c04641e200c1844a540200315140e001c401a41130401c20000d90a0000410f640c0d91a44a00c04100d0300003418400240440040c41d00104112000c03501e00e0f04a805540515130a20700240596103004800a42c0c95019004144242c280060b42040c4664034044028003039000ca0b506070004010340c000880542c0183e12100030036040e02c1002041440540215080300c00d03900065071030031302c62a0100302c0c0d19418041c003186044140d014015501d03441d038030055642040c40444145038085000680c1d1818004140d5005005140941603142803c3c14090f11a1601c14070000b00300003c400049001000c403400c803035a075014100210324101e04210402a035046000c01c840d5280600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 483285881 1250 483284631 483284651
    0x70c030c050613110103110d02070606050a14100c0206030402042004080609071208040b0307030908030f091b0a03021207030803071e0801030f1b09020408010c02070f2106 75
    0x400c8032600c90f0f54011661961044241440e042c61059003a01ea810103003802c0c001c1d0342c2c1100c0c40054400721081d100000da210f480900c1d040f4058080c40c1c00064000004410001c0c540d84401c0034010702c010161116084c00580d0001141e00c4442003a020307400100410200f00141411b501c03818091340310392400c10710814581107256140d400390303200301c030903600100900c10101414460300c070003802c142880010b010019620168640228424180e41480c0800084d10031b1380640c02c81100d0a0703000d10307400c0c0e9a18040c0c0c4c0d500d004101c1518104040d101d480c8003c461005086140030045030000e01c03014290303240d5801c01c804981c200072103002ca400380b0f90000001a000c9000303940030740d41d1610707078bc090180c0c034264200405001c0c0e540001048184401000801c00040f400340c2040c2e00044000791a68504886030901d001550024240d039100042c0041c2201c01903201104802d425400e440483d0745d115400706003542c2c28000d40c1c2507070130051001440a00aa00781b160908c2c807800d40468840308c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 483287131 1250 483285881 483285883
    0x7110d11061602090903040501020607080a061d01081b0906040908090a03030e0112110f09120609010c0923010e1804050a1a13030e010311040f030215040b03070c030c05 74
    0x8059185040c21440602d03440c218685155210b41c44083d410045052900d1706000030342c5c903030000d400e480c10b0044030b00c041000124540c2001024009454800503007007103003038102c2d01c008400d10038800e203030144107030408804007981a4400303035580c010b00c21a519290070040000030502c54900f00c1d80407900f0410104251284114a00254001c0e100d0007040844400054448480e031090702c803a16240c0f0606422070b04d144002d0301e00a408035071200340c542d08148040348095510b000b00c851280721300340410024880541212001028540d02e09210130b540d035620001e605005211807094000207100e5400652142c3d500a40281c0c0c010300314140c0c02c507600c0a030b1840b5042034400365025080302036403505111520400c03508a510700d40e114a801e00c4c00910039030907014240070040400550040107881c1e40c0c4681c009110500034500b0303440d901e6546110807034000640c0d10049010b548100c081e1007410444001b070703c044070816070140385150307502c0604546046911008038140100e12030380c4004110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 483288381 1250 483287131 483287137
    0x150210050a0b0a0b0c071e03050604050601081002040f09090c0510050d1415010f09080106091b0302030702060c0705030d0c0f031b0c060e070801020712090501030207110d1106 77
    0x64901e0001000d1055205005407200d150b00320ba07502200412201002d58400500a01140e1441514a100211401c1c510400740400d9002a19601c101c10510090050118425040f103a100c0c0440b1926540c003c03c080507030050b071203460101196024200300c0c0304200d40089410520a0000680302c40c2c84d8400202842403895024002410205103441a480c0a1140302c2840ea8103101c000400c0c0b0b0110042061100d824043e0360410910762003030301c41d150117900d600b809401c80e0340003807101c035484134982c800402005010004036640105007240d130501a00c2121b0048542d03a029001584d00c17800ba4009030b50005800b283e00d444100603020070508a441851200ca401d55201030b500d03ca0988010150750040350003d80481d405a00c2c40a0719030401c084d584150360000000c9030382e004041c01a814034045070b00c20803c65000060b00b50411589a649410241040e06c034104035030345480044040340100312000304040d0400ba82c441c42c520f00540303001c0360a40712740c4441c100c80710310720089030140d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 483289631 1250 483288381 483288391
    0x21260c030406030c1419120534020d18050d0305030103020f150a030b04062102190506030a02070602090d260f0909060d050a080316020105070915021005 67
    0x60008038040c0105039141c0550405134a191906510b002400c2044003003d00c00d00582e01901e084035400700b8038142c0100c0083c045054003803010402da10b0846040b51540d1161103062960032840c6080307806036885094074850740e402c0c40d4010101d02d40c2c0e02c0e4040d54803e031421049610b4040e40c00c400035080e035440003ca2003144c42960f4031903d03545540306100d00b980c40e00a19520461001c1140460500698141c0b2030905081c500440d140c140000072030001c024a4100b009070f50114601c103000f0f0903805401085452080d1110b207010350b40103040b241010200d003e415440072040020034554011500a45070950085500501e04445c0000117900300d00384040c1111071049251061064194130809030038a450401484d030724120b0085440d94884c81046916403182d0320003c04a421900d4018803080d90b5680801200c4118405007001c883c2138000f11000c01c20030000d1901c00341242d1044c0540750103100c05d529140350050800c00303030480c60034179088070900b1441005d022001c249880d0081902034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 483290881 1250 483289631 483289633
    0x170409020c010c0e1806010503060409020a080c1009120807032105090c100203030c07050f0607030b0307060c0302030d0504080d020a12050601170a020304050a020d1a0121260c 77
    0xb041c1e0f5010250521086562851080d0ba45241c0501c8486004944582c04402440c0041d5251307078040004008003482d81c00650011203406001c5001c00d800a1841041d410450b02410403104125003281e41c41d0a901503184814103200684000400c00c03c00f5052051003420b1200701855181d100d044030030100204126882c1e00c0300706003c0740c60710900008103421800d80b11100101c5080002940d00d00c00903005442c0e2210010740c2c1e505008007441420b00ca0f000e482d054911a040080300240036140354a00e0074400e00454800040300c0d070140c410800040e516030091070400729200c09601c001d00c0d00810649182e03000304822142c0868610003014200100d0b100c0c514020400f01c81d0100f1168010280d9050080031401915080d5401e0345e0b03142d21208d00b01c0301584c0d07640c89240c020300f4910542402904081c0f0680000e04100b0355820940d8001514401c03c54540c1ea00c4403510500f001c00d80c0040203010051814001045441c500f00042c85290680384005000c940e072915a1507210082034801d03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 483292131 1250 483290881 483290891
    0x72306060a06032702210d030e0705011b020112050712060801050633030c04050f090f070302070201090b0f1b030c030906070f0b0a1d1504170409020c01 67
    0x9261641d5910060701051030b00b04040c80c82151030300d04461003150340c00e1854055411060442d621614038080801c0400e0094002d98a0b01400d559108020925000800d040403c4641109000144102102c0059442041030103503102101c140e0326603918140e0410800b4050448015800d02134a0300600d41e0799500038100182040190840b04140c01c2154540d040100f070105942e9154040704821210b048185d4030300070860418440c000e02c110400d0850b400c080108440504048043c0c0202d660554000c2040c204040070410041c1e000c0f501d40341c020000030007184c0b4481c0300741d0140804d40e1042c10548080c6c0d440c2c1c802c2c403140b90424010320761101030000b450750100342c8200c1c01036130490603071000b5414100c14441d0280caa0265245245c0100804100a02800a800780e503112290300450714010b075003090704581000d0070b62401d091028207051000300e0070140000510314400201490800016265035aa002c0da400801c841102528024003021680391010320040c50000c4600d000055 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 483293381 1250 483292131 483292141
    0x180105120105040f02060901020a05070b1308030c07030303020309030c100b0f010801030c06080c19020f07060207050a1e030512180a06080406050a0e0d030905010b0a03050a0305072306 81
    0x22580400305103480150341041c040c00001a001e0410b130120070750403550107480c0d4a0f1100100d181020b4140b010384a440742c1200000c083c1130141c01001030031280c0715410442601d42420310780c1c0c0d10038651a03032443c1e03010a10420104c0d110740d01135904200e510007038078a0070500c3c02a2524009482c0128014660303100419202c92401100b110f1b900f00c020f003411034256140da200d01440124a100741028000304000040d11403041e10100c885400e00140d1300c0100581c2030702c2c020340e240d8500382090060b204001001c0b40d035a000107480800c40b10001c00f0514401c1c280b51103100780c24a405950140884a084003000040d0140314004505c0daa0240481d00e0b5248002209401c80500561a000c0d1032079040c140203603a403001c1e405034040d802600100301a00d4004100700100080070b08004d00f4010302e48014a2541c1c1500091080307400b41c0001c3c0b169080080c10050988040c0c400102283d000d1403101000030700810203404824098000c01d0044490141140c0132429200c85094041d0402c80402c6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 483294631 1250 483293381 483293389
    0x6150922060b1b0105060a121104090813080303100924061205010b03061e221d16030311010b06071a070806030c0d080d111b0c010c060c0509180105 65
    0x4003403401104005e2099082610100e48030450380d010f609100e040801540043c040e204210022180025004000d40c1071142081000b48d00b00e81001805103d1180f40090303020347c004260703402404680440300c1803500e802e440310020004075605142c100d550240700c2c0c000201075544080180091b88a141d80141351507001000c40303005811440d03080005100380080c60311841c854007140002c0e2201c1503032030905030000036007205865041d001c0300700c025503808080503a42c0d0413018103542c0304541c0c24010031804400c00d4032401409402d00c154407000f402040801d2041203903618282000000140c141d8410010400320390000c2820b41d2685003813846070420f410048009503020840703180c0032a80e42013040c0003039280c0c215a2641032044142c0d01541c4180620b1104a40b62006040d20401c0a1601d1001015654203c1000c0c50701d140d004640c03400c00d074900480c27042d41c0d410b01655010b034407423802c1c2e580d01d0040541d10203035010402d09202e50390700768035080b80909050000d61a4810590724010800c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 483295881 1250 483294631 483294667
    0x405030709090308061c050a111e090c13180218030105062805120606040e0d02070e1302332113080d05010e06150922060b 54
    0x822028680805103010a6004d4621030b0440011500080d42260011000042c00240c0c0005030050042202000802c050582822818201a03902400c580840a00420038810011505410001610006010028540040200d003114108030014143c85000c0000e90b40440401995110703030000e0660580c103501c0c0ca200c41191401c40080c4028504080452805401103140d0a407a14404c60080340340390b083d80004004d0071000e0b00002d03000c0410b421039559102c09456150003a441c01484008409001c03c118201d814031307070010f000310791915502101011004056000b080f041d46460001a65602c007034243da0428000d104810700a0568514020321503680c05011401080003040d9913200303c03800001c40020300f26514030300c076a108100b01c0000a400c900090640100140021540c1c0070703940040e042c2c1d00c02c00031444969888200380000c100c1c44940c10320200005100c21605450b040790318906c030460321a000300320f201441e03103000c042c5c0784550840413100002060351002c0d20b8844500c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 483297131 1250 483295881 483295889
    0x201052a0723010f022802040513080304080a020a0f080705070f080a080c030d1103070e01030c080f062e03051303090302210a0308010320010813030c0c0b04050307 72
    0x10460110850401818030020b4806255051000d642400340082d4024041200b038114000001903d07001461404d4041c010441d000301d103e9440c10002c981350311b02c056402c0007400d80c06130072a1b1a540341e541340d5080c140c0240240108611625110000081b81c181c25401c6040c070909070075884000c1490414107041d502e0f0452010104040010440c03428001060021751350816040c55880c007400c180d081c00c5114810602d00568201151010400140e0700158403504e40799031111311302c01000b0011810f841c0e02700400c100290041010440540541d030b1038036040b16004042c40c08081e0503d4000000e41026140902c00e00185600006000c0c2c0601a40d5480000b50b5007480b4400345640d0701802c0e01c01c03030f1300004c0c0c014400d032000c80751940e4680e0402e03500c1c260760504454901c4843c0c0380c02004030100340403c8495020003da4010740101b00340044d110040140c440c0071407503680d1700d02540c1c00800d0007410307420004440c080c080440c01c4a4a03c2e8040d00440360903580c0c0d03d05120600d840d00c865640 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 483298381 1250 483297131 483297149
    0x3020a14120d1211040510050a1103030717090c19061b0b01060305100f08070510080f0a0c050f0c0604051509102019030f06060e06070201052a07 64
    0x90700b0001141d01500380c641001c4000000103100c034441546525502842d0461600081281c42840310150800084c100d0003104d40d8908005c02002c044041d01c0707020688001010a900c41004d69400d03c0c10200315911950b25802c03103600305c9007900010307041c00f441410202e110b004000c051242944c8220302d10344150010b10049000388141d5540020701e80148110810503503100045100002802c04c0d1000401414101c00c804985488a09465604038882c041c401e49076005a414124000c1003210300c10344035400058015a124211100586006550701d0200107013001801c69410060f80a0080c403500200244407a1900c7e103845890302000343d1104440001181c104141e0600000d22480c03641c8400c00080f840c112030b507110340441c0303001e855034842c01100480ea07181c4840104060498a200c1e0b60b4080c4510803031400d4040071030701e290051000107288100c4c21405070900388020800588103141c028a8114050121014a1000b17691040301c60344801064188900800404002d400100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 483299631 1250 483298381 483298393
    0xa08010e03070609050f07060305091009030f0e010e0d14070b03160c0c090906020c061008190c090603080418020901090519030b070c02011403040308040213020403020a1412 76
    0x80e00c0d00d640c0b8001d00e50300a00141d100d14500c8104981408100c540ca915902101e2000341c650703d014020344012180344000e4441c1740510281d40400f030141000d40341e00354030b5804050a8a24040756280d42c4001c2d0356050050343ca04521107034440d144554450b40c020009510101000c500c01800e00d0300c940e2241c0c8280d241801842000101d100560700355841c9030502100c00d02c1d440c9040f10100600d9030000319541d00c1c0004150503c501d1740c0062031501d80c014151905a6030b5804001004041c0d8050804107501490361100b080c9442100d811007940289540404180d0720079481c4152900c40e003040f512884040f03003c000840d621450a10340681100c010b5007406a482c00082c40700c0e4031445445e00c14406c403031325000912800500f0070003460f000b01002c1e0071860155409000315482072422030008040c24002412100311005607801603a15980d103805d662915000c000f0801154404c51038643d80c20000000141e680c2202440109125a0038911456008041000300030140d002403215410103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 483300881 1250 483299631 483299651
    0x612050103021804061b0f030b120d110a0606141518010302090d050f06090c0103050c030a020a051624020a020a080d0216080d060821160f03030b0a0801 67
    0xf405002c10703000b112442118070355228240000503000c04140711111082e840c08290340e603030b400199020300711040e480900403000400184a02e205201640c00c2e4580c00035000220b44904c60302055800d00b00e05011140d0780c03c41c64603030508840003544003060385084d103002000c00381080e07100181c0b424409d980359404d041e00c1181c2480a150b0403c241810981d000030007072030035542c107440341030480d402ca800c070341c0340401c548513803580c0f0402501c201110b840742c401d91040035071090040c1886020362000d03030381c11515045110310294014410b402e040c044107100010100c1e241e882001c44541c05085160700d0343c85d6103440080130f89403100340c1014407401007000a100d01d8000030780012469009440660310344450340ba140090041031010328a11500850403000d1065190150043d0a0080ca0030032405948032946a9102c10019901c450b05100c4208221110b0104002e40901c41404085820f80c0980b641d8459803055203080807008260355011a0210b0306050484202800400008012100c40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 483302131 1250 483300881 483300889
    0xa230705030307050c0904082b0609020702300d020607080a0e06040209070908010f05010302030f21090414011203030606020d050f0904060806070c150504030504050618030d0306061205010302 84
    0x16800c0198059060080480d00701702d906e1003210384441d818284985404414160275058500b01c40700c5031809401c107400424080010310840d5081a4014200c4400780300303810500c51004a180c1e0315860302112071081584c0810300f40400030500405502a1610303140290b4041c1810750042c01082051740b525006070100350002414a80168040395050070b19542c4a404650324119600700103865400d2200c48001d0144917080281621703c228180c03200d04c0e800c60704681c0c2e1154050744012080f0701803000044110b854000500caa000302800200d02240c00411034600c080b8280e000310410921070310810140b42e410301c00c03900540070b00d201604040852803401006030141031001080f034540094500c60a90f5507a22040003812240f095440c0d929205c2005004110480003d95800c8001c0724008958081441441c3c403c6a041e15007078142410541440131640040c03600e180a0301c0e80a0f61600b041d40c080040000c800c0d01039070003040a80c28800010b28040c010f91054200700d06240c010310042c3e031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 483303381 1250 483302131 483302143
    0x13020402070b25091e170a020a0905090a0201050f0906031005090708010308300405071802040302060a0f0210111e13120305070c061e050a021203090a23070503030705 73
    0x6131410604084005d0942442d0441280d64024620203400c0308200e0384040380407500052290007101e00984a980d905c40341000e82c0e008441c51a0140c000440040056005801600300411046100c900302003402c40411119841175039650300d07031040244104102c0ca4516881d980c0034499192000c015491a0344400050144101c40b070084c9603407080109408504000110860b200003001c01c82d5420b15007080f903100c240c04d001300c1c1c4000510741c0805c240c24115008680450354080c15a920f01100c80030304580080480a030340c000c41c02806111a401c4040e0700840c0f51442d0b107518140d6450b020860400b40c0c0260182c0c10034944101404031031001c200541501c0204c0d1082c111282c090f0341a40303003c89e070360721810300d00900030042c0ea80042640340e800ba40b201d00000e0301d00740c40c1c0e500b1040100700341c1d2540100000d078001030b803100143c0505810380d032024540080d03014080303404000c05a60340b9413291808440d00716500c01b0122006015180400038032000b032009902651070700a458950684800c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 483304631 1250 483303381 483303389
    0x30806010e010e0d1110020f0c06091210050702010b0a1d0916080d02010b181b04080a06020309060a05070c17090d0f0302120f1213020402070b2509 65
    0x102200070300c080ca9009090700c08048000a040b034050241038a0240c0d1060341d1000b109014254004d1199100b030b00001da4045084240c1d8000c1038082c0000d02000745960002d4005c0f40c20500595a20f01c1c0204200b10080d6034120000e408a514a0440350082c21204420803803403107144422000c1042c1c800c40341010036030060174100801103507a400c0701079203000710548205681407059440019079841c045a17620100c4001c0d4000e010181080e010041300e03e20450301c1d08031019a00012481003c40c90b041e58140707041212119040540c0da020307030360038581140b41c10342c2d010b80c0010821020f420b042c00180e600c4008408204414200b180008001c00c890840c0180b01402c08202c80c8800042c89040e00d0407010010001c2502c00824504040803401601084002d84104503443d061001c0758026184101401c184071030038005160f442c0c245213480513100c0b00031350144142c4500962200d000134240b250181c542020141405200719400e130410720203c902c000b03110100a103015601110100840d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 483305881 1250 483304631 483304637
    0x6050a0b0105032a070b01060c0b01081c230f071b030f08070812011805070206010602030315060c15041a04110402090f0a06030614030708070b1608030405060f010b0703080601 77
    0xe100801035441c0d41c0f28001006d491a200980001003040e4054000340c1c1d4148034071203501550f680d80c0c08a664418a5280351f00340d1080307542c0310900e00703403081e40381400c544040410144101d0761b0018101407540261188540940001516400e01002001c0456022110f4900003c580c1c9540c9465020000d032540017060390f00c0008414090141035010f85034400c1c220b1035400c0d45569100b880303a48140700c8003102e500482c14000054402d0380081075842c100c40c0a40c026601c0c44d501c44070302400000402c851640e10140610180114510030008201e2032201c0b000a42b41d10308181c204002c030345030b8000740107004254178800c200001c2e01080500e9002002581d015071555254400204240c0e100208550015003054002440700c3d81600708508591072160540c1507448044241610b81500d80942a00f99016070340c10003140300007500410780e00000d0b00030b65013070410302d81c1c6070b4032998020390b000d4880740d200000b4040d503003000c800c440b4010040c0441191404a999401400c241d00080c616814 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 483307131 1250 483305881 483305941
    0x109020304020a031209031502070b011a120c090a1e091109030a050c100309030903120201020c06090f070905010e040f0c05041d0606010903020a090506150706050a0b010503 76
    0x11503e407180e0307000185034800c1201c4150f1041190042c62454036100035102520100e40032100842c01e4801c50303a036590480341681e0350380e08142488601001180b04501156010480b071001001002800342c0144540304807503036902c0d110300c104010441e81d41c2010481401c6a40072103144040310040d801210200d0b000442c12001c4c405048581e40a61881d80d40c041c025421101d0070060b010410001011089505802403141081c0c100c00300c031034608000780071864090050000c40c42c0b807a01c2c039411046600c0094904000540c42a080c03040640f450074040e0310000c50342c03c0c03c01c000d01a0350702801c1e50040400943d850504280c01003400038101404440c1c1503120340b0280081403103c4406020301070410f0003801142d0703a0619030011b00d007261079000d004007004218558800e01c091000c0300d400400c0d0701001410722030721000414001c1e240d01d0b4001c2440c1c0342424000c20350300103000707070314010354001506160a03d81c031000d580c9000360700350404c401041005416480941c1c03e6032080210904501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 483308381 1250 483307131 483307133
    0x717030d050a090b07020c012003090118031a010306111c0e10060f0e06120a0311010b0307030602040e100501051e0d020d050402281a1b0106210503030109020304 71
    0x700030643c06202801c0341040d00200801141c0000d0004001c000a03a07448402c59401310201c000701d03070700e24581400c0b9001000070341415032154030142528079001080e50082a82c03079036400344a1004204a103410405003004006100681c400c503200c0c002110440742c40e01840c80d80800f001a40522003846a9940e000090240b5008010074001c450050744204112a01c44603461a862031038445c3e03824089000001902d24241014a0b404442031000241600c2115581c01e0726450804822682550760b41d64034080d49035410000c030390003103000e03680060361217043c101c81c0403a03040010300740340b070009900ca420462a6486000c46141c800c00000500c075903c07608a48407030511400018a8180740089500203500003298040c2d40518800c550401c03a00340b002c003206410740350540002c1142d0760951070400c05001105d10004003a40c181d0213184c5403890302ca039210320401c0c0345514824981e5440c2820b10406449201c2d002c1c81300320640015a0302d052a035502070b51792205008080d20340d90080040342c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 483309631 1250 483308381 483308401
    0xa060f03230114010807090e0c240f030601170720010617070f05100c12121b020c220f0e0a0303050f180a12022a030717030d05 56
    0x4184064a00028411202c200c042603440f07010a0080c03514502854900203800c0c8528030070b80c41e514444501501c5c0e101501d40400036040304003880d002c0c2801fa000000b07004070021030000c022040300000302da42c61342884800101680e006010841f00c1c03c10040a224007650804500800d1808915100303000d2041a40c0380b0303014102c41d034006c0c070b02682c0c220b05140c01e000d03010401405a41c0803510360040076548408118044011219041c00b103203900c603c80e404036030140c804529417005410944c503c000050765141c04c0301c50302c03900c075450f80031801e040003000c0354140100311030304d98100c0c2d03420228183e142c0c0d01d40c150120030003003685030340c5d0b0341650343c00360300c0242c01c84e050a00e071f8030040ea0041e00301410003801800701220240c141e001d101d8005220900c80790030403d50300d04400001c1110324041c2d84c952000c18004030390340003544540b0721003020f0b00310f00d0700319a0340d107041c5032800ac07801c00d82d400181841c1c0000c68002003420605403003920840040002031b182d0701950110b01042b1038640c13400314 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 483310881 1250 483309631 483309683
    0x9030905041d0d050a120e070f060806040e030f09010302091206010807030510060f030204090f02191d04020906092a091f2708150f0a060f03 62
    0x5550081d0034550494440e010681540710108035510036100c1501d52a80100c1307291042c6008100461100710341c1c07882d1940303558041c2000c1c41c1d401088910300b6071240360110740801d403540540e0000d900c81c42003100301d042034024600141c2e0120011810040d00e100d4070303082401100440360405501140340c0307810b03075180f02c031061400c90300e0025140c56503103441c6250781303405607800180c80a104200121204604920175031003200c08401c4041002c81c2190300f0400504440780d8203a4031510350300101710251351120550b010710b402160300c0c04050b0f4070384145003402c55800324044800d40c00400810002d600e94800d4150300490443d0007101e0355444d441144400d002c60030448103804450300314165038a8950008240502c41110720440490300201340f855002c240202c1c0c900021016600d40191900b8140d5942220724180e148110305d80d2104807481c0390400c003085801607904040c05011003a10b400fa0496000440028103211907424865580c0aa014500c00140512107581e11040b0f070544280302 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 483312131 1250 483310881 483310889
    0xf06050f040e0703080a0e09090706021c112d06190e070b0a051b1f0507020f030c030301030309170601030f0816050105040c052d0d020303070602041d010315090309 72
    0x91280c4503060a03000400f080711f20109140140b0700f100c04503111520000c0c45000703c132480d500902814000388500400030f07515102880034840b900c21410315000e4240400321507911000b44000781414410f001d2042d0b22180d503004809a0844400d108588451004031400c0d1180c0c0c41c001310b20070b40340b007000a1601d6510ba00c48004d100020a090b6112540000200000d150501e0311102060345c10010b81e88480141032165841146208070869a1400b6041a41d00c140e03203006813000da1296540b0300e400c0d580540304202441d000000140101504080c4001c060310000300088816a0303800c0c1441d036511030601010f00510000a0520304014081084034040c1030715500480b1055424500b55001c0d10302950216038480281c88007103040c0c1402c0310400c000401881b0080001d26a0703003c190740015a200076240c200c1e6502c011440035031410401490400d1086c4801a81d46207800351240344d00d03013607210041213141d032200100049051905105a0304030708103000a1110340e18a41611094613030340c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 483313381 1250 483312131 483312143
    0x70507030f150617061311060c060123060a0302160819020c010503070f1407020a030b070f050403120e01030b03070b0408150105031504051f09060f06050f040e0703 72
    0x60304008009038240c4200c1c84040058083c00110f07100c0c80c041c031a080c05445100e030310784d00001c0001c00d0b003c9000c54020116000351400404800b032000400c80b46e40c414088d40c05542e0180004002400035242034542c000d41008070200790604a2000800701c0c460740707190104040d0042480848817035108221050740e80d21081c840c0d0340ea1908505440040c0b46c2e000a14090f018a440b5500154026030440c0d21641c030642e110030400c0d5415130140c5890203548041055440c0c01e011440c01a00c0e498480c801031405071074440c0031441c05020040440122040325810072105200c100005038855240f030101a034242000c813030102d10100101c0061203088a007690500c03905400080d10a420401807064070140800d40c3c260680c1c5880045070341c9020310400d6055801859540d51b0790a10001e9135030898461801d441400c0190741442414801c0c40144c02806030b685c014400411003140f00c3c3c814000c0f95481d060149920b0b100000f0740e60409445003a014039114204100c082800b88062006107030b20403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 483314631 1250 483313381 483313403
    0x910030b10030f0c021209061803010911031c0507030302090d0c0b131202061801020a0b01030c0f1502100c03060f030f02040b061c0b010905040c1e030e06060607050703 74
    0x884020054100c4003e03c00101e4070f041e0750441036078801b0800510405507601c0d600d1404419034140030080d80071599004445110383ca441e510380c0d80a029440c8020700580340c1054190035031041600b01200313420a01410405d52504066440d040342c03e86106a406040c0140c0312941d44001c0f5001142001c4c00030450000b0501c045031150305440601408105512094003068030b440148070b80702e010001c0698000028482e20143e11003141d1011548101881500c0c1c142071591754040b42c008003a0030403242051070001c00c4c8128030a040c41031004080c001e44e010361481858001035111821a0207e400c0280c49030b04070703100c580c06a0040d60041609100301d5006c01d40d241005211480d1441c0228411402e10019a4452900006543c2e0340c038480181085503859425008002309044403900341441400880051195210301c5040300841560b01c8101101c0301c02a20300340d4420f070141a541c24149002494414a41d0014859038032800507510388c0d50355419810180c1c6820040d600081800180d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 483315881 1250 483314631 483314659
    0x60801080c0d0221010c120b0a0e07050708130905151806060c0a0318050609060a03020a09091a120303070c15020409020c07030c0602150c1602041d1902060910030b 72
    0x561200302d0321b00303d0356035004c143d0801030004e4054403041851550b1042030003030180118102410010741003501428030b90b00d40500781d580c203000ca8000484190350b284051208103e01d200a0007550f5026502030f0303204d41643c003224001400424542c07501301d22442002d00003001d03a11104111140c400355401122540b0800340f4000740390401d040610302c50341c42d211a00050901740f4400307441c09080c00500e418102201c0d960100c00035044030f60000c0c2048040203002410100d548a03400c00f907440580c01c00c1e07508001b0700601840311040f52421180e5401001000207240d4802c00041d0072550016900c00e150108442c450064040c64100780781c682e20000e51940c2e00c900010706101224400c07004055810b035100400d0f0388a6885044910030900351800052070201c0383c070f00400e143c0440a0b04c0d081c5480c00c50300403d007251408800005d42c0c88490a0740d05001a04005801e0254083c5d681c1040b0741c500355010402a000f080c010501a032500b5491101aa0081d00302008068010305003114000b59 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 483317131 1250 483315881 483315883
    0x3010f020408070b040506120901090609030c031803050615060d02030f01080f0a050c10030f111b03031302010c05150c09210a02010f12060f0906060801080c0d0221 72
    0x100380310b0000c6920550800283c110313412400e40741181d4004107030600b0720324028403584409500610160240d5695120a0001051445a045071500035510300c00c0080e10b5180150000a501e2900c1d0201c41890000b000010320026030650320403065200040c140b000c580119013a40a15044590440d0000c401c112110701590400390403107280100b154200600b040d00c168030381c022600082d096230400302c42c051913070400c1c3e14041441089885c1c0010800c81810810b011600f041c001075001110008600b82c00d4152020451381d0b010030000a18590b041050704010000440000281070207a501d80c0c070b40034040141714407015071100482000c9645051070004815a00403041140714901d1248804c0950086217007640a000b51403005040070100e540064844440100700c400420220a5220311804024041d28000b04054000ea425490900b105902641c1c001e400940400a40d280100400d0000050420028405030740c10703654060540045000380351070800002908404014008034000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 483318381 1250 483317131 483317137
    0x3050114010506030c0304240903020c010e010201140a230a0204060318021804061d0a1104230c0f0313050d02062728110901060c0b0703090203010f02 66
    0xe200d440350415a880d54100b0689000c00c0c3c50103921000e040c400a00083c810b440031048000140307150a048951000d844401e45407107000850068202442ca100c3d03658001408070ba0a5800340000d1228080303809882000711401030a030419251640c03210795004041c1082800740d40d50398400303940d45181140d013000c0654420300c01d0700002468a400d03008c4140421030744041c8207034000d0400641c0001c141c07440982c040041d0094940b60383d03c01c405105000c034400c05048000350100030340740043e0a414030300c010320841c0300d031035008078145007241000c2995032099822040d00c170782000035141c07290b0410f0343d103e00400901c0d0319031200001c1485610100c83c10000c1c00c40c0d10407000c441c022400300b42c04076118581592000658500100e040502100000103424034402d003c04440f030341004085402e520300320100082c411141481d1100c4140608002045030202040d520b4030107a526081c33009041d000d4080028040e10629004107110a101c2e400141600d50014008e0103070041240301c0d10000d43c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 483319631 1250 483318381 483318401
    0x40b031504150312021e0d0e060301030b071101060b0703030b041a09070c0f0515042603070e040b04050a05090f070302030c060c0f0a031d0d0c170115030501 69
    0x642050366400d40d407800e401a0b844692a26040e07012043c55580c1d035465042022000c84190302035481c0f900381d40710000282030040c9907050014041069003140c00351080351454143c0e170140300e0420060001c600c44101964000c080c0e4513000090110002180307005104d03a801031683e40c000050303542e00381549a00a140904022030f4104180885800c413911810cc3ca1080a40c010001c04000b0f80782c54083c200c0b440302540170b079224560188803540c405007003200028119a111200600340300c107220785041d0802145442411100390b03410018407044203400000c0c81d900400662060003052516590450981403602402c2030009040a40801000d00411240104c1d90f108044540208a800051220880703401801a003c901100800d0100943c8a5a196002440790058400c8803820400c03521215034025543c156102c8520b41040f4502c41d4140340e441c1c815200389500c800480c0610300c1c3e00007110100c003001e4034600a03026000c0d024242c08071414440881000c0c0c000180309042d080b419000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 483320881 1250 483319631 483319651
    0x14072603190c0f080a0203070c0c1701051321110f0a020f01090b030c0721030903171905070219050307020f01020304120f0c030f29160516050102040b03 67
    0x909689104490300b0454001d90300016400c080412a11720141c0d00950b00400545032096580007030352250b20500010360f0202015820054460029100038458240c01000701034140d048094151505003421000300c04101c0514003452412011500407440d11042410002c152841411030581050700c3c2c6007d080e00b03901403002c06024907100d620403101c8806680080ea0040d04507212404c107035a0a40180c04212580c03541d102040c6021070035480400c030420019500490304155a20780140042550001d0482d034200400521a035201205038110795015a0b00c1c00148680d0307003650032460f10190b2210040713031000412420041c05000320040c030090b4020349010b4104400c0b507004982c3c07840b480c407940c04070708004507050001803032608040b56070724080e49600384030540703d0320b40345400340fa955802c55030006114442c5541842801181c96400765a50160049107012440002560701018444040280004007907100c2900c0121010b10503401000842d00d66807500078003031044e40305030707074404075 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 483322131 1250 483320881 483320891
    0x2010e060105010f12050606070c030f060e0303130605090c1509010201050c0c030910020a1208090f0f03090103020d15060908070b07110f0301090f05070f061407260319 74
    0x100d5004c2e0a152a4000c51941d6255849800d40c3c000030081c41c0c0602029032160040007000d000c100c9118000d40610301891805071034001f28034024089802a5408030000e400c01d00030840300740400b4804c185117940000c4045110b5448114041c245804442c24031344c024945440c05036590040d03006008012801c0c0c000300700c2a00c81650319065400b605800c2c00050b80100302059207400c00701c2904200404600440d1103d010719a604816040f20859030400580c1210800076070308400c006520502e001100688040f80c820078080d501c910071a140981030640005c0d80c80c0116442c0d03808500801301760590440c405443d180028601c0c02c007445100c526100b480c6000c52958020300448103010f034480444010310044800380800c0d00e059204080c0c0c155a13030b0f030084001c01c802c0c81d0800e0f1058821009032a995084c03681d00881c5503c0d82d0012000c20000d4021003400c180507004440041750002000d40019120104280850b6440c0c808404200030100070f02a542d0b010350420388000042501c10701c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 483323381 1250 483322131 483322139
    0x10507030e0a050a11210307030f0318030305060d140f0601080f0a290901060302040e032b06080f0d03200a031a0a1409060402070c230a0602010e0601 66
    0x952541e4030b81d030142c6950041024940010151540310469032005030804d0f58501550408100141181078180843d400000d4810100340c0d02c04101e1701500004e0408001d001441140c0d40030000310480000c040c5940c41e03010a01b1940d6003000c0301d0b111640040c1241038000b900c549151200e003000d8020078036201e00000492880c10124035002c0070881c07240100018586500d80f10012143c6625002d002040e403803c00d00c8001c40000c2c018032541c420800030031903900d103105000c110781068810210f0f940041c800c03140446801070810a0150087c81d03090800d4210001620080800ba403151402e4414160340f030703c01583c040b42c2d02da603684041d24104450070340e100788100b07082449a90703400499010091420b00d1030082d400381c0d080340084524154071210000100728166610342040c2c0351101d02c941440b4a524064000c9a072142d001c0c3c8040d400e11035175640301a0300340d4440c02000c0c0170115401a040900e118007003041458040281508900c95031424068000c0c03124060320704a45c086c40001003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 483324631 1250 483323381 483323383
    0x90f03161e0f0303020706061502030c120c0a080d1803090905010e0105090f18060108030711041104210602070c05030c0306150d151109090106020d1409060904060305010507030e 78
    0x100180c1c1c10008882c14109540e500302c000390b0265200700e55260b0b0340c1ca000b00e20401c2a03540e041031100030342c00641d80d50100500325443c1901444000d400321104021400c1d4055000c10042c4820b030340310000c070762281c0484041d180a09200501d01421419994010040c103034010124022141c062000b0031a503601c6001051a114090103210741000c011008201486640f00761141d018034852003000840b42e0340c80300c40e414a10300b80e02602d810740c0003042203802c0c00b004040c608800c40e07049404201c114505103e0300f4141c0120300c1100304107411241030020007031480c4a40104c040d07000204540ea648076280c2404207501c079000780d038024801c2c0341c00100c0c42e00300050a5406401d00041d124078040a20341000014960408102c1b1682075010854900030000c0c00380350a4403048401184c1c41d140d034a824415144016031000341154001e1300180716450308031081c140d443c0056030b80c03540e46501d100c000c1407803485400500da8010345002400000c0c0078041d4816030140c00176036014004c040c05a0019 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 483325881 1250 483324631 483324683
    0x20f0a03050105280b0705010b09160f0e0d020907210204170d08150d1a010602010b0315072019050d050c030f16020a090509160e06010305090f0316 65
    0x140700000c413032004c188012810b440191940912901c0081940383d071070000305506050035100b003045c040b400760f0f0000003180c00842900c40e04c007a9141400c081113082002400c20310320050040c1c050059040441d40b214414610100d000300d0b44c40c3c034001ea0045004e480c200a61043c0b050740201034a11500001c080710200712102401c019580c0c00100b0b0f22401d422007415441c5415059100000165076000195920304d400d43c0714080464800f52585010006030a48600e00080d9200e50003143e0486070038541c1c0380c1115000851841d02c0010318545800d00e46030801445141013440c0305440d1100580c040e103000e100e03909889071050300d41d8000340101c143c0e00c90042c42d9015049800c280044000b0f40c3c03815002c1e08143c40c0348900140340c0c030f0345a00030413580c0c10390b0341200c42107603110410080500d800b0009508501c901e501b00030035491a0580030340d0074400140c100360426480b1804964607542c2048071146821800d01642d0340c4199090014146103446041120010040040544905021950303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 483327131 1250 483325881 483325939
    0x2011706030616110a0f0c06020c060304080901020106051804050d030b0a060e0a0504140f0c090a03060903020c1302090906060c060c211602060a0c0207061101020f0a03050105 77
    0x20480c83e2640f070360045003002c2000f031080400c6280040d10300851030402c0903151485c00394403949688001810b261070351140503080001550301001c1c4c000116268030007200d0340240c100c0c00c03168842175001c004034050710f0786600040d4411500046151140b0451036018003030751095040364800b1040c07500642c02c0d625031120569200455400812009026a1130000d1601c001815220710b07a0319100028202c5c0c440940002900e840c8104210601044084c0c0c0c58108110061440c1010903440000b4220005404000c103455250590402018020405030034038035001855848003000006030600250401008240f25454480c0403d000e401d000048030301e280243c001805c0c0658a0443d08240c6500c1006195010710508585a46601e01d00e29000d015542440301d015422040040080c50410058010000e0914110b010009107400169201c111030503800c081c032004100d49483e90081c040c1302543d107000c00002940980710395256200038140c0e9800c544454030100305485409455002d461 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 483328381 1250 483327131 483327133
    0x30d060603020d1b080117010e010c0504060f0305061c0614040503030901060b030906010b2a1f14180a02030a26040305071202210a0201090914160224040201170603 72
    0x5c0140282c981041d04c6600d071b9101140080760343c00e501e00c2114212500481c250001440100b01481002d602442002c0d00480c20320742440340d03090110004103c2c04251079501750307841c07110500104001d4650022555403401c00d0100d81140f0b0a82000c64881e441202c0050840d441c000e00414a01201c400f43c82c014a420344c01031034142e081c516004800d0344800341805c09061224484c44511180e15070400b40919041d01500c902480501942a290740c51402d03e82e1076030a006002c40d41c1c00489041551140d888281040c3e00000500c075541005000304004c2e405000e02104071050060750103018030300002c2011107105270000034800c6401c40c0164000103080c0e81085070100644484156201d803070030b0004140040f20158444503200d00304100234940010782100801006540c1c00145a2009011060050081d0200b0401c1e1403d000d80082480108001000140101c54402c2250320b2404400001200d4012000c410700103502e035040b00c049000035201407000c1c1c000002200958001c80001d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 483329631 1250 483328381 483328397
    0x702030f0304020603061f0903030e0a051f030f090503040e06030f06011205490504210c12121d0f130c03060602011b0507080c030d060603020d1b 64
    0x7600301319255001070034a0307034003205410b518807451603206061410b200c03c54441401e03207850740c1b4002c2d01c850112001c02d031182c0203a08080080f52103444440480014003c3c413040200700e140b130140e005000c1d00d4400b10096140010003420004000000c200740e8560b0350764461556030f44010141d072185229000d4615400101c01004072843c5032643c81c001c14411000e40704030495582d444900100c2451b51502d1841800042c41c05440c5820300e501c0700100c620110a10b1400203107006040c91240703200c0d48110141e009001949540212449a04117500040d030910f0155600c4507280f02001848040c1e43c0d85002c00f413402075840c020b1001d6582190300900080521035801c1c01c100200b81a100416001170070402e6821002c2103602c584044d00c0d0b01038400041c500d09102d80242160031220f028260036a40784809254541c110082d103500a80c0207148964a24107081c1c02e42c04e40c0100312a450700c1508102001c10655095009000c424411401c1081402d4036102151450b92095000c00b010441103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 483330881 1250 483329631 483329633
    0xc03030e0a2303041d01090b0d021e010504080709020324100509010c021f020705040e0c211906050c12060108090a0b0114190b0301060c0c0315060305060702030f0304 73
    0x880c207407080a4202c03041e0b03420507541e010609122882c1c1c124802c610303552100148020b0300c0520a1644150054a031624a0f41055010070351900c014210b28034003019440d0900302d66072052049501500c0d80401f0b6900d01130707032480785002a40080d80c1103481c0d05010030314240041040707416451000c800405e44040240707510b0060b10305510100c1000c0c100100b40c2d42040c090703140c600081502d4440c2400c011040c2c0c0c06250000d0030040e164211621890902003500035135640000c03640d103050350488000c0c56400c07c03090503581c0100c8014500540d40148025a031903e4064002203c60a000f5a402d01c102e945a90036600389100e0b900701d0304040810000824410352040d10503603401183d0703e086502103540d6440e442c580c80d109034082a140035550a1814441c100340203034180451011042c40361140c100114241a0302050107035804010a40060405101d4984600c8000f950402c0f1901c04500e200480b40c005800310740400d4030790388500341c0400e8100384008101d03444000440e00072801c640b62 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 483332131 1250 483330881 483330923
    0x303021c0c0b04150218120c0609040b0a08070e090d031407080c040f030804091802030601030809060403060606051e1e0c010b0402040b0a1106040c03080a0909020301060c03030e0a 79
    0x3020b4410780d010241c1103036543c00700215200401c207410340d540030a02d8041b040d408020840c0640f0300003051640024072000403a4544000ba209000c108443c00302c0c0040e00c500c0450322112255120044a11421800040d1241e00b56540c038014041481030320318603000403509806880d070010011b0000200103000511480c441d861040d004040c2d22550ba142540c0c0d10103181072034132560000c1d00c0100d00028200880d0740e65100b106581c2108071403540910b141900040d40f291b50502c006403030b0308070010306c0244e075a03281c01c1103401540d4401d0b0104402c81e2103a03c0240160480c54860000003a400007501500241500ba10b8000090160440c00040c81c081c1340c800e203800941201030150348440d036032080750744d071800500044e081c01d410381e903102c030b00000c0000c0060080807200e0300c280c0c11074400e002c00f28982d030000340c0580b600b00780391b0342c0e480c05003501c2155224030356444122084e2020001013410f990001d01915020b010b65401d10003c0f0452420a4840342c080100070207080e00790100caa01520303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 483333381 1250 483332131 483332153
    0xf0c07030813020a090e1e0606010c06020f12010311240c0c0901080d141303030f05090d0503041703030f01090b03070b0d021b010203090a062706060303021c0c 70
    0x7060541110b00054580c0400c0300040745402c880c0b10141ca80c25211101041000f8070340b210b0707200300d00c0c000d001100480940d072180000781007581000a444024014080c00741c04482c080300c900c0780d43d07036514071400d44880142e9131f00380011030b8141102c0a041079146044100351180103003040c5517044826841400c0c0e0302d540c2c08401c1c40d007110b00070701084c08400c0e501d072040d460023040c01c600a0542c507065040001c2c81c0d02c00100440790f200c1001d0210316800c1c08850384040940b0740c14101480a540714070015a501d0140f01442544143c284a40030f040040100c00b410861344009140200c00d4004210f1544a000803500345440c5042070004200310070b880d40101306501c902509540341c2c10b0700c8203d800c4840d0b0000758840e090b1038001032010355010f801030450a0a00c041c600860840c2001080c154a03140c1035000501fa444e25148048003445522048000031400b82e10038400d0800c903480d0810140a8a00c0b096025000d100c00e1000c1d80ea10b84880d129180d816503441e00d800c0160b503540c2d114026 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 483334631 1250 483333381 483333391
    0x6031406040b1212280906050703091e0305060903040509060d0609050f010b0f0a0b0a11010b03010e010f050a0603080403032303151018030602091f09030b0f0c070308 73
    0x1901060f1440c000e01c4042c4008071012080034881a611500d03001c2500c0903031500b0910480c511074019190040990000c03c01007034419500e032441d614038503402e00316501a0076401c004079080b84004035240c0c8104080c0340c40c0c00c0ba0310810030303140c10b40c0d0f40010a42c1c99008603c41c0503003008440d8001000340c42d0161030009511b10400b030000700c030a010b8442e50b1070684034104c4a1007903035407040106814a80011042440b05084a007000d01c030f403c0c0f401814440c00340351004824804d0b5900640001c150039044480c0c0500060000c1114091140307105000e000071085044c43e651070080440c400b000180100c0042c0d9030042d03044c514203859613508030740f003214034075031004a24070300703500008803a42078030040d80a16031400122807400d010000304080c84031540462028400146410000107104000040880e03410040050300c070f101000c0802e810400c404c4035400864500c0b110682003a4000080405880c0103440e00c1320180e039502c0c081080101d00751030621211400340186c00019100c2c0100e11b07801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 483335881 1250 483334631 483334639
    0x110f03100e0c0405150d0e071a031b07020307270b030304080706080903040305192a05060a1403011d0f090c0607060b0306040302031b032104030c0c0b0304060606031406040b 76
    0x1046a00d25840308507041a541e9100d0754104c20b80401c41c00c0405003a071030407100894801465414100b00d08240c5540310000e06008502c00b10f20cc00c295541031040b0782c010440140195440c50b100d40d425441001c0b42c00100600a1810303400c0815802d0010949003030b00c142c0130007005a941070107002e0301d102800a01d41c1d0800e102c10007010001030000e003ca07510801a642d031110105036145000c1c285024a0070314055030415078015a040140007986203021a40300352082c6540b460694011100b4103801c3c50b440e0359500c0d00000004041407c1100804400d107210850801a00c80b000010005403041c0c6a6541c1c0e60700948080343c0525000e00107041551042800041c81d105500200341019011142607003d40c00100300340b49502040004400c411202601461400034190010b12800e80311041d03900e458465900010201409003007011f03804d42d00b290854030318940d5800b044a49620465048812500700b00700002e07281d000307008400c846040c40035202c5481d55a201440020016510030b9588 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 483337131 1250 483335881 483335887
    0x3180f03140403060e0102181c0b060301020f1207030b0603070512060d020405070c050c0307080a060c0504080f2109130c0e04020c03070c0f0f090f110f03100e0c040515 74
    0x35560721594005020f01000548c03640302c01e0110705024003030004800c2c015001071220000051000030030303c0d406544409100e15644481c00400e009001c2e140c0b50248019000403100e0b00c004808880030f10400d025a070a0040702900e03824172900d80400d45a0601181051100d81c01c1d00700b5085105070304c090047c0c10314203104c0c065000202552000c0e500e090114181c00c020304284032051109a40c9054150010104545411081551002c4500001c2d0a1598480c140d4603100d1140c3c0890b001030a40b4000c070395410549135034154559907032404400c42e080c401614030403848500710907110342120007030102d5026603030980060042c184155018007045022039907001da035a140c0c40038141c1c22080100031900d9282600d40340000c030b0010b070000b40109070429000c02070200c51b001d903075080d0750043c000810030290031803d00b400340108142c586080c82011520400d40c4078200e02552040d8140c603131703081d02d40e551249a1620301e07005403141b0a0b9030004101c1808542017241c08400d1090305600c00c145 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 483338381 1250 483337131 483337133
    0xc071e090204030317040201170a0c08010923060f040c050a020d090b0901030f0b032d0105060f2701180c0905030c15070804120b0a05190e24010603180f03140403 71
    0x1440000c101d400707085040da032f0030307190100c0c55100c41003030301600f000f900c104100010b0280700c242c0c02c14201a07038442d80000c84001009a10b4403a45182103150241c005d1159110b0305001400c1c50700117000703204c014880d420640742064031906140c4221822509a00d05d8100a60011170203025488050400d0301d031500840c00c060384041001d40c0e0000c9940d81d00c100d00b05080101480351034002d01214a10780c0c10241441715981d01c094141d0781c095001c0311120760514080819418806141c0050042030304044000500440224407000ca0320541d58010018244506015603400015008441e0580c0c04440715a89504000c0c5c81000a00c007a40c5000f801c220b425a14004030342e1154000700b03040c60f1b00410800412031005e000680100610800740900d14180084107141110310700101c03a80c81d00d43c0c3c43c105040b8018016400c5c1c01400701490000041001d0611030b61b85004e1281d400000d03d4034400594a5400d001d07282c5115071f002e40071120760122500e0494483c1c081010345420b8a8007048000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 483339631 1250 483338381 483338417
    0x11060112030807020a20270f100e04081206120c01110c0d08040f15050304121407060c09171203061c11030c041b11030c071e090204030317040201 64
    0x550b110780c00441c116014020541400004910021305410002d078140e250b048004a0010340c030f60140c856102001340e0f81e1907400402480052b40e0094040e220b501c411f010510040400520703c440780e8418414258480d5014811700d4000c0d0301c0c101110343c01003120050190f2050078034803507039603da40840d48060142400907512107101c41d0100c0e4075038000641080000d07510501c5200a20266000f1040000400350241a901c4004c1c80101003040e030342e02010415005001c00c1018031018102552075110342d00d0014001d054060000c40403c1003140006802d811003220b0781d0206000c080900b040b50424803003c5d84a4001800340c0e41c0c40400345405071840c00300e485000c1100c0e03004050a200ca41e00c81424141050740103004c01c1c1c00b881c244400ba080c030b14401800c60011206034036200180c12902d41100e0f00318004d2424808040c09807240000e408401b0041000301d4000350721440751400d81d02c80c0000100e21481c40003d02040307001d192200d8100c1d0643d00d0310741c002d0040c104440140701c084800c0f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 483340881 1250 483339631 483339653
    0x50f25031d070e07140a0e191211031f1a1801151b080901031e020406170402240c010501061d0d020108060d0303020f0d05060111060112030807020a 65
    0x1c054150322142042202c6a00b105000b038201c00d890030648018450f810040240b031081080980c02c1c8403003144545526150b07540c12000c4c12000a409441540d10340c004801c54a0341200e0650300c02c003550503d441c1c240b5002c250408821303841ea07081000e036040d207030001015003000c4241c42c00f004205514000780303481e400000304c0c015001a84071b203480d46c1415000070804440080381d0b810442c0d800e03008800c03541480b051480d619004400380b0b03250880d05004030081c00000c0702ca903603078000085040c20300d5070f45500680705841c42e0383c0b42c4840c1c803038641c00ba0315a4810700300e8004c4d51101501c0308084502c581c0e4030350360a04a0403004014504600c0e030003580d080d00e43c00c0e40b1403000200c02c030480c60407602c0c080c0c3c000b500d1034400b00d850310081c0400e900001c10301c61020b002588209250a20001018000d5044030b0f03078421255000d94a0340d4003590884010601140c125003c1501c200900103401d4000c101c80e4180e03001072034400400609034904641c00b240051003075055200d00b0740c804010490f1702c001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 483342131 1250 483340881 483340931
    0x40203090c030712030516060b150918251407030806040c020604050d18050301180308060d080307030f0b04090b060114040f12030c150906050f2503 65
    0x8080c400306101c2032526004159101224000d4510140d000280e0702c5003c0b00c06402210300350703020b000e00c9414040000c0c290303e615607501c543d10230303110074058070703140e0141c4120300007120320f81c5281031540c101000c14a000c035860000c1c85000048005541a184060a40852240381040300c200703a048500700182e1107460150301280e0380e182084513a103064002d50710741e110305201070030780b81c14103546003542c80020340140300501c40110898080c40a070604120024440100203021100200e0901e4900d0010301105400141111001a5043c03c18500d02c0f01495442212546035a640304011030040182d400030510280d1207000061141d680ca01030392405501a81114495081c004005025100019081c64907648180030801c4040d04a08403001110840c07000000d103010689821504071840690003081681c035200300448000d80742d44092210352045504001c2515030001d00c3ca0100c81c121841e0100308c80000d160030307000f00322070f926a614070340c542008501c040071b0001c1c02044200c1d08003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 483343381 1250 483342131 483342133
    0x203150103021c150b1f120f0c12090218040b0f0f072c06132102060f130e0c070519120c0804030506070305060f0406050307120501020904020309 64
    0x41c020341c80d0018004004035541c998400060201d0f070b440b803044010a241100401d5a1802103181e02d80700d2061003080d030f6041e462200c0408401c0c400203001d41c400d030021a09007a00d00003043d4036507902032007880701c1042c0300c0e02c1e21a0792440c461300003400b403d05000304070b820460400f90f2507842e40728601110f00440c8113600c0c0c110146441108201c4280004000341c0c01619110305000c210358000b10440f551440b8244074020740c159405003585494034804030683c11090028286085510314030307a40d42a585001070413055005070310b403014412101c1d040040c1d4040420083c180d00c10a000000f40310500e1131007030382801140d60300300941040b0301c122500007900c040041d81008000f828401c4403100d0f03c0d4149200180710710b03034941e2070403d1244a100c40c280b150340c1c4004000e003c0e0b032506aa00075a400001c03140140b60018000f005170034280c0b102030003400280c110320458078060103180c0c01e4803400780041c406a8508807084004d8080518142c941c2d550820841246440b54002940300d034012070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 483344631 1250 483343381 483343423
    0x603020c01050708070801120206071704030302070803121512010e2103010f0905062803020a1502060a020906041a0a140301030f020d020a09090c03020102070f0503100207030203070203 81
    0x1903155800e4690080c104002c01c081c5008000016402c0b048640c103440c460b092111a95a40c0d01c04605140700e00c50300034200310051000000000c012100500a6910035404c0d603d4050b51184078542e24018030020225504080c030010f10460320308041c0313580c040c1c0e004120084c8a424175021508448000588964076000b0b083c2d001400e02c4e845e0750444070450700a00c0e40c2d16540c904110801e400d5040d000300d040003902c880206195540d0384e5000001c1ea840c1403050b181000009000741c88100310f80c0b208030702034845124001000c036120640320044100580103030003540c1d22040700398001c0d0300078802d441e80041c1c2800045010860005406140c91000e4403407551813200550150600783c0080307040c0b50081c010801032001940d007107954090203a05071072246d4a92201e00c0000c0800d10190088442180740801d131401b4054814541000c4078000c0c0c0a407075510780c42c1e04018944504501a2540551100c2880309000b00e083d8001d00c076250103441a81c1c100821503000a04180c2d90482d130146d0b8400807 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 483345881 1250 483344631 483344647
    0x170a1d0709060b0702010c020d0c0e09150114030c0f03071a030a0b0a180507030f020d09060b04020a02210408010507020a15020711040e010908030108010c081f05060c0c040204060302 80
    0x3621400303003d00446601c981c00c2180950009100300e5017408001e000300500a255010005003590403000740c481440301e44180d10b808800c2540d190094000f070f0f030120800b10300001c0d0305001c072545486280005005040701445a0003400301702c480300d80000341c0501c50103400180300808402c850074103100002000f41e0743d080011064066031003241449100310241c140410134400072004205001d411090003191682d142c280642c0201500701e0441441400040e40507840003065020b0482184134060400401d0b6140090004900500c0b00890250344103513420403242e0030100c0795000340141c850040d4613050f221003841c0e095400079140c05015034400071440041040c0e00403402d03080009081c08501700410b41e01c4d104004600c1d9180303d80070303a69521703a003440c0520070340100700d10b644c00c1582c0035a0b03542e4800d455402060989014000a4144800702e050480e0f40b5a128203000f41040400c1d840074208010080c1c03e03480012103c0882c424003020101c0350300c413400608010f1400da1070050b102c0c1a6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 483347131 1250 483345881 483345899
    0x70302040f0e10230a0b0a021603020f01030209220605120d1d010e030615040b03030f181c032118060b030a080409020405030c03060403170a1d07 64
    0x101d90030400707455520700100316a603049082e00c0c0c0211250340200c4c0d04240c400951030f4103075980014040c1c0e0402649070012869080d9070000b4244502241e08a90707841308010950280000a808025400303d0401903094256106c4e4001e00904240101201e40141c104041800305c0c4110035035101d03900d80c0307420080003a4030708024102c042200a8016050184500100800b200700c144510030344080300102109507a4442c06a041001c20040e0480b142c506109400440828070f007a0600c0c031490038204c84400e070b400d0100030f945002078091207803410f002c19041051030f092442d0a0b0282c0160350075030700110058090303007000c1c0154040d44a088500710700c843e1802800d85100080409103041035002c074441951420340700906d41d0803030b070b00013500840c110019083c07100b8078030043c200410200c0c0c042a8135030668000d1044840c01c400f110398400c0e0381c10038151200c0c011500035001c140c50401c07501d44010728640c1c46900c540c201c00c0005900c24501c0c0d41c4e66a0007204000c1034840d078002001840380c514 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 483348381 1250 483347131 483347159
    0x102120f010303140c300309070f0603180609080c030304111e1c2402040801061e03060b03160303170a05061302071103070303050d0b0f011d030f0607030204 69
    0x1407000d40c3c03a8680500c512040356200300350003282e03100c0c1180c0040c1d00c40241070146d240081c00c200d440e03925920305242c445103560307800f0ba008074000c85580ca0800030b440e50080c1b10f00f411184005140551190454131110001d091a207025600404204900c840c0030130284000d40c41648546181106071801c001800791a902c0e20803415103407100318401484591b21200480442c0c41d44020144c80c2e000c003031a10f5003042004842c180c0401040004c0981c28440980162040d40d600c64020003c0790358580f2010200c4000038206c0c002a40480c90600100b5030755041281c00b0000607007100c200e600002e00d490f10440b103d5105800081c1016030302c4036500f03040c0700c002c0c2d0056004801401a0b00341440001c42002c0c00200310032109074002681c10030001d210f1030306500704800601742c40304a581d90801400c260310003c40d2101d0310340b400240c045117203441c104101c61404107a56400e007180c44180070704242c00702440c10a60612a0740c1303007c3c1500a04008861080010342d5000d600c4520702030324411409 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 483349631 1250 483348381 483348407
    0x3130608010f050f0d02030706260c0318070e0703140906010e010b09010c0c031406100602030f0a1209060617011b0503071103040602070f050607050a0b090102120f010303 75
    0x2000c500010071825680341e4044043c1d5404448502503020460006034010000e220025014011030b440012101d030024406034000c081080e803045800003246001c485150200e4000c029114180041a126111041d1048030160020300b100c04003620b5050342915075408407501c1d400a40c895a00940c032400624115810860304070041036154180b401c0d040d80d001d01405104d040440201c1c24603100ea10a1843d1003441c0e0300310368401505178032410048072036859000d82030202d05c030355000b00f0481044d48074804129280ca902840c02e000c101782810f88540d0260080804000382c52000800d40c91b01e51207040e000301c3c03090800061031032801c544034207029a005c2d0141c040d6450302c81c0300f8007098003848203606456014035050b5030325591088143c03200d400c2d42c0b40c0101c1342d12010402241c2507400203081e03800d585103076080d000c0e0300341d40303e0400c02d680c0304a81000700300740c020032034840c0011080719005800a050b00005070900e8070564940f400400c0c00c507055035401e142d1100420a154002c08249401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 483350881 1250 483349631 483349637
    0xb0d0c0203160b100905010902180102160e0406021c0c03150f03060932060610050a080c041e03060e070302060711061204061a0a05031f1d031306 64
    0x2003960303809882e4100c03160540141c44480000005040c0c21020141e41004d807507603840070003895864a540b440250040c07100000303501025500d0100941c0001050a0902c17100c00c180283d4030304010f80c200c80700d003020703104507070039602030104503401c030004010040107a0402d04c0000320f0035108880181501e400418500107075500e90f40920800c02c202441500342d076002400070070a0b4496107041141402c1301c0c205070404011100150544121816068182c41d100c42d013181ca00d5243c04042000e84400c1040b440c0214104200f0103c6160143c0c0042c2c0e84114800141800d183e40c44c414a03441080720002c0d84503d41010800303000b000300504c40d826400b02000001c0c2070b0b907825a80460300030311408030080d14260480b141031700d960741c0d194122680f2205642e11220366060a2030288007401000c00c4100c0c3c3c40c0d4420341e12007441d04108502500300c0303500030020031102c45500b500c814400a02c080b24580c55480d0384c0b01000210b0035078101c20f54880010b0055654982c5408401e0243c0070f680c10031820 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 483352131 1250 483350881 483350887
    0xc0510022101321206100f0806060109150324060206010b040609271103041103010e0316030e0303030705070c0b03091e16090c020c010219030c0212070b0d0c0203 71
    0x9007140c00e40c01002c3c040400104812910307000ca001440300f604e0141140454841c0208205010180840000444000100e100325144d240c1d0001030300c410b0f0403203480d0b0002d008060100030140c410b914034440c65505080009460080f0742240c2400141400120010b003007890b0100038407076041014a00408111800c6414a402c0040040c08184c0d07a20a900d0703034008081801c42440030620a24441381040c2a042007113080644811006800448060308c0031156407a071414981018001c0180e80c902c440301852400c1d0200162064424010707909a00b01301d26480d030700d241c07510b0030402180508500c0c0c840c50340315040d628142c40380306055000700c090401d0070b2007444400c981c0000d140d0301e0008803441c441441c07074018110034a012115001e600c0d600903680c00c00503409086034806080006160b09490303401c00008016a520220000d0010400d400c2001d1800428402c0c10a1a0014402480c1d00d014285202c0024600402ea8200f0030240030005100c50b6400700511924107417900c3c1d4000307981 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 483353381 1250 483352131 483352169
    0xc030c030d1809050a0501030c090e0c12010e07080109060605010f0909110909040309060f03060617090c181e040201050304170903070b1e0f04060c0510022101 70
    0x40c645810440c0300091244202d140740700c01011004070340190803444020030040c40c0c44652403028150a1000352a04c512101340443c5c00c81d120f000e4842040c0c680300c000c08020305494244003854114a0820700155030350b190700b0350947c40501c442002002d1540c0041307581044c07410080301302c4066a00c424140020b1011800c0300540045582d8120740c4060b0000402484000103899103200e2a030308942d001c1d04030002c101c20190421041c0741034800d903a5504104074121300082d812210749004074404039645614561444a0003001158030503120303420395601c144000d021825416030500410061420700c0200000440d4140507003854a0320185c180d00d40341080c1c1c0010b0003d10016002401c1c01807627816041c0015a03003021110461005411104425910b14500100742c00c0300d2008096141c000c103040c036840c4120015122041c54588405190030710341007040d682d41280240403100c2e40125861150303001100d1010f440c500c10224141100703c0c1e01c1d8880000c07440302c142c01c0201ca600940c04600 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 483354631 1250 483353381 483353383
    0x8030724091505070203090418050601080d0c020f060c060c040311060319020c010e0601090f1104150f0e0a0b0a030e0d09051c0c08030c0d09051e040f1d0c030c03 71
    0x144202c01c000d5000149611440012805c2d449040342268016080c0010b08480c40b0400c00100c1401380108159043c0f6600d03000025207455200035210002144006030708054605400d88040c0c0210007071481c2e1410003c80c074110700b0f00e0030480e4030f0391030880302050030000d000001080d080510001c41d5010325600c0d00c0800520f101c2c1c0c20450344403401d07502140b131107410842540a0700b410160401110010740c1d444a01c007010700a2804111000d80c140802d02d40e05040f5042030320b041d00c4100f030040032201502001220314021282100c802c004c2009003c3e045034a0381e01c0f500010300b40d8074a03401d503200f08030310014094a1490080003042c2d80601200450243c1c0f280f010020b0320400c8030002003101c0d20545c2c2110340383c0c9c48000504243c90b1410006455000040106a0302080e0f00c161440e1084070f810a5620040d60311071b507908980100501d5008100d4404c5500060800800000300303000d04240c0e1750b0031241348150071041c0d40d90108078a514401d007000707c107030740201c201d001700011079200c4042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 483355881 1250 483354631 483354653
    0x3010314012304060f14070906030501053307151103060d080a02070902030c070501050124031e0c080103050606190e1330050a170603070803072409 65
    0x1c0b0090341c00b0003003020821141c1018a940c220007100744039180c0e001001d04030400040d18a24041a0054400108c280c000d0164034101d070001007102e104859144580c0748800da804e02c04400311000d421b042c00780054034802a00300c143c040c0710581d0040c00205040002c0302d400e5a004420034000f8400c1082c107a513850a4000380e19030180c0c0d000d4070743c1c100050503443c0842e10303000000c84600120401c280d4454010180c400340f40514001c0c00b0b82e0340d0b02c4008810000c0054101c03205510701c8100301d112107009800050380d009500c04007440a180541d02201103541c498001d50006000c04010418031204210300e42c0c110707a00315040c404c1003102880101018906204010f103052515002552000c02c0114a42c407094006a44c03400b100502c04402c035140610480b40610208010000d040c0c00c0d200d2029668801d403ea19040d1403000000b252815500c03000f0080d40c0c0c103100e80c481c0802c403070f482800544a418450b20441d64500caa035440c5110101400c041504201c0c5002c10b1940410b03c41410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 483357131 1250 483355881 483355931
    0xa0f0512061e0627010318060e1c0c050c100905090903040306020c10050f0709050405100306060603060503011b020a02091509040b0402030105150102070513061a0301031401 76
    0xb03218030701d0781c180060b82281410418656071149010909070324041d0010707000d245500c240e040303210400e2404c000540c00c81308000a02003034000c01002680004017686c0c450141c17541d810040f10000c40c9202c01e411351140740c4c94056030000d0071000041080003010081c03100c40d070030112050491407c0711034004106403518495103200c2d80c0e1400101e180108248215800785400142c103541c0c4803000078001d9580d41444040c19600c1d41b0303100c00541c2400d20310a107603019680c02d60b81c40700f1052500040102030400038100c80302c03a41d00c01c44000002101446280020a8152004a4140d280a08060864090740024032050402c1840030b4195030340407a22503507940e8112a80c603000c0d2524070348050210345542c461900001c50200344414068510481881f540c030840090000c2c0e624400c0301c40c0148030048000e40980c0c08a6424840d5141041540c035600c40d10000000312299966411803030840c50410210816070000014010310007c003000d41c1c08810a08000d104600e0003100322100032483c0b1030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 483358381 1250 483357131 483357139
    0xb07020f0307151214090705011407030804060509010b0915100903080a0f021f0522020d02060a0c0804121704030b0a18150506010306050409170306010c020d080a0f051206 75
    0x5080c6001ea02c1d0740c0000c2e45c2c1c0c0303141420800d41e8500b003a00035a840645005d200d02040300d21140c0c081802458040380c079025415501e030b003d1a11a40c3e118005000c0152074a10a5502c1d4404000203071150f140080c418036101103207461401c000303001c0c40b080e102d041c4008410400d4020040c00407405101c2200c601d04802c2c0340c44100c00380ca021080b41081c1030480a044100940c5024410650307054206601403090b840e00c58600c2128050030f076184034204071000750042110303019a00075180c0380c801303800e00744840d040110448407141d42d141c11681c010341022995400c0e825071001480a5044048050f017990b01e070043c030b000c0c10341d21040200700c4010f00244000c1e40320200111b021035060f901070003941d403268009440360621b00060002c0e000c04c880050002c3d01d00f480000e02440c1c00d0045407034154001244800c0c52261030720b0650a0760004210700d051007130034010403005850700c8200e000030501a10000e51070301d854940081c5006000a15501000300038804400b200300101900785e00441c08807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 483359631 1250 483358381 483358397
    0xf270f010609062c0a060507110a03020319080f0403140106080303040503072006040e07030f021305011209080408070801110702010f0c14010f150f0312270b07020f030715 75
    0x10f20100700b1915060241d03a017201c1c84000000304c0a402801a001c0d03d80310f01840040d1417110414050300761228400130750305601c640e150840000c1021907011007940940820b62804419000d801e000307a02c0740c0d00445404030440380d0402d840c20b0a1060700060160000034500e1403c1c02c1e1599036982c010000041e124200004505000c4016581440c030030420180c03005480f00d580762960815044211040804a8100000c48522160324805c603103240c6281008014010704000044800c00440542c0395005a652019003002c600104041c100800d460070050081a0404282c1c3e82580c1c0c2421408040b6002440b0600060b0703085000944d8404052501403a44c0030700c0c1c02c0c180c45c18006009160040d500c3c0150312810b8882c00d0b00300e810301404910b14500010780e19041e011440009200240c02013481c10004006503116403030a00c031b000320081040c0201d070003c5030241d100c0d81103980208040400003c0402c2181070140301030304410701c110050110b007403905800c05a43ca00e14401c5108005c150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 483360881 1250 483359631 483359687
    0x12111602210a0b0a1802060a050c07090e21090607020103050601050d0501031b061403010501030e070305100605040615020706051b010e100509060903090f270f01060906 74
    0x4012807401600c80700215401c162035420f2400d584001552810401800e080011400d180d08601d800213036a40945520b1504400030b404940c1034015028015290060001c00140d4a000c3c0c05800081894140a0211401040c84001e40c0c042040018100007000740400b580643d1000140c6d401d068080c24041007035520a00100c0305407045105400c1e00364a403000220a2210646500c114502c443c1c88002c42d032600d681003540e5990341c10001280d5004208014040b951081e00250220030401c4100c81150741c036a40c845083c020756108e00152155030b0343c82009145858000e01004014608107900b04219003e002515105140035403014050001200310503190b155898084001024008206a04074005d002ea241e20241042d00d03415030414001c140000c0c0c010561034054041d0034015443c1c00001c509015107402403d8919a000031401242550381d010942e0340c1404d4141404600707010b180c0803000e9503a416068012004201082c501844025040a101078001c0c00803104104650f2030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 483362131 1250 483360881 483360919
    0xc0a031e060914010c0305060f1e0303070525060f0215280204080c010810060c06020f03010b21090d050304080904021b060609040309050d050705060a12111602 70
    0xc041e40040040e610501800303203001045d80108421103940c0d800f404035450b40b50421107400b1200e10304a60280e81000250345014410381c0e110000140542601d080104030349505013040104030003880700d951415206403921094214403000350145040150340d44a1480009558012120400d18480f80300ca010881403242490340400d07132080b8240702010280e0824060020f0341040c0b042505074030400d908205290b02038280c580c4103441030017400d41c02c0c502d080c20072229444080c00c00d540c190360810041400006600081d0b010382840e004580c0d6030f0a1401000c1d540582c0c0445181c1e0b008074041c00d0008140300030a64a4420045140c22a100d40701e50034903440034801c804106a01500c00203e20b036200e8092001c4450840c400e0381070310000d588080600046130000c80d0020002000070800b030003140341c041d5201c08002e02031400c455a007616240807030314a0303100104803808a01000540c422022032400788070b90b0110407094090802c04503030000001038a40d010000d2044038040c0b466400e90f80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 483363381 1250 483362131 483362141
    0x6050a111002040602100f06380a080603100903080109150b070b0712050603060c0307050705011109190e010512150a09112713021305090c0a031e06 65
    0x81d07141070455036141e43c0e100103075490420b2103c0c864801d041c0350f1a044042440d104d28030031600860b41c102469906080c0c2a0007800e80c001002c2e800000d0500805400c2502d07030302034103421919440741580e5040000c2007601e0410301c111911002c0f802c11a0010010b40d0000c1c4041c11540c1060707000c00c1108142038032904800301508040200c107008035030442800340b12110940160102e440300e008060000ca841c40c2907440880316603030581d00c400d01041c0216504001075a1110081c50b095062041c40c1d9641429180d40000121400340045142d0101e450074410b4070601403409190130f000146811900c80301e030f00051040301d04c61002e00215a0314000d003840509007802038120751184a140c200381e8032004020f414800c1c1c0b0304000b09404290311342080340c40800360032140800b44c05540b04019a14502400003041c04001c0511525880c0050b101c44407a0080c1c0071090303401146504d80220712903d050f00085940b4403032942e0302d8003040425504040007401006442c100003051400c3c2c103014000d04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 483364631 1250 483363381 483363403
    0x90606070f05070e1b04362c0c060705070b0d02070c060903020f090a0615020615101e02010b0604060509090a05010f090f0e24070906050a11 62
    0x400d104a81d0800074003082d440c081e03a1040d450034400d40c60300940c0c400508010042e901a00804000c244000105207000045075118140c1040a400340d4181c03484580150307015040c1890303101c5d0100005168858129400612450354a0300d0307141c80f40041d65607440320303954403901a09000844500340101171001c5c402404464040564411822150500a5000217420340f00703034850346808170b603c910030140c7c441142c1d00100a009071901e1a010804454400381c03a4202069030b0340070004a8101c00b0807680d4a10201e5009008103181011282404d50481e1101c54800c011015038102c600e60041404d80c0074800305060980b4480110030247c0c0140214510503520010108000450390303405070040540c98401d0b610b440e010b4880d5014003054400a024510902e5003024040c009070f61264006ca60f190807030040884c00882c00c040e43d03801d08108010600c0140000c44894001c4040d50200c0b507005200342c0f030120348031813130181c0040c494003819002404008061205040c2e10342c081249081003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 483365881 1250 483364631 483364643
    0x11d060703020a111503191d0705040e06060a0b071a0f191a04020706091703060a06020a030c02121c020709110304050c22140114030c0f09060607 64
    0x505050308019680b0040b81004a4503414903c4c0b1309111401e101171049000c0c111400d03000c0c00e5440c1c00300c0d401c0c0e144a0700c1121440035543c0c0c4d01890461403000f0001460200202c01034041e25007094280070944010084034034050340081c0038009541c440718000f10403500c0e540012500d50405103005020840e00f02c040d20540c500d00c0061102501e00d0f222464043c4901311070a92100c420340c042d00c410380e144c103541c03186400903241c514174150625400815107984102c1703001845d901640c2d40c5012410144078840005c02001c01000101c1c180707840700b00041e203030f180010401c0200640d0010812140040000c0c0111a20340545442c10720402000044001012180fa2000d400c43d40080d5101c030180718200d0704605281002c61024944801c0f41c0c010703a000030203000c041c1c010700e051004000d00c90b541d02124400b10100180610011f00c0307a4101440103242d02d0300f06500d0903825400381b1201c22505071007a04007104c2c2031a01d5444042440603560103407401f0f00340340d8400c4005002401084405010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 483367131 1250 483365881 483365887
    0x27030106143a051c020d0c0201181d04020109060804150b060918061009050a091a090c091305070c1101090816030b010608040302120c010b15180618011d06 68
    0xc01ca00400c0740d60310b044c40b40420705019650580126611804101048045028105901c0165200705803540c000c031405540039500316034694200c480c00717000c040c82d0310b10000c100c002d2104669100e07505200402c8549004c490070300703054032070380540a691589175134070956425941440e07854243c141da0110782c00402c41c4145501500780c4044410080391400d101c0c03003014400b5910f440c05444100b041d40c00c00b81541c5c05260405404000900ea425002518821821021307006036882e9039610344038155140460340c840095278284006441e40c20b00d8041241d05020410044aa001120320721160700500c6002d0740b90103081c0181c2d001d902c5078125508070300030100d90380ba40b0b2441031070040840b842180d10b55840e82c1d0f190012141e020041e140200160082052a0045030145024140b403a9040300001888042c0000142101c9401040c20301c54140100b004864404e80390b20441030b200d810b40344246041548003407002c100301d202c0b40e04c60500045d09000c03c0014504462400030703003005002a41d0b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 483368381 1250 483367131 483367133
    0xc0e040f0209010908160303030509071205160b03220213050c2d0f0705070f060906020d030b10050a02030d050a1413030207030303090827030106143a 66
    0x2001c2e51140503102d000c40e000f40d100050310880080c0840c1d50818050800c001107045039011005404042d2401c003586c414840c0210320742d5140d03001c01c110188104001d02c3c0340c0420014a0845044075800342030000400d00c2001241400020031200130800703410944010882c82c030004d5050008000c4610900385032104004000140500170455a110841038010340c0100041c886000c1490790a00c66000740c2c140014030145e10024090b0044030300c00e4003034582c20758030b521004001100d550302400025a509000f00006501480144400c20782c52509106d00c1c103040340480c03900c1e4955114031003040000900f83d2013092080c001d4a5030310010328801e2115003003168031400a411010b4481400c10020008a01000306106c039000400380e01d80c0140800526540f011f0300101040c5509544081c2d0401c104510142c0e031813100780000783e10010b008162160701c0c040c142100c0309a081000807407041d03501d25200c0d503184140b100400d02d6032569070413108100c10281580d1074140510b0040c0283e42c5c55980 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 483369631 1250 483368381 483368411
    0xb010609060e0a030507030b1312030b0a05030a120807021905030c0601060503130803041403030f040512070206120601031b0801030b0a111206030f07030506041211100c0e04 76
    0x240480c0c03590359482032146071030b50070007400d5003140c8401410382d840910200b00160130180c0140d03000d40200920ba0100826850b01c60001d0b00810b640000266140300b80400c2e0701e00803210002800c4141c0081c11540e056941d107548015004d098a01840044800030b00c03000d20802a40f007140b82450384124400c0d03801c3c94516581e42110b484841d86006110001c240c143c4502c0560b880791549846201e14400703142c4400b0031030781c0090000e540c40000c80700c00b50054001000158090305454200000a281c5420910f007807000c145100711450b0307020007094001d40d0b00ea000380c2e02c5540300e4506c3c0f848030351a0340d001600140010724051440d00b01e0455400c410076042040d8034100ca02038450703210641d41e4449000d0403035600220180c02c3c1c403800c0c014000740010000c01e50ba400180038044441039520421014a0803609a20850b1349034802c604000801c10030074648400170f0001c1c2442041030301d040b80d2580c0c89804494a110b04981d5908241ca4443d00c0b4860054154074054801c01101d0724900d060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 483370881 1250 483369631 483369647
    0x50d030206090d030506061e0f0403140610081522230c1509130218011103211b041508072c060d020f0306010f02060112080a0c0b0106 59
    0x6150b01950590f944960b00030b020385440344000800b190300d4080b4140c0455030b0701c3c48108201c84c01003414840c3c1c1045494800040002c1c6000d501800350030149624044d2034900700500c2145070312034100c020003007084001131b0264003030345c1c1c07405056030343c3e607424042085500303240b032a0010f10940301c07840010b006040080c500b824414028450003581100540c2d60f5400700400000d400078903a02c03400c204400c1c2c010182c69050002024480421400744a80c0281d820280350009048122180c0c00629030704000456540300840b0040c40c2400e14030101100850620740c481101080903400040c06018010300d8042c0c2903281d0000c040d107881d200e8661044807140d8010b4100841c55403004100d03818011041041602c0c502c420304070341103020800e1085000012000c06401c013609119880c0901a00c1c0060700402c100000c11907100c2c42e11400060400d90b1080b000030964004100621080a1088501c0b01d401c0d00111032942c0c070000c0701d030122036070080004054281600980041507e0350b010f541d0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 483372131 1250 483370881 483370891
    0x90204181a10050a12060e0f0309010314040f02311a03030c0d11190b340309080d0f0501060e060c031911060405030702130b0319060204050d030206 65
    0x100400c540d24000c0d446082002c0380111030f4454401001088101010240407444601c906d10110761070a11174401880e00303003400710603a0141c101040f008425603141c40f40111050703100c1210304d0f25040540781c48030f600c405a8400380c0100c0030040d40c4120040c80502c0349500d540ca10031415084603011550030010901c3c510007008401c541c1c50301196500e000403c0c2c4100c40b070624040c1c5001c3c0e56148080d5000021000c04582500440041c050301c00c258949002c90b1a000341d503c500c2c1403810390360b03403003000c1824285d1070f800c01c402c9084070f20403090f0f45802d00d080c078660342800142c1c0785c0786041c020002d001d88103e00c0304c020f081c02c009440c9a02203402090481314251070b01c10691141c281000b0843c01201c41d1010164400c1c000c060f42040841618a00f88001d82850703241e65040406060406004403400d490300d5100003228001c600b07004104000c41400d403403003004505070b10783c0000e03103ca012401c00c29032508007191540034030003698126801844010071a2462500504c0c0181d01e9a1085903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 483373381 1250 483372131 483372173
    0x30a050703060612090203071d010f0b0408030703110102070b0c120919031b0b180f01020a09150905030f0d110309100503190501170d02010b060405010309020418 71
    0x400c0030315010b4028941660301d9500c581d001070f030300c102906004228090091342c0c1440f40901c0050768002030101a04100c555841c110a10740c1420550032030319840c1c1d400042c403607500b0070003000025808420f84d40215410310304080246003080e0500e000e4040d6201c083c0c20b503c4440e090101540c0d0f5a0014a113841202100600c070341d440700d4030292071304090112200000010051640000d10410249a10b5403014203885205122900c85141e2141c0803901641076040500c0c4010ac04403003044040603620f02c91000707500d84420104010a1481923204460316081c965445401641c00340d610880503007409802c6a45550020a40716501c4070004e101201003600c064848848a101004448221002601405500c00b940d034044a140d8001860040d0310030341d0b10341d60300c0d143d06c2c02d004190003001081d400c1d03130440070702c0b2074200e090502071001e1000756850300042210384e45a54042d141103c0c804d00b000a030401181c00820701078900c00246200646022115404001180081079400e100c1c0d90 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 483374631 1250 483373381 483373391
    0x140f0421020112061422050c1314010f08060303190806010f09080303042607050a110102030a2f0a0602041703030f010b07030507050f070810140a090620030a 69
    0x41e400d002100d595000d5100d03031100c149aa05806d05100c002d02060000b01a00800d03010300180028046900a0742c800d80700f01c05c0010442028202c106066018202039016038440851100003e08081c003405a5842405507900000354107176003d005170b444a40141d0310320181072400c0e4500034966002101c0103804034003440002c41549124107540c00a50f04108006d62458803151a20110054207400581400b828a0400b1000700c81c100084c114407441040203010309542c0380750242c510fa24000c46141154418000110616032068030001074080382d80d0020306a807031140e80e00001159182c05012503200d402010300400c0f010f85d00070401c076400300b00400039440601a030f040d00d03488151048244116881d0041c0441c010b964010643c1900c00d0402d940b17000e46540d1003605002e440e0900302026081039504100100f0700b400f00c070107031030603e038003c2020003600030340b00709006406801c44040300e40d102c00040402101e070344803250942c1020300191b010324a00d1040280d41d071040b2211038056041c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 483375881 1250 483374631 483374657
    0x6060507020d0219050d080d0c0807080601030e190809031002040302090c03130c0314060c04060207031b08011506170601050d2d0903110d140f04210201 67
    0x25106580545500030300d80001d03407100b5001c002c9001d91140148014402000c8005003070b9a403000000d02e0203200303907185d90f102c0d429104210221800b0011034414059203104004c5144c1c0e0100c8442d83c42042401e0010300000900c14031860060004070150b20b4848a03c980313001d0100c024054008030382d0480441c0e16924140b00994103a01a6120007500840c5c07141c0030400d4402560061944460100031640c000d2482e030302c5000c410300046d80706850300c1050540042486e0f00a200c0b069104612000301441d0524011000390360300200c4c40b02803c90408030f5044000007020910f044d000702202c9000b4001150740740c0341580c0b068903030b00c1a64081a070141c1604246c1c040c3c41d0a807403041005031265405c00940c1104813003e004242040100305d0140981e1009045a000f08882150340c40103002404000601e005410b00380a10080f12480c0d0005c01607450741b83e0300c505105150030040d2003817900c0b2010094505014011500078035284501e00f0300c2c05c0002e07a084004400414001da0350140c0c04144 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 483377131 1250 483375881 483375887
    0x40306050c0a1709031e0316030e1209043b0f07090903020a060e03032208030a020a0c050607020a0c090b150c070509040f06060512030909072a060606 66
    0x540444001281e445030403c1011294940220340c003202c0c1605403842c2030b2034a0b500900c00340940c664803500007404020b00170038030800e1421040300c3c0c0050800f0807181402c500300d1562210150010a0340304400190110030b41ca4641061890880407004a440004a224040101403807080d894034240b1003403c144203100d01c00100e800c0101c0395800506581d0703082115400285c05040b50a4056111b4804030000080040c403443d110102c13440061a200c1c00c00c0480d940032000507589032106003100954000100b0020401c0729086408410010b0b40c95076580b00c02d4030480b2086202803e940a40e60802c6019900415821021881490b9003071103640c643c202c110440b0529051507070002e000c610308144400784400240103141000c411226015a501d00042000310110303400c45d07807807060311080004c110b964007d24018040443d500d0070005516000b03241d4a0281d20340151040c80b000000c00e21040c00340e042c24032848411310074144c2441d030074140e411020347c05207401c45015140400000322144 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 483378381 1250 483377131 483377137
    0xa02040e0a0f051b030403181205060106080703090c09180f030c170316080603011104240c03170406060f06020606240f0715060f06030c0201050c090d030e0411040306050c 75
    0x41044511811034607240c80444003000d8101c04100040c23440c007c0410031020200d00c0b000305c07030300c43e10040940e503040c10030003882880060030341d0b4181810200f0050000310300c8070780d0106403111901d000683d1050400ca409501040507405841d541c1c980503010141680120304d603401c02d02841d20200007203000ea2000182d0701c0100d515480c142014410400854802c00700c041e0406001400424040c603001c00d40007103684a684418421403441d030058106801c0003001c84003d56850401000305805500d02520b01001716034000690300c2e50000260030000541e11100140010911007107080d0b8651101940d00c0000741c845900c01e07166501001c03100380d0388440002c01942c1c1c1c20155403e0010b0341d1205111908403072011200034010354456140c0000398411640240280c038000340e07090340b91030ba000c0c048a00c09100142164100310400c003c03000400100d0300c0c0c401c0c080c2c64490040c54a410f0848686807082c0003d503009040410002c91245000040e0003a280981e07000c1045890304102c2140d0b0744 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 483379631 1250 483378381 483378421
    0x207060c150c030b0901060c0314030106050417100204150810082a040e0309091b1c0902040606080610050301080a020f0118080106060f0c020f04050a02040e0a0f05 72
    0x502041d0400308080c40c541c0000c0d03400021400c02003200100c0e40c0020b02c940600341c00000c0061492030300c910a0690280d100c170760644403000024030750b5040c0240106a071003503004402400c010f0340108881c414081143e0a60004c0b1000d04544450700c80200c0c060042d100d00c0b5600000b20301c0408143d14810b6460300e40704503a0407400400e5154440448643c20100807200c081e4101094440ca00040c2c0300c85c003415a903007180700701a43d55503000e03002300050a480034008250100c4443d00d0041e04228031000c40c0c1c100001d20311101a0a06403d00f1000a03080d8260300a4000d42043c100085c0a40c020003401c0c040e2074222440c0c00c024109034404c6a487c0024400c410702c0754004007142c000b41c2041d001102641d28103140503003188907010509004654a940040310b80e0303545100422a150b800105481007000c1854040b82d20f483d59000105a45040018603200c3d40c0d940010494440e21581160018591420062803d1818a2103040100140050412014103041c009807911040c840801115 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 483380881 1250 483379631 483379643
    0x3020903071818050c030105090f0a0308182a011b060b033415021e2811060702062b0207050f010b0f0102100e01090206040e070207060c 60
    0x6250804900080510b03003400340a8580d00c00040c42410143c000b4590258003400007082007240e40c506060031190003d107210006c0e0450b0a640d5480704000c075003030000c15007600c2d140c121512800c2c00c039500440c401000a200348150300e100880103605003000500380b60022899001c48030700f580152501c844940ca60466640769080400004849512262503624064200c1c0d60031584007150710445002c188039502e10352410950852008035540b052030242031040c0214402c0412100003039502c0300711805286a40354050000c0345128000c100ca01c0c460702031180c3d440000c5901007030704104070321600303015603901c0030156580352141000710450341059406003615181400d1b40ca518660003058080541800c4030b81c0500024919250026003100c9000740c4c080c1074600c07400701d201400c41d14003005850184e03081610a4449a0300494804151000c1c040040360800c1526413003801000c0205c4002c0d401503000c03074045800c0030780c2c1000301d20605c8107408582100c0c1d03c41000343d804041030000140700b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 483382131 1250 483380881 483380893
    0x711030a0f110703020d0305130f1401030e011b18090b010e130b060706020306040b040b030c0d02010c0206030703020408100509030a3002090f0103050f041b09020d0f0b0103020903 79
    0x854402c540280340380d456241a80d6031607440e0707800a940c0380b1400000354005040880d20400c00304882c080d1000030801100008005807401070a005003200788a4603078181582da64800c07140d40700a4121401c0700e05814080d010702110780340041c1070115801641124460941d002040b100c0c520310502181d180161940e005940e001820401515540071240820b5522a401010075403222000fa01c0030030302c6400e0268503442d240d4140412288490700e4244180d003010005110307502c000c15182c180f0f070000d41f20000050800d00050fa001c4281900094111000008024000358540d01400960f011102900c414010350100d07002598400d4030140a682c000700080040d8500a01c4030600600c041601e150f00440000e562107403002d41454860541d5070000340c0805280b400c000003411010090900304402c1c10511226514003c006000510004a000c44103510110b5802803c0040030013032800c1d5980c01001d8402400b07007030030184000440b81851102103c2d50302900030349050200140003401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 483383381 1250 483382131 483382157
    0x10c031a040b0315180609010b12150105040b0301140c120105030610060f0909020d09030306080307230a081909122402160506090d170711030912060711030a 69
    0x1980101c082c05c00524500801800c2c00035a40134056207110304511000001c0315500c0000b8880744541d070807130361030254004030b1121740c40d1052000d855056840070758001030300a494401181c01414011540a001c021420402c03a09050000080801494000340b205181e41e0b18828903640d41d8041d12108240c0404280911003a8030410354075000c01164034107a196140d580170100100d910421242d11443d8407400904240346d09801604000d0402d000150710300141d584480d02e1070081c19109100d000c0c4036100700d0034441d40c00c200c1c40708096049a41d80e60344504c19005210103100b0f660a00002c04c880100c00070b5202d1812070203840003070b080311140802402101d401e41101d02c0c01c4c10b10112580d800d02c20806c400c584e0000507103043d8400d000800450414620b028030304214000c2e01420088140002a049040a40e005070441c8540c00c020300a0940d60000c28218002c0320381468105114000184a040c0005082c0d030250601c0d8a8102031510380c840312030740303078801c0c40181c074007141d07140d440b080b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 483384631 1250 483383381 483383413
    0xc060207020105040f080607020d18050d05030c0d050d060518060d03091a04090501050904050c100933080c0415020a1502130605070506060402090111010c031a040b03 73
    0x891400d00c1454100e1070131391118645c0d85400c4c0e503a003101c012548035004101d40160108144000d02c0c415040208059a00d00b2004021807000d014241c011051140c144041103410000c0d00e03080d04151051701c084c0320300183c008286400551a402c0e110341804030018003401c10515049480440700d5800181d6aa04414440e04612082003101003040b4560009951895001180700300895800c1c942c2d9600e191401c003509541040c0c201c80d204041102c14400054800501440003600079030395010927420707500c02500c1640b0541c0c040f010003007400061510b0707000704140c0750000c02d0034030070301004200203001e0032a0310300e42c202c44504540c40704000600c5041203648907861050386078811a111180180d03502001520f158000490083e004601050ba034140282d014004d01711a1400034103001c8544c4445543d01d03009000030780200d60000700000340381d04c6005600c2e02c10488000a2100c0a11088018014070040600101c0c801d180d07004440070b85032500442d044070384014000c02d643d1201a40760 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 483385881 1250 483384631 483384637
    0x1a1c050a021507050708030a030c17011205030f0c0a030801140a09021308030c0a0c050d0314030c04030f03090509181f09051005060306010b0c031b070909051b03030a0c0602 76
    0x160409440c01e03c080c030000f0308100081009001004091600c886601c800901942ca104400c1828803400078080258140d4040e207060440309100020000c6c2100742c205903080d840b0742c01e0111080711001900d0781c200b020010b01c40c01c5040c420340e9030b007007140c0c0d98603039902140c24000c0c00709a100c064a43c080042e041c990300a0080c0303540400f5a00c0c05c1595807404589140d0000b5414001c40e00f00c61190b4080c403a080403103800910080c2e408805152840c1d80040c560751f1180903060348503601001066800000c0400d0343d01642d40085c2a2008080e5814064146035040c4a4030788152030902c0054042c201e201048040c22485200500c1003020300042032040d08525454005059907408820300860010021060040d102520001d800c0c00c0407003c0c10300f0960160010b844281042140d00e0901c0d400104a8142400400070702e000141b51100882c20005207611044090b030802d5500c5080c040c3c041029900c4410f200c003002c1602c0001400c0c55220f02854403c500864950215040411029001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 483387131 1250 483385881 483385909
    0x8040302181b030c1c02270a082806090b04031e0f0e010e031501030f0c09090201091203091a220f06080c1201030b0103020906040504230f011a1c050a02 67
    0x5401c11841e2000c2420780101c03c484089081208000380d203190505003210005440d98002030000c01129840f5108098440141034494001800e50001840bc2550002c0c010344d80c0642c0e40411400e083c10300410184401c031443d44070020020307460320500d00804820f002c0b004103803902168250800015246c0c9140986055054005c04c03503000401c04440c0e104c0c0d4080e6110304000c032810364440c240700300141c03000d03000380035003900d0585070714051b13038010210000300c8101f020030452052051500b00da00a006600450a03034070383c038448020700c003c000040c0601c40d000360b60036003107498505451100751240e441744ea050242c49010602007a0f10034841164021a440040340c50007411007121040c1c04002da105452207000300c00103004624000f030186170004401c0307a0500c014100358850040346180140081d06203c2102c14210740958284607102c00c101c04a002085500300d12030116401e1008040320921a00c0c00c81e01482c142900fa090b0b081110b40c0180040c00309688035400e2082c41441001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 483388381 1250 483387131 483387187
    0x10c030c1e1e122c01061202100c170301150e090106030c0507080c030406030c0c11041a060d140108160b0d06030501150905010b040602150408040302181b030c 70
    0xf04119001c8490700542d03409010301c244080d40095402c101070041e8090015024080e410802d0400102c54102e00c6920b419030115141c80381941c1110050f214042d18000c018814443d0042d010095444400618100c4070440d03940f90b041c85041008444031150301e40099800580e940040c00214400d502000e124045414402c1c6400c2c4107859412041e001100743c0c1c2e07443c0d40001000d00183d640340c00f99100c400802d040082e00071195554420035000c8a5100780d00a560b02e1003686200d03042c070640f91350007050140159580d0704840b90703a50f0140c1190360a02401f44628030000840d08400a141c4a103e41242180e8000038240b000f003144a91005207a2460b1036119a00400840ca0a11500f034184810408070703640e26142c12496002e40d4416405810030801c140000c0150314cc000c502f0069800d5a10401e04030b560310b51414500b00e009580000e07401007030030304c00e6048417071040c42a1401368100c0c0083c01e416005031103006ca4688400c07500c0c1100104280000b000f081000020141486030b07480c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 483389631 1250 483388381 483388397
    0x3150408070609170403050115180506011809060305010c02151302030a0b01060e01020124030809180c21011a090d050102030a06180e0601170708010c030c1e1e 70
    0x1484801245074480c1300036812060014013041005003d2095080000c0005540d50b007003450f20b03415401420240f0303c2011425240e4001845076031094044140102401400448542c1c440c2c1030a0001e020a00045603958600302c40c1c940c1140c0006285801a44180c0a40d00103607580e412511400c10340c180126018415107107000f00041c81208428080c22055880403820300040000900b51912080064648081c4003104074845503280d001c2410b81c0e80007803d580d510324141021480381c10a82c7c2d1242c0080c0a04401d101321585801c004000da5000c81002d010840740c151a08040401c0c02c2c85818400803070051150388000320f0102030024208000e08030420310f030707407a02ca86081e0b07481160103d18103642c88200b80400d011090511044008400d801c10400c2e62480310285d4074541070080050b046409030500703140410800504000d000a6402880f450704144406001382000003051707004500320000d0715020004021414800750b04e00c0da100804a8034111101d904400c013003130302c001081104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 483390881 1250 483389631 483389633
    0x10506090121060203070f0221030a0c020c040603060c0f14030f04080c0a030f1103030c0a05031b0706020403031e0903060e010e0604080903010c02030a08010521100f0b03150408070609 81
    0x61002d584207002648610310176016940009092108511114880d1112240442109e4800b1400d4a40c0503510700400100604660700c107900d081180022242d2280c1015008001c001198002096846203a25174482c0c9040d401810b80d2100c1c0200440803d055003400080c00503e450240280c211740549032151404040300552400c00302403141c190040307940c203001202e07129441820980800e80510295041d42005403c030030440c401c2d10f91680421102002183c80040b69a124401090481c019180d49488602e05100a904a07200a9020840c0040014000c18040880f4031420a00b641c40d002c90074150f5981000422844642203142e640e950f481c081201d1003006603501807070081850303a4030b603d0340804060a50b5140810103003190018000e0203500c5800032241410350b01d044600e004c05116603011461215103200d00e0b05100e07c0703400d0316100b0380f200c01d03400394070300b41641c0009202d0903592005050303843c00018026000d040c0b0300400074000c211843d01401049200d0b050115510700700b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 483392131 1250 483390881 483390893
    0x80405370807061b30050424020a0206160207080708060a0501050a180518012a03020c190f080406050307020d0906050f031005040204150e0312070201050d1d0706030509010506090121 80
    0x841f02151001e5018081e91054641040e910700006201041985040f4400c80300a446040107402d041e41110780424080b402c1c0c0c001d110007400303010400102c49420740d80700d224541c2d485096504050310307840c0c5070000c2250705140e22040141c501d044140c0d1010514808090001c00c0c0003055000c0c4041c140c5588500503e0a010f40d03244810220000151500c22806080820006c4609003082c1481085440e030000004100c04056282e501c85018400007141410140d511043c400107000c1c40b0001380c041400f94002e0301440c025940f650882e01021852201510784001d94002d01d0701003001809602c0076188000020b60340441c155840802d06076941010409a0701302d03400521a00b600450801d2400758000c1064021880482c010258040748002c006458492003101a041003000030300000d0001c20350300040700c00c050291010040d11031801140340c8802003401287c00090604010418141c014041c0502500e001803140b0402e03441e0944400d900c5c3c00307031200706c03031a802d00000860109003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 483393381 1250 483392131 483392141
    0x10050901021c05040302030601050a21030c060207060e0d14031f090c0503180607050d051e16030f06050604140111060f040b0601080405370807061b30 66
    0x41580307030f85442c1c82c01c62041505009058000b64080c4030200001c0000c030b102d0403884c00204081204504482c01c2034101142c03150541031003d0300b200e000188030030800500b4dd005516108900c8265a10804401d0701103800c3d034103484540622020070300c0440e80c00c050701100a40082c1d103050700c01084580d5603801c0d5003662030700400100490404000c100c0c1c4002459002541e206006014000ca440c21f14005003090051001800c5880d940d5000103880541c40c200003128041d44507115a2103103440e000c49810901c1001c59040000e040c00e03803141c60324055000715029220020203003030400d41042030500c403501d030002c9124101b10050350b01031420113040c010759014000900380d610182c60039082082041c5009000e96040082c00c00400010030000706000c01c0440019030000160001c0c0900450300b200303694070840f40345218a001008000c580d10040810f00e100384821302c41c28400c1040c00e0015200010303501c0100d030400208072038511103102118042c81d00c04120303030300c1c50f002d051040341229 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 483394631 1250 483393381 483393433
    0xe1201050f010f15081b1b060411030106030215090102010615050c0d2105090f030409090b01120807120519031406190e090c06031e01050d021005090102 67
    0x8040300700140701021451014002522503640c0c0d05050500b00440142084030080c00c210303221461a01040340b0b0700000702140d0414500ea50841c0c40c1400804400e5201c900c10f5070115090202162501413a04060058a04907500100131203440034802c00a101c480d40805603540c11956950380c0441c21014100e4002807a0940d99101900d58104031125403424555035070700424041541000d40c91200182d4520000111508005c02d2a80350a0015840c00785601d0043e092401302240108405000790300240f17695010704204911a40c0c0e0700302d000002191910042c281110030009003022589240480e2640181e51801d00c0c5400182c16000b00d0184070075a86100080d125500100c080007002501c1d904070504603410a10702e1507541c4c1044403451035203e401d42103401c10000904540051010307182c118006441e8036540e290015810850404403541200c0d04001000045018280703101807101080e0b02400c1c03103000015240081c0c1d030035082103c0ca0350452281440180c1c459901d169140080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 483395881 1250 483394631 483394651
    0x607080706020d021314040207330e030d051503191103010914010f0608211204060b1e012c0a030b1e09030a0804031215050108160f0e120105 62
    0x150404086d040080254900c50744a9801030010a000c18801200c90043c400c26040b40420080d4810164641c0c0814903030300072034540b411240c9102010080001c000170210341c101001300e0760b07405041640c80602d10081d181c250780000c510328400c1015201e48085a4013a061405040080c10000f81c04d44009900441d51400c0c8000c0c106c200031024001d019440c0601d480522502e42040740c900d58441800ba1420000c031f07510070b1a0840c0d0402c54048591030621803595205518043c107000340a018a111010300036002400c0c1c5a22141c1682c030040307901d6038140c0d81c0c6c140043e80c10100c00008180d00300f01301c13600c2107038015204003690f4035a918002103110b801d400a941c80c0182a00c007010b00382e206401840c24021082040715071010003103d54045c0281005225034032181000c64449415146420b0101c0c544400c031001203409481110444000340d0701c0317600f10380d2000b42c2c296404502824a401141d044950342d100e0a01402c1c0c0481c031850050440c1218010106200f401d44000303840622107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 483397131 1250 483395881 483395917
    0x603120e0a0e0a09031403040308071b0506010e040c050a032a2304180b13030512131b030b0415110d09050d050a05030103030e0411220509060607080706020d02 70
    0x20180c005000300c06046e40000c0841c110f280075103010706413460040c20b8408109644400f00b0b000041d98041030120754000044841940e101c2d02900b03620282602c05a42c0008007038400205803030941e00010903039600454100c1340c143c1120700c8141941c99801003406100390200d002c03d070030314054101031148075206284811541c0d032074140000c55102c800c0300300c04544520040c80c0450855103450390080f260301609070719524103050460b402d0189400100c56101e4000900c8900003a40c8260345655000d2005191441c105400080c032110301444004d00d1855110006408155001c10807038404d4810f0b94041101504c200c45203600768409c4070380180e110750b54907002d018060204415105001d40381003040c0390042c640c2c8090840d0005100080c10011011030902707240d201c0d50006054102c0c00b031440350b218150030604e5401d10300c0d0304240c04080c1035110310010395451b054a143d8020000501030b180382c900c01d40c841c0e04a59000031800e035503c1da002c200450008416100900302c0d55480310049117 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 483398381 1250 483397131 483397133
    0x30a1a10080615330703020f0309010c0f14010c0512060402090f21060412080a062702040e1602060703050907170a0204060e0a0b040603120e0a0e0a09 66
    0x40031401a41000509034020410841c0b203011041c040d5520850403981034041140090850f441e20241c040b800c4086040c43c0103800c0901d120601804940e8440c1e020f0b10f161030703540700255a90303000c1c0e50b8130311b40024031500b00500400c8440c0c07a41c02485000c0d00081c0e40008a00d103407242915940700600c2c0002d8800141c8260030490b481c1816000041224150b10b80300c5014005002e0064a60303031944100c5e114240c1c160039550004c2c010500c102070784207841243c9050304010780200091108003000c07507284000142080c4e180c0c80b5500994211500c0002c104502c07040c20741401103128420201b09034200404a0a4038000c00482d11680b0300a02c414030800c0f11003002818001c000e0324140a040c102001d1007204c580c00f01d4100140e541510030708100d0b44015141c0383ca03113803140c2c8011790485d1400c0303070209203505440c0040d4454881c14209101d0400580117010485403a440090450070714002100c2c0c84d10700c54503840703502150040005d0351042d1541c541c45440034003502d070507a00b01c0e90f13141400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 483399631 1250 483398381 483398401
    0x6030a06060f1401020105100605130e0103030c0c0510020a14100504060204080f06010f1202150a0f02010b0f060409050c070203030a021614090a0f23040b01150f0509030a1a 76
    0x4002e00c1002e05c004e00660901f005042c6242e103140c0200001d0020210b56031102c03490400706500105461514074a855035a42405480142040301c1074a011a180e200411241455204030f100c000c0103900508074941c032504c4104114200010110085c000e00460003c10a0350380038242c0114003480d00140e0344c5107441c8000d840c001081a4410950b0030a10041204070b1840440c2004c6a40d80000c0da01072031640c3c4005102998080c49811100700f010503604c0001c2c0d40300c40c5410541784039030000c10003120f80b401001501a4140724059000400300b00038008050b030307034200c0da40040081d1181820404254000ba040d60083c0f601d81006a105600803811800102010707001000400e600444044a130404201d00d0303440101500798550f2110481c0042880070307400380c02c4441c0a0512010340d4a55081c0d00181240e064800791890b213030307810001c14000d101c1c113200000c4c0e04c1c1a03115400c205540d038030103035950703045140c00c103601d8041e116856020640b02503605644190b13510810f100d9203400240b003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 483400881 1250 483399631 483399659
    0x3031b1e0306080703060228110c03031801030f15060c0b010509060d030503150a080a05150f06011d0904060b27010605070f0606030f02100201020c070b0306030a06060f 74
    0x14108042c2004401c004112010582d6000e998101c503000d039403015407490312160301105d41c203130413285041c240400034010340c8110b00e0700c40002043c0a90fa0b8140701001059a24000d0115442c50b06210003c40516503002c0e506c14041c000c58110041031901041c2c0828010002d268050740100f00a4601d0b907003002850655240540021103940802d41044004998540740c140c500506001001011800b000c0b2400d02c0e1000c02e04005001c0348859841d015902d07129285444200c50798401c00e1820031600c0400132813544a403d1030840704125544801c01103c0007901fa0030021031140340500c04040644030f084a20f41f10358050300c4042103850b040000c0c00a1070554001c0442603a00701440c001c2d4031107101a01c1030448245190481c0c4901d4203040640301050110801469246440d40010401043e01c1d481e21420b40219022441140e40d03030016030a0344540100990260440310040c054003d0305000b0b0740d042030b400390480d46070311070598411080390156001140004201c40c42003080c00b40301606 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 483402131 1250 483400881 483400937
    0xa210203250206090c06030c0d0e0102090a0e130f080c0102031303110607080a050a1d0106050f0d05060c07080d180c0602012a031104030b04021f021903031b 69
    0x2400c803480c0a00f0115199003000317072214840c81001003c1100c420000080d181800d109002c02c000303000291180b14000d600815005014901c0110005007441c1c86048181c4180a81034000c03c110402d950f0b030b081001c881e0601103a80501c1030010050180092001d10300c200326441c0d00056080710340c00c0244c21856215205c105d107922200c00c108526900c0340c90036402c030103a804085416141d0b40300000103003514030702002100b0405003201c024880150401d0003110426183c28110f20702c3c00086c0100302c220468007410560004d00420b224601d580010900c40d4004c419103414603085900c09801e45503503648c030522032602c80e11410140104020b000f4001c11140c0004c20440800314070600000d94035400b0030200002d000d090b0003840b4002c1c1c01c500a01341420200716640e58403440d15110910040e2000d80c015900841c1c42c070384441e040c0c60180c000020b03e80040c50000021005c2c105102c2c0b1130702c401c0b0209612550200ca225018640c0d224502d00c068845a03030011034415070254004040e15 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 483403381 1250 483402131 483402133
    0x150402070206190219061a09010f150201140c070210030515010c02150408060a0e010b090c0a030b090a020702030f0114010e070309150207031707050a2102032502 71
    0x2258800503a520011196500d9429880da00c03407901450341079081540031070140810001c0d1600917800c01141c3c1c2d1007101c4004050440c1c05401d000e030803c0c000000400d0145450070541211b05009950030409000c40f4400e040c80003081040c800390031481e07101000d41e59860245400300d101c808601d00341d032080100240920302008245880701c003003c00e01c4001100c0d18144250303070300c207002552101041030b9000d1040144065503250794503910303580c486c01241c1d041910341c500601a101c004041c0035800041070014064500350301c58801d014513517071000100c0424181e48120100c1c2c680c4a410030103115124030315005840700424010f250501d909241300d226203034945501420314102040881c1d05407254480800b0442d55480b400750010800d001c0081c0c000901c3c4100d01c1e10300c01d215002080038500c43d03901c0c404c00500686442405543c181d4650010980900000d1482e81c800c01e010011351310420f0748044010764500e5004200e0303200341d03510000740301d146203014030001c0c560140b0022004144 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 483404631 1250 483403381 483403387
    0x30a030b120a03051e0708070803010e1501210b120c04061d010306021e0c071805041101030f0914030d180305030406020304020a17150903311d150402 66
    0x183e03000b085485104004100300c6500d240d4500740e140c807001900d50442d40040d520340e45242c541014000c41c0c1003403088004550b080070000b64100c0b562000c144c140001a1142c1c3c00c81d07040c0c800b00403c5044e0502c4603084903603035410000c0d0940e40760340c1d10302c00f01130360329014003010b46800080c4801c2c7c40854004010b003803103030b40e8039054880b1004c041070704494200000588130042c51001034114a19119200d02d002404180198148000304079103040703c1c0303e01e50a45040308030401c0300d410769404031b07000381030780c60340d61f5900c8159400394000f0001410364420000d80100b8958038502c1900d03903250441096480454511082010761150840f00c10404d40b45d56030103540c580e40200944001070000b4440b603008404203045407240d8002402510020048406480480148507a240142440c41804401410205403140c80c04800c4600c4180c0c020160307214404d080040e100d07004101d60694003801e0300108006114072903c488800303951380702c490070017042c1000c00f92034442038000c0c0c43d00d034880c0e4410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 483405881 1250 483404631 483404633
    0xf28050d03090e07020a0f150b01080402060a0309081c15050a030b0114040908030109050403030c030c02190c03080a050301141e0108040606050301020c0a0b220b090f030a030b120a 79
    0x40001c42d412180541d003140030303554401000300d00f0030405c144010005d5134a030698104100703540e00040305281003c01e04002c0340c510400110341d0076000341c0d0081e410450030400280c5480c0329400400c0350300d0080351114034015a440c044000058604821000103549402d1466006c41d002c001400405013280c10400b042d0840d12444c00b481010710520752407418010500e687d039204c1d9009025890341100c0800d88075a9614074031009020100ca0480020f032a0040c02c0040c1e600038402c034401250554000c11607010200001c0ca0000f0140d40180d41d1807064007000400201000001e11902d00195229610b030351500f54404004101102d0107407180e480e00003030703900e01025050620801c03802464003003856140d5040c604020090780e0803481d0554000101640348030b000281048040c4e1040306014032035914070142c3e0444502c145402a02260054030301e00210380c00031403c54001c0007640a440261080c110442d1a6500000002d00802e840312a40006442c00c205110000c09100e0040c0c0704000d60303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 483407131 1250 483405881 483405887
    0x2f12030904110408250506070c0602010c1403011404020c0109060b130c0206060f010c0c03061a1f05090303130303081006030b0a051311041716060512060f28050d03 72
    0x41110310240c60f5260400220805c110801d40c1c1c0c00a0401804195603408181080c585144150041030055070810340a0503000b44500c0c0d42c04e6446130400304290840e400c15680008100c04140040e030302c540c003804412010403007803003014030180c401d0000003105c20650080c03000418000c804203a2540c680a403003600d140e008034219a004400300d400e2030010b0070a600580c1c0f07403100d101000d045a515400080100861503014591118480d8410001c0f44a2a400c10900107560b00304078030000b948100480800b806417014007d84000142030f2030804003106070550100d50305a1094001032410000d120566052904c084050b24443c0b8003848942540d02c040303217001d5000e1240ca03000b41d260202008480041b03500c05421851503042059031a5504c0b520140c003141c01781c44141d154050300f2070041d150380c0040851000c6031540e80321070b401e0502c0e07801d403060854070041080380c0059848161081e01e03950a03061200b58440c41c859a204416a0b400031080074101e50040c50180e8606106c000100e50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 483408381 1250 483407131 483407143
    0x307020307060504141005060a1505070204050615030c0904110703021b04060b0c060402030706050301030c1809120216050f010c02061c090804170a2f12030904110408 73
    0x380000780800c20f51141e03e0f000e295540801c41207141402030b1b00c0d007040c1c00a010b8208038020401220201b0b005030b101c0e8262484240c3c10103841700442c004008401c01410035410080d400b2200608070100050400d10a01056200f00c45058101100150020030b6290910900c02c41405a0710a035003400401d42e0082c0d034a0410a41d00103040c00e02d2041c07181141d44503000313900a8024008800c1d114030013101c0301c6a8840c01582d00b20b1003401000408142107204109072030403a500407030b4100c0040d00d041110414018612d080f0031071152502e0f0242c021800a400c2903450a120380c7c010030440710031594075541d507503140d0442c44c80380458054001003a03900c9074100c0301854044035005c1d565825820049824906240038102090910311600180801e28020f0030071940400131109440d21b12003d20780d169101804c00030035821000501c0e0355044100c0e65020b000c00740f208558224406a5000a145003030003001441e4a07900006281c2110b040c45e0044441040c400c04585041504180d4a140c90392 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 483409631 1250 483408381 483408383
    0x306060403331e051e0a020705030f030601030b0f010e1507290702070b0735190306050d02010e2110050906090703060507020a020a0f0f0b0307020307 66
    0x91a01c4400d4420b072240b40526103060812036200c00711404140a19201a0946400300d01207541c0c0014003400c007800c1e5004492140b0722a010000508441c003c0d072840d142005001085040d17401c2c401e031b500244041000380340d02980b0322000750f02ca1800100040540740140031940c064410603c841c200c590304a1408500c00d0780444a01040340d04240880e00540105040a4000b024110300e5001d1070141281003080d901d80d0540c03031741c030560b035151060340c0d144010b10030001a200100700060109203000b0400340c0c0b0b0f40480004640c84203000865400b06600b40c00c000f240300d00000f40302c06014011000d0b0b2400c5c006641800c0c400c0c80d1a210004001074000b00300039050021320000c1d80d00c030b5074a070424001110b0b0702c407003a420f03480700d038040079551844110000a442c900c1c00e0040381074500d00040c56485941132000501d40c8504680e15880036050143c003400651203010300480041c1d4881100c4000382c1a01c5e030000000c0c900c0c01081200410199000c00307442001003050040d8141e000c402c070b442103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 483410881 1250 483409631 483409643
    0x1150f080c0c06010b04030611030f1308071a090705010f02060c0904020c0703050a030e0103110304060e0102040b0403110f060702151c090503130b0f07140f0307081e0306060403 78
    0x10303640c07034180560500c16294911002e028100000c035070349204102074000d6134080c120400038a40c8402402c0c50510007620300d200b052140303400086c80441c50a56070034250780b1a6107440e0424a00d40e80d000b030101c00440300c68458200d40c1080042c6c2d00700c10071046008107000d1030800b0b01d0004068010b5140c107809803540304000b2000600c0740e1a83c881d501280c1d21808043c046402c5a0b030749082041d180e2030301c070904600040011550014940c868059064003a040700398035451038950399034400007041d0074a104035280d5000d120025110300854086c10080d4001e208401260401808106840091808152041c0c17014080f210242c0c4892a481083c021422200c1d80e84035128040400e01100308004800418282031110040240c080701814607201c880602c40c881e07030b4079091444030034003809110b040005018428640864280000140c6021440050343e0303a04554242c2c00707086511000b81078800040020b0050b03103a07464800f1044010002091240c207500b080000104244920322003c0e01d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 483412131 1250 483410881 483410897
    0x60115120e03031303120605150307350c1201030f030c020303040b0405040c0309150f110301060906090f060c06091e05010501080f010207020a05010c05100c08060901150f 75
    0x20680d8035a0169620000c11801c50b030312441c14124904a00d0808001240020034040d40003501c4c803001c0c052103056480042c04800600381982c002105900024140340411045d032840441d440c4503040d0313450400170350800385018041c0500d180c58035003030050031a0303e000c90100114810040341411560542c0d40c801e80558600c80207040c01c40d65070781c00e084065407600000074002802c002c0440280300302c0700251740601c240c2048820070380c111100168007074041c8602217054803560855520031a00703042800c00c000740c0d076801d140135401c0640003608800c000c2044400180206c6800205800c000e10007500000c04441c1490700045c074030000307404c000f0500b60b100c6c40d513101080001e048151801d00c0b0407045079680009420054042c007020711403164140079a805035038800c00d060007104c1d590780e0050000740d80146440c00440b000e4005601c150f0740c9000d6250040d4a0260038020000c00c180c559a41c0c41c0b15041020801c04c0070a010b034072030842c0f04120005c8448003504451161100c5145003031001c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 483413381 1250 483412131 483412157
    0x40b04020d15020406080709050301090f1e06092904081c0209040e0a02040c020c150c0f0a0501060905060603010501021b0415120506100b04150512070804050c0102060115 75
    0x400b0280060040c1c403000c1c0045008103803558850145480b40001d951030508059031441498202c40c00d00c07101500880016071a0404941c4005d48140214031f00080070a1520311515082e0403655419011100c012182201d0101e00d0840b580118003402d8410140d042818196240e0403184070380740301e286180c666100c4094152005506940d40800040e1041c40601c040000790703500d40c0e1903040c0403489945001c003030000040c80001d00d29410039001c5c0c0f00362140092007606848a800400303824908ac400e41301c0a001c1000d0510200040500c03602c0085810303814135080c4c0d01900c400030500e0f80550341c144010030040e0782c0010b01e480000090796411400c00c1c14035010070054554a40c02900c0c2c035007403c03c001030098881c280c1038000350248081d6251602d030040803003201c244ca0b00c9086080d200074803080c0701c010380082036800340e8180c5080080c545005523010841400e01160054003258581007040140001400102c00201003403000e0600c942c1400f5640e00c0098130030b09c41c00200100040d08034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 483414631 1250 483413381 483413393
    0x170306010c0b10350102190507020d0204090f05060c031308400906030f02060c0106030b1005010e0d05071202011101050a1b050f0307050d02090d060203091203040b04020d 75
    0x210140c10524800c0083c003a81c00e10606001c0f04404640384c0118418403042c450020601c2075070b848041501003000c0d00c0b0b51007007088505810541c401d0740d001ca400340480c40140e0311031085880c104d1007844c1d5000341d82e843e410140d0401000800e80380a00300c080081160408002601c4201e041c0e008401c0f03521110203540e66207152414030401035070440d5a030709100c04040402c40503490781e10b0b680d0a10704000d85802e05030050703400700d1100070301c4103000b1026040140ba01002a15800039020000184941d9986a95441c00c00958544a1200b0306030001d01c91542e22900d585010b4400352030b080101d500711b59529a4501d030760b108200303648111001c0c14003160701c140d1100e1002000751000b80480d040043c1c030980107064403d65451448080034070b4200180c0184107407101110740c5e542050075540c5482050340c1d035a20008101034003070703420050b541d0980c3c0d4000142032441e025501c0182c07a490116030305442d0446010f0883d503026001c6c0b00300800281d28190140d40103606803900c42e0035806a103028 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 483415881 1250 483414631 483414661
    0xc05030c0a080310090e031e0d0609020a0e01030507080a0c03090203030304060615022407050706020a03060816050d02040e010b03071502120a020c090414030406020a170306010c0b 79
    0x100340c0c1c0941d0304444280801940510b004d5032101c030144d20782d0f0781c0d039040320310845400c03030210041178205122421106510440110090b41c141450350302d403003842c50f01c1d030049a4440d00003d69595010030480c0c90154000c0c0600310081003820208021b0902c05c1019002c0d1800400140103e40c4623820700007841e210360412502180d0240c00c0729168142482c0c40009001035000b508294040c120600c55940d00c005000c032120a0000860b603155041c4801c0c1d11205d860041c60381c014450104821000641d03680b0041440c07603031070780c0c00251890a106210381415025103c170041000c0d00c05e0140450b694183c2c1420541d54101c030009001110910103070f015210600d941981801880d00005c1c071103447d60184009001181d007a50004100a0f04006840c0201195403005a0140c0d10120282c2080350b40710f50800d005074002424070f4000d0300b21929540c060381003403005070408401c00c1d080040040028904440c1154120300710301e4a81c0c0002d00070303000c6060182020200c0d0700424079500740c050720 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 483417131 1250 483415881 483415897
    0x230f040c0201180803010503162102011b0312060602030a0905040b132a0f1e0207080303010b0c061e13061e02030402100e09011403070816210503030402010c0503 71
    0x3003c00340c5062420416100c1d0024442c460007805041e011524010110f00800d0035101c03001ca4080342c3d52680c0d014070600f0700403260b04a05021158000c9030120300703810700c000c00383c81c400d40c1c4c0c60250b0203c448000c010b5402d030358800402d560050000760804c0350001d50a0301954400d4a0018006d8000340c0000c006103500c02c240c03030210b481d104000c00da06031444075800400c44080c00c0da100b4500086000c13103902c0314000303803030340091600d421842240c43d03074114000c8520003505c101d4244913124443d050540d803082e8030a0191650000e41c0f1240c03480180403895100c0d001d41c0e0a004908240c42840e8480040103118414800001c00c2900c108012640004401d5a0716404204011840c002c208001c3d4400d403002c0e4840d21503041150206882880707100ea00003405010000c25910f00039030744948007455402c00d58140100380d8040358030b00e401c10150f42a91240c40609401d1464040380254042c1204100403010741041e0200020030400030413030341c00c00e60a01e4a0b6011103290f040850550042d211 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 483418381 1250 483417131 483417161
    0xf1b030210111c20060106050403060207080c0d02030901090501090b030103060b120d030c080f09100e0316062c061b070b090723030606090907050909030301230f040c0201 75
    0x342e280034007a84800360440d401e02514060804c4d03040d25040c29075503542481213400003001000284005105a0043c000031841a180c107402c01e45840503807410066030309881030050f07102050042156901c43c42c0d100081074282000010300d42021860001407105000141846880c0c7c04500010b0b2211029134a00500c46400e403000c01c2400c8a0050260200410400001c0c100c40f01041d00e0603100c1210714014030098000300882188a52101c01404070341180181d04d00091141c80c100e00304083e003010074140314002c00035003124080d03194580b2500d50b60700d1690342c210140c25150400030019801d5044481c191505032412510040c0d1060742c030030880c00038020518581031003000350b8000741d850306540450b40502004058001401c0c00320781004425640741e80f180700400c8050130110059078010041400f5951402d44800200700c00c8482642c03000015840000100440144100c081810403181704055008031401c07000541201d600d6000d5074407441c0e03940c49508105000358008020528011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 483419631 1250 483418381 483418423
    0x901060309321e1e1507031e05010503011a030304090b0d08040602030909060f0102030d0f23011406090a360e160b04030314160f1b03021011 62
    0x400c8207040e00c3d105004080d032500c1048040b10001041c00e941140d4034070000f0083c0300c03003a090300894000c554040c041d031082c140c1d01c40144290740728400784034183c0f12a040c2c010580394502828142161020b04800c0d4100176801092a80f5640110450b8100c4d400708802007602641e90001416110b810140140000400540003c06940100192400420888804030b00f1b035184420b0112042000c6000c5005030010054011503882d1544041079441300d11100003448d0f00502d1034400c00383c801522007010301008400400aa0001ea01468030a040a48102d0704188400380490f0b2280118000c4180d41c0f4002d4002468074480c000504000b0740307610301341061011082075180003c001c2e03070f200c6d401240241e8040000440510040034111215203241d28500362554408550300341d0035580b1498254410854003515802c0b90035500503c80c011281100d50490600c0d203d004e11194001ea0740c0703841c1c00d22a081015075a240540b90441d085810506022940049441d090016130480d201c9001800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 483420881 1250 483419631 483419653
    0xa060b0913110a031b0807020304060318051516050c07121a0a0c090f030506010e0c1201180b10020705060c0c1e03010507050408030906071718090106030932 69
    0x981c104041c80c040241000c05138040c9503901b11100d0b0005c50341c1c40c025910420003082990f200ba4410401400c032049007442041c540d555542c1820b4084592841d070000500074010000451442c0e01d00211f010b0400d185003444901a258680619100ea41c4d01c940748803009000b03128400d0402c4c004007401452048161502110708002040d07218000300001c0c4c1c802d0360100ba03440e4408507540550380c00c01e004182c20382c41d0480003070b080724000b0000601d8803004d0000c50304030040c449110703028114845200c0c0140c60b1780c0804d802125000c41419208105c541906002150041020301c1940c100b510400d9880700d0444140d4540605403103034135007082c0e040591460070816101001c003280000c40c002d00954646490484013800f0700d0081d50f0032500704000788516464590b00a203980e5101c0d50f8814040c00031480c0c0c0c00c19a402c400075001910310302010f0002c04d890900e221902408040c10704000506194480c3c0002214850355540400300051030f0802c95404100314540c0c1d11201011208601d1031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 483422131 1250 483420881 483420887
    0x9040203160228200a0602070e060f0d060c0e1002010506130c080705030709030b0c03040203012012040602040b0406051201060f050703082a0903060a060b0913110a 72
    0x12441c1200014003655144104201c000440d410302d400000003040030002d11500c0b41845002118440442c40f0300c2110b859009460310780c800d100404458002c0c02d070307681c508403410360348030b03c0101628401d03600101040c20f03aaa4211080341c030b55030407176030008802c4004803040c0c03a000e84c1d43e43c00036440580080014913040d415048039201e40400d54803061080b51401c031440541e4202c40c2040301065040c4c0000310064400c1d40659440041071404c1d0148507940d445555a0710002d4a001050100000410065003405d00030032f0020f174640840340001540c10051083c00340036501c0d030011143c50001c04501407003d9501564050708a00c0e800766030300c0ea591400900140e0100d920000710019080c000039509000301807441140c02d4a4503514031f0000329503004c0310300041c000c00c000c0c0c0400b43c00e4101c500b00c44001c0c03100b84041d02ca0a40081ea00c414890800d46010030043c5021041420400140a00b1004c14190788031582c0a49542006030880d200b101c01410100201c0c00ca10303200414440300300c82d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 483423381 1250 483422131 483422161
    0x30304090c030b0d0c060f1e08090606030a0506011208120f0f130804030204050402180c0a14190302070804120c050a1202010e0f030c091303020f06130201050a0509040203 75
    0x1e07154608004504050051044001190a001d40f18003a6464100441030141940d00702c45481490a004094510407049002d004840783d05400680203404002220004200b07442d0000400c4005128130030640c0d403466980d04050061100300b030351039041981007046440581d064051130b03800b49001413030601036030b1211910864240070104c2c11480842e0009034100394203812071780c1080c0a2840d0a0654007440050030000c1c1007203801c051008203074141130701280d03c641e0140b007260300d490740e9075070f44030f000200310082c41c032100307007a07003000700700c0d941400000300403c04000e2400d05025071900c42c03a080031a994000c4c0da10940d01c244402d030030141040a0f0b52060020707280c04481c10020359855407002c0c1d8402094040c02804541c01d0b24403008a49070640d140b034502e0800508a4040300c0005001c03c02c498415a0f8100f4010192a054420181c0500621a0648000c03000b08014a003202003000b07612490103010341440400606001007600c81c0c1d084810302400504107550364141180e071080148 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 483424631 1250 483423381 483423401
    0x40308030a0c180e071b12081f060903020d081c05091b010f180909030203090306130201050d090c0f1401020c011d040f0e0d110706020607080406050a060503030409 72
    0x7504041500120700d0340740150004e544c5400784421030f82c2e442e8402690407a60000c281020900c0c00390041000900a1650003120f6002d130780da03030055081070128900300403648000c0605402009206000155200404034100ca070100c460702d410410500b0300d46540d10901b401c541640903804007a43c0070480320341160380654028811100003058242e00d00100c9202c81040c0390000d44a6100d2030b007000c0c0f144800552511030f040601130808c1d5a103d4101c111090390030200c0168201180403442442d040c410130b5405aa4152740302e1507074105500080c444d11451841c9a0b01c241c1d02c41b0950140903d8121500190641c0c100000304148c9a46102d00085e1341108403d0040c03042220f40800e55110315507400d9038030080690802048054801c10028282c00302030580007940c0d4a256141e0104100818100926035445a040888600d4550341c24070100e0341000043d540700c04284100c49a000c46040c0d40305800090005c0c00f0740f50500524060700d0b0036030229601d8403001c900820005040d620601c140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 483425881 1250 483424631 483424637
    0x90103120e03030304080901030b01030e010c020c1203160210050c2e060b160203030c073003020d0309030c0f0b01090b030a050c060f0d0212010906090902030c15040308030a0c 77
    0x120564010150f681c0300480c0c0040c0040020700001d08954040e802103091408141004941d01c1002407403242159a45118076005070300a58200c18a400c0030100c0d640804a145c001d5071901300d034a1112450007090207030090107015941c021115a0f072080c03064a244007401d000b540c12040303071002c0203030135808502c450180503039102406135808081e0388500703c00c03078050507941c3d030034116510a202c04e5440d8101059805002c20429280d0003003040c44180060407210015102c81d01452120388104000c800008101402d9000c4034004a5000134207010032050a00d0301060750701e110b20b41143d01c5007000e013008000004940002042256001d00941a00c081310310410031260201d04041d034030415a07001a0541d000b0b40c04841c0c0608103c801045034017090441c0354981070b14141c800e802c980c01042e001e0450103200005104815250003204020248076806001402043d00020385600c3c2c0069041e2181900b4400051003c0d440c600f50f03001075411003207498aa10700341e01042c0180c5840460f41e000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 483427131 1250 483425881 483425897
    0x203090606011202030f15010201060825120503041404020405060a0206040302060a1107021908030f0717070b0f0a0b040e011a090106080f0901021b1c08060d110d0209010312 76
    0x296418904c02e8038442c40c005812040700d80c0f60500e01e00c7c28141c0c0912064110354840e6070201d85094104828511481d410f080c045040f9203101c4408070702403040d0000184001c032810070030040350000003034405070703251a02d0803501c0c4400c101c0060300030f2080364007060700588003140e00d40a041e000b2446a10450181c0c00f0b42e01c640d0f542002400403902940400c401544003417001d20f000d0704020540f840c42c0c02220301c801c0da185854144462450f04100000401d1110000f4208200812041031410010200d40614180555a60784e000c030b206000b4502c410801405001032a03040a41d0400600000040d00402005003c0300225003c1c080000d448982c4a1402c400c00c0700e00d05245035214100d42c01a0f54428403515088145140800c01030480d00c4690b400f03011440c0c0041e01a4484100f44c42444c00421000610718004140004100f07403140901014504000068407099440003110707601003400c2e41209a07080c0059061013171014040e4220f030b18070001104000768000c800491000700d07161812 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 483428381 1250 483427131 483427157
    0x3120f0f0c0314100f1a0c0a080304050d0906140a031b050c01060f06020d050a03141008150c19020a060e06071719091a0408091504030b070503100306020309060601 72
    0x40c80313800621030100300307050a00d001c000048003c445c800024802c0300b519454070304850240303490800000010f46244a001013440304206040142c9107442c80c0b20308104007260b103050405404010788076504403c0510015008c2c0750346201340d00c1030a140716500356151446240c150004d1681e040380e111603103290310b060030208030034520700540f208540050740100125420010b04036640d0b000075032590f083c5a110010b0000903e0b012041a2107051f54000d030b8641c00b4600100e043c07a020310204000d0071241d1101c00c0c4401081c1b1482160015003d4400040d07441c0c001c1101203292518a241c098401031801c000034402d008041005802844181d4460002c6030740022800c0c0f80100940d151449810313200500440d0500344d0300100d400d90300803000014091289245180c0c0e02400301d600f200c4072080085d041d50306150400340b18220a004104c0d2900301402e5949070898010003414200034010088001400700c02d041d05002c0155038007075015916824400c1c41e2940e07800054405a0204449040d400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 483429631 1250 483428381 483428401
    0x240314100f0e061309080f030406022a07150210110901020d02190f022d0114070b010e130218060901050402071a0606090406061e0c03120f0f0c0314 65
    0x1d401843d00802080055082d085007000804030200c1c02c81d440b2a040c0403080b4000b151002441c4180d015200142c0c0e6504248a04011111004441a10003000c04500c03241c0180000d224419903959840000300d1880501d000da01c1c15408d1030110403514103003024503040301d1590012300031000c6d080e02203c41383ca0545100ba42c5910b040d84045101101c040f501402280c1010300c1c145440d40050f107203000c8410f1401002410400c0e9015402000420766800e0010f540c0c48500008006032402c20241441540e603035402e00600180300700320151401e00041074104c900315080424041c0d00901348030715404503140d14107004408071001c4e0310580d184400003c41d403c1c0790003103460180e0300261440e10001110900c0c8104000600200d4000006001125960f2070301e21950b0003502481d121101400e500c1c225150031240d000c03001c18100b106500601000a810000c012482d440411000c240d1010400b41d060040107410401d16805051071503080c1010f815920900d0191131005c0910040d5031158450 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 483430881 1250 483429631 483429659
    0x71209081303140d031b1407060c0e030d14160c081507090501030c050f070f060e0a0b06031203040b0403050c03030a0209131a060906070203030a03060501021006240314100f 76
    0x10b50400c00341c004170220147c4030320601039500305000505418002d00b0b03141c0204886004c0000004a8000e451890035031608100100a400302da180c04011007880c010260814002c16100d8003003808852821401c1000600d42c00780604080c0341295003441d40b83c01c01c000701a10a841d2640072582001d404155540b2a0041d41c51260079030301e855142c29001c4440808641c030100003501c84d250710070042c800182c4207000746807810410310001c213826055401c1c04000322502030b0220344650310100200e401c6090b4801525405504009040c1e620354650505444a20540c3c0d92141e007400000100510300c40380345d01030040312400399500074941c00d4644000c801c4620083d40002d565880000c242d0701c500d8604003c00c45050301070100e604001c81a40400d141d50480120301011944961041c0401d5034104481d060004a501050002c00d15000500ca0f41c02007503000e0202e18000c48407020041c0d4000e401c4444000c8403640b0340d10309854156402031107000d10f4010010800c00700354000508003020404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 483432131 1250 483430881 483430901
    0x70305061914060d0f050903040906050103060e1b04080a030513060f0c060f020d020c0708010b180a0506010512071809150e060d0f0303021c0203071209081303140d03 73
    0x30401810320b80041060301e4028500d40510705454500f07070300518030180503071401380d021034008644940c10000c44400346d4006420882c101850070340304202420314030034002d812400044a0608050010788803c00350322036500040250702c80c3c5020f09041541c0b18008107002c61f143d80a02e0046921488122142c502595483c0c0016030004111804a800365021109004d4401c4006180540c030441101c1079800c00b1100185541000b01d00700329100080c0249141a50300300d805d49880324240741031002c081c4000c3d0404c0450b5a0701c50008032030741d01a00444601880c002e144d240580341100b8000c010713203040152440807003655200002c800b4420302032081d1b4100307481d00120f403040c1000c090664003070005103e141d1280c0d0f41d1100002081c02c1103200c40489002e5039016a5459610000000d085698490050224410820800c00d158441c11a07032140e0003001c40840d006140341481081c3c1c1c00b50f07042491062101c400d0001c104503400d2022040103032080107072400002180400c0d030484402c180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 483433381 1250 483432131 483432149
    0x160209101203110f0708060117060910050901061a190311070b04080d0e03030a0506190303231303060b0f090412050409060b07061b0e060c03120703050619 68
    0x80c0100000e0180c40d0f1428041810310403501c64243c8290403074504030791940b012156800800052203070b000c0701e80140c0e0018032040000d0a03541841801c06684801540115500c960341c0d0000c40d62680c4290440401488600188620380841601031085640000c0d078009030320240507076106580c0e019004002d03621140c2c004071401e0500765201c10078100001002260b44c84400c1250404045840c8a072600d180c0c00c0300d0007182c40386444086002100c00152625110b50355088013040030305100c00c0342205407589071800403e480d200761826030000800d40c0c0c0c000880300d00480e815030244000558082140d01a00081c80f40a00020600041e03040b07550815401200c6400042c02203075425140c14104402890400d00d0a9655544d203000c43d88207400c12306030440f001030046c00303000450042c0c2821400100e62255007030307002c2401400d6030685030680c9028410110f10382440c028140181d4220306000d40304040c8500e00309500500500c01111903038070036a01041c4440c950800030308081c0603206005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 483434631 1250 483433381 483433409
    0x1902010504050607020f1201050103031d090c0a0309050d0e010e1c0311120304050106030309051e040b041d0a0b011d061309020d030c060507020114130c05030316020910 74
    0x41c1800b000c0c0e404413000781c1c1c1009010402c0c480580b2650704682003004a4400000c95504510f03000702608080041104404921000e40b0801d80d1118410f540004851200700e66a008403035007500513141e90b000c042d210740140600f142655401226013649108260390b00032041c84040b00300108507440a41c0420804044244400000c0c041e0640ca4980d810380003ca804a01d16050031081507030080781c003140c65135100d220406c01c050300405c111025003002c0b04e03001c050000000c680c840c01851502d81911881e180c2d0b408213404d486580c4543d00e60207c40400180d075221448007a42c0d521014071013100d40048080000818250710840c000d150b10701d4100b0300307400f030310b40c00f04000c18a0408102c09403c80e0f03503611141c0050355000395071441d291282c0c9951201c202c99003000340c03c60724001d0411055904050300b06020038451071f41950b0241d101041d0260500f454100500e409299401603034040c413002070705454408500c1041000c003842100c0c00c2802d40c0c0d07011340380c400c0c03d4003921850000f00d1101c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 483435881 1250 483434631 483434639
    0xe060a08011e080a060905190f02010e0603090312041509060501051009123804020f040501050a030308100e240604050d080711221803081f12030e031902010504 70
    0x145d0800661b039401881103942020f685039024085407a8004212200e07810a4007240c11540c001c0480c80100724125901415841d05e83d13000d640f01d2258407401c031350000c2c80b140028100582011090f050351b01440d000c10a81e05540340030390045c4020300481e841421241d0750300280d0f601ca4410300040e1550440c41e92547d403807564582080303110420381629901c04004101d0f0000203603502d04d6001c1da80c034000516241c10540140711000603a800620301640c01c1400500c20390300d520000d001141d03071500c1d01c19082e5441c40b0700e24403143c545401040a90350752307206204041c0300c41c050000c0701d0030304608200c4054041004201c0588120310030a178102815039501c41c080b8a14402812400703000d50140e0b258440100009984d4074805c2040c01203071040e05e0014129101c091060414048424402c4044180141c4020b401800018103c0b07101518403600381b0100380d9005404c4006000d800200324990a103440c028102c010120307803003400f0344500c2c505011250b110800c080036598040c0c4900e8641410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 483437131 1250 483435881 483435893
    0x1803080a050307021f1e050903040b070f080409092a17031303121404080a0611160803040308160f051818010801060f140405070e060a08011e080a 64
    0x4003c080d4000d502800c15904000365007281e2080c841340c0c07889400280c0d1822012215403048480b0700e40104940791904110300300f10f0000071581900c00c0525220f494044030318000f4000031a02100902c400300100f00000d45031519005000c09500c221952000ca0310803083d9144024034900840100d01f604640c104030302074203c0f402c407500e030031130300c050b00d00d400382c2101c081e0030105003a4000c403007090614111040d0158032500022215040710300d201d00d00391809036229926520220040d100c0d5548001d4150720f016082d00f100d4442d0900d5002c000c1e05009418000309d2034108890a50204501200080d101c8881c1140b01d05145000d03200c04203690003180701250f0581190300350286100c138000301c04510342d85d2010200384907000007060b5500c80d81040b01c580d0075100c5a5019041c201036501c000d100e05c52402628140030801520009511781e80c1680c1100c064807890316154201d00001100c503522603006080906030781070700950b0442003100044021612000780b18030405030300315400f2480084c0c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 483438381 1250 483437131 483437137
    0x20a03170411030d0e0a05040902011d010c02030d0c020f060c251a07021305130605191112090c03070b0706020f03070f02101109090a060b0f04061803080a05 69
    0x40500c09240c0c4000c240b001181c5080c041080540128a00000c2030406140c0f41c91200003418041d18140300034a100e90020b0041081c01401218405001001e070f200c69100b00c0c03c00f000e5980040440d44400403484001c4c1c00781400c0c2c0c02c264003e4104281d2a8600d0030410f04881461810800601140b19100703580c84000c4000e1601501a10b11003500141c0b203a46071001501e01c05400300f07000c0d0344201910410415020800524000c60b04000402c941607510060704810681c0002d80868035a480506014002e040c07402000400c1e03150028003111290600090040c011000710202c2c456240c00000310b680f0754101004c41c2d8581e2040310240001500c40b0041c1182c6446103030054104504801410000d030822208107002504d40c4a0070005190304000c00441211003480400c149650007024400034460200c0082c02001801e002c41d1148049501c1213006082040f02a5200c0c510781c1032040181c0d0042c85400f000850f6400d800c114881b80707444002c11070383c0c4008401c0c80e00940c900e050f9940c0d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 483439631 1250 483438381 483438383
    0x405040c03061e0c02010b0f191703090411042303060114130516091a030403050901053108010e0d0e0a0e0705070b0708060102070302040b061b0304090c020a031704 72
    0x2041c034200894003d94010f4001c1010b2540003c40c88010820910000d007014643c0e041c4503a03001d8600a82003135030303c04c2c0071040d07403418000010b041010000342d030300e548246000150020725041e001045609131070080c1040c1c545070640004403210920596454032001003003680d060700404010080e17405030043c0748100143c0600b010703d0400b05c41418a04a070400c1304c1000c0041d80030400050040c0d444040103000d0030303c0f03454801d2403012210840c00340c0d020080c00101031041c0001c3c0c19450741c0c01103094840d4201516219482085401c1c0320040c1c42c07030720410036405000501030100754018180140c1064100030f40040c4454400c40400f02c50b00c0041007e0f0b540c0003880008003048032800c07040664407031100b42e01c0d1a07075101854035107001200c4000f88098100035400c0c0510010f80c3e030104101d82200d40480e0f002c91283c02c1e2100147d0329100d0745850401c94500c1b00001d102100d00400540101c0b11020400c000300300300f00105988412607400000c000800c40c01c4065112064540e62903041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 483440881 1250 483439631 483439661
    0xd021c030f0f02040312020f1b01110f070602010b030d14160b07020a0b1303020a0b04031404230a0b0f0d0b090901050f180a080903030f0f04080601050405040c0306 72
    0x110303035500c0c01c0c1140d1906805140a0340c0014051050018807210700190305903500c002e0440d000c0c40d0050640342c080c88140d284080c41104581ca100d43c2c40342c0e048490a4a0350400d903036450010aa0182c0d40d20954807411001d5402c100e590305003460085050400d291042d12801788811484035036a203e80d01c03214001c02c045030340c0c41028022034064940345100d4041c540041081d2001402d203046d1801c0002c1c203081220100d40d01140c0044d81c04170b00d0003e0b140c3d1000e0702c042c1e0f503251460161142c510704400322800c40c0300801d000034402c5100d0208862540c144d5004200c10400311b062040001e4a4021248411400c2100d410700e4a9002c00402030504641000036140615100007884d000f0190f409030360503912082070003407610720070a8a98005103044185081d00307214410540e10347e00b40d190080c0907000007003500500c0c0c2c0c80610456420154002c1016646c00c00c0b81004841c035082030040208030700c500306c000701f5582800d10a65009503080041440028907680c0c0f000043c01c180d80810f0b41b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 483442131 1250 483440881 483440891
    0x6050a0b090714042d030c1d150609240a0908010c021c0309020306070801090e0106260c0904050f070801090213020304030c15050711010911011b080a031a030d021c03 73
    0x5c0d65500c64191000313144201912806546008540e07000c210558a505280c0c403000014000c8412902d01d00c00450350041c1c404949505000c0c00158103181902507540300c0e080d480240d40c4580c10705800a14504034961250140f8a0300d07814020b08840c52854414096800f80c03c4e0940084107114086400c0c00b054a004510401198040b80c00c2503015941007001c10f2030313100184540351044c021a854440b002c402000b0541c504140c246a60244041508500100d4100302c1d60054050000c0550000302401c0c242c01414a4605540d981190742e080c40d529000d005ea01141095043c040c000c44280c0060007103410022160040c4020341c00900100d0601c00c1c461910030010f2000d84035035100c01d0740b6050004144c5802d500c080c1c44811441b10100c0d0a900d0300c899075000442c214014440c0c2c690a2070318a44072000d128000302e00c0550030b400500380c404089030b0808100d925800c0311180d5901003e817050414200310a141d9610355852007180503030040710300d0001c2700401c014010842d0403075142c0419 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 483443381 1250 483442131 483442199
    0x4080d1806112e0b0402070c03111207080606030609061b1309090507030201080703090b040602031005091006020d0c0210230408011b0c0b070507030c06050a0b09071404 74
    0x1c00050f4440b480100320600c83c1018507220340724070450b0342092081d030b4294500356065680d02284001400000d1004003040c01c4c16150f512a601c0d40000101003400f100c8049440b104420b80e11036041315010b10910400d80041e520b401d0105406008041c0c0100e02d0b40b05103c0e03118144502c1d04080d00f1001410a0704800042100702c600400c03510030300607400391441c5400c41c0001804031400601001c04d260500180000041c01d240b40c0951240d0007550068907a110440d0b05004064035602c01948022841d0501c055000c10000840480b441c1c7d0302100d540e41000c0b40e096601d9541280040d50256414130750712081c03400340d04500c0e00e41654400038508038404603d00401604140c101c016161740d61782c2498481c0403c0e40b4400804d9070542081c013641d440c41d035980b20070018000c080f03070b08201011070035004050103103401d01d00007680183c050066150130302404c0024403540f483d10348070300002d002003000030b03000ba01141d40c00b0600b1403182d8078090801e112018aa0030020f9422075441c0071030b02d400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 483444631 1250 483443381 483443413
    0x150b090f040515090307150209062206021207060e150c130801050c0a0f0207051e0102010b0d050601090b060c0a0305040509151804030509030a030504080d180611 71
    0x192003500060a100c40e00d00301800e1580c0340031420405040750100354002d0288250001017a546026408015105500c10a49484010b4022034080030f40014004c590124081a082031403100c0910b07415004075407654445040741e481c40d02071040c800c5043d0410590307012070401d420841c10720100b0300c100c0d038500c200a4842d00c0c9046003140c4035078001801240f00c802e500103040b200340041009030024000350905140a0b00f10344142d07030644080c0551420400704042c0280314a13030040c00002c00c003001061b040c00d00c0780c00c0803c10308807050055190020380086840c0401802241d41c4d0420001e15440c1c7c01e1059280c014245a1281c1c2d501c008188180103942c1d01c100070b0305003024860390720755891324500b80a12050090140202202101d56410b10107651602008039007548002403012003a61103608080c1e8072482161400340d0180145a04a4103043c0c00800400489003211304440720302c1c80701441158007110a203c40c28006065110402c411403240c880814044150410b0711010303800c0300b00007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 483445881 1250 483444631 483444649
    0x108070e0f030607020c1e06160302122b090b1801060e0901020903010e07080a0b07050d142202060906071e11010906141215060d090c050f01050403150b 67
    0x1d00051b40140c0d0701c50000d080c070b094036540ca4000c03000048001406a40007c449000791402c003d01c403e2a1a405010315100f04001e90384c0701490b048407170f62000e444580c2c807030600094410903c940c019510142d02c038422882581555904002c1a040a0b16070545a02c03c6030201e0f00c00150310741d00c0b280007203100c005140c0114042c6000130001a503d00c00c0700c2c207040c02d484030742c07032010941d8001031010443e504003c03400d000b00c55400054200d039980e418005403641d004248800700381d14545480c4410142e03001c40014000c0380c80f50320b181c8800807140e00000303c0791707030f50b0384c00a42221062005400f2400c10308040c090403480f41106011f01204913500c4d140103c0b0110303081d1658400c040300003001d540c1145141c00503098918008100d2003c025944002e4422710034a00309054814000401202038400d0000d112100146000c0c0c0d581200101c02c4040c1c85290015200101c07140c0c00040d8a21f41522911a64001030b190b0724282403664890003003840c07420401e501d041e600e805040caa1a034440b850 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 483447131 1250 483445881 483445891
    0x90c0801021b150108100209030115080d0e04050c07060902040605060c0307061103040b01030f02011709031c090b0106140d09080c0d090f1403010207060f06230108070e0f0306 77
    0xb40400190341811168500504110b04501600c81240140440341c4041610310350b020b08040d015a40c1d180b800301003401410800036940c40d1404440000c20005804102062595280c1d5503080500c4440c3d4100004c49006541442d03071620200113450004482d908541c034002d00041000a40582d2076002c81c0d0f043e4001c008112180e080060400c08201d4030703200d112000d00c4031045a900b10f10b090f603620703803c007401070001a002030310070100c55045a1084007c80c042c85032080014203141003901d2103035640d030003590f030004000e003c03120000029040d610890001c1a0041542031840e4a400d40c1902e407544055006003280800300611070030014240248142c1034494052503a48101c00c03410141031248070512102003288610080151150035806d41050300e1942072519010281a03000034024450104010841410010085400b051031341c4020200e03050b0654900445160b920040c100c66503922811340480d20240124091611600c1c2d10351204602400700307039082cce060b90006890940f0440d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 483448381 1250 483447131 483447157
    0x9030106080d2705041107050d0809010c0e06180a081911090609040308130507030c060f020f0709020711060705010605040f0c0804080c0c0d0b0f160210090c080102 72
    0x1480c0309a5903c03c11101c110100411491240068041140d441c10680c1c800c4600c103540702d1900c1c0d441c135083c5400b101c0742c40354013000f01c91841d00c5445020b404800100c131154070303035483d100c8205105402140d4010b00881c1c003c0c0b0083c038100b8099014450f02a0901005401680d04e41011038020010400640c0c811003925014043e241c8600d400c901c031603d2128828060002d034401d02c07069803141c1c02400d400680c1400c10000c40d9640c25802440b801030010007a00911031000004148070130282c0400642d0800e907950b440b140c804410581c0c1e076610025588540b40d100e4001041041880e070301a00910b4898041c040f4011601000940d203a00445000d8a140e5560f82080029180a116200c81d180701d07580300f403006c5031140b503014040020043c4046c00c0310398000f86002038a41b0601010030b206a00518544080c20326042c1075100d51021610341c82c00c5501da5010500d02c1e600c1a000d507201c800319a00410392030300e02650310005400745100848114441e21000b181c1917800b800a0502560111 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 483449631 1250 483448381 483448393
    0x702011407030b030a121b0c080c04020906070b0702070b0a030f0c0905012709020403080d0b0307030b040f1a01060507020301152d050901120b070f0e04110903010608 73
    0x1485103414200080c10342024146820840150307900c0114600034030350340105003007820054011040d0703806804402100c0710b156207031a4507000c000721122800d0a03a490b001c00c9894041580c41844220702c25483c102d03501c1a4180008030020b440039822a9026000d4416501d94907a24040342c2c010b03070002000309020946803545074040344020f1140c80902ca24918086005034070700800a4840985c800c5244d216184106440c080d450404515400418845a0842d0390381d544c6d01307001616030807032040000c96074106034a82c0d555140000300c1505413500005403500c95100c9690300b110304402103008070b400c1c10b29241e0140c1d0300c9080c03410300c2c1d00818403501d41687d0350841d441050700b11000c006506401d1070f65001c051141e010b4184907040000c03808640c024054028402d42100104103500641d440b1595000200305403200780541d01016106040310070080d241c00d002582c43c504035200040005561410038155441c05400010221a07030115942c603100f4124082400c0d02c06a40240499902071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 483450881 1250 483449631 483449651
    0x109170c1c02120a031e1b0602130b03010f12060f051501300504051c05070b0a0c27030609050c090c03010605040302060d0626010f360b070201 63
    0x1840b03100242c803040c3e41c064420716049503030141c0b68589039100441505620203001c241c45001d1140c80c80101f0078a84000155011464804065070020103a880558400c100003c3d41c403609030203890590351400a42c20b40541000342170064110b000b0400e1710125203400100030303810141d210325401391001c82e5104c4818000000050041030200c00d500311043c100849900074048403080d4001070181224003c5090380300d9050507840c040081050000b802103102c00c9018542e0002d00070305003e4440c128140c0c6964039451281d003141c5000c03000101107840f5064401c01d4444900c4035921501c8031003d079005003500e0341ca40b00d049440b01031088a56034040101c94400d4900000502d81c04540c0da80c0b40c0740b840d8106140205a80a148802401500041150a141001500880041d101c4410304d0301342000f004440008060403007580360603a520305518070340240140d014104131600420340ba5a8940c100300e512001c0782090b0720200e102210300329007943c000340300c05402e107020341025030020540b0295 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 483452131 1250 483450881 483450889
    0x27020d02220f05010e0108061c200108010510020d0f0909061d0a020304031d01121a01090b04080d1206080319030c030c0903140c12010608010506030307020109170c1c02 74
    0x40b40d0825818024014122071040e0383c0000d13401d911000903120801d043c9113581982c81c01d6074000200400700321041c42d1002d06101d03410640c110f411001d1340c503140541d076100c00307000c016050100702d800180c000c510080c003070a02a081980c4448128902500e510b640c3d1407140048a4198006404e40007041010324000b075032810506030070a10244085140d4106554090078400d50100b41c03010046190044211682c0582e41903003242848101c03d11039070808400718011185041c82c8240890480ca00c007284081107002510256001c44008101c070b240004410385400c44256000c800481d118007001c01c3d10301090000c0d181c02030003020350109007201040060b06940f10035088104240ca81000405141c3d0b00904000032a50010b105400da54070304040941044148081143c000550440449516005500c414211501c840003003000e40c503108201901e034400e030030020f4000703540f80c0c2c001c0c0402486001841806074000c012202918510808078500d20003000111081502042d215015420 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 483453237 1106 483452131 483452159
    0x12003030a06031505010b09011d06120f0f040302060606070312050403050c0f060123031507081e0f0c0a0c170304050727020d0222 58
    0x40c0c40c0014001425280c8011104d80d000310f00708a110070003d124190580360144500c501c1d0802d02c90044800c00c845000900c882d1132444a0f481407543d50400600cac0b40400c52664842500d8441490950214010b200c8400e40080302c0400c8002070740030418a60124040700c0c0591641c0103402c048404c182012240314101c0c0c41c00b8140414540c00c64090300850b896102101c0c0128003003440d4680319070003840380ca40043c408041182d641d410603507503d1300210001e401c0f01e030001c001c22000003002c8402e96444001c11400024411215541c5140482c00d070001c010f86a40e604040d44031051418004181e461044004140f00247c43d00c1469000625604100585205800c400714811f00d5030040d00c0031141c070f2003020800221a98030501010004140c2e550007000d08000300e041e0006903006003803011890b5420405044d001d00398024203110307141610705a580d8541402407400e0210 = true := by decide +kernel

theorem cover : BRFrame.Cov 483273381 483453237 := by
  have h0 := BRFrame.cov_init 483273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 483273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 483273381 ≤ n) (h2 : n < 483453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
