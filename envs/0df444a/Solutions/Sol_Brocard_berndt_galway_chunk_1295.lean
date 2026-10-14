-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1295
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:13:38.580618+00:00
-- url     : https://prove2.me/submissions/0b6645b3-8312-4a7b-91a9-34f476b16069

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 232733812 ≤ n < 232913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 232735062 1250 232733812 232733827
    0x4080304031d1503040218061e0d1506050a0803041a031e312d080304060621050a02150408160603060b1204200301050405010f0f0603050c0d050111 65
    0x10f02a5104a030200d004007640d80100c0032180d09414501c1c028900140301110260035210301d07060040e8801000e41d4484002500400894114070038480220b11184011a43c50b0500007403021a54079a440300d000ea42c002c001c10071a00c008440400c070400819816150749446405090001215152040320310020850500c0030454890320a00c507a00300d000d0644200c00060b1007100c03140704595070040e09040b950b114102d6600785240c00525030400351040215101c107603441d0740090350030031142100d142d540d400042c09440084d04a0001c0d5680d94800b02c00f4011917546e80d203031038001d900d40c024002c0d5006100c4904080d070300c00030b45014000d150300310f50302a00e6242003035095078668410000860314260010412100480481d0051000021542c0d6603449a580d0710f40f44010302d40c4803079010900d0090400250741c080c000c80d80aa40100d0020800c1c001d80019041111444105801e10310f140001c10400100c0104000382000c0e01103c00401000c42420300c00e01524420340a01e4104100080c4d02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 232736312 1250 232735062 232735099
    0x6030b060a0c03301509060605030610090807080703150603020f0904020a05041103011703041a0307090b0a03020c0706230702060921060c04060806040209040b0604060e04110304080304031d 83
    0x4d102007000c24140c2442a178880011b01128850f01604001540800c001222030811140200b0682c8151400c2c0401a960789a260304001254014404c0f035040000308000340000360000c01219414100d040003440c1c5968002411020105207840c001c03951500000c2c15960341681d14401000003030420300003014400d9440c46145d0007401307400c40040c0402c9060800c810000306036001e035014403842480516018850140c550401040380d0100184040f0105900803000701070098800d06031030243e2580582c1d03e003a8104003090b0850010002840d1514404141400e000c0c03072000442200d0b107503074003807a0010030b010b8402c020301c031600844110501d20f2102e07a252030030380d0025094803e840c40341e2528842c00e0b100e8812441070100003440c1901080440c80c00d41e00402c01c151008000041c0760b000382000c81c2c1300e500140e000d800411351220f1022003a04081c000c0c1e0541d10786a5a5142c83c5150a030764168240c0400303480502004065010144885503030440380510b0f41c2d0050020105d0000c01c80312 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 232737562 1250 232736312 232736321
    0x10c020405190509012331030206060102010507021e03072310090c090b01120614120703080a0311040f0803040317030f0f130b0a050106030b060a0c0330 67
    0x390106030f01c0d107000542c011406100ba15882500071030b000f40e0600d840d4401c9100c1d410081c001580036603107014410780150302c040d200c0700b400b1140048002c0d07103030b200d0401a0400400910300303419079050100304506240e01150b80c6100c2000c003200346020b1003048041c146540240c072030060030154860f81c10048007180a40300e042080000c0221041011250140b038281c034060000144000216001400f080c0c01507003064010756011724000032564003494503103040e2000b681c003103624188004902402c81c1881030040030120103180042c8041843c594500402d80702d4442602c1c10503585100e055170603003800080354014040348003140d1910381c89410580d12603020340300c2280c5a02e01c42400360100c0d0755440650344210100104d080c030a646800c0301e111003c070010061180b00c0740051412000488610301c5900031400c80d10006055818201c01508a0350710610030b51103850244070b5a081c1d00e0344050500b16541d803619080400b098503540c040325801c2c03445074244500000c01d03910036904dc520fa00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 232738812 1250 232737562 232737601
    0x7030c0911070317181009110307030807060c03060317190c08030a0504060213140306010902030c0a0c0206091201090312050705092808070303080708060904020f010c020405 76
    0xc20000650004401c1e2490700c201035009002c070f00c100b00050000a01c0004080d84440c0030300e5299a17400480300c1c45070034982d08031000d5101568484c40c3d082403280d40da808507038500c801c0d40144006403c41d16004210b001d0004010407807a02e50009038400d5200f504150020766102400d030265a9800352095855000106240040d5400740e00707a071000ba110749010088030350414005851601c070156281c01405004005a4a0b6902045a40d03603809121100310002c00c80784c1c9e1000d80600825040500380345041e403000d40843d0040c41400180440384045502909290400d40e41c44200d900c00f082c014001d00850035440810b403d001c0c07280030010b420420310603200303a50f50b0409600309042041150003d0b2240000036005000d8895103043c8891a64911000480c142410300c0e00e0601c3c0001600c040e4000900c03c0e084417500b0800c15030442070003908425541400d0801d450002c0100380311000c0140080c1c462059420404c2070b90f4020225421296000380060243d840d1008210000703c200c0704 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 232740062 1250 232738812 232738829
    0x70302060f090105070509040b0a051201020909090109031e090e07030204090507020f0706031107080f07050610050904030f03140708090c030c090a050c040e360c060a050c07030c 78
    0xd0b0030050184207840c82040551034081c02c0125010502000344030740400150065228240481d181c0d42d050305801c103402d458000541d4465902052100500c3c2c007405101050781001100c400003a04010b40c000180f408113420036483c00545c8003141d9034110380d0b00c86a407944c0a8000d00c04010b40c150000c0054402400c03080c0140d0710782c404100d81e9000d40540d841400e400413403040c4026442034001c04094603054080c46c1c101a0360341c8548009512075042c0516154002440034201b00040c031100f540302c1070b1203410140152900020803100fa134011300081c20070002651040d41d04d80640d00100e51003020b001070540e1460001c001078208071081d00c2d450325504c5007001c80315240c500011400d07030039880a00800300b66110021003034050f020243c1890100380d0144808039580c1007035081c051044020401c1c40070b0f8120349010a8528114520300f07540e01d08d40c0c05210303403040a00003c04c0380d007000c0300b542c405941d6110200103c0d114020502e2000702405054000400e00c14011400030550755003c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 232741312 1250 232740062 232740091
    0x2a0e0702010228090e060604031712010623030a020c010504060605010e03030406050d0b03010905060406090620070b0405031e0301051e0307031506150302070c0b091e0301090807030206 81
    0x43d486040b041124070500000941d03828014040304651100c0e103508928040c001c45c1c101500c07691181e0085c80d94028011640e0f00124049581d40560284030b4014521030808a481c0003011401000c0c103141d03111543c110880020114500b554503504481d03540c2c2080000b0031603400c043c501100505407500c142c600050001d29100074501c0c021044a003114065241d19103418005141500a800340307031401ca505568031040100425070034044203204a12541001079080602d00c1c109045617140c1c4000707028035001d0720400398030b029100210f03035007140c122441d500b46c2e135150b140691540c0b08071844c005191008042500e40602d84101450595808945911800c1e6055440341c0b8044a0001c04540c5640b29410820206000880c8a0354002150720302203100c580301c41d410101d80c1c2c104d4000c1400650300140c40c4080c800c090320014050035018840600c0e28003040009049c01700c541204003111004091011556682540700c044040d91000100d0b89585190a0207900d03041c00f180d1880248158 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 232742562 1250 232741312 232741357
    0xa0b03060601030b01090504110408030a0801080d02070e01030219090c0c0b060d020d0b13121e0e0a05130605031e060702150a0c020309040614010306050d2a0e07020102 74
    0x1307001d841458201a900d02241c0c07450241040007402802d0049100100c0030440400d04141c01d00040c05401c81c0d40d107852002d545494000d6140070481554803007107421107102071040c1010924050704403601100c0b14500551600011044460160700403034500d0315001220b0301e450740003829100f0709402241c107a00030b07076100820b109030040310844c02544524040d102400160b140114a42c015074400c402d20b07004903840d9142034482c00348500c2c10b0b01096074802e55a5200850300102261052030b41b40c00307480700c45442c02042e2680c2a038040c1500c42c404003030003020420050340c440402030030002c04449291007001c0f000030442c112002040540d00858002072a51400000c400500da400760a26880c0343d0380c1e0422810081c20010301b10030450104003c0099655070354010480a0820300b0980d400000d0084005000c076002070340018000e4014803459000310b40a510524840354402040c4042103000404d00443c203102500710840e80d004c41c005104d42242e0550113000380e06081c0d000312404009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 232743812 1250 232742562 232742567
    0x2010b10030f0c05070c03021c06060609180c0807080702031e13080a0b0105040903120e07080105070e06040306020f210a11040806061318050604050c1504090506180a0b03060601 78
    0x501d885c00382c80c005c0740000800c010300b0030540610034880e00c40c40d020300026140e9641800d0f540b0590005000070601030051001c400c03400400c00c540b01c01d490f0b01700105c005044000e462060014021014404510f000070307041c85c0203000700c2d540c624036100c40059201c880a074400032070f0040105000d0b4180d40c0c070b034042a08080041d09003001900042d0b1381d00142e20700740800028141d085000c60410255058201c1d4100c014040c4407002c0000d500a0b110307050401b403140e400c5603c003c001800300114410030340b00b641c454004480903280c1240c805030780c481084211940385d01c10101c401401c085541c18162107040e0503002d150140c21100414050120020702c1c1c00e09a00070750242c464640c0041000c42c00a150a800c506005a40002f02003030f0404c0803944081c41e8604800c044e1950341120302040300700301c010f010b1034601c0c030000c03913204120840201240c202d6005500500030460b41e60804a1a9641c0d842d102c0a07450110482200591426001990103045140302d0a806803181e00045480c660 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 232745062 1250 232743812 232743817
    0xd060f05150708090a0302060c0609010f0204060e012f0607090b03010b0a030902030a050304090b01030f110307080a1b030603050d1409100c17090108070503190c02010b10030f0c05 79
    0x242040e108600b45016525407549070342c0410300781544103010342d9001006032201d0340078000000400303019020f2841c009220500f9220501a441e404610400c428029180c0141c1c00c801902d6003881c0040d01901d0116484a1000728654412903000c1d0703807111441341c21000201248524816070324400102d80e1250000c8580c042805121003424003032021419051081e03020380c407807a00090441340f400180e510348505503806904513524594542c15aa202541c260190310141801c0d00010800b003030044040d21341600010307002c0820450f0020101c0d2640031160000101078000c001c28038a1030804041c00340c018059480100c5150003210800fa01003402414240940800d5110780351070300c4007110811000061281805051124051405c0301241441c00250191003001d460030b40e56a07904000074151010040192003003200800411120844d0346128030700c036180c034440c04528802a140140c1c09040110103040d005208100c04810707650b4183c00102ca14440d00b542004000b110080494451 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 232746312 1250 232745062 232745089
    0xf0c0b04230601030b0c0c01021903200309030a030e0f0615090a151e0e0103080d05060d0f0803180d0903030f0c03170403091a04090f0903080601180b0d060f05 70
    0x208000103001b502122004108154400d00010b1134014284880040c6a40007800480000d0703030307003d01d144407101c290240d101d40c10511404900354508801115600e10480454000b0191604480c3d0012071007008000154400743c01170342c4651506800c40c50848060f16442c40c031032005100800c4544c0c0c00c070311944209882c6030301c501c1990360030216884405800d04400080001000740001280a03515a0f500e020b1403260400c00c3c0d50343d094400c00c0b403e4900140c00c052203040013840001c00110250440504a0b0b40019010b880b540c40e944c61001c20042031107140c0342c1e40102c000512407242c1c07003003c1c90290303403194551048040409104036103103007401000a02065291007502500340603030710b8455000b4841d14007903100f00e0f00e03104804e0024106004001d50503c001c502030108920310300411988100c1400104a2480123445c001d04101c0050500c505124680707108000a00d81d21403a071300600441003002d40d48414030124403000308007501c541040c0c204c0d20710011419281240510b0079a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 232747562 1250 232746312 232746323
    0x10903050d0f090b121008060105011209170403030507140105070c02040f0e1204060908030a0c06090f140a050c03072718060b090a15060f0c0b0423060103 68
    0x70480d1031002d481c00c140282000702400049000020804d203032500034204580d40c100740300d4050411419400701201d840d0044c1e502600150018861a40d03c0601d0f003800081801c00420305655606280c2e01c1407283d8005203820711130014020081c10340090050651a214505074004540e40c800c41500700c503001e0300c1500018024900300d4000d440c0541100b1b40c0b001d43c5e840001a80c11a0b084083e28080b100720b18440440c00202c0c0c200421a08084d0800c003c00c40340d80036503e031450013803008001c55000c84000301681c2d031710030b90001406400214155840d60100104a07204180d40c20241e80d00300d8490115880d102d0300c100702c5028100800c0a078100d400e440c20080c07010b03580040303001d628282010f100c503c56a81d0800c940002c1e07508a0300340d900e14000e290000c0d05c2c10040042c0140742200034500c00344903080041c1d201444804100040460306a840e01141000842c04101e0302c01e010800050b000d078840c00c2c28007082c00808010480750880200301c08540041d60440c203922080c091101808 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 232748812 1250 232747562 232747573
    0x40b01141f030902010e04051e1503100c020f0607050d060f0b2d0d090b0708090c0906031204170606031f1d0f0f100b0a03021e0d0f020f01090305 64
    0x7042070007a0440c03102c20340305050081c0d9821452000c602210000c40703030b800002144c004414010300f0a20b40c03035600b000c100b0440e6031428035200040b9a4034403920202840340d9030b8500503412058803d20100000395203120549601d424080320050079900440c0304051610325110300010380300b002840030341c01c449000000750308007206500c0400356140b05a068240102126401d02040c0d01b03103800800403854200300000d011040e90400d000300b81c20082100050044010034449404400100b000003200129005501652520042410302c404190207981c03840001c5008101e12468072208130f106200b000c200c1d6000c0c0d8521040560301c64541496842280700c100c500f01c107400340c980041c100701100c10507a50103011150403c0e0719000070424075000d940c2105045540c0c01c0414051014284060b5a040c08203a00e14000280d17018140d01c0b00070301c6006624450179500c590001e03501d40da0103000300409040307003035420400440c030707104041240b0030034640b50f08048940c0034051840a807900b0400804 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 232750062 1250 232748812 232748869
    0xa0f0c020705040b01030e151b0705010507090609051c0302030405030703150c1407060b06091005120f060114160602041502071d15010c060612020f030105090c0907090806040b0114 79
    0x20004880581850b48000039080380d502544101c9c0c004007480c52149000081624003248014584405034020070100164a24200a5a65544801503c43e003552010140c0d49107103203001da1441c1724a6202c0758150144002c0007007405000355000038466418001404000072070304d4125404498107071540001c200034400c6401007686a07001007006100580b0462400b50002d00048003442002c00403030024a0008600c0d007221802459641c000241c03d26400c1641010340003c1c101030444540801e140f140866580101c00d00c51001600035500301200715511038039903100b02c6200000755021070151107801c8001400c20401429500650a001101d8506484070a00c0d1840c141c00511002d04119114801c1d1003c10f45130700c12200200707032401e0400840c1603e44140b03d035014072400c00c50b2082e4584800c0003516000811080c5c86104103ca28440543d06c0d11420398035008150003114984c03040c1020401000700303000025050340c1c502210b1010001640c020003060030f103142911817641502c0441003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 232751312 1250 232750062 232750093
    0x11120306030d1d090f090d0305070e010c2402031608010f06031a1206011a0f030609040c0807090f11070f02060f0d0906060e0c0a02060105090a0f0c020705040b01030e 73
    0xda0341e04450000315000c0803207280004030311039030503105c005614024009005841c642085902c1044866007030a01c03c1d0300d0480000782c4a140034218003410301600b86034540400041424248003080e12008159090100c070300711030003d40045071355511141407160001c0c003840c01110010304a468401f101d501250901d20103d0290000149595a00c0c0d0b42c88002c5070386544560790129440f00b1500200b40c4c40d132410745c100c160800e240b499000b07502810000000c8940d150401c0b01d0340300c4404c3e00c0340e0180d40c652f807610044a514076848540f09002d00c2501041c20380240d0051295030b01111018400d0541d98860740d056172140102c01090444840303103030401810040d014108541c03030400d005040c0b1062049000a03100283c80440e81559100c000f401520150391704942c20400c0201000c0c00c1110141e0040d40c1c5102c1130150320700c41c0114a00040080071140c0143c086030558000500c4400f01c00c940c0a9510201d6001d502d200703900305825032600d94031034410722086040c2800248052503904008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 232752562 1250 232751312 232751327
    0x9010e012a0507110603040f02130612230f010204030b060604050303030a0c09080f03070501050c03040203030315040f1a030f010213050d1403040303090905060f060414010c021011120306030d 84
    0x49405a01600c00500d071696201702540c07142e030081007601c1c0000d00a104000440903607031503094800e4a00b000901c202000d000300c24050381e500201c040c509045002890314483e0300b00c0300d10f02d020321820118185090044d00604100d03803050f42004075a0703e0342c8040003201d005502407030303070554000d000142c1c0d0f40c4c80c6034004080768185030810341441034407601c01c14100480442121000d0b80f00191400400609108940d804106407200a095080a50019407207210182290002e8030121707414000036a075030b600c48075030ac121301c0c002000300401030304101074035000f1803a03058403d00030030144800468040c000c64058101412055484500340b400304000b007200b03031034142c5403296000c400b10480300b42000208040c42c042d807a650085440c29039803405840d4010503c9004921750b1365031101507180e88064606070380e0208401c102803003c940040b6180c0035003200c041d610011200031802c0c1242c00c09100c845030a06a403d0b51054030718a98025541d110940d61550198814441409400c1c4034044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 232753812 1250 232752562 232752577
    0x20105070f030f060b0c010e0714100503090723090a0c0e010c030203130b03010513140c030402040e01090b1816030201050903070e070206162619020309010e012a05 72
    0x8005001a00d91200e1841a00200c480c00c1903072390751361141408800c04204900003085400034040d1954082c0001c0341043c41c030288a24144030003c004030380c1411040c403446014103004004124034107049011020360f00e034103880ca01d005641d00c50100c0c0c1009614010050100095154145810820001156000c003c03510a400b140028880340c404066201d038680014490070514903100d50601040100d40030940301034000f80c0703241488031401c54800040082d80101c4401c00d142d1280d6031400032401400e6030964040319075181c485a0400c02001d00c54850003568404510034101c81c0310601c4556500c07074414070441c00e44100004000541c031507030050400900141c00d0301c401c1966607040e40380c82442075031982c004d0303000304081002a200c1c5801034210602a40f03003881090b08240500701d440b0318181701880b4243d020300d000400d68000404440c00340c0c80408021503032882c01016880c001c0242d40c0c00740d040303942000307032034442a00b0710b00308089101d405900d000f0315481c110710265090b5001c5907 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 232755062 1250 232753812 232753841
    0xc12092103130516030302190308040b06010c02041d0c0a0b0d0e0c030f0109050d1e0c05030f07110a0b120f061c0302030714070b0706110d151401020105070f03 70
    0x9070002c000036820f01c00340d0303a2408000c00000d101c03400d40c50b001c0d080500c90300c10b07201e11409280381000800d9002403070942158000c00d0700d5000d171702c404004a486071642403010b9041810a050b00326800200038a0b413070380481c8502501d00c404890783c1000310f482c0341d40c813070301c45425014465501301b6000c5612054000100c00c0480d4400d680a201103824251010700b840d403076942d00d0002c070b414858240a001402c403032a2424044d41040c1750324450300c02e454807a00d542042007c40180e010404200304a9000048041c50a5120100351410720101c0780303c5800c4c3c9000d440d04260005a0b407845a0964509030403d41070b40160b5594001140e207a1040102050391044080d028002001c10307960303040d101240a5406595500c400c5e08000303410100c050410946075200c0d04003041900f5142041c0ca030040c2c0d0041c0081181c4d40703403480400050052140c006845450014098034917071140b118141112064560700b900000c90033b00590032120700f181c6c0100855003207610a0540b031312130382c000c181903055a03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 232756312 1250 232755062 232755091
    0xf0304051c1a0910050c040e04051e28020906130b0a09061403150c070317010b07120807020601060c0f0605161107030c0b0703170c12092103 62
    0x19102c5000452001500c1605110220280a90300d07005201311050513809000501a6080c008201c8425200301d100300d14038911100d01080c1001002c0c40002502580c811a641044444803030160700d070121300c5040d1070384442640d51a52031041d000c40da80740d0580c008204072800c2d0f42d2003040c0482c01000c40041841d40755205900c0381e090380d507444028090411500d00003090360034000405410b00082210314070076445104c3c0100c00610018029a101c1c50306000d04d41c440c60940341c1510220030510310002d012200100104101c0c208201500c0c0540c065018000207400464040c1c80b81c1e802940c4180040c3c205a0050200038041d001031880103215116440c00c132002911002c0031a80c080d01c00e03029070b40d2034100010300950300c07401c4c2007003090350000684465440e50391407030244d81040c0706510f54441c01144503802d040c0140700c61003100d0113005200c01e0b0f03464841c3c402f2403140d1000e040c0e580810400404603480c004001a114404000d200b01e04000c580d00c000500c8090f0401065002d000040c27 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 232757562 1250 232756312 232756369
    0x621080a02033703050402090406020913020304060b011803050c060306060403080d1e060b1b010b1801230d0201030902120703060516021203240604150201060501020f030405 76
    0x1064181c8099062804140300c40143c141100d000c0c042c0040c090303040608003c140f00260b0b13100c6220a42180e480381c001a518040d10700400c4d00300c9001d6640d050018400b00411003800305c1904582d0281c0c20076030b60114009103c079585a101003045c080a490b640c0700707044140017810b221008540041005040d1030405036030707564602450340039080c262080c644800c00800a6025201685003000900d103041c09683c2c20305a400c80540103018510060307034040d4880f209180f901790b00c07010b40300c00302900341042d0071a00421201100428451903400d2500742c91f0404c00b103e206c0545520000b070040c11075030036034125001100074008075002640d12a522443e14010841d081040500441c0f2408002c10301d072810320080208000307800c0e902015074000024a080c0d410360700045070ba000140b40701843c03020296000003500080700546143c0c0049001501150b0905082c0e520014501140d00a0042c1d07034856004a07103130040796240d190716500c2400103001903d02400381f01940d00d5056000c101c078202 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 232758812 1250 232757562 232757587
    0xc1c051c020c1201020901030506040c1d061605150f041208091006140319020f24070f060515012c0301020a05092b060e0a170301090621080a0203 64
    0x7003c401544240e50004c4c0f680c0031540c050140a40c8400f084400701f0804540c05c3e0094801032201023200c1440c01101c5d003041d0255640700c20b41b042c3c5000b84881071000c40c2e403407a10702d90715103407121520f141007041d0000448a603200c0d01c03042c1c411030740084040001010312105513581c2303101510032452805050420b45030b4600304d200d420010510030499a440c64025401e140c104400c81d4010040700031000c1c083c501503103642942410690080c1d038903441040039224130b11100300c0c5a000350450705400140c1401800055092490050b0254004122503181c2e200000780c540c98a60005020450210030740144401d80b603407111040f0168905050b180e0003090010382242e100e180d00310042503000c51b0452441c00c1c40b0801c5c0c650021035003e5101c039132001c01441d80c045088a003000302110b442c0c3c818007010850034010103808552010010b583d01510111000a9030024000d9107091403800340c0018461700c0d1180a440642001000341c0601c080301d4603152203d900442129081d8030003044408403600 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 232760062 1250 232758812 232758829
    0x70201140411180108120307091a090f0f0a090e07030203070b0c0d02031606020f0c030d0b04150b070f030311030a020a02060106030c1b1e050c1c051c020c 68
    0x601c6000218505102c00040103c010411252500424040401403110220001d1582450748099600c1d64690b6503041088801c003a1540220051071003984c101c500030725504002d004824812a00351903601001418003030344400a02030240d110420706400c00101c1c289034400741c6554000810380d980b2640300d4005c41d181203c0c5a0141641440024100520500503c103842c143e10712480075502d41003084940c000d5580380c1c0d81300584a9030340026151018011070046600c0e00c458001540d8680f4441b2811b04000e09284a08600031400c150a035003907a540b48504000f0744090f682c80900341661600d4008052207040b40c12401d040d078501c520a071046081e805144a5011000056070322100b0b00d400034180101a440310302814203007100c0780b090b140c0008005a9208410301a0981da428a0074410310589148012110300a203000000091000102e11800349030000d0b40d9203010702d07203400303070032080701091803009449504020303660900a22010002c03107600360075104840800381190b00148084 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 232761312 1250 232760062 232760071
    0xe2508071e05090906010503010e010308210f0a0f020405010c03030f14190b010f1202031905070f0e0d0305030606030709030b0f09011b020607051c0c020706021b06040e07020114 78
    0x2e5000c500c5660528000e83c41541c000000c0c6401c0c0d003903501d800c1c18800c2c17224040c0030061440c0404030711a6100002d09a0100101f40100c03a0b0b0205d6080642041c202c045041d41da040744107041c055500400c035542e0080310101c0b10181d403540602041a02c04070b009007503603603401a50700d46071030036007483c64089483e01d8043d941a00310252890b01401c0180111541c08640c14117000040062040140c0c215a1184041308880d41c0560f0300e603180240705003a0307a030103a00e941c0894601414000c0031503000390780511b03141c910b486090f0142c4d060340400201d0900540020000b0304100700107203003824150051a003085079410030850064481d52040081d0108894641e40c5e00a018100310001109005d8040e205c10707410b1850f601c03210340f0400252207000007400d030801d10030006481d95500c1c201c01c4840d020110804e5080205c840e52140003034441030584203000c010701c100d00450041c682000f1007007008000080c25240360603d8070301d90107401c01d0000c040d80b0940d540e139652060590409051544507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 232762562 1250 232761312 232761317
    0x606081b0111011506050703030902030a03050423151e040303031a0108070806010e030a170403060b030303090a020103050406060b0d0507020d260402120d02070e2508071e 75
    0x89488031030004090024410003110707180e050410403414090518800c100b03440b05460141c3c2c5d034801d582801e40103001c074490000d4041c403540741e400c403d15a0040190090b01d440c04206000e842c004c0c60200b040000f0581c6c0c1a61105c4000c4c001c202100d07045004000341800b11504903103007003c5440e01e14054100c1da0040d40440e40b01c50351b1405000543d00c3c903c041240900300f075500e5042c02d940c010162040200031605025107928400d010f96000c021b20242682d00c00b00799024191581811440c1c0c3c4c02c2480708451480c10b188403a8014038011081e2441104540000c000442c03807600110302404002d8029a8003e6403a18040b40c3c0d0320041d00180500c1c4480740010906040408009182600c00c1400804000d06003010350480014218404d084c02d41e61b840748203440d1035078000111000641c0702145e541b0b200c1c0d0904003d07090b4011071290201c80044503511115070702d400d8020313824141d0102c2003040c8010340f51030000d240e0283e10707590340045540c03800c4250f589098090404050f9641980000f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 232763812 1250 232762562 232762603
    0x91503090c08030c01290f041e09060c090806040b07092610050106210605040e150f040213050a09021512010b040b0405010c080c010510150306080c010c060608 70
    0x10249030074000d00100226088071900c550300c0200c4044010060443c489200b40c546920720a0b15544681104403030740e82c1480d032403101409d1102c60500030840e01c10221395490404912843d070601594000342241d17242d5000d01141da84950b5000b001d52001041c10080c0a01c404000c21a044400c5000002480761124144a404004d5407145420001c1507101074860a1100500070603602a4040d00200b40503203070624000022407010015020b03640089800030318001000c81889000103082a940030030070140d46064440030150a4601c0c82158080d401c4030a003945100010260707406103a0041e230004d4001744800c0240c1c0010300300201011150180140424208009048548460f0041c510086004d142c64585414010390b030103140324003414041000b00140034803103a0011100d4620028000300600c0c40c0500c1c880b00c200505014800240f4003220b04014410b00078426103041da11414001c1039400410401180d1110f00b8007012a002901c0300000281d4820800c601104809040c81086 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 232765062 1250 232763812 232763827
    0xc060905040e0607050f09040605060a09170706020a02060a0c0506010620190303150b070b04060b030312010e090f030f0405100f0504050d0f1b05090a0c091503090c0803 74
    0x42680c020400a40c515080882130068140e00b040c1182c20500c41d50707516a0311120380200203002809a40d1140ba04240d00003142e15119a005914005803544041180d010031a02c40d07110f540c9680b240a03943c050b80c4140208409483c00390094a14101d8038581942c0c000c14035070f1803509041c070a0340320381d001c1075032134400407000c409060365540d0386040400102128110308c00316000c0200741701c03406005d1540d80c2030503808050703017018901d000e4510402d140b40c0d00c1600b454401e010600c03c03542651410700d0300c03991140740d1a001c0100c40703032400303c00301030b203860f90806500800c020760143c0081403d102d030410302542c413030061014003820850007030f5680d200d602c4d100c140100c03070352022a801c003040391074545903280707a411006803020391342c3c251000a80d0110307520381850b03070b00c10550b0301038540900d00382c0078180102c401403200260340c019514101c198440071a260165070b07001ba031850100c2c1040405008a844012040318051903501d40829640c06075110030702d4402940e040741c01e41d0303000001d015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 232766312 1250 232765062 232765069
    0x3190f020a0309050f0a050304030b10240306060314060f01031b031406030d020a03032d0c12020c0a06020304110a0e010e010509011a0304170f04050114032208070c060905 75
    0x3a29618215009810600b000d035030b4184e22031245000c0240802032f201c0c04580e542ca80d8400360b1000d0710702403000c520314480442d2514a4101420780747e174002801c000b0003040c0d4511034000c100c5517024a410741c007050b031940c03010000300400410603d4100b66441004800c5c11600f041a506c051019840000e0b0340d825001210320303071100041c4600d019510022502048590000d24045807039014540040c0110710906400c100e40d0090311584000b0302044035494000c0361541c030200900c60303292101011b45400c00440400c0e8000c0300014034083e00008040380c082000c580055038003a120f18250406400d0a40010700304c89040d8200602400c0341d180188810b01c41c03120301c00e0140c0b40403680c400466150002c0043c01e45a0140c103450b00c5036010003c10f0400060307050381010341540400e1207031500904101c0704440e82103846005d0004940c000281540c85401c0b0489001d1001c142c0c1011815a84052942120400801c00c0311003440810154000c98424220303038000d840e0f140c0d20071100a00c1c24042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 232767562 1250 232766312 232766323
    0x130509060a030506040f0f050703080d15240909090f0201020f0f061303110d030b0a09060503030a0302071502030f1b090306150d21030e030f03190f020a030905 70
    0x10701a07111080c1c107102050700061225486039100080703d14034011440d208074503008040340244a407203626000310804c5540000340c10200c1c41700c2c004004010b400710003240054020300c01c00e142049100d40c0d0002c9140c03514064140c114040c10092074141d51003000720111005d20005540719212340880c1011580d05200c45040c80007000018040340c1c0400140d2030f180e044c040d0044a50204110080c410107026040403007000e0340c0b41041c0e4102501090b0040d010f0b00310102c03031a2090b5030b016808100c07601d032489004240d035070282c010b60030140846000d4009600440c429103885280c00c05c650380038007250004600c40c0e001004491001c2c1400064400b4140111680780c00b208001c1c0103114094030009143c640c403d0f804280c501101042401056180804100c041c010b0300840114401c6100750010207075217840c00d80c3c2d04115030210312680300c1d2240039030610070045400400c04030b44410004c4420038405d8070203030000140f5166003295074040340c1c8003011050220303840781c0344081405001e001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 232768812 1250 232767562 232767571
    0x8070905072c120a0506071e080a050c04050a2702180d0201111504020f06040f0611011b08100503030c1e0703050f0616020c0a0510020a08130509 64
    0x40c02c00080746040c441c00300201e510300035001c0c612001e002640855441c10300342c00c2140c1c5800296a401030282c209151103281c00c4424001044100500005604640341030550004072981c4104183e12152211400342c4000341c4240b00000c4c003072001240c80c0e660900d5032401403c5044845040e025100d0840010508a1850404040c410301002e042c95008849081011208954510760004c0610050b03581d560702980781c10240c400c00e111500390500041da401c0c0114003c0b80c007181c120f2075520401c2203e20540c040d5680d07400b0385c490200440c070300070700340f118040104e07500210b101e00d69103d02c5124031491041480008000304240000e1200380030341354016080680c083c6203021901100c81d47e1743c8100ca5892211080038685001c039030780c01032180001455114065500d02044080324654501040e10720342603131144404118481c5000069000414101401c0740200b0ba1502c1d08203c007159000361102d0960280181301c00c0001c015000403e00303d9001c02c10031141a04040600c070711b01c40c1c001c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 232770062 1250 232768812 232768817
    0x90602030301050d0201110a0602040f14040510031e02130606030c030e030322080406030623010c080a211e02071109060d1e0218040210140f040807090507 68
    0x80140440d07103404504118551702800c0c00882240f10b02107081c40c00ca412903014285620101d800700750321400e0a0218101d5414508000361200c4100400c0304440d41510b00b0210300240d20402c00029900b2034200c410481c1820740343d60182129008200d0b106481480c18884998412040c411260503104451b1000f62916003040141c0500e0b803216600d11000d0705001c880642c0c085500003521121462180346580984150788a41c1e9030301c07025019229070700a050201420041405108007910138500c080d044c140c0d030780c92049540b40c8841e00694054210701c0c0c03c00c4905561591032031002a814541b1031540e12001401b4071130102c040c800b80b5130961000d248180104444008a030b0214028051020121b40088454803404002080c0030450307940140002e035203642d4007080e80c0d000d40954408a0095842c1c0300682c2000d102d215103020308590003980b101611503081940783c0304440e1094610a810f2040386440504200d82e030442e0032a03031000c1110b038402c050a00042406000d403940000709030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 232771312 1250 232770062 232770067
    0xa08160302091e1902042102040506190501050a031803020d231801020c12031201090b0102100b04020c01060b070c060201020a05030a020c010b04060b0304051b01020a081608031609060203 82
    0x481000365181020300014140f041204007008105055412100142044547d1032502a52405c0c00c103001100c020040c1d1207546000005400da092041c81158602c00b02c5100d03009003030400d40152415007050244908265595450380d80b212149120010303050700075001801169910744000b041e04a042000c0c081d0030040080b01601e4010140580300e034141d8410f8203502c01e030b0303200004034603041c0b41c58070303c607440380340d141d00300e1840040030004002c409202c03192520b59a0720b80c0450b205507620014050f0060340286801da010b00c8003540034802101c0d004101521f0003584c148100e00756450350300007000380d5a0000d80c2c03404012841040710000c00c4680000c0d814400705480c05005400001c008491403500007070f205000600a62100080303803001001008004d4440e4240b03421900110780071205803284020070040300c0c8481041000300d0005034001d00c600725207661502c8d01504010b1451400c48141c01d035880019818002851068084014018200101d40002001c01003030340d2000c000d54004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 232772562 1250 232771312 232771351
    0x150e10020705070302060301030f140f0d0e03030f0a0807030c1d041e020f0405191508040f0c0e07030b0a140609030a050d1115040302060a0e150c0a121e05060a0816030209 75
    0x1103034041102816003030501c0354201cec01d0007281c254170907441c40d05500396001440b1122580c002c001c42c0c0c080c20059400b049044c01091050b56502441c070030070606100300305100d129614143d0020612400000c0c0480010006d10a1460613078000c0d41079008071680c042024001814040c0c0001034600c1a200c81c041d850785800c2e60346d00c1060100c0140760400203140001002e1100070307509c0c3d00c0020f5020030305103035451351402130511248040d210500000c1c240b0b1502d020314500000d01c8002c0d541c10b41c264038065225807040109680c0710340440c0750107018401184011540500850f100399400b0b440b4403130807208040e030490500321604101c1003030340744a00a00000c603500164042c1c1c4180300c580b0025404040e904507c0c0b4003075200020090b02030641c010040c0b0321001c60003602e5100c0b015203d45080710591040321056800c00103103c20356600300351211004c80500d4010790b4205001410341c07807180352190030130740c1450345c264400350003500c9a40040085080100189900c2144513913080b070b00030b00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 232773812 1250 232772562 232772593
    0x140610090b090907020f070f060e01030e07180b041401030606120803060904060207060e07050909030c0a0f02010504080607030b0f060a1d0102010605120a150e10020705070302060301030f14 83
    0xb01c02055003c0c10700140010700e014002c2103020000382c0364104a80e030030ba43d84c8030450b010307060034080d6000180410101d140f50b9400790040c2c15000244002a2141a04200e0700a1030021000c1003060781680710302c1881055180e611540d04514040390700246550b045090500c140d17821030b841447d2100d502ca29800c041019001030f6030f0411b204440013a101d489905105010303025131000585058580b0204010010000030050100c0708240c4201401d6540d4404070341d22802504132100c010b4101c95000c100080b03c40a40b084018030504140f030611380c440f10f06925205086900b400400d0b9150001d84180ca003a07001c0001c5240111500c07803030410030200080c82a040801012440c8180c42c40040c096070007900218090007018040c0202d4806941c0b0083e550b5100180c1030b02c2e241e002085141c3c00021600552115507090402024129492581100254440c2c01c054078140109000171006070b443d000194001d5001c2e070a407020704030b450708095034500a259200b0410350b00c0441c05030602003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 232775062 1250 232773812 232773817
    0x1312020a060302030a062103020f010501080a0305030417040e0a060506040303141b0d050901080906061c0516060e01020d020a110f06091201021b0d080a0c020102070204140610090b 79
    0x41c1e40e80b40140e12030f2182c21500d0042d1191303800509032105560ba01c010342d42c002c00700046055000781e0803190310001c44441142211000e009195a5401098120004c6809100215007040c41107014001500c24020340c809130381c00c190031454101e000300d810311135400300c5801614003802c811075640e0b04d0103207180e4018140c041c5444024002c50000700320652100b0150b2601000908410203845c20044c89800c001d00f2030b0300029045000c41c2c8644003040c3d01944c005901c6200761000b4180892400504890941ea500c80a10856091044a41c180c10b1003003699000c81c000c0c1116202ca041002c0c01c04000783c14003141055200c11036002c3c0703c40f00c000c2061202d51840000b4261100c540148818021880610035202103681003001c07034018480c0d089056000709040c050254a007004001160303055a1100f0f0035505003000079000703001045060308035071301c050841ca041d40001890940a03902090a0b0b07280901c500704003107004003c004040c2410110301c07d81b445036103455125182080e21444890 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 232776312 1250 232775062 232775069
    0x302030d1106240409030906120504050a020d02060408151e07080a0c0509150d060f15030b3606030d020a06050601091e0315140711030906040b1312020a 67
    0x6100c8800c0d41c03000b40b24000d888041640c3c050828040384400e81009491028107102d000e000404c1003003410a040268881c107802194003102070301040401360204803940f40080002d0740d002208000010b8a5003003003000000100b000c004880042c60086287d0703900c091b0a01d180b1410003180c1b010001240d85c00b440722a8031004404000820003030300340003113032070740101100b02d0341042407600c10b11034280c0d0302e90282c8121000001c00740070903501e9a007480202041d0307105141c01524840d038400c0119019401c101c5450380041c02d4122888114044420101548031520001d50070399407030f03003540d81800b502c1c19500580503002010000d900900c001d5446422a401801007503030383e03010a005a00c1461040024198001007007451507405c2c50b010402000d49c030007202c1e0440c00820746001d215950003084140e11407002134040d150707210401603480d81a4107959203180c4c04200f0080c1401e17561180940301500c8410780c030a07110229034524544a0006411505151030040c0407640160b941c0840c103020b5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 232777562 1250 232776312 232776331
    0xd02030c0918070605040f0504060803030f06060706050103060c080f0108030403080f0c0303010b18030d0909150305190b0f040506011701020f04231504060c050a0506010306060302030d1106 83
    0xd942d03408403020b0b410380d2911110346040c0500d107000603480d548040584255100c0b402d941000f5075598080100701d5009109034812a04140f002892051180000316070010340604454501112643e4440894000360811103c3d2981c0f01d0035548000e03400747c991030b481821040603c1c1a541400d441e65941e000300e00c40100107480c0014030000d111003020a8172401c000460403203444c3e507150b80e400c5003640c2020007012582c604500028100e4980003e002c1c00041e400c0d220103400509000001000d09104000814403000b41d400002c0020010809032418243c1504103410f007021903c0c0260250758050946000400300c3d40c20310001c50b00201710a0f0460309002d50f180480218180d601d4003a000380c0d11040c0c4c00510108002a000d030010b2001c0448500d104150050101008108240e400f42d69142c3c40c0105414001400454040c0c903001d0103040c0640308441803d8050f40e0307064500740090f0012180310391158001c0003141010010075580383c0e41030a144004800880b079295680b030380106801c62 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 232778812 1250 232777562 232777579
    0x110a18050f0d08090904052b080c0f120c0c101a090711060405010501030b0601030903091e0e010b0901020f030a021b01120203091b0a050a0e07050408060103030305010302040b0d02030c 81
    0x80095800072156003004c00f826464151500d400e00a4075850b28191000340c0418036030011480300b00c00c0d41d81a880d0016a101e80f071494607990342c24a029001000441c1040c0e80c104031a440180040714403500c03c2c41d100c41d855585c0c5003034110240c00c0c504118004000c03541040c403215550610320b40421040da8040d24450960f64a1000c1201c3d11400350b509025039002d0001844184401900300780c1c1a2401801602c43d031752204e5004404951100c040680001c031050018054034050500050b00113060010011407035071603036019101c0a07002c0e4400c103569000010541d080d5601400f0286886124601660801c040128069100c0f0800030001c20a80c3c008440302c2c5886c1c1c058483e10341e410140b20021501c038038000c58001d544249005540000c503038207840002584c501011620251040035095010452800c000d0f581c40c20800b406950500c181480046100e036003c1000e140203501a1b5000b0510703516500500c802c407030402c0c01207400360300210060805a18005803d945850068403802c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 232780062 1250 232778812 232778839
    0x112110d0b180106091e23011707050108040305030a09050c04020f120105030706090b0c071517090d020d03050613090b0f010b0403022d04061706010902030403090501140d110a18050f 80
    0x7c250000072a1880f6030280c0c0d20004291040d2055107a0741012010040305c40e40d42c0c40c0e20040d208641b0440c3c0082c0019410400034180b2840d541040426902c984221444502410002406c0c1d81000911031a01e40d030100702401c00b055000c10813801044290054450340c1d0500e03c006280c00780c140102c1100600000e0302040f201c80402c0300000800600c1c0449002c03140c40754000781588044250b09d1090814900403504144002c0741c031100d030f061144c00403c20890305400640103020b0042001d0391100342c001c8000d82c89400c40c015245203503c0b801041c285490252816604294180c200350720661042c40203200503190f540100403e14440315075403444a001005a52a9455075031100790400c0c1003c10016905040e07680045482c0c5407642501d94170fa0320780410318103d020864015001807011002004654003401ca00307030710100ba410b4158941031500448034251107004600655a0303600242039066245e1100f154640d071040c1028500c40c59241100064135091a502041c0c415406c43c1c801c1d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 232781312 1250 232780062 232780091
    0x10e13030903060c05191716020a0b010e010e09070803070605060f04060e07140c1908040f060512092a010306090509010204030311060112110d0b180106091e 69
    0x120095a202c0d0090114188414008009406c20481440b41910201c56208500d01640340b150b454461051401d020759100000c1c04105a0381007900b00560082a41d000081824100b0b19406040e4107a062540395142c021220400d603070080101000d50450707030050007010000b000310b403401c0e604400c02095944450b03000902108901060541c003915000300003c495240c03000003480751156889299100400b206241035912800c104102d007034004290306010304102c0308403030b00c09034000d0029600301030302e072905919000d9240c0c001d41c01152011404045043e142041d040d03000b0231800c05010303d69429031134120304444501d0000305400c500222090715034481d5009a005000c0d614051201c0e0908111143c001c1d84540000d60010706c8a52019400003c00644581280c000000810300c0080c2078458028800641c1070703003680000082c0ba02000320b105c3d950703224060f2507000751032841090003864103421502c0a40c82000110305140c0c071100100b80c881302030075400194000200e0f402c0c0035098070707 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 232782562 1250 232781312 232781327
    0x803250b0f10050d051c021f02070c0308030406050609070906020a06110f0a050702190503060a05061906170109060f051509030706051c1103070e01030603021f021005010e1303 77
    0x10f0381080000c1358030414004009408512880c101148001640000504a071521144139090145039500301030f5514114055000340981c0d4002e94003240380d01d4596441c010381e5031050383c00f503a003a03480340107000b40c9141085200b900304520303003800c02590742390040280d210300f0690320240030f05685190ba04440c514007c00c07240f0800c0c82c41481541c0d8292888040e10039003081034242c0c040d01c10400c0154100039640382c0e03c0240e8600500500b19a902c600c825005044014695a000458240c00a0050395882101c1003d002241c9038414a1101400300c1030028405a100b20440d9041082c108017840c03022000d01c080c2d070301c00d441038020746c500c0c40030f00c0c0c65920030b4600e4150076114022000034480d5014015101022040d07980e0680280c0da215400107641d1014903074481704100700045007441d40101d6484408100605000c1445503494001400b10061401e20007840c00c107025500c203102d5070511448405a0241c101004254100300810401340001403010b1035010340368a485081c103004420 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 232783812 1250 232782562 232782569
    0x9030c02130204080105010e06011704080f0403060c170c0a110a0807230708030d2304031e020a050a02062b090c12020f0103020d09050102040803250b0f10 68
    0x46441010054070100340254414810544030b5480c0a0012451102080c203203809494142d41702400300d59400125030b04607401401c120307800081007242c0142c6580b1040540025401513600207408809404054405641c10310740740c0c1c7c488200340c1040700c098280c1d01034840c1c0d07041b9850301030342c10b040e440c5101e45403220f80c02c4041c02524022030054200680103191004c030359040040301e400d280a1029580c2e440c01c007030048000942041c44805088005948403885410240312807e001041581200e4020203064805030005051101618060281c2d242e0f100700ca928a4401006074451036268103844491683c0b00074858200001e08a010a4031300e5116080300e854800c60440301c20001c08120002c044140c4111142c00700c44500103421840d140c0c920440680142c014210002c810004400a5002c5210b110140e9034400082001c20401d00c00b03080a42900401143c0d80c0c20b000045210325840d84010481e940380b111000b0000407643c0d0302d15a04104801200502501c4600718145038807044e41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 232785062 1250 232783812 232783819
    0xb04081804020c010e0c0109030503071212020a0306091805030f1812070e070c08031303030e0307060605040b0f060d020a0c1406160302090a140409050118050705040513020409030c02 80
    0x94188070507201035202c81d5822034045e048602c2d0408003070064410071103501c4080c0203070300180200c030301140300307244e50407208081490f01a8100342d004002408030b8202c3c0c911440020ba8482c820f100b524294462082851860121080d03000042d9562558a2040d104904172064000c5610100e01c00e10000940c460280105040c49440042d0203250b5942803921503648501d070180003240400c0d004110030300038950400015803455030707204178840f5a00450740c0b0490405d6900c0001001000050002c2c1c1401c620580d008143c140c6044100000c2d40d403a808850320031602550048000c0d51508225a2616510310026031511200c103401d6070f0545110101a1075501401c130310707107080d5002080a07442210b039031411413104484804120124002c4030b103101d4100b000c0b440705106407107610520340e011800041c00860605010380c7e550f400e65206003030583c00d00781c81d030b080c0ea03003040018045203001c0c02060b241004036181c800d03801d42020f00d500c07001038007455275022044c0031f05205061b6265241c0c0c024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 232786312 1250 232785062 232785067
    0x303070c030b1501030c0c020415090632011b08070c0306060e1302010807111e030901090e060901121401050708060406091407031e090303060501110a0b0408180402 72
    0x3400d207640c06070b02c12680300da103509406081c09001c3d800380c414520109070598402d80c0e420329507800d12004141d981481d0308000c509602c0054544141e0060070054203451076041641b0b043d07415045400e0425510000241400300b0340d440061f68010301c0001300429501082d807003801319003400d0b4060300c80e145025004a840240100030300220341c0101f41110321074218000aa076a402416843c0d0030415030080c001503100c00070a200a1049000c0d0030500701080c203680c20382c1800c03100c4c8800c0c03140d0034001c0e10444e040443c2d060103943c1c205600400034440c0140c441860310340500001e10042c0c0500a00c1a601c50090245062140b00c601c074100780ca42120080203241089400904810811105903200b04e05008010456099034024280001451840e03001d082e1200001500034000251564100009100601044117114094000100d0081c4c40004400703041000041068160303191141165000c541c001000034480d00745a030b401a00600030780e8a031596072029080d0034440300141070b84103002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 232787562 1250 232786312 232786319
    0x6092811040e0705031003110f03030c0109023d211d010c09030f0303021e1c02030705090d031101022106030c0102100209240d150b090f0303070c 64
    0xc0d1001001550b20902c1c1540559960040403a640e100c00c5407480704814004008200081031807007040c08120004022030884007a510110785503402c105101400703a9140d407140b1040d401e10f080c544403c00306581d00c100142c0c00d0000c14031800111401415800030007144003400051081d03240ca20145c0c032078035400501c1034032504550060050034544c002061b14049100745403840501c02e451030400742d5295085103901e1901e490043e2805600c05806041c0c080183c1300c0303100c02c190400d00c80140706503016a01c405001030341003018280c41d5410310286204000780101d1603080f1094400e0b180c0215807952258445142c211544210850320030023543c004101c109c03502c0818000b40002180102004145644041c20142d07140030420b1014056001200e181080803c06c1c0c0040203070b840007400c0c000a0300d003104141350b101c040c1c640f250881f03004080364a070340020b014000c5d644c0019503400c0c0012501d082c070003052018860342441502c01d140288100d44241c4040c015a64095084800c003e02d00b81c1c2c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 232788812 1250 232787562 232787591
    0x20a0305010c140a0e010e040b03030307050304140d0c15060b03011712090a05090a06080615031009030f0f090803030c190206040b010504020a021015060f0503060928 73
    0xc41800403e40201c0d591614030303920015540300c4001c07580e030b0148441d01c00f001035a42600c0303000d103150002d0310380c4400806070702c0800040d030148005a45095413480d003410880c20303550b11000580305030b4000c60100c0002c1d6910040100c02c29410618100214a24101c0070004050a41c0100c000c00c0340840000703100e8081c903c0c070740400301c40344055071356800040c8070243c9148101c008070381d4000010001841300c3c0c11700034940c903400140d081001814985034001c20380740200c00c0721400742040100b4189501400d05000f00c14200415034024000b0756410344e80501140741d00c0c0581010011004801c0080350701c50030f050350040600350192680c0c0c0c00c01004801459202c0010220070501001d07491000d40d10010b40544500c0d08066140803903400c00d0308000203035000034403001c1140300c1d0b180a0b142ca03401c58410841514034903445c252401d440c059000e043c482d0590a2041031040034410410b07252120302d8001d61100c0b494900500c20102da5083e5203000e4810100440228644000c0e0200b500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 232790062 1250 232788812 232788821
    0x10207020a0807050f18070f02030f0d02031b120408032703072f0411070b07090302040506040e0a020402093015010b09010f0905120c1e0102150c07020a030501 70
    0x81054818140c9007030085c0a02c40f1301d00b00102c9141e01414101c0004c0c461600c44d0f6208400d42d241c902c1540c3c64a0304100e2041c10307a170400c8031140ca4031135002041c0130340700d00c0022000840031000b0781014105130450f44100c01c1450008e0002d01100d0380040060815410322032441240000110200300d02d00b485c0060658a40205504a40014001440f100c0d00d410410041a6002950b4083c032031012201c001d010182034110103601d0080c209110060016081440440c030850301907607441100c038a0f500401082e00c00207424240514a41098850101008120000000d070103450240e80ea2070500f0102e06201c820100501d6920b0344650b03042101000c00035448081c9410300212001d00768010140c1414010038841d100381c105080040a0055005020009070508581091140306545e040441c01d21111420304006607005007981950031324180d03030340e02c02813012520010583c000301c1c40040d644034201c4c8a00e5440f20360800020b8102e448072030803039000f6540540201c15a41e47c0b840c155007c1e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 232791312 1250 232790062 232790069
    0xf2609060a09020306011202011709010b0103061707030303020304080409021606050a0b0907121103010909021c110603040606050d030e03060f07050a120e0304030302030a0f09051005030603010207020a0807 90
    0x5024110100341c1040d0203020344440190002d000e8811070b441c018024140001c0c0307143c1203043c041c3d0441c85907481449585201d02c240100c00000c143c03618190001000c44103560018515444000e01d0542840c400150741000c0d00d5060030b0040c1e41c0e44940c100544540500d0384100301076400003640550074070310385d4031905c6602c1c8550b40c2400f05444101100c1c1c06c0d240f503141665000007001c000640310501c5110300901d0300300001400600162040c800703204960003600907a100036111b0041004500b400c101c2c0d080212445842401c2100250b81c40100514000304018032a032004030200b010301800364443c2e4005c0400030311008041c280351030301a0481102812051290080c44002014041d100b02d00d00c0c401c040590300d1030b191801c001001d45958641c02e00c01090382c0e0703a902080b00640d00810040000d140aa001140c84504010008040c0b24904c1529010000e15050802c41f640303075030005142021050602c6504d90b960800404e0090090340c101950100301080d0024415501094000c286c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 232792562 1250 232791312 232791331
    0x1080312011d0c030604020d0e0c0a081c0c03020f030a08040209070e01021c0c05030f1801090b092b1101020606030f19020a05031501140a03030f0f26 66
    0x340e80d032100140c10b4014070404404201018100254103d03500070019a40807800800c01030074805a96090002c446200d1521a01a80250305822032460200100402811244004e200f01c1e40c030f00c1d410001c07a0804041d08002d0107420302036002011f0092050021803842e01d411242c85284442c0020030206003034800f640145d094801040080f8440d804400f5542c0040e0010008090583c4004004250020107a8104030324869040e00080d001c0c0000c04143c024006a0b589030310301e290101070410640e4103100e040c071180280801c040a9200142d4429100c115003207030b042482e0b840b42e0b2902d001541c0381500c00c80c8000002c202040201c03410300c80c2200d000e034201c0325283e5411091541d5060320b200d40c0344159006da00e100c17407050300000074031540c02d10140400818564500120f454070345200349911b801c2c41200f0040c03121f500e60010300c05882204440f00092240385031000340c69103d10003000c1c000c209540740c1e2940c2d414052a03061000c074148061040c65807400c540c00340c8021034140d450307210 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 232793812 1250 232792562 232792597
    0x51b0c010e0d020904020915030d050d05010504050103120c0c18140603190602030613051006171b03060a15050408103b070609080f0f100c02070b03010803 68
    0x160790070108401121298060650358803170b1200c1e020403081c41001000c420703101080540c01c0c0c5841c0c50520502c00c800a00da01c0300e5480300340701c1c07900405072070b0141c01c41402245400300410100c2c0b8050309412482e4030078100600709000508154008010076041881d5000305035081252082c10360b03010300310b2804c25001d0b80d401c0f81c40b040c0c10162503642540f01700c01d84134641d0441d1004101a07074000c1d900700d88010560211645d041600b0130903103004441541d400b2040c00e10400407103422501c1408a0080c02c8610744071482e21003d50034aa200f4058545130803140840024950303207950381c1c0140500b03d5084580c8103101c0c01c6d42c00522a0303120f0301910705c0c2c07402403100107030403801680911910074a220301a8803501080f144130890075600a00d00d0020050560400b6099210512034031025001030340c0c40082c4c5034204610a481c20b0818980f610440d400701e004115600008100310203000c50a00000c640b00d561244101d2410520741c105540d1a00c0000001400f54400402013042c10340440400c40e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 232795062 1250 232793812 232793837
    0x50a0e040b090d02071e030204060b0712050708120411090a020d060801022a07030605040812010b03061e0109030515160f080c0304150c030f0509010e1c051b0c01 71
    0x40d1150f22002d515805680301c00001d000c1e030180fa00000c40980c40c42c0b004404c3d015601e40010b400e0711802d50245c2c0310a0400100b10080c0801c0031810751105146040c400d1601c12660303611b00507031027103007494507605803d80003040400203c80129151400010007010300d034186841d003040254003038940c001c0313028688140020300b050103000340c90400e2200c0e000442ea0300b40ea11901d0015805001c000c042134081d6950110001c0d105200d01c074040c5000b43d0030146c071107050485001ca0803e060300700303946507203003030042042c141c0d103030385d5525a6003e80100c0c54001014000042c1d88010458100600301e0199014102c05400c3d0542e42c0c030f1282809504d045a210b00000040e078121a0050b5800d00240c0aa000514510710980c01150403038452000c0085098030038812504880741031142500198444040844036841405030b55000050311000304021084d41030321540d188030fa10190940c0311031070344078100968020b509403040740f4440740341d080341800ba03030f0300941c0c03248022580103010030504201c08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 232796312 1250 232795062 232795081
    0xd020d020a0615080a1505070503010308091912030e09010f060207030b0601020a0609030201050f0703021c050c070204050f011a07120c0f020303160201080906091213050a0e040b 78
    0x14124006660041c01d103a1040781c407030744041c00c3d00e55802c1e100080c01450000d0400360030890080164060107a950180c089582c104c1c1c281c0b50090262010084240b0051011403005001c40d880180115885180c0403005030340c41c421003860340d02103610703908004422014140c00002d03062401c641180c42c0f003682da0701c4541c0900070003414042c4500581c00319000f400041c0354281195000001401100d0b44c0301c65540d185003e030390b04404100c0c010307510b84c42444401c03502c100c07516030058011b080c00e5043c8a81c1401107114030140d2524800b000780c070b543c0400d5403940c425048500c103d40190080c0520701d8a401c14001801e402e100d101c40c800081790304609066403460583c0d01250340a5100a404d02c03851004403400d801e60728060b00c408810348480801070340c08000030a41c00d10b07441e007210040c41d40341c000540040d800502ea80c8154100f00104005600c0200fa00d12034010a503a145c3d464605c0c4008800140340d03e03420581e04a81016070104115a8520450b84114424034121120303503a8036440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 232797562 1250 232796312 232796323
    0x1206060c030a050a03060506040f08060f070e04020a03201c0507090509061903030908010b0102121225020606040c020c0a0509090a0c0b1902070303120209041d0f0d02 73
    0x18855074000b40a004000b5204a0003006814a9441d02059203500c610004000d6485076100c01140851a001040740034018400e0340e80c02030034201c2007011031602c2c01001d00b14041c6001d0640c45030343e0000c0c096000030b01a0b0f210000d0800d00019040c094101c1c4c1d2401102640903041224039044550308820504645002d44c5d881500207a807030007079252030031007848603070080680070b2036001c940e0398400800651b1100101000714025a40c0409240c60200764a08444954600604641191611075004803140c01214124598041c466515640d214002d02d04000e2480041d1020500302445c0c004661f800210300d4065402118100015020340000780da0b500390141c0c031540c102003801810001071811400442c0d010607008281ea5145030250303545008801c1c00e420840080c080403e22445201e00c0e0403901d94804440d000401d01d40c3e00b103840c01b43c129001c06507a00300194000231a18a01d8403240c00c109400c2003c045400340e080390000c00c0546598070701d03107107041c0c40c80782e15290811180300060 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 232798812 1250 232797562 232797577
    0x1b0304031a01030809040f0f020304050105040b060d02011e0302070203120c070605071e1103030c16080f0628110915190806060c0604030801060801090236060d02120606 74
    0x1307498030300008007040c44041c1c01034004c1210429035403d030080a00038907000a40c4540d2040c40009a41c1c42c20345403400d230920020b0010360090101c1441600140d030000c40d68041c210b01140d4121082003500c00c2140a0301c0b500d8402509030107894040c00c4603003415005862501841000d8070785640e01c0c3d0004132021b0141350406810b1104103100c031510803102c9000c2c0308003103000b00114050b1120f40400700c1c0c40c540c40103005000b0340e800716a4500b600e0107820030400282107208054088901c500c1c00743c55640f0f1010700200c5ca01d4105032920401c15a11f1441c0c4861481c181c54144209440791011200d960070000800c0c2c055081100400103400720b800444200900c041c03036088000aa12004403070b0030900805a9420a10810200c2d040d00710410000c0d214074801c0d610b8495640c14588014420003040c1c0c42028a9030051045c444014400032000404101c141241800e04000302c01c50f152580d00b40c218150041e40024818108841c590024180313541d8910288070350340c5402c000d120700c0b44030346003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 232800062 1250 232798812 232798823
    0xf0a0305071b0b0901060e0907030519020d021c0204060308030603011a010f0c080d1401180501262407090f080606040b06040801020c010507120b0a18021b0304031a0103 74
    0x400c542c0000c0d400901081c0c00610038030001401c036850380f1118644100554000c541c0380c0c82810200100030040000c0800041540c0b0503d00d01c0d0065404140841c5114100a03c00da442c46001c00c01114079083c0402e0894004009102180c0c0d2401d00301340c0703a07200342c0b00a070082d42001042c0b00b001c1c2c481c1030132142c0400182d503603255400070140700f00c40d0809400d07070444100100b0042001101c486004200c413681080e099070300703036524000c0e4040038003c6400030103c03810300b410010804040b0001ca00300c07040a58019501e070b0b408408403000c4c20f0010450502d0101038108800d00f90183d0108140c1c2e1141d0030030f0312403400580c3c441c0c0110040107407603c141d195940c420000150141003e402c50014200040c224604058403800c5080c2039810910703110078641e46d40c8041005a5612020400a520b4a00000c0140010b4540451140c8180d4002c10443d029000c14048500000368101c40200c050410521407000c00c4d20011510381c1e2140c4410f03140d0446203800d64070036681c1200500e0403039a000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 232801312 1250 232800062 232800107
    0x20a02010210181709040605120727050f01030c0803130b16080301060c02040b090609070f0203040f060c050f060f070c03052a100c140702030a02060f0a030507 70
    0x1d04184020381119080d4101642c03443c000d00f40040e107107001c01d0015403c84000580c40b01c68502c18002210703000e5100034440c980c3d01304031940071480460100181d0b00740080d100b03100c0ca1120b800040420f00754000100b404e140c0010842c40c681501c1100b4140d0b44100d0f0080309203039850504a54900844828003d03490030303000200403407031a0b800102640c070b400c2c080e20f200b40c0400780c0310510076400982c44440803070182d00307581c1d0031031801d84506540320310216005c1d8220f00388000440c407421002441d030390030700544c010012061070081043d03a00910303001c44e42400880e00c03580001e1001d00c0705113007140d480c810320851240d10381000c03801c6817280740c820304034480c60b95607240100d40d071104044064040c44003c2009241100e110030303504c0c01c00002803451000303403d0040c031502d190070b50f0b00d881d409000f031415402c4404141e1114001c40411003007a141030300d80c003603800041d0405901000017980014005444c0f902c0284100240503012043d4804120763b950b0784400356105041c8408000111290 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 232802562 1250 232801312 232801333
    0x6100501020d1b05070305010c08100b04030b070c060b031207031706030606061308010c030c110d1b08250b01080106140103050702011e020409240905060d1209060e01020a020102 78
    0x25054005101c0313006801703d4072050f6a17603c41c0b40c01c541e0110030210004000104000c518880041e00c2c000600d2980401c1e03180c2465502ca084d90801d0140c0b4080420400d000e4090a10005402c03005103110002d0a03500901c494004045450748542400c4000c25030240c540e00f8440018801d4070322608018000d0925641c0d000c04110b13443d806021070f0752551880a201184c54582480395010003503071038800103901030b0151000780900c000d40a0441450b400000494082640103242403e401e51045c40300700024007a140011290040700210041e800350040015107178861100180b6055000700401031060341c07200452402d0b94013501544041c803042c00c02d40c003802c0d44603501103036010645100028040d4040c0c0017031001c268411040300d1105801050511001d50315204d90800038003409003000d4004400b01c42c103650700007148107008003950b403840001c1c025203540c460090f908c0c3d0700c086603075240c68001002a1480b83c0074002ca01c00500300e04500f896a500000306810600d80580081094048 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 232803812 1250 232802562 232802597
    0xd020d0819051315050f0901090314030c0705030f040e010e070206040314070506090709060906050f0f011403100e0c0306181f1205161206050a09080c06100501020d 72
    0x1809496021040c83c1510f0300740101e200d80c0f01c0c0004c0c40b0010f81c030111341c605021141c04c034811000751401c61103925050090000030f4101c05c503032403252003250007180c607680d600910b0301850040a9020b0040e00000030980480c2007080d00130815125464600007481e42c039900710b030038020401c58803240580e010328042000300b4042c0d50300003030300d0b501000e0f014079261b0f07565115070610b00f00740d818520691040a00b849500c045024070f00c042d241c103013410072070b55250a000415003403194021034064040b90b03444200d107034410702e04508100c1c3ca99415035643c0c2000d10450340c1841c1c1310311620344651204ca0100c3d03178048403602181e001d010300070400b04240e14460b401031540704001e0020304000311011200d00d001c860640c2e44200a1284042041304d46d8000c2c10514180241c5103040d01c8070400304581070001000ca082000a001e802100000b41c40d070b5104d08160040940c41c4002d04094004964111070300c00016200b1722a4401140c42080706580c1c100590755229100180300101d4000b040b003200f000d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 232805062 1250 232803812 232803821
    0x60b041a07060216030806030c01030b030c01180803031003031103031603051e0a24030c030314090303030112020f151c0b13090210050c030414060712020d020d0819 72
    0xa0042c24018581040c3d12081c0c941d42c00c441d001100842c0c2e0341700070040701e442e00348001c4104074000c2c01c040c001030a0708070000c1d80f2001400846414005401352282e00c041100109002415509088981c2c03810201c800c2e0b40000103034070007140080e00386c55a0b003030024000300c103683c0101c0c407500e4200c00f081e000903c19009400010840c20b50010007015610701000340307406543c0200700b6002c00080700c4540800d14402c0d20290000307085a02070b40d07501000040c0a0070208000c80340c05240516107181144a40502481080308560b4103203c044000318400d50b140c42a03424140c401c4441190780c0d615002440304803116051020944002804101c940c0100c1c40400b040d190520000050790303200300400a0704101c034000ca074800269590310403000f14102451410550041170806034107003260040000e0340c1c1d220f40d00600607110842800c0c804c0d40d8550000350f40c0d0b8560b104041604c148501e00e40299116109100c036401840b4842c01210b40c540502c02e014041c3c16840d04060301030b03507100c0140000d40f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 232806312 1250 232805062 232805077
    0x6092402130504021605010f020a0e030f0601050114120709090e01140610020f03120105090601020318010c0c1d0702160b04030b060102070302060c010b0306250c02011202070c09060b041a 82
    0x5050340380007000086d40a01c107141d414010101c005880e0708880700300500c6011001241c0d8041e60001100c0308074000000380584c11900240380c031001051214006410901560100741c501c1c072641c409200d42e294010358800140e840da180e0411407403411109540c242c2c0d04281c00c09910442410100f401c5051181e0341000c111b003140129212a071031600400c1c9198004500c146003442840b00502151034510083c503000b440034402582080b00000190800c0c041000c011410b00c15041c4151007084203030303071440c0010102542412094103d40f00029200e07801207901e50014020302c80483e1800300350560050540f00840b042c40c1c1400e096660700c09150401801031419880350a078008016a1140c0042402a03881000415010201c40500d0300c3d103200034207803100300054412281000c2ca5084242909104030f840d201030140c1e110b00044e600e0222090001f1503a80c0005480c800340a03448802504031010300104204150b9100500c0e82140614020400b104aa1022510590800c9405820380 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 232807562 1250 232806312 232806337
    0x30c080c30070f06030207060e0a0506010e0402030705060706020a08010503070f050103020d060f080d0206090a02090a0c12111216090b0a051c050603160e1603090609240213050402 79
    0xc2c10f0b200c2c034220641d0343c1580d21440c0000e800007038060030002135000300101401c000700245503605066660356103490050103503a40c1204a800003400f9541c007080420001e240107031840703554030b0fa2400c2c810043d41c0003001300b601143c0e4910002410f403c000403048101d030b0001008541d61420400110701a42c0110b8200c0300b003d4540e180441c850030320096841c003c1000d00028030030400c61100290401100901a0b0115000f101a00c0003503194075140c80d07804601d007480080c0c0c20115403000e40d600010204580c00640c580b4000d005404000002407034540407041418a155803034100003400c84c190b10107440006041481c0401164040b103001d000c40c101142012418203014825501c40340e0750b140f4000505a40303a2050214038101440b60140d1036000201613800603040800d200182c0c1e90151018220f10b007200484482c051082d80a0b104541e0301010511110605040101d51000c1046982511810f85090016080e0407403003220840d40302514507001003880c0500b00301c0250420000b0110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 232808812 1250 232807562 232807573
    0xe01060807060f0809010b09010b0a02032a0c22091a0a1a01020d0e090714031008060f090705040507300b0402040506030c0306010513030c080c30 64
    0x140c00c0010301100001d0000c0e55520b0141a0302c0300d000410159000d088803c80f41d1500c110301e4003546500415906503103428482036903501005400324a90302c20762850b140307421660046d25075408401d0315084a0103602a003140c64400840080005450b0804022208209295120b1140c4a0580c20200c484e5006522140c01401e418600100841086031180841c55403280140c0c0d000c103074040e18610f41d0200784010303c001d500303846003c0c01500c0c8941300184510904000202c0f101d128558001c0303046081d4464a459007081080b41135598014041c40500d40203450006000114044841c4d100340b0740139000b01820380c80d14007400014103003c1c1070034003004620303408001c44880000341c0454841c0d00c4103072280c01001c1c41c0035000880d02441100c0e403150307004100c20815641ca40307041e40d13008032103003016590307945444006a49034810741c58400300002c0e040ea40041806010381d14102110300700001d4a00d030040c01020000c2e00c0e100740c03c0c1e042d4405010007c00c083d04400452441400018004840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 232810062 1250 232808812 232808819
    0x60509040b181f060f03051f1d030912030703120903020a02090903090307050901050612060307080f031c060509130302013e040308040e0c25061404150e0106 69
    0x9050029803d01400012a158a4200092118412280104000b2a207050010305581d17849440b03032801c8042100100c0206520308103000c0e6a03014040c0310417030070756481c0d0122040e980c1c2034981e0401040300344a0086a001942c03a00130200488441560594403600c0c00ca040094201c003c0c02d6840c1c0c16000c600c0f50340c2c00310006803a500c0100c0e002d03000a0000310f4076100070400b01072030b10b81d50790070550207041c0c01f40041001c1d0711990203603414405550504142c0359146400701e0310f010502d901c040b105204e25000d10100e03100200050452203c8010100714401c0041c1c0a40141c071418846c50380c00c294404000743c2101d0110221400c0305200303100104400c8002c00c540751800170f0304800340c0c2c0038025240c160303103400702c10285042150400c0e41915081c14611745035241c0c18040c0344070b026009000c0000096007184007a00300c5074080001d414801521a41064403400348007002804c0300d00600c1c0c00340c6410314000d0000d6962250b644030850740144103e1102c45130280c40401c000041541d2100d0010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 232811312 1250 232810062 232810111
    0x801020403030306080f0106150c050f0a0602030702060f060a060518090a0c020d0c21020a0609050705090108210a050903010608010b1503040b070804080c010203090c13060509040b 79
    0x3040194040c0d500820b5060414985a0038481c0d5040201003da241c10030401580030300f507136075021603070550425071103042450401c503081120300030004460380107201c150320800145901460080c01981c0c2141c159503035030b05031071000c100151400c6a01c444240c008004091040b0010140000032051080c3d1b50114000861400c2d0410707542c07691b450341c503000c0841001d54104030403142c12506140c4040a142192141040c6015a624a403036884035048002002802000304009441d8000c400b0000a03410b82003d42d16614640242442050460000182404000361940c0300341214603051640c5120900c81f0100b940c46440b5000920005100c0180503940a10901c0010103210002103000310b040001c001c1510f4aa131407056172030303009005201c04504500d11007540300349079041804580c0c469080501071400b8000300f8120940c000802c000a841002c50405400001650300b0000801da00541030f05480c0d40c3c0c00780301c0e0002650800030b4042030250000c203810644207a070648008040c6100d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 232812562 1250 232811312 232811317
    0x3010504050f01111809040602040b03040c150905090f1b07030206040c050603090303040303021608030106110f030307021b04200a17010f03020f1305150102160e04030f0207080102 79
    0x19601608000c462200c002d0080c00b44042400780e400449180040c14242002d00e60307404d091042c003030102000002c013042040e90458010385196070324561a07181501d445040c20f100350007000680400d680c0380044440c05100540140c40b00109448010b0351440f51810069200a00106511070386450015110f000b01c0c0040030480e0180c0d02401d600d140c02d0501c410040429404180075407400c20800c070300c0c96004826641c101d50b05150140ea590718550740050352000b04540503001a0700000005140798000080704000d0390070b0f0041c0c0300c0a900d1180c0031074580c00704803a40009a00304510421214414480d104801c550040000416141a2241c140720380c040d4500c04860840000e80700042581002525142c88500e540d620410740c144010009070303400700e02c402801501c000051300c810750384038003032511a422048810042c0385401102c24100b102c0c0ca6000b1409030188814440c0c0110301038a0400545450aa088500e52180e40d000c039120b0301110560030841c040e448000c104404207000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 232813812 1250 232812562 232812571
    0x702010c030c08040b040e1f0b070f0c09020319090b011a1207050318071a181503190203040506071b060e031309090201090504110708040e0f160207180605030105 71
    0x80d00b91b160307414240403821010001d40200707100304205503029403401c0741c581480b058a000200958a412417890100940c00d1090001420860500c00c04200560158091071003441092030464413296840000c5c011540d01c1440540160076081c01400303840705030020b60000d11300307481c50b051808014130200304e900d51056500e032001074000420f00000f02c81800d10504058405406030503010b141401c3d0038101504c41d01800c54800000ca07269103941740b503540d6004440000b070059030400d08544002d104562040704c1c0700307013025080840c58a400405109991040d070340000101019103401006503403000807030603114070241050700c2d1140051402d00a50101c420110021a15101c80e4107840c9d0004e07055400c80514141f03401d824038090707a4004014001c4a0041c3e60000341c0c801c135249186480d01c120301d80900b814500203800903840001982403072140300203110704071942e140c0a041480d030036814070322640181d001010500c4403d481c46079007280004440400200c40d545d40011909441d8120fa = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 232815062 1250 232813812 232813829
    0x70f021c0209043f170c04060305101206090c060306120f050f0f01090203120703081807051c0c08160306020f071205031f05060d150f1e050103050c0702010c030c0804 73
    0x202e03444a070001c42e00c001190214603105d48911700040b0b40c000c24002c91085804054a0b41c0105a1002581040310041c1014a4078035203a4511803d0607400f0f8501900100e1b8200218900061428468407941c425a100003000c1d5a11001980364503420f4a403440301694140981d001d03550002d041007107801d5204d4a02d000100700e18460740101420172240e040d132400f5582d02000b200000a42c0b007a0325992194405001101c1030400c4514180380400d9074001c51b0b0048010f0a5a140482c690665036008501c148600c0c0c2c1007079115944161035544640c280700354000182000d1002403030b40e4015000040c0b00c0040b1504184603034944c0d001007481d000c8580007207400001440001c2400984044c98090343c42044114545010b010450702d2045401c0c16503520390302e00e044603900c0010103154004026440d402c090040e114501030340d100d070100044841103010243c00107101e50090280e207100e03050000205041c849250015102d0028030a002c50401c109481c2460016001d5006407000c4d16982 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 232816312 1250 232815062 232815173
    0xd0809040501240518012105091b1512070c050303100810050108070b0a020f03040e06010f0e031f0e010914101b2102070f021c020904 59
    0x2400c101c40b804464030200e0200030042110700d00f0720360448907805c03040701c080c030700031a1040040d42c98081e80e01100d031007540340900340028001e000100081c03992800c0883c02901321121800780c20400d9162541c080d000080300140b04a88810b0050400701e98007000c6130404160401e0180c2d86c0d030b42985c1c0304941c401c410359802001400b15550400408100b030000c402b080000e54149101190fa4203020700c40c500441000084800903141b09001010f1240c07014030440e034a407501c800603001400003c80d441c44c005242c0000300d054107481111140d06034440078015003154500344110340401c5c0d090094003d200d5443e410410310880092041d00030349030154440070594889001c0d071600700010806906032140c01e00c042500c1c0c1c02d982e48011904040c8d42d09003181c03102404140c2141d06441480303a15a80c0e0b2020030285c0c05d0041c106060000b95100700c50307020341e6140362480030072804111040a5003140b210000a4009841c101e1007025214001104000801442132144d1240310400c0c1170040b8020704 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 232817562 1250 232816312 232816349
    0x51b0f03031006030203060a03140f011a121506060d09290c1809040618080921031b0115030f050105090a080d0c030603021f0f0206090a020d0809040501 67
    0x210903030348010f0080b9142c00e51950520780d00081599241d40800b6000100b0484076102d007080070032090b50b8a910020091000c1d207800700c01d00512400460f100c0c0c1c01802c035400c12803609100842c1c11a07254802d000c068425490340300500c4190780200505081d80c0341e030741a030003021514001002060381c0140503402c9840681400c0c00ca0a141d0140030303901055014081801d60340038280c0340c951464429541e45820b0313900d0b1709203400a800d401070740e19031801d03105400b072047c400c03940020400088150341c180d0840e2100800a9440f6900c1c9502c21800e0700b00780554030103180004c4210300120380d0200080ba00c01c901282000c0413041c3c5030300807608144c4446010041040a009031a0701c0359280002c0c3c84240e0072a19101000d120b0300d1003405c07040b5030701c0381810f030030034040e41c03140c006550082c0981d942001d584041d2042e417a03103050740c0c50101300e844400d00e414900c0000c0c082c2c1704030789840c064444e0b041c1e10b50910103141104101224060310608c90742100342c440703100c2c20b0700a121081d20515011b08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 232818812 1250 232817562 232817581
    0x18010e0409060b121f0906020f070b0a110a0e0d0201120c0f0e0405040b01062007060c0219062709051003020108070f050403020906030f0a030801050f01090f06051b0f0303 75
    0x3024084c258030b034010100d560320512518220b000130b01030340000821120704c14a0010001e2040e0701010781125400308084091281200a10348076032802c03481088070182c42c0c14804064001c94822500040980c0e03030666070750901e0100c0200e810b106041c40c1445101503408034054608248000c400501542a440c2d07402d540311043c0d8103008800c0e2000c00c081e0405449080c80c1c800140613a4042c40780c2c62000c140030700e1025889520300c1d196003003540c00c0d80d5140d0200800d0060310400503407240c00c180307a8002c01021511280c5003200c003c0e131101e00400b0035920310069080042d4001d40d0030180107050000324601c1c24025030b07200e01c032400c280d0321080b8103520026044c03903000b620f0030007000084c0d80c1d00000350350040210f90540c0e404480c0c20100342c3e6807c00082ca0300041c0c000f01d0001d801007208803010150002e103014140c86003224542e0241801d140116207120046c03107442c6440d00685020440e0a014500418065050396600344410300c82403840c91030305070500144005a800007003044011803 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 232820062 1250 232818812 232818829
    0x90d2f0105040e01090207050307050f0a171804111b06011502161404020f13030b0705160b04020f060c06151e0f0301020d0906020706060501030b010518010e0409060b 73
    0x2007400e2160815041c150208401c1c001402985005503000500704280079041064820b00c82c0e0040485103185004121180c843d000c10300112180916641148140c980000640b07118050b808141045007030400200000b6141070001400120002c0185201ca90a0103030b0190300c031040b00c0020700c081d5140a0175808440c002c0010b030021900000303640c0c051007010001d40704c100c5240350408201108107a00090081c42905402a4108000903000450801b0407041c003048a00031124a40b459888003c1507985209111210b003039903e8502008000483c840c503042e822078000380014600c44c80d480003003246030303200c0500c4980d40e521050130030030a89018079100c840e0b46429100d44070721040d040d90207010282c0000f6041c1c4103c844940c1c00555807000d6060340d8424940b01401c3c001034126003400c60081d848813005680403401c0420208095010b0b000b040c04025048c1e40e0185440629542c2207079550f060404281007054407404440c042d51140983c0045a02400000440e031295404010441 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 232821312 1250 232820062 232820153
    0x90501050f04090b040f03050f0409150608011d1e0c0c011802011e02010e0118020f03010b090c0304110d080301080d0206060307061803020315060a17060a02090d 71
    0x2c5040c81a810002215540410f4009521000d2107040e00c2583ca0107031444d0068002a119035100130030002440c21203604032030740c11b0880210507451140ca0300011500d0203c240989070f2610508050244503200160080d80d0080004ca0300c0d10541c00f074000082c5036003130301f5a0104030200c03000c210101000c0c420311a078003141011001040302d4440b0350380042d001c0c1c080103140751003140f0a05050b440480c001e401040c101001d141c000c0100707030541d05000d50380d00380c19201a40114144591140d081c01e05100b0350140c10700041c41280d0b183e40b9245981001d910043c01220304110409001640f45c441200100640f03225049132030710396062040c2186011401c1c14484219070001c0c0a00606480100d10b16041d5a118648807086403038826552040402e1030344000d4041c0300303907001440040c0804444030301a200031540400456503444172070400080d44100703003131a60090400704d6810000344e401404507190203004c81042c1c400e0707510743e0b40c144e49a9040c00351003031a0740300d0ba02d100503402ca0805a030f02c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 232822562 1250 232821312 232821319
    0x10e070908010c0905060912010504050f0f2d03130b070b060301050f06131107050703170f16020d021906030f0e0a020d08090d030302040527040201031e06090501050f 73
    0x49250a0000620407413951241500988002440103115200e0000201a8503c501c000340054182490001c1d80c4000500b4681007034081c22000c002202000300304683c440d5800140e5001c0d2100c04100500107503401201c0c0c2c049413000304000043e0980300328901d0010000210000d8407082d03181084422a000100664840d900d0003040080140c101502d82d0341083c0150380d192141000d1841d83d900a0100c900042e80301180441d20404200000424000340c0740b0804508888021800c8003030b00710b004058000365801024031007000d05900d8040c1c8255828002010b00800c02c00680204000c141103600c003403c4040111018000282c060148444045c0030403020400f65444150389516812540781c0244035641c009410b8080c0724101013601c0080c58000c006880000c1e19150107802540a4819240184510480751500788100d40c0e0448580703140f072541681e20781e5550300440090024501000040c2e0f61700b018004000407611406015104040000401d94101020400804202c20b9424070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 232823812 1250 232822562 232822571
    0x2070b0a050714030c012a0804020a0b0d11030112060506090618090a06110c120415031e02040f0521030a140c0607200607020304060e120105010e07090801 68
    0x1045074440101c907952500492a11403c581082c056030540c8510b00d01010a5030170448080e001c40500b0300c450640300380c4181180a8000c2450042c2c0e1204001c94010303501c403540c46c8081013500ca0742c60050400c0748418400068021a40c2c540a00c550000e812400c9840c0380380c1b102c0000c0241c00e1080300d81100381210b1000d11454050002020202910a01c2c0004400030f404104a2001040b807046001d50008040c0300c12095544006659080764103800c620703100300c600541a404800c021941501e40d000c1042c0341a40658000f40d015100390b400c4030000c0d24101d10164a16007003407002d84044c2c002c03400a41e00ca81d1800d001c0105404101d00c5051303001c0b0601002d4807035444000304580c1002e4050070b185501c15001009a04c0c14001d4002c0c0032898064502004203565220004090340302c2c00500185016130140741c3c9a070b0350007049030703070708003503442040207000d10b9014010500c0b05140040030715841c2001c0258140c00c3d2402a0300121074540c00c241030080483d000700302400a0f0401200800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 232825062 1250 232823812 232823827
    0x21503040b180706050f120403030e06180c010503150a08060108011a062d130603050c031023130219050a0503040605040c08010507021b06090a1e03050d09030302070b 73
    0xd4030f8090600c240030034072030000741e0084900120b20941e1140007018503803089030b00d054280500540f404444c0340500f4011503000400c0c81c21000040200107001c2401424116074060042d1941e0344064a512141459000d8902080da2220b940001612032500030b0101c0e940740201c0c0b01e00b0740f00030000b840790402c00c0358030350042c507150743c0d06440c80f01044100c10354110340b0782501500301c6900304003082c0324001c00107000c0d00d604024210b144102c484c59601080315642e8606001024041520895170900c0d422000f00308045003102e03030b0400d002c42400c12440c8480c5400c0021544070407154401d956030340100b0304260120120000e400c2c0b0300381905000c1d146c18080d000c01000d61100800051545a0f5100402d0038490400d2a1001804d10400200400c1c102400c01030f5481e901c00c008031815403c448200c5529081a00c1602c10341c18000c0c1044c01202e04120b07481c0c02c80407280d8141c0381d18018210002001c9803080040714541d94403915194001c50442c10002e0402c500340c0c108031517500e41002605c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 232826312 1250 232825062 232825111
    0x60b010e030a11040507050c0d03020a020601060f200c03031c0e3712020109020f0a050d08030901090f03090311060f12041401050a0b0103050f010501020c010c0609021503040b 77
    0x181e80310f03030101c1d80054195610705066420307010318100d85501b4400e94082c404100d170168010000050113800700c400c1607a0701d4204444000303070b4059007000200300c074146104d165090004007103020310305810f0300d044ca2400300c04030340307903401040041054140074100c6001030120352248441001c5d20720050400c101500c1e640d103840201601490ac9448010f035840103030045181d01c0201860b5102550904024400038004d018000c5400164402e10b02e4044040c12464101c0c5402c0440e40b016001710141c003001d0b201c6568035000203021406c25521880b60500117a0000c01d03c10340b8521944521b4000c0b070035070410310014041281140d00510b003c020202d1242031260a03601c540710b0104249903140d86a2500c000706602d14400108690b081606010f8180c2d11500944481d0500380c0e02000715644241c0e852007890300038440c050150704038028180055203e209090b140c14041c00001c80c900505c3e9010842d07141091145c0c0c0c4c904180071042c003081044402510390450044a5881340034404c66a80d07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 232827562 1250 232826312 232826333
    0x41802060a1d04020408150a06030b070c03020c0409054306090905090c12031308060106020c1905011812061b110606060306030f0f0a0302010e070b030a09021c060b010e030a 76
    0x8641d001f00007200261210005407c698050b650140320708109040c0040b01500c904d01121086007d130103000c0e040f51490400d44100702400c0d82050003024440300c100c4080520f0000d041c00c0f0703644001d04003094440b42c90f690b0001360185150071092502e5601e17007000100386c81c1071038022591150900040c0480b000f40058202c940c0d103011520f00c00c06541c00000f540c40c62040300f03d281c0001a0662002506030030108105048441c2034098540042d8100704004c1404600b1500ca010155007110900c11544100d001d40010031000d203400c0711140c0c641405401c00c9901d01001c50710300e525074a1130200f040b4131240c084030320040ba0500c0941c0c054040c1d0115164480105010b024860100020f5501c0d50100320a401c0f201c0c9080c141d4407601d282c00300c01034480718501010703002766003401d80d900080c030310029410044610041d150350668440500c0c00d805480d422009030b80c001070042c5c5001c90309102401400c0c1c024442c1d000050b00c3c04c10800058114802480440d10a810a100090104005d4101c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 232828812 1250 232827562 232827583
    0xd0f0b0709030c030b25020c09060a050102060103111519021902030607030c18032009090304090b0103060306050906070305010b041a03090a050609150c040b09041802060a1d04020408 80
    0x80b004580d07a4208141d84035002800d10705c0001b40e080d50940712060f00401c01c400b600c01d094801120b20b54800e814454805098403030700d80181c3c800b800410220302e2030034008140704e01c010420301c51101c003845c2601c1243c2000550001982024807010344940d01042a1043c500a030400c00704100303000c0d000645c80d01d50041c080303414181c85803400ba06081c0300b505e0540d00190310010000255440e82007504400340c0c5806c03a884040c0c0f1f5091468298901000c109110b4155080110315113030400c608040075045603146035040c9920341501000160380c50244a206590000c02080075107841c2c50001e00342c031410b80c0b1002c1e940e1000c2000b0300000d22071316440c0c10f8010350114120741d40e85914036254901004540094900c0c042c070001d00400460100f00400320741780e6030301c070829941c0f251030b080c51686c400c0c5d01c10486003010421547d207007030412340c010003044004000c03000307031145540e0003044c9594880b00b04200000c614030124222008113164007602c110054504504040c1040c03142642c8103e5001d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 232830062 1250 232828812 232828823
    0x20a060801210c080d0914190608060f120106050f061204032303040b190c020c10090e01150206070e0306060904060905100b03010f060b07020418080d0218030604110603150d0f0b0709030c03 83
    0x400612261181c80c453300705202c010b442c41c00b45003203080d003441c020308490003002d1160f442080f845480b464000d0644085100800c66000c03c1d844948c2d05030b40c10031310302c55000c9014400c01c00c00d2800c618403c01a44c441d600444900c125840e01210003001b13480546012038550b80303406500c0c4c1d000b80e40042c060741c0b205016100128580b0141e4019154a2040e502100f035401c842c100201c2c2180800c000c1510003401e40d000c6900d5901c0c1c0c4841034a07001740b1000700139056131003400043c034038dc60a901a540c119000d51000a505400781e01e605080c4050000c480082580b070317080340c05981c142482141407281c80707444100201070074850075102900c2a0070010380302d00c0c1c6620001c1c0d41c0d0110340e0100d403801903000b01c1b840d6403101140200c0019400145100c03e440601000c1508035040204080d88183d6208080d000220032004c00c0008540000d001d08070764036070b00f40445156454032903003071504602035031060b0400c5142d841d0250b0341d0000141100100211717003d0800000301142a030714282c0f07a016 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 232831312 1250 232830062 232830077
    0x21807090e0601120213050102011d0606061c0905150a0207030806040209040204050d0f0618050d0c05160e0108011508031e070f0b04020a060801210c080d09141906 72
    0x10012501284004e9011000d140700280103000000c0c2c0d0603108080701c0e020b030020301105400d8880e4180c800d4004c0c0460140c1e4000d54001505450110000e100401914505101c12105c4400c1d5a00704d03501900126001d034031410400b03c49801c0011821b91140000c80198904105643c004003010800b0b01501d00442d00441c10301c00540d00c03038054030060080585400303004e01844c1454801010507000941310700d071501e445c3d480b036076030900044980190000000c240401580d0000c4542903818003050301d840c001c100303051861280e00ea40c404018058441501000c0d4180f01c0f26508603441d5122003950f04040c03000401a02d400032060f039058070000707204030840800d140342203481c601c80d0080040110021864a0041040501c3c0d11402180203a42103041c00780c5035042910210320070f00030a51040b0714501c3c0b015490400d4050107100910030f0b042d058249544109141c9402c40b01444007011808129042c01200b85200c1c0300045410120354000c813a504212651003c95080c1c0134020410505 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 232832562 1250 232831312 232831321
    0x1403161704030203011e1a011b0f0c0902040303020c120a02060d06030b0a0204031e02030309040b040212011d071701030602070305090d030210060e040c05220f0504021807090e 77
    0x86010346000b980c02038002e200403059003024541030440619074140c0240381c000329040041c40c5460881f0000c0c0e040e1504400210b048004110010701c49004907000300d04d07030003108001004200d5040090280c3c1802580f05c50851a029040c441e90b800050301401300000c264402800c00910452034036015141c180c0d40c0c050005404001c2c00d0300b5000500b506803200144481642c203980108122400f0340e04d032001d611801c8041d00200640100043e6241d44240302d410b80d54038140c3d1000c40d03c1c00008000600d0090b0504010014100903070100f185120544010a10705401c1c0d103c05074030001320b00c1e0061141d00581003503507a1741418080680700030742c0824281c04060050044524500b4020b084000ba0303c8249002940e80000e48031074101141003060004003076010070806401540d0181600390420305000c00d001c009540700e140c42944c80713440044020104c41601c6404128410f02002140c640391600500c49400f42c81300311074107035034040420000c101d03503c40c041c1d105582041d03404c520345498 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 232833812 1250 232832562 232832603
    0x204060212073c120f050a080a0c021f06030b06031c08040c0504140702010e1b06071b0902090312030103050c010818150f010801060b0703050901090906090504140316 73
    0x12021488032804010120f0414000d4030b18850602070441d41d11550300d07044c1c1040480307603402940c2002011800d41004908090700b070b5003121680090520444100b4000000e05224201011002180076592840203000b0302444c03404c0f0300e46c131090540040c8000e4001d101034601d071501e90256041003152940c040340800800341e40d1300c402418018014045a182c1020b4000c0100e0161981d10240d0700e0104c213003602007004a441001e0040b240324030707018034040b401804080e07030054004031004800c504c00500b6140710b5900033409801c0540c80140c40300400c8041c585400a960305a140b1480e091004000081700000c0300068214280b800c5071894071110300481c01407804500e04103e9018148130031034110302c10921548904086e940c40300859030788404c030900300c1d501c9000d0801180c40800072040424000c0000b01088501071500641080d500c00059048900c1d5400c400328007070f01c510a01050120300040007003252000743c051840d01a190049166240d0910402016126042d80c4d103441e800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 232835062 1250 232833812 232833893
    0xb040f0b07150c031d06091f0207060e0a060f090b07030f11040b13050f060f07030909050c09040f06050f040b0d021201021b190303050a09050d03020406021207 70
    0x110b5591060001e0540e050014028183e041d0141c40070100044e8010307840400010842c0c0071700b0320b42c0b02400041d4200c04262405a1351400614003241d000c10810000032014800d4590750003030750303014050060f0031740b44c407070285c0b103c2c12400d201d4541801c959502003402e00740003079005481030400141b5502e5280200300501188540c038454044007007400204400c86000401074064040fa164002c240c80b00f04119500001c0358a40350080340900c010302c0741c424400001d00303000d8020f003840e800142c1c1c1d4a21110070754004035400c00703403d08045111200340c105401450b801c900030400c203001041c20403020840000c02c0016440c40b864440c000280c403512841500a2483e40150070806100042c3c0080b07400307075100004038201d05841307040e014001c0d0303800b0552014a100815840d8060310f07540e18210060a0040c094145156444014000050040202c07030034505151b180507803282c0c6004800f1f8100078030007140003495801080a1000030311210307049010f1484400c0d00044080c8982410920203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 232836312 1250 232835062 232835093
    0xd02030f0d02010218030321071205041a1e071413030b060901060f0e060d110d050708090a020d02240d0501050a1202062a01060608060a0b040f0b07 65
    0x50144100301c1201c1075064004000400d40000043d101d50321030414581d42c0e108030309003804515499500807901c401f10403c0c9030f800a86d0361030100303500740315010038204030b400a0b03800b00d500781000303a00e0040008030300c1c4a5550007031000d6003003c00191003d100092280c0000d15542c00c000c1000c1012500802d00800e41d032421080d481c6000c170040c0ca0780303030002c203001c015100c0a00c240c0030a400040c035144156800c1410704004d035a0648080a4101032200640044504903049a00c2d19000c0d102400004081c0c06544083d40b404145814503030030107044400050845412604203014010140c2c55403020702000581c1918481041351400c6641e0b49400380b40300e040901c03014000b407948094085600014180c46040720b03030140c1e00303544540b4070391126410200290020707800e000402c510041000302c4540404020420440b2030506c101903821140d641d00040041000f82092000500340320020f03101500d9101700e03092070b003414a80b64a5110a091261403003417000003500b501000f90242c1d00718400c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 232837562 1250 232836312 232836343
    0x14030f0a02030327031605070b03090a03030b010f140706020405060415091d0112030c02100908070e090a120e03160303080718060e01021203040605180d0e0d0203 71
    0x4500d0200c50080d12940f007611100d401150b400301c0303040c8440c0320040c8040701495900c020b41c41c1041502100441c444031030710640301c078000d55100040418080780294840c404100151038110b120740303800340440380c03140101810085503170460001a40c00110981c100701c071174580c0c4c41d151034852808030080e201342d03004a90415004a070000e1030460450b58a49a251203440f10301406445207049620b030551441d4480c00004000010080500380e4004e140105000745040840704500da00419440f090011280c000503040d00000c000010041c0403800103000a1000b90300b0034240002020f55038191100050403564a4100042185024007118030a100b005025201c0c1148581180350341c0100e1440241c0c0820031443c00580290303c40d80d00707820200180034491012600701078040b2810211954043d040d4440d6282c41d40c810390000002d10712a503c5a04003190074a42090a510243c42040030040303603a028100580d8840c1e04486480c0f030100c42910441240216400003925180c0740c1c0c07900a09 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 232838812 1250 232837562 232837567
    0x60a0504060f0b06090616120f02150f070c030e03011d0118050c09100f15030f0516050f12010e07020c06032211060d0c0806030c03060a09030e09070203040e0c07030c14030f 76
    0x249c3c0c2106801300320400540a0780c0d1300c000108000d07160440c040b070703042d90907190500004d0962401285001c070118020b10302407003a841d40d940030908441c503440d0303200b00003001600c000400640c00d000302040300300801042d070a60005a5500340d41c4840340c941061140d5044000a950501c1008000000300741460000004a90701c001e080b1140090442090000f418110b540880140500030302d801400500a090034078100071000725030941084040c44c1c000c1c9420000d914a01d00301010341030181c14202003289550404210181c90b1032100b2007101d0085d00c040c02009080b5607a000001c207080481c400d544510340a52400801040300344900c07660004003c9100d0041c500280e10036114403a03a619081000c0c0c80b0794080568814101005590603482038002509101e0760350000f4a1152090401001018281000400300c540480f11000141e101140800104e44449000f641110000c071280746010712907180142102050840a0400279504804e042c410604008403024455810344054 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 232840062 1250 232838812 232838843
    0x101a041a0714030703111b06071502161506270504020f2211030126010f0603080307020d03060b0304140a06020c010b0a080111041a040503060a0504060f0b06090616 72
    0x4100c89038200c46d2941c10f00c40d510025590340f45800821480200c01005282048000d80e60203800011031440e03440e43c150240500d11603100400e01c0c1c071054601c01c207c56250724007507003001000c894943c3d00071407905041140080b41c00440d0000d4150580395044042015a22400842c90692403500c4190704810b120340300d11002c2d42d2072400b03481111141e1000b40f10f0780c2450003200d68503000c05c0c01483c00800d401c1150454901d04004030b14241131580c000850740308080a010b0044030605e40c402d9400840c00810810899811b00c9581070001e1030381400c20405041c0440e010803070200500060100540300d114224000f01041028170156000b0000e543c0d0709a02c105541c0030b405041c08050180804210116054006000f0611000c0c03034108010706041c5401d03010615840084503011b8405070400001c11981c40a11145110303a4250001040e2403c20780351990444547c410718110251070000d081d4141d0350fa500803500c81110444400303490710155901e2080c01414000b000341000c0f092070b10711 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 232841312 1250 232840062 232840067
    0x18050d0f0507081f0b0a05130b04090b0403050c06010b0316080403121e060e13030e060c060103050c12030705060f06060c01090b0f0709080706180905101a041a0714030703 75
    0x100800043c4c101d09008181030720301403040784603c0b409400c2d03024441c01113002014005078450072100000910200b0010003907140c030011a01d050b0750590000d640055000c034103040402840d4010001420142c1c0355141c41c4089006060325000100300700408140841c050501c41c60602c841a445000b0805c461304c8101c80c0d000d12902d80d0000e0911450401100082c842c000e10b00044c420020340c01103919406060b03500b240c00e030342c1d001d80d03d0b03600842c1440300c80040d010411101d03029500c10401000d070302d14002c0801c0a0512a41302d0344404c0e074000c00040c40004e50110b842c41d000380320323801080626103030344000640c80e000325403810b4021741c81c10440c0c0060011030b4510074003a0401e401c3c603003a039440e03002d0103e03803442241c0900c521a40c80302c1020411148940e0000764a407250b000c9400d02c0544071500c12084c1c0e202601c1c440b80c100106c18003030001038151801c8188000d115240303545801c0c84c3c040803050355041c0c8804c5110841c0701160030410b04c00786500d007054054900007541d40c1e80401e440d02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 232842562 1250 232841312 232841353
    0x4030602071e08030c131e080601050f0906090603010216050309092d0603190303140a230606090d140d030c021504060b0405040c06080109060b07060203090127020118050d0f050708 79
    0x239403042d0300c01d10340005590708103e207180361030940140c4000c0656a982d014004145000750010790559400c200381c00a03e51400c50030001184120013030340e52003081c80700b0014008005041050850350f00981c20b50107000c0c03036200068125040b01da4084035558200002d0400b004640c000030755040b50801d400c00c26515a00c41302a022680101080648070308a450f001c680364825160f03050b907045d680714858444600c800f69482440141034030310b0510114085000080e5052040b2545999540f515407011001d03c00e0300d4100009240c01c01c2002c82c2e0103402503461070b114496602099620004c18180702c00d0f07410801c4400d0000d002440b59003040e1804002a114078840d42002407154000400c0459440c05681c04403001280303424101910343c1c44001c002d601c00740488245658030304da801100c000d80211340c8003600300107203030340300016841c0000350140c154000f45c500020065001804030750741c0c0308100320300941c014180c4c403000c111a10b002c6240940319000100136201e5130f8922460117505841 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 232843812 1250 232842562 232842569
    0x1206012a0318030c30110102010f05060108060f030a05030403120f031401150c02040509010b010e0607020d030e1504080610060e03120f04090204030602071e08030c131e 74
    0x48816444030084034080b40800240030042c405011910200500d0722080504031542e01c6135460b1030450803c01252540703c80e80c0100c1140c40d14101c49050302d42c2d41e028868403040001130202804145454000204815001402c042c49009043c14011154604101d0f080d46070781e000e011203940341e886e424920b140b100b405586400040000c1d10391170b003d40c481d016500780000c61441c42401c503406d0a00080241c43c821090b41c0c00c01009c14000030142e41c646c0038441c09400264000a102c807840800180300b810039119050003464201b02541c01620b40c803550390030464043c544460b05003a03803000200504044419007201c204013040100e0001404640d0034040c80e03407603001007801d035510442507648080c29105580d0503001606565090308009005011032103400d59071a10f01503c644001040360401d402c29a5651f84c04580c0a040091006490040c104454615154412030355110142444004c1840d81e019001080c4001c001d40c07424601c10282102c4a01050a601180711402c40c0d08030510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 232845062 1250 232843812 232843817
    0x1704030812161106071b0602130f05040b030a0b090c06030711060609010b0d0507120603030914090115030e070e011202130c0207030615090c080118050c1206012a03 72
    0x501070b51400d00800d5a180152100805820199100d0300155001d09200312622924403000b03038150b00040440c402001d10a40310411120150304191402c6000222500b0040c0528030340103814850396000076202500a50100c0c1c500401d07640e2564207810072003148092608030101000b409001600500e0004841c086102110188e0b03440500300320000d0350a114198217010104030300790700c0c1b540703942095501c84c26a003030540840d901c7c184484200c0300c29501c184c001580b105018030201c404080306a607001421180c0c405c943d41030600116504100506034010f0558940040e1008081404a4802860000400c82c250b6940380c00c080b240b8544800100d00c1120300140030000c100c5c0620030b4aa802049a00902c3c4013411591610b0051101c1c260428010b20300c81c0000401064034054a04480300310fa9a54000b5450014640000c9180d509890070303840c2001704101c8038080000c00d4800703542c5c100109500d0b0742c4803440161031491009280c2c4000308506d07643d84182101c10240781c0b80340e51003a07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 232846312 1250 232845062 232845091
    0x1513171b0a15090f0b070203040f05040903050f0d0e0604080a0216060905010e0111030313020a06030204050102060c0d02120103050309010f08151215150a05010305131704030812 78
    0x219a907526041001c00c0140045103000d55001803419591054032072902c165041c1801002e19202c00d2203000c003c54100006030300004041c1700309880285074800601d01550b0a000d08403190b60042c2c03040c001c0c0040040d4801020550110801554102c0400076440a0a80e031180c1046d06103a16113500c010000c1015215a0400b91056610400e100007120803554900c40e03854100700c01110480041c032640e40c1080107441c12107440182c280300a501405540e40901c128246a01c180300103007010794400e40078103106000c00c220f6a600420800e508c038483d084020380d40d030540a401402405514160404803034105e001104000700040101b40140c8262070705655004841c108885400d400c441c502d0b402d20700d504440035035007440740313502e0440518942079500012441c600842c50b404215405080032500c0d80c84580300703003403d09a81d800340601b0300c0c040c04240340c60880040001c924a500038413980d5240c6260320070843d04070564018542c401102591418103603045040710105991800b000c4409 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 232847562 1250 232846312 232846357
    0x307080f0402030a12030b1905010206131505070c08030a050411061c0b010e120c101409010c080903010908040e0a02040815040f0c0305010c0818151317 67
    0x4000d485031090b54000c00034410b45090342c0d0b40000e07240c060140d280501d5229902d9118a60b03a003d040c01d000c4079000300b80c12103036103440002860990064144807044000d580d6000100e45c0107150f2003e0103080f100b0215039a11481e004540904240002615079075000c0706011038281c0503040709001d00d000b040031211071440c0f501045814451400d403816030501c0d081603050604031640040507100c0d814148110501110b50101e03c00c1d40040e090803085401040070004c851034500c07200303074106400e840c02400340340c2203000300800b51066030403050501c60600074201c104141c0d8411120f215401030001c1c8030191441c600003c0980040c01036506c640203400002c0c0c500c9038280b0a860844187c10000c182c079a032038208200210710040d00c00d542c003401e41c00401001c00c11401060700198880e1000003085c0c400c804d8014070140016164502c8a103034001088005100050308103030701e540304202814151640d10b00ca504400040b80700801981c489900700ca01d00002e07401400c1c0e040403003005030003e2402d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 232848812 1250 232847562 232847581
    0x305030906180d030b0402090619030507090608061c0c060201020d2301120c1a03041b26010b04150e07080105061c0e0f0705041107051203100308070602030708 70
    0x218202c1c01c0311940d0294240b034000c0751194000c01c610160140c80140350040050106078142c0c0074640d02c402c442c004000a115403a4148a00c0e40c0c040064646000e0050a1210040c01c003100541018481d210665078045040c2d034480e10403d159602204034500599a000d010f8042e400c40d503032200650780780074051b21a43e40480002d0a041d0707152a6001410f83c20030400c420403e1400e802130320361508841c000706417400340c43c0001142e602c800c0c02c6a03407240760a280030001d2003850311800c0101c468580040210706a2040358122240d4030f9540350301c403030030824511401008442145540036041003915610030301d00010340c0090718142030441145649500040d26414028420603400c00810011407000700a240c08010b02c2050f044000302d013513024000a24036010400078164440c2c0c00c1914200b20342d140c58840c0b03048917107140c00320718184916900c2c0c140d20f80c4035464048010b50000000512510410600400031319031042105d0b0320385515060680003500111000004241a04080b07102d064 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 232850062 1250 232848812 232848841
    0x5040c081908041a0705070b0414100807030f0e07030c05040501061e05071119081018151e020c070e01080c0d03051b0a020414070504060c05030409090305030906 71
    0xa402005440c90240f8002c41c14204500012180306104c101380050b400182080c0b210714001d100e42c1c0d044c00e4955040110714000706681c040d15500c51540e284000f1a03290304180301c0b642c003003d00d00f80080d8a0030304c20703100005040c403280e070040c0038040d58801008001c180049039003541c0d003e4030b04001580c0c8501c2d05031911003400e0303c00c659040c2d420003c3c41ca2a813040c0010001e140c030a00c2070400050701940030442005501404002601c8040e81c20b001e403c000300040391341640c1d692028400403403004041880749000c0c50b0050040701015454000e01c040c1034000d1050941c0e6901504040415000c90320001e40041e982c80000d8044c103100000c5400c02c54607002d05a0b12183d01030b06242040c0070411601d5146004d0031402d0007400d00425690345500481000c4100f41103014050802c50791041004623554200c099210356882c2c400d004600d036000054405603405410205404516401c00a10f90f0140780d1001c03480c9820104808c0c04c0680c0710300910b0081d0740d207000b00c5d105512011140803140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 232851312 1250 232850062 232850113
    0x307060905250b0a0c06020409020901020c06090a1205030f0c06070f080f060409030e19050102010608010203040c15020102040b0f0d0e0f03190e03010e01050402280905150405040c08 80
    0x2d84019409000000b50392005010810a50620300c00565065941030140e0700180d100d541d82035804180a4050358051140b0f0981c4001125130302e241040721000658486c4085c047c1c00340440c06400c11601f000300400458a116030f0102c0b03030f942c0341c1d1103014030035643e0389048a51000082c01c071001e08002e1800b503034409004501c1d40c0c1c03195040e0b945450600c001852001011703010420744501000f029220340800b41450002980351032619820040064255110342d40b1001040e131041040101140b02d4001940c240d1700a600205a024602da104a0190040b504548280c1900207501d40e01503c81400800705800a15003c3c014841a100c449442e4400c00405002d150010440d1000f80007098030070a40e00f42441c01c0c01027078010703418042821070301c0c0c01c4500c03080c0b690740e481070105524000856520311507143c050311185400740323141a001d8081c0c604c140c3e1402501c03800482e082c21420b2a680b445450040c0c001c020754503160825100c2c1040b6031103421120b00410056507001161070300203644e603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 232852562 1250 232851312 232851373
    0x71d040b07032703050a11030f0708220b040f0b03060904060b042004080c06071a060a0902120402011b020607020d0503040302060703180b0408101d0307060905 70
    0x40c0e07464940a40c060403030311803c289400003100c0d1203603109103a03282030b414042c02540d0741515000e0080c000313042c05020721000800c03a80144100b01072080300708125060b150b4000c00c401e80302c0310542090706100020000d4890104281000130941080c860054412541e00e41c814101f042c3c3e860017840d000f403000b980c0c4940c10460540004001c540c1d01e40118071700b1000604005400c02200705014564140152980039034070000038100002d0104001280c0c2e41003048500301d16008403903032280d51b016402101400c00013540d80c0055091b40e038040da540b0041c0fa544105664611b02000601d00444086030100c0c0415400c01824091401441240d103030b00d94090305a03403804603a9020081c0b06011544221541d03c410040070005031184009400c1c010310a0f16608640c00ca0000c0d0b82c1b00081254108800701c8005110030031401000003040702c0285412903000501c3c0401520174080743d0008207a503452888005001400c10215a1104003102d00034410f94070303150110100031101040c1c0fa0090140c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 232853812 1250 232852562 232852583
    0xa0b03060114090d0302011401060e030a03180f090b1e0a03020402030c070516090c140f0c070302150406090b0708040303050a1205011d06031f0c0c0c08071d04 70
    0x64650140c80341c1e05220b80c4240d5410308012040b80003880c684070f015001c81c0181d4603185084e00198a40c03010340e01516890500480400d09031010a6440e01c08206c05820071400301000924603001c0c10203100940f80c500340c126a51038860f0a91000f4000718809540201ca146a0038501a00340c10602100154000c04100006145400304400317500701034041c0682c81c0040180c3c000080c005c00c440c800c401400605040840e14104c00041143d002d0b01d20300080c000c0482d080905012550200c0760300c40c113519121600c03403000c0b4142d5847c10805400094104040c40c11890f514108180034104985941d82e5110390107072941c18501050141400081200d18140800d000180c02030015040e0203050349005085400c01400303003000d560b0283d02000d101c0408896820b0f502d0203070003600d54042c0d8203600a1130100304d1001c400381601003001250604507682d00c8000300040c4507180580e926034000100c3c0200507251103107242c888101d4880c000150b030440c0d1101030600120700c01c0321b210701d400584840 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 232855062 1250 232853812 232853821
    0x90120060c0a020309030303040b0f0901020f1c090209100918050c010503040312050f061c0c06080619080102090f0a0605040b0d0902030102070501200435120c010b0a0b03 75
    0x45254110503070302c0c001d50009104000440d02c041000d98410b601403008003c1608210325003080c0428090003420899004000000100c03074a4011103600368901134078180f1035440405450000c0c6040309001f9417100c6103405200d88440c040450a0561340541400c1000201810310349425000c0038000038400e4008002e030f14901d601560107142d009000c0e0600b034980d071518001d0f03001101c20490b4991140d02005041c05405e00744560f0074000b54480d240c2c8104050f041c2c1e1a245242d104e01e1285500300030040000171529251007251080245144c094a284a03484a00007800307500804443c5001d0215103250f00400d03e08105e4620440c0c000f80c41d66440c150a1010440107035000c041059211500c40c0801070068800f4070003406042d01603000060780c4400780c3c16100328403990401441c0039420500081c07100e14860f160248a4404c000082a01450002e00e00d006183c0c1c50034280600d4050b6012812103005070f40001c200c0425510020000305103400104400000c4901651511900c01d00004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 232856312 1250 232855062 232855081
    0x20c0d06050a0605030307050304152607140f04090c0c08121f0b030a0507050f1c0b03030a0f02070b18040902031c0c02011b02031c050c011109012006 66
    0x703500900d03110720100f0025150760129245510030f28048031aa400041d00300001c0c01c8400000c044404546052030111500310100b02d441500004401d0110070f80c840803406043c060458040c0042080c2d04990321864841100c0c401c541141c42032500960030011405000c0e403160b0400c016075903000a2050606181e41c136484140c03200181503141500194516110b00030b6207844a50050280c0b080b40c42e901c1c64806c1e00c0100396031015200b8400e200c0c06005089018001105403000d200c03460a4001e44000d83d1030300c14019140b2071824507050700000440001d541c2e8003c06030320f911041d6408941402d96980b120303228611413042c0720800084030719a104080d1500ea0006591030b4002401c0701c80a080c0310721000c1c0303103407409070140022440243c401c02c21960480302a1041603440d01c9610210001a00407d44450b4803020100d400c4003010210140a0b006006030f0301402106402005109c5900300f100c40941d11850b44140892180c2d80d400c0e403128400420014a10503031006000e030790700c442400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 232857562 1250 232856312 232856321
    0xe011107030518150a0e01020f030406050c07031406091b030a12120f05010510020a080301031b0b030114090c2a03042403110c0a03080414060403030f0b01020c0d06 72
    0x14010010405188001d0f90b5030703080da401028280d014061a900c0c803440201401c050501c10b222410342d0401c00024540301c20100c00e0b41c048842c0c070305000b6502c4440030482d40c01d09e045900001c2060352072f40c9410b602d541000903002d102d030309058115070741170440c00000000000c031a1601503140d40501000310028107402d0106003500d51a00340f10791000d40c80512b27401a41c00f425600c441c82941c03640100050301e000c2c071050081f030503280040e08030f08069403904c071103034481404081d15400c0160211603460b00e007007041200803c14540300307540b2940c5800b161400d04200b40c481a200b151044081101040720108580503a64003217004802c0d0040340800002e024484d1024140c580414800010000c1c40c003e80c0000391551030782e4a1079040c480301030140440d0101d40700714500717410034050001000c4001403100c0c0c0e01505030504124694076441c1440d90030305104050700041c0542c2003800100354060300300300e040350340549051042c0c440c5e40d1b004980d90341c1c08030500c590005030000d02c600404d031b03039501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 232858812 1250 232857562 232857577
    0x3040c090c0309050d020c0a0605040509270708100f1413020f04060608090607090312030207150c0e0a080c10050c2b020f120739090e0111070305 64
    0x2404508041035441340f60605401c5601540540c1007a20203401c20314014038240081c0100782000b6003094140000b140b01d005008141003da0011600c0b40001014900c04a050142c4021300710750320180c07101181c03074171548200c5203d8416410101e400301e0b244014001c5118290103c04810301a559000307104651395414202030ba006041546000e40c15200e40c0a0342018002a0321480901c1c140f07270034130070700c0e04d4401000d400c100000000c1c14800100022803c009a480f40d1030090707101c901c6400c05401c00e0b0150707049801d100d4a40185410500d400c00043c81004000710b030501001c40ea90142e686d20390455002665200f10b0210111a116000f075001c0c205103503801040343c07104281035001005403141041c69008040b03075816400c260541c100441c2c10305468a2010740400485160740c0c0d1003a00481c0c0c0000c00c0551525421103640502c02d52074032110141e14000c00c03c1e9400b413105c2d2084d2a40301d000d240ae086003000c1ea96448030205000c0d8102d603468400c0518508112910110342c42d801258 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 232860062 1250 232858812 232858817
    0x50d0213060b0d090201020c06070b0f1b040e0105040c030605150a18060504170304030f11010302070b0a0f0b0118030807080c100f0605090601090510020c030105040807140303040c090c 81
    0xc41c0030a0b11205040a4006108400000500081e50740006840c101580194610440d0208096000119090b000d260090001111451192517003880e110050b0b46101c6200d000c4040420005011a040301d08207040384d00644080129840307a81089050381d150740a041e80043c3e060b50315400c900e0303c20f00241090092483c18600d0a01d2140502e220020282e002c1c0f07000820202d414800821031407403224100d008200103516203480d6a4400c00120040c0a0140c00340c0044031803034032564040e4045800c490351040c5ca140b241e10300302c0320341e40003020911204141e46280446180c041d5000c0c50007113108113400c46106103294550380c0c51540300d9100910403207c0c20001d001c0c42d03801d60070402485071130251541005c260300f0510b031030718000c40c0c50355800684600c90313007024400d00345d800807920010740f0300a03120024840c101182c142d241440a044098040d840c040800080c070184901600d1901d12850040c1c0c400c2d0800e200d0705913240015200500076010300b500c00c00002c0801d500c5105502c0460 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 232861312 1250 232860062 232860071
    0xa030b09010b180402040b09090a0305090d0b040507060e0312090f06071205120a0902010c0201030e032709150604060c0302101107050d050a05090402090a050a0f0810020301050d0213 80
    0x40012074810348a1030b064281e03d88240b81444110328041c0a0005644016034004a0314a05045591340ea4880c0c130034090240100024501082d07180c0d45071054440d600220300301c10724182403400035500c65140c80b17100d000810242e030031441840c01140c000d2804080c40c40305810282c07100200301c080c81c0080b04440d40280100020300000700250b804059030f0300c2d41d4484c213813103185500c401c401e07175603005080044140ca001140340050381c0040d65032124680a10300081c02d0010000900c0c41c5104a0302042000c020603511f42074000c0c2503445032105408169000c0185480701d0102d08030b816140040c09a0008040c44107004980c4295296050a8003910484907287e01050703c8500700c4a0240028007003540014a04050040030408060900003134130b022440c02ca814103008042d805600102c901c07842e00040c07164119920a031b00c00b005083d0041041506540e1908025070000d07040c498500640500d020b0750b0700d400040c2c82941d04841010317100c15501a155400c2010b10a01c0c21150702540d641c3c3c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 232862562 1250 232861312 232861331
    0x90705030105101a090a0b03070306030c080f0c040b0108010308130f12120c0203060a110706020a0c050601090c0f200601080c0130020f07080307021006080604020a030b0901 76
    0x9000e254002c4100f0304811240504040c0c107030345008510081812010380c10050307030089480741242c8000702d851001650b500d075103400500324083c0820b6032000d040048d00c9000440d07001c90200d00c070340c00c40100c3c0c422200203403554400d0100356406880000e0110305a0b0b401040882c0c0004002c2c01c04104407504031403050b488241d4030b180c000842d00424403040c2d80101c1c100410198400c40c90a440304c5003400d107008481a40001e585010003000e90801c0b903101c404682d040700300201071b51a001d42c080425503d03085071f80c0c4002d01840700e15105503210701c100400015860540d201e80c0c1b4240e2003641d1040c03801c02d2940800d4424452090b20304d54a665148224080c582007444080d001c0d01400d8080d003110014000010440741c0a80d0409a03003034440c2c613008046030b02e1440325002e507044002c000b41c0c8421241560300c840d07002e0074402800e0350400100700203861f5400f14401d1000e428504d400c01c4003d842d41007032a56580100e800a400c140318407003c1c0701066200072115801882c1c2c03800407858040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 232863812 1250 232862562 232862569
    0xe130804140112020c06010b0a0903140d08010509070c020405060a081e070b042d050a0e04020a090903020a1103070b220e0c07080d0207080c0307200a0e090705 70
    0x319611034414810304220145056070302c403c80003000b111100b41541041303009206242c54100601c101040407030000303100d11040d40210080c000840e040100885054003207005951544d00d415a0880050a070310004119171070f1100e03005000c1c0346c080d80c500c900c040c01907007401300404011b0700031035105400200000c2d64020400100b02c2070110314008107410044005d00c14500320703141e0424046101c09200a00049803c02849104403124510203103400310842c1d2003420560341c58010a4101d00e88001c0807500d078140326155030149200b522074010260741c2e5001141200c00310341000700160003840b5a600131901121402d0100c070001020b50320720903540c24036541c5543c010708034101084001220500b44e102223159010045c01c00c4e66030a00640391401041d205445500e40003041540c0100b02d802100d43c199069515040c1d101501554561440008590700d410400e8102c99501c90f0344200d81c5a40f40066800042d490080d1200e803509050607070004040b00004c2104295100b2400300056a83d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 232865062 1250 232863812 232863817
    0x2030417030703020703020f24101502070815040f03180819030e03060402010507080c120f040905150a2705040303050702070e060306010320100e101103040e1308 71
    0x98490700c005030307a005c0c0c038540a4240548000791600ca43c01c200d045809100c0600c070003400569441c85000034a41c3c0d1000c03072140e003221035008500910051404501c0c480d030000345c0a8251180c2000705c5041203001d49007141c0410301224004c0018110180200000c2d01a4401c1603142200c0008800800e890b007410b03031314000b540c16200c90102183c0820f141450380013603840f80c0005080d809020f9502d05900003800754443e1150003407105000003422030405005100324051a40501e0a143d51a40c030382500308070340e0704a80900421a480d02001c660350412800540d007200d440a46191100340c41c00040403a540b102c0c8482c02481030f0902c2501032035810ba440ba15200f01d10030340b000102802c04580092403c426a00070700030285403c4240440d0396000030380c8604481d4031204105101c21082c40301024201800c03180c5401c0360340c4444940080d6044030101e0080348066407200e0282491050841b80b0294440303881c00076030010001800602100f0b01c1481c4e0061502c0c100510f01d0142d5980d107156175 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 232866312 1250 232865062 232865071
    0x1101050906121f0e01050a1403071e0314011401140307050402160c060807050d360303050c07020d0204150f0902030a0506010507150509120409020c060603070312030203041703 77
    0x910b5943d244901c5150034514140548200c1074811103540c1881e0110700c4001d100d002d01c101c541e00480c405002a9010050340002d88040030f00051511200c0b0396661600069000480320038290045a00c004c1505208070403070703076103161161401ca9181c021201e0b07480c98001c044e00c1d094016240c001c9043c0d200c0e40001d02c80f19441075424000f4404906021903503807000d804c000c0407c18160306110040da07101c2c0946021070000000083c04a281460540b0918400d8150744c1008405290b04e41210a041c003840c40d4690203920f003400390341e89074003010002e84204100254860301c0c0341c1c40c10001d4180396209218041582c03144203c1c1a417148018910b43e40039502c0b0200040c0c0010402078410014090644c003c0c400b07003170450500d24140d51340012a0b036580306080c480750340c400004070b44107002c00156400c00003642c80c3c00e568944500c0e00d00081d52000d001d0541610904010425906000401e0700480b60460300311440603024490480107940090002d0315280062441a141290408002c500a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 232867562 1250 232866312 232866331
    0x30f0f08090c1210021b100203040506040b0a1b050919050a0303051e0304080a0315060903061a09090c040605060901080712020717030103050105070c20030f01020403050c0108010f03110105090612 86
    0x41b03411101107500d005508802c00d5001070050082c0400503500042d50b0741c00990000580310143d4407000602d0040c240781c03103081c00c08110f101801440342c0d00900189584481969100801070140310350001141c000c0c400c55800030034a09080000c40d00c40c002500d580440c1400c00c8000d100d014a014030550001d039000d450000d000102441c140350035100e803520b41c6084110441d1004c0c5440806018246180b001810003501c4551b8420b080604407a15450024010115001c606020305440e03130b1003021070111802030349810380219680c58003000f0340c0c10702d61059483c00055510003504564480c60481c500e03000035024409640020b10004201c14841944140c09480358903504000c0e0a648000e0030030028404440030380000301c4c070000c1c101000091440045081010040d0100e4a00480f40140c901c0a510101e404400c110380420910080038090340c501021381d072201d81e01000703021103100c002c00c481940900c407039031940180b026003000c420080c411414180c14542d81c40c0103800445103c0318 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 232868812 1250 232867562 232867597
    0x10e0a0503040f061107030201050d020706090c081501030228080a0506040317090706030203070c0c29160b190e010501050102011a010e2b030f0f08090c121002 70
    0x18864100f81c00000d10441c03900e0f05080301c110b02c1c903e440c0c05003404081e040110005000443e1403890701180c1c45a0303408402040490050704203a0120107c0d8001c0700d442e401185400d440401c1d0701c402950680741c00401552460304415041d0b42c10ba2051181035410001a410008690209000910b2502c2c020b10103400d65103003901c0c0003810312040d0034290810b8130100c000e01c0101310000800c0030554420342001682d0384c84050041d11082d0325075100828400024002282c52045089007101d03071020940d0f08400c403025890105401e001e40c0c640c440449c0340003030404011a188449240d04a445000401341c0d84007600d00e02001d4401c4030601c0041c80e911280100078030350f824030400c210342180d1604941c80c6200640000c0160290005043c458030207038000c2141001d00e1194000d000f0081e0581c034801550b04c0c43e0141c8aa8084140c0c0e101141c140001d04800c03038016445140f05030a1750000d0251150140100880c07152080ca81c0051481002104541203881e4070040c0100341c814002e02d00d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 232870062 1250 232868812 232868819
    0x1e0f040b090f072c0d0c090204060201060f091806110d0c050702100908150a0e0a12020d050f07030c051e010621030e0607051005010e180a0302070b0a02010e0a050304 73
    0x4c000380a043d058048007415908030000810001c40701d20f601d49021103001c4200f8030241403a00003142d00307401c5404107d20002d80040c401342c0560205040355030f200d03039015000ba0381d0304c0702c0070448401c07500180c101e0726442203000010f1000c2e0b012000181c43e01c8083c6090030b900e403a02c003040303420020b1490041140003583d141540b501c1500e502e41080c1ca45031100701139050607100c0340c4598010000d031442c46203000120b0704c038004c0e80d040058104903885c200e845a801a040415030660905812805030040b0f01c2d14240f0144910100c2e06250b41542e1418a030050666084450000400d02501d1038018508520f585040c03105958901c5090940041012801c1ca0b1500c00480f41840010703401c0142c01001c040040c0d04031160100d60402241c125440d07142c60300b0883e040032111401210b80310b02c0c04002040c0c14424040c1d44e40110842032100d440b55100708066030f9104442e55016003d6072290000b04002011700780217001d0303101640b0003c00c841d070503900003d16040c20018115080d402c082030a1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 232871312 1250 232870062 232870067
    0x6010e010311030708100b01020c03030706061a0f07080702040b1305160201051e04020d050f030a03060801090f08090d0f12021c27030b070e010e1e0f040b090f07 71
    0xd40302c40080340505000307480c0821641d540d2000303035200c0240b5034656003a241207a000b407168400042001d01034a0341e49810780303800c00060120340140206d000340b0704690742c0703045130f00400e68040c05001c0c54000d140506039240c050941d0002d20742268050f4076140041800c0d211130117201540301744542e0101e2142454a680056001e803003040740c0842e031402007040342c0d54120301440407660f00440500c0c84161624004610304000403080075255100d09100c60500d03403030000003800c0980060740c0c10003800e605c502e140303070070780c0d5440078050154540c086400300800e025000034550310310001c0800420401d0759039003411070b0300d45200030741e0510030b10300081c26000d8040c08040d00302c200d0070f4195200e101c080b4101811400314401d401c0c48c054244c40b840e640303400d0701c0300d000c001840e00405040e0103890154002443c515452000f01d0029101d85000141418034038035540e400505001d841000084030014040001c007600c441580c4940c80d00341201558840800190041c01d0040309800c4501d07041d0b030701 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 232872562 1250 232871312 232871333
    0x306030b060d0c0e0703020906030c0403060c0503130b060f0a0305061515030c03040609200a05060a020d031503170d05060303030f011806030c08031e120718030506010e0103 76
    0x2603a000c2c1190340c200c003002580300103040094440e2885080310a0700d589404034024000c00c9042ca800400000074000728242140141086a101d10018410380e40c01241c21129030100740c610b00841c242032241040022a0810010362015010b00560700c009a0074000030b2031110150f1090350a50812810300103401481209400d0b0079070166607020203000c10159a420501c401001d001d0034950100200b0300300b001d00d40207540559004100d66560150ba43d0400180d040701c1100c0c1031151002800004590500001761800a01c03250040c110300700c11103000340c01800090041c0d40624000310008800a840d40840454040402c10754580754011001c2c4031003144c86c081c1403a0700c20303401031007040406a204013084e41074580040049503d58410b00703142c0701400302d0307401c0204250f81e00340002c544028008064202507180c5410b0510080c0c04202070000c0e4420715804004066131000001c00c00d6002c1c20b514040a059540b031080c9c0130756292603a5043c04400c0c0c10209100784018010024000c4041c00c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 232873812 1250 232872562 232872571
    0x30f2509180507051e07080f1804092604050603010b041a0c0303060409020d020306070201020309010c0309171e0406050403030e01050a20010603050703110301050108060c040e0a06090c0306030b 85
    0x100503e091089000c0c2c00ea018416024450070103880041d0b030741c4110038069403a020350064044da143c17424144000000e822100483e484c01c01c1d58048490b070352910340101d1614540180d40100861914080c2e05001480e00d620b4854240003080009000d4035a040114003c042d504004c2e44c455080a030004040f01e201035044a40d8001488841840e801c0441202d03001981220001810865440412450811060065854054101000341054064000b54840c0303a4002c020440400000302c01d4046591901e00944a5008910f600c8140c0c030640e002001440101004584c80e82006104400e0550054100c1400100041020401c00d038200c04440041071007401c0c01400c00c00301000080c001000740410103440307410000003021b2888203500080c0603503000000d80341000e0312814a04104094000164000d620306000001c0c0550085491030040d92280780b028038003454891100e04107240035140c4004165260030000b04c0e00203034882c1c455040c10300d480202380d4604d1414072907a42ea10091 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 232875062 1250 232873812 232873859
    0xc092106100f0915080a14210f180a031113110a0e04020405040e010203180111180a050907020a02040509010c0c0609110316140303040506030f2509 65
    0x31030611150081500590680f1110540080d15000321800ca011441e0a684800340b140220342110040c040d40c60070a0118009407000c480500c0d0b440003000703807c00c1e210032400b26960710620400001a510340f00078048280983c40300700d9070b40d0581c000200480d000d235000300c40c500040241d80044e404c0a100340c10b449042000c040110049190190369944100769002042250044410300305071759550580d0060b1402500070442d501036401c20034000d51094544400088042501d01c02000050042500418083d2401e505100101c8071000020744c482d0a9071368000402040401d403515000b101501c01d070001d500400c031000c2c2c0d0340180411600050014210b5905004e00144940c0d008540c0b0041235900c0100000c1009081c18006c40001c10950415454003a03036082c1c50002c0410f50741101560f22840c56201440488010140c1e030340b049208064100c00180300140010b0102e000c056840052800b030196400c44032003000c86031001c0c60352104007041316200305221304a5084810100d450861 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 232876312 1250 232875062 232875091
    0x3070b2a03030c040909140303010f050a0f080307080d110f030106081806011503090602040f0611030304020d081602040f020c070501020714060c070e0114040b0402070f0b0c092106 79
    0x800c0340f003180784528013945025588448280d001c010b0481d05191801001d90240d90701ea5071158428100c0c01038078858284074011000021543c481d10940142c21640c00324002d40c5040401e0355101000e030005d00903012150307030342d10000c0924900d00c5c0042040c80000031425540398103001028240220190400328200200710030f101d6200c60000c0c145043da42c2040b0004447e008220703044003d00f12446000b4205070021600140c0312928144260070358602d41c544119024001c04038540e24002240d02030340c844141c0c001074010030601c200620050031a141c0c0c41d5002262074000c5401c0e20240140c3c1402e096001801941d0450b06016000290509102400d00c05140405119803000802181e52040c3e600050a0207103050421040c0000c10310300103006c51569503170704841c50311820100e245000354100101d44019140900c200d0f94919800344840504c00025226007046480c02803e0111076002003000b00103556078440c2c00d020701a00c142c400c800500c80c4094031824480044c140d0706104000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 232877562 1250 232876312 232876321
    0x1051006110c1507020a0f05101103090d060207020306100e090a03020307121707020a0b070f0f0e0418080301030611090d03121b0f080603030301060203160203070b2a0303 75
    0x101e0b020505030030481d041201803454a0400300e0078825454001c2d8800320904000448010641043c03044903011510880440011002a1507a0b003100c0300c01c03041500204405002840c043e84004140f5004440041c240055940401e02c3c20f08143e8a520000c0b00d801420040b0000c51140704d64042c86c803001411340791400c0d5030083d6490081d60b800407e01400c041005000a1142d08507112240052521036428109220040c0d00e414402d0001c0e58960034400004001500444c8045442001d0ba51240b90500000314201c90085c15258800d92003915800086401801100c034008024001e01c011992540341d40352a200316001183c215880c003205000761800340e600c0080315058139415040440c5101c031280b0060b00208180104010700d000d4202e40d0000b0075030300c03070005034100c1081d4644400c65140ea00c1015901e0100f4850f00c40141c7c410091030080c02c01c100e014031401ea2000e400c56141d10307210144810b0035004002d42616032910248403510602d10380382d012420f44003060140d851404d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 232878812 1250 232877562 232877597
    0x90303090103050402040b040c110f0109030804110406080627010b06040e0c0c1005090c040506060409020a0905060a030b01080a020301050105041202030c0306071e02070b03010e06120f01051006 85
    0x19020600703051543d110009015904c56410404440c08001c00801c14802c0404014144104456a1042c03c2c8200c4044201340c103c140301d03440301107030141c980048942e91035841250a1090800f071310740242d2200c2c00021860000c11a00740104000a09001b11a600484850303d1903d60a401d0b05243c0c100348000605455a201b21401c0d1401446080c24607551860325110601c1110403042d864442e8120003440b2a0a951286005059810640303400c5070384e031000c1006a99060341c0940e0301c480d0800c010860f001107a03006141c40c0d50581400740800d9510070000e0a542c00215120000c00d850350035945956030312004860b0712480c100d2085095504050008000380100e0080c0303103e49415200000643d83e081000c10302844004085845900c0d000b42c2c0100070384001000d14003000c1e00881454081400440c020047ea0302c100302e440c2c11a860030303c0789482d07084080e01464008030040080d85c0c89000c24480d2400844ca540b001150b00e06000781c0201040c0d5041d0b0281e402c112003140014030b6001d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 232880062 1250 232878812 232878817
    0x11a010201020f0f070507080a050a0b01050603250c0c0b0703020d02070f030f020109081f11070b0402210a0b0106090b030705120c2110080109080a140d06030303050a050606090303 79
    0x4c1a10f046581c43c0c541034a0b00500c0c01c10580c010148030f200e2001c60008020b000074141d461588240101e03e110390703079075080c000c0c580016200007100c81d0541c2c090082c40400b41c0b005220201e00e0740707080707030150f40d058031130b02c08854850704891000040010b215007419010045041c552034036100900d812407032b10042205100082c0002800d83d5000e010305d5055a114030002400303886080c090b12110784074a0b0180303511004030501400c00e0341c20000416042c191107000d43c0da480b03402800c624402d0390f42c0d03400c100289200c2c540041689010510fa10a8014108800340e0300e544101d2600b02554101100503181049603441900301d590f0070410000031b0707544041980c4c0500c40305c4213155074688a40801401034040e09083c00145525000c00380080741c0440c5c45503010752501c48001c4035040c0c44501842c26203074600000381618004000000308644120b43da105009800012503040001c2c40b00d04009840c0c0551050f000aa140d80900144802520546070480301c125803440c6840102c501107904c03030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 232881312 1250 232880062 232880077
    0xb091207121113021c0f0606051e0d02030115080907120b04030e0402030c071103011109100c05010f06060807090302010807110307020d0f2a030f05150108011a010201020f 75
    0x2006070081c1d041e180c54a000007003543d814224103540b1500008541c240d1564805071040502e400c18030940040b031060300c1013078151051503030b17024035080548085d28403171030390030340600d101c104100f141c83c00c42e44003031001c1c0d40602a402101e2a044c00181c20081c400080503002115940200c1c000300204080c200b4202c2c46550f001d2100f149540c2c03242030030769001c1c4a40361110b4000b40000100103a10080400a1020354030985072100683d00c0001498202d6800d41c00c500425501004242c080d803070024407860281507585400710701c090070b40ea1035500b0b660105885030340140e1070320000c1c00400d802c0201554401800c1c5001c20b40240b454000134407902c0e0241c4080140300303d6801c005403a52050003224000c6401400588241b01c4600d8a0500701d804d100c0180d0795015807040580c1d008040c0200c0b00481d81689503016211425038a03030300f1404440c500c08035094421160300d40c4c202e92040403114000d01410300005052050410704154402d2402d0307440f41164810070800c2944000b0320b0958845 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 232882562 1250 232881312 232881323
    0x5030105010e0303090301090b0105040c020705550b0702011e03090b0c130609031a13060504141b0d0605060d170a031a01020a02010f090f0b09120712 66
    0xc540b8400400d043d4803408403165015400c0c076a102e0140301d2004959412903900b550704100103900c2004c1203840d03061600405c0d07072040c58201014900000c050540c03203e40c0d40aa086007160100c08103030448002101d03150b0001c2c5000c108052001d404600303011008007403410f10946004003070f90000b8050a5070a6000100d2050282e003d8540c603c241d01041400e0343c81003414050381041700c0500f0f0301c2c2c0c1249800010842281201142a81c8a0302c11303041100c0c0c0c0f00181c442c1d032002020f044444514000d281420002802d100040072460500030540500e0040c0c2aa03810b071801c0110260415006c01c0c4140c002c0480d81444400d16110744481c1071651380c000100091648410000030114a54420007803c0b03c5689260941e02056010041004200310340342040032483c0c4142748084214030030300c03440c00b58100160030350255009044414080410b882c0100d21039465140d4103446502642121031000001304d02e19a00381403920300030784e00035017850040060618040742e00389442070780c0320300400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 232883812 1250 232882562 232882577
    0x150b0909100b0f12090f0304120302161e080105100504022d0a11060420220e12090f0105070602090402040608070806040504120516020409050d1e0503010501 69
    0xc803080a200310002d0008120100d980b6000d82070303042d9050b04907000c58a1404c1c882800b16800d071400103203036060b1035000006942003a26207241e46888050591040d415400340486d00f021000480388c0c01c00240c68142d28a8040d07000d41006115070320441d410000a580c0740100348060014030089200407550708543c0560354070580d10000a42c0803d0b03010f42d070b0204050804200e091940d0070040d184501342990340d1201c6003642d0712003564841060f54064540407168109030300d00302200c5240004020080c200605c0d02c901260508128a0300c007403040c4072107942e02c5e0320409401c4103001d02201040c0070300b01c0c20308011402d0006024203407a20300301410700c10300140d20010040a60103031034003280010001c40d200c5031348180c054041d000440d148000a04080001200c500e86807003000d0046400001c510401145140250b620380c0c8410428500301c07007003c03424001a6260b01411801a00c14805014140054440640a00f0040e2141480003120120540129a2210540e8119202480c1115 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 232885062 1250 232883812 232883821
    0x703110f13050a03240216020d1103160f090203160503091207050d08130308160203120412030b18160309120c03110c011b0201030e1006030501150b0909 67
    0x506a00e929404140c02c6030400c00000184509040350f007184400c0003a05c0e4500d0f0510001040885c801c0900000d40d142286000c1d5015003810342601c001d0f10b10401c81c44240d12820340010382742c09080d030315981141941202c1440f00c1008201008010449048154154204052180702071042441c0b914100400480040c51584081004100141d01e403544287c0e50401410700c5903c4541003911384000c00c00c000089442103c1c0e4a2a282c8529050364461a881d00c85c070350000d00803411000303603100b1840103018082901e45540c8600d400703644900e98420301c01d1240440501aa205441c00720711070100c60607051902c80c814864030303520030180302940d072920341a200c1c02d800902188801a0042c141108109040b5801120a00c0028000e844103070300ca00207003100340c0d0795018900086000404820201041b031043c690301d10030b5184141070200322182114141c524054111040300310701522340360708000f0300c94203101d000001071014407070031040c81c10500358160030702c900c290700ca01807088000000d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 232886312 1250 232885062 232885087
    0xc08010905280f39091502060906090d0f032004060507030806060c0c1c120801030b0109050c0301120303060b0a051e0301080703080a09030210090e0703110f 69
    0x1480549042d9907154203203001003081c00040c126181100c20f220316145856542d54880d407484920b422040100c20002c0c0c0e011030b131000003940c1899095081c0308040380013007071103110320401c030760300b0f40b40e40d802007410389003c224075460414090180b22198002c40444010f0650007080030200c0d032094203011440e010b58411207d9609943c1061b0002044082004180f6a504c80000d04c009402a610706015480d003008004c000c1c071a90610200eaa48020510303c41070514085034203005401740b203c0d00c014007450311044041a2002c8460001074103480041c002c02000c2b50515002d05070142d01003000d0320306a1609003507440306008200c40c40d003045031510101b5100c0e4201c05c0c00380c0030303041d5001c0c0c4421049030f0140150304441502107103181e2580c544000c505040d03084c0d07412204c9e4a8020980c8a04d19248c4150781e83c455a04142003151344a030102c056215000d1204403807010f650f48000c039a00d40003000300d01310405811401014100062200c5604203481510000e07408080a03a89e10810341111 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 232887562 1250 232886312 232886341
    0x2030c0913022e0e030712020f04050a02040e0a0c120e0307120809010e010e07030303020703260601170405070b03060a0f0e0601030e071a070809060711130c08010905 73
    0x20750240071907040004891000e0a000842402034042441504880344256080002030501030b405d58028481004813091038090496010700142401412200050218041c1c41d400c40c5c035070503c680c0000d0200203c500155500740d00000b400010030100d060000000c1120b4281e0882c0c80510780c989580424218091007212040d503440f4500d400303113135061030014000c03140c100d0b0290203a5203030601810b02d03c401809244038a0001d200074024140c15654190020340285a00ba0100000900c5106240c03469019a802940407000f0b02102441e0a04c0018114240d61040d00f0080503003405000014078006100300640b1030180300e8540320b942c0c1002042070741c0300d264842c1d0001c480103400091f840c00c00084484c00703000280e800f031000d203c0881540360741c2c1500e4401c640d00140c03103020a441c18210302c0302401409109210036450301d551200050400e80105134165010060a000018280f40c0360804014400c547c02e4244141d03486140c015141041c140314082d002620380001070718000d188841c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 232888812 1250 232887562 232887601
    0x30f0309120c05040606020c0d20060a0c0204200d0b130603060501030507080a03020304060f030603120f090f080c012f06040309060e0a050402090102120f0c01150302030c09 76
    0x9440450a04207042c1c1600c9501c00c050180e8985a070104032244040380220070050058084010440103035141d0710800d88200d500362880c4450140f80b050740d50b9036402001d0700e845580d24a003c9141c00e00403c42114401c2203c0140440401e145642c10b440a07400c1e10503030b250300c460004100b1141000b141a412010030304c5c04500b45002e2011040159640c030042c1030302d01035801c550741507440340701950fa25901500080c1c050381c014082046504d20481240781200c40501d00490300d10f6481d52142c00d0107048480c610003242c1007000c0c0c0c0d10182c2d4400381010040440b4404600302c245040d10a60b11440300514140c10443d1100c1890158503420881920302d400c0540c1c031400891700d020f00c0e0758940d9400d8400300c0006245000003c1c110b44900c484407a01c150091400e1203492806080000a50109142c4c5056005080044000420b100d014210b88000040c1842d680c84000c8070260859280040300e01150041403400c0c80581c030300041185032400251858000ca4a4081c04100309070180503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 232890062 1250 232888812 232888829
    0x4110901060f110c090a020c060606030606121003050102071520090418150b1216330513080708070b0310080106140f0405040308040b0a0605090c0702030c060310030f0309 75
    0x34032079080111f9008140000c0700605941c020380f5000c0801c10548025540240e0117081400120103141014990907004202d050581e48030507038a9441900f603030042c45050300c2030303107100344403040007401d81c01b800c201c0a409001202c6a004034041e4108035005141c2c0042c0110f0780c0362110280180c911252030708450b005820000100030100494015102c5000458091030000800c07500300b440000304407408501819100000d5030a041c00c0001c242c04590743c0c454020440740f4407496107046000c4003888000c41d5540d16503174840c4c43c0f03c4e00148200035403100c50284d00c40c1a04026015010900c0001d4901180d04180e40303480d18200c01d0701c0d507000d6401c070100d1946003080015940c990001001d4564400340c0d03402d03159413030300c1d41040110b031000c65024001c1380b01040014006640442540c8d40b00d052180001030b000e44071400304002503401c13a08071041220006d01c4100b980360411040b45a41c404860681c80c5107800c03003081e031046815100080503603400c10107100402d0301410861010f4030041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 232891312 1250 232890062 232890079
    0x20a11030d05090d0c0b070309020d080d0506010801081203011703040b03010609060e150a030506041503050a15110d0c03020f07060b040e03091507020a050d0b04110901060f110c 78
    0x40c1c1d903960040100361120702c400c0c403d00c1c813007040450250004041c1360750821030041c041e1303a075100b0507005885a014100c0c2d015107584902c0000034040405010f16003103200c0e000070185016030001d800804c06030008415548409045120340d0704560842c3e0540e90042c40c840e02202241a0a500e03600a44c1c02501707200d03001100102d00141e000a80b6000c5407020740d50318111320560002e01406035403601c200c6039a003104204030035a40b40a0f400250f0041c202400008004841c5420f00c90362a845030411641030300710807400d205102d461002c061003c684c10030100000d040070340c030401c040e20640003140c0b0341f036850791801005140a0b50581d0b44204246020540e108807600d171200c000d001d00650548141e09e8129904a000800019031768901c501074900500080054520445901318074400c0740d00c00c461183c08116502c0e4035140107a40c5101d04810710341c6043c1807504483c000b0031070440d1406034040000401ca040d40c480d0410340c001695084c50301021040118950130921800303155900441f50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 232892562 1250 232891312 232891327
    0x201030e0309090f150a0303080720070803040e10061b0f0b07080a0c141c0605030a080c1c120903030e010e0d0f0302090d08030c0c010f02031503060601080109020a1103 74
    0x41400c1c05115031080f903060340e174910889081113440011404080c00003801100041c440900648014000c82c0061104425a008409e502458403145811802d40c0d5040840c04201440e60340800c26004081d9940c0400a0782c100f50008001c00e100b030380c040000e00b035001800c0d418030100000095500340c04c00c00803040742c0380102000d00b56103001e440f5a81e52525056040115903ca09022028040d003258414900f15034036145c05d00c070042c404c0034440703016503803071001441b40c0c0c0070030100030854855512252988203404a19050008501009081000d0521030006066000c070451003102100d55000600061600b030840080c40e46054814042d0300e0a40203110000d400078030300340074020740c0d1350354050000e6040045081e4011150281d4200c840019024001031034500a5680301c2c8148141c1420729202840282c00e4414540c0001c007040d50000c1403000c0b0100c3c1030120280008107170010510360503c080000d02000e01441014082d0350b000c1520804a442411103000410589007140d450341c04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 232893812 1250 232892562 232892581
    0x19020409090b060303120711010b040501090603020103060503071a13031a0108010f0e031603021f14070807080a05091608030c01051602070b0904061a0306030c1c0201030e030909 78
    0x1904029100c2c0c86003500041c080303140000032101c041c09403048050070794995032000da5415403034281355045552190b080c0c200702c1d02c4070310480c3c1c002e1942490100c0d00c00d155000140c221078094200b40c3c026048000309100420314600c4408030141c030f0111165a4280465030f800e0f100d0210b8100408902114948540b148241440d40b81a00c074064001c0190840b00c003c20000c03928402102102c1e500140059040042c500300c00d2184035000c3c1c016142400d03444050400007200c0004500b0103183c4e600c01d0f003440d4081e0500020f52020207420301000600300110054030008000700203a04094440700051601407051200130134100340052129151074a59000e141c894004000007071240d840e10300010090380b0501040d0768858070319006070805a007040320148881d031145c5000c2d50055201c3c0f500003080a1005441e8182c0400218065160b0401c00d04250a0648004070700388a859060448450724088140c0003049a0b4242000210780e1440840e1904502402c505668041d03603c008010107000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 232895062 1250 232893812 232893821
    0x12010b03040b0a020a090308090a0905070203030901060605072a2106150f030b0705040e041505100515070302150708060102061b0316030f0606090f09060b070b19020409 74
    0x1407045206160a030f03910400003040740a00701c0000300040e4084c40c00c102103a144c2004180d0303601c000d0116a11581c0343d841c404183d540a84003200180d100001300090540207119401c00f402281c500306181011760b886404c6034160040c02e1110f02e5450400001c0500a8044014001e0290305600c1401002000d4030301a0840301342000e441060404903662800c601d03201c914016184110f02d139161060640c1c5480031812001800b01090203410040400c100c01c420f5003240c41544142035105612000070068030a480c0041c1404010328158401403045507a111a0302140d143c20300c081c1c640300d0b0b10f00d0400324a8802c0700820300900d0718144080c010141d9108811600c00c40c401c4e001c6481c076865006100ba560b8401e0000b4030a51003092010843e84070b010303007203a1611000f51401142200c013801c20402210000e034002000f003850804204884092003001070010281404100b10171440c0480f2441d540c400d1600040074581d031500043c07050840191000c00d00c5619031400c6403a07a884444a50003031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 232896312 1250 232895062 232895071
    0x30501060e0901081b0d05010905060115050a0c03050904060b030f010e1308030403261303080a06050d0f0816080414040203150409140d05090a080309090408030c12010b03 75
    0x141400c1159003142c180484200e0486460078000d01c082c9034680044038030703150102a000e40c0b01c00b00c80c90ba4808a0030900440b040c10340104041c00c007035403414040e400b04a5103010b85409003d030a0001809050304103c29618168050800070740d9001c3c407000040060016400803042c1c60404400c1c004225100e21200741a503030000320724141074595004080c248680160000c2110408000240000380320f210a110040c04086514410601e03100003d84401411a21000c01c00600c002c00c05c185039104444c42e1708106400c0f810480701c1d04280124044507035203d40a0500030401082604201c0040c088a03c0032654450010002d54903190050203a485840752106050503580141c20030314051085a00440d18400200c900d1002581448041e006490041d1070f03400c00d51036050100c0d0000c0c0000d8134946030725515030f5600d0032182e0820000c0e00d0580c105021541c002e000d5080c10b0b40b03960b94401c0c0c20076041034840e504ca5803414040010f0307200b80101c4088603c0000000114002180040c40c0203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 232897562 1250 232896312 232896317
    0x60605070606060e1003020f091c050738130807090f061d0402010905040f06030b16090b0f0702130519090503091210020304050a030f03020403080301050609030a050d03050106 77
    0x1542d4802c0304407130f46454450b4466100c07800016160040e4001c0d030041000b00c45080819007841100000240380c034401080900114000380381c140200401840010301410410580c40c21501201506203640105074500703950361002032a050341754035502c2c025120401d1410701c040c6001a1514440307600c40301c4a10448031420300f031103c4030244240e14001d49080d02c0681380c6841c0c001540d805190713180400500700b6818890328800c0400d080c1c1382c901800b0340150310004007003881031940c500300b04640001404202c18045100035110019801903c46040b0b40c0303010462912001c00391015503a42c031036000029480403016a003000307002410b4000a02c00c240e9200058500004c0ca8540780959114120080c0f45030010001441c0c245070500c0010148900001220700411100c0480c608076403080c1c80954403a440300700321004055001070b07904016552352409500f01071840d0b45a2095001c1806024819400031881040c25101086006041504582110804100780e60083d0041c5003c0c003a5000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 232898812 1250 232897562 232897571
    0x1002030a0f0206090606040c0c15051603020c1207051612031d010e1201020403020d080306040e031303061107050303070f0806040c08010905062e020c010c051902060d0606050706 78
    0xa8035001160040c0301340d00041c0a00b074150340d0001004010b040741d0006005100c00510020301182c010b07e0207607002000498000f65a04040e00e4400f0911100a0001e08040c01007216505590380452000c4c0c0321080102050740715501450318504010b0a52115180844d00327484c0050b02010003190700240c540030351550341a24842e841d040710b04544510007076020420141140e4014106640b040741c00d50752100006082c15120360000362200b8500d1026901050301009000251a261051810740314a02c4004c52605242100115882d800c51002a04a940d18018540340040e00030407038101c41d0303120081da584c9160550020b0111083c2c02201800280c8100009040341454450f03190381400c0707625541151380c80e1a501c180940310080095402404040e40507178500d401320f9100d180c46e011012060b88401c2d6600b0000c2c50121003c52660420107071007241c1000c41c00c00f20700c0382c095000e000304110401e8241d0011800b684580e00741254043d10b402c4000076010b48c0322001e0030752544a60300501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 232900062 1250 232898812 232898837
    0x605041103061003110f090915011b0501021e030901060e01082e110c010f14010e04050a05030a3524090f0118060b0f07050102091002030a 61
    0x200311140d10603034000c10301040022900300e160205212140c1100c6140201d5842000308508400b40c21546218002c40c5003c0f6159880b46011080c40d076005050602407091110340000007000c82c4040c00c5802889050042c4007001c0c848290111002800c3d400c0010700003455242c04600241c0c01162860444e5280030000f285600081d000c0324100c0b0311001c000e1110020408605c42c0688200558001491a8000d0202c0c242d50500601d0202c2e040c0c01d0740f5949600742c000c0110700b5140800c000819451070140f03465010310141c501541514040c2c880c03500c2940c2e030303031901368a0701b03024a60191641c440440c08058032030f07000503c801c03030209640c83c141c080101344c940044442c04e405440e000c120020030008000d410ec58446d0903c40791501421010001d0020204610410550b0181c200c04c04440041c8000305500c810f2403031070482041c2c1009801c0c545607080609001c0c0441c205c124010008400c014048250152482e0b03240060890000880c40140a55203502042c1004045614a000b05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 232901312 1250 232900062 232900069
    0xa1e1203120b040b030c280608040b15220b040501090c0e06071a0423010b040b0d020a05040506062503030c08070c02101205070207061803020d02040e1e0d030605 71
    0x2139a000b10203001070072026203c3c03003001012030340358040300c0f18115070b418100540020000080d008000c1521014082c0c10141272460292900909480080a0210388190a61a04503003143e1407002c070450382c4802c2c040c0220440151481104d82d03a8000e0070540045480354956100305c030341503407984034220f4166101090046a004010f0040c200c4c0c08244000072170a0030a03140958071a100e040b94400c0900c1e00890b140051b10352940320001030303554030000d05041c10980314130380114508803272007031600300701303a00280180744207014050046c0c0d00c0d04042001d684988080d030710244110100c1119441e40d441000044203031680040c0e0000e03080c100910b06a0f8000c440b4140906480d0359a450050500d40070b01030f400242010420410861000d201da20600501c6454001d80a0381c3c0078007055450814001e003d07a03007402540d400c02600c00c000304010703075410001e0002d00754143e902081d1038200c0e5550300e0405900104403901140020407211f0820310104401c403210070161403c11116449d036052 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 232902562 1250 232901312 232901321
    0x2e020c0418080d020a0207120b0a1107080d0e070f120c060503060d030e01180e0412020105090c120f061003030809010207020d030305060d050d050d050108010203060a1e1203120b04 79
    0x1d0714070302c010864800c2c88078032074006204400050040724101c1b40d6494031890075100401c02034400c1e42c4410180000080203010b0007000820b003541080c00c1034400d07241c000240c45201d01c1e10318000d5440c030031040c0003942888654010400b042003240110355034001020340c080907074400c640541c20b101000c1552402030040d0313400f61402400f0031540d40c1d0307103039416a0b00c4072605801031305002009900800720100307a40036401500c11030103040c8883c1003500e00300c00754404110310107066905000400c5800c110015420b1901001100c1c6c10300900c5a102c502da050003403000c0b0080250140a04200c00b800f0006038010440c1c1c40703941e030112a0703580c0c3c003840c500300d02900a00a50198110072940c0c0441e210703410450700030344003d21203030041003641e032614608010b051704903002c1040810740701e00000d03151041d6801003403914003d500e10714090000030a0007005005400c000c0494061061122540e803400c64003030580b0988001145955040103860151003840400483c1d0a000b0303075a03030a0820703008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 232903812 1250 232902562 232902611
    0x70f02010b0916050d15180c030e0c151902010e0607030c081306020c16050f040608060103030f05070b070305180d1418040f05040b0106080702030304022e020c04 71
    0x403c49810b84100d0300c1103685a1210200110035038541007030144460880c0d0740d1100510070702d0041c101407050301d03030040103644042c440c10050614085e4641170946000c50f2140c200300c2d0843d416140794501c184050428024100705c0e00103450509200da411079015404600c480d4290002c5036903d944040c0104d06a8428040c103a0002d03120001141c0310104d0400700c1550745124080c0581041000e031412031421424143d070900600002d1000c02090601004104a00409640034400c4508056415603558010711000b010000eaa02c031901046100c0c03010741703541c0c1d98425000139480c108080c000313003c0c03c401e8800380300c0245508001c84103000000b540c1580400951200d0f551101440ea182c420303a08490200c90291f03605030340c80c03121a81c4621558000c50141c4070009064200750400b425189016040442404500e5060001e81a0000296907000760304032440d01d03c0d850160280c290784001b24080c4031001111115000025801080000c3d48050950b01040f0100444944506024403500d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 232905062 1250 232903812 232903831
    0x131103070b0712090312080f071805270106090e0f16080a0e0f0109060e03030402090114011206080a0b0903130b0c030f07081c020a0f030507090509070f02010b09 71
    0x201c40d900103807444100b02e41c520224286131800c01e0380c944410042030240001030000526540402500b0b030f462501850700f04038103181c03008001c519502e5100354000300d800740c2846498a01010115524061107000d07070801454059481545c0d5001c001d49110101d0080720f803070800007000146502c0c52000780070b129500c01c80041660700d407282c40a0310480d201030600603441e030b280c2e42e44a0560104104100c949158040001340381191030400c101110040120000541c004000b4000580e9451201506464004054241d41f502100050703824810254101104a051030000285504045858000103005460b90956590b0710035005840c2d204001d03c3e5074540d800b919040c03004ea026074020b80129112030381203170b14241c101c440d203142035000700f01d04603800b00e8001204d501d411004000d40d100100340703880c158101103012a01a01804281e02003000f010740d40d00010b24030354803403c4500010240948881407e0400020041a09080c0c3c103416000d582410000c0704103080c04090640305d50b407480c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 232906312 1250 232905062 232905067
    0x607020d0e0a09090c030501060b0c0708070302090f0a150b09010806030705150d02041e1518030f02030337020f0312040c08030d020706050606120a020307050f03131103070b 76
    0x242c043d40040c240601e0941e078110340071102200040d802d00c140d00c00b4000003415551101401c04100345042015040640a500b04080400c010b03121180030308c1d0003407a0f2078144000d0360b40d401d0722500140401c0480f0140255100c4001034003c9540006204100007070740d40b02011340d1107409140d503034a000d22031a500402943c48034802582d150001c5d003444581d40d82c3c05403030720f43d8440d00403003d40c2c5068112060380005060030810301415064840825009040c1801207240c806003906c0004410300c000761180900c10f0034841159014000c0311101075110805020751200010007110043e0440030f161200550303002401403031400020208a00b00f06030009500c0c01000d01d040d031003140d901070022191011800d02c0070821940510260903080304002005842d0790b83d1f4185107095072800740c80706001e204c00b0044061140c0400344080d500400d40040560380c0c1d10b03034140c02c444a02c42c2c0203180103000e001200b03000038425003034058180f150155260b8085d1007440820140c17158003e20400302d02e034004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 232907562 1250 232906312 232906319
    0x50415090b0609030a050f15011401120b0402120415151505071406060a0e0c07020d140307030306050f0405060108040308041a01030614180a0b0406060302120607020d0e0a 75
    0x181c1c1064101d2070001d80418100a0180302181c40c062804104036880e030400741e003690250004014021007900c203148420318035490b240300f600d1a4141c070701355141004800c4991039100062500070064004001d007045503180a4000c86203080c107c1a0750403542c24540b10907140c141032107805590300a0305a66080e01c0050315010a607201e015501544a090080074000d0102180c0300b41a03004a501002000e0101c52502c9030400c039500c016030304551701c5941018144080c8800e100305a4a0203179040e0b4034003a050310942401c540220f034203130b0051070600c00010352004040c1c3c160803481c202c500a503540000760001034104130680c2d0040301d030503001070420710000b00443e01c0380c6002074201c1d0080c4c201e00d2400041000a04588000740c105440c090348902d168600402400480c1c0d89c406e02c240501003541038030001c003648032500854080c00b81401a400325040c00a00e1740040000d5500401102c007040e8000e0040f0f80701c8104907890005401401a01416540500a880c07140c030401820404203506 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 232908812 1250 232907562 232907579
    0x603060b1804060e13060f02160b06011e0c020102010b06070203030a05032517060907120f0204080106090b030d0807090302040903020f0d081012080301033c0309050415 74
    0x71201459000b51120b00000d480110701c628580a400c01c1d421181c1d62a03a1030030034405643e80001d40008942c8100301c55803c0012800e4160b0303880d513000080a215486450040700d0907105525080b041070040f101c200d5a05070820100b9003418403e0f00240216408402044081d004011010350960410402103c41521a40080d6032050440c95a000d6041450301d50580d000f40c1c6c0c20000d030200310302d02017a0b0249411110300c540d0240041f100d0078060301d01100002c0c4001503540801c001ba80d00c032000c1c2e524070006038040e078001e060707004020820ba03aa506c080201074601b11541c0c038000d0107450f2a441c0400d2051048611401580d15400403907880e550910004150b484010b07011401005c0c1500012134040c800030040406e11758503181c40742401c441d00261900c02d50700488600360680060f9002504220603a41165040340c1240301100e204d034038510001d810600d802910034402e00c44203041404604481c58800c1c0030341c0c4c0362001a42c40300144800c449100101050301c8001d650204400c44 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 232910062 1250 232908812 232908847
    0x70207063609050c0306090c09030c090a0b04241d06010f050d02070f0b0601030e0a080304030324090b01090b09042016050c01080408030a0902010509120f06010603060b 74
    0x7a010030040303030510340c1d5820a4003181c078141c54000c0610000414007446103006d203151074001c001c00765114a03101e40480000c0d43c5a01c942c0c0040d0156611100250a100d00799100580703580c0d010b0024010202101e840c10390040800200032400c50f4000c0d80403909002c1c8001001540b00e41080e505e01d00d403070303803401521602005138950307080160800c68a05c130030449001414a0700d01c10032080c50031003003520300019040b60040c0007904040c030307110507038020b150002074120541b40c001018559944850400f140540101d1443c0c1582494410718681c5072010449040101e4418040c20403100b4201001150314000600c0f8002c0410410f21442070185055802820880031005101c13002c03d8000f040804190041810341204944010340142400ba040c4944201c4c6a400d02e070981c2c10f450f0590303910701075010107450319400c01d980d0744802d011a400784d812288042801011038500c5c9504580e049e03554100b5031450308981c01600000507040d4001d0003224241e98240800742d080200c00c1c0d500e2900721 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 232911312 1250 232910062 232910147
    0x509180a120503041104020309030a050c15090a05060906010e0604020d060f06120e03121f09050c1b060408181903050105161107170a05060f07020706 66
    0xd00900e00e084000415034000e10380c4103025038440d5a101c1c03420703051914091300380d02c02560042d8010401c0000c2c80758080201c45008465041540e100c21250900c00d02d0b080040d00314102141521050040b825030000b801d40446120350212403d03541d0701103407291a00020720900c0d980417007010100700381e854603402418000606100014060381e40d001e1440c1c0c402210341c0501c0101c0d900c1801400340002a016248007403444d00c00071454000142900551100c00411110405e862400d480c5144624644924000d1600117002d201c20300b04030300011401d42c0066080200c4004a000065405801017140d500c101e8011015509000812008a000281410116a10102003004866002099080f00700914004c2000050602d001759a0260040c48030001409008007a0b4840c003000d08000780080550703002e240002c24011a14400b0362500020840081c100c1c003c0b8801c001030580d884030614403030009035088030705e02ea640314400e60703420b650001c0c5507885400031109220414407038020407851 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 232912562 1250 232911312 232911361
    0x4080c090c12040b0712050c04090216080310140907080f1e0f04050705190501050d09060921050c1b15030106050d0b0109081009080c0a0308010503010e03040509 71
    0x2004440070034042c0408040720225804006081032210b4164020181c1c54008109441000b00f400e202100400c64040c0b03108402c1d0182d000211099078400c42602a1a03403070b4000800360b00c0c0c2c284900218100030f028041c4103100140c14a44440314035084410703a000f590140c954034140c1e26001070900c90510010000c600039040d805080e40d84210f8440858850703617401310055528105807402c107080440f544c0c4158403c052a52407804d41000601c00c0e80f0450700309003040303642c54840c9103508028168200d000383c2207038a026161001d00c200480007070845c8034202d00e41d00c0c8081c0b10700402d55450240b0001a0810b40c0302d101c406002c1030410350300f06002000100000001020a4440c68269201340c0000c4009000883e404104070510b0040d445003610034200164428105038405903150401e042650960340c550518101740201542240d91141900301560f40421243c24045d08000080c45402e010358a000303032000c44880080306136015902d0040a01841d500c4903440b452100c04000e81c820039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 232913669 1107 232912562 232912567
    0xe0f070305011e051612181b090c090e100e0705040f08030304021f27060801210305030a0f1401140108040c0b0a03060b04060206180304080c090c 64
    0x2461752645085280c01c2030383c1e66408040d04e01034583c01004100b903884101440194140b204008440f14612180c0d076980c0d1015804860030b91240030001020a00c007880003021240e0920b07046501701386041e084a8a6404650905900b81c0e15100441c0c1d00040801c11031064030314020003040321201460561802d500804c8150440300c9056021041c1103c080840500030070820171100c2e0b90300c03005111200304400f0f520700034291b0700a030804104141c00000d802e1b5141e1890035000c0c025030882c0b154601359035a0546d2280c102800800c20701e615040b1060040f102842072002c1ca2005141402d40341d490500364428a5441041c003a041141550800c004a0b0241c0c0106048940a80c0c859695251244045005000540000c0d4011000003000640d850340021035038043e001050403160f510812a0809960340728070310820328a030b04500100e400515003a0410b5034041001e9032201d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 232733812 232913669 := by
  have h0 := BRFrame.cov_init 232733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 232733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 232733812 ≤ n) (h2 : n < 232913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
