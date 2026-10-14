-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2896
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:03:40.761151+00:00
-- url     : https://prove2.me/submissions/e6a9e8fc-d335-4b00-a2bf-b7445af6df18

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 520683453 ≤ n < 520863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 520684703 1250 520683453 520683461
    0xc120515010e12030708070609050714031b03030d0c1209030e040e011407050a2102031b04120b1506120114042a0c17090103180b0402011805090109050109 68
    0x868102c0d003c08480060084281e10780c420020010075015000601504001155000080c1e07250013008070f03840342d038854456416885002c28001d00ca40304407440d0500d1a118038400c40f0750798802a005d907052183c1c10302c03400060480300d1850010302014401008095a4a2140701101c40c0a079503051510000c200501003120608407080f0042c0e410400c4419041c00801c1b030482e00180036280c802d60303810f05280221201001c03841050b2101d51858044046103507103401031805000035824008003201018000c1403d8405c0e44254a1001e0700102c200000c180794440c6603034005d4242c0a000e9902e90301d40005040c1d030f07106c01d00d000c8078031110400500c04c3c24206000021480d0054804010842c51409540c0003040110040b0203000c4443c40040e445034440e04280c04602e034400d222148007401c2d00a0111141c01005146002034681001d804c08003d443c3c8035403000035044401c40c0c500381c0b40ca4004586c4003101046803540322600303000000d1035844800700c081c0204410718002a90354100a0803100351 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 520685953 1250 520684703 520684727
    0x80315010905030c101103120f0a140103030906030c02010e0607020102120108150c070204021b0d020d18030b1f0801020901080c070b010501030203090a020d051507090e01090c12051501 81
    0x3e50f02c02c4030450b102e5100c0c48002c0a400340c0506110300c8030004034840382e04d588100000c005220326494203101790702d0300a003041030180d94450f0041c0039101e10320401c1c070202502444060005206070710f040080318000d5104c2a0710114610001c50300522145c0520701d40441a00d40d800141c1d07001400110b07420428030071902402550014101c00c00242e40c001c40c288501134240c03500408001030650440d07035180e0447d0000d9600c045100420414420803e4407100640d01540140c0200400e12021910072565140c2541c1515115103045045443d002106000180a5070f00c80b4016160342e00c520f1414241c100c001d0525000140e030300c00200000400c1100041e2403040001c009202c0c5030001002c5459260540b0000e20380143c490781c43c00f450301e1800c0542440030390000c13407804c818404e200001c154402c40f0203000d000e41c07030141c484100442c0c503800d0b240308060713000b290080181b09800c1c6075040042101c919241802810504501c807604aa81c1601c4080d1944d000100210403940c2203507518400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 520687203 1250 520685953 520685959
    0x201110f0904111c060f170a14070f0b03040c060e010f0c050c040906060e2811040b03011706060301022b11070b090105130f0308090109080315010905 66
    0x8114600c0508405409040076491165031114960b0340403c070b041d01a1480c1c1c50348030848000c0c00d940b400301c0f18014207807030180307a02000031044046640c51b409a003590300da00030b5030000c1c40c280e1169191000203000500d4060b015000d01c0704000780780203490104001805400ea1280c0c1c3d40c0c14145405401c0014070390013041403291800741200e542e80c00402140c800c2095050070b1005d10001c1c03508030704128a0480007580a8540382e07145003030100f41d500240039601c41c0619021709403141d16801c80c0702c01010042d00100c854440540c4040c050a0304103030750714038004109a003800d413500554080e81c2c00c01d0f0413040e090314004000142d061410040342e900090190002c510305010b1007421880a06a40815440d00d9002142d210095010740c7c042c00c841040489690b80360003203480e10b441080b00680343d000c107560070080851801c44c1c81105000056911040e20412950996415120790f00014022a415562a07888001050180c0000c6115010350140850314503111300015200184581110780 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 520688453 1250 520687203 520687207
    0x3080c010507020c061911010c17010503010506091602010b0d0b04060507140d0e030c010f05010e011703071e020901060e0a0603050f011202060d02070638060a180e07020111 76
    0x4103446590440d051a00a406003180c41464071b44180d0f00c030403041d5036007c0c1562a246448140f02d0348000c0488440240c8001c0c407030030740d9881040500fa04c6050358501d0f4009801d002003000200f4020009080300401c2c0004606951000c0004500416a41050340c6a5060a0801003045842e22030303260711401d01c0c202042e0410381c2c0004080d180c05800b1681c02c100c3d07a034040b40740c43c549040060303900a6002c01d00030700400110b21128000791030280707e5181c0501c40d84001107000320f410b052000801c04424001c40c03c124440e00c8000100b1030380e10f5515040818084280056121078403200d02808094450040029007081800358103405548040c04040c07070038043c04096250281d603541140c00201c4a20002c0ca081d000090091103040074100442c1d2000a0000c104803180c0c00913802051348560303d084100ca5041007844800c81d80c410f00655540300d6840c11200d280020140141d5a158503022050414124030600c480340e1305e8019000042481c2c0420180944c2402005000c50aa8040c1c0f4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 520689703 1250 520688453 520688473
    0x20a0905070c0818060412030305010e0c180f0904060e07080a0507030f1a01080105060906150a0311130806060f06160b060d0b150f1f08060d02090103080c01050702 72
    0x10041e0b610358000510f01c9000184000c0c0d403810115900032507a2000700100e960715642e007480303641c0e420002c07001c0340440e09003400094a200d5903401c0c20300c1000003501552a00c81040384c03005840c408164501e91200c54036001009544031814458440da1082600180081103170b2012440c000e010303408281150300024031200050f00109895048a61241c524032481c01c031460310111013030403400070f8a28902e12030300000c0c5404d415008240030711401d8480d2400d40c2c4428041c0070002d0862800c0492000041240311807152181c0e102031001c040302641e80f41019644840640780681507440317040180d01c4241400303407904e03001000000c00d0208070f6540b0314002c0e04401f51015280103900180c07c2e004010000750032522001c000611599021050740c0f031901e07040411841c2d02c0840d075941c0340903c002c4509140c40307041440042c4601d04280144900304021940f0441c1d44080040549412030059103031003005803a0b0214240c003943c4103040040d1103000e071380096402c44000418040031540055480 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 520690953 1250 520689703 520689707
    0x308040f171b150118020d0b030303070221031b0a031d0102120f090c1c0c0e011503050106080a1104030602070309051201021c02032212020f071a161a04020a090507 72
    0x2a005048517500503848001035220700c8028860000020b826000000401860303d60215504884400180c02d445039189000c9820882d40003c42c1c400011010444003121840600c03000382c001040c0c90700e00403900349412915290358041141090340a070b0340215054610b02d00c040007441d44403040691036070703031403034186c0321a640d41855aa1b03003405068021a0181c100005002c0900400c0e0805402c469141d551403022a50503402d01c940314150b038414203040c62040c071901030309040710102d580d0f04d116910b90b58203d20090110365880030a0381410000000064041c0c005400504d01030b40350040054501030520201d81004000c0381060792042101455491000e040c011341c50000c00c0f001078481d074078402801c003203001c0289028900020021000100004000781480d06646a0700340c0c3c40d00e40200c07000c0e0740c0ea03d58501940c090140030382002a09400704030050f20f000fa8030090700c410442000e4540342e05140c036440f02003440303181d46001c001c00d5084c401c9101c4000c0c0400308081040d40b80100b00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 520692203 1250 520690953 520690979
    0x10509100c05070314061006051602090712050c0301050a0f030f06050402060d020721030204120b0603120c0708160501020d0e030106050a120515040308040f171b1501 73
    0x11010510541c09859030038400d00b00030150103154801e82541c00d06040d4840340e84e0b01d001c2110003916111070344d400411098459801c0d5842c04803412410440c0102c194200b02d0a21310003050b0804218643c0d0004086103903034040c00e40104801580d250742c0f5418101172001c10358075034001006c1c4111285c0c00b00b0002e80356070304140e00107401000001d00c41d02c851001400c1841800c08070440303603001203061030070301568142c41c0032031a4035060039035024100300310b080d8103074059031184030001c141c0c1f00761004c00304114100e40c0f94000030003004e0314500c1890112100880e0006245c00f46643c1c030800c0d040c0321020b801c010f0840034880082420f8006c0c1d28000c0006d640c3d019210117503003000310b145048102c5071003d41107a009841c0061052074010307225040a071340b180e84604192410b10030248895402e41c0318500980c0980c0e010360328513015030340d40d40316240e0304400a0000c8980c8010183c041c101712581002411640c1141d2003040e0300020710007007061030141c2c0b11140200c6d15261000400481043c03040c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 520693453 1250 520692203 520692229
    0x5010b010206070f23072405151302090d0c0e090106030c06030b011106090d03060f030201080c07030203070b18060a060b180f030703080403020907020f0d1b050708010218010509 78
    0x1409817441c07a10290b01e655152481107408040c01d10200c1d200c0200704031950b015082640c0401982c01c0060900080010344200391206e24580304186040c0c0e4103030401a0b028402441c0784c030f00142c6000010804264030f4109160240c460b91b25441003400a1a104265186c000c1284c9000f03000041c25515a40c2d03452503144110424181d562100d04c4869000d042e0380346040e02ca20050702d0540c9403500d211520394903103102150029203805004101001001100802d507a01179580c03400603600c03403010401951103148260154401032142000045040540d07502c41c07100050032100707000209507480d11f0301a0140000780c0312410080b00340000407005054540001e05020800414419140418203110a00c003991380c0500030004040240842d9034024000c03079200b60390504032982e52140880e121180051a21002e1b00701c5103d15404500c11a5220440715510302081ca445140359580d80c541442c940c0071001c2650086134001c000d9249400b0400032040330308040d407400800da40080c480b0b510000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 520694703 1250 520693453 520693457
    0xf070905060a0e06010c060c18120506060607170309030a080618060f04020423010f080108071e05041e050a060506160c0b03040303380d050c04110705010b010206070f 73
    0xc0005203191b0b10039030f442040b1540028042140494172a002051103007400d0448550f10715a4500003041c0101c0e100c01c5040341c0c3c002c400380c40c09494040030400140e00c01d41042d40c0c20390702100c01c0100ca014000045019189010040d03a071407401d120003500448004060034401c014040c1010940318600240560002c0101e600100002600000400900564002e0804000c07900034065410408dd40045020402600d62004030001000d040f01c15890902901550f6000004204120544c0b441e1000385918070750780d048403094580d80494211896611981d4008400f180300e0b018072400380c410f05400100e156400d11403241002c000c5465849011007000103648440122424400002407117405843d0200540350307241854200100a880b0605c0b1001c0c264045000300c003d045c1081c8010b00e40c1b442d0400300d10300640079060070020900e980220540759400b03480740100c10742d50390f03204200200d0915502036440300d40d6130819500712078446080a0640d88a1403d0101240e00038949606e0030310b1074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 520695953 1250 520694703 520694729
    0xe060f07020f130c030603050c0301051612060314060402010801050a0f050910030b070513060201150315151d0f0702061305010b0604260c1e0d0803090f070905060a 72
    0x103070003061501d550f0031068401140750402c001c485951540281c01100d0241044945150a80c41058200c50302500d644860806250202d0f60301800382595082240003414001030443d60b0b03846640004a1514103448180c0040c1d0421085680101d00300d0301405042c1d82c1005001c0c104480d5990860f040e01805204e190344400017182c11525065a10186901429040c0503080595020307165401c44501400040b90b2080041509441445180c142140d56840320b0121451600c444045800003245a4151602c2d004a14691205015800000c1008001451071401e4000300340c060b000c0c01420410450074074000340100390754001021900180841d0000c01c03c03180500e0310038014004800c0094000720046030010b0000071a142046000c1001c0c980300401e4051030604989070500206615409203030110300704080b0445e0f000c01c2c40b03081e00c05400c0c100d601c4c807135480d04a00e82c0c0013226a103074507521401c8005854401440408010210645d0034003180c200000000c007080700b1405100c00001e66 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 520697203 1250 520695953 520695979
    0x10509070302100c112e0f020d08041a010e070f082a0705100b010f0c0c06180e010803040303090b1c0504062a0e0a050109030818030304080d0e060f0702 67
    0x4060014213600c1005000c1944031030014071816220800901b900420700c2901c005001d440d02031040714030b01a100e0703400741c6104903000006035110721010300203482a000f01d03d00b6400c69440c42001601910750103180b0b44491800c800024051072101caa241c04000404040c0036111282c415100501500c3c55080643c0c140426a070350518060004044c1c401d1041019200394000c3d1a4019900342e40282e03a594402480c03c4000d0b1060346204000070003240e000c5908220180c0b08218072008000850300340380500340e45036480c420050302a0486809508009020010190002c1c0c0c1203004001903840282865100046001c0b80c5288041000729036840707038001010081281d00c03d9080621195060340400006143c051850401c0b0100c40041214048a2545407401c0007140086a00594540614509642c0e42000d00d401c01c98905003501a10050740c00142d40c00c4c0b02400c060040c0348014100c1e4a40c002d0010701815880e0303801805640100308007610205003000300e03010943c055401c101d84c442 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 520698453 1250 520697203 520697213
    0x60314151212030f0c03280204120b010503100606081303090f120b0a110d0b0f0a03120e0405012d0f08100b04271103010c080108010509070302100c 65
    0x8080580041d00703000e61440080c48416a0b80618000c00c1a03d88a044580c1c608841c60028403082c0d07115401140d0f0308100318050005c10b41c81101c02006160092705041e5100026203816081c181c1c1182c1881400005101506003080b4015407510081e5050003658513205026114800103004038030f030b116458600c0e106140c01040040c0c01099000441e00c261035950f80c809044604810080740c07448035400101c0c8040c5064000d200c0b0442070300d0140c0d1310340300b002c04035030300100700b05004950081c0c6d10406403d0305c2d959540812000318040c0d10755032201c10307a0003401440d440f240020548524649001800700784107928400407078020000c1c40da024410710030140c201442c0d0a40c0701d541c0c90480c50720003180d9100003080030450244e03020400c1c80f0320380c0184100b109550449202d40c0800c0d203050b0030103010700c0f103480c0c8102d40d6a024010243d00102c00d84086400d6552421a40010440500c010040f80509124090344075410b0300240c48102d0540d1300007004035040c115078030104190000400f041c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 520699703 1250 520698453 520698469
    0x4050a0501060e190b0f07111504140a030204060e061003050415021c092d0213110c12030f131709040609061205010606090e01030b0703110d051006031415 68
    0x5940d6600a07101c582035401046d465005610481d42540d5800300f49000781000031a4103c0c0c090880045410705040c02c3c9114021812a07000e1544619030182c00009612907226400103007400d80c2d4280490303c1d00c0014880d034014880c030403008152411007040045580c040b40702c8159905104056520070b559502c0c40d041d40100201010883e01e40101007082080111003840c424400700c440c0180a0380901e80308108a40d9aa4042d4001030002200707020903a040d4841c822510001040e9802d142c122400689050340c64441c040301000000140072a1034070b91032505621008000069024890ba032b642d600a2135070b0010014900b45010850720221360b00c9400000c0a42103c0342c2c20003034076a640320314403940c0300012801d50302c0354a80200843e800d4403910408050f100012101041039103566108811104014504002c065841005c030082c8502d1b40000c2c44407400007035010445080410044e00e07103018590100d42418500035544203007040d042d028a07809020414001512076482022410304 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 520700953 1250 520699703 520699709
    0x102030a1107030813031e080406050c12061011030313020a17100f0612060f0f0209060403030c240b100305130b0408090306190e0a021818071404050a0501060e19 71
    0x34881f050b8007428465809043d0a00c00c50103007809005a03142e40c0440041481105c0820302d20010880c000f80040c1410355580354202550700e03081049500c5000c449055410566504d02101005000081949001c030046405030890444621801701300074041075641da40101c40383c280d56120140340085200b1a03202c00d006001d00340c04030740f0490143c6820801000318050510480345880401000b1891a200340c410b50a4054421071810342952403d561600b56500c00721040c013281151012864800b43c8400070000c1366550200b0080150420001500008140304003018545000c0059940d007112540c0c21013034004020410741c2d103031410301d000076126240c0f84581500c0b408080c054ad201007c0955904603859860402c5840488551542c85490040b400303944181002c4115200219000c0c0d1141c0011000ea0554880d4180e9035030f00d81807000c203034092154035140141c400100e003400d004803503000c03007501001c21942d81880c038090007403074604060794001c403858080300c0754914000d0408000303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 520702203 1250 520700953 520700987
    0xb04091211010501150e190803072306060a12030504050303030f04031704022d0a0303080106020c0105070f06022b1e020c060105040c02010204030209090102030a110703081303 77
    0x4403018005024101c0400c4860511480d07103070000004540c1940e00c0c1c203503800700a40d43c41c04040c1340e40c034041080c60b0001c481441e031007402e1076100060b81e20b0100000c203482445010390300101026400f081d20818964482c10740755400440400000b0b0350340f5408002640c06c0e08102d070001d090182030403102405503400151b01840008188800c003030400352028407551080d500c50300d400100034102440104144c4000750011240c10044074850656131828071307815000500c079001181c800b0005800f8904551055022a43c2d00c0014802182d040c002070944035020b00f0030300d151031984e9540900c00758042c1c002406a84e03011070200e079040e0001580340078070380c0600c9441c10003031a45102000203041920283d0150502c07091101100d4549000703460f103c07041c0401030102eaa00c1c00c4c00b4000940002403541045540c00c100110043e5070f002100c0b4003541946000680f00d02e00074041c40304843c880c20301030a005209100d1107002070b40c0100780c02e80c020340311007031110750ba03000d468180c2d51140d804800c044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 520703453 1250 520702203 520702223
    0x1051b0102030a090507050d080703300e0c061305060306061e04060e010804051005040203100207060614040e0727110a08101401080408070b0c1e03060105030a0b0409 73
    0x34900c41500524840d0340640701ba00d44641d43c43c1e040261400001400402001e020700051000c82e01400c80a0240030b502407a424015142801d03c0d003040f64400591003d85130380382c0070455081420000c20142e0201662420300e40200c9501003000e0030001c3c480d50784120000000200c59450381d40a840c2d140b011100c44070340c000410b2805185d141c1040c080c1ca00003d040f0080032580b5072082e0380941c0a6900a4040c0030303210200e68840d80a44002441660180f25010308650502d04901c020300744940550400120f01d803e00300b05060840305100458411810a071f640081c0b12400700303902044420f64070240c1000e102c100d805030741100001020305c10642c135100c55407040c8a924002054040882d80d180360072640d900e018031114142500a140107500090b18000165004944031600140030300354260600c07200303a6034001c125801300c410355140d14002c104e2103c0180340ea803002144050701e11410b410340c41e0042c0000d00c0c50200030080050140c513444e1059031522280d01203e0b1258028141d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 520704703 1250 520703453 520703461
    0x417030f040605070b060a0303121a130e062d070e030102180f0414130302120c0a0201020708060f07080403050d050a15091a220c17010b160201051b010203 68
    0x1800b0b0750011802a05c080225900149880c54210010000e6a070306442d02c003c5215000700c1b5100814401c00801085007290000681c59551018111014402024041103031400080280e041110190070807459500400020018410f031084125174440f030881c01c00700981c1c4001088420142103025103401d540300041c5218070a409070f40c00718180d201501e00340c1010310100140012515011282c200030144070001c25200507506d201030000c2c9005e441140c101900071fa800544030390002480e075003030340e001000078021943c06111a500900e2020080c01c030914002c106001500402000c1c0010090316a00282c1090700640c25140e07200c440c01001c01691a21441e014010420035259034034100350044000340642d900d01032030108c01c030504400c1440311540b8007403025201d01d2060002b02000d150143c001020a0b502c01d075560b105d0165508080282c00c04141070940d030068108403040e4000f0440c2d002c09207503026003821010380c2840e09558034054106480c02203940c0c42a00440c55000200740 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 520705953 1250 520704703 520704707
    0x305030603071a042105070e060607020a1523030105010c0212010504060e0606031f020d0605090f011809030f0c0311030f03150406260c041b1d060417030f0406 70
    0xf400070781e0450b1161640b034010314040e444000740300f020002e1469001420500c000301d41f0230002a00804050b000500f00400345c0c1c00100c085441c0c0d04410070000e100c0c0382c801c50403507100d40300040200e030600c0000001203200380343c503410344014024113051050301c120040c215200d0060054200c100400200300300d06103442c0027009818031000225140c45894046041480c0200c0d028040445001030340035094940025900603402c00c44800920303aa880000090f82c0e200c003000305109007540742d20b401456040005440f01d4000c2d501844555520b401c0030100000c5e001403039011604600c0c1001b00204119240443d400b65150302c95040c02d0001043d40314117a01d02c80095801f03202e0340954850014520310610044503603501c80ea10315151001c04501a2440382c007280c240c080c4100058401d141442c10101d8103585003810481013030b00c01c40080340501d662000c090703071001c1d00d1403018600421029000620b603014074001c1036414400200c041101b40c104008842c11041108a0203890310303521840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 520707203 1250 520705953 520705957
    0xb070b0403140a1d04020c1c03200304020f030c04020a090f08010e190507030614010501080a110d2406090302030d0201020a1d0d050a0605100602070e040305030603071a 74
    0x11004607200300003040e15100b1030000d40381014442c1d51284165200d143c4c0c00108480e2030000c040d0031990801003914049000d004a40304140d070101e207078040d603a030444d000b001c0b00d510300b480c2400076146800c4000c24115000c12241c0140d0120f03440f045022104000038103203040d00720200d07403041c4001074440e80c01e03400010840c100c0d80308840700403015503100c0b010380c2070310f41204116283d178210300d510300b01c020707080c003400c00d41103018030222000151a030f0b031020100c0c0c8032203606d00c0309192200c004125540e8072070003966001e1001d44090000701c803a026000c40c07500405076091403064407516004810815440c060184461040b49843c10320b64400000e4601c00b101c1c041a40607003d007010702d508050050080b0b4111010341c1d1f48410300708160000d000c11503055905410303403090300c180e000380100d1000c2003281405405000c00103210b0500d0f441c0600c04041d154800000d5400080080018100702650705901c542c042c14255520b1b542c00000030304003011500310805851182001920610034800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 520708453 1250 520707203 520707211
    0x20309060f12150a09020903030301091107050102031e01080c0102070312170a020a0f080103050c06070305120a0c1206080604140c0a03050c0120031c0e1207110a03030c110a0b070b 79
    0xa0818100d03461708145010b034815a02d43c290542d108200400c080102a4403004100850780c50081c10700080381d4549013623a000f07a0b42190801e02900101c0315840445080380d00500c050750041110081c02c03030000c1d481300c00520010381041c40e20141c0154a5000c0c1982c0821201c655615203403a181c0002918001d40121002600256a440016503154041d42d003140c10f0340c0d0440c00601c490b4100108101c983e610000341141000000d000010189003405051401586889408500107040280080c542e00300900581c100a01f030120400024002181b8035400903001142c0090110b500c2a0203032404402c120b03501d07040500300302d00105200000c514051840000d0b0b071010900f00c01061800b240810b441041615500b04000d11614404081c8051044112102000c165503004004403414584201002c81011000150600c10480c010031600000841120128481401e503100101044050384000341113940b9254004816600c003c4198000d0642d02011642c2d0f54442c60103004482c0203039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 520709703 1250 520708453 520708459
    0xc050c03160b151f021204030f2105220807030510050a060e060603101a0a030509070e1b09030106061e03200a03060e0c030702070e010501020309060f1215 68
    0x2c00b14640019203111020480001018210b0f241d83d5000c10307100b034500d85004c5109500c92480080459000c0c5400307840214010507001d00c84081600702181140e401e10b000862149000710409030458100040d107080c2284081402c180c2d09039041204508a0707036070814006407082102c00020000c000500c00c1884d0b00070b04003400191141c40700e1109441080c012000d4026a640014a00307080c00340203107070301c540425000d03083c1c1603441288208a40d2980b40c40b100307a1100003620b600f5250117000d0940c0204181740100400c51508100c1960b00001406a0003188031000344601d403190284152021581b0081c002c200c00c99480501405203032000b180f540d0011400510903040074024850b01c541109000703011700c1d04808980c40c0c031005900c08007200003407590712030f80404c0490000e0b9200b8401c076004040c8695a007801107029242070300d964081e50100b1500001400140d0307000c401d440c6601000d07203070581c031a20400010a258040d1314802c0c1c0c0e0211034030741001000400400e540104181c1a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 520710953 1250 520709703 520709723
    0xa090e03090433050102030a030506041503050606120312270607090906050f0a170304030503040b0a11060c0412110d052104120f0c0e07030605030105010b0703120c050c0316 76
    0x70701c0d584900100f4074810540560801e015403091130340aa040a030740b10100400003d0301404004c1c0300e00242000d43c2068039154002420804a41001c0c4408481d01c020800114100790542420002c1210300a10b43e0344160f1121a5105509031456801c4c200555103a01f0345601d0300d41090001d0000d0054801c01c04140d0406100052604010300c20181e445030140002e1140e90804105415450f034080180f00b01d03100412001000c10340600281020301410000c1d00e59560034000c006060032010301d1102215000030081c4040902070004031412a6203845800214480a08204290034401e9407095001f03400d400c03c40342040008201c800c0c441c000040000981c100040c0c0c446900c0c00b941c0183d04d0410318a5201101041c2c0703003107400016901c1403031440d5602d170320b5020b00202440144ca40e003000c242c0307443d03003032105190a0069601404a2258940c103080c9036840003803d2191200180800c95a0b42c000c513902640304004031290340b29110b0440e0385c0e07110341e92006c140180103031606584010107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 520712203 1250 520710953 520711031
    0x40e1f0b090f040b07080f061e060d060e0c040e0414210a0809060c09040b0f0d080318151801060312051b010b0d031206120b0a0b01030b0a090e030904 66
    0x69140724004c0030f80320007c00e402d07600c19061246601060310400c1224100d00030780c01480d03131640b00070502c40074016030101f0b000e440c00c1c50500104e0400f520000d9114001e020600800382d1000a05501c03a80104403012100e4044110b0360401a002c184a0400300d1800841d2420048000080c174211240303541d1070342640c0d10209269101c040954140c0c0c40d0680c204244c81d6a481c2940041601c081c0042c01c0f2410f48c030000000803c0000b0790f220881d81e450011082011804400c445180300c07110b42c00103450400320560307035a00460001000444600c102d0b000c00e1102d24401d51108024541c04050542000c06012001d0a22317000b540d404100c0c50300700b0507180702e400e8060049029800c4040c141c0c00045880c1d940540c0d40c02e14040d041c8103400e035111000aa8210004000c0c0f1840b40220601400d074104101424160741000900d68185400c019034210940c88190340101220745421000451104404040d400c52003120180359015060040c8c05603000301c1c60b03104040010810307001481d2420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 520713453 1250 520712203 520712207
    0x7021b03121b0609010e0715020a140307020307030b0a06051e06071b240c020a03110418050c0109080f07090209120f07050f040e1f0b090f040b07 64
    0x1600641254064100d09031100740e14100710054034010001d0780c4441101c2c80c2c9080601d18003003040740c2141140c0e4644000f0404030b082441050060403d40c440c1e420341c0f8800c0c90340a5940c0c40b21040050075519004c500089401080c000c2d00d400540c01015203825954a003031440c2401c00940d00c010702140350000005061809904000d4060741c841c20101a888002c1c0070080b2540ac204001c0d02c00203c2e0400742c0310740314074244414001d880950000492a01c6112404080c4514811000180301c480b510201c00740c0c0d248603c160480354082c400c400418590800324020b09441c0849160314803442908804200c0c01060040300503500380c1c1c031541404da94521075070f43d40c0701f10004503086030403441040c80211910f400070700558001034000c4a420201000c0383d4589802ca24403052a9006140309210900e00403014600e18802181c092148000383c8a40d01e854006e2401781da80b05030801401745141030140e811448096100a101801d10b00c1c10304002440684115011100c003240217000039110780c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 520714703 1250 520713453 520713493
    0x20703140c0901120f02150a03110301061d031204031a0705090108160e060705031b0d170a09020a150f0807170907150e01030b0f06160602160b0702 65
    0x1080050a442c0681d02e01212102510005542520714829402e40240941c031092000c02c1460f0b01205d034281e4075400784d0300c018115140700900510f00030080004204495014204241d2104c3d41d61114880000c20000a864000690025030074a140800c00105101102680c03101800f803040982906580b000000c8032a0b10401220502107030840340440c041c04001c050454203582c0303c0c10411f1076030301e80c000080e0300c58200f014100c0e1943d00c001b80b0110002c0304d040500758600700480090070b03403245009024020010300c01d05500402008400651900f00c2608140a031507009041c850351107407103004c071401103543c40d01042c0c0440c041c0461095618426458540300c2c00c01c41da5000b2100707485031901c80c00301101416041d400c1c8140c1a011814050184040c1c00d4410b46841d0740805240040024041d94031100d6442c0c0300c1c1807600441040b07070722810704584490540000301c030b06000c90741c9030501c0203004041518429000030401c0d10100400c0e1484680140c08540880708100144440c44c8121 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 520715953 1250 520714703 520714723
    0x1f23040302030c030a0b1f0305030f0901031a01080c0c2503030f0801060813030e03010507030e0705060304150e07080f0d170402130e0111071a0601080f1b07021002070314 75
    0x80030003400047c00caa0042d001046440220358034003048203540f5243c85295030813818500b80032040024540c0625a0944611600303917042c13040b2520b071080d9403400608000303c000c001003e038202c002201941c5000601c07800c525404010700300030360311940203444a07816642c0d0008801203420881d120007480d008d4401c881c120f03185d2b503136a030702965071300480c5010203030640408409002c2d82004100d071070758007802030a22076001a42c0004601180c840b41c5482d1481941c005405241c042060001058140541c40350070550003002066002e1442c002902c0c3c1141c0d6031150000d401000303030001d01440f02045201142000399519008a0404801a1143c1d0b105803402940f1030b04506c6074408200c00c581215914061b0b103000061140e10120842465501001d41280c2e0130300c20320820f22010b00780785456600580c0c20b1a05040910301a4800388041d94054004110001d21820405c4111007680031a25010b902070b2032080d0f01103038448040d54554041c00205c0d101d645d903100d8907002c01000501c075425 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 520717203 1250 520715953 520715963
    0x6030d080f04060207020a0306050f0f0a23091906020a02060604180b04030302130305070812030907092f090102060106031a011b0209091005090c1f23040302030c030a 73
    0x11926290b80f070304021350200c00103e0300010401800000b280d5a4465107101c2c140300c4201e20600c1c5032204484141d203000516081e0074a10b0f2100e4030300301c0c40d5107000e803410040000965500b50b49980712602d00c1c07c0c0180c030100083c03a400e4510031003040590307000f4009030703070040d002c0740e106486d6a0708010940d401502e241c016540c0f1120b0000201e607916807142d401c580039080040c40d00d48402044414030b5a240c0040e143e580c01807508126034a01001624100086008401e0035400c00800f4507480750200e11a03002c42d60b40b14482c0d201c61580225104414840700380116a41d40d100310a00c0c40d060300000045c4d409401004000030b4060f000c2c0c0550034018440300c0741d840c0e0002c407004c01940d01c0e1454101e101c02c0d01e0b5a01c0300b035200584071340c0c02090082c601c1200034000f10b101c00180c40243c0f03000500e110342d036400c14100d402e507a44480184209450703903592001d18290700c241d011a000d156030f40080c130464501466401c1200d41e900020310580c0c0c020b40560f0703001e40900060503500c5941c102c000b00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 520718453 1250 520717203 520717231
    0x7091208030406060807170c0306070c0b09121c05070e10140c0d0305010f060504050a1202030c0409110a05030a3f0e04050f130305030c0c0109080306030d08 69
    0x200054445008580c071500c81c020003e070b1640c840c541245010703803640150700c80d100c9480b50003c50082c100b0034042d4101045004218034940603e00070002ca03040c190050480c42a80003040784210207126040000740c1c0c2440c59503d601e003880c0ca9269040301f10401414251801c004500118452034040b20890009440014240c2d00c1c2202192200030700300554201c1c0d00140282500804140442c609080d02d81c0c1d008100d550400d42401581c1403907078061400d10030100810045c40c3c9a500301c031021941c0c480c03000342801090f4008070741450880d84403d5407181c680b920718030402c4608201c46105503016240b80d001113850f64180350b40c401880b0006407004a0052003d10880c054614081810007070003488101240c010000d18800112480311001051080c02c10401c0c5007031510400d9400b41c801c880b40d901508041a0401c90b22065031405020031400100280c154502d080c119442200b00c040204005035403802c041010342c00507600d840c40f0f402150039401001e446840e10b0340c01030b60202d0b41d1700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 520719703 1250 520718453 520718489
    0x5190b030f06040b0321031e0412090b2b02041d04060b030c0117060607240b010c08070201030c05130603020c0d0f020718090b09030c07060207081002130510050a080709 74
    0x101e6547c0000744007181880000e08185030304624640001c0c0114401c006038248480307080009801a0a103070091002883c0511400c03102e1031301c90203144c01c41140c90b914000c604038041c40e00c8002c3c1c8145e810041c6410840400781c13402c1007002d540240701e43d00560b41044810400c1c820141c60324000d9481500051031100713413620080044074400c2c1c02040052a0301c1c6042069910f210a4041682181d003070b604500701d16440c03440041c02107443c21142480c00c00443c802a681e0509030703029581000e4101503440300300c51340860082e411100d10302800105140400e036a0721000300039521500302c14650b03000e40014003000601030b08181d520050030b07401030701d520340c20320801d10366211b500019650000c1e164410000032546203401e0340e02070002e20002d103550302a444545840c2c080150b01090031035111507010030081c031021400d008940007070700016a498006490804030b0307032229002554040d1b0b00c0090b14044c241c00400070507048030f1a45400d011540d4403542a52030030524400c0d4950448803420070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 520720953 1250 520719703 520719763
    0x120f0a1211042303010c0c0318030206030f060a030204020c030406021b0901031e08030103060605100206040c120303020c1005061c0f03030e0109050f062e05190b030f06040b03 77
    0x20280c9403000302400c0c41107080f030b00000d083d580a81e03080d40101740010720300c00c00d1683c800d00307034001c040d1644c4c2c66140952856001c11041d10004001c0c20034902604007242c0103075aa1061000155001041551984041d07003000340c590b4020304c206c20261117130800b00300340106071900f1229420801452140183c0c41c42d00e4100f4120201c1006001846040807030600043d2454050b6001c0c6000e0100082d05904103024000950a032072346190956016100300000141d01c07900c100706481510f560400e032066a440e00342d000c0d018642c1850802c0c041e85407581c3e00d5000c640d1005102e000d08039080d09803141c4a040e40c40d00042847c0018195400c0b415140d00481c0c0a508588407035545400000b8020b8681d4503903500b040d104580c401481e400c0042030040845020103003040d40200041c1003c144800701e04926480c40b4030384220f0b400303464044a0524401158150f90340201034151215950b450000c0c1c1460040c5421a2040d1040d842c0050002e55800c0000703000308111030090400800d40301d0310b405 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 520722203 1250 520720953 520720979
    0x618010f0e070e0438060102060603100e2b090b070c060e01090e040c06110304080a1101020304080f01050a0612030c0f021f02030304020306090d170702120f0a121104 73
    0x5031a00d800c0259118000c00d074180c0c0340d145d03046000391000084074201c46400e014150107002e03c0e0465100c40c050000d02c5d50040b03030034240c00640711400034000c1e00c0e424815050901140c01458101000020000d468071418130503030b01c490703032031780c2d05041541c581c515680b05028034100984420003101041c8034442c0500080ba403030105c1414844406562882000320103601210103c80d4040202e0b402c202c0e040d049241880400c500d000510f007414149441c2e80d5540c2d0388e50354050048044034480c41d0303499000b401100c0140143e201518440d07440300c0c50701806040280c440c01140c3e031030301c5800074191010038031031068150705650360072461803261034240d1300351035400090342c2c000d0b1300c8120300d9040369000000d54415030302a0042c54403494076004241c20444020039207040d036041204d10f014000d500805525940421032031600d19522140b0040307140400185050682030400120360100040c10005800c14103c640d403840d00380c034000101a001d81d03c5800c5d02c8982d0340c000340305c1449002d91940d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 520723453 1250 520722203 520722211
    0x1506080c0313020607050a02030c040b03152d2a0f0a0207080313030b010f0303050913230105100f1b14010c11100212150409050618010f0e070e 63
    0xe00d82141c4000e0343c00044440c0d0107440f0031206a0300183c0000c003141401d01c00010040005c407020408501b4400120707817240101d421102008041d00c002401178048410740151b0015003413140f808401d84020404041c040a45040400180451700c0c0d1004400b44420401d0000300203607481d041c121458406007040c0c00550f120070660041050200b0110000c03c0500301c4040e40b1941050f11514504085541c1c0d02c043e0031180040001d0101400440d40020850b282d0007000c5d5982100304400540780ea00514044180300128000d282e0394005041c642e0070541e058400448013940c81700c042d9001590360750401d0038602c010a913401928110b41e2100928103810034022a099101d50b00203000d0582101c14081981001c2510380c0c550ba040d24400b04004009842204030840c074000929001400740000200301410b076890602d600346113901d8a030440c8011700c0c0e03c441140d8913402c0184104505d0007030000806232079843c00c04d0740c07a00750003540a55201a140700380545000f03406c2107480e01104134010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 520724703 1250 520723453 520723471
    0x21b0d090501111c03020a0e06071a10080f0a02040b0906031e150f1f0e01030803130b24010201090206030105040f02120a02090f010309024204091506080c03 69
    0x44c21821400403501c6000c1d101414980c2c00503594502164050011b80034504481d01405043c003403c0c0010708030043c0c054060202c448807040351703602d03401180c030340c200d003a0410710042c01283c080d800d10400000304440c0e800e10841c3d0230b225260500c410700044401c00c03102258107078001c2e84880c9000d0400f56290342a070803003406a034182d14074884501d1403000c041d1001442d801c040fd0030000c211000b0343c03aa10020600c01000400b06150112850001e001030001038080c80001003c100645111107045c0c82865010310846210f2901d403c000e04105a06001031041c11084001d107117407584103100d0302050030f900401440c00c0d80d003094180b00051598100c00f64446030308014290740000344140e03031032103640d20700300143c3e82d0340390074040c000103015007542241458201040600140e440c1584640d07403092400c60002000ca01c56004041840d28072050540c0000c1c240e52603284910400003081a03400042c001d03c444c1e8100c09040d50120342d18442c0c000091030010104400792800c400554100d4000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 520725953 1250 520724703 520724713
    0xc0a0b06042903070506120705130e0109020a0801090c020a03140c0a050607090645060302070b090c030c060a091e0618050f0409021909021b0d09050111 67
    0x9449503082800c00c00703111075203940301c101c92410b51404004103c050b25050302c6690520800b9080d04103080c401a04a605010000c910082c0203902d6418007001407503010384422195070340b0100c200007540012444c90002c2c090000214202c5803501071114005119401055088600d450481d000e01b0300c00e4065005510400120100100412800707a14a00880c040d01d010704060704040c056902c81e40c0700740c06000619001c00300a030480111000185142c7c24907082100d143c0385d408080311500720840382501c1d04814041852641980a042e0f9a0f12841a04203252107074a849a9117500f202a80c1d94140d00c00c014902c0d035410078501030883c600740c60505e450580d803500c0d482a902d4840c4290308049105086041084940c00380d030140540d202425110704450900022540c4e06044448a6010b40d494101100464445a0b5204500003190302a113040a84500300707680a54840f0144262804071100603540d86913000c03d1000e441d120540700c12080500d80401550113040c0d00c00444007501803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 520727203 1250 520725953 520725971
    0x20a0c050105310507030b06010309060507021c09050d110a03060903020607031a010906080709052101050f070e040b010c0f0507210201051b0a1a07140c0a0b0604 71
    0x424014140550f14250350000702c02445084402c2000007a40d005520103500912900032803004164101683e4002d003000f5495070318440140e000d40103503600148848d24042c2003001c0c0690114030540c8124418000034441c00150004540d21010f9001c0d03e9489900d007400640000e151004d03078110448040c010019981d039a4844104642d000202039025802200130400c005602d84202c6079900c0528460701103088000000810041c841d008070030901410b440812041401455004000e140090001c90f154a150225a580a4030341140034640c2d800c00c0d02190b56080c050030311502c600410760303c1c900e0a100f41c03800c20029086d20701c1c240741841140081c440c0442d1a04600070340e0180128014070351076180c00100b00c6001c92500c0c0219050800c04030150060b0ba011046640050308052810401c07400c4040c024280700080e4001000b100102017480450b418103109948260f10a48599121a0a85c80b00c85601e01c141b100e1006103821240070440003441c03041c078494220700e014200144001c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 520728453 1250 520727203 520727213
    0xb090108070e130f0b0108010c030f1a0409050f012c01021c0903090f090203150a0b0a0305040c0b12101208090405070201140c07150903020307030c0f06060611010b040c0e04020a0c 79
    0x170a0b0041c100694448a1120300103416001d40e200b003001c8007204200320389480300c80320340a502c10700b49070348035030385580040d014000100454450400014001c1002c681603101e1400206e00b00c910b40941d200c07840e03904007090001842036039900307240c940300e408000310b510f410b078001404141c004909011a00e600892000015138085002e022482c01c01a664182a070886130911000c1c01910b20a00403e030003804805522015074010380078604000c21640c80c0c518190015204a400c880c0c4000f10208802d504010903074055030250301807840800403c0d4480344401c2d0402810305d00034050842c108034103006030a207075001c0d59000307004e8400026107a40003030f00e001741400140c0345c4006441000c503c3d507090110031407801c5c0c29440000e0042140654a0381c000c0d4032801040c2026007403020340088034040c00052424207043d19800300080101d181c85480c00303080c1190b403922207003441d880e2103078010180c1060b100320203001d81d6584507075000c4d00f4450b0400c006580455050800c00c84d09001e401c000403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 520729703 1250 520728453 520728473
    0x3050d060e01030302100615030905070e040b040c0e1308071a07020304230d11010504080a0506070801062c03070306090803070305070924030b130b090108070e130f 72
    0x1040c00344809514600340245880401e846040c2c14920781241041704174041407070b100c0241d04c01c9c100881c90300b00604080341020a65803084840300c24080421003004441d504661040e4030800003170303401c00d0b11403404519120b0100c1d01070401c034018002e0352001c40e0310b03100604110b611400780600c018541b40d80000a000c001c3e141c44004da480406c05200c841845041d041c2a415610164855001408002045200500700140003920200b4408240f40d100e5403c9401510111003150141c40140c54503a5440381d04860410018104d1000850f042c0d21410403113015080b180081c4000407403510110b03071103e04100c0090383c540300d20ba0000000502c84d001c1c415125004044907512498181e00280940d18000d0261041001c0740c101489600d100520007005078440c1d851120100403651401d83c0200074400110764032030b003c1c054aa103560304c1c03070b04007045140c8151440030b0180d90700d1810320b68138403160240c00b81d0101800000b03000c9006800c001d0341d100c0d000c1c00400c1c0c404440da4946010034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 520730953 1250 520729703 520729709
    0xe100312080a050c0a0c1103070302091015090b18030c1206040605150a030602070807080c1f0c020316110607050d0216051003090204060e0112020906060a080c0703050d06 75
    0x1040920041000301c1842e40f003203030b0340300340540075081c40c142a022005107841500600242900b80112a01c0116101000454007642c0c0c00342841c8507600b0908030400d0003070114032a1040d0f40e40707080300481d1000d10650360302c000c44146004041c10141e40300d81740c41e0655012181207415124021081c11280c0e18401a0341c441e02240e03000c0c0850b400c09041180030340300c0050404000504840068805031640411042101d800010050302c40c0060300d4100c0007403044081c09050700078042480c62031101c0110b401e0000014418443c2c4580d10205040000d80d0010405440036070070034003039014101b05080e00c88100500c6051007448959142c1c0004c1e915400c210015552544545080420203404016401c201c100031910b061040d45404009003540328194003990416032a1a4a8411911140c0104014080c038803840a895a120002a102105644010ba2041c2c0314500810400e0070810b040710f02c0c1c4003080c0d50703503c801c2e0356021604d00141c0c04010214104102040010010b110314415280a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 520732203 1250 520730953 520730957
    0x501110a0e010e0a0e0105010c03030b06040902040524090d11030d05030414070315020a1b03052a03030411031f0518010c091e030812070810030503040e100312 70
    0x24040700303100050450980003d03050040c1d400c6682441040d0f01e107081d45045138400d20381565501101c1c82c0403800b034040200d48a0700310394081804142d250007900500251601525400380c042401070602e61104132000a40350b980c02c040050b8680d07418203451090403640079801c10035943c0402001300307240004121455000560100c180410880d8440140c05003084800061480710300b140c49030102007410190341403040f580010200191400381c80c030040da594021040740f42000c040d00303000d0303d15840150241d0220080085e4025200064000d007200721020800650440c0c0c0e0303941d2440e030264464039a05134103224913001c0410024160382100c0c0e1a0414030004545410000c1c220450740d00500c100d880c00d80d050104c05503c0b0b41e0f028200904880b44c412140420701d0440c44007400d0b094168001505144000502410184603095850700502e49503491210503a103640c0c0108080c50a0701005046800c01c00c01007103406240d62409402c5000910500f02c5d140e544e99448038108000504a00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 520733453 1250 520732203 520732217
    0xf090509212d03150102030f0901050a0c0b090a0312020a120903030b19080111070506072d020c030c10050316090f08011e0c020a1506030803071809020a0f0c0501110a 73
    0x5400c013203014510340d05075080c00103504282c100c07210400745010742035819042103004551461051300c0f4110a100080e00410840f1a904000d0401d5455584003d4260003050f01040742501503501c62003214010f07901540d4410342c030301030340a0080142003c40302c144d0405071a82803070707000d42d1707220b4210400440c3c940d440319044901d40703511103081d60342c080b42c1c0d84500b00041c403072140481da01080c0035507c020300d03241040300d90181078583c4c0c0c41c03401c03040c00c54403605002d009440c1d0581d0300004c006a4501040b003c94641d1890201044032544122131b0100010760280b01240e52182281107001d24001c080c20300f4080306843d0f040c0210b0142d101d40c0503401c070f40c0d140c1254050500c4024100074022030001000d014803200c03884062341c0c5008460000b0280c40b020302c4204e1062030b61754801c80103140e01107901640ca00301071200801581c40d440d090a010084d000000a01180c01d108036030100c4801d888440c490441c0c0d00d02600c50000c809415502c84d5200c0124125510b0408000d101102082c7c4600c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 520734703 1250 520733453 520733461
    0x426030309070311031204050609040e03030a0209031504080a120f0929060603130f02060406030e0d0c0519020f04050403120b0d0510150305070f090509212d03 70
    0x60055070040d0f134002d00a402040c1e141c00070300422401c48082d0340c400e503400d03a95846001c1c0890010076181504829a00020040c0918900d90340c0083c0b04e009000c400b12040d101d042c121100750320b48150f600804809040062082d4907000f100d8200185603103201c0014050304200c0c00c442590001101101c0e001111210005040000b80c20380c082c80d9900480c1c90325038580240403c08a2001809503000b1180e504100c4c0c0400000350340040589a020300361607104e03a03856801501400d81469084001e00844900032000c42c840c141d9800c0d420f4020000300404158441079a100c266981c07030907038000b2042804013126880c1c1e0f00500d40036034480c0d50385200040641c00b1013001c80390740850745440342501c01c05030b60104d04005424080c6590207200098032a28030a48844440c0c0154001403e900803101c0010309130304903a400404481340303000240500e65806604a441e03c0c0c4115000542b4401949401e0442900c0400b0713021030f5982c40c10199200c1400d02d0400900a1704402c0f034511000000104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 520735953 1250 520734703 520734713
    0x60203100b031303030f1d0102030703061508070804080f0a021b04020a09030215130603091703251214150a0303270306020304030c03020c031204260303090703 70
    0x450041544407001e90660030904000c1d03003810254400501003507121005181d11a4151f40f14402a20029000e5803614041c0403050303011303400849001c2c1c0420b1412000059100845031030b0102c06040f03544945441d5549a07042d00c00b02c2c1c014200381c42c1c0310030911611b0400300342d5000801c0038461035002400d6404805000094240720600c030310380101c1c0140682080c03150000b10307000a4960448251180710041c0d0f904407043c0c0030350940d01c04070315a060000180c49030980d020000c034501425006c4000985146001440d00c415141e8040d9800c0c01d010420300d042c4014200d04606450789042c00b41d03885d01d07050800c2603032200c860a241b00154501404a500c20320302100542c10f0b026509070003100d18544019003035890f840400104000343c8030040320740e500070035159005140d00a20840d120304050900810148070907104402521811404214600c4d0000f840980311826080f001d2074542842c07c078007a04220701480c00102420b411040e0508035040c03020394803503110b07540140710f010310398109 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 520737203 1250 520735953 520735981
    0xc06020a05270607170d020f0409060504110906070516080d180b0a0c05120a03020403020f090105030705060c03040f030f0b0f09030706180c09150602010228110604060203 75
    0x204440c65a2501c904000d152503c0e000d0707804850300070b0304400c0e04034529090740046115521449401c184001030b14584080ea200161080d919074003410440a52507a0038402196440440840910018004600f051400000401c0024854415070f80151204a0f41030b41c00e0f40d0640290403107400019940c01c01ca0b510120b030540e190301800c400c02c0d41ca03280443c4000fa0748515502c030f000300962181e554040c080101300f03080c0c008021020b4a0360311450354000800940060108920442040106410915040e24104c2c103079a4000c0180006c00d1410f820400c8070750003c0e104001a0000780000500610340080403030045003e41043d4003104001c0c034084200200c000d000e50f0a00c400f10041c01200200003040c1c07549981c1c0402c0009940d21a131051481e419001c1000800411030303104d011941742219082500c06044800f1041c0c0d050703481e440c0c203030300340c3c00340043c481c03010101c20001c000c003482910200c01801e1101e050800500310036404450070705801711001d640483d000014014040c0c10002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 520738453 1250 520737203 520737247
    0x2040911010210140f10030f0c210b1f09090b0a29010503070309120e0102010608241302030a051b0f01020c0424240c02130207030c06020a05 62
    0x402c481135540201e550606405040c0c40b050040342400100f0082d414140c10780030710f80180c01c3d034800011301d140000c0303110800d001d180e00e10090103030000003010a400e09042c1a660001200e10550ba0b05507071004082d8035a00030340444c2d0300b0480001610f106c035116036a1068055504000340d8503196031540161044031041030818580360f415a4448603500000c00079013002440c007103607030307460b00b01d0201d000e010300c0003012f458144103082510b581d40d000400001225002c0e0020301c010355032512411784501c149404003d00881e0b0072018480b10107030300182030b8410000c2442d010402c50b1a00844e03c1e10250b440111403c1e4440101c145100e10011092001d100c6c08640d215501000d0b000000d40306c02c0281c0600d4059521209070082030b07440307080741490030100c95540300c0d0003941e5400300e030f06038110703082081031848406c11403c0045442843d00c81103680c3c001e007880460780045485c0d10025808074074150f08101a0b07950340000250319000900f4941c119681c1c0c9a144c00d030003004403180c001c00403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 520739703 1250 520738453 520738483
    0x1290f0d0803040f030329031005090309090406020c01020a200303060f060a020a06180303051005060a0f110a030c051c021905210c0d05040b0702040e0a020409110102 73
    0x10000380e0004408004403036000e035010103c507540d00d6807450180c004c2c0210829100c604041070b200c201d503038035000710724241151040303045610000441d02c80350219007096420504a80042080741000d041c002c1c11182c2141c440c00b00103107846010042c0310708a03008030003144002040741503401c00080c1c040c80c2e81c80540350701d00c029618504000c00003410003680b9200c00c034000c1c0c0c004180100920f000384402e11200f0340014061040d028403042e40c15944001c10b104402003442c1c140400c5403a82c8010464095803c060601d074a054003049065070300d81050f680c400b0420100084610244200380140761046100e0b40b2001c6503d1414035049041c1f90040d2041d0031140110424514030503070000c0c24450114500d088001400a2420494200854000355140c1e13000940300e80300d0080c0c1c810b0000c02c0040c1c41c13681940c0c41d50300e01e00f0301110ba520451081494462040c4072010140c681540000c0340d0b01442d004444090096a0224007591a115403c1e10302c00034440840525503014400001d040c107100e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 520740953 1250 520739703 520739719
    0x510050901020c1314040b061201020304200310020d020316030c12021b0616030b031b130b030a111203160605040c0e090703031805100e0301290f 64
    0x20300007540d880b0400102c0d03201e011003030420702d024040d41d80f040c4050306400125016519107400c0030048090140c508600610540154518629040c420741e07010b141d011403500054014076500c4040c404d1103048055143c000d217120810040c0e800c0c4000c102940391244096140d1410000140100f0250445841850b09144035509071035408008400c10744480d07100141c0b15941003091810544610311108035500c5840140a4094404941c004888140381c0c0e00740702000410040c1034954486c0242c641600c0401804101c1c03619150100b11913500d80e039000002c075450900c000900d0111850350a817420030f042d04e12403c117030524850b414040807010005515041d141c0d20314415401141101420700365844c0b02060030001105d11500081400020106c80343c204070700c0590b1241c0162100700e000c54034180d03103100014041549581110070003007000c0110130300020b0594840040b480301941c5135584011220b801d080c1c3d8a48040d56080c00015402103070010818095480e4100075554410004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 520742203 1250 520740953 520740967
    0x6070302040303050306040f060906060e040501050402070b0417070b0c220f03030c0f06050103081c0b010804030302090102010b10020706030e0f1c0e0603010e070f030c0e101b05010204051005 84
    0x240485c0d810050a950014034604c07800081d80041210f0381141e82c0090070600005503407584150444043c08080fa0100071590340d61080108074030a0503401446002e54074001404a801311403441c0c181905c11100b0352418200d42d442d0041c00000712900700444501041c0b2a01481d070100504207041d6800c00c1312034965091042c54114450113100081c00c208008684c98108441441d443d0700981c0d018005005071b50b1203283c9404260004a83c12803c5904d120612030850814000ca212405c4180c481c0b00172920782c2d8604a000c4c0d801f54422906540d02c48810a0950f01c0b01110229001c0280c0e002e81301c0b941c18504c0040649175001200c54186d8042d00c048896038001195001034001d41c540302c40c0b04481540e400f601d12042c085136290380400c2c040300014041251050180c8105110382c0c900144000084050701200d04042c00756000070400017544a590030288010242c60741c4c0c40c00c0c20000c52500081840220b07000510854042e500071404001d28149100f41944801c5641071260402e54 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 520743453 1250 520742203 520742207
    0xc06180715090b04090501083f1903050a1a060f0703020f01180b061905040209010c02040509010213050a150e0411121518011a12070c0506070302040303 67
    0x609401008081c948007411610079900600080c0c004001e40700c00319072074940d6000b11000921003441b400009008160000715680d2075203102c00e01480078190442402d800d45074604d140329200300d1488407800010010800c0c4d888113642100350814140d54082400d150003650301060303e1411004100703080039405041190760b108020799207002050204540c0311103c074103089281100d0090034080551a0284001e1f407111a4242d81d40058018110480d031500c91100748100c282ca120310750842602c21312824446441d150f001046540b205151800385044030341c00080891304141d031a0141c5a44c0060380344e04030a500c2e1503403401032030200d415428a901d001c03401550740c1d048900c0c510070450b1400b5608050f90759a0700000021030156600707501c0352110007601c1d40428050f1044080701d034142d1280150b130f180040400342c403c80d400e22401ea444e4030b4200c1420403144090303000704554105125051036401901020741c4100040e650380ca20703140301c3d42000c80c1800000b419000130180104028408a6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 520744703 1250 520743453 520743463
    0x1507091212111f0b010309020d0c050a0e071b05070f181b020d1b0b0c070b150a1211180103120513030b0403020c06180a090612031803060f020c0618 65
    0x21503d100102d550104000103d000f482006802507011800c000b001c400d1000034070a035030030740c0c406581600129032200802601d454085860400241a0392048206d00b040000880c035014400c2e0100c074030580e01c4481d9502000e949800c000c84400340c1c003000c1c0244000b980594800e141140e0750300885100714101c02921141e20b1101d40c014051100d00801c0e07501e254000c0203c8480c6c02042c1c4007060b0401030303a0000e03d98045802544e0814100c0080b80600340440e824032449100182507440c8d076403404030380740c0064408110955074003180b0760f9a58015150019101d01d2041040c59240056045207004c40c401040202c40ea02003103001d03c86813204005404015059a0700910300303107004d9507103107000c07071030118846400c40d0080000310b031030078418034105d0800c02030110840320300c4040f5485140c048116500b80c4906c031000000d40e446d48011a0081088060507801d058140415580784c1d00c17000180c883d01150404095400204003030005030920030b40342c2215032040728030b000b4000000c40b1a914 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 520745953 1250 520744703 520744753
    0x140c0601030b0408070203010f020d051006020d140d050109060612021305040b370e06090408160f0f170903060601050d020714010605150705150709121211 68
    0xc0d072a20100e8113001000c0706a030801d03a8010003e0090824807c0d0420180d08608802080c03181000007254800300b1801d2288203440c41640200030101d800d0b0380450740317502a40180b14160000f0440403450039210300034a40030700028003002c142d040c40d020004200303800000103441c001744188041010003036007001c0034046a200300d17004111403400600185911140103070800c0c4031080b013031150b40149141d00303603141c2c04c1844043d442c0c05144c2d1079910501d52081110030a52003807000c0005000100e00c2ea016085a014913030101c0c02d88201982e4034000b4451085090320300024000b0307107104000e25141d0f0544071240d810030440c20700b4601d03230120303684000180c1b26906029000c9036280c1001d00f0355041c0d400301d64101d1010059010740c090107900a015a000c1c00740500442d00c11030b1714021500e411503021561104c01002c0441ca010040d202a64010707103ca01001080d20b000114400c8020100c05054011845c2005009680c00080c1241300315616045c00c079002111541c91451107031102d900c174 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 520747203 1250 520745953 520745963
    0x40e010b04150e01122307032d0b0603040605090601050f0609040e0102130b04031a060307270c03020a1e091404020f040e010611010b1c0203070b0c0d140c060103 71
    0x140c4403d14016076284102c2030300c00031094a84649540e1a10300c1900d420b071601c0e4100702440860301c4e122421020ba81a09040c6400c4000d414150300c0c001000660200c10b001640000103041e80342c03200020026441076500f0b0b03c8843d20765045c89034005061002500602e0200c6140d81c0c203a03009800700c0c01d2405607800c8548956511558084429402c0d01100c9151550b246111960b41e02d440710100180c000c1d00007643c1c2c503d045558034403c0d4600f0b800c81401490020000c0a045142040d098820045a06d217001d410003070000101404510740105d401c14480c40c0c401588030020940002d00490302045140403180b040d0b0074090910343c0000b07039001660110015030102c0340c1105c002c24042e20881d8940c5d1102e150011b000035102403c80c1107241607502d1684c9018101e0701981c11542690010746225622204600c40000c0c424012840e900504c3d20140546503425a43c0c5860f00da90b4002d43c07882042078001c1490510460340c04072400f10b041010501d400d050183d585170695641c1d43c14000189 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 520748453 1250 520747203 520747217
    0x10b0304060b060d0e01050f0103020a1a0f13092409021b07150f05030f060603071107080c42040b040906030c08030a0c020f010c02030f03040e010b0415 67
    0x1040c08955080380d8400100589820740d546200c04000e07004100c0c1017005e194035403802000c181c000c0b100c0c003c010f040369002001783c20100c0c00c0c074111046948110700f40100080e000c0000c00803c98421000d01220010103244600c410f24124076681075510390341c2070315003010700445591006249100e003001917444801005840c0d0544116000a10422400d89030707683c41010000280c0b81d079194107800440000f5590001510780e881c200307940600094621803850701100000416504001c00a150f021001d494400312081110103803500f41405a0410000da07000205100b01c513041200440e0380402891940240d00354094800c2d101c20708030f200b0004140d54409000d5a1a5200078013a100a02032090205a880761749064407001000c8038401124030844203d0001001400402a5640c1e000b2640300c40814082940c00c00c21580700d041c00345414411640a88005a10100440c0c030420760400015070f03445040504402d41900c051744030b1410940101b2080c00390760702c8215812203e00351814010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 520749703 1250 520748453 520748461
    0x9090f0803060d020307030b07030605100c0f1109040b07031a03070905040c0f0623120f06120304030507080f011514010c120c06060e15060906090306010308030708070f08010b03 78
    0x66020010703c2c001951500c502c2002000703020f105a00c0c140900000d4404020b03a55076031050105500d41c010400011030307200d816990104442d4802ea140ca944250010240800001d00140707200809841c259400d00c1c4050820079056014800e00d0842c0005012080b001d03100e1800081d51765409018443c01503887d4000f107130411040820120240c040002c035401c48072384400d8020f250310314a1000b03054540c440254852a00000004c441581c0841d50030844203a07190209107416070b402034415a08024400c130080702210781071025101031071241002d003801074584035801d450240e039603242210991400e00445a0f8421409540c0102d501000106100181e0600181c0e81881034800c060f00d8005800c916506140d03014090b9005107121340d80402c00c55894844e488181e440841315a85180050180c48005281900c0070f448030800040049240404400c0420305042007070b0b000b103030030300c1020080c0100590040102170b4043d031240b5010740ca00105190003000e0040610500c010300c24000089 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 520750953 1250 520749703 520749709
    0x306060625060507051213020d030503060a090e1b06090d1e021f0f030905120c0a1205041a07150c050c0a0809010224060634060609090f080306 63
    0x60726516400400070030161604010140c030701d6016020307810260349440000b07020640d103c1c03021003040c1d030064036001d601147c0d598281c031154400303802c1030b520100705400000d06080794001e00d10302e041d001016050742500325540c0c400c0000c004015600c91071040c0010450760321400c48ad4030030f1681141e00500c40c1da0540d00400201055004040d40008075008840d80d05411005c01070b00c9a04540d58020141000c810304804440803614028403940050103101c4050700c2403805010504d03822070a0700d020400c142d80300d4003c00300e4000d008010034008542044120003003006042003043c0d0f01100c0d4a0240700d551240d41c0c0003840d5005454060703482c0300185000d84190217a600e2601c4030004c03603507000c0460070990f900307400814240b40103104410f0610308003809130070060f0202c140d0507899401c1b42c0b1003d04000740b6800010980906080b40a4682c1030450618081c02c0300145031740b040c4101c8465400c003042510f0440d00014201400d2034902c00006802c000c1c10b140c05074200e146940c0700c1e181c101c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 520752203 1250 520750953 520751017
    0x5010e0712120c0f0f08040501110606100f200105061c0507050d030e040509060402030d020a170a14031501030c03020301030503120604061205240c0409020a09090216030e03060606 79
    0x805000410b0000040c001c000c1408020701c00e580c424ac07512400304615002e510b66401c0f086458942154003500c41020342801050707000341c0c0540c1d13400e0450002d1885480003051032500e01030000260b45400512207141030502941025440f20200055850302d90384616694141d20b100c0e09015840450701c2500b818420811036032801c42c0208240203d0406d40200c030b41d50042510240c3c03003401003801842c445400010741212b51907001d0108000291020001092034001401c00d609004403400d09405502581001314424208451b0b0455441e1800c0001000c40d01c6034522001890701c1040140003050b000002c1d18450074100003003460075615800882d02400e815845205001d0102215104005000c110456103444d00f00d03032140941a420f00801c10018250f408419900041001380034010303040e0000c2492051505100600c140e1325102c5030126800304003210745107080041c45008055000003e1054040b0403001031042d03083c80700019a01c0e105038242042d00c0450b102c1d40f002201c0300c03154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 520753453 1250 520752203 520752233
    0x103420b0402040306020c070b031303030518010c09030302150c120424090b0603030a0801120c1d0402040c14090f13020a26070203090616020a0305010e0712120c 71
    0x350f464641c1c900c3c014010390043d02c285032550166100105010300d461040d02d11801d41e0301003e20b000002c1c3e0700e054000b8000586111240b40c00a24140310014090042e031400180c5a51159026480d600f002800d04942c084074079850f45182d03041c07004150000d010b4501c03588060801c842c441d10744d0300c1d010540990301040c1c1440c03003508922000d0b42a000740d0208a800380030310000c203503e5880781c2c100345d01c030310401040b0f5000c1000c20005102c5092814800311050b0301c03441308810f0440d01d620680c50500d80788102c9008071190f120401045081c03078001e070400d84466041404c1d15940c2400c00c900c0e240580a001c5d030081d10090b640c102c1940e903c030302e024030300103a101e411550307003a0340a402420a440741c9a080e43d4000203c6101202d0b88041201d14400e489030740c051814414108104005988507580d10050041908159400b5940d504526001144071704000281c2400014000303051940703683c07150034418504030200003c24010321403c61007081d80c0c40c2c001c01340c4030301d0320f8184041f60b4040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 520754703 1250 520753453 520753459
    0x1d01050f01210204090b0f030307031b051902040f050906070f020a060203010f080111130b0d09080a020c030705120a080a0324030201020c0a360c05030103420b 70
    0x102c620400148243c0c000c0c0141d0351052400c0c40406e03c2d41040c80383e400440410b80d80c05034010020900441e20412280030807004900740c1c1d010000c16925602c0c0750204000000002c02e002610745801c51500c0d10654620200001007030140345404503941d42c4400d0000c01c0c009c280301e1040003003500035100380083c0e9007543d480401151a542c40343c030420700c500c145005030785081d881c00c048810202004400c1e14114a090209101001d0404201800342e07000f800c406c2c0309c00f5865070400800035240802038001c03107040340e006010b44101c601c1014544502640018000c01500c4c04642102c140400c003040703202d8001480d80d940703040115045004041012404080d805080e40740f41d0b240c50b807285140100d9000742e08640d9803415400400c03424040620411255404007012141c03a44030221182000c10240b5a00038407407000140c00500351200200842c00083c3e0000050081140c03a036041071000940706c425950b2036482c02d4100718050301c91040e100000941d12420040030340542c00241d980345000e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 520755953 1250 520754703 520754747
    0x30319060b0324030d0c170403120e04020d062d120803060315040b0405010e15150111030a030e0714030c060d0e03070c060807020a05120903070509090a03091d01050f01 74
    0x7104006013090b4546c03800300c612a4640c202c105030a0039040a0303070181ca4100c00340c020000382001d002d65200e40c07400c550700d070032640034400c00011260300d1085000505d56405210703643e40da101001e44a482407503500e062545000c1c04240400c518203007d030b01c40c081d805002c06a50b0f03100c03000000d241c840368214052007081c0d06020032003001102010a03000300e104078002e1011800190850303450b8044441801090340f039100006851074010b0704031800629040c10102d8500701c4000030982954001d10000c0c000c030380c442079610341c0b07840c04101040c01011100290b095044000d4002500c0e0000309048034418500071400b0b250300e80c0300d07601900d14079403190301702d03542c402c6989070030360780c2007810b104030408111500000b0720404d00104044108a50280c05800341d40f50640a80249070071152051303406200d869408542c980701c1025190160b28080f0080c00711601d40e160040111459810540304540c3c5440c0406610100205040c1901c2c0c003241d21401e4021300c000100c44000c49049480420182 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 520757203 1250 520755953 520755973
    0x302070603020d020d1a1503060904030804020409060501141504030b0711071205010f060602010c08010603020a020322141008060603191a03010c050405300a05030319060b032403 78
    0x4600071500d880c000584844c00588402407c0d660b0f603001c211b414540290350000041c00284c840c810705644a07100900000303012006840b8202103503800d80101940c0030b1507078581525480c01c40c0c0c00c0c000c0209001020303481c0c142551740b0000d2540014100c0c409111b080e02c912080e18900f44003010140a14040c100e401d50540d0819502a100c1c20b0000480f0902d00000480c0c01c1e403042c05000c501084a4403a007070580d00c6c00001320001e60014640d581140020b00c4910014200c25020f07461400c1d40281c010286070a029128084c0d11408100d140308001d0122007240d41908401e6081d440801225629280d98504a4003100c24503600b070400104c41c980300392424440040500050700c0381e800d80082000b983c0031401902c180c4240c0c0111903004840700482d414003190000400c0784c06048000002418120031803d510b0002e03068402c0b90305800c00300400c4246490700b0011904612a040140041da00d48404a12944006045003412035010031102c20401103401100c1e80e04a400b03030444500c518 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 520758453 1250 520757203 520757231
    0x9021203090a090204050108150406150809070b090307120303060b070b100b03150d05070803040b071703010b0403080702032d0c060f0417070e0106030b011b0302070603020d020d 78
    0x4000861148101c2e900000440d01c01c00c00e00c2503506640d010384440c107a50b201d103040004440c06000c03120b40d002d5290600410781d5010f04000200410f1355490321092420494810381c02c00a140d001000901c806120413120b90794009483c0b800c4030044030640c0c0c1d048919040031000790805401c07400c0d0702070001510104004080120706c0c41b41642a01c18826580c503884e041b8054031060303e0362500d6644843c40c070003082c50301009040703070580b1500440b42c0140e41c0e00d5070181541c219912401140c80049920030031321450b050f031805104034580c16180b83d0342c144440c40c1228055800042e00505020030302e2400c54804101a08412850084042000c00100d021481141410a068009006201c0d2004c0103045c5141507035200002c03020210f003040e00741280090718101801320ba919511403484000751200310041d003c0d01800390350342d0100307207a0f142c1000500f1f0311080912240119050b044440301096000c92a0300503555146005a40c0c0e1007801e505402902032560300002c0390703103082d0b52190300107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 520759703 1250 520758453 520758457
    0x103170421050d0201050106120b0f0a030305070b070903170c010b0d11040c020a200a120302010c0f02150109020a20030a030c05040332031812030f09040504030309021203 75
    0x1e4032401c00c407420311120030422400c0e01e5080c4202e030003059039a00146007a1000b03800c4024040400f81c4561200310303800001440442c6698030070f0700400d8001a00c130042c0202c4e000f05603031001d0141410410785246a4414442c098541121094000d002c03d107200c2d414030a4026a01c030740b030b00400c5828081c541d41004400f4901075000144150b2910b100002c50500108003101ca03190460204d003c2031180c0c8064609924880c3c600c1c0d94010710740d0304045000503840c030340e100100f402a8000103030050708030405440c000242c141c403010355100c420780807a00451440700074103444d00000b0140c0c503021411420364030b92030883c5500c0985500c03401505007102c0004051b0582c02c51a640c140049040c0760020345151080d400043d0540c800301e04030b64078020ba01004002c561807082d140d0441184042c044605641203003806410320703d00041ba0140300e04c1d01582107018085040d016501d0003891000300c01c06480f490004500a07070300c0704001410326001c0d81c40340c6801500540318104060035010750035100c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 520760953 1250 520759703 520759769
    0x201031d011a121605060a09180212071b060905120a08100b0415030203060f12030d0b01050c070909152c0a3504080706200601031704 59
    0x3d50103c2507543d050100000e0306541e400b0300005240c015500344824421107602c001c03814400d1107842301001603000e407000390a4068032900d40300180c8508429200a10556010b0025410001c0c481c0e29003000c01110030340780e00318a0b40280e000408200c01c1c50018144220b08416480807030021a42141c240c1c0c0145d00070b48541c0c0c62440e01e800e42d5444100c8401c26000e5405050404030070940c1c1c0c0c01c1120b0095004541102005010700d18139645080000c00440c13121755182007681012900c0341c0a44194080c461000200b400d01c2414022004c030040c3e900c3c0b03d03a100380c200003038807168400140310681d80c0010150303000c0ca200f441000407100070301d284201c108951100b500300030780c080c2e00480008111207a07000d40c41a0b85c0154011501d50728a8080e80e000c0701401505d000e80e820703004031100000100001c3c070008000d491428540380d0003030158070704001c0c0100301041180898201c19000320f14503054079405420407448504841c180c2d071103070041d50088100303d001c23402d146c103452400c42100a0340c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 520762203 1250 520760953 520760959
    0x20309120105040b1906090f0b0f0d030806040f0b060d06030506070801080307060c0e1905030c0d0c030609151a0f270a020903060406060611190201031d011a 69
    0xc40140c1460508a8100b10b03400350103650158003185004e0300c001d800401451800c80301080712034030340400c8000c54000c190500042c590b03c1f50120100e05020185c0900a071040342d00c0c44880406447c06060640000d21040c491607480352034041142141d0b0122684801c05045542c88101495115000f42498003069415220340b4001841c0c80c5c0c8100d010320705851005000d50f00b4103440d50f9405004d08002d001c49414440c22400000741c40d107503030303008540120300c105040c60070526081c1410709000910510502540601100c0e002045402120310101c9500c6100000c1c40b0324942010110707030288100c441855414202e0258201c0040d11154403805000c03180f8100e803407690420031007002044a1240111810b4003c040703030381c2e83c1145025a10000204015190100204c0024100302040301d007158100c0c3d685405101d142d81c4045204415040c038401407842c0e9201018103180d11a040030000c1c101911181224581400761405070621500f0700d0090100c400000b080204001e00c415007240 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 520763453 1250 520762203 520762219
    0xe010f030507050303190503060d0f0f150b0a1a120a0501080c040e0a03080601300c050408150a0f0e0a050f06061507260a090e16031e0c020309 63
    0x1845284c04002c40c1c08042e010160100c9200584600390303600d03000180b003d0381c40011200c080c00070a00c2d211001590714030450064a95405c2442c0c00e0010301c01c0c40310054503084c544000320800741c0340e103000c000a0f5606540407003420340d8040c0340300c000d0348144440746540000381401d110440d8503582185041c0c6000c9020b8940d05080e00c0144800c035000c07005288a05c3e40007918440c0400c1c0180c00d21a04440c2c1858100000801c2c01b601c100e03003407011414040802000f08100701c07094018480c0d0009a24145069032070300e071603c50410740d10031204004420720146a0041801d804095000c0d4040b00c0c0d0501045c00ba800c030503d0200e4076124012000e80c0c080c004c040001c407050f003000c505681314610041140d107544454402d6442c05400c15001200d18410f40c441081e01540c1408403030002c104502c064664500064800901410a540c41503000d002044203105558105a515030485c880c0d500d40020549175401100c00a5010303064568940352403c103040b03c149602100a05c6805c90a8035820 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 520764703 1250 520763453 520763459
    0xc030715030606020a02060306040209040603080a050c0c06040501090627170105061206130203150411120d0509010c06020714010507031103090606040b031c0e01081e0606090a0e010f030507 83
    0xb980701c02c0e051714001d601950400024507036241035800750031028030240c800601562a5a1898480d40c030540405002c075138085440c800101d0104884c0060a105450503406e091500b4000b9084e00c7c1e0130300503401408196186600d4915907215503040002c050080c1c14282e5a980b110314138181c24054480c0780550070500014090709103035440c2c1a842401500a042c160ba8440007800220380a0342c00b00c0c1d00d400303212007142400465000b001d00960040e41803007000311103c000c0018421503001704e01c00c41e82288100072505508141698042c107030030708110013130390540d140c20b400920840b5001000b40003009080070843d041540314034819156030714100100c0700c50141d0311065002c103c515030340660082c000598541440e400c24001a07501500310b907a03041d0701f0b06440d110200d0141c014170024070004250852507a0203013040307401c614110401107122085491100c024403006040d00d02800700059191580d4807065100c0e8010200b90800b003686584442003902881d9007480195190f200b004408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 520765953 1250 520764703 520764707
    0x1021022115192309010603020a3b0703050606040b120106030e070b030a0b041401091b080609360a0c0b030c04030605040501022701020106080c1507050c030715030606 73
    0x11002101c0d80c0243d8801d0036094800d069000070040028000b9522180000016240c120180c009032128103900c00c1c111483c5500c61042250360764140000c00b001c2d030b02d0300041700c1050324540d4001d5144e1030049501c0d070740c1c0b4000c07d415104651042c0c400090006001c031181c00300d221141d0503a8210394041c804414801200ca0340c9108902074114014002c0001c191442d541c1d038841030350010301078404251090501401000c0c400e00f644589001074846120807600c21510403203202006141c108079441b4108400031409145000300314040101030440340c5585200601039414041c0000742c0d000c0d820120001c811034130307400c040d103046402c8107030a2404035020008030140e03885106c06ca000141414507586a81000e0100904107440d2550308100000c10465044906c04000e400c2c5115031600800c210002801c40f6501e5000581d16004064440c081d80c1c1d0f00e5032802c82d0041c0300d043c03098448440e8201141049070207103040d5810310640c40c00140030388a070f10004000c4d44082e01c081246070760310001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 520767203 1250 520765953 520765961
    0xd0b06042d05250801080105100f090c0311220e040305160f050a0b01030219051c11120f06010b0c12250803102102211519 54
    0x120011040464000c12481050350095a0100d4080b070303541900104580e0f00c2a16a04142c0c0b0030b00040c03130341d10050125042c00d01171682c0051380c0340f10140f00c561400410031007202103400388201041e25030314500e608511a400180461481961996407074000504110040c4004440c50529101e04040043e8030302c40311021520460f0035469480c6800922564101e5010300c915081351280d40c60040d9802040c401c00c0ba80075074900c103603014140e40d415070041141e4180d00140301600304c820150140031a444100d5480403001044003a916a50503528000a02c60030800c01181c02022841d440e003030540e00010004240c0108800b07850340c0341d03220b0280a81d80d1180c0b20817002c4036802000000394401c080780003401500103108501507003224a1030f2012420540140076039140001100384540d200740c108032417000780207000c111584940c1d01c01550841910002000c0c0c0b21300040e40b40c00352011040d1001c40340c80360b030890545140c40c02c121001403000038140c4141c80903d0f0118000107107009244a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 520768453 1250 520767203 520767251
    0xb0109061403040f080408030304032d1707050f0f03150102210f2b06142409090c0d0b042a1407030201200f120907050d0b0604 56
    0x16645190343e940c549491400c0038400841e41e20700b00300400120208180080c50180e44242d450944080b04660300b00918454200100030480500003210405500906081401890030351081c040303030b1b075194050b101402161403c2060001c00581e0300b407050b400320021031003a0344214070240340c42c54404c01280d8519807404031100300004903842e21481644100642055200c0c2c01d0120719010414031035955181c5031100106ca4801070344a81c0b220b081d101c1c0149000342127485400d684000d03101001031b40b0050010011a070000c030300317100c010607a030742c0c4400c5800d00200540040d0750740c1000009801c0b076a00500f0000e04084c41e126262031549407500501c5804540a03040741c04242c4e1811401101c00298014407080c416802409141c040304100035089a501a800008410b420802c500100002d020000c40d9002001c0048174241741c120030554074040ba00b00c1c680d014664800c0c80e01494060a5048146d010001440b103c081110b000c508910950054505100b40740605c401c00c804810f8140c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 520769703 1250 520768453 520768487
    0x140d02090a06051c0218040c080709090509072702070f030e1c030518032409060903040314010605040513060e010b0102030306040e1504050a03020d05090f060304031709010b010906 79
    0x412000303007030a170300a803103200c8050501000e440028000141143c51103104007001c1450340003000740c0030b5080b000590051414a41c28031040c40c1c0301d0030f20b944880742e0380141014007441c2c1502c40c14510b0401d607800186001200c0c21540e400040c1030110324000d940d4800c8001454a101940f030302d003010f070aa550200d04e680c4090011010320340e07040e5075a802001c090700c0d240b1106140310b101940c08201d5801800060b00d103c880b00c103080807190311b080c1402402100b10b58009802c2c8041c41070000b0441b01241c1e008803030f4102101e0761001490140400398822580141080b0500010700c88181d00580c1803803044004000c400e0518000c0c1e802d0b00c101e81e41003400360300180009019414250001da628580e1101600c071030543c2c9455121400e4020b44090b03c0d00d90002c19650105038042080f01c01d0752207242025410280400001052039004a2026014420100c08141090b005000e91003400900d500d142038503103004d031070343c0d070003000039040f580d00080508400140c035601903d50750128000c0f036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 520770953 1250 520769703 520769737
    0x9090714090601110106030b07020c0a0f03030c02150406050307091d060616210e090405030901200f0f0105060a0b0f070c0305030c070f14030a030807140d02090a0605 73
    0x3041002402540140882d062100300c0c25898400300081c42080c010310310503002c01c101c0b810102c0700203241c4a10002924062009140f041c000680d980c0da000007203e134980341c014600d40c500e10200d20000f2040b1000444494040340c04200c030b070b030017501840c841c02480c1c2c2d0300c4c10312680d40d6014840b00c0d510441080e2540b44060003240044c00c1030001401081000c48090400e401e00340c0d02c800f41507503511860b400101c484201401c46a510001121800e0411202d2081508264403980e441e44154180c86040c401501a041c8400004031070500600c0200b8003503580c8804150301403a21903c000d01d840a05518100008240d86002c40350401503c03c280b0ba40c904000010501e10019030001c0d101744e610709210322002002400401c0113084485580c0045c1c003c440c90324080340e84017885600410300c036549007040300280b41c80000b5103856498141c0f41032100c43c2c6410400f6034080e41c9594207000780c20070004074080c1c02078442e0002c1c00d52480036103149a00c55901d100441346809000d903007000e02c00c1d203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 520772203 1250 520770953 520770989
    0x3030a0c3807140c030d14091005040309030b0108160608090a0813030206031311090103080a0c02010306051203250c030b0a0f050a09111f140405030703050606090907 73
    0x2035016241e400766990900080c1011154000c40681c1c000c680c4c041910ba00004100d9400340c0240104040e042e49408000043d04184032030b079450b0125070316405086595030300040c4c01c0c14400c0b40010700545c0c1040c0d40314015610b540c40282c60310800a0744031206822803d001a649206d2103000d40b1415070f10b000b0306800c00c1c040c0c0d1408100d0340701c1030350103260401c40308010026030b80c0c0d10b00550250005650302010300943e803511603001040c903801a0322410443d030041011070000030440d0500b681600d0203010310010362005900030309098200c1608150614441c8556980c0000200701e00500c07103084207948035005031801684c429055006040c0740700490304100064044440c5c0d038012a50a0300800c5030101c09102c201268011100d0040040d200c03d14002880501d10a02e211582d0540da544490a248200641210a80c10000c410071140ca6007400c031f6414800300b682d01a000080948000503a2410720b69900c0d101900c0c0d880c030800310307a0003255000794002107120441e04002c11030180694 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 520773453 1250 520772203 520772303
    0x80325020706180b0316020d300207060f0c020120041203051b0a0201080c07020f060d02121518040b1501050c030a09060906031806090f0203030a0c 65
    0x508103845010545450f20108100300300300c02031407091400240303902e002000628020701d0403c80c06503107400c1c4100f0001c5061111003d41c0c85450384108600c04020a0f80b504040000078442c003000070b80002c1c40e02528502208441c0c01441d84070003960300a2004413484000100244081ea10100039014104801c0209100d0154421809400790620070700f03241040035090440381c500700d83c42100c0e81142c04c00004540e000014550404449901d503400e003212540491086000d00000780e10070039010801007002c00d4141c0440701c240d48c0e458600501401c090b0444500c0107070038030300d65104004468802605000000b075941c8100e41107180041c1c1c0ea26000d00b10601d11684001c454100300082120002d0044204018403282e8016074998003013510700200104500b6603508034400301401c1401d5040b120818a81e0219480d401c0000061080e0707c901d8445d0300094a8900250940000f0800c07040c083d030801e00f079201050040c43c107010707840708501d503032421450541000c201914008214606e164 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 520774703 1250 520773453 520773467
    0x1204120501021b0604020103060b03010b0a390b0703050708071215060215060102010e030403141e0f1005240a0305010501090e010b0d0c031b090603080325020706 71
    0x29008000043c64800b2401c0d01c5200c2e48203520a5007841d902c03040a120031542d140c031402c80180074488045046504010071001c95119038045001041074018030302c481500142c07070003460041e940a003200002c144004914045d01000d00582e00740d140e050004201d98020b0107054803804081e610407405590710031041c5c0c3c40c85211210040c450782c0d510940a500000d52090101510340c0760000d020f070618000c5505841900142800d045904000e40d0085082c0000252001d5a03804030100c0240d403d80724000f46030415000030b20403400600c2100600c90003010401c1152a5481000d403213043d02c4801c084000d559084d10010450740c4010021810841ca04449921140008041f600102e03944d45696003901d07003e030050111035644424984084100b481010420401582da0b4980d00348143c42e000c44411052002801c05e041007900c1c134058940b608070320380c00703441c10300810040307545c480c10050f09035003048900d885141c800e030030b0000a0b660000d5250760031a09560060090a0a04800721551 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 520775953 1250 520774703 520774739
    0x30d020d1d030a0809030f0a05120703020c091519050904290906070e15070b0714120f07051c020903101a030c010804110d02060d0e060a0506031204 65
    0x1120581c01d500301d250340d0a01029580500079450f4946a1400404050821901c00c0c0346800d070707601c500c010200040020904a0582c40d141e0740e00c1313440d035590342030980c2491a601da800d9440074130300b000c201d2904907402110003111000d441103480040d96414000c00100203004103648503c81d080002c0025205405510054944805030751051100450801c070304541a142082c0b260403c03420440f00c1640804d50b514203000448581c01a50070002070080c181c03207110006001c043c2c0b504002562280500715000050400100c41e60f5255580c031402950560181c902c14805200c1d180402c2030103110300f065601c4c0003070003c032821030202603641c10402035000b85452901400303103486008407814144200075840d07001d03403440c0d0240320312101054244202400400c2c10f110b17440091101061481c0046800d0310403d4602c151224001d0002929a000382042004207a0421401413082c0c00082034042c00f86000c01000c2c405904c0e200101070b114450030707110722086502400b0400030044690300820324 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 520777203 1250 520775953 520775987
    0xc0412020406031b150203070f0b060a050d150605060c031c18060f0b031c08070c0b0718060f170a060306090515090303010e131401020a0201060311030d020d 69
    0x159a6603541d4904229000f850241d2482088070780c100811860f51710391683e98050b42c406185840d10640d9006104d8490f4800548841b02c0c0c0c1c40040c003140c44181c6120080d0100a0030820070006d24a171528941992010203020319081c80000111810b085054822001040340614104181e102d41078440340040744152081e0341d114031841c180c2c040028443c0d9506405528085241e25003200300340c003a00d1654a00c0303800f0340c0c0308140c89150404000d800541e4070000b440d02c60516250650106e0b0140d54580e40940350313071180c00500032855004003c0048545603005a41c0d43c0998501050b40d85102041c00c00001c40c401895583c040000314120540c0106150710014009403680c403044100c49010000b141c0f654810184050000c0f0714184155001007184c000350314542c1000194406d400c030180c80180011090503600041002140c02210303034105010003151584110540280641103078032080d2840350700c102c540b8400c1d040c045805d40005a4980052081c401280310071104243d14400c1410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 520778453 1250 520777203 520777211
    0x5030c04080708031b0607080a2c071d06010c0803310b070c08040902130f0b030106120213090e100c0f0e0103140c0a0207080604052406010905270c041d0c04120204 72
    0x32b441f0304100042c068400e0f01004200460510484c0311251030700ea00c9510301180301104012890380d01c50440342d0784680c050714044c0c81e900c620501044c1c56024010404c1c50030b000b07444161490264805044496020f80c0303084041c0c1e01c0f40d4130286c50035104100d0141a01000f00010b114800c00d9030010081d82041103622a4a241e0310064540c4100d400d40000300081d0001004205030b03070748844100028409610111318141c2030040b811510f0009101d04040c8a0f1524036010420b03c05201d03000c4c1d00d0807003803001e21440c0c1020784020807010303009500c040800d1180310580c40c50b520910507490403c00c070f90801c41991f00c800219101e10303080410b660b01148141c120109a8040a10813140610710400041041d0b0b240305200c041b034110f00035003200c074204a200410205a80c44071003070301110015103c00307031001150316040d20795103120210743e0004185401440320150303a08000f00200c903104044155100c80081e80201c0f41c940a840342124510140428001c003a040900c9028031407000304006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 520779703 1250 520778453 520778501
    0x130b031e150f01031110020a020f0d060f09170c0703110f030d030f050a0e03181c0309031208040c0e090304180f060b0c0d05030c04080708031b0607080a 67
    0x35681034129a100d0b1142480c20040081000903a10111542c4080320300d001c00c0e07805100001c0d038803008900003a1180710480e5001e816a01c03a0071081d421320703030031440c02e10450b5807201410014000c1180100c440b81111045154182e04030019102c410034540003a0682620b07581b82c1050b40680f00d6003a90b4802144de80c0d41c01c0c00d9401300240d024103955610041003809448000d901203030001058401e04c08e00b8240b080700c1c00640441250b01c000c01c84c0f940508080300c0e03140811401101d08a10003800840700d01803102b070640050080302104d1090041106000085508072884030080d140100680750303001050010311000c03e1259804840354003100d0030190303103000c982c080541f00d100ca0401c141c0d51b81105402d02c0e0460103050094010000010725000c45e0130511940c45c40010701e038000300003010010400c00e19041c0f044a00529610040b1072600e42c84050482c0c0b6030344894480700132010604000082550045030441c45504580c460081ea0b5541c9454071001e00b925400c00c0911310b21421b040c1c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 520780953 1250 520779703 520779733
    0x204050405130605060604030308010b160c0b0903070b070804050d060906050406090b06090c0306060d020408010207030201020a18030b0609070c0b0f0a0f06080a030c1e08030402130b031e 82
    0x40d40c840c1401c204074007102c0c29181002c500303c0d0405401c640c041e180400003030000c00e03001a880c2c0c0c11944003604460b030703c1c039100a41c0311040110800081c880034140d000004d03c01410300c0904110740046041d1f403001c5d59203120380401846881c40081c504031080c0010416841e040520030030f081d000301070104904425945103021100200c50442d1004c1d5290004418803502a0340c2c141e11600954142c00b29081c034601407101c5020041155120300400954000e82c4001901910014000c2d00001d54840c0020329000c0d01135081144c2303443c00141c10243e50140250004080170459800281c01e503402e072503140511031250700040080e400c2c081148450000a88086144c81c8541d481256170500d034240342552405035511000540c3e48241080340c148400d11010646081036035141c14038120214041c503000c80f082e02040d0a0a42003041d9960000030700c04043c0056114603c00c8404120841c80d146c0c00341e04480150701910703050346c030180c0e07102d06980880450040380350080301101c801c41002d02103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 520782203 1250 520780953 520780961
    0x315020903151e010503030306010206220827061204030c02012d0e04090c0b030711100f0f05090d1d0d1401050106020d050f1309050c090a230d02030102040504 70
    0x3018480d2214485102d0340d401043c3c5480c0d024140840203140341d410070200003503403090040c1440d210002d000d0409039000080c91401c0341040c0c2e10202c00c2c3c3d00c1c3d0103031800b5000e8100c44e560001c0380301424211103e44604c0e150301114178400d09021510100d4459032012101d50380c28803000c0341031250400404406a400304001500141d042100c50741d801d075032070b50080c0300310031203a03406004504010310b0800007022402c4c80002e175806100072a8a9030f4070381c00110350050b85120a00468028813580c0400d800d825041030b00c01d0760000f60306011640a000f0200119403040b210110240c202001d80400103124070600c03021451880000b400e40d21661000841500610701c0c111046102100c1d880d1842c1c0e02030207454010a568006070050312940d0f140902144103469524504000020b0041e0401c040713407844802411540c5010009480c10900e04071045e400503601f140704031540040001c540d498480b8540f075100720a0340001c58400b9402c1400859122820100ea255400b400003080d00e4450740300d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 520783453 1250 520782203 520782211
    0x706090f03181202010e040b09090a12020a1101030c030608030d0911090103080703110f01150603140105011b020f03060f25210e0a030302040f050406031502090315 72
    0x4551200c0d1a6545800b07008082c81c91500300c5031000070706040241128410440c20038580a00b46200c49001020000d8000c140312854a03500500346424080301000024030540c001d48240301ca410b04842184044c0c1c0d4138010750000600002c00c01c001c2145a5102c8d40006000b2981800e01107070b903031f4941c0034131410b54120045640d603056442c08500240f080c2c803151104140c00580d440403555040d9111817070303540b007044e030082c0a01801000188100d04200501c00c660442e010003005807403850983d100c0406024464240002e09140b240001c052003074980d01d0403144142c454140d641c1c01c030503070014407a2001000340d0780b0150b80c6041c0039040d00c09004040c03161030002400d00f0305283c00000720044c0c48851202110705600317101e04000d07103504010640b02c484004c01568a640d181403a203d40a0198015a84418090201d1a10030507030140c0240041d1800c80c500c1e000e04075150004c0c80103c480034070018000e4091401503845140d1161700034031802e04098140d030340b50001d410890803220400e0b5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 520784703 1250 520783453 520783463
    0x11010e01020a0e0f06040501050f040b030420041b0e0a0306050910060b0a050307080a0b0d050604030f0c02010509060a0905030d120c0302030f0f070e1e0f1017060402070609 76
    0x5060011964480d43c0e1248aa1045503806041010500410040d0103580a03860504c8400a0702201c0c803940442034400414030003842c6a80d924051401160706420354103940340003004080240580c0c503003406015550390064520001c2c0110801003261140c0c00d1511a80d0840e06600e00400803803400e00507548a0350115008025440c00703005013500301da0b810351020844100502131440c800d5800801c80b60406164941482107844011481c0010690f1481c1c840e80941d0b81042101040004641c01d841140682c54042401c5c003009401c1d540c0982b002d100a00007003041103042c0c520b28014000e0700e0f1404480c60100d00013926280424500441503100c04007081d16003140e01c1c01d01000d8044d0210204070b9140a41c218105100286011031000c0c0031a50007209030000218814801c580c1000c2020000b480364040d40e44c003900b001d461400c2c640c401e078024818907107161014140914045101200d13503485078030300c8d0845800c40d90f203480c0c0135015550041c0c00b00040d001040d070354081d00155901034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 520785953 1250 520784703 520784707
    0x3105010e0a0917090312190801080606011b081306020723100c1b0f050319030804020d0f12090611060712020d020904020c010b031b03060a0c11010e0102 67
    0x106114622500006000311002410302d9540e00c005448076005000301d00100c6032858a4407050b0340080d08045803805031600105020915001010900c0040d05010956464885280c0d8a40402c980c40754003c40d480d5022448d01c00d040d1000031078220010710700d00d0085282900f003881c0c1003120726025586621401c016400f00c1800d11441d20302c0d0116200716101d05000740c0a0200e50004506101002980e85040c030020712060740a00014284010300f204003000d400d0341c11078a60022200d031500d98014a8041e01c80c0a502442c10017080400410854040d10b0300c0910340e4442c2c3c20403080c082908002c0b07404141d401c40c204001003031030400080e1094107441d00320409041ca800140b03e2007104071050b00030b601c00020f0003275041e0480803c603d01100c3d804003603512000b11410b0000ba11401c920076030000d1002440191654040d03204540b0000110103951020381101c0c0342038401c121800c48154550088408140744141660003102c5046007410800c010480c441d80150071109281d0184045c1e0b500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 520787203 1250 520785953 520785959
    0x51906180b0919050d0806041e06150c17070503041802030f06010215010509070212030a060f05010203031e1b07050f010c1701090c09080a030903020f01030207050309310501 76
    0x2030100030584140f12141c8025100b103038441c0356440610b202d000040c8452880443c1c42c585881d0045100b0015240f90231044034190107488005010300c0c80b03565205640c202e040c41c0924850030440d103216404c0500001030048030500002941e0001008030740510003000b000500055076403c2c5040803c2034480141c0381d02d490741015a121000501050464002417a4503403402641034a0303d054800c1076032050410342c0c684005030719240e005075000d65210710210402c42810312541010044d00d0b9a040c0c10744640e44d903003005983c0c0340010b031000c107101040c2021407000c4040154000368005010444880c0d0009030384131516695200007410707607042c2c1140e150002c050a090140151800e00c0e490a030007038080700c103031405075a00f0601500040070303120100c640c00315110b004c1a402034010207083d030f18803041d103140180c6254102d1008a001c1c8084800d60540c4d580207100380c03a0700783e40100186180c6050380041223050a1822404d10200e4180300002000072002895052440c004040008003541 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 520788453 1250 520787203 520787221
    0x90a0c030605060913050a03030506190b040f0e0f150103091217010e061003090c0323010606020118030804060f020d0e0606043303120306051c051906180b 68
    0x30004015590305802c620081d00091b0b0b00240541c0480d80528002950751501000a52016401070071020403404c0080041074482205008100700da9140d6011060103036100303a00d00441000329410b086514002c00022402041d650007807484010501d800100720300160707540784003400c030300b840f550000c0c02d10700b0049043c0e58801c0c440da024010210100310249080e07400151040004009507041544401c01e01040042d514120006940d0156030388010b0361800c50200a49000e07210600c00540c01d0031000a440d5006102e00818203840400b00201881e00751825105103501500803120307140c0d951a0a07001c40c02c01d2002c2d10290007c00341c0480d081c401412140d19044001d0115841240380c010380c06600c90b40e040d0500a80c0200081019000c2038081d09003000200941c00901403801e4142e0007100141d26920060564104887c0c0f000365a030b800f51034150507111103000411940c058032038441c0074000e448040007014803483c0040782c40b100d59542800c205807080c40c11503290040d907040c821469 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 520789703 1250 520788453 520788469
    0xe0603010e010b130908090414250504030305070812010314010e060609060d081605030d06120b1807170102070c1211040c110a120206100b12090a0c03060506 69
    0x3910307070303009020310700b0290f0000b070001d0005400300e80404c0c1d031400d128017082010310941c0d100100041c01003120054032660740340d100704115003880000c10780d4014080c20070017562901030b104403144d0b02c00f0b0925041d61790a440c26400080f0655104500303004c440e1840344070600080c080c6200f00800c003640c1e510f03000c0c1103007500c60b160340c03010a5402407403c1004507160f60303180c00d510060131102c100504007030b0b042c81030417403203115000341c40c11145443c0141400300003c000d08594620300303402c001d100c0d999050888400002e40c0014401940440407070703460b0b80840c0b0b540303000d007a0400030364141b40d5031107a03007048240342d079400031042e81d4020401d60300303104001400800030101c03a03000ba00c80e500c81d035443c07140e00c02e2031204640c401d50343c0742920190144214008950300c00910b00b12007000c01c50f4280400f6680b0078041303000c010f02c62000000d02000c4400d217603e0441e0006603a081c2850400c04e41c644007030000801640b0644661014800030a0041114800450081e24000340fa8140642440045 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 520790953 1250 520789703 520789721
    0xf120201060522060f0b03150f0d02100e060c01150803031909030e0603092a06070303051e070f0807020703240605190608250f05070503040e060301 65
    0x26925120081146850b0b840307061203403114004066504600c0c03050b480000f00016040139651102050001c0303160701c0c10100441c0101440340030303959005484002c008001c0a028804c0c1e4000d510360f82c0250040c1842100170170a2903680c10036028115101010403a10341203190341580380e030345511036a0400c0d41000010000f44c44080090b52840c90500041c5809455200d4240d200c51b5946000c0b00c2814421100403800c182c0c01084142c4e41c1c189104401e0307580c52825141c1055000803072002400b07801100022000c01e001070686401c0140d546c130b040c1c0c02808010020420321031080c40300c0956080d000c48191141c0d4041d15249824444903000500c003000c028074a00a65200080c14404100b0080c801903050210250805071209850018009081c0a0340f00c590000c074550710201030300061003a5203090b030f50309a03034884a5a44555154550108800032210a041030900040400348100c610f0034854405050a61400e19070b0b170b842902d550700c2580040c1c1001540c80178006a85170038002e544030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 520792203 1250 520790953 520790957
    0x50a03050f0106020c090c1c09200108160306170105090706080603060103060c111222050f040903021204060306210b16030e060906060909121c180f12 66
    0x1d250704140300650740e021680c0e19a486226154000b50300e1440c100115011200480a00c28452a5059841d406090001c800701d58030b43c068940031080c0004111a0011520145d44891054403404003600107451014000c0041545406001c0343c6044000c1e000d1190b00d0265000169901d4295551400c0501c42e82040003084100c0f003c1c4466680c0000c0c51606494100000080350306459405450420080084100c28015140d00b1a101019034010781160b17403504041e2400c2c1764440804014895543c000c40d648549450007044c0c0c141416800002007512034011a030300700305c0d484503440c00d60b0440da1222000070b880e10780500c0340e21050070982c000100d00c500d134140a000d0a54990f08041801441401d41000e44902500020312981044030660090401d48040e030501e8a00981c0f2100100c0b00140503840b4940420310b02e010015000b1800301e80c60303c165040c00e540864005038a1054002c03401c050307890b46a0444c0b05480d4210500c1410b200710b03880080040706181c004884800b400800d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 520793453 1250 520792203 520792231
    0x170705070b09310c1b0f0c060309020105071b0b120105100f0507030e0a0f03080301080f0c030616050702040f0209150a09120f0618031e050901050c0c030d050a0305 72
    0x50301c1d003a02e0030703038680f8a0643d8201162900e8058070031940c1c410303a039107904030018030020907a0500140b024041480380c01500103d01a64484206405031940e0080003400182c041021001084160317508501c041162050b148281c0c0e564460751091ba0007808903100c5928a01004000c90f240510000d80c070240141080c2e00b1541e41203001400300e02034180c016040c80701c00205e03101d6541c1e400007408050118015019041d0f03403a810014040d8209028145503889400000c92000c5c0e03000801e00c02e00c0e4001402819250340e0424401c9000b2914071007842400002e1104000598880c02a141c00c0701e0800c000580f20b004040800c1841406c0140f0301f1743c80e9070300700800074140b50322000c0101610807540c02e0301130324142407402034403503038001d08050406807a00c0b0007402e0f0800514802c1c03803114040c0e81c90300c0c41c099081000a9003c400d003186213020420401c99400d01d035015001808600103008182c454400c03407500400c1c01c188030340994000181d0b0001c0c82c1403105415200b06604484002c20300700d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 520794703 1250 520793453 520793509
    0x180609050a0504050a0f020c0106083c0a02040216020108070c120f02031312031206081b060705070906091a0f091008011109040f02090904170705070b09 67
    0x641c08603258003820b409940c0b541d00141c584503c40c2c200301a407500110b006c542e501c0103064078038000d1003103020f4003400740541e16910a800031074202188460b10388000e03039560f01c50050703c02c0349070030003400390344030540100103807100903903a184042d040030b40311031815400d15642d603c00100756a03001440c01c01803100e01071004003c561282030100c0921103c1c141170480421181e01a407a5003d0b00e41a0103104040c001e0224921180032682d10007148251200c070041181e0900c01b000b82d07242c80c041c0c0c02a940c09035142641e1010449010180d08802400580c43e04406444050800d5410f030060001580c0303d403020482e5510603c5035203001403542c1342d08030711461020001011320050b094960b214603220004103422400e0341412000418043c4020081d014107481d04078644e42007244c155125a20301031020034141c10b00d000304d812010703000b0410312035a0b40350f40d1007115070368448841d802c620805101d0000060403c02c4805d0162400031040c1d40c5500e005004c0143e5544403490008071021700485003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 520795953 1250 520794703 520794709
    0x9060e06060c101503020a030503070b09030304200f0612070801060c030e061e0403060605030d090305150714040603020301050406060509012a021806090f0112141002030718060905 79
    0x1048043c070460300003080318400d0441d07081325060150000307580101209000001c00c98004000e2840510503c408481a507a1400483e128002154007600450602103600c0782d610100a45a100e0b1000516054140d800b0701c000c0f441c160402e40c00802621502018081541d8100318124010315182c50102941203507940c000307003a5035003060740e2409141c011801c2410700c2070501800c0030000501c01915180c4d9524201034010f01114030541c0d0203401480c06004203107105040142c00c1e2030300040101000300f02411303e1000b516004040303034104580200180e68200d4120300420043c01035641c00740c2c41e94104003c1100300c1e451a8801d0041c8030781000b181035240d80142c0c241506a440002c80b60300d01c20504110160480489070013540421088002c01e481c0140c1d0f40e030640190070079035003403c113a03951403130704a0048420300a10100c640f1659003103000440c1e0000b031408023080390058070724a0402c003078414182e030400d45442011403907106000c0d8660445018100c01041d491800071251403501e004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 520797203 1250 520795953 520795963
    0x90305210a27060b04020d02072405060603070e0f03030c01090b060d210c1e1a150d03020c030d080105100f080a0e03070c0603020c19080904200409060e06060c 70
    0x50040d0388401070303070f0110303501e075419aa203201f820281503586001601d068454076100c1c4511a00070315140242c2c42c0344101d1803080310f1083d4400341c555451502c40381d6080d500e06008012007070f803142c80e9120342000c3e40c03800d00c040c04810f10180d00100f00036610380f0308981c2040d0000d0019010f181100030840124100c1400070801c45401c1c0714076a12807400e880100c9048041040242c26145d5105003002001c403000c104030f000324050b0550400f003658a210400120106880c04084643c0280004003607207081c540c03008020780f20b4011a0022001d440111342020a0a40b483c004250000010400350400c44220314245000d0304d4074442c60007a40342c010303000207000b810f00386040d43c0c0e4028404035228104200d82c2e40d150000d103420995039a50b14014081d5018918807034450003041c41e02000e200035500284500c541c072594181c02c0c018040c00348001006040c1c20051031a412280c1031010203002401000070b8005040e02042c0c0c242410200c0020b204047e00c4140031f010100710790b031003108010034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 520798453 1250 520797203 520797281
    0x9062a050c19140303071e0c0b061012090c060f08090712060f1d0c0109061b06140c0307180b07060903051b0a0b0622090305210a 57
    0xc00c020b2000c507241040d5055440710061507200c2d01c0004281702c00715400c600e4501d1000440521440b209902e140304503103070f101201c00205124005404101140342103400d6004000c9680f03040b00d420201030f01c2c14000d40b070541900b507d039030f4410f040a00840c0d510600040340000941882c81c01c0741011510301d6030f103800e00e100c0c3d545000c000082d500100f02241d0012841844081c10903c200c0b4001000013041c040484010100b5110b220030182d00b07540180c4508003103d4132030300c924034400030015141480e001c003000c00300c6203d50350701e1000280c0002031032458010202c0104480d202d240c24500034000202207030356691036800c4100300700400310380d11007180c902030f91055010501074400d140658550140144c2404070601401e0f201e12104000118094003d0040203800000d84400e0140f01c402d000744040544414502003d540c2008540c0d0004a1003a110713180a83c0340603104070170980e5020f62110451a20035508040c0102ca81c002d010380f00c4a08898a403040140703500386c5004e00c080d50003030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 520799703 1250 520798453 520798483
    0x506040b0903010f02180a171504080424030f11030402010e030a06050106020a050106150c141203070305011d01050906041802030601030501021210062109062a050c 72
    0x5401c600c0c0e41c80039004400369080290056460b0b4520404008098071b01c248034500460010400240c0d11760300c010071b80e182000c00070243c075606400b04c4800703907141c4009105039030192040000003902c0503074040210001450308617000c101200020010292039959500954940c10701040320141c1e8071280c212a00250309081c035004081e101d101081c2808004000504001e1800000290f80c540110381c10118900c2500200815a210301c070200707031450f0b503040d40300000d282c1e144d09074000b89c5541c10346c080501401c0c044a50000e03142841d05083e51048810b0710010b40c1380c1e401000394558201c01d0300500d450002203200c1560610010840300310780102120310071610345100c0460b803108010324158558002c0c0c1650049d43c0c4904106000c0d40c8030404000c6da4445600004150308803003101c481c00d07511a030307a800c449245c500003261a8070701c800400c0f0801ca543d400301240011480c1c0b1480e04400810300b0301c400340004085e200280c0003660700c0303c0e0b41402420082017104c480003152821800d0244 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 520800953 1250 520799703 520799707
    0x101401020d031a12010e0c01110d080603030c010f150501051e0f1b0a05190b040b18190c08010903090e0408091504030605060105090112200d0e10060506040b 69
    0x10303250030b1040c83e107400082d0707030030100b1051081ea4140c0190000c0004803082000c03598030060703001c01162481307241d0791400c0c11070300141059217000340f090100785e400c010002c007124100602440410300319010700074400405e9a803000c0d50748081206a591a00a0200b4203000f8123180585007040c405030100d4101407148a00094508510768a40040d660861103506804134041d401d450100e95035441002c0171303078070303846110482e00c00b1900c01c01c8801030003503100541c083c00d516160b41d0309521030b0001d05181c0900d40b56000c0c04030020820003424a200341c4000c0f00c0c18104159051070054a4542e41185c181d0f43d04241214000c00e4009042c3c50413203100d801d040c851544c441c02c10a8050103002076490380081c0801101c604441010060002e50380154420080358030703040010744191061072602808184540b4452140d0300f015803250051401240801740f6912080440b0f141c1a4090f40751440f5540c0e0f1032809190580081221203034158840508003e000d0401e00055250301039882526250040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 520802203 1250 520800953 520800971
    0x306070c120c0809040b03120c03090a080106060212030601030f110a0908011817090918100501240c080309100e0a030c150f050c03010303080609191505120105101401020d03 76
    0x10410200d6002c44c02e03236034103d07202e0940385001521395103d01100e5110350420382012440200601c500001c4441075001000b44041e640c5421000390030041000d03062554804480170210f1a07400307620200c4486180303465070303460a4070000d42502d14079009210a80e00d44030038003618064603844c0342c420b9500000d50440c0e82132069101e020a2281c082c000b40c0010029051150203038402e1600260103045405072030b1110f483c20703085411078000344101c100c4000d0f00a06084640002c400244190340503150030a03000c805622008c1c1290b2003694260a20303805071112560038180c0e4859a86040144000380051681a45005080402c084005469601036001e410703641c0c1d483c1c1d4828100c0a100b840c0910452815034841000307070300244016800b007651400001c50780d01d4040340e4070384290266200080d01c00540744141c0020300c4684582045d07242074040224003a40c1b0b1111a00343e140b1040d001003640c0c504910701e0311104c0d515500050b2000281070301501d65a80202d07094a1b141d03214600054003544c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 520803453 1250 520802203 520802209
    0x21801030b132303250f020d051033140603100905010807050907030b0a270e010912051201030312061e140f06120a09020306070c120c0809040b 63
    0xe8611410020102e0788210040240f004c00600303244910500488030f00400c001c5550a454000345004041c09800710b04040146070000b040252140941d045907454400004040101c0d5207035102c0c4902140d0b40c00440c0d9403101ea040b804d5010002041d00d04c2840c3c0d141c03480d1404141ca031500c2c4140310b10030110006d10913078031692515000746000d807000d110300e5031748003013560700d41140e8020076014540c402c0c00030700f100d40a40149104494040d103240b100034544542240801000c04490682d07458060b40082300741058020140400d840c1400096000a1443d103819260100c1030384c80b05005c001e211010201651003681411a40c050801e0807500300800349140c01800c050700400821300540b140320800c01410380a400541d1030041c07040030483da10f5000c000340b402d81d10103001e40c000e50030000c00b0b00c202c40c1700041c07542003404c2c4540840c209003150300180c2001d008440030400650508105030034007243c881c100d01920f503036003482c03030008035961107840061140c1c180e190f02440e114160355046031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 520804703 1250 520803453 520803473
    0x7020f03070b0c1b0603131403070b0603070503060c03180c0d0f0b0f010f090f0207210806061c090f0b010b04080c0f060a0f050c010c0309021801030b13 67
    0x410060680e07030581e40326024401c0035040190420300ba0310403d4482c04244e030f0400480000318100a0009003503980c2c4410440e10ba8680342d008a9a002d40b90080f540d00c1d100400c060880c4a20601c0d20325640d140850030301d4501116a88050301c03076030041c424400c3c801e480307004490f00100c620140c01c90710132503590901d1619800d604410f130080801d036908d00038800b44400349820b49114409068450312800c1180031407501c00e0055040d00031003510200040c640941c000c08030448505405414140d0513200c0d00d01c5016010340004198031504010460250f00400f5160f120008890250078560400e11604460000b2038035104c4566030b0309540001d12150b584081c2445900170075080180da16500e1940c61074001d403194210138401c81c1042a25894004e142009801e00a000301d403d00e41c40c0b0504440103c40b907a400c0c41072200822001d000038074203000d204100e075018bc1b00071583c0a498418480700c2d8010400c14810021841c1c01400040c6860034040d03000510290300d9240b004407420425024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 520805953 1250 520804703 520804729
    0x10c080f0c090a06050918040c120302070b0406180f030c170f01050c090102010e03030103081801050d020406030618020c1c12050f04031103040806070516060203040510060807050112020702 83
    0x40640f620001039503941c454001d007a000300c103032410125005001c078289060f04040d03600030b240d00341e001002d000d945004680501c103580648100c40070320303540d00a00364103030740540c2010380010712400041d40100c4241103500002c201140c240c04c0c406240da11a40c00308041c0d405071201c0c0725680146003440c510204200d2100c60b001d00f000f0030050910080390500741d80601d00d118090f5080658103084800302000b581c1c101c94000c10241c0c5410300200d0700442d02d6580e032032803030305000e014400c4c0e411908091010700003900850310300003142405d18004400700040c054580700414010800c1001500010441c411400c01411003810b0100160206070395901001003404c02007843c0c201000820a8441d42d89405280661140c1d40b101030000c2d41e25803a442240110034969100c5004104001e01c25001082c91003000c45482c0201c1240b40d540e2400d03644162000d0720541c1c4003000900d4030342d120b841541d0040205400401c100b905d0000081d00c01c1a100d4003c13008590f002c11228155200c1c40031429107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 520807203 1250 520805953 520805959
    0x103061d040b101401050f190c1b14060d1b030f15230402040b0c030301030b0708040803011202131a0f1e01081509190c0c0f0b091c05040302030f010c080f0c09 70
    0x500c1e410002d00900c04c81310300105640103806580070001c01c0811000ae01c0c262100d00351091038106025090124641c0102800f5200658070030804081c3c920110b440802c20744d00e540d010582500001104c415a0900e40001c18004550740c420480c02e02807148101d100d0710806080c3d0380202440300094002c0c01203501403c03501c1000180f851070400d0200044d4182c0384560380010a50705c5012048a04503c200d500412050341040140181c0540f84807201141348002c0c075182c00b042c800107606064445d10000302540f440107040c3c1054606d030a0300500544901541c0559010303c19180880c0f003032800544007414040560085651075000e4120804000e0014240000c2424803c0345044844207841081c01c07020f1900301035003601849014600005500441002c1f80404a522410303418075018cc211000b80c400d6107070324041100a40b060100b902e01079140c6640b035030306c1d600605080c218041031800d00c991401382e82050240e041020315420154010300401b1383e545034110f0f0040342c41a540801e074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 520808453 1250 520807203 520807237
    0x11060a1e0c20031c110306120304180e060702060601050d0e120f1c09020a06142a0d0503010b0a050c0f16030303380103061d040b101401050f 62
    0x500d401c000402860005040520048103c0c900c4d85240115524090282e0800d0005c1010607010b10f04004515000980d80040d00d00e40355179200e02007802c51645049807040c81d111640307003c500c0d4040c000503074040f81900107400c0600c0c210000801c1c40c458541e5141583e9a10383d040c00403140104080007100345244003069035050504052115a00010041c0c0c0c807a401e41f04500c08410041d026094031542d010705066030b4142031010561f0144803902c0002c0808030103100c0000c001c01d01ca40c0101c44015a0701c220258403808041031070030903405d05108420300200b00010480581c0c40c504540300551585480c9440c2d010207170900703007030120b15040e25019106901514490403c025030303000c203ca102c3c1d1010050742d081c4c810083c1c84441c1c41e13005d64000000180c900b0ba1006982c0340d10302c00324101407400084d80740c4c40d00da0481000800e241b01004160f958020030041052900c034007500070500482a460307151030f08050400c01030a0b0f105103810071801140c50135214001e942136940840c8542c060300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 520809703 1250 520808453 520808507
    0x708030d050f160504120807020d24090506010515040e1602071502061302120708150a0207050718020403080408060a0b04020901090509040c050a030311060a1e0c 71
    0x84007501c01990a082c480c03950328040380c100c18003440291840000c1c1d40300c20741010b2512500a51005c413414007502c1c4c00104002403030040e41e40b107009c030542901c40e520490741c41503a22802c40302420510164610207141034542404164000b602d981114400ca6005080407a4042c24003228001c036407144429111280c20f02142018124404450a20070360031602041d03034500b005d022000900e1001005a00084080340c100005107036403410560002d407411401400840303040780303440c51691201e000c81d0441486580c6c102c030b200705429000071182d0800d50420b001e50321070b00e40b1100144615a2102c0000f0070301500380721640c06031001580c0111000752640ea40d185260303202d58040301c1000a00d881d044032090185040e2013518801c1c0010303942d480b0224108801d008035a00043c2050f5a401d00803c0c00103881e075a07007980c2c0c8020707521a644100211421000d95460410040c01943c041ca00705410b803024007104508910424000500c0810301c1c20340718400391946010142040c035401805c0d1040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 520810953 1250 520809703 520809727
    0x4110715022802010b0108100e0a0b0604081b0f030c010c03020c09100501021005152215181a060304021305010b0a1206180e03130e151c0311070803 65
    0x70030b2820250782c00038050690043c004441c6104126482883c7c00000c48050052070300d501081c90703016101820001d0240e43d00340000d89244c1240d8440702c03070750740021181401855441c2c1d40b455031400690703c01a040103014002074540708680d1381181000501c5016409041c0300f00080e40c1091f401602049103418140440d4205164502070306001d0f2190195406130b10310300b442294030030315400301e1a4a00c058103a04122070452040c0a0304003110b5056000311000c25903215480d48031b0202c40c2452242c92405801d0426403462188030b0403074514000034824000005403003100c0b000c400b11450380d030b47e0351a071002840265040c080b08140314541030000c286490103900030041e0000c2a100ca880c05241600c0060681f4000c1c040c60110034000080c00c0b000c090780c9c1e00103100701011001034034181031178800c042c00300168581c8010407094500d030602055090b4040141034100e8203850359101480007415482a20304a40f030001c0030454880c4100554145c00d22810340908004015680e80302c03c101d1203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 520812203 1250 520810953 520811017
    0x30d09050d0e030307051515090c0901140a05071b08150a11090a1e0b12041109040803070c06020409020703030b0a0e100b13052d0411071502 62
    0x812000c500d140c1d42c2e5a200d45000019620190750007001003540c101080741c144075450303000d4068500b00940180620699441046040c40b5803a541012622403904900040265804512840c03840800b04603400c2d0282c0e0000444041e10340104c528818404080700481c2e400107158403100b2940110707000e1010411402c1d00c12402101a040140a00042c00e0311034a8540b2902c501550310400210f420000000d80c2c0d0702c0c0c6010b80c401d41020b2401750759651580c4c100765000f0324500401d010a901040108540c4e0420400501d40582300d0015501d09942c1c0e111640c4000b0f8801010b01418215030b104002082c1c040700c000d0007001405540f90702c8140f8010f00601086411036128264010011a02c900030b032401c140325400140302e5505042c50701c00700108690001c03040c880c030360024010110305600c41c08020710762118080c50300e2907920048101d03084007884144d1203d2141d4209101c01e0385041c444016580303000e4028002d0020301004030243c1d8001d00c00da060050311035185a0b04401c60010200e5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 520813453 1250 520812203 520812223
    0x120a0302090906060405060417010f06060c03121509091103030f0d05010b0903031c09020901170610060503010b1c060e0f090106030f200d05030c100506030717030d0905 74
    0x1418080341c3d01d8540401c034450045002d00360b003111050008000d00400304d807050040007880300000070010101249901030b504990007440114030030000880030542e012008a111a01c009020400c040c0d51940c19000903000780704e907244061311465680180213840d540442004002011a6901d00c00049452500d40007666540305207407400c1c2c000201440c0c01d904940d044400100a1441c12080c40c5a03c1100c0c102d101d5071541c003c0d56054031800586a0b449140c0c080d1501c0c591440c8280360f007104103403600c04001c01464044600100800071203800c0703c140c90640b5120303416103444229441d0030204c1c024840b14102d60403418448000354030103000c4061406084481c1d003404c0c1d0340d83c2d500101d42c240d0701d240c44010001507034039040b0400306d10341740800c00c0c0024000d41201640032422000580c110200f1a0540b02d0780c200080300705142208011011181c009090103200500d1b106000940303030f84480c0300300070045107500000954170009004a0304410f00b41e1030200b000501c0c41c1400382c1d80e520034013 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 520814703 1250 520813453 520813459
    0x60b010e12300403020405100e01030305041a0a1e030f050f04032a0809120d020609012405040c02120a09050910030b16021906052502070611120a030209 67
    0x590b00020400280c0701458124101d0011842d1a00d190b0a000040c0b1008080c000c400744060000301e0f808813880c10245c0294003035078549440c0c90074294008513040c00c6020081d04d10208000c24500550450010800070701140f00580c072040c01c4c5a420380207481c4000c0c3e029410382ca0308003001b010a2440030340c0c41c0514065564000d400b4440b000700d2841d0010a40c580d01c1071081203a500c80080c030108024110200c000c2c0290280100e40220180b400c1c403c401070f0000742c1c00c0b1504004500100340700b44c1e00da141181d0178014400e02c4105c110390400c44140215406951a800050031440c000c00c2030301d6660b802100310503590250707000c0c0200448101d0040a103d9050384010400c490740310705c460015640c00a13214941034484842d804c1402c400c0c00c20100541c0103080c025030f6690039261182082034002c8002060a1911040d100c007030800c03141c401c081520340220340c83c0303aaa84c001103207816a400c03400c007582c1e0303210502c00480c0307028031102412a0b4520009980301544d941078002e098258415 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 520815953 1250 520814703 520814743
    0x105032a0d0e1b010f02120711060c0c0108060306061e2701060305011a0d02090a0e010f08010624080405070305101406010201050405030d0c14070609120f0c060b010e12 74
    0x243c0d0044500034040404c000043e400721218a01040c2500c00900c5914811950303090103c4400c804620b02d9044000c0c201d01d160003a240c4001d06507042189107502200031009088503150030400a850048044284c5580303600d035010070201c42d10b030101c01c815800030800040340500c0d06118116075110007400740300006418040005035500715071040928803c030040940782040030200034a0000d40080888036031044898100103101b1745030031919400b0381004414085030a050660542c01d40d4041d510402c00c0c042020500f00209012280151003041185400d0380e4940360350078580e142000540010780030340a0150001d607002140d81c405840d40300502109011507541a005900b2640100e0f40944a50420401c52700754070440c2e400103a210200b070810b039140d0540c0552070b025a0700504002c072030721035464403268203014000046503c9a419468050710460349070310b0083c0031340000c8000905058036154501640d03030145403425004c00c4003628010035403545501065689101740910304081c4e9035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 520817203 1250 520815953 520816003
    0x270a12021206150d08120a0501060207081504020613030b01080319030e1509011503110301050105060307170402180406060e09030909191b0c110105032a0d0e 69
    0x7000c90154850032a4002c281c03000308252003409540d010036a41150030982c00c000c00d20750039604004030350003400c140310300054640c10407034080c0c58008680c1010a4a5102c51010088840554031003940940d0554050740c0306d0a00705501c4c26809000e400060ad0700c1010300003c28080000030160203845040707240030803544103c82d030030f030201c07030600b00c0c2c504180d003012803e21005a10300d003106030002d01c224000141d49641081701190301c102c0b5001110740800100c2203189178a824056940903110032a00d0b140795048c80140605448078918080490301d110f000018190360b520031001240181c0c80203217444030710b07003450010000c050034000e440c410142103000c54000c0e000002560302c001805012002103846544401d24030480d51515072078056152081d182900c1c41d40340440740d51110079182c0c0050b50b211490480540c0c88841021810840148100850761b12030303100030300009601011700dda0141c0780c0c204a89041c4203071801046110700300101c41e84058800035000064080a0b41c0442030011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 520818453 1250 520817203 520817239
    0xa060507032d0f0e180405101103152704061d0a0b04021f08180d170a0b1c02040e060f0115110d0908010f11270a1202 52
    0x51810a10034107403400541e025914014080790f511040c441c14020180140314002640b075100320809200043c1c4210700b44402c000c41007003c1c2d0302d4551181ca05008000c01c0c040d60b4411170000620303038071115a821080c03c2c010f0f15140510445210340441c000100c0300d100340100314182054404560351481c0c0040074000810100d520b8514a20010152009031595201c074501440054070a036405200c40ca01d592200410b12880403034070010f070711014043d181981009090135061100036003183c006443c44002554803c1001035803d04010600405441d000000c1b0b0081c4006100380d5008201500034640c0300034544103029009208440030300ca00c41c001090309807140d406a41d8220b03034040141c0144441d007440c02c4c1102c95409140313012842060088407040c40d2508011684010444c00c031420f1054103801c0c055907000400c0c1c64428412464482c00040084c49a05400c08641c108840d490103546a0320180304840540200f402e00c1306516562000c0914120000492003403005c0201303104040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 520819703 1250 520818453 520818497
    0x100309211209050606040b0402040f080a031e210f1113062303070c0803130b0105011809020f040302040e1b0109080303010e130501050901090b010b13150c020a06050703 74
    0x903910001622554031502d05100107804681d0b111f40d0710540a11000c00d00d00b00c400700c02c90081c00c811005000d0b5170700c0c5045c007400480540380070800600b84248030703080003500700c490004501c0201c1900e061407080c1889881c001c04454040a030000c0c10301820050f014075040141040300170801282c40c0041da40c1e8810345045000c0c40059681000f040301d50400e40200c4006181d208a00d030801c1c9c800b001650740c41d42a103074411640c0220059003170904106200300503a20032f014110a080003003441c2c80550180c04800311a00c101c28106400156048001c400d41c01500c00641d4064030a01c00d507101041840d4451003070754103050b1070801103000701c0c14a6218102240852344118051455642030250300306403000c0c0184140004600003400c000001c03001d102ea40c0c8540c42210000613240814580000454810790140707401070803d01c10880403000380e04903002100d829012039000b6048501c42511154040b0402030740c00044d034039000468580001c01444118030a60f03d008800c81c6944048002c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 520820953 1250 520819703 520819721
    0x6011508150307031a2d060910270e01020708072603150f0306093f120a09030503040320010c02031c050105010c021003092112 56
    0x240c00000400c1d00c00c44103440c2005090310150a507000d02e030301d030744859494100031a03107605040140c4080142c6002100f03103005a0000e48400308034000565019131701071140207070486201d1042c10380030407500d00390031000e54010140a9010f44000686000ca50b00802858444401c400d083c42d40c22101e255044c403c55030b100e82d004d02000e003007640700d8480020041e504509200b16000c26188240d401403c140035501c03c545d00d00900c034080c1e40001c00d000000030303144c3d002ca00aa0100052100c03880001c9000588444500342c3c642c00903d40081c401c4000000d803044800900c40c6480310902c15184900030000340461000340d80444e1507102c6e0304011180b200740050300080041c0701043c00030b4481c900d42d0303130508480c2000345811603034290114216820104444007590000401d18007003225048140ba02032118801000250f25107000a0108000400000e10404070348104540142c001d9010b0302125401800b007458a01a04468500340e0401c48000c00200e02e80281c00079060099000d190304c6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 520822203 1250 520820953 520820957
    0xc0c090605030d050c15100512010b01051c1d01151508010306110910080613050606070b041a010303090f0512120a1b0c050f03032503030f0c0f02060115 67
    0xc034072a40041324244c001c100c404126000e20080310503002c03802401700e4002c8400c4043e001c0003524040070400c680b0880003400e80700340d040807000c81c0141e0f00b001c141c07549452801c49412b04000404003c1c0d0060240000400d074000e155407540c0222041540801d02e5883c06c0c1b0b02c02c0f1103060300d030402204403032011022000010010001400050300507003000c00804a03040390705080c426000c0c0020405020942a00e0004203483d00308510b920344800d02c0766104902003010001c03411300714007040b06031154440c00f90041d03090078041810040c4001c5010444160b0b640d0098840d40c40f0300c1c009010420310b10a0032a11003000401040c1c03854045240ca0300c00d00c180b001014413043c1e800030803000303130002c1c2d0030001401301c581d07401e00c0d54100401c44d01d10040d10421140c0e08440c1410108140c0c00488040395000c1d52050004180780d9005040022070103001c10300b44640c1404900e0200d000d0006050014205c609101121040300e401c5903000e018907030907800741c1d03442e80e8940308810407a484031529040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 520823453 1250 520822203 520822213
    0x40537030f02190b070f12030e0c1005090901270506060d0e100204030b09160e040312021c020316020c0f060708071703010f0f120b1003120c0c09060503 67
    0x200602e0f0400c1038200c0b211460002c0e52025035188911006900725600549100340102108070401c407a88546040d0300c0341070b007000c10103064601490340c1d9032125000c101303000740a010300300b241d001d004005440c42c0c128000d1560007650b841d1815200d0808030050040850b01090f43c05c1e6038016003c2c05201d101d80d0020300118140b1031555001c0f006000b4030381c910456402040024004181d41e40020005903008403120b070458100600d40074074029485003030382104206685c0a118240b240c0b0246600300307170545400342c103400700310503000002c3c81080510703240300040b141020304010701d40d0095481002508201079100700080c8080c1c0e00c0d103a0400040764000b0803001c42c0105850441c010f0165180102541c500b0400255943c460b4800c1001c4502d03c9080c000c0010400c203101c1d961042d0140400030031210403645440049410b000b048032000b0720200203000090400c0c100d00f65154000c58006c200a1100b881c425000703030145c1d14001007030760500c440d0000807481c101680501c404031680500106 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 520824703 1250 520823453 520823483
    0x5070b090619031d0313080712031805100903050c0117060105161b180905100e03130b0301170c09070c0c031403030a0c03050f0402060a0504053703 65
    0x1c20070540c08245000f4169200c01020701c014140c500080c5200c0c005000303599075015210340b04d002c514564412041540003070401d211030f054008640285940c103080401c0c1e140c070601058541809250082500030700440107848a050303001c40d807001201e01076425282403440d030f0b0004580300002006039058156501c4e01080c12944504001c020008508004071542d0840350384d40c040e5100402da102c0c4889120150a2015005403111070701c41c05c0000340700b04811802a5689921075030b140940c00c1a0039a0340b010900024414011925256000030313200c0c0c2c0301621900c081c007280d04203000e503c1c0c0f4441c0001484d082c1c4040060440301c1c090000b4110356450b551950708440a00b4002400c070340d000c5581d00c1c0000060000a544080e4120840245440f45452002c4800300e401000050382010b040506015410302c1175a081d40d0000d405499040c0d444241d490240c07401d108681c040c0b41c200e8501c5c18440481c41c10181c4400c0340b0000c2c1052500c07074403d40c6804042d040d07014040a40003424411f40e0f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 520825953 1250 520824703 520824727
    0x8191205100311040b040212090f1b010309080409020307031a040e0604121107080705040515010c020d031413050a060507151a13021216020a1403220305070b0906 71
    0xb606680c0014130214650780c108001c10300341d800c001e03c0414202060b03c28408100d20500401d18140382401c001d2010300c620243c07054080040b0340425040c599210040424000060708503806403440d00010341d0390303082c003910041c0242000c2006604414081031890000d01c0c003402103000340c20a0382c0040c0002d44907520b81c1c111401120b40c9140c14421108801203107400d0034440c103c02000e420020b0910b00303203400180001d0f55001030038180b404103000000c82d2541e03081584005a1601520034072010130461038107991000401004021402c0045080301141c0c940032450000e41d04165808040940e848005560b5800390303400091018200105014414549a00200040c1d241c0440842440528000f00c0e04041030880a000d10580006d0f02c8040f800360402540e8110300850861306450310808002510f607003400708002c1690819201000c8640700410039030f07182040300d210040a0041c20000d52007064020f11003100d290107180000180d007290314003943c42080c800341c1010300d0b200003c15a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 520827203 1250 520825953 520825973
    0x30907061101091a011505130b090d0204023015060f0f19030e060106020304180603140a0302101b050c010905122101050f0f030a081912051003 63
    0x1032419641d62501e0380f0f80455803081c2d0103007601240780d00c0840300c0d504150514540020364042801408410030a030400d40301c0200300b03501103640c01803e590f01c1b0410400010550b60204401940c86800401c1c260480901c035250400d05452082c040c038966451074898072486072044039002c0c0400b604640364261401d18070001c0a22800a0141d03520b050b115000d0b05030381c4c1c1c100c4c00c8010104d100c0c1c0304091044613094030802800031030010003000d4079850040c00130760307901c218001d620035074803849804c0400c000f01d608040c014590025000c1041021604c0c450390b208441c2070f00390018450b41035582200101072042c0800d00c0f503000c1300403c034032400310001d8a155204407844807007903503180c0c070510104500b07000386e41320181a0b43e1100d55030b603120f0442e01e00075400d0498503540307101d01c034004100ca44c3d00c0802c0744403070070b40548040304616414400281400a5171a01505080c400500c80c2850810340c45078041c18441600c8103542c00e412220014102c501c1203880000d016030078407050000c1445110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 520828453 1250 520827203 520827227
    0x2090f0f0a03170c07081501050301021c0b12070803120708010f14060d050a06050f03070e0615040f270e030a0809010225050606030a031704060902040207030804050c010503090706 79
    0x180e10f6140003c000403044c038098450303202c100280c20006001800e1641500c5a40c0107220441c029420165850701d401c68a6142d280d58091041e078501e0700980c1074482400410003800648250b5140c036a0341c40350f0305d40365444490603508030302d001c0000803c507070f00030701a80c0e041e10b111071030701855a0f0500c01010312850f4100070541d4000010711019034080b555000f001d10a20f481d410105405180600b80301d441a00300704002c0c82904200c0c01404079060b40c15a00d079101001329042201c4103450004040113100700c0e04440c3c807250205001194040c10f0020f8421000d0741c0b0a00c03003020705001c002400c100c8a08140c0c184054004201c51003c1d5441021000d411410340d5000500e00042110903c038074019520f00c9009036110748003c030703007444014001654011016409800e0540e6903a03401020501040b04c040c088075084008202404041d5101d20040c5901900c119901c8156040240950b08100c1c0d0843e03891080200300d94841d486542503c1c000c40010000f07000c0300e4207012040d108084600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 520829703 1250 520828453 520828493
    0x120b0a020d090b180706020601060f0e06040302040213030b0a06030f0210030b1903031d01020d050f070f060506043c090804091506020d05122802090f0f0a03 69
    0x303040c1c000803c0207011554000ea282c20b00340e0344506102c114150500d03030180d22000c255001600104242d64014208640c54005450502d0030314840c0000070f140c50040781c0000c0e40151010035865490031404604000f5a80901c0c104006a560040140c00761500380c0802003210100e4061803005040100e042102d00017582408030311448101c0c0031803c500504100102041c103403110410a142d00860200d1070a182440808001d0f0100c20020703540d0b49070300c6411410030000040341420000c108082c0c442080d40b000100150008a092042c041d140a9600500c11850201081042d516040720115104e40c80000d901161070b01e15070703107560358540d4000144a1a1102c2d11800085d0f8008000c001401070907100050005001c1c0805104001a80041055500041e000b0b4503480d08103040d02c0d101d01114076041c0203581e0300a03800c21107140c4145a80d120391074220300c1d0984040c2c9500074224040003500c0070020440d04404110121200380c3d40c5070b4000c40c04031401e201140d024a00311040c04504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 520830953 1250 520829703 520829711
    0x3070e03010515040f0e0c06090607120924020606011101090c0803031503070b030a0203040614090a20010503011203030612081216120509070503010905010501050a120b0a020d 77
    0x8010a0035a0400c4950320030300044400781501614041c4100e41045586410410004402d03000300c07603480b000c02d01d4003407240501044142150765410300300d0341582c0d070266141c1c040c142d000710054034214060203003c12050340303c250104a80d81e07810102c001119207900a1100c0d49840c8019074010150003452000f0355295024138001c51804c250600080510000441d035a00e050320b00b0b00104036220842e03610981155404000b5100c6c0003041d6038010800300740c016680c3d260752511034000c0940000340700792045100c04109150f50b002c112030450300d018092459110702018800c0380c1b26058030018901168003440180a40c0c00e80e05020300249200b4240011101e4131030b00399080076480498225450140081e03014219424101825080300360390615002c1c1140c49840a0318540410700c0701083c0300d50703c1d00040e00e03101c000c000700401040080e00800c00d0213154200140a003009009540c040d642200001607071813800d03c2907040351500980c1720700c029142c24107aa0040e40c0121034030f00e041912 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 520832203 1250 520830953 520830977
    0xe010f020a0e09010f030f03080a1811091501120e0f122203110103022802010608010b0f0d031b1e140d020715110d170912070204020307 60
    0xa6200a003000203507600c40d4888801c0c2d1000b008003441c0160042015090085e604000140d801480042032940c507040c6103103150703a07085400004150700d840310441200303c01190b07011f00260240280481c4001c2e20311500c40e644411001230007410781840c2500040e1215240030140030180e10040d54110014255441d0841c8008a180b5110303c11380e6052080310005200c20005d032070a0b010405140590b5008440c2a18503102c0d8414000c0b10400306041c141c0000d910480c01040b9080036410070001c801c821000040d15600900820941c001e0401d598030703111032540585070a140428a4010060030b010310300a072940c00715038041800b008011039400c0c000000700080d1521041207a444c0b145481c408042415040c00040c030b40540009c950150405032044400d07030b5001c50380406807141042c0d440d606505144040303424000c00350f00c1e4080f6000e40304020300305980c00240481074800b80c24894481d07880f00050382d519542070010070341e41c2c502d01b00410700060605402441d0b00401a084c041410b482c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 520833453 1250 520832203 520832231
    0x10219020a080303100612090f030e0f030601090c020d080907050d14010504081c0506090c09060408120a270e0a020415030b0a090207080f090409050a0f02090a020f09040e01 76
    0x10781d403400b05d40c150300340c05005055100b50340c1e500e0410404803c2c401140c058951082c20b40d00c2110140400c044403022165980f21840c5590009001400702d414170f69640320181e0082c4820f03c070030401402032090b0003003010f100701c1c00540244100380c05404598985820030040d071510140407201e611300003050205100081c498584101d0240d201d0030f651b20a030310041c050b00c400361701c030070b52619252006201080d1200d0090030b80c0043d0b81c1e104550341d94034840000e00140100d6001c0440d920483c25403441000780e000c060f10f4450141d48030408040807034038a00d400300b0300e0b242c007450356003130510820800503a007600600d41088142000528081e12401070f4a050124080000c0200340c0b90004590703241452a1280001e01d4500811410018603503911103043c401c2c5000d200f580200410041d102d5130300c50307001c201442c0d40202101d0158030949410000035010141c2a44201921740c0007031141000b40c003c075661901c45c1c1240038035280d01d02c010080105001092503130307599600c20180402c06 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 520834703 1250 520833453 520833457
    0x1090e070305070611062202040b060f0d091505060117150d0323030c040b0d062d0503010902010c1209030c0902091306030b0f1e07090314070302010219020a0803 71
    0x520f96100031a5800030f05c03443e8500740d0040d00200c03d99209080c41120a82a0707108010b010b40e0440f00403807284440340000d041800340c00e58080f00000002000868004d56a01602e01c06c0e215101c0ca882c0ca40800c0c114408075141240c900b4082600c240c000c1a07038001e81a40c1a900903d9030380e00c4003102c5184000b14600707482d0040114041110b06005400643d03440b0f0300c1466806038011101d02c2d51030882180d402d40c2c0194030940d40b0880d404500700c2004245034214801406100c007224401030510030300003014801c002840040706510040c089003030b0406009400a554040e115241c211420b035640110140281c6118400c2082140700440083c100303e4011000b00388140025031240414400c00c40c168499002198050342781a40400029140030203440d4000d12070600010103070369000d0180403001c0103035429412540729208002c032654202c100801502c0c02078020700d00300b007541c0e0010355507640240806805a4800421b51198801081803034000b1072000e03094806050791003503003d15507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 520835953 1250 520834703 520834709
    0xe19090609031701050307090c0203040b03040f0b01060513031101021005070201021b06010302090c030c0412030201020a080604090f0b0903090a12120918020904110a0801051e0901090e07030507 85
    0x540e120304014080c140d00c5240c0c1e83c2c2c0342c3c081d0000107942d9458540001c2c0d88440303e20621881c5d5803203000e40c10500b4000e100382d9006040d110700c8182d0700c3c039142c0340415040c82c070400101e0b200c010200002c242a841041a56843d40c513036043d10036801e05545a42d10009281000307103045200d103000d4a084521140281400340d8140d03000503854901090310050b88500d80341d00c001c140e074080b1004201598402061a810140c03075070080d0b40d071f45c40701004a5510701c1550400c1c28018550076400040660540c000e000340b074400c7d602d01070162941c00400060b51a00c1c4c00c0a082003100c41c6200001c21030f00f25500390410b4070403089a10341070590001c6400b2000c9940202480740e1904c420030f003400401c0040c20400c50145c64214541e6051104500d840308050b00625072207980460408000d0300c5543c40882c1a0065904460301c9480030500100f40c803000b4012030740a5402e00c1d0300d0400040804400035140c4034010007202d540d03800c100b00400100044018462288102500000405c10501006000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 520837203 1250 520835953 520835963
    0x15080a030e03060a1e2316080f070e040e0309040f0e0d020c0117060604031416050a1206051902030711120412030804020d0507080c0a08010c0206010e1909 68
    0xd40d6090310100743c1401c0004240f503c10780d040c0f015460b203400900d41d02d00340d1a00c008000058522000d0086802c1030b10343c21280e0588242c201c18001c11a5040511840130300036552108101d1740c0300c84906405840540307045000c2560058041500e14040c0c0240c500300746210122410300d0358500c0010242d41d1008800c200141d5a0440789401d05014007000b01c40740038070f00040001c0320401d40020007e0481e20001e94119030820003003400d0340e481030200c238001c43e0042e0a80d0105250320015503201c03080103001480703040b2890000911800c0904103501200e41160b404100140203817107010241800038228100f05140c208981c001c0c5d04244080d6009243c01da031858050841c101c0020329001443e0350343c40701c0c400203000801c07a00d0a02c2015031907050b418a00208140c455201041d2400e43c032903401403031800743c8032002c01d00c1840041c401020f008221040002665104011030885121074580030061700160300611080c41109107007504a9960b81d000070001d03a00302e403940c040707611002c03007215 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 520838453 1250 520837203 520837217
    0xd1104180318060519020715050301050f011e21090c031209080601090209061603020c181005090712110d05010e061813140604020307080f1015080a03 66
    0x6040e400201c5aa40c0503000381051102c41c1451000b82840c000e0824250b54003184c07160103031030070f8805d00100c8001d0034690110400218030f84406001ca41003406610300940007003401203001c2d0320904d5001c81862610960505001e08940100c5402c00006210030074130b04c0c58225030a801d240c13807042d107a100e40110b103409081411460644a1300700480054000c00158000034820f40c000410142c0c1111105180142d85030700b12004582d250003114104d4651000070690481810707004205908911012640c160b0040240b806000a030407060316260310b0341032441d1040c000c138180074000e203030071840a050005c06014008103002c15284c24400400080e180882e5070000d01a0502030107024000f000c0c00f2030740a190030310115440f8042c1e6254102008154000b1800d901907450800c4086604085c0c0002c8051440d000240d5484059804a0091107894400203081c074022410440c0c03e901c100141c00800c2518503504047c15051a00c10741c0584502c0c000280c802040100d146440d02c00d0716000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 520839703 1250 520838453 520838501
    0xf021c1d100507020f120406030b1512070909090f021002031612021603052e020a050c060c0a091514040909170a02030403021207031a0f060a0b03060d1104 68
    0x2d04203d01740480c18025441121080f80000300601034030b041d07a296203000100220002c00080e01200850403501d011030001480725100003840b58000e2045500781c840c0e5645035550b079036031412500344d030b000904002c6040c00706400601e040c0d14800102501881100d042c600009180303503c0101036002113620500403034400c03040b203806002403001d00000203040e0003540c0c82c58851544401040d43d21018051928103a0490750000f42420301c180710f1249021900c1d40c0c070300b14016080303a04c007134050b4103284140320005840350b02c160708507a04151070f40d4070034209601d040000f448041c1024a51014043c10400540c003611403240504010031b80c1400c081036400e180e0a002000c02c1c803000459060010422034070a81030740000c200d40460fa4141c0c2c04d544101150b20b00310307040104c1c54100510304010030305a410000b280003649801529564200c4036607031952410899180c0301d41c450300b041e000041c80080d2151900700400391146004030444600740c200100010300700d600340080d282100e84200a14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 520840953 1250 520839703 520839707
    0xf030c01060602060124180b0d1d0c0d050f24100e010501050901031d030a08090706020a03030b03010e0f0304170c211911040f021c1d100507 62
    0x841c001c1c0040d0000e00003a5040404080e01d100260080780d41e105000074280e20030300e00c200340d04030300f080398810070007482522035640d040c25510142c40a1180d500b08542160741500c208181c120710b081080c0185a000300c03031030510614404030881528107000d1901d010200100601008102900755110040903045000c404032416038040c000c4a1080e40c3d1240500c40d854100300b00b01e0668100742000340d00c0354101d0300100d0203400250704102094811030807036403a100d0000007a00380c1c101d640d2200e01c0c10390384880b140c03540d801c5c5610410700180e11050340302d40420f01961221144c0d22000d00042500c400100e903080c50040c01202e620342c1603000090030409641407000050405285201615061030514000b9032030f54180c45421400601e07000d4401540681000508542e0103003518040e01d0208a040c0241049141661a8011810901810403804043c0708035900142ea00011004e01c000510440000b070094440001d500c0003510300484440c6410080da8011a40e0304034040340e13a251039000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 520842203 1250 520840953 520840961
    0x1f09150f0c0f0f1211041205060601091505040b09010c0501021801020c0d0b040b070504031e05011a06070627150e0c15130b0301060e010201061e03020f0f030f030c01 73
    0x40008000501d6000d4450030703132004d41c1c00b100c440102c0700403550a159041504481c403035940b001084c02c912024071030402101142d2544100c00c01d03282d150030309542d400c1301d104107500940c3c9500001c0d82003006002007542200a46035810b03045c03401401010303231580d4003800c83c0d00c12200040f80440503040e0070410341e8104004a4001c0094802c1c100c0d4141c00e5451034642400074100501c2c200c03001000810181c4900c2c1914020b5800580e031721180850b40c4940c0c0000e0b0132951084c0d480794200800000c002082294580e0040c10103040d00b4541100f81e21071100900c0345200f40d407262004948059030750352480840d00a0300c1d0042d1540043d003900041c0807011140c240c0318444054104a00141690f942d0440825603400c00c2400700b035840b51941003c000b003800c5078202c8260604040004900e1641c05503162004105c02c1e0020000d158841929000c1c05d598212a908456440c0c0018001820140c8030403490240140c031011001c076040c030010741082c00d03254105200354800b250200da0000c003402 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 520843453 1250 520842203 520842227
    0x3020313140c10140f0d141018050403080105010e0118140913020307030201110f1c031a03070b1809010611070e0606030a0203040201110a03050406020f1f09150f0c 72
    0x100480d135562444101c03120f90141100400c1000d00c0490403d4010003d80c00c41081c2801d0120401810b1030103591042102c1001d0040200741c1c800d1080903030707201c055845110300a980544030802580c0c03a110044640e00200c010040c104465030425400051021a07018060513181c0502c891420444050119105000317000c00f4040c07801c00c0809016031804074100c01642e80a11f05544116941e0030b240703246c415642d05414041c410b003882c07a0082c0386003610280d6074000b669402c0c401c160a0315102c0848038031100d86203906070040c040030001c0468484c018600b20311666010400c44810000107294040e090340a000802c41c0c8120501455005115400141041025105403403c106000c58000c0c00001c0c210000280d00001181c15a8003c18041c2110b10000d070032102c40c05000d140061044e00140701b00790142c031901340781c0e00c1c902001240703144100101c4654546120300006103030010f0008a00291480000500b0381240c64074140200c00b10f0f0181880c012407a42e85445005040c850307140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 520844703 1250 520843453 520843457
    0x21060601230904111201060c02040e010c171b03010b09120d050d0902130f0f06090605330a2102090f15090d03030509010b0306040803010603020313140c10 68
    0x5a21045045a007006a8402c44010343d40001c03001c00c00c021001051048072400e81009140f00b00005005a01c10b0b03103d01010301c280e4080c8040307000001013900b40d400c08401e40d4007154a0311504d0036501140183c103076000c0862809003000d040010180c0089900a801ca6443c1500000c0c5c800c00ca0705106200d90070250184d0b0040c00b00a05034040205140034103280381161680314003414095550b00c00c0c0e03040c94003035407100401c082d441d520a03010061036862400c5c40e189080c1240001c610303066110b40021101c2c00b40c490b070503048000d403100e12400043c841200c808003026400b00791844801000c0d14444071a82c40d8502450030b00784001d0b440c00c20241c0c01ca0f070800d0040000001c0fa858481c0c15403d0004140d8015a200b4420b448602c403500500c0d14031a003100c1070049000034554180c01c050300845e0344030002c01140c040302e42030589410b8100e03409041c0d01e00400c010841a40310f640155444407130324803c142080e40380e6891100e04d00c03481180c41080c0e4408041c008403807400103007081e4000918 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 520845953 1250 520844703 520844747
    0x9160f1401050a02060c0315040606050307201207020d0b010b0409050c090d080a1e17010807080a080c010e1204080c0d0215071703040803010819020108010e0621060601 74
    0x103c8000d55a0710010528580d0a4003c80441d04910704514048000c0f800203005110315500e03908014803e0f0011114200002c0c03040405010402c3c488000f9220f1028000c043d01d4048039140e4032004681c80500e04982020994025202251700c05007240d028007855081c10350740ba031418000318283c1d0000780c01805480300c2001002c415598103001d00d29416440491140c0b200d02007181903d11000c140b1601030000700f90348042c88c05550102d5403500349604a4040f0140c4d0b601c6034240b40d0341c0c4c4050700500d04580e121032805c2c0049100700000d40041002007002151750304064414605040c8120740b1002d4a503c0440c051001001c2071100008400066482300c406003540d400013500041e5054480e500c0d000300207401024002d18160308201440102440e942d2810039103480e00e0146d200744030b501c000e40240f001c01441944141070a010043d016501c25110b642004803600a203407001e40324031b5001c490030908480b5006216204551107603800d02805051402400151044580243c290034030160 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 520847203 1250 520845953 520845967
    0xd0f140312040f1506060207080f0106050d0314070c03110f030d0207051207261c051801030b09070206071103090d080306031f05060102070f1d09160f140105 69
    0x20740d1080d15031080d004061040002114203284400c884129500101039060030b10103c1e6031340e000160081200e190300211640711400018070f508031800d900480e40c2c4103035800c1c0d450000c039100c1c1030090400301818440700c1c540300c400d0740c0340d8050203c40e520880b4490311500303202d00f140c580500d000c3e580362010b4001c1e02c4807460380d1400039102c035a98050a0b00c140760480d4082e01e0403804000c0c281c003030a058142948100481000010550b18007040c4001c5449012078043d420403000c46c208440100c203440c3c01d424604051044000211055100c50416940300c50a82003650740039500d501078012034018060a0802000040007402c41440c0c40d8070552003048005480c0d12603908200420340c1200c4103c0d22603c41e040000e06000b001a4030000c90700101d660f403ba004410f51125016160036002c50b0304e00c682d6580c0321240b00805110301d0000c480d40c1080c000d20f0110003c60684d000803610207403031180d10344007880c8100c042d5079008100d112140900c144190b1000d11100b645211007401e155040c514 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 520848453 1250 520847203 520847227
    0xa0b03061c1b0b090a0f050102030f18100e040b01050309031b0114091005010e0601171b041412010b0d030c0507050301022b09020f1e0d0f1403 63
    0x41c99089200c1140381030460407050104280d1018504240c04070980c0896503610803481d0300d0b0700301c2d5030030900c00c03036182c3c00c000b850f034510300364080c203c0300181c02860a01c3e48004400e140c9411804800a91211403410305440c2ea807507500d150b04506003500d8920b0850b4026051200305d030100600d15041c000200184500e81000000707070b40e09900a1031403c80886c54940307215014000b8150b5604441c41c051301407040000001ca503008012511540800040c2e07070ba441c030160456025600756020401c954201140d800d0311540c016801a490f10311140b036034420401c468041d0f031250b03001204c0c40708402c0d440700c0c880c50540c050b000844440790086c44184c03401130001d2050307100e030361008082c4030104144404020741400260010321005000315280d91100360f8100c10031560303100420304019003082408441d2241e204421079150080c0940751208040030500440b515800c5d049101d100d42c1d580c0300001d0360b4441c2c480341c54451155003480c1500001e440c011404003400240a08070703401c00d100c00c809484c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 520849703 1250 520848453 520848469
    0x1505091b1c1b09020a0206070c0b012d0305030d18230709020c010f0b0d0b190207080403141e0a02061c05040c030c17060a050406020c07060e0a0b0306 66
    0x141e2207044007006040d107241100307189004101c098000e4900442c0083c900c4650782c00342a455000e0340982c0d585035900203049604100c0c030700e80100019030707480040c00a5900c054050070700021858090004d40019880114140f8059004441a038030014140e8000d860b01d003c2c0c03008070f0041004152410001d641c2d05420b11a4240d00b601c2485150030201c10b911804100b0b070401032038001e83c115910145266031501038444c024030801401d00304100c4140d917081c644000c0d05540e40010110800b5254034640b1100801141e840c80c00c469024004140482c4044004000451240700d06407149000c0b003080c40c0c01c0c14203542d02c100c2042d0054180008000003c0366640901358100c5101d0740d5401c418002124040b00c2810150030300e85401d04110030050200f0310306095078020a0300c0c0213540d0355013807804284441241c04801035006080031400c1e015460b040650428424600541090340da8030460b460400b041e40480c0008118425600260402c152a035001d041c440c0300c80da16626001c004a0490 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 520850953 1250 520849703 520849729
    0x103050d1404090e03190c05060f09150711190b0105060a120f02040f12030212090d020d0c0803070c060311040f05010c02151902010506060301031a0901091505091b 72
    0x1d02d461360103200c60b0f26030600494071030714040104421a841040e00081640c1b80803003084841d4481c11000c9413800c03a00e41c0c1641e106140325001050120f1041400608080025088409000d40c940124004650030f000284001c04100c03c3c00080d5035240c00c01400c840010b0f40160302400c82004819800c036841b52441001090340c82e00460203c44410b5514002d11075a48801081040344401160703444840c86084400340c000d60807134060303210400080c442d522510f11000e90222071540c1e105c00600f003501516001c0c502412400c60070a603100d890900755404901d00721201c1008403400e0007043d406100e00c40a214a502585041c1414000d0f440c50042d00b5000d82da0510689069210441d592032250305044542c03081d800d80c0b1009440703600c0417401c0100e829003007d9400d1600049290a0002c1500d040720380000c0c170003243c6801d4a03400b01540c0c002070300d505215500e410300d036400300b00d940000041030341c20540300140318504000d0550070013141c2c6403400e11180d00b841080486036940700c514400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 520852203 1250 520850953 520850969
    0x1050415032d03050a11012d0b060c010207020114030c0f030a02160302070503120304050712081b0a030906020615040b0604031a0604390c0b09060103050d1404 70
    0x1100d101c00c80281c1541c240c2c480903a00c201c05500c070408042e4400b01a00307480d160b41c0c032017000d0410044240d60a842c10080044090000070707040c520600c903000099121001e036621f0000c3e0181001c00810907550080613406003da400082080c11541d00c884065100d10080d00700030b095051840c4510030b1445502c024203800f10000c00811106c08403503044a000050345440d5000645040c54065110081032213800d100e4094604125030349803082d02101d04c2564094007400c1d0b151308206c241001c084004000340c2e10380b40c050204841e1840c05401000c006c113945401404195900d241c01043c2c84a150046d00442d0041c50030310850b0503d4103044c04520900b141e01042c107410390f04c04140c1900555002800c00c2045008001c0b610f0b140c10800350048400ba5024002129440540e20350604030507800082c5584010034030885001000c014203c00890b8640101c50748007903204c0500940042e60303c0b04840d0008001041009000c10910022040c2c1e420941e1003035035141c00362140307801030b8414881 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 520853453 1250 520852203 520852223
    0xb0408060a0b1507231209040e190503090a060311031b0d0c0503010e0a0b1e150304080309060702010c2325050c04110702010e1f170105041503 63
    0x5840c1d4030040110344081c8a09150790321401203040c0400785c0850181d44100803000020200220342020405560408401d150380b45080e10329803c1c040100f806000700f100074081e400d903000c407004a0070454445103010b0001140c460508000300810228154448000d00d0b1905032030040c070b0011070341901e80c0006540c00d21010000711590b89100d920a00c903828413101d1508006060094103c8042c42c140e0300002503003031580ea1848194000c952008001942c00a440c3c003d40d4031440800032800c01c90800030780b03c02003681448428446940041c1c0b01203565102c04003c00120800400000351310a450780300903c00d030b081c9814050032520417148246441d40030300000c03900c207410344001c40e5403c01202c40e0921020022142080491242e42400c90301400381910b09003136450715001d112544420300030014074000d4203a0054401303c0c1588540d94220b0900d4005610b206a0584601c85d5254180c6071210710003603000090940d490141c104a115500e445060024121881c0700c0d4010b40e80d00100101c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 520854703 1250 520853453 520853471
    0x10801140f04020f0a021204060221070f0303051614030606090d0206030a090203070e07080c03061c0308012615070203041e090c02060910110f03010905010f0b0408060a 74
    0x40c07019031001164580007800000e501c10610003640c001c0502c03811507802d581303a0880c212000b1003640300341d01c00c100c01a0f000c3c2001040041040301c2280b000803500d654070386002495560300b001e040f41100282d02080d55081086111140107550044101d110315044900003d2118200030038040030f411103000701c0e07000c00c0121070f60303c405e07040f40c40301a00141900e86914000c080c4002501d17042008034040d001c1d0a81c0040e00c0326209203100c1c058031040d1507a00031595200c00e4000c850304020718250340172140f000e400952900b03c86910b80003034000e6890041c40c0d810610100f0242c01d4590484410280070040280c0a00c80031600c1c03802c1d0001e03074004482d20344804004034914025608500704040c00c840e588030121800c064031004865020205024410501009a840f440211a25146604841580c8207501c81d203078813060b43d130030703240e0302040c141360744c2c00040d0a4a030802d82165998560361790043c0300e100f4a40c003800d4010003c0d101e92500d82803d0420320ba071290b2005d03041882d50b54030340403c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 520855953 1250 520854703 520854709
    0x70e060607020414060f22091e0b0708090705060f130314030304060c08040b04021003060f1e0b030702070608040627020a061b020105180d050a2001080114 68
    0x1a81d241c2c0d001081800301c0040300c510701c0c078a05001d0383c41c18410258940305414a0a01d0741c40000080d0301103030100f803c80c1c1d80358540005009086c2c008c8810b01c00c1c1583c0c1140141c00d4100ba07403e80c900076502942c041c079011601404c6a00c0141404881d40c2c01683c1c1000039940300c20440d550066a021800d03221403200c08801050042500004c210b2609282c8201900d14004003861041c0d000308014400702c1d480003030560b032035081554050080c80d100c3c00058050304200080044803031052070b0004085968800c4040c0d4107025410445407410114100302d00008018514070241c400d0a04032841d50801c00d030069600c0400788038202c203200000300050180044ca9000000040b1400d004c00501ea0403030600129424250300200d01c51180c03000302050641c8075007000c1d205100714250b00f03d1030803400d400565886e0852920080000c00c036120341d1205450345d09281342514800d40040001549901c0c28211030507400703810003450043c03400903d400780c2c0e1081040d411601e0103c8484217225158005c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 520857203 1250 520855953 520855957
    0x10b040503030f0d0b03030703050d06050904020a050603060d05030a02070303080c041401110307150b13060602030d1107050d08190513061a0a0e06270a151802041412070e0606 77
    0x90103915000100b05c8c201410b41202c010701440c0fa105200708405030b00c40d400c1082c0c501060b1030103034100341c2401c01400b0605180e4002d6070001001802c4281c40c03030f41d0b0b41e1020300d9a030040d071f1030703500580000c4410020190002c1c010394108045e208410300700b609180c2408c01403503642d030a050400401b0f41459036401818030880e0302480d0032541d103103406141409560050030407a1022402030029480d071304542400342c8203910548820b0b501452034000614606005040503162800080b0801c20400300010400c11000541c207240b902e90414a24004c00f003248084d0a4200403c105802c0804004440c01d4040a484070240e10001c00181500d620820340c41411044842e950810751041d00481e94401000c40c1c241b092200f262440030001001d4050090f60172110111100c554000c804250140300c0744c0c1011407078503150421070845c150b461640c02e50014441c0c80140046500003401d208500050010302d002a10688a4940c283e00d840d29080d592046071150700d141203c4000400c2e02e89d910541 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 520858453 1250 520857203 520857221
    0x804030c080708090a061d0f0a08060a23090a0f06020d051003110a0308090d0501110a030213061e030903180609090501050d03141606090308070206010b040503030f0d 73
    0x4600d40724050b61400c0e5850b41d021138282485003209000000c0d907544200040c03044500b4034150612110f0311740702400b4081440e100d1031584140703c0d26000c1110b02041181c0c034460548444045903055103080c2622022050319134062540c8949003c0000a02000555910b0144d021210340300490090400794000c5c041c0081c0c50007450705000c1805001c04921094070144da025400000041d541e6604020040d42d880c440181101001e22510b8010f1802080c050304042c000e200104084407611030b0f180c601d904c0080071901280d4045100e86294140058410140c4200d090a40c0c484405000354124258200603160805450b600300c4010140709440d00f06080c0c2076950b181403d55128a4040c0c11ba106d0f50003520f220900c2c1030000500303440c1500c0d001c030009400d6221b1054000f00c0500356012940441c0c4070540d00116020f2880018140d44954416a8007035514a00c10741411389009081100c107074010015008280014489594003004460005540503480e90341c50384000c2e0b1210241444c28 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 520859703 1250 520858453 520858463
    0xf031401230601020f070f050607050a02040c1809060e04320d18060906051b070b030f070801030201140d11030702060103030f1d010c0f06050108070611030c0d0804030c 74
    0x245020512280003101c06000308000d030241e403064540b101d102a6240d010f40304e40d04224480d00e5081210b405c0c28001171484174003031b0781607450f412056000714055940311000345000503061240443c103e0806c84282014110500081c48960b00d001c00302201c2c5400500041e195290f45807a448024008a034500d45450080040e04408421521520344640d030104010300840e007044880343e40e2201c221344081c2981d0041d1900510141440c008661710f4100b102d15401d07500c006655074816a108200e4400140020b8002a07035074609201102070701c08000c2c140c081800300030001400140c0e00a031000c3c1c4128448410541c860b91044d4040011304213018051400050010a100c011540403600506903400f0340c46072041021096001c840c00300710141e20b811240f000a80c4480958803071403104c01c3c4103002d403c0800c010f401d6515a2400c039442a030101c4415800503070204040b80d04002400762000c108809982800740d6100f24540718107140000d2001c11280c40d00103410940600380300c04c43c043d005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 520860953 1250 520859703 520859741
    0x120b030a080301060f080103020d030806190b0406031d06071b020a080c03190f080a030209130c020c01020d0e09040c26010b2706270412090f031401 65
    0x203401c0c0754140d0350081c001c000000b03440480c540300c000e015003440ea0482e54043c010708510540b03a10100c50702070000d030020764000070580352003032501084030549000c3c00b41600c10580d5186030681c0601100c0d08021034000c000091500210020307008604540c7c420918100140604d55050000b00303d0300c0071501c000d43c007003041031000c44c0b402000154440c41410030340890ba243c030b584105920300ca80c0551801090403000c060800d0010b80c828014082d494002d08002d400c01a40100061a841d002500154540d9031110249085a410080008007020a00180040b800305031030003445549900017090003120309030082010010201070080c01412004908200c001103914003801003441e100c555010b0350300b0641800101e281c02c48402d40c9000610311031110031645620402a030320b8000340b00c1c03a4080c08500fa1001c01480c00400c180c100205c103200e403103803460145000c0500c1c10000c14104104011204240040b14200460009484c2c01151481c41c1210329880b090240c035900d808003841c0c1d114 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 520862203 1250 520860953 520860973
    0x109090c0e0d06061e090f02091c03051308250f170a05070b030907080d0804021c0b07091701180b04050a02130b0f121902190815090a03050703120b03 66
    0x54103240241c521001302405040e901c7c01b05035060b801200c4002d503205805021040c1c0480100494841e4140b2030308050707040c1a000310b01406e0303145540c2c0c42006a034010a0344000840c8600000c030420036401310700c9a0215062143c5224444024010f562602c0c5134580170301d202d01f8080080c003424951103c2161130740c1e80c49504082c0c5d00d81054440e880385114003140851100c00100e103145c1800d1240c1d0b00e41e0b50a90b100d4003004005180250361540d039180c81074ac0840480d0032000c0f0648140e100740c4910404030f150468060041c41281d0000b02240d2500e44020340301107035013084060b50380d0002c4605075640c41e5820001e0500e00b201c4402980014003215401402e40c054004070890081158061680004101448403600181c0400000c5800c0600000081480110300c80841e50010b029405642c81d16512031504a540f038008408951014403001010901603c1d2560b02c4080c09004d070041c00e000f5038001e40305000c0c0c040c006080c0a90000707007081d100300720340c0728100c0c0400c002e0488000b418 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 520863309 1106 520862203 520862249
    0x32b12061d0c0d0f0c020c0406030f081e040621090f020603071403042a0b0a08150d030807080723030a02090d110109090c0e0d0606 58
    0x41849004408040c0c0d1003039000c4000069000603072170500302d401a180c4005605920701c02c83c2400c6040c00002c00d440c0c0e01a03406540305089584402860307060300b0100e5000e21151280c01030200d00050b03aa98024815005c083d000440790701c0d40311403e0140d100b43c92203010081c20354611707082c9080043c10010015540004145400c6a01400883c69018150310503501030b03440110700503241111004162001c042c4611100e505000ca502d0019401c41500410b10b086091142c05000114140d41100003402d6442006000726500b01651802524203001900d1090015031900300041c0c1e580c0c050344200d00c14401c91651151084108059090a070740020700d01e1427000d40a009141041d15900b81d55010548100e01040440841000040c1080c1555100d0720b0114140649869031940000d500801100243c5440c0c0130790286042c001e01908407980004401504800b4040c0225 = true := by decide +kernel

theorem cover : BRFrame.Cov 520683453 520863309 := by
  have h0 := BRFrame.cov_init 520683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 520683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 520683453 ≤ n) (h2 : n < 520863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
