-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2568
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:05:20.877367+00:00
-- url     : https://prove2.me/submissions/797bf3e5-e51d-4198-9675-47f5eb406b4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 461690647 ≤ n < 461870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 461691897 1250 461690647 461690651
    0xb1b0a0f050706031401120302010b06040f23010f0309051c090e010618060f020c0a0b1822050c04151e0201021207081f170606060901020703030c1505180c04 69
    0x105100d0080b1000d050541f5503c00403d5140c40e841c2c9000d900500c1100162174200d40302180005071119801c407000115a5645170040d1440d15402004841c3c0c411644240e0101c1c0201c5415003c50384640e0025020368401d2003156912030b81e000400c610b02d9040514800010b52a40e420701c080b91580d01440d00502e42d0b81065208030000d40881d58000c0c6483c01290b08008100201180542c0700300320303580c81250007900f400d01c21529020041000d6011803c00a58001040b124283c5410500034810700b105401c072080c01c884e066049080c001d08405800807040403400e0101041150f01a0b01c0344422401c107881d20612441702941440c0f01610000009003564818007801403005640035000707900000303510346a8410f50ba52440c00000d0041031210014901c10440c000c034420b80e00c200c0e402d0100080f502182d41c541c0d505030801c019031161014541c01a0070001003040000c3c050110241440e128101490030202890b030f01e141121000c0398038091388848841c00c942c8150082c400381d9030600003500c003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 461693147 1250 461691897 461691911
    0x2070e01050a06082e0302010305060109052b0b090a030906050a081b2206091406070f0f050307120f0809070501140c060903090f190b1b0a0f05070603 66
    0x50a0a40288209000e0080c54130004800161301c290391440302c90149030903a002c900b41509100300103005d000490102e49020302042540d8050007048044810040402c111a908414510080303650070b000700003031850280040000500c42c0c404544200d1440008004840300c80c2001050400300e90b11540510038104008880340fa030040010398004400c1304640c0c404d0b81c0703281a0b000c6070300c185102c10606410308040c21400662030346100c0210340c01d07666011401511005078000241e0112011076105208000c2c10f000560034207034041115016020003140200c950b110b01d82903900c03400045a1143c2410003416100f038000443c2122500c052400031058034003200c00568030f41181c00340314144051004c122015108141c01c8960310182a0306851850a01001581d502c0e08078400141c17117400e401c26607880c2410565054a200040c035448440708924001060120f54041032140314901c40c0f000d110890101c080103608003651060282039265141e42c00d10700c0c182061500450704040c10111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 461694397 1250 461693147 461693149
    0xe1504081207051c1812020a11010f09090c031508060106080f090a030315050604062c060304060b0d06050103081b0102090f1306081f06050328022d0102070e0105 71
    0xc014030009042d68000034040c0d02000c4826101d044003c0c0244169010a50586c620390701042c425001c91040c541c00c0c441c0380040005590b6400094082800a94a442e0030441c040706500199518020750600041840f90f024000410a4064000c80003552041c030040140071380c48060654420240f14151141d03040c1040d0031601c60341c407440080c1c1095200c000a9034403c0300700a4440c01001c0040c4603540c2c0e640c0d20080613040d80c414045030f00e50403e0303104554404020121001c1c8505c03600514540c60750341c496442c20020022018119040401a000400007a96a1140c1d0740a90302507000e130790b26007042c401083d000d003941041e40a038590040c003484090380c17180040051252030171140c0746403c400c0b072140c0400410050784030100d148104e84040c1e00c00e60441c84282071442c0c1c22202031200070344503070901d50784400307104081c10000c0c580c05140300a1011184941f0101e8030003000c02c0e601440c0100c04220000781d6480001c00564070900107121580c042250500910340710100c02c465601d440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 461695647 1250 461694397 461694427
    0xf0d020c0904120e19090501170303010e0a0608030d020403050c0409020a060e01051603080627060f040e060c03010f080703021804080c0d0801171f0e150408120705 72
    0x280006181c102c3e02d2194440340b070700031041084841005064007175103001890032510180158490180240e10307040010506c1c095440c010481540128025890342c1d182003800082040014902e408856407840040f80d0024184010b01007400090380240e02c4a040d03042042c205008130b1101f0784128504401d90340180c0301c4082d064100ca00ea8181010851708504c0107956600c142d000c0401c89210050118003050f801c1078a2030702400003a620007400c0b00011910038942114035030502801e42441002a203c0d2401c511246032200002e000803c000382d440405910308081034401940d070010110044c4000c0ba03031105844e0003040480010244145540c020400781d61003d8018502081a00e0018003802a2a411250140c8a5108980c0503813010b0700002c0c02048227002d0800e008036050a00c410300c140c001142e914000c6100141d004500c0e810008400030081700c00011058050b183e12083c18486120f25035100d23a0064015a54a61410410802130032004003182d080c003205201c0380d151282d142c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 461696897 1250 461695647 461695651
    0x10b0117071211070c0b0310090c0923010e0102030702010804020d110303070807030e04060819020310111c020403050303011802042105070602011e110c010507020f0d020c09 76
    0x280c060105926074420031030b0004070034501c04800905192243c2007402036040104405800340092183c1c45484a2825450f44000d5940c03130088034024100740099180f940c08500e80c1038550034058443e9590389215206a1800540920180a802d0386e40d501035030481850f038030012007440a1894a44190700280c210100584080d000e18001c2980804201e8041070600130844000e00b16603c40d242850401c401d0743c03011400b1000180700160611142c1018000d82080d601d501c80540200b905130402212003032200c10781640c1c103120340701c800c0c0120042803080020050800000b26500c1c00450314082e8041d056060022900380304210800100308040162070644004030504040500021075040103405150170a202d21040d000b200020700e0703c05081c18220034826019100b00940c2ca410590032604030600e246000010000415252605980100705404691034440e0400220040b205d0071107008641180260b44421003100119104020103410290144000e000900346030011403070391200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 461698147 1250 461696897 461696927
    0x70803060303130b030a0f050f0c2b0605030f0f071a040f06030515030705030606210a0f0b010b1c090303140c090a08030f0a05090a031a0f010503010b01 67
    0x404404900903035000d00c2291140c55844180c000d00e15141c11842e5042d900941e92082c43e5490840944029080307409146c0c81050980d15240a9607070701c8201c0c00c4568400c286041c0d910b40c050011f410090200040d0007040300d030071301d0000340181c10032050510300019111460b5441e0300c1058000200e000024030003003610754003403d8128010003410031020364061900251818141040041441e950560181d840f9250840314600c25000e000309150b1070708640e00600390980c0001000031424200b030030000c15040c00031401804440e0304c1c038072110b05002442d001200e00bc11004483e000b804035203802c2038058444282d44900d0305119500101e2031002051041cbe400303986078003001d014903002c0d138400820341030254001031580c50494810802d0394852103560340304078003481000c00c404c0c000005641201050f0082c0c6132600c50040810303940c0390841001e82c1e80c081170161011002071809003105120389041c08030241c05050100014803440e0051300000c2c080e81c50104503004507a40030100c1000c041c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 461699397 1250 461698147 461698163
    0x3060120031b0f100f06050f10050334080c120103150608012c0c0f040b03070f030b0604060e0f04060c120c02030705060f01061205090106090c0809070e0c07 69
    0x4095004030b4240010b1440040f0389028516966030240c4541c0c004003c1c0110000301009082c1d207070400c00c8402c0d41000a0503400c0400000c07404500380c09074005640000130601d281005441060303c8100c081d2100d00043c41c3c010300b0401c1060340c2c44c2c1000c1400d4012a8464130b0b03904100380c00c80d81c01e1040e101440040d00150100c06e00344540342c0030781e0211010b40692402441401c0d140780810180c00d8648803d520408134105a04071004130228000c0300080b4014510b1050344800000c01029200020b001d80e0703d8002c84030000ba07012603000104009610032992000395103400340c1041304640040c1e201100b00701c2620200504e01040c80091a4090351120000030801040c2d4030845500f40c100c3c0c112420b0625200c80e10307045640000103490b4861141c0106c91180c2c0d82c04a1001c5090f10030301ca0342003c9552030a107001c402d40340d40c1160364818211300000036130303954505850701580c40038003c0b0b90108041700300b48801b1000904c0340c5000703454268503080755418801c1c16031801d84145400941019 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 461700647 1250 461699397 461699437
    0xb13051b0703030f0507030912050309070b0706020f040612110a0f0c0f141e07050d031b050304090603020f0a030b0c0c1e010e100c0e0108090a0204050c0306012003 72
    0x502a44c40403035402901c040400c114a00302c0c902500410515000340e0310341040d174200341c0c022407054041b42d100721820800350006915050380c5508642203030f0000c850381602408086911803000025100401d40350303450400707482c010740010046508102070007050b21010400344500c59081a42001d80004902e4640c2d41e0039813a08025401520300702e03000f880021a440ba50b00c60202c00035000c0070210078805451b04003d015070200d9aa8841762013960f400080032440100032a0244480b0307802c0007150405000d03a42c010390307aa070b41542c0c419082000d0f0301d560313a14140254105101c070055165000e40306e01e14001d046450f0310b40c14a200821035040d1180020340024120418010720b07040d044030003040d4a6000040c0c110f10302034580b8402a012a1040a800d840c48d05c10031301500a1901940e01e4a40e501060100110342c0880000c20b0041c2a1043c040040010b07102d911078248a03103800c0094903140d01701007000514044070710112094a0020841d03e02c007190f0007208482d000f4140c049885442 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 461701897 1250 461700647 461700653
    0xa0c05010507151a0f010c1e080403120507060b04090c05040f0b0a03080306011e090306020f0f03090a0308010602011e05070306080303090708060709081c02070f06030b13051b07 78
    0xe24034400d040443e42130200310440e40300000c0e8004001d800c1119405440402c9000448800e514014054405078800740410100e81c07421080484141c003030380019280c69140e0b03c44040c85a032800f800c0d0300150b80052144280f00541c850200000011031b01406049807a0702e60500d42e00302da0003818803c50ba96100c80003200741e1641300c0c200f400400b4001460455480c245101e290b00110703020b5001c15500f050078082103c070029043d07044401502c62005003819078860328002c3d00000e1410311400340400c40300000300e03643d00103184906203400007800d8540e0341e49401840408103902540c03d40e030403d10b002c2c05411010351202684054041c3c0001d0664601800f2030191015030311a00340d038000013060242da0300c0040740a0382a1140070b0300b2205103032640802240d02c2100f0740315261941e00084020b5150000c280c2d403419071448584100c03120580c07544d4450b03660f040c15502080c00b1a075500f4109a41d410044002426018011001c019514042c0301401083c015040002a0144001000010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 461703147 1250 461701897 461701913
    0x3150c0203040512100b04020405060318031612020d050c120c03130f090605100516170a030f1b0203040b07052b021902130902030a050307030509120a0c05010507 71
    0x51074018480d01c8041c031400355060b100e044901142d030171070f400d0240ca02900e003854002c4034100c58000c0c00140c83c5035581075010b1503190085602080c5130104000c6075200b1040c042e074070b0050034083c849400c00d1012801001c1d103000310002c4084103114040c084800110804500e6181050a5802139942e85915400e628154801c40708907201c015006000411040c9144200b00c1c140c4078030b074004201480e1100d0800c1210a5030f0a50304c400a40104010329120101280e4900b5030b911500e500c8070400003050b2a400107802656110000076070720038100c50a0f80700c1d03018074000d525009a09007500c803540c14000351644224011200110400107406040100802017941000d0304817100c1138248120210003011314035186040001841500c61801f040000d000640741555801059103031401c1c141c0074490064420f8500503039042c0141d042650110300d061008190141c0700340d4495580300e181604021407500b200d1180f41803a40013040c00310004003a04c0c0e404081c3d45090030059107402c160300d00020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 461704397 1250 461703147 461703149
    0xb13020612010b0c1006030b0112050109151b0c0b04020d081201090b0109140a170709150e0108060903180a09090501060e070c050c0d0320060f010504050103150c020304 74
    0x30801c0e0102000080c0500030714080c040b5012184252100800004007010a48a035808040e10510b014001000ba1141c522986c1c101c0354414000400d928100d6220303146580d02d03c2c4842d08855440c3c9003241c1c5540407c445040b06920320b0b041c420340701006d94236114264400107000a001d201703c1407279507040c010b06405a03051009001004009980c6950407207029100448a1501040d005200800d00202c2c080c482c00402d0341c05020355184d54a032000246601c0e002c0c403104407140c000e0ba00c0210741801c0c1401a0b80310340604102039228a40740400c50b0060890583c0184c507550408414002c101c140401103501c0715522602c0d982203a544070740011603020349a8080d01404d4901450881040819040b620859141ca0404101c0755540402500c087d5080032004015400c150250f08541c540410529102c9001740740940320b003000842c008000d140c47c0240582c141c1d0202040000305440848100e004d07080c1030307805004951640e0b49002e6172054060703c02400d07603210405815070074400c01c1914 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 461705647 1250 461704397 461704417
    0x50f0315270d230f0d0903090f030812070c030206152704170c0703060207050106050a0b0c0606010e0f0f13110c07050a050d0b040c03061406090703090b130206 70
    0x28000b61465401030b04651032580b620500c1070350b0390044034031141c0050664241c0c074070780100145000a011210307001410000c1040f0184100654049401c0c0c0b1110180b81c0990310072490540d0300d4526407155040104020420020004404c0701100040c3e4040717195a00001818559161505c40d0400140101c0806107001502194106000c10020ba1005100c1c0280d0160307038010055000888201020701c2441d075102c200303500c150410800145294000d0842d9405540009800354417040058940112540064102c80010803440e2403250107002281d08990242040d90f9605003490100f0003000300d1003810303803144103809040400c540340c1e450025103020202d1400c00c0040e04a42d664045900302e0b2142c0000c62244107000300d4141442c10040003602c20090402c81d24903c2561101c003103080040c0302301c075401c41c1884c0000c0003413007501a11141c0140300d20000e0040c503001c0107120b1100c2000385441e080505040c444000b041212860750f8000c501c0c0e0750b4203d00c4011131b0020448070f100320151a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 461706897 1250 461705647 461705653
    0xd051605030d05070f0905061e270a0f12080304030c05010504051c1407110604120b070f08040c0308090f030703060515030f0c010509040f0f06050f031527 68
    0x24880b54480c0e40300c03a00c1144241c4600c1c0030101070070302c03c4482c98800c0c080c95410410400400440c0c204002d119150840714800451401c0658400c5503003680c0726000e24800e018030101d07070740d069250070090040036214000104004a03c0c00310400000004158090900c0c00d001010074285442034140032181c60304071f8002d12042c00e182c0781c42e5664181800f004041616a00c0074038030002d1050000c015400308804940b03040c13035815141c9030642510200d015501c00350400c80040c0040e03048800c2c240e0113014045a080c00d1522440c05440c6410000b03e0500b041140c07000c10000420030200361068a41040c0c0f404c0d15080c42e10003165210341804003280d49445000000010002e0581046108000c2051404640141d04007810707a10b05130103492032025000505d403021154420701c050300b221000104040b800c81007002c400411102d082c14030300d24081e1207580c03c1c82681400200000c0308042a00104401141180c00c03200c0300d070001d010603580485030391070303c0d0501c0c0105040d80404090349042d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 461708147 1250 461706897 461706907
    0x120f0e010507080103150207030e100c0209010807090c0306030f1104110d0e010c0c0f0b07050f04030302030d470306010e0a0e0109170901030603050105090c1906020d05160503 77
    0x15082d0f1074244402c90b413406050034280700c10551030003030b03c40ba1640754881000134040c400802850828501002c2e0800c0b0007a80308002580c0d0b01d24200380200a02070260000d02d04181480702a603482d0380c2001c0a1604006003040011013040e01c07038411a800c070304c1e01a0328000600015000d0145003100e1218881e0100f500612807601ba8070150420200c1d01c02000007503003100007552850007a0801130480203414140c040424071156003681e08c0460342c07410714640070645400d5481d81c0c0151b00700f1f0300180d001003a0414294054806c1503007540441c4c1041c1c81041d154160304496058402641400b55055100c25040038841c08400c401c1000041c261040c82d0703110503040182100403140a50101d040090102c02d103101840b0310780c800ea4000380c1c0c081c9501205044040503904c04421a410140c0d80c0724004003241e0203208140c096410f180c058150601c500c01045901d2043c44660f07100517035440e03010000c0036000604400d180042c2e061494444401c2030044d15860b0408602612a000c0050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 461709397 1250 461708147 461708161
    0x602010e010b090f06060721030b01180509150103020904020c0d0807110705060f0702030a20010201050f1b070b09060601090b090907080a06030f21020d120f0e0105 72
    0x1010218000c000c00811900000800300003001c00d094030b00e901074041c14808117105082003002489984d00803001800c09090041c1d030b984104a000c1d01460004e0b50311600b00010350380c85119660284a0350b413203c50054103010008007040d902900e00c05d10101941e00300b18460340650140c81480000400840d142c0e000707000c083d501c2d02042601d940c005214100010062401400860303154040d42c40102445803e010034088260301c00f103a102e0340344030f0500100c00165070401031085e9051054040400c09078803c10302400207041814030b40c1c103690524040040001c54070002079404150401d0300d0315000c0b660403411500c0c0c802c1c240e01502c4405404200500800001545405048207030303500f4031510341d110204840d50007000341300747e4002f10702000710303041620640600d60401d900000c00036900756240e990002d00418600c0c221525900300d183e840502884141d40c003803040a60025103003220285600500090031500c600d1501540c0b2498009203180301e902041c41c24005500800c6141080c42c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 461710647 1250 461709397 461709401
    0x50c070512010603260d0b010c0618030210020a080402090408070b041a130803060f01090512011409030c1528090c050f01090303030e0a02100c03030b0a150f0207080106060201 77
    0x4001500d448903002c0e0910707420f01d080160207001c00d00e00005141441a00c0c6c0000c0041c2c8003007014141046108030071180481c40902c5017011051402c100c140c1107440600c0c0c080c0c103050301100980c00b0188140070914202d074214103074030303400383c0d044071000c480356100d24002c0e11a024103900901020b809800700002c01c0a000048c0d10b440b40c64680c40700c81607560543c2002d01054562004040036800c5c4003149050800307039080322045405042040007181c807803012451404a042e10718805a4455031152582c0d07001012041d00140c001019520703156100c00c4441d030341c00c50b40e11000f84602049000811030039108092508007a90890034001c205800003408000d0411050141c40d0503041032400200c600e8040c641d44a40481a151001101d107107840c207800500d03070301403070089501130000d401d03005a881405119419807540c54001501899040003000c44180d188042d004e0b800e2540c0500c001d21151003c8a8820500d107083c0400248000d4200d05100071540324004642c00c0c8080440c11a03019 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 461711897 1250 461710647 461710649
    0xf120120041d06220912181a0912031603110d020a1e05011b0c0b100f0e07030b030a030917030315064017060601050c0705120106 57
    0x1a6191080400b181a1400041c8100303440290344001035019000102e402000024052080c0b61000207140000c3e80b11203418225845420002405024214610002d0300000201410703c0c1511810a00c1c2903002c0c0c2d403054030440c0c01c01c0f440348440c1d0012003040710080013150000c8000c070160b000c0000051401500700908410052001d00401c060481802d1001a600717050503003241c902c039402095040082600f0300342d400d050340c00f5500c0355800f0408210b0b640c2122601040d0380c4c0c0d9801700c0405410406072000000c1c0c580d0141c0401482c00700182031409007a5800d031140010346031419200c4d0941078004140141d040b58041c05030f1550201415001000d107812607480c05030380c1c3c0c0c0c00007000800c140c507484204c5102c0300c60300ca540c00d402c1c1217040550181106410410603004c0351041c20700580c0e240280b18030008110090412000c1c444c40c5000c5c0c0b810001c001c0c21154a40210f4480300250301c6250052207035041001c00302d0030b005284001c0001c0c5004050242006010740113000700d0714007170101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 461713147 1250 461711897 461711909
    0x170d0f060f080606011211040504020f0301060f0512190e100f0e03090d08090d1a0103030e0105040303120e1920010f12051f081510050f12012004 64
    0x16001d0000741e40d40012a0780b80c8030307a1050f560080c0001801000d40002c0c0011309854520050502000ca69903c540c4020043c0608100e011b07506da40c0340c42001000c9081c040030b08030030085c0621900d00c280d10740c400030a4204507190601c1c01480e42c4003058800920500d04240558800c0785818000c000842c1e0000c0b014030309202041c41a40900c1c40029503900c50000740740d422120710701e00480420f5040d0003a0121741001000803008290303a032603414690769115100c030103240c400c030010801c01d9080401184145001e080c00d0b03060a1550b00d014020b02401d90040a0064950034181c82c491f405005008a2960030344c41c2d8140070245042281c2e000612040200120001625680c074640c050748109640b0101c07940d820040718840105040034010180504500f01c1d60b02200c4c1d1030a800740c2d0303080005841f0741c0c40204000305203a960903132080800f03042031241c1405400140a2500d170413400d40c03800b0741d041d039800604040c140c1d40d543c01030410042c07042e10300d902e400c0107007042180d0000070011145 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 461714397 1250 461713147 461713169
    0x9290a0f02210c0c09010513050406020d05091b030a08030606130923101202192c0f010b04170a0503030112020a080c130b013c0516170d0f06 62
    0x35061092583c020702a8650022340e00d000c2c02c02002d9550407255100380300f44005810080700c1020301042e2038003a40c14010a400c45075200d152202d190600c2548210220000c0c0543c5550b9203868240c0d10002d00071a0059000150400c060550001000000d0158180800c803680124280303a141e5421216030b4034a90458402243e102c0ca584490041a201c60101c15520b2141a40c00c105c01031200d80b001d140a81c900b08000144c91440c4180d8101020401004c0c80e191507241c1030100083c20b00030403034090010b682c40144009940481554251098000450ba00b180203010361450a912008010054840040003242114048a402242510a95203807400c0713600c1d09116911003220bc0d503207581000c95800064094803c03a041010080c006051011158001c10840c1400c80351600441e51443c088400c0c60486038903c41003222040c0f401c0c40c0c40c0e8200060f0b00c0f0954440b1109100c043e2004104402011a0111560840c1d5150000c01070420606550400d08406001030703109118181d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 461715647 1250 461714397 461714413
    0x60301060f150807090b0a05093d05070501020d0b0a0506030424020d0e1c020c0a03140106080d0c05010605090c191e09290a0f02210c 59
    0x50340080200065070616070303210b003403000074280880d000c030b0008000d42c040001ca840d001510a090b54000c108228169803081d42d5000c08500740500845010094039505031155046250244080020400921902560300d01000380741d1045070305000719803000e030003544002124a21500c1551083c48010420b0b14007084166885041000d540000c0728080d11b4200d40c00c01032058446a030175103c1e003e0348081401410402d030603110360101c51002c07890540680c4160621803506840c24501c42d030f00c49503840104607004000010403030400c90380c48000c104000f6000768403000c01080d04843e001c3c041a1044682c00000248010f1800300780c0b034801d450a52034000c01181c03038242108042d103d24030054041d03151036032400016604141c0340c4190030401c908466040344000b0081e2900e941c545075950349404090a0000c04000d03034144440c1c4824500f0700041c1740c5120b15100741540c030440c0140c1099540d0104600c026070901402c801d111111860510310f4054958000001d081c50501040885e0381d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 461716897 1250 461715647 461715659
    0x402130806040b010501111b030102070c121103060c040302010e040212070207060f0801150c05120d140903160f051f09060e06071413120803160309080909091c020606030106 76
    0xd0f541e41f10302441e81c2e03080820905400b07840042e0303003801c0c0d20002d03000618003a41d0b41c55010040945400245900807060080c07014006030581102009400b00c0203002603040580890245200d144030007814015440c45840b80c507034030360303058440c00300140030318604034900010002c0d10756401d8080e200100c1c420b44141400390b80300308001d90503207a01e651030603c80c1c0500d2105440e0001c0001003118039214070400d129000208401410400038420000f040f004001c0c00641c5203014020088041030784288158040e0008005424034a150003196019050210b030814a003080c100801c851407150304c08c10081480ca14580c05280b180c2d000d00300800218026940e10b035182c072401d80351903000884001d55a540d1184c0f2500400102c0b16111120301513540d0303403591001d09082040195243d20000c010055001404581c0c8104c07a0b8461500304422501555814135500403940c82d41d010b4400c1d003000131603031101003002034440c405aa851811014800200940c0c1d814100d0b405402542800000519 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 461718147 1250 461716897 461716907
    0x270615011e0806090c07050f0f0c01110613050a05012a0201050720070911071e03091208040b0304050723062d070f0620180402130806040b010501 64
    0x80c1c40c0c4030b588803202500e600e01007050003080502000303844403040000000244c0200031031401254230402909035640503e00c07850030500d594440d5030500c07080e071240b03254101e801300301140d10046480340d94400b580c40d030038414602600342c2c8000340319600e07014009c0740e510401c0c101c070584c0340b40e00e801c8800032000c0088101d082e25000e40f07181c03010850014008008419a8011080c40603140741140c00013030755603111801362205800c4241c00c154000034801c0030302c5100b0911010103036a20915403207140b2659402081c820407031150404020300c1c20101390802c407801044600a04441040b65201c0c1001e080042c0c98607002d05c944080500a15002d45030600b01c0340d072095060200424045c00d208842c0c4090749001c0107815002d1000e0055140d07443d0f0025494040c01149020b0900b03a0400700d2a440c001e0300b01d4841e250b1b86000c04010390905405010382c5030407590200c112440c0001c49043d102c1c0424044d0042d0a00d85c1c0780e4040410000c44e0307030900010280d103d103009000b6001d06990398401074070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 461719397 1250 461718147 461718197
    0x306090a020c0a020f031908070c0b190302161203140604061202060702040e070f030b010e0105060412030e090910390c05100e010b100827061501 64
    0xc00d810007003e031000751510550144401e24040c00391904894a66442c080c0c500134028125900400812078009000b044405103010340304036424545420100440e8065420303010a0f028105900000d40542208924003981c0500340d1007001c211301130700c0c220400b0b00500b40c0c40b00e20803240044500001c0c21890b00380600c408440700c802e00000300070502c0d0203004050380a584181d8215171035252807280ca520403c4010010200801d190341c1042c2945400d180112040c3c2c0102c024070644401880555a400c0c219030454400c181c1c01c185004662800750b68041e4010061603201c0ca41700104620701201065850102c170701d884007049002d00707200c5494650903440f480344001904401e148014040c21041c000d9465200b4242740030001016038a6038680100000128402525074001c5054401c00740100031942d8421a451000f10b615080c00a0000200a000020307200009a101403000c00c0c1860352440380d0018001d0311014607100d80d45d46030301014604961300084403280c14061003924582e94074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 461720647 1250 461719397 461719417
    0x30b040c081b1c0c08090604020609040f1829040f0b040302031b1506100807050d021608120c040f03080a030e030a0905090610120c0c02090901020306090a02 69
    0x820705450340014502d909200b0082c4070082070007004160f02c2d5880c8101050046103005002252808030044018003842001d007820b0b4280c0e01510600006a80f20741c141e444400d8241c400042c911804d840c03030400744c1038212201079151001629603040c0800240d030441c4032482d007036400d020403403c481c0071030000504032000fa01d4191280002c1c400140c2a001c00b40d04107000e031044030b041107000c07050300c01c124030342008011290380b02c03d5590240601d0081010307408001111140411046180050207460001b00f84104002000a241002000c80c0d8182c0e08454141d0151405013066464010b03030030b6102d111101d80c4640002c0024181c0e4604504032030075119000f0f02c401c54185160365900d1580c10510f0315a05151312000c8404040600700003070080035199540b4222542c0c9003070f050224000020700b2860068041c4212664160f0300300c445a901c8100500300010b42c160316100490b45006001c4000b980003c41c5414099141815005103001d01422940301402d0388440d00c590040b4810230440d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 461721897 1250 461720647 461720657
    0x3010c110606060d060308040603091e030215040507120b040c08010528060e1f0806061c0807021009060206010803071221110c010b030c0a15030f060603090201030b040c 74
    0x10882d0410300041c20244c580b0b00e401080c01626503aa080c0c660300aa008000040d55400340201030112605400c603031109041d20764102e012594400a4941000c410350280d0000c05101003001c01c41c013000114020407200c08910240c1c00f091500e403c40d6402520161540e82c148000800c4039001071095500a0642400c25420b20600410440c0b0954040c104800d180d5500d00d40058000c40881c89540300e98003140c44841c800c0010380300c5419480761500202e03641d500041c02c000c0030b61141209048222888100014444c11602e404035082c407507850000d4004030914280743c001c80d0008424829620680c095079642e80c1c0782c50035070f6074a000741074001c0c0071010f072a00725900483c05100b03803036002c000803920f010900c0e89080352001641c10001040100c4040000c150f944800c0a10440c58620011400750544160300c0c0002000407a8074028104c00401c0c10b80650010b90113070380400311182e100c000c14010300d5a1144041d000300070740da5003640480d007040c603184500d280034442d01c11511055125 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 461723147 1250 461721897 461721901
    0x20a181b020c092509031505010b16050c061201150e03030403060b0303161b06030501050d0303020901120e010504120807080106120f1b1803030207030f020f1e03010c1106 75
    0x800a4005024100d80c034044d0f2140d8483d040c4180101d0b1540318446544c81d0107507241e24500e04503800103104010001d840c3e1404005001310304e100c50849e40414014000c20744200381a003002e42c2048100a24a588440000b8500f00c0200640c4861412254040343c542407030b001c1080166200c0490f6044258140c0003040b0601c00a191030740700e26144807000d01140c2c18120903400c0d810002d119924143e030b90130034581c2c494072086040e0088601400c850b00d402e1001e540f42c4004944130010204004090603004982d000059100d0303018408501001074003401010003141d503490080905480a035040c20364801c0f800300301c500031101ca9020758031503030b9800f2580c2c0c0f8245e000c4400044d5070800403951503e07507914021701d0001e805042e65091302440449408002201c0240500c0f044191b10303089005800e070300b080800d030045800703400c50f81c00c21181040e6240e50310000d1140e01980031040da200c141100c0507070070020381c030404201480003500204207041d0544420f41d02c001d400c42c1407101e41e40c02800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 461724397 1250 461723147 461723149
    0xb0708150118050909070e22140a020a0f0e01050d031b140313050a081204120c1701020c0d02060121020301090b010602060405070f0e01140d020a181b020c 68
    0x4402000c0c011490b00245191070302d000500001e000e03244041e03030341e010f50014440c2609804101c0e410640300c0210b001c01d02442031074a0016074560502a00d407201000c42c4400c146018840301c08107903801800c1240c21a1215071408454a040c000c2500c6540a40000300303542c24030b810070f00c40745030f01074407209100c0710344402e03201d0403185c0d21074200c80013003900107940a82201040503224803003c0c844180c0505041000780160285664400901580091080d0443c0503001e4116815114641902d4541003003606009141d424554000384a0300360b01800744101c0c2a0640c06401c0c1020100b0a490950080c120100e0f6030316028012032000c90524144221504006040707840001e01c0500049000461511b40300c0c00018260302841c050b80189040108201007030000ca80079021048011501e01c0c208413101c411810140a0218841d0071070000301d81c035541301c10442c83d034143d0041c810b000154a58142ea403441400548c0c1c103d0302c03030810507484c010390110100c4400c4c2150320b5006101d5688108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 461725647 1250 461724397 461724407
    0x109090c1401021c0e01021207170a03150609080d0e030601050126010f06020d020303271603081e180d15050c07140c010f140d090605040b07081501 65
    0xa4159819481100c481c4107001800009084000d10301e031729410b60012080001905080c190104200c1c0000104440400a1680103403440550341340c003181512540c40395800c2c1c000b00030140c00000f000c00102d500040072544529440300381c030000002c0d20000c5a080724182c81040103c0121641900900c00502c001e51041c083c2804c0380d0005180d160405115000501ea500800c0c0c100a02402c40c00030244101c0340c040114090050082c0300440c03540c5042211011b1048081d90300d00c0c1401d4082c040d10940d21010040f001d44210a15130441001d99240303400321b0346910941000c21845010b440078000401d010091710000324004160701d04a440b80c3c010020310503070444d400c5a801c000104069074044070fa100d00307840b4012401a107665001e02d410a60a403503180d281481d259071150403d0592640e00c6800703444500362a092110301c01541c0100f4500034041d02d000d885000d450050300c0018000340350800381c01640540303540441c03501c804404944005045400c0304801c0e10807034400c1041d51080c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 461726897 1250 461725647 461725679
    0x3121a0f010912051027061d0d0201050105100203040b09040b0a0b0703081f03030e090613020a09050a060207030f2004060902030a050601031a190e18060109090c 71
    0x14034002010b80d880e50b0540060807844071040c0c03219881402481c0150141e88a001d054002400990440100f01040455504110000100415102e03000010084000384000c5922000c00040d6400414141c030024004c010900c56a403040402d0a00c0c605814008421642a034035542c844918000e00d400a010180003d408402c0d0414440c1c00d001030b00f09848400740421078481d030b8581c072050810a1035008941c00414400040104a002c1040000d400081d0b0303602026040c0c8221005030340b40710000303a4403601c8482c0440154000503040030b006a1101c4c1c448180c540c1107645184213521110101d907115440d0100410309440b103048240821002c22120114240c200b081c1c03424031110704041810741d00258030026410341c0120a000a40c0302600645a104e202840c1c00c0056111680e00d400107119102115809076000c00510009000c030980b0440160482144800e00c504025000c081c44411903003200b071140c02050004529050f0900800c0004c03500059440a1507040a64080b000096 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 461728147 1250 461726897 461726899
    0x1e030702060a0903030e0402120610030e030301090e0f120307180819062a0e03071e03031e140c0c150c0d02030412060518070e0403121a0f 61
    0x148410001070307403507400428440e5401c1e0b41ea00e500600d94038001d06001d1030242c03024442e41c0180418078110113580c005503882502281e981c000f8514681c8180c00505030070002d400103010000021840004541080d400700c82044101c480c4c48101c000a0b07038076581d03e4808035035507000410114007032030b20a012000807158000305024040303a5a007c3d42c1d00c0d025001c02a01d61843c602c815560034402a4402c0998a98542c8d2074030003c0b0b40141408949032145481da00705001401540e01000e40302084940080c1071401c0a541020f03d100c1c4d081c40c0c46c91002d210072000503150501641c410300e212000d90184100c2901c4400b42248103c91030074041d041420300d101c81788509188074003295522160050710712100301c15079a981c103404035900e081c03250702e090600c207546c410841081080507815100234a03c3e0002070010b403a0300d895640400c0e0403507002c01c106441c410710130086101411824800d01031442501d51440c043c80a100305005e030381c015092903103507202041c0d10300007a0800381c000b9083c900c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 461729397 1250 461728147 461728153
    0x51504060309150c031b02030a0806100903060e060901050c12040209060111100605040f0c0203030f09070503060726010b07170408011a0907140d020d380108091e 71
    0x40e10b40c452048a00c0021358800094590800c3c00c40d01440120800c0c0c8144244081c40c508100d640e030107080c04002600d90382c040d040306103500d0369052050003500040e645c4118288400c00031410065910030042d10205e220303528240c046060b54044400310340c11205521148070311581d45408000c0d585a0080c0882c0c10303c08030380140c0c60807403402e05c40c4040107001d408001951a040000b0b001c00c40382c04005040d000e920f09482041019000000e0f070764171981483d440080b03944c0d50f900c243e08100c119440b0503010302c50781c400d020711103030030903105c90b03841d8211403062003075805051444103006028400c1c00f5040030f00b0807640c00891082a642c4846600c3c08143c00e1510356150649400c41342021020030f0500d1610315003800c40d10b404604203401801034a4072003126801e14004003024890303014488140c1c0ea0005c0c282542034150f41000721005460001d0b101c00f8200c1188641d0011000c820041a1040182d5241c1321036000e050f2441c081c40c07004000b0038230700b4880c20314951465182ca000464502c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 461730647 1250 461729397 461729423
    0x11032502010f090605042f09040c03140601030312090803040602031e0c04051504060516050106050a0b030613140a0f061a1b0106051507151a0a051504060309 69
    0x102ca0003204810307031045000007042d280c42c0c18a01c80d283d8412a4202d1590281800c610800702c00140c802030120003120a034091b91903e103060807941c26164001802c28001c0700d03a11180c0040840e003181264003a0302c6035048000e883c3c038050100d17140034030018040c070024000314000c0768450f409142d00c104110480740c212100301c07040c0420903604840d001c9611030000f400384a503041c1340070800c4c98002c1c40a04c1c3c5c0d007002e050820140250041d89002204014011142000d20000350400c80c028400070b40091603090f1200311441c019030040b0380d0345000364040c52052125103040d108003c106030f5a01101911a00c800451038007810182c6040607040380ca480e000709000c10710382100701d1002214003130b0550710740e03039060909124510703500030450070f925083c2c0070007154654484050000700c0d0640d419690706214508101c2c9c1074403081d40c0380315652030000001440c603561071003040286411204240000d0b80c0d0410884e0860105034000a02ca80621042080b2402904680304061280da9082024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 461731897 1250 461730647 461730671
    0xa030c030e130f1d0c01140706020309030315030a0f110607020913030801060f0c0807031b0f050613020a05060904180f02011d06071212020a0203030108011103250201 73
    0x80100b49001d044607030b9440c0c50320301c480851445030008401e0741900320006103080f0450284c5501c111802241484110790304070b142050010100c0b15001d80c042c03000c5459080c880880b680d81d03001180e641c1203051280b0780e06d2089140000e09034200c0796001c02d030040d840210340c0d5500315810f15a41125001f540030b000c410f0060b903d10341f1a906c502d803a0f4a1540c00e03000c8908000b4900e20042e8020424045203401c0010829401104480079940000706641c2d07072442c0745012100d001c0c00000340c403001c054080660041040040262880e00d010300229038694070f0b03040b880d80407100007600c02903006090ba64200214200b0720050700480c2d900810002e900300c0036207214200316180700d4045480d007140304221021980c020315040203008010a052060b82041c801182d09849804400303400c04200d807030044416841170b90003040813401e450040d51107852180020b95250028001c07e000c9500340b0305440306500310f840640744110400c0c0414078000c18241c038520211417080b10410b0841d501c032200c1c0020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 461733147 1250 461731897 461731909
    0x6262109030a030e180405060403081023010225180b04090b0906010b0304080d02070c18091a0907051203040e04140f01050601021c02340b0403050a030c030e 69
    0x480c1c003c0c1c940e4040c00c0782000070022245c10b02c0f00100c501035026000e01010900001e190b90340198181408109038640360510200c0ea4101e90100000d0740c0d1504001c6811211241d06400b01e01c800e8085805c0914840b125a08602d9194044c00f422580703028100400550f4100714100202d1003d4000f40c034445400c003140c2039031008001664050854000d1048021040143da80180407200360075045040540e1010154840c000c03002d142103401042500a0040007101d810060600c0c085803290240c0e03c4500c10042c0c098002c090783c0305c4001d01e103031545803400c0c40041c0d0710492289015201890905003000b60241d81e000b00b1642c244418403010442001c0342ca0480d00590003021030a40c0ca0100c0840240307030182800004031181d051005011103a60001466662180c0326421204603a0500308200e00c5c00049007001d6102004840c005407001c400d207040c1c507181050006034a80c40e25201e12800d03020784100d1000420940c0884030740d101180c410050900014441d01d000811a0014070020755 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 461734397 1250 461733147 461733163
    0xb101214070201060503070e06090403050304020415080f010609150915090f02040e090a0f171c020702150f0406050f0d020a020c091f0b09040e0607030626210903 71
    0x3001d40e64921045c0520700c0c00b041000300411000c0d2800815207000c0c000703d0007505014000500348540800440c04546d26904a8075048001685201c030321541e81402c559188114092010954a01000424802554004c80c2048044003200b4240c00b0701c1e001e411701c020510b0390840d49018984507004182680300b4001c0074007802c0e109801503101c0d82840404048170030050110085548140c0c0c8207800100040d9800350059008044081d4100c81d882c0616140d1244000c1400e000e02d00e06508500c1400301e40c09048928001d403000e10b080240f400e440d1009104464002d0b00c030760000e0000b0820288203074001c000c91030352898880e0a00c808400b02a059030004110000581c20080b0400c1c07c41c100945500d9000d8203071302000c0295585281401c0c0101503038058600140c0340001d101d40c05171140d0300085103012060040781c4107440e0205005009000500a01c400c02c001c410359190214801c940900030015660003400002e00340002e04200f8000d550a074605401052190204958060181c2c0b4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 461735647 1250 461734397 461734411
    0x60606090105040e130b250c0512040e01090e030705061f050907030504120509060a050c07170d030b01021501120c05030708150903070b04020d140109060603150b101214 74
    0x103465550280392002d0100e5005025103803840031038454a040d6070400044488214036070400800923080fa06110b0300740358149141c42d00700307800010001001020802d130f0504a41c02004100b004480032503044d6140d1080c540060250740c0004089420780781c3d4041101c07400c900106106840596a02c0030078041c62003217946801003903644040100f8407500410b110716002c80c5240003450080b0b0100000d4142c0500d00704038080000c08102e194030300c3c4007042a540034282e43c0043c0c1e40c072030700c0444202c1d070390f050180b040000203410715080301c00035400020f101e0707001031026440814503070800c0c03248404c4101c0003005075a4a000b0000004041c2c80901680d03003e002d4010103001c07814440130039030b8000f01c005820484158410440e40c408580c44411240c0c109504940c50a02c0c145c0c0c038100324480ea024a0104049940b80041d102d04002860780000222071041e131035440d09101007441401180d6550031070541050709040c2e2044820b114682c500e50642036140002071400300d8035503000601c18112108 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 461736897 1250 461735647 461735671
    0x30406050438090f03010b060409020d140406020702030d0305060f04181205090a060203090303030c0c0a120e0a0509040c090b060d05010305010c0908030304080901200f0604150e060606090105040e 86
    0x10b00d028245485000403184c02680203002c16103441000c40c0303541c03041e4441c050700d41d43c6c0403641110180c000e4011803140e0061014480c3c0c039080c6420b00388001e62081c1c90491003881008804501c0c14001d0040c00d10070751000303007445140c01c19a803d20014090240b402c4051a020350549800680d240c0458002501242d541c151101200c3c01401800300c07640d0462400c1d58030510107031085550000442c0d0703000c0f22210f036081d124003406c6503051a0140381e1030020180d020248031441b41c103a0140c404024454100c80712050107036103d0034404040020344010b800c140e5554400d01c0303a4001d83d013103000b4001010700314030318081a000300d00c8101c420a0b0000c0b039441c1d45840c49155090360091000303010707100c66405980f550905a0314401c1d2441440c00b024144007101c000300982e1b0800110150b680741c5644103a4a081c240d041c0c88507200c1c1002c80b0129080c4034580005010041c4a1103284001e2a1500040845442d9841084542d812594619041210822010807440781e40b10155014003501c9000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 461738147 1250 461736897 461736907
    0x16021c0f0507080c130906180b09011404030f0f2a0b1f1707123207030305131d09010b01030507080f131e0203010608030406050438 58
    0x441400c020701644a95840d034043d44d041c2c21a03586901d141c540e070349030111000801c0141c07860140e000d440e901c040703800d1603070080c0c40460a10010203083e40c0f060900900070070003690400700e01c22000c0d80503180580010810360001c0343c59809103071421000e2019040a000f211155210b04403090107804d041062069010403520411601d0754030f140c0c01205121800d920042a8512070401c2d260a1151034045030f01a00c03500b264140a11800e0301a050002070042103400e1400e04039010380c280f42c1305000e8244460015401e002078402c0b207400d600945000b802c0b16505e10784044990f82c0090b10366081c0002c0e9040d00140c0c8800b075031081c004a8060541c2e206152a0440c159421241c1001190b070503d8100f2040041c4035134070200c403540c044844a88041a40ca81142070306181001010013081013100800c04643d0409000754012107501c22002400741c0da4803150544d40780c0c0224814103010650910050125100140c407001e0404980f10500100003c101003803211000b840d241540000c1001507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 461739397 1250 461738147 461738153
    0x314190504062903210306090a060e0a1b21020a0302040f0905010e0f0903030f0702010e06040b10050109031121060a020703030e01180605062106160f0516021c0f 71
    0x200806480a900c80401c2401038403183e01720500c002445a0300c13803440c0c98009038040c07a03d54019405041ca003a040801c1d803500d4950040200340b103940078480f54100c142c0c0503403224450010703145204098070b5025210005151032001a420204a02c4180368003804082074090f240640300f002031103004008251545003026010301544040c1c102c2a120480d88200241c2c0e0702e00004503034102a103100b11404640c0d42c554101c0c0100320000410000d0702440003800280310400d54405d0084109050030540141d444005480d10035082c40000c0c2042c0d0b102414481c40e160058100106d0650396802d10442d908443d19141400c030201c070340e0005140e002c83c1070018541d16208041c1000399440c000c0002010008101038003e074002e100420991300c0d000056426252941e404812a00c1c00c1c0103014442c03c001c0d00251180401c0703d0100158180c0084400124460000c0c1c40b04182e894582d945000800104003801c980c10000c142d0b044400c4999a0000141602241020f540921554401002030346 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 461740647 1250 461739397 461739403
    0x91b0105163c08070b100b1306020705030d0912020f0d060e0c01050c0a060b12032d0918040f35040b09060d0609050708070314190504062903 62
    0x85100d04000e42e40400016030490101e540d0300b80c0040703400300155284843d140c40039146400c0f9042200002c9840840c080350003117604140d50b21f036000c0c0c400c21030300d4106042c0c4e546448184d000c001000d8032400c110640310305070030703400c214000340001c01e030541c0b41000b02d4590604610f0440c1ca00d60350b85500314229100780700292108509181c1f682c0b4000c510000181e50f01c0c69030f034010f0301c402d076980c051880503990798060200c24031000d002d880d290640c0c071404034000c0511034a0400800041449028030500d024211071103468020844035042200320050400e13040f004104940307404011038441d000c01e03911820031408100c3e5003540c10100341085030500740705e1080410b10a4044082c44207101ca8019642580d00c0b504051702c02075103401c43c00310b010340503101c03907401900741501e01400c1c4191298070881e00c500c50307084c03501e09220310100001d0424548000300d4090303c40c10901800304001d003a850f000a50054001c01020541008596254031000000d010b105000464200116410704080c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 461741897 1250 461740647 461740733
    0x11040b07052e0b0904120509032e1802100f05120406050106020c09070207090e100501060201140f07050f0702010e1504050112050112060b0102030706060308070209091b010516 77
    0x1a600c0c3c03003044c245680d0360311a449030b00d540340381130100100d88d0320304640b070810620200203403d105030071401010742940c000300703d0000d840d03113000c42c2080d07501c0309071480c0301d260b1000b12a400303040c00304c44034412001154400d21140400d02084410802c054610444003040b034048c9005800000f215458200e002c1d00d840340742201580a003607100c08010504e6004a4a542150a5181d0104d01c104090203628240b402449000c1100ca28020021031410780c150301c041c1d0144600051001551070340b8108250002d0115244800107104000340e102c0c80b050036018210052041c106004224440400185051401d0901c564170010200c1c08008560313110b07843c0e84440d1400c5008102c15410f100f12a00001c6c44c108e00070300150b45403220010981d10030021520f41981080041054035107902e4074400580c01030000380c2c4100308007400729543d14400300c0c0402003000303040c5200300b4030050700b00191907503005000c092186000681e5240c0100d444024140c15120321203050744580c00511104000316100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 461743147 1250 461741897 461741899
    0x4050303181c141b060f0c0f0d110903030c0a1e030e1c14010207290402011815030902090106180603020f1e0901021011040b07052e0b 59
    0x1500802d00301d5079684000c08004224a00958420f60010981c08107118114071081c03900101c50701c0c124419008a655070040d2000740c034031002d40d12030481e01c0c44a80200000000d9031482001402e1070700760f03a5444a00c00c5a0b0000c040ea040440074000a41127070080010241960003420240c010880030160792148420601200500c02d480354900400a0f002e010581c0c1c0159620072040901c0700d0300c2e02156490710345c4105800c91002440d01400c4c082c0d0008001102d0804500c8424805072048140341e400040300400410340640c1e5980044800038008040f940481d404603001144070b160703100513280d4040103a200843d0248851043c810102d0381641710b03800b00008040030000411548100d4011100c00d4031700540c0750310802110f440e030b0744980a40d13a1094103031111070071284800c0002501404000740c098030130000000c00312001f40c60059040a406070402c0001380011620b020243c80c1c254010800c076401d0002c0c1c0707454503842600c83d00d43d602c043d1140c083e80010b545101c0c0981188060 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 461744397 1250 461743147 461743153
    0x1513140f010b090d0f020a030f03020f1f0f0e030f120a05090a020d06060807120203060a0e0709020a110d030e0f070b0909071707030c020106090608070509040c0b030405030318 77
    0x302d468088001401200c1c0114451071421003081c05124000d81100041900185840d0400d0350760b2504112000039100101c025029400d4403030b454040106035000c900360039964216a201c0c060b48100f0041203101e01d0395840c10340c6c0c2c610f8201d41c1c2c1010406003001e20f00d03d4009070f46c5e0b0f0002e8085440e4620004100c44100c509000801c52095800314020f03242e13950641c0d8490084501d481c0100181a05070403c032842c0c442c1220002e0220308031905490a68000e030107640c1561258200c0005a42025aa0300025401201c08010300d100541c01489031249900d451041d011504a1160804d20141c03018030001e5284c07400c2e041c80c03040501003424a120312000504000f031400071108802d0103000c9603a441140d0350000580d03120f0240802c0240d83c0060b00c070704c1c03201e4a0b1400c0007030300911407564404019071034100301151141051040405507440d00d40144111480c14040000392003000b403049071041d40740e8000049444024010f940540d20079000780d512850910004901001c1a490501d00b9074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 461745647 1250 461744397 461744399
    0xa0606150e04021c1808030a06090b0306040c0501270e16020607090504051017060709080a031205090f0a08090f1813020301060810021e0301030b010e1513140f01 71
    0x119421307100f072451650307000c02040d40b0340100c181c140205c0e5110409446000d00004001c41303082150b108a0036105603607030030007902d21074800b45039446008860082c030f0746c134101c041400700398040c0c1082a43da041c09006ca012440a5214004480c4510340c0710000c6408044c0c01e2144800b95a51f180d0a00209803000700340c94603000200804c01c9075203209481c0a9075480010450007200132035400302901c0447c03540d10340d484c5801c0381c0c02c1d0f0f550350884145000681e07044011503031802c046450102c1a80690b544032b075a42094032298014180a083e03840c0500c201d41b11504400014000e107850300e4095aa02501d805451040c0181c02c82d0000f1102c5c412241071900c0800003000c42d00d0302c1c2c1c12000d0380008049034651840424018092500560901d01c141d9010020304ca0300c2e030b002000101704090901c1d400100c1c00840c0306041c042804000c2c0304081d141e0041c05000d800c2c030300c00366209003410760303c824903000c090205045291603810081d040d41c407a0038041039030303003c19680368202800c29001741c025 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 461746897 1250 461745647 461745667
    0xb030609030703210f020304080a030e0706050a1d1c1b06120b030a02150403020f06030708220b190b0f030c0f01020a0204110910080907030308040201020a0606150e0402 74
    0x1d0014030351504582c44c1c090110f01510304a070361085113107182d0784500715a00e0826082c5001190402090038000034100310200c12104008690b280407140344d0307103c15040c074250711001e0300c10140802400003109203c1001e4010395440808a150401c40200a030a1400d504d0500e92018054003031005144400b81c8000c1100c107130702c15400040300c1e00c07803e800a03039940d90030300190078842d5946d0007030340c4102e940746000304010340003004004032842120640e10600a58040c40010700084401601050f104000501d81c9203030020b03010180501c1c2c0c000da00624100360382d804810b6005580c244141a070790044415041e10034031503001c0545045440300902e0444400003a0f0741d09410704994062003464259140380d0f4003c00030042c045500500500001e400c00d01c0401d07498110021f040d12400500507095981801099928082c1e401d0002515140f030858905648182c0f02410490440c4920586240426124894000a4100c404020781c1c041c0850300000d041d00c5400e00320b03511543c8100552070b00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 461748147 1250 461746897 461746907
    0x1a090c03070801050d0f1b06030f09020901030305070503070f0f0c05010e0904080d060f080a110d0819050d09050705150c06190b06070c090f09050318120d030b030609030703 76
    0x11203100305c40c0662024103510308510b021440340360040c541c4101c00503808540d1200c04404041d03d14a9800f00300c1e0741c0080051b5429200b00e1000030307400c10f508400600c00b11703220303a00a000d054007980490385080540c4d41c071905d5070303200c20a042d1402c4018244040070024040b0000000700400d181040031001d42d440001c9400304040d1004058030300018500500782c1c00d5030015001804000360501c0e40f84c0ea11400691280a1603004450001c15007500c03c0d403a03d06013251044c1c00307400092890801042c0c032038205001d0313004448282882005e02c00840154518012071001c5031140c0040c100d03042c0340406002e800c10160300d5411003650300344000368044c0c400144030b030340c484540c10071500d40d05030050820009004565205400170030004448041c44104120350080b1184244100500050f00080e00d08443d040344005040c3e400410584510000c1086e0b03119480000800035410050111840742c0b400500c03030300203400320741c55003030280700791806224880d409001540078600d004d43e10f42c0c00a003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 461749397 1250 461748147 461748149
    0x305010e06091501090f0f0504051605031b070b01060e1002031602060d09050a081207020d050a030e0106051c0c05030307031b29180109030503070c151a090c03070801 73
    0x1803841e1004211940a80c883c00e10880100800e02d05030f01b14503140d44414004200a000b0b9a00031401c1030702041000f074002440c2c182c5071034a03945044c01d5807980340326000c00d40c2c0010014a9440c03000d018100100d400e402e0068003c06a6440345080703010303a90280901020136090120640d00706204030031201500d0706540d00582d074100c8080d075030741140014030300040104c0c100107880c510450005008002000d0014500f8000750b50382d41103d17984516049a481070021000c6000810078005003900c1c1d800303508104c240f01402070003c03488940300c902092684581a4020010a281c080e800040c00518040400900000d8020354548011620f024120725403040c0c03040c40c0410615400800d1211740d80c03449010200d030104407801c1802c4100e03044a01502600c1019281c1004440841000b20511424681c82ea141d10b0741c0741550364072001915040f070141420ba0341e04070420102c46002d19281320710500445104564241855034030240483d8100c0244580780303120040044c0003400b500142c6080c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 461750647 1250 461749397 461749411
    0x60206010b130305030304050604020a17070b18040c03020901120203040b0f040302070305011506030605090402010c061109030109122c040c1734170601091e060305010e0609 76
    0x80c2c2e20000303142044078080c8654400340c140d01010040c001008404138809000c4c50003200e00d0400c060321113a0b558400d00707888111001550100c40d007000302d000030310060880c205c446100a40c00716030700c5002c102658984030f240000280d000070009200d42c1c2001e00d08070b5900100030704600707502c0c26980e080358801c00a88560b20070301e031500c0041d04040c03003008180041c0d0b50113802448032100c00d5006285d92040c1c0d000d0507021900340790002c1003e040480780c1c1d510403030b01651141440d10b07890700c82000030304610b004440500800c022107001334900b4068512054841c076a807041d00d0f14000d40040500603c60113000482000080c481c01400c0920164040c41c60f00700c1d000a000d0103103801c141d0341020510761500da4070394040c04104160f4811940e00e00581c0d1010702002c1c121401c52107410320719403604034040102d82e8900078a00503d8812100c90f40c42281810102000341e00d80140218043c0382109048220500d0041407255660502800f401080045000042400d000c000100ca4000003403000b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 461751897 1250 461750647 461750669
    0x102702070f053c06060409021906020f06060d0f0803060301021b06090c270613020c0721170901030b040c11010b06042603041d1f06020601 61
    0x10010701081c107060050465001045844000036040d5014041e4060081c504040c0f11048860050b24400580108100124406004180d807004204001401f0403402079810030b5151014400c0c141442d00c1003000383c18980c0050040b040503a91071403070104020700903402502501121070010368880c6240352000d500a411030388030b65030600800d00900410400c1078140400084994240c00040b500b18000c60545054074000801c060900005400030411001e60480e0038118620042c41f6112160700100001c0604040c2c81008590300160b03008201108415084000308014144d21482c50104420030020b0840b1889110744929410122602e60084e24500004440a150303100740e200c9002243e00500070000300369020f4000b001c190110100b819150310344000b080c40d52a0083c1a181259860248101685001c0007425049400a450501c0c60f10080c00302061201ea0f82031481c941200b0158080d901d8a0310000e40541c03c40002010210a4840e9800b032088603400708125056810700041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 461753147 1250 461751897 461751907
    0x302070c1e05010f27030209090601030c1e0302090a0c0f0e06030c0306040b0a240c1e051f09170a0e060c07080601151107080a0210030221102702 64
    0x2607030700038024000c0107007040c40c0c49403080100345c01100f0402981d000b0340d11004030366108a002c0e0754a030421700025210026641042043da60080440319540521081c4003d00550300da0210380000025605401c0c030701d8588450304245a03000a115941644501d092104015028081602880003803c4d4180b184d200100154080c3c0341e640103804104c5029111245e01681c0d040704c484102c001c1c00c1c03003140126101c9003659030380d1b10925904000c01c1d0005000c1c00c0280a440c5203031103050114508841c140642c1d00d00c120b019101d518002c80070003d03410081100ca40e40d18101949070000c06006400400510800e040580d110011280405d0242c4074035540d011001c2c0e0341450b042d010703400340880e4880d603000407916506036440820741c0700464480142070b81ca80c0d4042a1580014001c604c51603201a200c4005844e0012001444010700d05005281002c507032080041c0c8100d03036820002c070040400510054054a91140c0010854980103840302c05d43d401900760001040825505040d0300410 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 461754397 1250 461753147 461753177
    0x5240a030f0b090907060807050a09121e120807031a21030406050d0c051e030a060306050103030503071d030d180b13180c05270901060302070c1e0501 66
    0x40b010031400e0703000b4041d02d21480d05045043c3d5030305541c010710b00000c20b848041110300340290103950310040c0c607031107451105040480c0c0110f0a424000b06a480d18440c01d5505803840752513400101c1c443c052140c241101e00d030480e0103452404080e0014080500e0080f505628100724000d55103030340011520b03511410541500070341d449505101d0307900303c0d0100150003d5840d40210080031500c5910106011041d000750003a2001e000d518510003180c0d403594a01c1d1004250b000080d5880800040d001a9403500c0361900c10403940240c004401040001007440721440e000b25045070b040c580da821610340c034811000840e031283d4503079203540240a2244040c5020080401106000d84445004240c464140036007100c039416442c0b15111880c0c59101692521350041e0160445141081e02c8461504582402031000b210404011400070301a080220025550300081d103402883c25550168503401103003414140d180d6540d2000c0c40e0309844030603001c101d4014849140481c2c0c001d0030403052401d4540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 461755647 1250 461754397 461754401
    0x1509070e0402030a0c0206010e060117091f0903030f060f300309030215030c0f0c0114010906050f0a03051011040e0403050a090608060d080903010b03011505240a030f 73
    0x4414036071250001c4204040c5003020b500c4402c00c6545070b400c885881e607841e410003500f81401e4986500050044030107410007a0350360000c0750085944000c5030b60030600b50350188090f030f40405150325001d460383c181c90181503160049004426602038108510743c6044401500070002e0701c0761410250080c1c940b0b40c42c0c04842011a200f840320b4a5800b40710542c2480c0042120300c660200324807601b004003000d00d409001c2000e8a01c43c0e51807618140c41c1000d0807001d4000d0f0780103401206841c4d900c40c2e950381c3c90314410000c442d000700341f000008503205040104001e1010726001c2e040d4010f280c603100800c082940003c56581d56001402d0000e000e03034540c646000c1b01c1c4102d0300000b52041d407070000d1004055100c0700401040c2840d80d620349039aa110307001202c1042050711550381c03041a401d030100100b9070440041c800c25034001c000060351142c0e507003c80d080d640c015034040526001c0c01802c01c424242480320050702c82a800c41c51150340754004e900704090003980c14030720400d6540c4004e214148019 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 461756897 1250 461755647 461755667
    0xe0a12020106090e0102130b0f030f1005030d0f0e0312180d0b0403050705061005030a15061e170c130902060d141504060b12040804050d080c0f06150907 67
    0x55807051010750040c034207245c040e51101c01c0c440c015044c80500040e41003141c205071108040218442c52664039101c070b103072050341c00180c0205102c1e0205000050907a4040100a05a5401e03450300b402e0541183d10203455051201d603448e0103500208640144400714100b12410403801494807007892484034042211182d07803003401000060050148001c2c160000040c04040340f184080b501603507280300d241741c100c546521446400d50710035984200080c4010a40340c41030138080c600006d01907030303840b07025100c10380004002ca28900303d50710600507a02918003221781c41e411040140f40003049680421100240d01e101150201e5440084200b10b50b211001c03034002c2c107260f440034060f069a0014600350060b00303030b441010f000710a8800441e1420503010341e03811604240619405c0038502045400180d5009100720b81a100800c03000c03400780e4034411508000344c007a0100c0b50301c4a6141000b585002115000c4001c1648660104101c0300f541c0050204501400d1303a80d80c4c0ba90f00c83c00e20940d40c525617 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 461758147 1250 461756897 461756909
    0x303050a0e150108160e01090203061f03150801051605030702013c060302090a180c0605070314040b0405010f030e060c090a050f0d030c020a03141507030e0a12020106 73
    0x40b070344815590700700700c8410781c1079a9001050f540c003100c40d41481341d0780c02c45034401c500c00f181c0d03031800401003060b80d030380610350104014240103403c0041d080083c005024440340740b03003c82d40c2c44a0755403d8030207508501010b0104e10000300702d641000c00600721398980c015900707000c100c030003c00600024800e40102e40500200c44400360400c02e4590881c0c0031030844180b020f44c920301411802890010340c01000112074002d005403496442d4070711442d0203048500f000f4074409a580309104001001d02d2014070052125070307542500da003203c1c54000c098124080081968840034007080c0440b030119421242107410900f445034107071040c1041a07010b004040050340c001c0c007500d800c00a012000d2402001a80000c44805d40c1441d26001002650820001942e030003007060500107000038000c8441154003400105130b0400f07541e03650384030416001e4503100340a42d50007086460803513104c4408401e400c441e49003005d00800da0805542c680c0d45001038405401c00007a40c2e40c0c000c2c0e0600039801413000c1c0c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 461759397 1250 461758147 461758153
    0x11424150403060f0522020f180a0905120414101103161202010c020c120f0a05010c170103030203070b0a1508030c0705010905130b1c050606010801150c0303050a0e 72
    0x35032400c0c500f00074001c03a45003501c41c90030800000c0315180f242070b110482a1200010b003502c40003540078004001c06103042507400883d800f00d04520b200d0161101d0b807089401180101c3c01d030704585422424a02000c0c000902c42405000c20310151481d007004000c24001a22585030b0506001e00403201218440d4040006010014058420f4890f01c2e41c101c103000c0c000e070005510068462412400c84500c50078074130050308026082c840c94a410401c51501305110070458440c0079904c0041c0c0e0802c02c0c0d4480440390b80e9503540102c00010f810101000f042003c0c00003450b074a61560310065143d02c1880ca004250411a00008800c0300c402e6014500342290442422455612421000e65a50140880c845e43d889503400008640d0b12034014081501c5014201a481d26810107007103001d0300100000c190700203a580401c442200c0b030800c2d07030621240554000c0c1003a0030140e00140000c80d041c2c00414031507098030790740350b0003030b40202d00904a60303232510b030000c4c45d42c0d0f4800c11a4020024a80038210b0780c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 461760647 1250 461759397 461759399
    0x30902031018020d110f060f0904020c07081203101202010801260f0307051002030907051003020c190b0f0115051803030c0d0f0206100302010e010e1503090114241504 73
    0x1111018000030000c0007520994a4203154900b004501c2c000c8d4240f80d924035008010078411418160040d0003500d00040840da00305132519661070420580d9a0920003029000c400c11200c0c141020000307008107400340006000805c1600002c00c3d950050140c60403207002404204010b01021201c82d02138458101507504400e6500002034580d0312500040d5010301c00c80300020808090707031080300c2c09001284010300401c1d183c00184803026030340303087c0d0310709041d828046c0c1202c0c0e8005010b0010002c00c001d1443c1c11180452505102d140006003645440551003001840100428001014101454200b594583c400c11141d5001220b10b50340d800c0d018000440d0161110800142104000c8900c2e101d003041c9040b80301c001c99407048100c421214510319101c0400155024008900c1003410601d031070b040500c9148007103804540070207402c0000c0000041045410b40d0281700360205902e0140c94900c03d0f09200c841c03500050040044508509041482a100f5503103011140d45104540d0880e19295 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 461761897 1250 461760647 461760653
    0x1806090602040512010b091501050c030a050418020306010c080922050a060806070801030f0c170c01080a0b06070b06061b03070201091401200705030307080d0606030902031018020d 79
    0x20b50464440c142c01503125942c2c0283c0c10720113004141480202a1820b42c45503a5038040200c45809202c50382e052041c200a40140340d0000c0c0001c2410b42c0c1c880d21500c0e500c9150404c01c00c0104031201c02c14940501c1401801400c0ea405810408650382001c07480c0e4076258843c0015031020400264010100d00d2a40d03a81c1000546070040342c440e050f81d170020407003182d480500680b45d110441d0024006540c070740040c00003d5008015000847c0501c3e0944581c5490b20100c10210324444078260807580400c59540156a009203070035030090107040d0038405523400001068583c082c0c03842c0108000c0e400340c0010703400d4880b102541c8100305909008540f45480c0318400c1e031203901c242003c0e800282184400305030b2484130544206192011703907400c0b85041c03560b5071992032203c3c0310220321014050080700054581c3c08202a003401c074011110140e0b190300d4007030918101c0322103a00c01024503003482c2040c0702598010a400805030501e250100d0403414401d0b10013103810110100a40c083e05c6882c0d05014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 461763147 1250 461761897 461761901
    0x150b030f1b0904150e0903030c07031107090c08160f0c03031107020a030b0405010b0901060804080304020d0c0f09060e160507030207050409060c030513110f0a2408010f0501050d18060906 82
    0x841d003036481d03017034600e0721111060341c5c90f0b06c81155211b80d0010100b12410000e8803e40740090202c0340d2070203403482c094450100d00103448517021100b0003c1e035040140b04030703000d4000740700d14201d4850a10403460031480c1c0000e07007807040c95040903050640d1103200c1d040ca55103250480c0c110b164010212600d031502c03480e0000741034405860945e2150b1030541815100d0829902050580e03100d80c480d90460f03525650f90420755400188100d820641028030760b00007407040000790029003092014080d0b50390400803107400b00c81c0d580e4010b20601e0022418405809040564420101c1d05407500716501d100c0d500f0268035201031503118a0700103180c014000140030150740704001c8180141e42c00d00c413a0302c5110705280450304000000d4280d50001c03070014030a00d0704070f0103440c4401c4c002c5e003125a407503a10116203c2c1c032250458072254101c1c00070300500049610440980c09031080240000c1c045041000081041c0030700041031400958680c2d03415045100422040c18083c0c0c0420244102e0a01d8a00100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 461764397 1250 461763147 461763149
    0x60e043b01110f030115020d1d13050a5c04290703120c0c051002130506030c0d0506040605130f0c03060810050a090c0801150b030f1b090415 62
    0x2d42c20144810014247d1011a01c82a400c1c0a6074900700b09090135200902070300c200d030240c5503200c246c001e00212520024021644617445046d03000520800440b00c03402689000341030500f1b508070580500d5845808101490034002c40710465241480c0e04180803202d03592007c42ca002410713004100007038205074040182d1690000c010600000d55188402d142690091a1004010814003c42e40301d42084950011486006606d807080311440e941c0c80c1d0f40d0514601c5c0040c001d078107030001240d41040da11006008000c2c402603030394510710301d4213040d00e0655002e5544412111038039440030800c60340ea1170f00804041c1c000201000c20401041d00000002e140782038075481242e04008150035000d00078490b030012142003001912521402c00d030341c03000500c030082030000000e80d1100e0788404134190141e080003800c071190000840750800c80c818100c41c4183d51000c121000d04004106120a42c0c05109400004600c2448020103030101351000351700401c090581c0040c0703011140c685031788135103505c80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 461765647 1250 461764397 461764409
    0x30c180405011506020607030b010210020a0503060f030d0f030e011104060203120106031a0402071a090f060c0a0c11030c03032a0a030e090c040906060e043b01110f0301 74
    0x80843c18001c0030500d1081c910030040942c2202001440d1315029400242646505105480c3c00d02c0c15410110100d07085649841e0014201004111039030800211020100008034010485c00310003010042081c950742e00142c08041e12804801030030102500064600900c9990b12900c45843d24802540c0c0e810001042c8115082c2000004045009100708003e000790311030aa8101a500410302000e035100b228100d41c030802c0c040702c0c40083e100c203c010f54010450b40e0003402c0d00e01100201c181c5000700140500d85d070f95500b0042d014400350080c00803400c6e5a449002a44a2105400006c0c10102c0d40c2d020150540000a0001903c0b0b62000b13044200e40d143c0d4114030340c4003030009541c0b40e0320403c3c000000c010940c2940e81b5449854070080c001c0d80144414811032805413140640b2043d10010752001e400b08580740300c50b611070b161a010f6900c00c1701041c030030341644000342c1e03400c40d01c101d2903280109080550001c00c840c2a40080d00702203010580101100da0312101e80d4043e10066100340310365 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 461766897 1250 461765647 461765651
    0x303050f0c0d0c2003030a0c0804090501030c060f050301180504080c0a03050307030c08060d08160614070806060304020a05010302160602040806010e07110601050603060a091e110c0a060b030c18040501 88
    0x3a091320311803400d04402c10401400540c2012000c0d8001e9680045844058030003001c10b110018540000b4051140038510401c00200a14908040580032075500d03a941070a220082c00180062041c0c81e0b0040e42203484d0820225690300c441c1810b604603c00d20100415501403203042c40e0030f168102d8000e60250901e56410040410b507004222400c40066805035032010b10044020041120100502618182444540c51702201ca03620241201c080d00b660040e085c14481c10000810b400405165002034151030191070b5141070390015101c01c05500480c1e05265001c04e070a0b2034040f100507448400c0b60f00a0045680c3e0751200364480da0703060240729003c401e450038030004421030300c82c455501e07088203440000c04083e42000100280b5400007080d03030782c015440780000203489000d4005c024505210840303d003412080c40c92100700755100a4940440d0307040801c408020380400080d892000c03908124001030800881c400a401c0c2200c000c103503076008242c5490451680e80e007000240c0290b20440003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 461768147 1250 461766897 461766923
    0x2190c180b0f060702130e160807030c06090308090910120602070606060c0b0411030a0602040b0d05060f0607020915060f04060e09150f030a06060b0c1005010f0303050f0c0d0c 77
    0x100f109510407440001d40100c0140ca4070a041199038101d4810500007106652290309129064485205664071000d9281d0141600300180440040c4c8000074182c01e20b005007405055455410440c031820941500501310540041d080c046101c003a980640040401d04c010b41415051020194002090540b9030a140c0701d400030341240148540d000095025450f02c80b29900c688401701760000052845416000f40c40d01200000d0750f0784010b01c0540061400c0c1612040d04010150450b000101000d00500d000203004800355100700c192441203904a803e0043d076034403c60412525a840710034950044004a408640700b8148000b8005a0b40f903030741c5103080300094000b0025820001d4807500c01c0c082d00c040c80785009003001e2074042c841d03001c050b0440f01e401600c1d903603000131501c40f0f600003905490080360800782514240000c0d8840151a0014011541440136807651207689110040c14000c001030064000c3e8200ea060300c0a00d460742d8140c035030309031030716030f014102000d6202c048822014201c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 461769397 1250 461768147 461768149
    0x110f0706020f013804020a080106030b010c03050f09010c081b15010b03010e090f06010e0105030c1f050702010207030b01141219080319110a090b030702190c180b0f 72
    0x1c0740050040e800783c03000c032207140d051824000d0405501041d401d40d04c0d007070f5103416550b2564002003d50030380070390b2504d00c290314100006080f2803541d50300504002d02d204104001c6035211094035083c03a0704030040d540c0d40c03144000586043c00074540c01051030001244001e01000340c024620305000c0014140c07020580c041560705000c640c24050a500c000050005101d01c014500b46198400e0504d0211140d00d00052401e5140060076400302901c1d40c08036006001c5402e06220340d030400913040e503107000300d6228071922095034071170240aa020810041140d000356071007086080c004642025005507203513100c1c071405a0201407009121b00802c44400c1c0a40d46040c0041d4503102901c50410506d8064850382c0e0345c0505070701c081d103294289240400000c070095140d03c00c015482c903c03200040d55800280c40007070a103002c10340c46044502d1042c0100044c5135004101240600a94083e60b151540c06141c400d601020310342006540461442e5046a0010542e02c50102d40f1001c942601c03120038004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 461770647 1250 461769397 461769401
    0x2031204030605070503130615030f14010b0303090315070e10120510030503070b10081207110102060124020115080d120b010f0c08071a040b0609010e040b07110f0706020f01 76
    0x303140781518503407c85005022840641c00740103044940308224070303840e550341c641100d9004801010b840d044c5040c0c201003c0000300340702d925210b01050f00a503042860800010341c450340040c951f80c2c3d0004101c8001350146110340ca400c8011312000700400b200300441040200340c1284d2242c00c0b08442c1c40d140c0880e0340c15101c04070007401c80398890011803624025079610300840c0703009401003a0148034403001040114050140b00345201001008a40312055410003488086280006506540116006200135000c1d0f4200022190303408003809a8440207100890044c4a0071a0219081941410100b4941d00c04a45c800390442156100d4411028007c00d8a040301c04560446001c00c08054007110054001d9000c0030b000e0b4018507489050071440e4030703500400d1141280e501440c5840c40200010020b41c424070b42d820000640e0000000d605041c4110710018000d440035068806000c0000c817054850200300c140002c1c0042179444220800c800541d03240d08500403000540228620b50541036014 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 461771897 1250 461770647 461770651
    0x7030e030307080418091205180a0305030a080c091c11150313060204030816031b0308040320010e07080d020f0c01031d03161401020c06060f040902031204030605070503 74
    0x214a50031314080c60a00c0507846071501401c07a0f00440c3d240e4410780b000c60b0315030f4106200d800d00ca8403010340e070303405a1b0300d00441c2c5801040820b202c2c0b44017510074008a040002030b03402d100c516041040d0350741c9034060325000300e00070001d1182d40652014000c01c038410010440264807403064501d00e0003020002c04002400072f8041f140482c0c00810b00020349001e4414085401607400b56400602d030503203c0c0c07940030f110360100c2c075056101049094040704061b8031290740082c5c00c000c0014040141e040ba98020404140944013030108009000e6414070303041210168030311a03026900822901f121030b2000780d140c554920880c2010702903003c003414124008204900e0854010001d4680101035100540003171090040b41014001d03001c000c1442d81c0c40410041124031244028042c0120b2540b81c030003030b02c104e031002102043c0d005004007101034800148550b08540211180c1c00b5007103011020400406800901a41c03500c03900089114003080c040017441680c4c01954284041d84c2d07110020781c1c8034442 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 461773147 1250 461771897 461771903
    0x1030b010305190b0a050306010b04060f0203040803040e0c0f030405011b0302040608160c1403030402100309111302090406030609110d0f0f06060f060e01081b070b06210307030e030307 81
    0x6a803420100c040300c944c065114000004c003001070f655112000300786008400d821174580c200c0006010b000490b0030404c2039141c4e542600c021460b090410781c19586a001d68410803286068500105414240c41c906450320410111010390700e9242c4be00309907010740100c050742603841c480940840d01076031180c000c844c2603580c26115241c0c5616070580700d42c45210000202420031224200c1c0030300140440c1402d83d403651001c4001e43d10b80c202801000300101108584005142c030703004081c000141d590030381c0b11018608803100768581b4000c4c101800a446100c6000381c1c0107203090000301c10040240d110782d02e014002c0ca654814809100f040c07003155480b00f0000341c8801c0302406c0c1603000513160041600d42c2c5204a0000c00c8565031800c207010052001c0d04070f4404034417007050034071481d42d1081c64181d00c015070265000c4000c03035003606141c01e48605600509846000400541c56844112101c4446d030004403504031400f04449045449401c110310440000b110391901203100d00e400000d80c0c4070650 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 461774397 1250 461773147 461773171
    0x525270b040e0402030a06020304051c05130b0d0e19172a030d0903050d290402250f1205030f151903140f160302061c1104030201030b010305 62
    0xc2001d425031280c0d00b0040040f03916110b4440e5141c0081e055001440c0210300c6a4005c1c0030b04110f8424008c40d4401400e44441003107000d10401d02d060690b03294800448000601007030f940e60080341080080c11804041d200684075038155104140501c03a91312021a029802c0380700c0c203003d20f101c0000e65108891510000d40d05444418203d40381245600c1c2e03050807400100d0f403a00c2007034484071f800d561540b007042d40402c1020a01c001082454062094044030b00c1e2402d180d541207415421580c41c5115412034012030f40031079042c100846d521858129026513002e0295010400e00e40320002091288044072201d4030070704021120b42c000c80541e40200305500440c2d82a81d90b003d2040d030400c5038143c3c815806121642818a00284400084007460248032420f4003808186000740c03401045016111440d0300241499032500c3c400c2440384141ca90403100d107956030b035403002da00203521046d0f50720030402032401da007a5194820320310007001140d01c05c1e20180b102559040041d02190421209107000301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 461775647 1250 461774397 461774399
    0x250207051e0f061b0f0a020f040509060c03100902030a020901020f03030403090506030406020412110307080a0f02090a060b040f06141216030f0f020c07120807060525270b04 76
    0x840c0c8071010303201c000418440103820200c10424240b42170500a80b031030703e0707420400300e00066003009000f400740c9110079201408942001b1204598964000700200440d000c04000301d40303800941c1e90300400a1101120039900c030304100d0f407014001d501c80f412080c0944a40c0c03900103410310001c01034a10490309900da081d899440c0c0700c280400c076030006008448240e420000800d0030842c0741940e03402c550040c5024145410000141850092076800034501c0342e101250400002c2c404464501d075071075064900c5600c03501c440c2440740c0503000c0360700544800000814041400303501d095603201190480e0780d411002c85058800d5110600c1400c1000d281400150009040310494a641107403000c0c05180000c0c0c000c1090a1071411a0381d61981c8514041d00001e01105825040000101501140b59400d480340c0041e6a211403134890706200511464960000440b10841044000034800c40f11003030842c0d0010041008001c041a03044012002901000b4146001100c130079010540e2140e1a20602c0c0ca = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 461776897 1250 461775647 461775649
    0x70f080601151d0f040906020307032004060c020f0301050106020607080c0306010c020d0224120a2d1407051b07030816050c0d05070f0e0601090905250207051e0f 71
    0x40c3c643c0d048459000f49003a03000c0c000c2c648441c8a6409058024940141c807810300d1540101521602c5000c0d050480b40d00c003401034041c6d52a800c460441c1e9007400d10350307a848560b2010030401d800d408650750307141d441e001c0000f9003e500410300a03c01c01c400d03580c031040d55507200f4140d0b04034002640d080e400030b01d00705040001401e0107480c3c8182d03280000c0800315243c4a40702000e1452035190095640e00700302281c03c00250403c01030b00741d004655042c0c02d202c103400f0b240203600760341042036040750010b5510014000041880d0311004d000e40d41c2c40b40045262410f9800038003550310584420b880b5002201300320101040108121013520f5021580d20318240810526490702c903030030038043d90ba50240c0d030040e104a594509070308032054450405818043d01d04031b10041c09004640c4112520140300080000b26a03105803007205490302d500e4009425285e400e4800d02e1480528000c5509010391098950b0341d83d0001540d1080760003c0342ca6080b049010b800b04140e5010515a030b07070700b00d1100c84003035180d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 461778147 1250 461776897 461776937
    0x3072f0619020d1104150306080a06050c31050301140a0e120d0e0607050a0915052719030c15021204030b090111030613090204020c070f08060115 64
    0xe40301c0c0d00d030340c0503050408040c0030324210340d9503451818415030000b40800040c4842010b0b40f501001c50b05007006610700d01041e954803071007541c100422a81d03950002441e0340d05550281c481001800b2090707090090001209141c800079482c1403208583c2d00350380042c0622b414012080941007106200306c6940b10004400060942c0a10a4405000d4030b48103000c0c051a442c0600030b840b040354000706000303421001e003600b0300c00050030300d20800500300a541c07441ca03006a24502103850041c1ba01c1c0c0d010706904402c49081c082c601c440303401380c0403410b030560100c914606c010340e49040132070700d0000602110311000000030044c48000d0061201e43c070b042001c01070f20200140240f0550050760704142000801c1100740d4000e030012201c0001040502142e020244110f11076a40603541582c614140600007401300d90b07603188c0c103d8100c1c0e00c818040d0b0454a4036015a1307070f816001800c41c0e48194861240840c110014096581207100310300001030072007104c41402c1d418a2054454100e0104a0743c06282 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 461779397 1250 461778147 461778181
    0x80c01141602190602090432070c030518060a08060a15020a08031503070303200c13021e0301081b0d030c0f030e030307150c0f020c0112060503010203072f06 69
    0x1041c85e428001e9170001d803660b0042e034144881c50b4031804104449886502d500d0072410016810510381541000200c58101c0d403001406600b40c1000c50b02c601b015000c06840180d152915908540c0119642c0c1d8103940200142cad0041e801220031074401c070384034084224020783d07954221006034840345181003c42d607040000d5070001908104900c1c0c04082202180c90110254011400110b034000c6007000e0580c90f2540b00b00c281c030b4050180555200e00c0c000541290408007142908503400200c6a1842a810304140c02a40c0000c210030784940e9140c54083e207442c0341c608048800c8505800e40041860b108541c002d9039075046e11580c103036002980304e020080844030003c0302449070f00003900341142d82c00c1014024842c41218070750030251619507080181c5281006d80410700c081d0f8154512456000314581101000a01c2c04101640b00035200c500609036035401181c01d54800024019415408400351244101d00f488021501040794500143e101c2800c401c036503941c010340d02041c1c01d0466022031803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 461780647 1250 461779397 461779403
    0x10c020f1e09070f020f011416020313031b080102070c0b0c030c0f030414031c1110020711040b0a0b19111501050324010909020409080c0114160219 65
    0x1404150001c0040740007030360155494004079a0001c0415042c40e8100245440c03082820028000d61180032010848504098200903443d180381798407290440c820001c0c1d6164540c4042540d00d03036590b90810142c01d4456040c1d02484814040f40400ca5000500880e00d445034002490280c40b032030508400308580002c0441003942c0002c208400c0c01b16020441400203000d9100035560303851400c0140c4609454200d01c0318084c1e00240f01556030f0349001651180d03038581e6070401c0104842505401810b10035214444409a40701180d040d0a21002ca0108000e00405403410041d002d079082c01c10a41d0700042c400c4400704141000302880001d0030803002c040c45680350919000200308402030504107660b07050216802e405440041200749400c1002c0e581d42e151010b0002c1c110340019441b0b04142005010f185002034441c02c0f00c3d011034465611941541e41c00240280d161041400c0281c06002d10761400d05001d00c2e5500400c4030304030300030b5240b46407204580090885c50107500751218080070a00c415 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 461781897 1250 461780647 461780689
    0xf0201050c1005091e0a03230d1508011e0905070302090c090a0902031003030c02120d02062d040204050a06050901090f1512020d08041d040201030b010c020f 69
    0x298501d00c004000c40d1500d03855000d40030072146402c141307140c50007500f400740c100801e5071150a0705442e2000b1525028a82c2c0601d000382d00d49000100182c1708488451320308480c5e0100080560f070f2141e56500c803a120070820260b0805042c4e58000c0d203801d0b13600700744000c40382c40002ca510700c00203a51540144080c61050b0143c50704c2d1541d0f5000030701d11210807070318241c11074400200408903141c00d81c80710001e00103a030021403c500342a03000210686050000500707200a09605d4800c0d035841c100047c05103481c41c800c403401d05041100094880d00c060702c10005c1c45241d564403107949040180174000c0728a041c07020a01541d159020023010301030240003d421150780d00c4c0d000c1156125040b0182c06400742d910049500c0f5002400f442c222046102c0c450411040700d4021720085250340e9104040c9501111900c4106d109410300c030480e48550390003e140050220710070300d02c070000201c8140c03103103000742c070100004072404005540d00070345e000c2d000f50f016504101d42c0320103252110314050100555008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 461783147 1250 461781897 461781907
    0x10b0f0c120f0d0c090b27040c031b020a050d08190606180e0f0f0c0f07031d040c1e03060512030403020f0a061e12150302150a0207030f020105 63
    0x106440c03070340032600302d5801c101d001a094038100f045002d0410f0405081c6045060289002c0c0000e1050083d41c6824010401c01c00182400825200c0345071440c0307000800c10000034824100240c000d21300310002d1140c461070320b40002c0d0700d18000b2a01800154200d03011300403208422004680c000303c000c1c0610340c01083c000d401e6041d05c3c1641b0554002c2c0005849241c540b0350704c2c018103805030340c03035901c180010070740d0000f0005041200c10110760402c02c24106a19030340c0f00c00001c50064018211200c82c1c1c01c0d00032a052080c554000903aa400003a028403c50f00c032401c5d1011701054030240301c4000c0100307200d6401c04a400d0714005024071002d503680340015603180c64900241d400031802d8441e042a80c000b1030b09005500d4130f04c009502c0c082084070b0000301103103006000f07080350758000440d408032000f0a40a51a003400b5200102c0d0311204aa030400486041d044400c80500d6580016405010b0700c808610b403100c402003c4401e050801e400500c1c0c40c91a60796242c100c01103000c003ca04210040c80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 461784397 1250 461783147 461783173
    0x120d27060903032a021603021804080906070c0303030506040207080306010f1b06051006020a0b0a0c170703090b060118140301020d0513120903020136080f070905010b0f0c 75
    0x1070304403d04135820408010042c00020082c945015640c54100100940b50200016610f2003000c40e1403130781c070500151880e80d030b80c1040c6105000d2601a20740004001500100b08a000008481528800d8504102c561218030901003240610b15000b443c002c0c0404c0030031b80641c0104514044013142c0c2c504121200300e80302d04d8440340c08804000b16a40350310b54060100c0c10401e241c100c000f0b080f8500c010410f14811303031a85156514082c0c40500b9039603030b0705080601503225407011705001c4890703032400c0e0392410314a4005004002210054070140401030200b07070799601c03070301044610348000010105498109200078121481e45840307140d2640d420000486908d03920302a003441505070000444812802e0305000220120303032042c1c3c800304003507010b0074001030383c210b084652202a0003140c22102c0c0060b18180c8214520f0084030850036000300c800280c13804c0000341440c80300324803038180c0d0f07503165850401e1700c01e846081c0220b01402506200300d90300002c5010140c030545402804072022804100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 461785647 1250 461784397 461784431
    0xa051003150204050103051602071703070206040e0403030515030c01030b010e0d0f03120225060207020a09021b0f070603050702070e04050706081e01090c090503120d2706090303 78
    0x7107044400c1c40d00410b04214030340e0180305030f0f9405030f90384896a0121008905c001d41b110b401d030090300e45803642c111170899045010801c1d640003d134064500b40e43c0c0e644030b01503403015513000c58013100002d0030000041d001c00d50348158468000c1001d8020300e00000e04e000158094552003040343e04100c0d001c050b0050565550140030b00060140707050081410b03c41c20002c0504101e0440250902e0040011400525081f0f0120b042000c5041003008a00341702e00d0b003000a80b085801c080e612042c140800314107446c059005255045105094145032201c07040843e4540d802c0c03404005840d08151010004940030f41c000550128142c4140c0d04a07a8880c00c0c134010308042a18140c4041d4810b22040c04101d420545147d080a07000415201c0c1241c10756100d028400b050242c2c0010750b444500c4400c855006000301c5000d000300600b0b231a80f030400c001210750030340c106260700c500046c00d0001403c59141901c01800082245148280c0d0811042c0c8404000c2c2c820703542c0841c01c0541d111014000c0719645 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 461786897 1250 461785647 461785673
    0x301022503260601030c090b07050601140f03030706051b04080c041118010e12010c0c060b0109121e0b010e06010f0e010203370f080903040501080a051003 68
    0x10480d212030909500340244012800d2402c0301d03628040c00324182d4030101480002d0b5024a007442c0c04901441c00c0030044480c81185c3d407208a141d0350108501c01004801314082d8140c0701e07144880c5207041568010060300e40d50280d00c40b60503400c20480300300415590703042240c0c0704a15400e410280245140103c00c5c1390b1042d48198056044034180701c441d441c050103242149606268618240f0b42d1001270a81136400d62410070f814881c3d01d081920041e100c040030303c664445c919000304921140c60f600a0808400c0e00002c440301460710100d00d50545c05400801d040e10030740b6204140c0341c0101d0740c0d5800c4445022010700f070f140d05640740d031000040c1e01c2c8442601802071580b03880c060b414044009000a242e0754000c0c414003401d074035a0100d0742d03800000c1c0c0342e8085032140c0d40e0320034254041508000240030407060f480c60880314003801000b40c00a40140f070ba410160369006223940c42200540d02e900890080c80d000814500208911000b9034105035008070004c5e0708a1305096480d521400203840d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 461788147 1250 461786897 461786947
    0x31101090c1203021203062d0301150314031e490b2202130e010806070305070c02040e1504030801051005030114011815020114180a0b06030102 63
    0x200e4511080543c140103003034003a4889100141103042140000c3c8c0c64541d0300300c1c040001c0702030300358441c0b040e0402216140c407190050001c000040100040c031008103140d020079552012007030001c54a0541c00011119402403829520f80c010404040c10049036021800400d00705150182c5401c00707004d90b540c00e132031804450380d442226042192012000c0100103e18880081c0340c001d041c0c543c1d480f99032402c00203c816000c400314107100c40d40300000a00582c240300000000950000c03602e4083c51503141e043e62104400c03600141d48c1c1d00d1085065400407105140080c2d10800360100600385500094403035100030b01903803074a00c2c1c122a01245804111402d038000740e8a08010441070503c000c201c0c1906686181103450b642c1072a680d000140d5003d45490704004c464042c4070001200040e00d800540b0782c50351010340d035481c4104028003034845070350b40e24124101c801c0400c0071701130014100c0d0302c449905800340c1002240c030349820803039250040c000f41e0195001c00031600c4d500304148a547c0c000d01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 461789397 1250 461788147 461788169
    0xf05010e03130909020102060c0d06090f02040501030e030a0905010e01091d010f211b050603091023070c060b100309060b01080705030112030201060b16050f0c0607031101090c 77
    0x980040411050040c3d004200441c5803401540242c1da000c141a80d110045145413940c4051050612000f45001d0b03000d44800c5140401c0e0820340c22094004100b2102d003681c081c480314602503000c03a01c0b889844038071008940340520402c82c0c2c0d4002d00c2b880202d080141003641c151603445151012100310281d0a0100d02031190050200045448254000d00340340003240103940395800c080e0000b00f861000181c000c03d2481002078000008481402c003501019103090748a0810b6240c860760341c1e00700151503d4040c2004a030b2403151100500c031751254521403910104039218404183c40c004010502551120380301c00f4000d9483d10b0f00400803040304c0c52036400040320401420414200c0c0c144121903410070100f1030601c004242d00070306590641d04c40440070120f0b000c00d8a01030340142680c0e03011282109010840741900340c801c20451924500a000b502d1882c14039002d0740391144106450143d12003414400400401d1040c000ca21440500400020f407d40b1030340c480341140c00f40c550150350303141 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 461790647 1250 461789397 461789407
    0x92301090504031124060613060c0c1406030105040c0e0306090709051b0a120e1509060702060f0c40060207030f02100c020409060c090b0306090a05040f05010e03 71
    0x5540051903801d040c83c0400900040c04080c002d040c4031054080005c2071070300159010450564403c002c64600410241c0750070b86407a80c4640c06040c40d004d265081d20b40b45140c1c7c60002c4c417501d00c0e811589100c480208650701c0c6a080c101000001c0040c4130402d020842da103a1811801d403001c02c401c1d07004000400c010071490345440c4c5050266140207020540411303205503888080c030140320642d02500c2040c00d0030190320406d000c4400c02455131a145420b0791080f00c0c0c8650380da401410340b980c010304100058a205a0354400c042ea680d4405554080440c102c020004900e01d010501a00309121401551125001c041d03844080150000d1150038401ca80c0d010600071941004101c10014036041c0040e03d41c041c0b80d43c45070080d0403101840640101c101559602d001445a44401c0407158020820004031800382003901c0145500e4500d01d020901d020000b050300e070f81601c01e6a05c135601c001d00c20081d42d9200b9000c03401803d8040c3c000c8803a84120000d1400154080c003408a40801d0740005544039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 461791897 1250 461790647 461790653
    0x120c061308070f0309180b030a02060313051b0112020c0a020112020c070b0d0b03061501030203040303110c010c1404030803190b130e0c0909030a0e0120010501030b0f060a092301090504 81
    0x115450710803154020b11f445480e001c20388000c52034003856501150000d807280d0342d14050f0008401501e20081007405100e544542d0000041c0c500e1280400a9030350070710210f4045941c1040b03100d5003c0e21a465800000380e03c0c0191b100d246150070740b81100f02e02509101b0489000ca18000b6690801440208045401d00a00c500c601c907009510304110020101800d161a4030400c10810702c0d001810503400000060905000e90020885d0304001c001c402da4603625075820900900b050440280000c8002402158102d01601641c0c140c981041946255844034107050004940f400c0300140e1325a1078403091502030f48e41092100c40d40750042404641c50305924801c03420aa20300c00d060384904030700d406000a4600000c1a101070b2416402e161903c40c2d802d0b001078418004504440a613502598202e81001e807041d08440d04a0344103003040d50080d10b45058035410300e4401c680088d0007410034002000552001e8001c0c02d400320a41040003440c003500c000c69071050708240c0010a40c40d40350410f0000b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 461793147 1250 461791897 461791919
    0x405040f0b1201050c040b07031e180803091309060b04050408040f0801060605091e10022109010c1203020d02030c180102010b1014040b1803120c061308070f0309 71
    0x3000b14148020030052410001101d003d0055000c0c0e8042144042200c1003090b00814410303654801342d649045984405040040002880e010740c10201c0904001c0020502000415a241c5000040111050740040c000c100020b000c0c0c820140c81d0a5203801c10141a61120710070240a58041d4103000e5a0340c2c141803d0303200c810f40341c0d408080d0982c5082c00802c4000c0d4004141c400c0414100c8074152039004100d502440164811203c40e8861111001b64090b1900051810780440000f06c01c0000582072841241150090070a40c9022039403001c40480010415071046215030f402e81801420f102d407400102040360800c8414020761100090714030507904505444c1c540b45013091000f44200d1130807402041020642c0e1511909010803542d5610180c50f044042d078015201038551241c41c0d91000f070103010407061402c4414000c3c000d10f229944003540d0b44044030003110130f039401009a915881d4400140444811003507a128006201d4140002c025202e4034918900030354070804002c0c1031414900c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 461794397 1250 461793147 461793169
    0x50106021e070501090603022d090307060311041509080a0f020f1c02060d0915051b04030b0c030a022106040606030603050604260307021f090809040b0103020405040f0b 74
    0x5610490b001c202c1aa40f000304001a0b0f60907180168994071480300100c895503c400c2c0719002000c03030281129070307030000501500020700c1c11000c59090564402f400d408623050289961b00c10314080006100503000020000a860080d24081c03885039543e04255081000005003218500007602412042d868400c2d0b08801402d003c890761031352030801c60080b400004c402d043c0240100008034a81d01d801c401c42d4000451a508088090b648107400703a5860000c0c1030449013001c0d490700d035156081a130142c44042e02c00f9607a02c1240001c0644400b048203050741c10041c00040c01540030020003802594484458000c0c00b014013800c42d145c1000300412003070341c921783c100b0420145040030805c04940001203070340c1c000c0d40101c446595070b05148900001d02806000e10b4084620010a00580303c0d80051071a03a5240340101080d000c0300104181c5003620034010018166400c2400700b6070b158038055120742e4441405050043c501703a0f480010030700b560a138010008596940d030403c00c103141070407030306c0301 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 461795647 1250 461794397 461794453
    0x703020108070816181d0603010501090c08070503060a050d0f030e060f1b01110f0d0b09070e010305061207060201060602010e0a0f030516063215100c0605010602 71
    0x100e90714045441362000240700c0c4004c820442c00184460251305000c1d111809840071a02c85a441c0d455600707102070024090703a00070300035881c00300001a101c03c18860f900e1102d00c5583c40e00c4c00340d100e910302100c6982015002580c440c04202c0001000e41c3d4a2a0340c1d80c0c135502c1150760440d000319034180540300810404038a80035000400800f004143c2c0309044030103032014100300c50340040300e500000780107080c529a4900e185074002480c0d00086c1d001d401078680e50340b1210b0203001d038414450a0084100c420340341407021900d181c0d80807060b58003d4000540c055070141002a00d000010500c6e23240040c40c1e40980007503555a0814031100b64280942020002003074000c04400c10035903250400c0d0100d0807401b404104001c110048070303110641c00c07010f030240c00c003800340301d414191603210140007280da0000c9080c2c1074030184600c4080004c2082441341015840d62808840341c40140005450610340200c100718070141c0003000140e980c800d0602a00032a4010144103001006c00c0f0259003d696100d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 461796897 1250 461795647 461795657
    0x10e0a0f09030e0d11060721030b0f0402030723090102120906070311030403050f03030f01090b150904090803270601030506061017090a030e2b080c0708070302010807 73
    0x4034002c81d420080020000f0f005807008900000036007000b90062600c0c1c1c4e520741c0c0c440340000d49003003031182090400c40c012804c21450401580c1c3c81038154200e40640344401c2d04404207000c3d0521601d00f40e07002d0741d805005410f0845906107a004008080c003c94000b0600c280c6012605a100f5641008400b01400110010300d282520920000d02340c1d0085400c002c0800c102101100c8020b18148142c40c02076030f00004840c0940e41410500e40c6a8200300c1c0e2030a44580074800002d01104180103c2c0000c07e0040d044100202e140c40500090b64440014150442e4640001c0ca000504140c01144607001101e600f0224861004030301c0080c0c11500380540403980514018004a1030200b40e150b0891800c8592805032100d8880a46022103c030113407801e008650010804c2484000c22550000343c4259903074840300400004105441c482148040a0198010810140c1417400d001d0809440d0181031603505060b80c01810903c0d2107003581100e800e64120070030420442d6007028046800c000d2901b00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 461798147 1250 461796897 461796911
    0x41d070b07080909270a03120b0d020f03070b04080106081009021813060f1505010f0c03080402060f0403031223041104150801060512122b05010e0a0f 66
    0x60030050f805010f0159110b00d12035800b04255441c0c68190820600e021940c8284864205086548417000781009901141c2400d098441c880305610828920700402446070720a48404d80070710070401c0042c0c0503190036116803003000c105202000c5c0a40003d210580010407403500f4001c00d1820301c19403100034109c160400c51002d0040e5a10241e0b4402004d9003c16880e443d90b425150305501ea14120b8003615040c40c0540c1505c200b000354010030a007030350010002280301c0e0364600441e801030311400e41c0c1300011507000303110f40080d00c52010140c1040c0003c0446040050540c00d09540d540300c7d9000328041504070012200c1e8808500498805a0b400c0340134619940550794414101580101b00508124000303c07031760381d1591541c4c44001000310102c0804000e603200c150181c0280030b140a0a4440c540d09940f286121900040e800500080282881e041c10081021440f07480d01030700050700c5440884460003c0011030344140360081140d541482e00340d0078481c8903003003118600d25007841c4179414042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 461799397 1250 461798147 461798153
    0xa0509040b040312020714011506020601060f03060f09150b0306030307080307110a0c081510090c050d0504050a21090e070201020909010e100803280c02041d070b07 72
    0x201a540c4960404124881c564552508690040f007500c51810300504c042421014421003000d0207541d920030344005c012008685910707100340d0796148190300c0140d010f0301c018026184a40b0404031040880d0074081350140d00c074020a40052015040070300f0144e540c21245000c1400d074540f407001494440300c035078070354180100400d0726841741e03402c09405140c000020401c114490301101d202d054800040d551100e42d02e1904d00c005006074452104648140150240c0280010030643d02829405554004a5148c40304800140c51200c1c52007043c01000c2c00146543c0f1840d01420388154480c1010b09015145481c11014415280700711076441ca04c502d5100c0d0030385411802d9003041e20300340904100c1582e1244000c0713019114030a41300b9082500301c0c0c000284280100d84490040d08031500f031494458451100e03681d603024000e2004c030000303180400a5a8160310b86489851880319180000b03880361941c010405640405041c090244030b0140c409440440074804074000c1c110041000b803804007951 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 461800647 1250 461799397 461799409
    0x706020c06160f0c020f1e041b0507020405040206090303030a0209012015151e0f030102070302191b1202121207060e0102070b1f06080105060a0f090902031906050a05 73
    0x20f2804000d04c85406044400d40d510462007000324400101490700e01c480303107000241d00944010041d0300541c01c01c09020344484c201401c1c1110104595109410140c00760208406418090004c1e81c00400810904c2a5502c0510041d032080412480c003680ea40007038400100965030480581e69078040c151104225114007040101e4054040001d403040c07038550300b00114541190700403c0d40d000941403400e00c0e0041041c4d8507610b40d400111805c840e80d0002105240c2030744201d000040c0103802c100400b00c400c80403c8000c0c1115401036807096241e02c1c85221004900c036068120f00a0300200c8840707102145001d28008a0052102015000510840341030034114054940010801600d4002c000e440f4442581034405d640c0d00005003810341d0501c0c9610400e40b554841c501d03118112030840100701ca03130084190504070341c0c1c042e180c1031810011035412102c08800b21410010403400040c000b603041817900185d03008441e5140c2c1c03481c549107d1001c5000321006035000f103001c0d60b88800c1c204119a112 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 461801897 1250 461800647 461800667
    0xe0108070b0d15090c02010b010905040513080705030c0714211b030c0d08030f0a020f0415031d030307020d020c06090f0a0e070909140f0610140706020c0616 69
    0x80c5102280046030004502102d00301500700071549445c21005e6054264150400c04004c2800c1e01c170100d00c59140c00030b000c2620b40481d85c0c40001036000c13280350300041844004188003800340301968104600d480045040251035409030344c43c410310b440100060324102d1140b01101000403d028180d0307101045454540707410051980c0b80c032003041d80415141d1024400c840124030014041520385a42e1b11b403550490300300340c500c121805004000a05010460300c00c984d202400b01441e10305241c60030203000000301c071541c001c00402d40c480020031003240307541013070600c0032100c04040c54491600c908005c0c0341000e401005821944500d00b1040a43c541c0401c9030040c0a0641d40940342c0c00c4d244000c1004161a80d020301d494003202001c0000460b0b1010300c0000342c0e09148410f11840030550b5800030901c17025501c05e0700d10921a408910140781c4032031034050100c0d01381002da10000f00300e541c14206820030802980c1c0550000381c0680b640e10f090090503400f10144100f1400c203200c4200017010201c01c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 461803147 1250 461801897 461801917
    0x212070305040b010522050c0c0c060c0705100302091306060f09050a120206041728021809011e05090d080106020703030822050f060f0105011407080f12010e0108070b 73
    0x2141d20719051500350483c42c204000d00e1075000388141e00342230b900d001003a440b03010040d44900460341d4015151030000e0807540d0101c2528010890b0700d003418100a85040400f103a6014145e007000018090303200c0c04c44924050100840000c1c800781340031400390180d0f55a404000801c801314a05000aa55000c850400d44070004e16001c089419807020038854400c0f034000c41c000034055109030309907800c00684c400c00b00c0e150001546585c09111103408102280c400003c0d4000d01c1e40081050f41c1c1d884019103940a05000000704100d040040d05034140c1c40c064030304003000c0c3c0d142c20820000c004100124401c00041d46003141d403e61401c0380080d29040701740001010050414040340d42081ca168401088501c054401d8680740d101d850280d555925900420116020300e40c001441c6500f11802c41d812607206864506070035400107000b800a50113500c00705c1700d44409100c8056122039001c0505112411492640b1240d41026014414610141c0c00401c41c0da1082d07109100204200c0b0940e000248 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 461804397 1250 461803147 461803159
    0x2070215031909020f0604290307170a0617370f0305120f010302040e06060109090207060204230307080106050d0609230105070908070b0f0913020d0212070305040b0105 74
    0xb0500c0055400845225050b500020201f804a403112400025041282c40b0b02c5605411061810348541180411105030b8080f400c4018144000720344036020941c030030700d4404c0018410b03423108100c502a241c802c000e000d183c0d100e0325100e4484141c03954000c1e0030b0b1251840c1ca1014214116407540c0480c03904c00000c20001d0189114002c05002d8001d4400000ca14500e4000030300e04213a02c0205a8401d10041e8420f07801e14015401c407000100e030490248106940b44451242440c6140000e03510410003205c0d050307800c00c000200800c5017504803001d02d44402c0c105081c9048802098a0300120780c12501c41c070f07403502604104554980b4203819415910060124402055043c808512919003c44107110041d44140102d05c640c1940f10a02c0b42c007580c0c42c1e0350310540d281d10015544007964000d0298040081205450107030000015001d4420300600c99444600318040900c01d0b41c02803030302d10407019000700704038050040c40c80401e984001c103072804004601e02625408811801841800c1c0144 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 461805647 1250 461804397 461804411
    0x203070c050f0d0f080a031103100e06010c1b0614040f1e0909060e0d0c05030d022209020a0318201c0b06090112080a0813020406030303020702150319 66
    0xf80391090030180a83d0000076038143c40120b800c00c002c3d2070b845103503118000b034544012890341d04c407002d0a03a0701500d144c2c110003030300f2414071840751501d00c070107042e440c1444060000100042e00414024101c0300d651320b0144407581c0760103000742a10300000c03200702004000340400c0c080003103010605070484180c10700b81c50f6414041503581d1240e40c5580c210420181c1450f01041c00d100f2103070012002c01d841101222016030b041d1408a03a03d11141c407000b0801c0d00100101c060002e22500a814028121001d03003013803c0c000310720100c945040ea0b0011005e507402049241c50103805204000703030682d42003c0d0006c2050a039444001ca44402412110340727044003004070f6a00e03110f141c1e40e0304c400300c3d118107281414078050415480d00b001c2210210300c200701110000c130301341c00400f0300482215803014400d4144213101c2c6c029035842c5402800c045110303402400e010003690b6940134034401540242c1b13006030780e501c844c014071943c01804011300c40301600030001d10071910786880c2204612403031007100083d05 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 461806897 1250 461805647 461805649
    0x60e06060f2b0e01050417210405010b090910060b040f061224030c080c03031218100903030b04050907120206071709120609070306050403050903011104150203070c050f 74
    0x40d10410482e0070140c60114602c58000c0d05602c5140298000c01e0015004641c000d0306820030303c600c802c005000d40400c2c0c0c28800d000e4001c00342642091084001041c01c0b51010082000007a00300e4400c40c240e0304c80303642218090b07003078480c00e00504544d003001c0b45010b08001c02d403c5607607524410f00080003603141215201d92083d0380151540110002d10f03004800024024a5119011b800305440c3c0344c099510005140000040c8441e004101801550800f11000b014184a400003040d6002080e481044400408030501c0000c44240c031017600020b040034103050080407075411501c01e0380503074600300611001c0000081c507881211549000345494504510104285028800c0d000f88450000c40d07020070902040806040d411405135150303540c880c1e020450139502c850585000c0b01e260007400d03042c0080351054102c00d40c001e004c4d00380289070010040c0400e0031500400203502c0703602c030041000c2c030500d400309803c032810501510041d401c1010613149c94a242c2c1040c89424031400080301401c0c8a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 461808147 1250 461806897 461806957
    0x130903020a08030604020d1a040c1b0b0915042315010e0a11030a0903230301050d030306050315010807050f0112020a0903020d030c030e011b0b0403030b06070501060e06060f 76
    0x7d07080c0010b400b030020918402240b260a40c01103072080c440c03801d05501e00d10151007900c02241c010035030003600b00540c003039403212008204094401840760003901099411a500360a415000e6881a0f8012849506605008840030304104100340f0700e40020a00744203070800102ea40341584e050341c29500a644400d15610000d00440c0d903c592415400300420240d100030b90704c070103c1240603840301e6041d1204494441c0e5070b46425500f00324582c10a0005001c5400c200301014041d41c820300740010071035100c2c80041d01d030405100d9000f0201c0c0c0218010320901d401803000034024038056503000c00403072a0800280a90001c4080c0d00e6a1a03800f02c0d00c5a1840c1c841d540450041d90040c00c12603c494460074020004c8100c0e020560100b000034009210300e512403a2410804800b10002041802d4560340343c101c610405807084e820551034120560103551030030002c003049032095000058a81ca0040c1d13541240000414083c401c43c1c0c107010450400d41d2102c200c6002010705400e40003040c0c4000f901002e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 461809397 1250 461808147 461808157
    0x3071b08011401080106080304051302090310020f1308120702011b080a050304030206011e09020a2a1110080718151106090d0509060a030e01110306130903020a0803060402 75
    0x1a207600b04100001c1c05081e01103520706859840c0024000076448a051990f00e10403803249607040710840c00020b6110101394040e00490500600f51400c0c200c1c1c003200300e0141c0c2c10960311300086610018680000c80240507840000300f1901c0051301c0000c1d00002103000600901c0c030b000c1d05008104403c0740b13400480442c039000f49079010502d682c903038841d954000e00310380080f50708601500c42c1c5000801c2c1c28040141039001540340409213900c5600b0f1500440c0650000d01c1e5030740501403148a800042003103290000d00450b840303070081d000c60b859410300380c90012404800c2d40c012800b0765200644664003058990340300c400d60600203010b8000d05569036881f0710744d9010441d05204002c02080d00ea5010b081d189003264060110703449906c81c4624107443e0094520400c001c10010004000f150074160068600e01046007400a0811a0000201c1c00d40780724140280f6103800000400200d403801c102d1500424800e0b00c0c08201a0320190b0b800381d92404140006010b83e030000c00022000e07501d80d01220b0f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 461810647 1250 461809397 461809409
    0xc05090d0f06060801091a010503030a320d15180903020703050a08040905010b090a03030e0d14150c130b031302030d08070806180621060708100b03010803071b 70
    0x16565049107001b0002118100e51848180c4a0130a10644201c080342c180d6400401031480d0528441c0103072400703109540c8031540700c400c4184403900076035804821100c0a448004484c0d030f402030a03c3da002201e9091402440781d03034450b142400920034004821418040c898800100c02c20320782003c0c1c0c905041075100400074414001101304000140d4050f008a4400785424801d90340c071014a130480d40129100f154012001020402c0460b01c104a1000941005003480c1003410168a400b0181000d9041000c9203034800707440348021503812203002d5400700ea10860f441c01d1a0403542c4101a480d2030b40700700c9800f9080880410b071039541380320030200c010394000c088405003101c510025180d607504607804000718500900086076820700200760060845050b040c0400d40d56500104071428070600d030800f010b80d40d44544006c80050800c00d0031701034509612001040c0c684403007406541c90094000b80b940042c10b02c0100180d03203000064850305940850103508560000061041c0007420354004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 461811897 1250 461810647 461810651
    0xc06180b0c12060d0f0312060b070f150501030203100207080906181002010e0d0c0f061409070506120606181e1302040303170a021207210c05090d0f06 66
    0x3000d5929000707402080040400c8074405041c0d40d41d0004c010038040e8581019280c441240300c3c08001a2240d14031803140301d103200c000504680c5608220b40c841d040307110101d880321800c1c4104418440c00480d0b4404900c5c20100501c403135811640800e49400c601c1e40402009500440d8003410481a02e055400585c4042c0040d6111a00303034100c0c8400b00700000b40c071400768282909180c1814418061100d8850360a0010103e007002110211098400c002c01039860078418003401001a18074041e0002a580038500e1070501d04004407442d08004403503000d507106000800c141c81581503840c90710742d444001202c2c220340f02c95000400d00c1e00d40c4005405554812094080c4c1110102c3c003d040f2141080706490304646070303010344c6401c0101d210360b01014000c0707400240758600980b00c4e0084c8903400a01e005000d8203110062040c0d41030504103447c000081050501d64071900842c01408110704814a44140080010160080d215118510365039000d0100c0c041800d0034080b5001200481c10b07489041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 461813147 1250 461811897 461811901
    0x503030307170603060601140f0915190503130605060d020301060902030702070b04140d082710030c09090b06090d0c051c05060f06131d010e0106060c06180b 69
    0x1005140300e000310010b030681c203415008503680c0c1c2400104188100010b07107592014540421803e8203540002200c41c04142c5d00b04210103640e202e05011054030040800700907111116104050301c00606003142808200c400d1080010303450b500124682990b030410000106070712041e01050700d90301d145034081e400d136080010000d0300d020030313a00862248140c0c0c1d081e80c1c0710f1a20740500c3c40c201d1103540f08000c40d00a040582c0030261400c1c0400f210f0003445008118a4000d0340e4040c01d8040b084040340011411400c401580c49040c0698503c4010303556240400017100c6030103028200d107595014074039140b0b580d0700008406469410841d0185a030003462540c0c0030720355150042071003038103001c0e2a0240c0e46104001c162231003151404602140d000f006400741d41d03203003031b420000000c0041c000d9601c1698022080c00302c0c1c01c58807441d5403041404c4100e11907800c003d07800c9429504104402ca542e07030b1404d80104601540b0010a0b488030364007035408280c900e844075105451021006001e00100740c0802 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 461814397 1250 461813147 461813161
    0x20904050d02070504181407030b092803080a0903090f0b130503010902090a090609150f050f160c2618060a050706090528021e031207030905030303 65
    0x149200100459401c40f580789072544280419182080c0059085404032a01c40001910918102c000d04a120040340d403d02ea503a01e40304a11030f019906001d10750800b80d0744d811498880c0201c581200c090503012139042c0560341c0c00805043e8002c1940c503600790303900d000c5401c240c401c4040ca001045072640204140c0e031610400740c4d083d80880580c81803032408000000d62400c060080880d2250024054546076584401d02400f0f007442100440300f65070340c0c403442d00000704018640c00300c1c00380c480c07000503081482c0c070341039001c4480c01b40040b8a811050f10400c0507241d0817480003040c0903020702e08801425802d107094040004008010a04544901c40407064141d80340007810f0b10071242c1d400c1c01030411141050005611801070840c000031030410000c8007040141e000800a5031094044031820100d41024016016010b001414051102d5020704203600c0c0c50040b14800426036405125042803250000e50344400d6207094440c3c48901044940130f05029950010003840c009d400d803135981c40c0c141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 461815647 1250 461814397 461814403
    0xb060a030f0605030708071a040906060e031e0d05090315071e2309010c0203060910060906120b101205211813020f041e05030303090303070f090302090405 68
    0x1d000c080d011403a00d4000103051070005451802c5445070130180900b5428100d03040201c1c3e40d61103080e0382102040000080e01100c0d485118000d100c82e581e091408009801018105010014002e280d68103400340011901801b00d2034480f42450760a003980d0740e110881c0401d041603200d00841030a40f285001b00400170390042c10f4120313822502c03001d241000c02c154009a40e010035058540c94503000100b0100d5544400c40000c0c285960141082e41800d0540e0340040c0c5001400ca903001e60301c0d04500c6c103c3c0020107a900a0901406c02c10006200709410902401032151041002034041c1100c6030101d00c10702000003040380a40214400c800d6103a00c02d0600b140c0c0c5555a0980e0140003a00c0110719003002614001d032803552502d43d107450a0901218204062691151280445144e081010030b415410000082c0014000c952a6010220142c0b40e5031b007080d0b48035403025000342c00c00c20070840d0040021040f2030f480005410080607480410004903170320304054100a401243c1c620a10052102c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 461816897 1250 461815647 461815661
    0x30b0103051006060f08040303201b0106120201140a05041212021b0f0d0314040e01180513080304060906060b07060507020f0304030227071d01020606060f0c010b060a03 74
    0x244401c0c01040d40e90481201c02003401707044180011199004500003a209800c03030314000c17458000c04811010403c001d29110342c400c441c07540d0004561000b12584e13074070a0152400034801001e452403103140580018142502c10381c40190710010000310400d8241c010701c1910003402c020301302e840100380c3e5460b1010880c507042d50068054855440320038044070143c003c00c800004060482050b16040c0e6041c0540140411022401d00650442c000e44030074210000d4001458600050340c4594509004c600ba01e2800c9440c60f210241003c0c204039400168180b0403951a61100c003140d940d640300d0810000411400100800d8941070240c00100d40c40c604015000722405140700304010348903207000380d0341e543d800440c1004030741040c80b04001500e80060003815030145000900381c035006001800f0b8409804030788040200301c03071402c50317000b0300080305980c0d40206083c001018a400c00100145183c003442a841c402c14100144649010000790801a00500c02030109515a441090701502803c05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 461818147 1250 461816897 461816923
    0x9020c0609071a0412050f0321060307060e0d0f0f0b010501030b2b08132402030405010815030a0b0a1e06050607060c02070e010b1e0307021005070306030b010305 71
    0x82c1881c041003040700320442c03d01d00140800454909850007090403101034002609039040d000c1d010f05081c04a00a200821840c000b0702d2100d4106c3c804464440108040584030078004c2d40420000d01603513400c0b650340c08280c0c40c11501038a05141d640340c080c10403290703040002c00f207007600282041003012410806060756403d89043c44501e0724001030148442c140c0740c01c44048640d45002414401e2007551180a0380d0041c000303140791000c010350031307a0018680d0303204458400c101d400404603508000031083c2c01c085c41d8030195261600d8000000c014041c0502008117204e8101d0f509819641c0070030045260f2580100381081d0741c40c01b00881c60080115041c1c540307049004540d4803083c8103a520862060300c0c4003e04841c1080f0341a10b501c0005c10030002920190b10030628080b0f58080c0c078016080c02030015041d07841d80ca00500c02512610f03a060703400010140c4081c4180500c8c4da03004201501d0044500000085594411000718040e081030740c0003806403001c0310004000c1c410081845518410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 461819397 1250 461818147 461818153
    0x614041505091c0201020a0312060e01080a03030e1912031407110c0102070807030b0a0b0603150f040c0f081504060314120403080403080d090605180f161e09020c0609 73
    0xf01c580d03800003101280380c000a00503001142031000090086107076007050102c0704c00004905032113120340307039001c0303401c0e00122240e43c0503261103010150f05000c8d4220b0842c0520150a691a0701070709801c00103420030780145482e41c6c5c14030b60114148a9848803004114403403812041d070815500c0582401900341c8403c445000b500070320b0485500005228089078280b10007080c070341d0320716100c458501d60041d0940021907250001d182e010b84d40c40c00518000c1450400440304e8454010400c0810740c4010a418012401c00076001c0c400c0d60040c2c240d004414041c14a0a2560713156403225074500b0b1701100607a8018500b28002c0188020722440c402039500600894000030440a50381a49002d00c1c407000b0120310301000244005004140a41140f4800d0100403c1c205440d595031030640b0412100c200c01442082c0000700e9141c810021010031660550217400783d40288041c0501c4c54a45000f411700d0342c06101c4995008014007041040200241e000440d110300003071f402c031910355400b5626401c1907c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 461820647 1250 461819397 461819419
    0x30708071a070f050a18031217060d0b0a09020a2102130e1911030a11090f043512011e0b07020907200105010602010f0905030301061404150509 63
    0x2030040b5405450802e0f56143c5600304040131404594013901000b681d0f46041c40880c0001c00205481031080c60410551103e0701000d00817900c03252411001040180b00e40f8100802101007241e008941c1e07041030990401003940030050010400c1a1100da0040310403030410b484901012070501d08000905200b00c1d88a0020742d141c150301030035601100c1c00003541d5080310070110100810800f4113040b4500c2924039074100468600002d0030700d10812003d90349000c40080200c518504100c0550b44020131100004042c02e054440310007469020046900310109a440c101500064070400c410032001120104c1e580c0b035401c20508200d0070280320300c9800c221449031045921130340a0300102621008804103040c840290200642180082c1504043c03003034501000c0c803020094041c50441000b140008900c65240080081c215040a80000001032500d03482c81c00065000c03003120b04492040c03a001861980c028108140d61050f40d1200d01071703410381031907501c0396078001000d800c40001c04c80300021a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 461821897 1250 461820647 461820661
    0xc0c0f06010e1303090b040b0901030c03090c0501110703051e0d080103080a030518031614120304020d0809060d0504030f08063d17010902070b070c020102030708071a 73
    0x2a10082c09000c1041102900140c8451495038001070142d001e40b4080d5515603036070554480c5680641c1042c0412500018690440d5826000d04d081c075502c40d00c3c2c20440d8035500d07100d503003800640e805000d040003042c08580c49001e100b0049a40034580007019a0481d0492860007031120340441f001c0342d00e070702480b440160b21078010740132141202c0d04a41c0152030041c1c2810220000e010040522106151901c0c40504031002003025010141c10204150440e641d10306084503c6150706001024651115102010a03ca060240d0343c2140d070541c0c0c0c43c0c07980d014074a4254001d01034500d142d60401c20120300448141e1403a00443d01030b600070b407958042c0032889042269464421a0322a80100c250280b1b103282e642251090719a0350640300136840080b9484540c601d40450007560013000849280d88286440e2404a038240100f084150031840d21126680388240c4a1000b000c0100348500003500c4020369009208440b0030704d9000d184903035140ca251a00722070030100d014200c0b5004909600190318 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 461823147 1250 461821897 461821903
    0xf0303070305040e04081605030c06090708071e0b16060b0612060108090a0c120506061002070b03040c1206060305011407052505010f0506090a06120209130b0c0c0f 72
    0x299096500c00b40303404c1c200f40615100c68400b9000300c0d10142d0800ca010082c21513110040406441800a1580c5020030402d092410901405402064001203003c11541e400015840201e0b40840c49006407048c1e1540803159002e074030351060014600c009085800300e13402d082d0108900348543e0f0100100c00001060103094061810201c07000307241c80c004902e080d801200c580d54004003950485504c0e284070368a4050146032940714001105040301c0220400005000b415031000040d24001c0c0c4417906110025513400c0c10740704421010720000082801c2c002803000f402c01801c01028958841d038058a05013008007030b82e200641d881d5180c40c043c07a8640e9107400c0094002d400c40e0340d445017030209074a10060020020342410200012000c641130000f0820301540790b40401c50b803c001094a000c40605c9001c000003019110001d142c41414002035501c81c00c418000d03501078985c04c0c0103a030b621a0b92030032081e80510140004110320104101c5203440c4004200c1000000305403214540320071f410540e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 461824397 1250 461823147 461823157
    0x7051b100206011206021614010c020c12030a050322030e011103030f0f060d0b0a02030114030d050706020d1e0c0905120a171209060103030801050a14010f02011b050301050f0303 78
    0x20020801c0d00c101303004901d9980143c0f601658031485070203060384564504e40c1c050054421021180d443e00c0382031445907014041c0034240481600d5004802086020f9142c480c0308007000102804000b00100c2c094011004044503041d00c809098120841c4605001c0c001c4c200781907190b070001e01414041752120901000740d9001f210080b8896025883d45608405420001400c0c5904003008130103071300120301050440c5008038850200180d503941030024881799092a00c0d0858003950001a02c500c882d0f41c420100e4080c0c3d50440c07801a00c0350b1030180c0d01005003018060300c040141c981c0d4081001103885038000e50b81d41600d0f8640c0f50301ea40c0c0d5107003400015401400400e1107600614055004144020f101d42c2c1031204002e000d07840c000601074000031000c03043d509482264440340040c01016045411540074080841300d204006140541201034003641c03940990400091140d4240e619000350411010300c640091054011100583c0052240d08248a052711440540ca51380356141400310440c1d07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 461825647 1250 461824397 461824409
    0x20405100216151b05100c1101050703060602121e07080a090f05030c0121050907090b060313062f0913020901020705060f0c0106180507020f07050d030507051b10020601 74
    0x95801082d040c03581441e12140304140c80070700a500100b1b84505451050b909913503170301e4454424642804030403600b125070060842c8241807a2150520002d6000189040310640b40481c150740e41040306500815a040c030b00f0041680d48010541004202400000c0c00b19030b020b5544840102d503807000000201225445007075010b4004c0d0041c0c4a9a500c50b600d2400800d504030000c2c07a000d44604820350413207208840c1c07a0000d0708030100a10003000e590244510190040f5422230a42c10810307250020761441a00042c00296140d641803480140604015000640d03459904105e000580c2c2011f580e40c0003040d400c4c0325400d6038100c174010040c68402c0d81c0e01540107900034644181800c090042c40e0b4403000d00041c5011040c00703a002417100c24081c0101a004403c1402c07040c01203484510207448000d021a002d6401180b1f08a228a8001907072000703d03082151456a414041c4c03e041d50107100740040500240100c034041c44000c40300b82903070601da1100350342903800440d003200126200c0000703000e80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 461826897 1250 461825647 461825657
    0x5010b040512030c030c0a031407030e0603060f10120e0a0f0b0c0d0e0d0914030a0b070c060e010921051c0204080a0c0905010b07020a030204050a02040510021615 71
    0x600007410901d0102c1190311101080301e140003150b4103880d01d503030000d42c0b024032191f000785038003000c00d5403002c01e4104a6504207082c90809a6903580a0f2000440c00c1c03419008650110000b007441e6a12460070301003501c040c150306c09181c1201070090140d200000c1001071a8140a10300c422520000703914000710f50402c000c0e151048030b07031f560014511005030103010102001d1080768440d42062003190801d00e40e074402000780400640c00074152805030b0b07120480c40005c0040704921514080351010300715900041e02c1b0b0980d610b14406407509001014044c0c152464107542a0507070b0340c15805040104c2c0203001c0b9102052126020307055001e10310202c10b0014905104404074000d02c15882d00c4001103003c009818a40c90300c1c20b0340d10344402200c00742d8400301c1c030700402c00a00070307144200d9002d08030403944e00e8500b1450750042a00030902d440001d0140355114000b6110110a60503640540001400324800b054605002961800c80d0410184c40d462030f5000007418a20780303907240122103c980c4072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 461828147 1250 461826897 461826899
    0x6020a09240c0b090a0b0901020c010c1409090703020f13050a0509070c0f051207110f040b060405010507020a08030a0908010b030604031b0c0902030c0717182103030103080c1005010b04 81
    0xb80f08007598001e030241e422446209160300c00295080b221380e1190510900060b00c0c2c07205040d45a080d1205041ca50301444924613065641c00b000c101220106030064a2030344154070745140881c0284039003071010584041c0440c4154011088007040021600d0464240c02e013144c5410401c4a900015586080455950081140012148090800d4041c0101d068402603089112800780d950b000103004c850351b41e4854118030303c5180c03008040305148410350303040001b03101460100b643c600c5240035180c1800004141401191740c1e038140380015000035000c0e6621070f0385030803000d0041c8049015044082d405c01d0350b413480d5424000f0341ca500c900c0d0181c0d038201d81d8591041d12a03083c60100d040c1600c0079a020f5102081404c82400154052086003886550341c1159040c00d9043d08006000c280000310100691801c1c520a60b09024503860200c8201c18000c12603094000000e2000d00c80020500001c0000024806940c000c5e009445004082d28400e03010014003404881c800d0007005000710041c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 461829397 1250 461828147 461828153
    0x6010e0c120405070504020706060e0906010503060c0c01060b071a01060e060f09010c1a070f0203030f06010503070c0507030b040309080307020102061501090306050112020a0b040f030305130306020a09240c 90
    0x1107190014000c0c01076980043c1c03214041002e0740e1100c20142c41c4a91110030030081840440f000307541c08580c21000c3c02c0c0d0b039414030380002d4031003001411610170342202041d013401c050820b610040082c603800c580107a403030005160a006e41d60150b61001c020a50050000446a000d400c00c80c0c11400010300030740ca45025052050f2041d0815504141040403940c2c2d038400161881200b054401907100c800710302484c0a040007018110015a044d00b10741007841404014044c40700102e4114109003021900c0b0b9a86103011101d03104e8440c4003078450310920b08004280000520303640c4c061400303a510720303107400d0f143e00240e80d5a210b0f004009005070b114600164100e810824144544041407404443d155665100c86068800030b03000140d0300075265152004524004051500804032010000d0405203400303100700c0d18004501c4098140a800202d40c1d017000e00c1c91500e040519804002151102d5208100074005900d9000d003451410210400300c06c494110200701d11000d0301656042c400048540d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 461830647 1250 461829397 461829427
    0x1202011407021309050f12121308070602030108010f1e0c1b080c0c0405040b01030f05012c07061b02060c0106030507060206160906090509090c0405071106010e0c 71
    0x40200046040521216006940c3d103442292503030342441001c01e2441d40e03070500a0810f41d00014924007944402811801710070303504282c804600880800039055510800380545500d460400144482000603620b01040502c0d4040c41c1aa005900200300c540c3c00813043c0300442e094042160f0084842c0b404c650900c1c02207400c008000040c0749815150b4070340680300089001c410200440f04402d0104150a0603a0104125102e41004032018000c60400d6102c043d0301c9401804054602ca000000b220244042500100d071000e181041c030f26074021035070030821210400c126a41d2040c2c041c50b40c00242c4036100742d509410750001042039203001e0030700740d0810905920860307800140303540302c94000000c50710a1000780010229500603000c0c41c5072051800002484420000d403d2001d050303c10300c500c607400034a1100380c1e501039450581545880352a03e01c1d0108540340f059110707050030200020503501c02818442c6066444c100d0360030f070b40c95a0144a8544084920307240c001d0040c0400c0721589141 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 461831897 1250 461830647 461830667
    0x12101e030309090b190807140a030b060d08090d0605060f04090507050d050c0405070e01090e2403011503030e0a08060c03060d0206040902040905010f0b0a021203061513030302010510120201 83
    0x405d0821414020012100d80d134800b035101ca200c80d00b02d81d00030042c0c03811071340f00d18030303489400c443c142c4920b411917843d12200e240140119001c1d89480c03944004000c9240221040c1040007802d0403024451440d00c54040c040458565000360264480805d075070030715010b000b19450740300001c0c00c2d55509000500245e61620030041d00c0b20710841d074401e103036900c0b035105503409031641e5a00c80d0305d5200400b0001d06900d100b51710801c00f0008136820000c2c062030314030480040400f00b0762703294212000c090009015000c540e02103061505481d100000301a00960240c04e0000203543c900c4e85199122840e40c0c50b940221410300e0607400c1080050703050f107083c40e5007402c0984020103090034141c8840b1407000302c1c1c005030040382d1407a548800600c4880c40034004180106003140f60580f4002483e0402506e405212204189440700031002ca0910b58a13401564180000032001a032241004500070b10358002900c001e0f07025520704170114811000707090a030300030303505451103000c694242a401120b1113a0701e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 461833147 1250 461831897 461831899
    0xe030c010f030b13020c06090724210507030f110703080f07030e030301090504060609090503092209051f15060f020102090904050a030f021911030312101e030309090b 73
    0x500329041094220b1010300043c80e2000014484c07840c207071614614009e440d0300800700300340a0003403084441501d2141c0040324001490518180b1306501e6280340e405204030003440a10381040200b0000d2541903022041441c0c010b001800b8a50001d800641380e071260441c0900001c8074240000c16940701c090034160401ca4a20300068040802123816007076030400e81028005607110001d0105001e21401000040c000c0341074200840c4d0350550f80c0e55582e100f00e4048602522512400030000c40041104d10740300641c0741400c0c400c654562070318640f244066030150910300c1950411004240e01c40c455003043c9594000c4440000d400e040069800f40145e00400301159001c0045c02000c1c1c0710340c05c0c00b0303004503c5034008100048892401404100360800340c80708550200801e81103090f110b510000c01c26411840340d803110346541c1c0110b410b5208103a42c0c58551400c4070240446c00c8100d0000104941000c0640c88000c005149246440704103444054006414058241708581c056400b44a8200e4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 461834397 1250 461833147 461833159
    0x506030f070806090c0105180d03030b060f0a1d06030708040c1203050417120f360310060503060f1f06031d120409180b040b04030e030c010f030b 64
    0x5010301c0c90008640c0010303456800500601004800c10400209548000d00301141071403010f040c0b44a2111040705114482c1800301045400d15020b503001e13110022015040d40d584036002d81d0000500d1380107000b03000010307d04078040c011012100e13290b0009010020003052841d02d9441c0202e0f2004000b61041c2c84c055020200002d00001800d224208144651200c1c2e0b100c51070503000100d030703003000e60140b4620781140e07440212400728041210190300c403251009417100c4021040405d01000011a0003510040400488064030702c039180d6002c100c82202203c40c50500a6030b1032050341e809100750f0b030301a40403130082406244012802d6034400c68001c1e00d401c440941d54000407800c00d07940e00c4000031036940c68901c2c00d1040ba015151100582007401400c11a80100d02e0b000284a00e00c920080c0c603650340381c0300c080d450166040707405c519000003e00d40e640c140707400c04180180003503030101c011600a02060751142004a501001900140c4a0200001c1c0300e4030264090034143d11459440b40c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 461835647 1250 461834397 461834413
    0x609080a112809050103060e060f0106140d0e0307061b170604090807030e010f030e070e07020102120703060e01060f12110c100509011113090213090216060b22050603 73
    0x40e1014860300080940704401310b1907500d0360815104540c280c90700b6885070b80080040102c0d00020748001c0c2d04450700c41c50504040b0100c6003203542c042c01008110484d4a00b03002c81140301c0340000001d44402c2e40030341030801c03d80900c41500c0c80c0040c00420440d000c0f03406144070039410030358001000d900010140020401440c59560301c495540950300860100300d0300305015400e540c0c00390070409480140d003004c001a00c00304299554540041c820fa41c110200800011921f51007034054446207d844684210a8241540b02802400442c0503048000485200020f5000c0c4240005000a41c0c55242d4002d03880c68060180003a1602e1840c41921503400c005000e64410200300c0c072442c0d044040b400288a0a110700c80600791080180514000038041c03141707480d4160031035183e00c00c03a0b45100300140d035107600b106000c011000da03510100301030b403000c074004034015040800030721900d1081c1d2041004803129001c00030071301200c0c02491850482c04000c0000003c550b44100d030401801000c0314481 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 461836897 1250 461835647 461835709
    0x414010b0a050d06060f080f010b040512150c361903120315080d1b060b03060f160f09090f022206021209240d0e06010609080a11 57
    0x18074010780c07108000406c1440c98580c515800540d90340c01c100420680c41c0a0352410700041003138003840c05107501c0f0304040d4001c0d1080307100c20800c02c0440328000c2400d40303540c9000f403040c40c49900007207100d4958541c40404041c0d91000000c0d101c20020510415002c003160150901c003103240c600303001141c0b03002807510100c0400c6210030380340540c01300c035a00469640ca10b050880d1420389254440c0c80d090780f1807040f214105800c002140e076520301d880c41400040391142040300c05402604003550b01800f03010180a0341c4a05070303a510340304001e07000a12402d00346441c01120404003910b9444002080710781c040c00f0a00c215004801c01c00c0b5100805030034041540b079595a482c8074100001701143e20503100300039240c3c0611001c1141c0c4460209603060000e00701c0801c861104c8200100d10104c00011401c501203041d805941c1700481e9580100902109019480d54488080c010302011500c060780c0081c00500005036242e40991000500d0704850a80d028084001850183c0030968403440e4102030f00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 461838147 1250 461836897 461836901
    0x51014010210050c090415080a0f051501060503040311060702070905090f071805161205071e080f0105030304060c060203071e0306092714010f1503020306060414010b0a050d 76
    0x501071303203c40d140e99406502c10003003110040c10071000c101846150030407505901041d0b02003c980c100c0040e05141d4802c1c41c0107820200c0c0d500c4a040c807050b0640002c1001588000514411407080d1034080c00342040b2541c030369490b60200c2d44040181d001e002d0600203054103411042e0000762040071074000212100025080030210f402c0001c82600c0b070f0010b4164003900f4002c41d50000030221501c401d41c1c800c454018003000b14816407008080e1604081400944070325440701c800c51300b00c3d540079582402120024100c41c001d0721900f4100c6140c00010a0b40d20f0044203c4040307810070f8950840b0135000c0e90301e80d00a0342005140e17130117200900009284241107032013007147c050034075940010042c0c20f110303001080325280c40601140c55042e414a40d0010110f03032001074510740202220103006002d10b420360260140b103120f0b440450400700d150140061114000c1d0507684220181ea000340d9a040903c4121000310051011503014400100f00d442c1600000f041c41c0009894881e01d006a507800e01d000f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 461839397 1250 461838147 461838151
    0x50309040c0c0203010501290f07021503060a15020a140c03070f080105070201021602040b030a021e15090d0221070f09051005130c03020403020d1110020105101401021005 75
    0x700c1d80c0010b4280840c40d081c03150300d01620300280d41042d082804554050f2180014452003c1c80a0004030000440c1c8070788180c8034503541c010211b600714003004d07051b1001a0016610540190017051000c144000f020500101c8603101c1e6009241c40c2009803100c0d4a1000b814a132843c0c0c038010104070103196141800700002500141e016030070350500e4132024508450005048200716441849500503c40549281c13200c0c00e42c04660210744001d816000904113107240f24000d5001c41034442c5070824107003d1a00c0345141e1001c03138200c079140d106080f0300030180c45040512a403003513513240c44500514101135000100b008200248070003910b0400098a84a82074011000d0161001c100300311941e880d01603540c0c404100c20051036007503c0c02e008607103c181402c81c06201c544d01c1d4240240c1c1c003446681070758000d42c1c000f40103041203c002e003450080d058640ca034260161000107003040c401401406a01c0c0200d00e80b120065030b182c5003a0f4100702500b007081120341103001e4045903580d40744240c040c03070b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 461840647 1250 461839397 461839421
    0xd0f090501020702421314010e030a11060a0909020a03060509420d110a120c23030102030a05061201090c050918070305060601030609090b060d05030904 67
    0x50b0f40703420754010405003080c40b0400481e00070f41c2c1241d081310802c040c11710081600680d19024421541400d40d07482c1806243c046140e0701c2c0120000013000030380601c041010680a8036195003031420340040c181c58002c050760160501810902c00c80032401c2c00c01c0104484006842d01d228050303156007441c0e00740d03400030035038000080d29032a040c802454041d22243e040001c265004000c00607918035031030302800c041c6604c001200c0201148140c882202610151848010302d086040600c603d48517161035400c034003141c01948409004603490781c41d40ba65080316600041c0300c1030f0407840c2c01011354207101000080702c1081c50044c06c60009803000d0001e1400b4545d9a040400c1ea4680b403402d002280c0d000340c0f003401d0035a0401d840080415601400c0c14107076201a40c0b406000c2e5125800341c40c130448240d04801d003d2007481000028004041100e50041900740e90030300c01c260f9509580b0003640d00040020f002d418482d03009c181c6a15211a1a404480c400c500752420071115000080444800b407400b4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 461841897 1250 461840647 461840651
    0x60806040f050d03140f040201030b0d03080f0c09150315060d020c0105150d030c0206070f0b09070b0a0f03020a0905040c0306030302101515050d0f02091206060f060d0f090501 77
    0x1100420000380072040210180b4a010410241742a220180081010300810120000c100128095921a4101c8040010f010307010540d074641f00c1c80d006004010481c1d103070b00d000d00d81801080d016030043d030840d454614010310924661128002080980c0d001801c1c483c01c0600344c081c498580c0e00e801026248004400c84010f0701d0f2400b9403001400c1d218000d082d5052030420380d071024215902d0000c000d04050305843d0211644141d440403c41c40d10074001e000c1c0100c51042c05e80c07410807900321517080c0306411050590701002d40c0c40c49905618001c20b0600c1000c01e22003260140b4040c4a507000c1c00003000c0e145800c00115607070380d011030111040c0e00c501e81c5c00691100e03000d00070705070108140c0780b141440fa03c2c10080f01d200c11001000ca9002c50240c60200240d0300c050f00040340c40b501c15990400c1e41400e0802000705503e810400a5001c8425603002d484030543c45c28990a021604610441c80075003414480c01031802000025030140000c8030100c1d0382e51102490440f403522486030864880c03000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 461843147 1250 461841897 461841923
    0xc0804021017010909020f0a06080112171303021002030306100305070e0d150c0504050d2901080d17040b01060818010e060703060e0903040509250906180b0f0d06080604 74
    0x60040e038441f44c81c040d501880c0003070420444c0c15448040c4c81c1c1140ca80104800d510b003009d141640e04000e00c80e000141d02140405c0d99801c10009000c03400842e4401c94034802c00c01407480041e0b850340021501d00e94841400c00310305400718025005640e200d580342c6404c6111044d6440020b80b0b40d03032040c005807410384840240001e0300c2c150307201c0d007503030307280d140c04e0103414686841c0001c0e0b000b20041c40018400c0420100070810009583d1400c3c4804054010704161980c40e550082d903a505010501c00c0050b000445040c1c0031f1180401c400e0155410800f1900243e091440503907142002501c2400c21107019241f80c1c3c50401c0c20700c43c1500500740100500894207203c0d00042c156402c9411505084a4090900c82da07510000101c0f0200c0c0c5003503859030215a240003114100308841c02070001c80c9654091030b14a804d038080b440c03100303891440e140c60110920000080031340380c0180c009c02c194400704001040d5020445c0b00900403101480c84040b44094640c00003c2c100307103040e50101d44030400300c08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 461844397 1250 461843147 461843149
    0xa0609050606060f0409020c0114040b040c060c02060702190f1d0612060106080a091e1704050a052e080106270e040f02040c0e03100c080402101701090902 68
    0x4250414002c4541d242003d2150315804039521031481030601a9030300080708d0049480030f400540103010b81e47c104500c4c03071626049c00100c8040072542103805c580c031200041140c3d40150010507085030040c1682d410550305038244502031180d403130710242c1903100301720010320301ca014200c40303014028440002c414403510600c0c00d043d02e200942007074800c40310707414500758001c030010b00c4c0e070304456031864005196282d41101c0c82c0100302049000c2c3c1102c500211101c00f0310404042509558840c85103042c1030601c501e03049416000b42e005a50340012400410042c80c5013035a1070390410002004e8005a26602c104806000b5510314840e002051f400c0004012841d0014840011250403014055441e09601c4072544445514050148180000c1004c20f0a014008080340c1d0032950107002000b803d01c0341440036165564000e0403500c28410704188015100b4540203440a43c84d0584480c0925102c5a081140103d1462000401c00500e21000c0c110381c0d0f0485000f600038103000703100181305030b40340c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 461845647 1250 461844397 461844403
    0x120306090e030c06190209030a060b1e100c110301060e01050a0b030702030a0c0515040804090b06120402090c0c2e050f06040b010513031b05010f050d0504020f030a060905 75
    0xa0500074070303a0400d001101c41d207031010950540c46160046000064521400d0090003405400211034061080319404001c21045521540c02c0040498204d00800003082d10780304a40c5203600e00540000300c80800100c614090b90010b90041d104e004a03d028640841c04203084407102d52140b400d0309481401000b8a00300132071900003400141c41c03a1481e614022170701956078421091280300300403004c2e207120148007042c842060035524000d43c00ca04c6051030300344402d058116018003114180b80c40402c0e0750620349007007107601450356050a40d05981d01c030b0f020440c5d0618024541201a601040310340c08a980174014410300352419105204001c0041070038101980c5401c4030b0b20180e0b4500300500160000307070100b440d88103a04840110700b121805004a0389030060381c0c1d440d01c0428901c034010080011f40401c4480c030589141700114030640c1ea00044030323554144401140807400130000c401007a015a0000e9500500140c0f00c0b214103030480e0003091a190340e11409841c0c544ea508041000c014040c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 461846897 1250 461845647 461845661
    0x30f060212010b2d0d02030f15010314160e12030c010b060403110f0102010f1e15061b110621180d081008010c020304030b1f0506130312030609 63
    0x6190107506040c56082084540040c004c3c00512110829040d0300300d0b4a5241c08a603004c04039502e0035900ca0801030000350754008103495900c0caa002d13540142c22154801d00c140b000c40d2040c507520100c15191224505100c07400700340385408102d00ca100041c19a15100d50150555401500941d0364084041c8001e08407001081694842c1104120070800302d41c0c0400d2104204501b12110b5120000203001030303005020b0900c000d0202070406480140c01130700b0600300c249180c2c0ea50700038089103400182c0c4401c0c4800b60300401c0c000c158a550012500311802c04012340b2103101c0c0c581e4036040c1d0400c200080841d0483c005e51050f0303600e0700031900c86070b0b40d1745044640c000c0c3c01c01440548d513526810086d511504500284001c10180600007180601c2e201c190311300510188000f08a44180ba013402500e0754010b0000380e503021490350202e400c544907040b6540255800890106116083c04208210750703001c0d50703030310401041c122008004140d40701c404041d0300c0d1482e100080c0d103524041e4030b0f5060f9521 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 461848147 1250 461846897 461846909
    0x604260705010c0c050603060d050105150114070c1205160b091201060b03070f020312010605130602120d0b0112060b0c0c01170a09170706020406031103130803060a030f06021201 78
    0x16800d040350004000d44c0c0300300140c8908079400c030348070f590700000b00e080003030000c4000e0540e40c00e00042c06024048035502c000640002e903102e010554401588120030305c11010300420619441d2002c00403032800d0840d21003000e200c0c0094815540d0500da040b05d0b40420f54008188800c070002e03100344075140505001c08032542c8400244105450554140703041e0100038502d0003488800760003404000c0c407c0c8222444818000920200b550715030350000c041c1d030001c0510350f01c18640e501000c40c245000140c0260f0a411020000c1e00d0026005821806041a0800c99061181d00340010007106494061503024241c0d145205071100e620b00842c600d085040000c19040c0081d1445245000742042ca4603035101007c10000301d091001413a1507084007481c0306e0f004581b901c0214049041180680041c403c540c900e540602c001481d400f0492007500c015280310040d5001c0300c4090000800300c50145a0148004041c20303031003952610f501e000c1c484200c000310741c1241c1c00100b03007210966815000b40517000f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 461849397 1250 461848147 461848157
    0x3150b0a120507020a0506040303020906042105010e070f030305071403281103120c07020a06030e010609110904091113141501091205010b0d1505010b03061e060426070501 75
    0x51a0381b80e09854000144c40a0304241d00050707a040f0648070441260000e0024000980780000a04000303042102c0381d16003268554200b0b40d1002000034001a00c50a4070460074400c0601031550303070141d41e41c0d804504129030124001074001c050386410b00150000907107a918032021000c1d40b02c800d904100343e1108541c00e1004640e0000c2c00d103000041518105c0316191801c05807521000c407480228011110000d610260a1602140c0580d06402400343c80b582000284141c60311150716905441403c8843c0b40d0a28043c0f0540000d454542c002c0111203000d000800c00c001c0d4120045400020300e1550100c600e9142d2a0745100000d01c1042e2640c064103a0902c80c06090f10840001c00254243c890380201c070388083e010b00c0034000d00b075001302c0c440d0a009188070700c01e8000d46411041c080582c68000e0210b40741c03100008140c40c1c1101124880e2100030720007206012a859000d07031403c10340c800705410040a00001c5804004c1043c0d840007400720003000014521034080c07062809406402c0141000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 461850647 1250 461849397 461849413
    0xb120607270509090c03010e1506030606011d120f0703140d0203030112031e080103060c0e0303030703180c0e1801060302010c151e27050a0303150b0a12050702 70
    0x81e24000d004160380d01101c41074141d0b240c060b6802e1904682600c00c42e0f15500e008204661107500054403580c0e291440104041682d420007056102d00d011940e190110300d80136929203401720741020360b8094810040a03e02055002c0705550b00e0146940a07103c51a44400300602c1400340c0c880c400c68804145800500d88015030890081d2640018400c50f00ca41440c80910402c145c007601c40280001007031118420641d03a14500180505800c0c4010794040b0b16080154440900c504d104c000401d1025004500e151501007003200240f030032030544003100b0300f0031030800b000800c1f40002c980285075200e400706180c1010a07a4101b030000013281000349030714000d41000140d07000100e0444003a005424200f102c0700781070748500542000d05c4144d004070f0903030340144030b080025803003509003d64030415000c040380c0c014464040300c4c60b01200a070095001c03041100001740300b41c10000da07804602d607ca0003000c1d42c925000c43ca0740c005010b20800b091a128205200d00c8840c0704280d07000700302d44001c003022 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 461851897 1250 461850647 461850707
    0x4090f0b100c03020f0d020703020a0e130201110304180905010e07030b04030305102103020c0109120b0907031202010207210c0308180f0709050c030105220b120607 72
    0x16035000d035094050003454200e41040c0360013072240071000195141034940e01c408406d030094031200c840c08128880c000c0c03900c020a5074050034074040d00c6801c40003952091951107400649629440071114280c81c8410040410010340ca0321404c00d5101001c0404605031440d0318125082d81c207203034981c1d09150300c810301c20000700703205036115070704580c26083c0024251100d150000074000b05810400c01e003d440580022240c0c065800d60311824025421740712510001c4004403884190f902c2404101d100c03280c003803000706d400000c03510381100001003100d040c5983c0381d4448031040c80da4038040d00580d5000c54200d0030300818041d503040c0102c42030030001e0001800c60f4041c0514099403000780800030060000b80300d40400ca03c482c0024006802100d00100380001d815980700403d0146000d0181880003044544074208166410707900020512494070b0203e86c0a005035800070780c500c1c4031440e11081780740c2054507190003183c0c4500442c0301030041071405490160101030070b0320303500341c604c080d0349050850 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 461853147 1250 461851897 461851909
    0x902060a032f090102060108030922090b0c0c1506090a090201090b04080708010b04020708090d050a0c170c0d03050a1116090212070215070507080c06090304090f0b 72
    0x144281c207000881a009000192500c4200400b120340c80100145407410303582018081c0c24004003d03802c9604581e00c42250b140c80e40200300a2640142c04410740500030000001c440d102c0c680c0d12800080c502042c0c0c0c50355101c8071010340702d00c3d00141d40000c5041d11080103200c0174010301d5028038402e1581c00c150010031140d140040c41006059521784180085a2080c003080d0001c01001e07034174540380c0351103042141e102c01781c03446049204d41c0380001d03527022400c080c001e840b8481d4004401a0510581205225100080000864107130040050803000140140c1046001d408640306051039111031240b00c5d1315141503900d02d0745c031070070b801c0301c03070300700099100b4110380791260245020b001c6c140703c1e510303c2450001e503242400040d582100b00805e82c5041a400f400210350400d5403103c05071590002a40c40d4003e441c0c0c880c1009216800165229015500404c0c07424441c0f141585480e40041d002424004207640e00c4800d900005001c11102c3c6050040d544805010380c8100801071a682c00105 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 461854397 1250 461853147 461853157
    0xf0403030c15050c0a091a040e07021203040f020414060d020f06070807050610060804081912090507090b010e18060402070b0a050f0a1b1121030f010504090206 70
    0x4024000c18210100300750040c4014005582d5407003070115082096254002c0d40284940c00005951458002022890550003c8944080c01011380c079050528400c00b111070340041c446c50542c07080c00320a08001c05480c005500c01c50003940030b079460000f244108801c0d00e01502d012300c2040e030044107001d09540d5070b94201140c0e9a040b10701201000c104008146a4042c2c207030064a0000003203828014010081815803141005008104039551600d1058640d98070a490180c009282070281040017402134151040c0d9420905040603110110620201501d2110004443c641c00604042110050301c0c01003407503012003401c0010642e0701c848081100c121101d400e0343c1121900b9008609280c80b685d0481c0d141d15006640e03400e05260804074a000b81c40c00344c030700500703001d51040004d4141c485032169042c0340f980308901801d07030102200221a03180c000014541d440c040d2200c0d0700c07004c0741c81d030f6140c004801c1e0310030f801516440c142c544e00c1d000c0001640010b00440c1858800307001070380e545084903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 461855647 1250 461854397 461854403
    0x6090c0c060a0c1407080702040f091502030a110d0c11011e0b2e2c09090c090106020f07090c090303051e0a0c140c030613080d050a02041a0f0403 64
    0x41d807200310780d0201d616202c0485003211002c80060200d086c81102401005060700a80b02880b0482800c0c0080d41100c1245801070300c043c45007020b58844501035001107400200448000c00d8001c006694202142c0c0721203070003038000355101000500d00d60020710401040c142c1d00001c201c021119a00d06100012030a108200f0b80da8411000c422980c0e011002081c0344a413216445064648503114001c81c05920003800108081c28103081819405066960744407800007000b4855640c0a400d0201028000d800750314a4010100311081c2da031100300c0480d0081055074010103c082c5013080003401c00c91141c2100381c0039428680ca5820981d0000d0050080303ea140ca4100d907581080d8a00c0e0003510f07641c007d007a09c4101c0019181400b641e0203225600000c0c0940c0c0b0900d07102103100d00c4995100010084180c06421203000140700e0400890040d60050003015510701e003100506010003103510440740c0b0320b00c180d400b1605021200340d9800448690039001e8081d881c0041040c0464042d000300c2c4001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 461856897 1250 461855647 461855651
    0x606060a0917011d0106030f0b1503390a0e070504030f0501020d05070305060a0603020d02090a030f030905060f0909060d1e1704050d02130e060f06090c0c060a 70
    0x6420400d10903503071003000744561a0b90004410755a85018080d025108040c0e180034035140c50740c220502d0601c91413007101c2d4480080b0850005540d02c008803214020300d0162881014010744078a0703201441008900f48000c002058002074400402e0200c0240308450148880044820029622200b500348140c646002c2e614085540d545c1084a40e40305540000b00480b5607000c510782040710540141c03c042d001c54006000c140d0b070762402241100e1044070059880100c0000421225000c1e0780101030745003080b4000751a000d5640d000c074400b441182d004444d0030700040c40b09420306502084420250000301c0301c3c240340c001040c850714031a0240420041c0700d03240ca240400c40f02e5441f80700581144d82c0c0500c0d0126900f0105480420851042100b9039410020764021039030181504104c406035180207004041a1816400307000200c1ca4044050403015a40c19050742e40c6401088414804c440403040318496117001010300a55040103404165010014440b809180c00f0200c0c19561040804c500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 461858147 1250 461856897 461856907
    0x3081014060d15380a02031c1d16080a020303190e0a1806050301061d0406020c0102040f031b0e070503091e07172d070f0905060103050f0702060606 65
    0x40203481d03240d40c0130344c20701e000c0c1c152514a0310760800445180c07200c9030b804041e550f030200701040c11240300c1d80c43d484006800411140307150004000b052000d001c20801d00040782c941003000400c5501403200303011241d40c0300e500712008141c40c191800b4003030300f0703030710b0140c040e021440d404256030b4068034090341d50f0702e6070009001c00d050b486502d9018100e030000f021a6525540c4030088c6050003490140340149a003000400300b51030505001c0c0c542190a820516a0009144101c00440c003001600848447d81c080044a502000034006000a0135801c201c62800b40e20354030780300041d4038110301c0482c050070203020b08110b5aa550f5410310340c072030420309186076260340c0c00490900f01041080104001170950b04000303c14000040d8000c16519648011a05c8032664201140e42d0380c030908942d6681c056a02c0e003860081d04c04218001d58488503000c0b150500c0d2035080c2e040c017401c42c03904040f08e229504e0f41085182c0d0707071500486802480d084103103e5a81440d820082d00d030200108114003900f80011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 461859397 1250 461858147 461858171
    0x20070807050c06180f0d170c19060e10060e01033e0f0406230616121e0c0206031329340c0b0403081014060d 48
    0x110365010300500401071540d98585100d0401110051448117000c1c011403807a400321400c02c050300d80c2c040da4005d0710000b10a4050114616590b2084891040d64000c2203101c10b4000705500c480c090300da00c14180496004959440e840c60400240904250f0340c3c02c0007410045003040386a040d041d603801c0a14050701000000c6118a80509480c8d514401c0300f441d83c1700c6008140b28040d040d41c5540407030f00d907180803120004000a641e0b1a0060903100319a0b0407107103166011001030300d0791809014100b141445c1d23205c00814004e09841c0307015100d0310a160108484144d000180c501d07984d982140026103000b0142c8020a208c030f9030744000780100c500102043c1038403070b0603000304001c55020710b2401c0c0b5148021000220010b00c1c1da0301c0510514504046207101401d415003038aa034442c8450350710011494060184001085500718040c8200e0141401c080351641c09210301c5039010ba1640c1519081c03901c8005d80010066001c401411582804002c0303da0341c40c030407500416003080003c580201d03042 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 461860647 1250 461859397 461859403
    0x90703080a1d06030f06040f09030504090b010c12110118080a0807030608030a030e0d090503060f0c1314120309181b0301030b0712090308010b1e0a0c062007080705 72
    0x2140c220f6110b0004410030202418801c10a441410305840611a1010440e1400151400c690008022590510040c05003400c1507001c003100e0201458000306010305c3e900d4046882c1b8420134803100081440c0e01030800c2c00380c24015000208200708070070b40c103060152940c1070030b402180303800010060101e002c2003555100e500320401820044090740d60f0b8218401c0090020b00400310095480e0003562004442c00b800781e491001100c001a01419195403001c0c500140d402006000700c0c2c6540c03062140450582c10b03000080058a07044444009444591003000140520700403044429481081a03040c0703911014070780025281c03003030741044403526400000359401c900c41c01c05600c40d0001000000038403a8003c0d001e4000c082544031502e480b078ac444109001d88116a0001c0e000c41c030410010000610301000400708102003074505481e0403401c40e807181c0c880d0b000380c0c014000207500c040d0702020720205e44185080c002d0305203da141007900c403024000c0310340078005028100880109402003408428 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 461861897 1250 461860647 461860697
    0x50a0809010e071e120203150a09060f0b1c05070501140405040c0e0a1706040b0402010c06060305030901110f0601031721012103021c03180c0e090703080a 68
    0x103205845205844613580120500c00360350491042450389000660b060368110160b0240f41c0140152030f4482c09450214a9494050185261503580c0d003080004951140300340c00094005901c04a02c03100d10700200101001107400800031200070600c01c400240000404100f114070a00b4805180e4171039035140481c1e40103a0703010940081c200020081082e511000c0100d0406c030071925810419120075102c542010303020888040c541c1b003400881c0220716103c4038150310610515100c002038000d56506801d40d070990340121a142d1001c10a100290b07008480b1080040c40c2800038589401c00c0f03051140e030b80d2410b10000d004c1354240c0185201203a41d034800c4500c418000e44c20b00c41a2010011401130b407070300910552203410610304a4102d209000d03031900e4480d90301135000b0000d8403603888010f81c203000304400c080240741c1da8501c0188400800c3d445100d5040c000c0c00140009407409001c42850180101610055045001700780300084d0044255041c000d041e10f0324014103150100320580350080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 461863147 1250 461861897 461861921
    0x9070f050423121207030c240e0d0513210503041710020f0702120f100e01050108070303080a020703120e0c0f06090607060504020a05040c02060a05100501050a080901 73
    0x1c55040c1840b408441518040070300310546442c4444409400300d5511900100b0703040801041c1080f0b1580842d100d28038038103046014001110403030001419115101101007910000e05890328402c022014090220380a15401414081c0c50241540141d5203030a800b4082d80e110340122900d4070000d03c460720b4500000d030380d12004913030303a8685410001c8018105643d1110482c0301709644403402803079030f0098a50040c1002062414190140d003000f104d210440d400c01c06621420050304c5188004100c60150201c88520006101070915110f03829541c0c140c1050f5816070000d00c04000003540221515405213032000c00503120506031808480009042c14844078071418910704540b1a200800c4540307c644049540c8841d802d010024080c017070181e09c12a0358004001d0006501087d016080f1603403091000380050328403a00e88001508032021111a440107078080c00400071840762038407580b41c2211a199401459601d0440020080c3c4104941d0101300082e00e800705003020001d420410b500f0036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 461864397 1250 461863147 461863169
    0xb060d1d0706081f0e0f0405010f020d0b0901080a02010905210607050d0c030e0c040b0f060d02190201060509041e050d050a0306060503010f0b0a020a08030916080c09070f0504 77
    0x1659140c020001c0300240c1c4c2003c8500070007440d41c000040714030f80890440e28004036803c01d6030349525060582e20b00c000e0054641e175407500c60b0646180068030007020602c000210000e01d00d5042003d00200a0058002da11b00794005400380001d40c0e0003141c108203d6804880595070b00035a120100f00d015030840019102e449507809001c1216000b101811524030108020003101421910071807c0c1d661303d044d07c5015402003100d18405003000e80020b410404054405580030788428081249a88004280180306d98003082c6500a8012079108059820580c4001d202660620380024400039000e4002820b44c0c085505e800b00300400d228100308070076001015612800028000944030ba800010f0480000b07180000c00302c1c4031801001624140c414000d40c540c9a1410445090346540c4000c81080640c840d607140500020b800300001e61040480d8406400e54100141d502d038140000390b049418030350041205052a6100c1c0203400782d04c40c40720b103018041c0400303248054030380f4402c64200b0703c6450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 461865647 1250 461864397 461864399
    0x30c06070c0f0311042f0d0915020406091208030705160503030f1f030503040302060a030216080a140a170a0f020708030f090d05070b060415030b0603100b060d1d07 72
    0x21300d220b1100514000f0380b000e218100365400a44801785d40c3d8100135400510304150240740880920207046078540c68000060b00100700d48401080058041d15044000c0d000982031100541c04594000141450602071403c02da65940308011800024070b1003041000c003148100d4120540f200c40811182c00c81c0580380c3d642040806040703c01c4045580592038201001114424444d0340c04180850f90000061801d0a04650030401c03290b00600da404200340c0c00b40881010112070a030107642040c850100e26546481c0b1010240480c0c2440205158a80040c0401c00710150090141c00081110400c11085e5a07107000c0c0c640004d080381028142d01c144007289000800800e0b070001c5009080080fa00d0365940d680d070202d107a441d1002c07070105001a40c203001c0040040c840c51900ca41043d4005c0c00031a14640d64840081d05048581c001e507041c112a506008003800c05002c021200c100001042c0080503886000c201c2c14807a102078540640e90701e14813803620140158888029641e030070309039141c403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 461866897 1250 461865647 461865653
    0xf06060912011d190b1306230a0b0109050d0203010e0303070315080708121e161a160f031107050102070308010e0f01060309050a0515090c030309030c06070c0f03 71
    0x301034080d10104081803941852280b07200004000000b640001e02c400f548407481c5c0e543c4544180058000c0d68981c40103041c400009803640104524555081080b1142c04503a0f0421440c00d00c0180020f132210340f402092203000d0340e10440304c000f51001610f1b8141100940d00c007190051903403c2e400c2090b0b000204c05d000ca5070790725810007405a1001100d5228503500c0b480659142c884511a05c0c3e001d42c08617200c4140700e003035139010f8030500152540301d10118081c0a1441540e601c55551801b40012418a03401044900e02959018180c0d101000d42c040c03a001c00840407040502d682ea030107211520108a01461003030304040f08585444181070b40311042480c02901075045440c048012601010011403851014030203e0704c5000210080c4403540d1808506400034150309038290341c42d01848140e800403a400704903001c0d04a28103c1b881c1d001d031034a02ca54504140303281c440603201350005c0205a085d0b6400240c000c11545e4200d4001c1c0d91380c036440c6000f0251300d00d0b0350302140801c0e000742000014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 461868147 1250 461866897 461866901
    0x4170306120d110c060408060a1d0f0307060e0604030c020108090325020406080a0c090f0603050313030b01080f03030f1314030405010f08010b031501180906081e03030f0606091201 79
    0x31a0040c011500b04c800c2d034504100300e0380210f01031881a80e00200000f1280c060070741000c101c081d03078010840b14225040c0891420441d0004020145a01c0002c009041100a00c41d20b008040014091320403818a65001400c0c40c941e41d10207410800a2004540c1c1140d05004036071581f0580f0005c103600142c50078848807031800701c59090307118034949140020354280100c1c005c18203507408000f80f105141006000b06c01000b030300800c08200e941c2c50102000207a001c000410118102d08045080c0030b2440c503104240b003405800c45050b03a00075007001a83d6000c000241c07a0002c02e00350315549103540303a2902c101c50f2200c507280a4081e0a410300e11400c0f24002000070400e54600380c0e1200422510f00e281503a21420a21404481800802c009032220212070780354600030a05160100d00c030a89168500e00201d15600295800ca595903000c20507100304210400d4400000108030400c01b54101c002510713030000800408034802d4060002c0c10070b44d075403011034040759030092110303445002590301c440c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 461869397 1250 461868147 461868167
    0x19030b090609030a091a0706050a0905010506040c32070b0405060603010902100c0317010b04081b09061e030709060509070c0b06010e130504060203070807030504170306120d 76
    0x4034038007400010a41c1c0e41c0011048070030114464890144040c908404540c0d80d0248190110406c002804044009000d0703004050040b182c6060100320340d0007a040003401c540f80600110f10580c40d0402d02506650403c6003202d40d845201240f642002420142d038446404261221204200004844003080285e0541e03501950013a0200c1e40c8682d6444145401c032511380c17070065071041820440d1140d80344552103410005100340b40c02c04040000d00300440d00c0d40000c0e04a5030a4150210702405280002c0041414140001c0002030444a5001c0801c5440001a02c01030144410014030050321110482070103d00b10b0240c04c950041da0b030390191100401090107640d224107504004100858446e5000806868000030240b00380c0e2586c4006492080215009a42241914581072040307640c038412944036601410025139246008540180540d000600030030500d403030002807002041c031122066009805094a00d983d1381c44000010754141e102c550f80740303407230b1280c00c9145c103165500003003002c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 461870503 1106 461869397 461869411
    0x60d021809040c090e0a021305100b03151e0a140406080f030a0305180d0c06091b0e090102040303120203060f0a0605120a230619030b 59
    0x40d05a0000b01d40949410400200070403800c005801401407012041c4050040303a40a075000480d142d02580034030100c680c0e81c500090381401d22800c41c0b00601803c401484d00c034a03001340c0800c080500b885d10b40380150640b800c2e40038090540020171880c80b00c010200d401250804400c215005420f05103503510545070300b0001580700c4240410340e840420300000c0d6903140140d10026083d204058020352a411040b548992407440110b0030610205040c502101c0ca031480c0c3c28000090004044c0c0030300b5011404030b004540c0031007801124200c480080c50b80303003182e856011943c200d0195100143c0803503900180503500e80070b03a034001e51740404014400d003241c0c50001e000c11040e03040b41c0c2009021a000040c01400d14000d0b10400c0e600c00c1050100303100d0b8011582da850300d103a03a01e541582c442c408400100300c290343c4446128030001c06407030311075610070fa9038100b840459405032130306 = true := by decide +kernel

theorem cover : BRFrame.Cov 461690647 461870503 := by
  have h0 := BRFrame.cov_init 461690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 461690647 ≤ n) (h2 : n < 461870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
