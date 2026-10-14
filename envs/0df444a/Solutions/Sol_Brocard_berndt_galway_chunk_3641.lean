-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3641
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:15:49.778079+00:00
-- url     : https://prove2.me/submissions/9fd4474e-679e-4254-8433-bde9572b4ed8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 654676258 ≤ n < 654856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 654677508 1250 654676258 654676277
    0x108150f25210c020705010f030e03130302030105151005090102030c06010b03061903081b0a051b100206190518070b0406031a01080a18060e07030c080303071202250b07 74
    0x14509031030f0500b007035a01607001044140a554851403000503148524103000ca00b140305d81c524a40b0b545c0c01050304080310303400c640e000c2c011031a080c06442c2d0003102042d181c90140940000140481c0d440356500b80034000300141c03240b80759000b0f000743c1f56140064002d4401c00d40c0c0d80c079a601c6007a40112031240c03294511407100d031140c4044410000c19240c200e036009040c0f1105200100085640841c10b82152140c0001540012000c0101c40c10300044d00d006507880801100512840814031440da005641143e81003101081031301d44032054003961010f0205503512004088084040c900342400d115006041d0045101d00142c0000e000321800d0303690400607501c3c40b100805294003446030340d500180507400460703514040e50704400696001c0780d0a1003041113095842c04101c404403101c00c0c03c96040301c0010400e001011081c83d0050104001031807452509507401402d0065024611254943c041083c1d94948800310181c060f40f410f0311618007000d5458104000c13030840454804000981044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 654678758 1250 654677508 654677567
    0xa061106070e04140f2a220b07120e240a0507023601050f100e030106030c0e0a0903080c1602210105090d050406030906020d060f08060108150f25 64
    0xd81c1000301c3c44100c1d82c82d04040c83c0c841403001155000e820b000e05c0e0102c0b400c0200d00c15003c000100791061140007445403d0340004800f4081e03440e981e0600348030300f1f800c004c40c00c440031b0358400255000c1e05c40e10480740c0d40e4040372400e842601545201030f41000034000c04540e41810b180c1007003203040340080940141d0000300004200076009005058028807400421986824403200002c45ea800a0070b20160010356a0302083c02c45210b98400c0d034074510203110801c024503200b003040350003500c41304041c01800c101c6d0700d0160404070064294002600c001603418242c2681c60240c0610319801400660131009810440b1114202c20246c41443e5181c40c0200c0d005840000c3e46041c0c0e1401510b545041034501481540240402d83c0c043d600580c0802004002141c1c0e449854041e2507206043ca030050f040c0074141e460140141c0006407581e00c6140c07400c0e00040389801050740000d07220491400c82c0ea8604d155400e1043e540917480c1203110450b031103440b0b260031945c00c045d0544116001480428201c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 654680008 1250 654678758 654678811
    0xb090d1205070c020d030201060b030c090f04020a020303070507060207020a060302030a150f060311040e181002031b0711040507050d1a09070f090b16020a061106070e04140f 76
    0xa42e501c0c00442c05002d034403401070400c4071805c0c903040d0190000182c0c0d0340d60b4200030b00d081d6200315444a184c12001500b50540c3c980000004481401503e003142089410324001e5501d1201a291200703001e00456000100441a0120740701e40c2d41c0074002c0303280540d403114050040d40003038540c0c0c1d41340c608060310544141f4001c80f030a4110744040341503503007592810000790010b0151400c0903070040ca04010208806400640ca240581c1103034070307030141c10004c8010450034101d5003a0186401e500400601100c4040e81e0b0b014240c000d00d81c14a1a560107041c900400088401d064903034016061108005020b90003401a140307048508038103000c0c0300560340300500c000d0144c140055014820b10080b4000d00d110b0050010301c03c845040100c50941c4409071042d69030080d40004c0000c1505c1c0400c07400f103042c4502c0450050000d814080c0702ea840c6840201d4850302e0041c1f020003085071101008060343d450b82c018504039407182c1c46038140c4e4181285844040c0c1d20883e40141c0b92219040c010800041d038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 654681258 1250 654680008 654680011
    0xf050d030210020901020709050f070f090b09061308010c030b0306061516050c1306081b0d0f032a0c05030c060412031701090218150a0302030a090b090d1205 69
    0x1070380609020040b500250009401000ca41c40c11489601d80c01318040449224107070040c89414500301546c81c20300c100400022070b8104040c20401648404c000c0e03003124605450102c4000c40d25151900008164103035010000ea0020381c056007400150601d0640651258006440c1a020358125542c6d19003441007130030750318041403a4100100010f0103016414958140114481d0041c3e032017110100d00007a4002c001c01210702c030455a2803a0400c00440c013000516110082403c403070101c541010002540aa424000641003280c0394040c0c8007014454001050910380070100540341c0211946a004881c01010048612811031a804225482d001a00c10300345c80300100352030710f06814040044500c0d514840102c00380f1a4001d01403262403501d506042c06020842001a2140240c22000428840115245000368002d0703000044181c118811181c18864a05001d640ca4446404450040c10a03d01c05040b921030081417140c8c000c0080ac3c601c601289559546001d26032517400744045a00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 654682508 1250 654681258 654681263
    0x1a06030c03010506010504031e06110a02010f0516030914060712112d190525020927031605150c0313020118090c0f050403110402070c09150f050d 64
    0x407d21041002641000d0002417101011486c50342d501890b68844065401c1080191503000010500b4026154244552440c2d840300355001e102604103034203a40031740031a805120080540b106560300c244001e58031030520b440c0f01d0204a03210f91401000040c100300d808503001c030180382010840b42900720f0500950340c11251050f1071000da885401e11071b4020350020000307c00e4148050088011001127001c00b0401a4851707100c450b130352007220841780e03604850b450180b41d0301d984040000e0050b0700c411044950040210f80c40302e084401014401c600c1401a5000f04401d12001800410032041103911801e00da00c20005c80e900b07a260120603a54402c003c449102c0c04070400d100142d84d00182c014580b05107401810441101d0301102c030714074075900c00d0381c20040302c3e20b03100c00c41c00740305270362103180840309090380c1c60143d00341400c40d0381e913400011081c81e065201c0c0b500400d0807000d004145900c2d00080c90181000c1108e03030303d2501130060110003442101c40442d00300400007403604041404c44001d95 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 654683758 1250 654682508 654682517
    0x1005030709050c0a050c120406080a05070f0c0803180604060603031107060e060a090302131d0d05160201050f0a0206150406080a3215100602070b0304050a1a06030c0301050601 77
    0x1c164000860701c9401100c0411114400e81d2150740ca000400c1c7c00400140650f942c40190a06c3d00d14000c0d01618409800407042082681c605038009a1041203402039941c400c032029580d84601180f5110240744803641c801c0c0780181f800b8802000203942c0303c0f508480c03103a00c501d0058800900708075180c100e2842503501003580300200b22082d02e814002010480000d040082e8115140e4003c1501e840c02c81d850180d00c03542e0350700203580040c0d4043c000550b400071300d0014072000004440043c83c0303001c0d0443d600d20501d80461200b0440e03004506542030302c40f992203400d49550684c00300039a12078060302c0d061801c4d40285450700b01c60030540110b406903000000140b0b1000740c0c50740c41c844a07100341c94200707007885004411b8900e883c8034081a030481850842c001d00f06501180086188594040d08140d4020788a250070400e16030007180e10341c110390550806607282c0d59030307040c44c1d030812040081c010085180c026000c41d074641c4c0340748018047d00050301158507841a00c0c040c1803c030741c2c0c140c5003240400d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 654685008 1250 654683758 654683767
    0xc06060f0105070f050106090c030207050c0a050f12070e0403021b03060c07030f030905010e0102120c25080c0a03080f09060411061809270c0607021005121005030709050c 75
    0x4d0a4071000180c00c1c0e2140000040751540c2e0240d5200700c2d4140c06000c2c00081e00021440c050103010004540e82c140b041f1005c4030744500d04400032b100207825002c1c140c0035800d102854004900140700c86001072184e4008800700745010b19000752104010003018007071129400c0c8a4806050015840d03220b001741c0014249010f0326503c064031030500c590855810542c56040c281d00086080c0164001c410070000050380304d04101241c034091490007825030325601c80a214110000004218140014420400c0700070b007000e02c0c3c24500401d10500d1001c9400c0c0c841c403044041019800980c4520031710012110140c0360f11015959615080c0076500a400c030b021444101c401032406200401d0046c00ca00e901940a0116001003500020b08503410781e40203121052005c3d41d449102c2d0210100a202c41c00307000040724420015445020750b54019004803140d000082200d4042c2048450305409211529420701d8101d103650405440380c003ca034000c1c01030500000713522651b0b008440c0114010108903041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 654686258 1250 654685008 654685013
    0x30307020a031d1917191407030b1f08031305041d01090804050405010501050a21021c051803070f1205040b04090204062c04090c0801060b0c06060f010507 68
    0x10701d0f018089030f856860840900281d69203c0c00c1140520783c03d5042c0000510b815510166850341c5c00d00305405400c868211204c2e90304000c116811644c2c0300c882c0701d1030002c0900c0c040d8640840c0d41c0004161140c1c2405108a089140003542011581c041c0200001c1d501e5029064990042135032010400c050b02109111a180070f42003004214a0100014000d16003e2801030030342e80d81075019100c41c0400101030026040c5402010f0140c102800d1251424800e08401400c102039800f2800b901d0f0103011007181d00c064a0380480304020300c0c80055040440d250b140490003448261660008084030401601d0f10170030100030344406d107810120314039030006a501c075194101220302e510400c01004020105908a4074070203400030b4401e411005031034500700b041c044e2503800261035050501c1c03c0150866041e600b1502c49000009013500c000c1201d01c2286130910003034440740c001400e01d50030a6404900082d40318054001d8404841c1100e005882d07048c1845404510101c2481c0040c03c1080420702 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 654687508 1250 654686258 654686267
    0xc0e061215040906050a0c020d050f030c040902041706010f0b0706050606070b040b160810060309020f060a0309060506040509060f130f11040c02060f1602010b150c060702030307020a03 81
    0x280700c0e9066205040000301d40d030014040382c080780c1e01255410750301c2050001c0d2415038402d8100310402800103000f000c403801406020b0b4060341c060040905000000a4030303010011050704e004000080045d51240d8840060808a58036511070050603c1154000950088040400401c64846404651130010301d07484a2000d0030000b0215038000d0707000c002110020f404158001d118034081d541070203040c00d044680840f5000f00b810002d0400c8261300030701034404020307046c1c017003142c03214100001e04100307920100e10420190901c86900c000302007007004001380c041c0c00080c1160700c14801040155070b4401040b040b02c20507200c03540b65510410000700c0c0380a4074201c0c5900f01c20280074640b00140305a0303c1d400103a869810855440300414040007031400d00d40500ba4191025001030241c2d890203818500704814010300c000001112141c0d000074050007980201d22400001d00000e01d80842202250310035801f03400c0da1021849148001140a48040141c901607165980030f01103001ea107880898 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 654688758 1250 654687508 654687511
    0x30330010311041802090c040303080f07080708060d020405040302070612060b0f0a090803270f100e010918091208010305030d02181810060219082505100c0e0612 71
    0x55401034191344c0409030741d40e04070061107444905609a039403030641c40e00409030007001c0c00380c1c0760711508481071094031032f08410f03000e070b02c1040b91901c080203903115000158150190350000e50030078a00030034030090507404281c5100f61505a01d41ca0426002c000030304044030320511906491203420302c281500c50580000400505403c0e02c3c0c19000300ea1640d4881d8190391003081f1524845102c4c88800001012080c4464004003086a01c292404655400304442020081d40c1c0c42c02c12115030100b50541e801b40c0d03040009001c030403506081c0355400c640d4920040c48442d40c2514140e1920b005541ca061146a00c1416a68000051400d01c0003c103400c03030180d0401c110746c2415440840004019449607090407001c01062a089081818202410000f00490360054011034020344038407400300d00240741c101d03e096400f0440d6a40c0d041c00d00d1416800e6024039000c85040101d002e2000240319002549100b48601760030b00300001c410605082c0c0f6105c5a00501c10703084201800614091200d446205 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 654690008 1250 654688758 654688781
    0x3080a02070b04320618120a1a0f0c0a0f0309060203070c0615060c02060c03040909080706050c13170a0605011e050301020708161103033001031104 65
    0x119840c68548084641e680c03c5030300000103818010039a804042c0780c100001e9051240d0009420368101018045421031044003404050003400300800c81e1151590404020354a802e41c0030740341c2100180c902070b0010340c03868504a698245403008185e1030b1317003450516400740703081007819450441003060030307201074041480c04800d140d40c912500c0c021030102d000441c4114420b80d80e0340c0742d500300c0d4a003207070444001d00c91a5071038620007841803248907001901400b4558048420710b07165030350a20220319510035a04140546400d2080b070108000f080740107802c0661082c2c0d414481503aa51012025034040c03031401005007801d0341003c01500480c14240e10415510b04103448400c1c0c441e0701c0f14000d0b517000f80c0c484600c036640d112100c201d0203010070440e009440102c000754036020350398a458a460182c075290514a8001c02000070800c140c503074000e0603248000d029a5100d04840b8024040c5c010312140b1428640a5042004400100c0d840f02d241a2a4041030074442882c118003408001d0101c127140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 654691258 1250 654690008 654690013
    0x1803081305010516020105150303041202060412060504030f02060708072006090c040c030905100203190603080d24261e07230405040602070615170708030403080a02 72
    0x80c0210724280600c1d4800e00c0102070000d4101d0346543d0090840360b0051442c03ca148207610510f813a940c2c0031044a044503e0706142c004114918000900b4922696110822507549d40300e1281c2080810342102e44510f0113600d401ca040c82c040c1c6410707a100d440448088000070094000510000d0007038582c81d00e0280d0300da5801822140810701946005000e07038400400d0f40c0103020300710341352400d030043c104860f640e0325080c0000b01860f581d0f10f6031400d01020102c00c09801000040c0c158074603129030790b9051000302c0d00740281d664034140403c0a5214040c280340d441e0034407044000200a40030b81032548048002c1c541d034440d142c81c2d494040c0808407040c10040c0c5121640481d4001010040404401252150745922030031320302d5501e18001407541f00343d400c480d44221500d0480010030301e010440d00b080e03031301185950321841d0284c0281301f00b481c003c218600c0c009503e03403007440552007070003601e50015000c290a24600ca0440e03a50401d48507201090f4001c000c140002102b00000d00080b0314103004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 654692508 1250 654691258 654691291
    0xe15010e060103330e090304140607050f1c0314060d14010209120c09160503041b090204090203180708250803070b041505130201050a020a060f06050112180308 70
    0x104c151100a044070301103481880b101040c4104102c1c090380c5500300d8060b2009500d443d143c0380156070702402520080e84600000300b24003060210a0184951000b0443c040d00d40040d401003115003c582c44801160000e417070109031030410086c50618a0007604024414038200e030503683c86201040c0c03940c40342c1c5c1c01550244409035813070705e43c010b225040720b040401514603007a401080c42000300004200405415102c1da1703007042c4075000000c498001d900050b4040d01050540000808203110758052a00c062000400185c00121540a0342c085c0410a180d100c907040c03103134046030ba45c0c0c00341e015090403508440f0050140c00c1821469000380c043c004c03c64414107a60f036040d181581c0046030180d03130305c0d40315104020400418510701004011410400c2040c1d0410b07054402e125000305000038140080060172400c03841c000c00c4550b003056407061080c0028060108400013418403841500d0205040080c0e021849059000703224038000390500807045400e00d920100c1d040c50010b800c03202c00751100341 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 654693758 1250 654692508 654692561
    0x10090b0a0207031103010203100e070c150b01020f0c010815030a0803090609100c120e16140102010f05060d0f210c0c08160e06040e030c010e15010e060103 68
    0x8000d45184680c98002d00640c0c0c0c518101100168007000c03100b84240d00c1002040252003036885c908095843d03444a135000d540d80c01405440509200201401075480344201144c0d01c0002d4102d03220001c000e034250b07802218400082546d4034115000f4038041404040090300c0d0002d41480c641e00c81c40700808444550703000d13465081f2035030300a540c05101900402c0c1000124003007042010581603000c1420405600744000051140e1225405030f0b0381252980c000c4290844c2c100175114180004200e00d54020f80c3c0e038841c400c00750301c41100e014095401c1c4a03094282007000d202d454400c01c800342074031003001440e50b601010f280c00c2c00011500e080702c11085124800050407032032849001c584031a034882409040c070900007250b980c490001a80710061251a60b400712401c241255a01e91b00c0142c03545030040020040c1a4009401c0610b100c0801c1c0c0d01c52041c015005010000100c0c030039180c218542016240c135201e424010b22aa08000502044007548640e00c02e0b8446802e800c0394010310007902 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 654695008 1250 654693758 654693779
    0x160f140d0f060f05040e0f0d120f1e0c1107092007030810090207080d09032312091c080406020405090c09010e01030b24070c1e05030c0a051009 63
    0x70f40040c03070f92289a00090185003045d1080102c155004d038020701003401d112180b06d949050110304102000031000070200740034101c1c0c005d0728182d40200000e001c611140b184220350031141e60715021441d0704212080c0030684c01201c0e5590340c00c020345c010b4541c0c02e0514414402501d03250038002c4450810516008810590002500581e80b00740d0700d8403030701c0c01c01c01d60309170250f0240d400c81e981081c410042003000404020072a1352401c410a00400d4a2807c2d00342030310200c00c0300c6c1e01100d4010012004004480b00000204190b03c0700d140102801d441d2595900c1d42d981c1c00180044001c00c03000d1756414002d011f58030b06a4440d2203000c0161030a03480f00e012402d00001030301c4421001c800814042c00071340e08204840412082864200150001c0c1000100400c0c3c07007c000d0342892100c80301010407141440216400b094200a108020640d00d42d0000340341c500340320381e40041402e40320000c1580d103004100b429400303900820281805042a04006450b2509140b0302d00b8425105000252070200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 654696258 1250 654695008 654695021
    0x24050a05160f3e10060e240a0b0412230a0803041e0c0e0a090c140a030b07020f0618070303050d15030c14040509071401110f06160f140d0f 61
    0x62001400c0003504524100303045d100300750041500300e40c0380d0040041e003098901000003c202d01d07845942c200c02c0c2c600e010404070a4580c104101d07040c400200030405500ca4448040350901c514524280da803131030a00b40300f41300514000d01d0501d40141c81040040703160840038582180c02140f0080c6040f01c00c0382d0340d0300c10264014003110440081202013105140c0103002075844020f1403000e10041d4155603500c035140c90a4000c554a6072494002d8010940300c000c0d1340b402842c4c4c480809072560605620207136991030522001d0980348940e1002030460150303280442c2031100c203180240000d80c2190f6050f15036070000300c80103004030750783c0ca040aa1074000760b025100440c0144516441903003800000d2000b0041c0e000c045009a040a090110000001407410215809a1070340694000e515004840d1329035145000342213480b49101c40303400c4000200c0d901740550b0f0b4034030035074289401d141410766070310050000647c0401e450725000501c5906a10003020107101c5003d0004c6c0e149450b244d078208581e107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 654697508 1250 654696258 654696377
    0x3030a021c0c08041703060102070501030e0709090c09110403081c3206010207050d1b0e0a0506130b01050901030b0f041509150305030724050a05160f 66
    0x1000c1c0310a03c809464204200c007600380c85c452841c50003500103036403001c4506c9400d040540d01c00b1201c0800105015200103025140801c6c0900b528609002c2041e290500842c030000f46050b0249c049000503408450440354046810750a0000c800081e0018561041e03002d16034580f660b4441c48000340d646000050710740d92203030500e1036070380c103150012542c200240958103552080760300340072590b10918480c0320b042d4403040112034440300c401011074103440d65021511001088061007101001904028490300c42070f1004000d8001609800003941d8540c40d03d140802d2040220801e554400d820034061801c01425950700c1035003c9010800302c46003074100304800e004514007840200124080d41c281c44016569810069003182c40c1c0b1910b9219100c0c00030800511300e060040324130306540345290b181c01441d44c01c02441c40c00540710340150004841c42d4800682000c402081c10b4000c40b0490384c900c0c0c7e0f1750759100e521603000c4604140150f0701c000c588000d000355503e4860030b040131500803d078402c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 654698758 1250 654697508 654697517
    0x14130c02061005040b0a03230a03091706040c1202031e0f060108151f080307080d0b0d050d0c11042c01020c03090d06020c061501110a0503030a021c0c 66
    0xb400c1107818596000341d030000c9114a0500160b403501d45c0d00e15081e0340c16a0f070004010070352000340c0204500c07000341207820304071076001c0c000c030400a064201c0c190001322040d000500a01900c0b04080c907868410850b402800b000c520b183c141310701514000b0380300c4000d1018040307c034583d400d4030004010080401c0384c90b4050744450404080441c040c0b0465004007081f100404403030100302c0b4286c000307400040011110500900d02c0300c41c080c02c00f1800300e00428621040c0c1b90340706114202440c242d030003c2841c0f00c2190500c2041081030901a5001219070b030840045d01741600130242c1280c2983e1030010503140e144112034500c0700e960b5581b15031256002002030b42d10b0004c202e145c9021143c903840c0d2411130280d1050041c0305045034040110b4016400c100d440c1d450940d020b10701700c00203001b10000c11540d0b10455080180406c04074562501025091301c880310b0520b4107005141d600e83d1800c200800b140c100b4408195840ba10f50042c25004980e114a0740c400c040030007200d000ca0300c080c20110b0024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 654700008 1250 654698758 654698761
    0x30c060e01050a0614030601050d080309190f1e111905060d0b03010b0114090f060c0109050c030f03041202130b060f030106030b0f0d0201111f02030402030c0405060a14130c0206 78
    0x9580c8841045c918106030054005c56142c4400204079100c00c40b000b074049800000018511117050081c0b0408103051404108403045608100c00c140100340800c480c00002a260b1407280aa00c00c0d00c682015400001c070300c84e282c046400d0080e02411010540701c6a04a41130204180d0b4929010b04655400071900041c031900d600101402c0d1405c00c400641481661400900c000c81042c0440742c2244c8181c0d064142c0803000c030003049a6115100160015501e000e140000300034010441c80620401141203480104054059a444c0e209034400d016500d4a952100001420821310b518426400c050000824040d4400840c02e264403008100d061280e00000611125400d845a0b40940d4000d4480d95180170020f40401c901128400703019040c00120410b00180c9170f002c01c03030503c490050702d00340c40c0e05405429000001e5001079808900c03d0044034000440c50806100c0c00e445804010078154409151030042c0caa00e40324410002c0c0c0003c1705502207100320704140205841c81985078028102c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 654701258 1250 654700008 654700019
    0x91211011d16050a06080a02090d12031a0a180506030120041a03010b090d060b1009080f01051611010908041412060c030a0c090312090303090602010e0a030c060e01050a06 75
    0xc02c0b0302c1d8100501c51200600103200407540035840742c3d400310760348400507030b5451030400242c00d050406d40002c046c99a01e100d8095015070540000500306403e000482107100d40b1820440014090300840c07141d401120151b41140c80d20383c100c0b03500301c40040c000050781e011318104202070ae0680c03400101d4841c00010304003d4600c541c80b1842405070803282240c1154106500070545220318540f40f88286801241d0909100041e07000c0302080e00010100200007240001c044d00c0e880c00d038407401210380217000710384407030003018095a40b0079070398101107104034144803009891315503c0c01d030644403540d130b10900c8800203000c0d040280b0240410f404c3c50000c3c540070408002c40118041000b0710341d500305206004071407c10700141d9401014040000c11483c40d803013003c4802251560003d410410082c0c0403540043d00003080e00103481c000d030b0342c0111840c0c070f801c4d09909980381d1005030019a80410030345004a4400c0703950300c3d00644511004144011004410383c01d407078040d6561a4615070360b0104008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 654702508 1250 654701258 654701293
    0x8031003050706091406030703020912010f0f05040221030f040303080612010e0d05031b12090613050a020d142a100e0d1a040302031309091211011d 65
    0x14900f92a1071142c10341405000c02d1000585484140107880100100d400c090194056070b0210b40050801e141251440900034049e023640f6441c100b180b8600003405e540c0380d40502a051245402911503041e00100c130640202c1c03881980c4400d40203000521a00340c1903540f4100900081d801ba54a00c111800c044042207000c54500c884c60300c00ba0b240030a10030b0002c001142c1c0c0c40b030b548250b04001d5240e607501a0986015040200003410341c0000041c046c0d013849041c10b541d8010807110084410310f030380d80ca80c84140740c6410513000d041d0340c0c05921800c00619140010940d0f01e84a980c80144c2c1c914850310b810706e0400f41c0b02005031090300402c60440c00140550041c89400011144800c00310844800500140005007405006981090740c440902128800c00c0d021030036a49000401d40c43d280c00c000752260410030b80c00403c0c0802c00c3c00002c544800e07004240c680740c0c02c0500c09070580076656080d1800080d034100c3d03000e507540300c10068801d1302220600c00182000b01018041c0c1130b003144411403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 654703758 1250 654702508 654702523
    0xf050105060111251205060a0b0a0f090b03030d090302060601020606040203070f0815030a05030a03230711210a021c1421042a230406030803100305 65
    0x6040105040900c0c090342c0c800942a8046141c4c0e055000340c0c5602071504180840041c0c111801004c180b4084c441040030004040b441070034032200800c00001070751b0401c9a161400e11031501100c9500c5801c2c0261071540e0300c42c40310050000c1c11245003048201c40c5034140c581c00141030f405038100d5402c107c000e5806000c0d01c0c2e8411000c4408514602e001c503000740010b0040310f848001c00c42c20b60006500c0510041040c601102d00504442004409260080d5284d01c83d041c010300090031301c00003481e40160255803c5072000ba44100c20301d5030b80d420904580711041401914814894800e81c00b0030604181c032502c81003400740002c9607645500383c401030b182001606480200c412000c6420302001e034820803090b403d0200001003992603941550110b00d0006480361384070010455410300c010400d0500d078444220005650041100ea007910340700560305041d00c5060a6a14603604200a018200c60030044d0b2040c002d100003502c5440c0c1e00e40c00c4150300200c0c1c8007582c41821003024404d0080800001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 654705008 1250 654703758 654703771
    0x6030d0309021315180617030f03062205010602030c010b0f030a030e0d0501050705190810061b0506160305090613031d030f0106050405091b0603220f050105 69
    0x1808880e1071640469440d680d0f0300a8000c1080d560340a044150a00c1402003008001680c803020303088000214580042215104025250500b036200544c503450200685110442e103524850865540c60288042c5910303041c41203d000410b0f05100d031600c032062050f0f5029204550040da2101e8901a6181c21290450b10562050088102501c0709540006214203010785c145449203461890101040514411050050895080c2010800041c2e80807000d041050100340010040f0407641c08290744451090701c1c5221407150b0400c081c0501406407a0071400000f04c0000850f055003c1e4540500300a0103071043e030b09052041c0105044140d25004607608880706201802c40d5040040300d2030f0300c1c0300001c9002001e2040070b08071000ca01c9541c940390a002c18010b0180e5030002040800303d07000f0b140302d008452260b450040070540d5054002141c1c118202c0003120340b9002078220042196540005049442e0518040ca04413042c4e50a80c140009051043c03101219900e4246806425160014484c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 654706258 1250 654705008 654705011
    0x61603030c0f030b0d11030102190f0e0d030203031b21010f1d070c05010f06080c03100c0903030c020f0a12050f1b040902040603050712030306150e060c0316080306030d03 75
    0x4444d46941c460380d1012000e80e0103141180784405440109019000e01c00004211480b10041c0c45000da400020f00e03e0741211f55034550351000641d00800910700710003038010340140e0050000400c50701c102d09801c0c26101c41c61582604111031034404140400c8403900706107007001c001004000d50344000a0b807102400f6801c2c1503030220644078050241603140103029204200c01290301400f400000e41c00204d10103480c800500201d502c600c00141c6d9209851190741c06807040c8241038480c001140703c2c060400b4020740d101c100c41c074555241182c2ca0208043c0a030783c010035420780d004080d59410704a50050030108010f400f01c90160400700d05040e00c00d905182c050301308503000d03030448001903044200e10303104560025111240e800880c00414a54000070403520617003002145aa101072140c41c401d6100e03950a2001507103401c0409646a00103121b0000700b051014404844d03e005c0010301411090b0204032410088200f0001c4003445081201303454180b0300000b40402800d052000c2d0716043c4a40c1030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 654707508 1250 654706258 654706271
    0xf07180f090b0d0819030b040c0905031603020120010f05010602012403020a0302090a020c0105010311040608070b0307032f180d03120b06120c0d0c08010e15061603030c0f03 76
    0x582c0c00140c440e0f50031500704143e82d18140345c60f0502035404400910070140c400c024030810040c0140c40d281076801050300c244200e800e81c0340200c41c448100015680c0c182d4440c4d00c4c000e001b29902c5002c14900007500303080d540300c122a20391492180f26203402440c6550001c206c024161a820340030303104d0f00c094000030740c014820610241e1200034015003182d9042d140e185081d9035a01c800320003805100e45482003542031a00000600105100ca04142d000480d020040303903544040995440c0b0701407180c0c90b041c00c8248005041e50703020b64410069a50415005034200030343c40c160795504010111041403440000c220882d502c0b54042450601410550f80c0f0391141d202c0d41c401900c0515048808001c031600e03000c444030982c45550988103031501d003e8210406040c55003a144190f0006581014074a02d0018407500a03841381c031200d4102ea00d60403445800f07468a4010740d020108014405070080300c200441018014404101030385140603a80005000c80f882900501e003607451565801054103001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 654708758 1250 654707508 654707513
    0x5010905011a1021020d0507020c013509010b0d1218050f1005040b120415020304020d11011e02011a03071409060307030605040c0305010605090f0f07180f090b0d 71
    0x80f61525440302c4608113860304481c10704000068440c100c01d40003000d05100500c424aa0000342c00d0030003040c00d8a60550f840c4012488a0035800e0305080c5a4001c409081d85206500f0307840c00e030702d420050140011641003615004140c9400c04200203c031100156610164203913480012420001440b840304009540f030200061510500d8004561050a10798020301c0503038090800c07035008084c20601c2c2d940b00c4404101c900b40c030392812102564002400c10355114210028400c4a1080d0b60080140055443c1507c859001102c21103542d0706000700070b0035480e103070071240c1011441040c00754004507040e440da11244203000c04d017400540c040c0d40030300018003c0b401040c01e24400d0070410349041d0759642d03e10002a00d403100f00d42c0058042803a00f0b0902090010540d0031030142d80c020700007070148950724002d100f483e503401c80d85c50580c1110003000c07607400f081007400203070003007414600100303120b08103900c80d10b4902c2960b003c0012003107045000c11802102e40540c2e0b01d081c6040390005c2c0d1042c0e20380c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 654710008 1250 654708758 654708767
    0x60f010303090e10030c180b040b010c080c01020c030712020f01050f01090c0e06040f1a041d040f300528020f1519180204050c0705010905011a10 64
    0x9015400244200000040303003648075455410045400004d26441d950340c1d000c54180e20042c1040340c1081c64180070022341a401d05020381264030350180d403212004c00300c5485d910343e507070000d401810b01c0d55020041504072100c1003014200090280e46040841402d850b8080c1c03511000003085151130b410102080710849520800a045507911540807860b03050420b0304a8190403803010303066200401050224603400c0e90b1604005403500324071101312030032a40184c3d41103401135200d02d00e113010540780c000d8002c4c007404540d140c000344903034400061401d103540e5140c4940c2d18241185045e0f094215030040740700c46401c44400c0420a410600e19200b40c0c00b8596000d80c40c40e00482601001c0200e0f5020000d2013001003101410580003603440e182c040d10a10b0000c5001640c08605900101c1c183c0041581c0c4e5116042c0b02a41c01c1140180c103003095800c1c440900070040401314400010700400010400a0041354070407841398000144000d207402907a041515145a0039004d141c00c01209101d85410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 654711258 1250 654710008 654710027
    0x6030607080703050c09090f2e032303030f06030c04020405060706020c0f100c0e060a020a02010c0203160f0305071203090e040f0804081005060103021620150c060f010303 75
    0x110f20300072444c0e035116954110346200d407030185074221541d8010801000100c082c920302030618001520700782168100d0070722400d046501000b1038210190403c00001d00c4852000ba0755420040388070754840c44442645046030000c41d055000030602500304005480c05015018030100100c0e8118101814540810100e00501c50003c03c0f039a0300007000c0141100c100200c2484000c4541295110000f1005106c0075154814112000c520200c8840815240c00720540b24040c03020341c01440c40c1740040d001150203008507071060742c150040380c050340086510665200d000d88080c50401044900e03610305245002c84540c081c1c04108480c5502200196020081c04211917080c050b800058032682401d462007414984010080300c1c0c00030300000c1302c501c04566a2007010345000c04221680d1502e0064050744207601004d11100074000c000000110815010300c8403201e200c8034403401c49030900204d100b0058034022941c0e0640007203443c0390350700301c00c00c401540030302e408c060300c10300754956600034001140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 654712508 1250 654711258 654711271
    0x30a03060e07121a0d03051b06070f23270604030206070b15040f091e410304080601060c0f030f03092f01031505010809030c0f010c03050603060708 65
    0x12030f04130103407503490b0b50600c040e80003500070407954404819160240c995804125061340040f00d0030720450320441c0c0842d410b40b05601c00d40b036919260b0320307100c4212066200c48040d140301b00340362240200381c1c400c402e025002d0003803005076180f108524070300307409080d201c1c0e5406588500301c1004140300584072001500c3c00c1c29403120000300a43c95043c1c040c22024040b041880d00301c1c0ca0060000d130b8192082c0c00400300c150046800302201c0c03080382d09070310840148030b0014112030b20407640600b02080d018810201880304902d030240c8000cad03c88550120030200d00e0744042580c070120307080c8601e103001d014450044c451b6040088400d02103649503a00b420b45841c0280a00203881d001c000583c0c002d4022a90f001e40c440c9018039004021021880b04128041c21100205256400389403c0d500a11902009400800b01e5040c9a031410b00111120880104040042d01081c400c070f20040504000715101c0c02c041c6000400d2080c00500d00504596009042d24869071102e81444000d54100758225007002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 654713758 1250 654712508 654712511
    0x8120a03020a09120c0e130b0f1302060c01020703140a0e09060607082206030c0503010e07050c15090d0516030806010e03101d01050601020601120f0c08030a03060e0712 74
    0x209000d0305950b103d100798007081004101c1100b9004111020800f40c0c241c0f14800c0c2001d6a40d243d80c41160107045a03000001d010f03c800314080b801c40408450460390103d5602c1880310011102d6000ca201d40d00110b07464100361303401082c500c0405411412154511391081101402c04040d0340c00208000494014580244100b8010030405d0b12184101d40c1d069412103c601d6683d0010a010b0600e480902103200b0200714104010a516100c0c2c0210f030500e41c41941c4907070459003407400259501c2d40107842c074000d2000c10029004098000e215110102e01d40d040080900d01d000d030641420603404616050402008010410040b10840c049500709030b01480e00109560740d102c0103a45455010480d640d0500c070700600080d0032901600001448502d9000fa83c0190b58640201c90990328255003040c0981c0100c4014002c48100104999003580544650f01201f80c664440300307c81030b0a13130411149600001624986250540030b42c10040602075401e00c4585040c1400030161800360a840c407025 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 654715008 1250 654713758 654713767
    0xc03020316110307150b060c0f010c05040506120907080a050615090f07050a0201111305040f0e03090904031b0b010e090a030f030c03110a050a1b0206040621110903010608120a0302 79
    0x21017140c1d1000c1d118450240080f90348200c0059402e66a04403013054050030340c00d01881a50340c0344128107070350444901518140c180030074503146c0307450700c2c1c401490607003507208100f400904260200a00c5050600070400f9080d0ba0405200c4030504100c1071401c00c1c081c444100504c00120301c6a551a51f00c120140f61950301da80300780700128007421955242800709107020488000c0100c0030350320201100e60446007001204074900012080e144e050f201c00c150f5030800c0c442441d090400c0c80030f099000e4800d03e00744021200608860385000d00782001175480001900c018407180c0107400b240c90b00800c0b03c400500b101445564000c01b92818081c0c000100b41e100d01d02c0d943c00c64041e13000085018604900d0700e8840441c1103004150380c10407480c030400108100c100d900000084441d00180070f8019144501c0c01d41440e109554030b11841314000120181d09c1091081e5580c98810001040c610395482642c540d80d50041500b0f641c481e40200005400c10118079900d0340c070460898800350103909015071103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 654716258 1250 654715008 654715043
    0x1209150207062a14030a031a03030405060906040b1c0c0201090b0a0e0c0405041a07050a0c080708070609151a0a1e03051f1107020f01030b0f040c03020316110307 71
    0x441c2c0e18000003061441d80c104004c07000764011014020400340341d60100309501d2143c41459424813240d4007503415030010002400903041c444010f001000000d002240b400d6921092150b05a00c000704505483c074050b4090005803c41c0d0081451640051000f800180c00503242c0c041e1001001d08141d02d02580d80032070600c4a50184804101e28000a104000303500d0141000031140503001d02d07958101b1040c0c0c0000d5081402882641d0890a4554402880110725500e000e02680a1a0140c8480c034042c04000000b411901907035400510500c0700301010b109003081042614203084000c81c00101140b01c161298070703003064080c22a59070b0406803055030b40c050901d44410056803c060994010030210200c2048840381d242e201c0b890303036072041045a1060130500c12501603444001e5014213207120b503011541c800d0308401c070202001040080c103041a017001904a9590100100110b1380100030021944581e448142d00c0c00c0146c00c02444845054072415200e2040d0301008200b0404e80452a05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 654717508 1250 654716258 654716327
    0x30609150301020a030605040606020d0f140d0f020a0206180312041a041202070906060f0e0414010f0513180f060f112701050904090609120915020706 66
    0x5920340c041c00031566010411801005480340f070140c01d000d2401d0034030004040d840065400034250305941e0305204200242003c40c1c201041c10007500c00d502043c0200300740d00070244a00302282490a20040e910b031941d00c03000c0d0621100400e448155030000d07031142c200c3c1401000710b0306024120108440d407035039280303000c0300641e1625120f8140380040f40c3c2000200070000c030000d03102a8980e000c0302c45803a2790310b00f84410b45000380161400100c0008070b94030807071301a108880340c42000900110b07240562100031000c43c1c00907481001e02e10704041c000c010038104500e001e04080c0202100b031107041c090820f9410318103440d210003089121004400d00034000b295011102c894080f40c000d216568042118041c1d0f50040072038800e1340900c814100304034400c0440c01b680b0010042c1c41d010300788240c1900f000001c01510b4001e83d40c650303c4074021000906150350844032860103846220003141000e0b841041002c4a14a40066500c00d181c00d11016400001c04100c0c4643ca03840b0040c40c15250007041c9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 654718758 1250 654717508 654717541
    0x6060415031107240504020d021507141b03191b031b05011704050706120f15090605091b03100b0a020a1103070317180904030203090f060a05030609 65
    0x5002e40c0e004180c40003005401e041e03400c5861442100b00c0c4203c100b80d800402142c2e81646c000754404003d03980b000040c01c00c1101c050803204040841420200380381c0b11201c624a1500d1603000d84c0c1c0242c401060034402c15160238109080aa0042184d95503489803c212075400c1c0002400700707081200030328520400c0091908c0a10750003c1c8403000880003809907502000b0f2409180e000c10140c1c0440301d000300300c1404c0c0074031494104c402422000d10b426801d5031107003a04240c80c0007181e1075480ca09888140390007000b954041180601600c141b40480c41d004907010fa400c0648101040404e01c41c188107818101c2c40c5613454940800c0d580e8540d0b90341c0e2841c4500c20792281048500100365041c0791600450801e02da14090400a1254880501095107400d0103020040840d41c00070204030003060907070003a152001c440d5064400c2d1b4110700d80002c40c01a821242100180c0c0000340c0a411801c000c0407031001d0010a5948a09000300480090714500000f440350f4000d40c00b42002940000c2488540c0c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 654720008 1250 654718758 654718781
    0x8030f060a080318010314060916030f02040e04050d30021207020102071a3106050412030e120f07032102040f0b07051c090b030a050403030b090606041503 68
    0x281d0782d03202043d41350441c14020521244c00306e4078050103000528200c40100e442034000522102035651825403481c0d40d4074411007600c1c2007603501c003640400c070000ca10080001d441029482d2030710389498a4914a42040b01c070300c01c41040107200b14080701741d510107103c80c0c0180c072038003240c08407041d0311103190300030b00494410701100b02c5014140300003250190700030710701d442c0a04654070740783c03450b111038444083c000e490324046001c4958038220350000360113101c1142e100708035000c44014120b07128081611019201640c906a8044c044602d80d5050b00c50610843d0340400600403010282d405000580294405036512482c0016410100f510a0740801c406009000701024200e05961092000b900940a4210110703032000003c560100c45005a84d481907000000304402c5c4070013070440503203403003441f041010300290300ba004c215205110003444c03081c001000300180070b01c0d0034100101590014581c030740c040c5444c1424081282c40e0309040340d0583d2420300311220096681c01d0114010700181d00e15 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 654721258 1250 654720008 654720013
    0xa02090c0421030e0607060603060911010f17060d240b010e0d02130b0613081501060e0a06030c17130201080916120303090f0620040308030f060a08 65
    0x10031180c0d400c0030015105a070711a44030703640030380d41c10100c00781c1c4102950300140c00318040859900540c9400001403100384e1140b14003103002690307031341c401094460401040b43e41010030126071080e9640f0040041d20251585051108800c0400c081101d51b0b4018207018061480144c00000380321003682d1050103c0c3c4840c1004050968211004006010550415000982a0003402410b20f00300224070049078004005032440025a20454000d002105a144d084501401002d03902034a94603468010034801c006011030035030b4180c440c488014160040320511081c1806580c860701c2e6441046e05035451400c000412800b003a20940b03100800c280d282800e800e55404002c00d08110151000c004c5100ba00c0301040c1da12103100098444600803401031500301c03030000810011b0842e5440b03816150003400c00082c00340081e01d83c0d070003445080c10155071072900d880b5040c0c0280300807040c54050b003601000d01c0381000d0a603174a0004a10000e88031040c00c00076840425110382e5441960801010380c1d104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 654722508 1250 654721258 654721261
    0x10b03041214120132120c03100605040612051c0203040906030f140102460804020315091f0b18091c09090207060b040e0312011203080f07020a0209 65
    0x1010704507403d09010304030001c9001c031202c01c03058181c5030210107000310341d081e884404c1c08640c0c288103c80d019119007000074405e0520380b41c016203041c001024042c0340e00c1c03800b11f81a030410b4180320684a160344141c104911148140000c510302265000481041046a1004481082040f8690f0042d40c00c800382042c5410340c00030801c256103e0020001d84280018841c050030405003908034000d024110300d1948002805c4030704090b01e8600c091460781021010805e0120340c009109842d4200b00c41c010110f070a000503c001c1d442c003041040c052820142d407100c840d291415280f5114580340d0780702401458094075440401101d40c12101e545070010b07080c6001c441180c1c0c0802240c50060b0f80e04400340c06014101400c01c4410300b1000e4242103192200304500340342c104010300950054500303031401a91076010b0007803951280600c0d0700400109006584806000440c078a6640041c1c1c4513503040c580b800d08240010b500300030300903071050141e280d100b066075a141c4180d050460140000b54491000750 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 654723758 1250 654722508 654722527
    0x103060905010902250b190f02040e01081608030405010e030f01020a03230c0f220810060602031c0c121104060e093102041e050708010b03041214 64
    0x501030545035140134610301030b40c0103980c100301008545500203410706c07102100148624015440d1203000c2c60828800007011080360480d04100c0e001504400520010302d40108003a10041202c4031001c0d4480c40000f074800e16040086540c0d210b80c1c0304450601c5030803001585e4a43c0c09202d0600380001500c02590b5400e02c2c00340080040061340b07010500d24600c1c4c10000e2052610441c89841040b001c10310903d000f5004000c400c0c107400080b000700643d44100c0c4c200d40c500341c3d404c2d0740c28002c2c00904000c03d14170400000020640c2c01c0382c2c010f10210752040c0058044280344180740d0441902c60000003401103a5034000b03c1e810303070380e807921a2034136410003001100c4000e0010040c1304407809540c070321055120305000c10424003c140c40180001e100550310b00c900104164103810030000c1c10008400040705070b4080340c00d0796600713180a0240035820b22380c0911010140600e42d440001881c1c80701041d81040294003050001601c068141081d50001254107400380701100780c008a20001c5c20344494a50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 654725008 1250 654723758 654723761
    0x6040e04060c09120b011211180105150f040306150503030a050d060b0c1c1803050601180c140f040b040b030610111e0717030c060907060e060901030609050109 70
    0x50000004444040c0091381c1c000000301d0301c0b203443e4049400807043e460594480058400c0c00c1d800d0f2202d0311500c40c00031440e075524890030800130500190b202c90350301d800100100600f0300010201c245030100030790340000d00402d044074250b81d40305000050903401f030008017505880300e410894040c48009001d4000c0b0360804042c00c00390381d080c542400200d0711420070043c540104104650180d104248503190400700e0620702c48407900901e010190b0350f00c50100d41403860056170082d1a250041c60040c0403081c002607824003211981c0401b407280496180c030003400d811401044003e4507c003c01d0050b0b4052481007213500520b22609841d41307550f120390030302c90940d0051343d146100d80d03290014100302c00e0040c00024404c203081c0d40a0302d44030115411954122801692424241c09101c40201d9400c280018100c2c510001000842d01c464003460302c6490100c0180407003140d03501c00c6004101c029400804513049081c1600d03000c0e1503202d1540160302810b207541082840c5803c0000204514515 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 654726258 1250 654725008 654725021
    0x21608030c0417060a0c0f09120510110703020c0a0e1812070305220f0b0c010f020a050c070b12040809040b030d030c02010606030b0a0b0901110a241a01030b06040e0406 74
    0x13240000c2207801e00b1b030300341a10282030615081011520b010b900f000f680c0c8111400030b440c0ca0080c0c055840c0c800f402e030024000c1320ba5a07071aa6040c5000420200d082c107504000076443d04100303403080506c4509103845c00e4445034004000d191094500511503a80d0303070303044c071101003414092410113071200141e10340074280340c00c1024615140b14031a076075000960802891402103642905940c0001403c001c1d808540d603100d42031088a03903490380805240c1e800c6a1005002c444002c1c2d446540343c543c0c007603c20381010750f0780d03011910541e010b100e030140035500c41f004143c203e0303072103042d2583d106c10381000b14001d8415020819418042d07920786c42461900b68019101c43d5010758000c020113500da0a0550889040384d1207150040c09907001407000108040052600700c0c01410000341c0032094480705850030306d1411003207894104800014020101911001d2120b05c0642c0b400e200d054035036100c1220120503150104e0405484181010850f11044116405404a121103240c245028246040075103030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 654727508 1250 654726258 654726271
    0x80a1101090c230d023c0f010503040510020a0c0f0c0f080f1b190b07290f060f04110915040608071215031103060a021608030c041706 59
    0x1081c2d0400300d4281400365203ea491500140318100d8010b0b01e40a100501e9410100d1100e4940f0401c581d03208a00e5100f04403000e070b80703880c813a80e03820900482401610b00f030b080b1100b03043c02800c1c024000040d0000c921480701c0b110109005844400d80b607000c603001540c0c00e0002d0030804902c010103060003058440b00c4165400c0215194041da5146070307041e580c000e5402c0c69001a000700200c10040042e48031504800d22001300b40d5003940e45d030881c8981c03481e07903950310035100044001500010400e000091003007000054008050210710034a08070308800004000300162001c040005d10140d40d01540c88c81702d11030161080101c486400080603040d4450f03c10544540c40343c4030003825840c1304204a400740d407015603400700c05407510a000d89000343c5d000802c500c5252142c0340d440c1054076405607000114065003980d07001c2900501850f05000b4041c062051080c01002aa144510000d00019039107600002803690303641c42c0e2044400d00c0c00f540d00034250452803480c03000c88500c40000e8940c0941c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 654728758 1250 654727508 654727529
    0xa050d0b1008190201081005091303140301050d0f050a05030a030f0509070b0406180b0d0515120c060c030903070f03031701082a1909110c0a080a1101090c 68
    0x1512aa202c0707039241c2800c2c0c00d076020701d6000690380e80154425034444d500682e1060050021a40324000070341d110000301c803a11069000b880325a0141540301801074240500341601c2461941088041038985607001c0010b0140c000d929042000c100707080105a1100d41c0017001d603a00c0720b507000c03c010060500e2104600c1d1403030400000c1080c90102141c074504072100240200c1c03501e494044182c90b0b00c01e001c0d08440304101c0d4210002000400d02004005001240900083c03610340003d5078031110001c20311090090030108103020340000c00040b5a48079846c1113072610b07220044409120300d10300c44d40b8817168050082c0c0c1000104841c1d1102d80405507880780c1c99054405a542080f40c0c914071003446000156800300c8509003e40c40810644507641c41180c8440c141e00d1189000f1440016200324004908144e601c001c005801c21881210340b101c854a107203070f141c0100d520b03c3c40d98a03e010000581107003000200388240b00e001c2c140c1155400c1002c8001c1c40b08400c2420803189003c11445080c0040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 654730008 1250 654728758 654728791
    0x30309050420120403020f03031e0a150306240b04090506010c0c050d02010521010f060203072402070c0f03020103050a0b210102250210020d050f090a050d0b 69
    0x1e603048070003030b114425012554201a100050142c20180280090f0198020f000c54030001a40c1030005520500c014400390008d030905040180581c070000740450002c4c0d00d00082c50060043c440154400c40341c00c2040400c1c48401c00c0c0000c08100d035501d0000c03500e1005070310002102c10020001e84100c0c2c1d6040000c00a642d103442c0107441c060b24518004041811410b0240320500e003400352820914010f250860402c12910350540154503014881c201e03640c1e0fa1401048640305c1c010750361002c1d0010f8409107084c4140341d680c0020001d1510700041500341c002c0d240601010941d41561a1607030440b0001c040c4a0303961005803900006400280c3c0042d042c100000d41850090003000c101d000080c204c80c1c8400140750822100c0d88517069808070954080020850a2904004080c000e40c07560001150303500641c41001a007480d8030382e4000a54014503c2024840c2d000303401e0fa641611b48000d41681c0719401c8001564201d26604515801236544180a00703104001d90318512501d034a03015002030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 654731258 1250 654730008 654730031
    0x7030c0c03032c01062c0103170f030903070b0108070810020c1006031b09020414040b0d0803090c210304050607050a0b1e090105040203031606090c0303180608090c011b0c0303090504 80
    0x4805035281e03003210f0801d11b200400011300304408916001c045000d205003805420f12039442d19900030340726042c050340049160b03810320005020715401048884024440e0341d241c51112a00c4000480e40d02c100c0b640e005c03604000241d0140314074003801103031b800108012070316443c02c944480c4003c41c10496005c00f00102040c100301c1e40c402c03202520041e0203560482c141c000c04100203040f40ca00559000041c142803400040c98010107076000e16029000341c02c042c03040409000d071101045000089030b008a00308500b10b400080101c2e426640f050760883d6403011a41045464010300c540c00811810103e820070a1711000c0c02c480c0340480ba401a8503084645442011a003618010b03a40690326406c20006905008880106011820b100d1306000c91301c0080e1f17455071001e070103540d0301c15004102c1d40d22070903031f43d1807252244030090062820449401d0400e00141980e8085424209044c0314210b407100683c0303ca56280e1000241e8071601c10903141e6181e280050000301d6521034640502d080150403141d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 654732508 1250 654731258 654731309
    0x14180d12020f010c1e0c1a010611010b060a0f0207121b12050d0305061306080c04150e070c03090306020d0b03010f09110d0219030503090907030c0c03032c0106 70
    0x310341d40130f580c89030840e00300545801e007250300343d22160342400704031001c82001912120858048036811480121f00d1361402c03201504010702c0c220380b1030041c8d140140c1d500b46a5500c034107a805a0000b0311f080b1100c0006a0020780c605291500311101e08884201080204022407941c0c400c14120807106101059881c1805492428400c900500c20303084445a019400e1290b404140c0c0a000203100135101c0494141c00c10441d140c80d000141d40b0342149036006614201405030754103140140c043c0c61881d6240042110780c0c800301500240402c02440900c0f011325100315204800307541c02c010115a00d602c591000001040b010051038000e5003002c1b4201c1c0142d10501c2074412140d000f0b000460000603c004210581c84421030481c0c0c840f4140640c014a0440401f01c0c1c000343d0300c100015a43c0d18006400c01042c04d0004201c0710803d4100000c0e0000164410758005602d03900d403e0205029101c078561028001760100200000781c42240f49a2401d03405400550454000d41106a0a0040343d0110030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 654733758 1250 654732508 654732521
    0x60a060b0307120c030f06030b04060605060712030c050d050a09030807020d020d1107031e06150605121003060e03090a0e0c0a050d0905060109060302031b0114180d12020f01 76
    0x1012485850500c00d005409800c01540341381d0a1400241e2a0002c1a010084a10b41c1d0400da4003800000d08000c200300962280c1d00c09410102c401600300495603a8021184080c00d0400040545804484200c24054020307100d13000c506240c02e021600c1c080d03c2440041c1809a4281c5c0017482d0040810b04560001c01e140c41c0c14061540586a15121444180d1310121100b80740784c154403980f40d002003c512018080100d0358001810391446134003a04042c8241c0d04180381c0044481e045c0c2004104580d00541296041e15450f003903450703581c1d9028104dc078000e0b1280e101030815424580d0000c0142d401000404e40284102c48000d0b065031544100e0041010480ba03241070808104003210006002d04041d0100d10b11001001c00c2402d03541d62143d003040300c20386c4038941e0903841e00300a104510b0280b000241850001c10b04822210100700001d10704500040c0100303000700c0018420040842c1000045100d0401030064241000145860104a00c0b68142d10005001d09a201c0f400b660b01809040c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 654735008 1250 654733758 654733771
    0x40f030e0906130e03041206020a23070b060d0f03030204051908071a0705031818100b2208030c01050f04050727050a14090a03080109090f0f05060a060b03 68
    0x15000c07403103d281d442c00030003404003190b41512052100282c0c1e11910f0084610452144101584440501d031016000c9807540c000030202c070030384454200104510710143c5a501e40c201c4400d0007251240307404101212041d01000e0214a058408035080c181c064006000b03c400a07100d86100039819082c41100417000d00a0740c5e0319410804042120080000c0c944c42c01594407a001d51a00815944e014515400007001d003590550147d1600700b185403901c0107168001e03481040c401c1c685469814001114401e000d02e420f51500880c8008640d06615103411403449a0000e036019251a038600f5980d0b46c01807141c104081d07090500080d1084144494280a60392043c014100e803030600d9000140e00e14082040d124040518501e0300243d42140156401012958400200c082c0299101080d01c030005110207007543c001c280d03001c0000d034001e5040e070464001d10360016a01c1080d2401ca03065404180c0d0142c1540d59010382031003032000c00306172280203500c030b50010804240c2c2d4080c00b00039404105c425 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 654736258 1250 654735008 654735019
    0x70f142701181229090c01050304051504051c030207150c0f03020c0309040c080a0606050315010e0609090103151802150d0e030a0306032a05010f090509040f030e0906 73
    0x1080243c0200c1240c4400901c40d00301050054102c0359512020321100001c00200685201441913682c424443e816500100b0302e0030b04c0c618501038440300e83c2c1e8504100c0c2c007140c0a0307000e40080c3c28454107000c1000b86180100a4900301101101c000703020350802ca80a48031032150b104251401035480c41a41c20882d03054035a801d90303030081c0f0020b400940240c10314687d180001c1161807100d9655110b103020100c541d0311900d9007402c108401e03c003241d815401900911104000340301006590f01861103034540d0919103072580801c1d010205080d4060030703101640000c0008000310030000c2400f0b00d207292079000782041003550040802014040d8041102070b400031041c1040388401461080200040c50800001040390b5421510862469224616503000280e880b038041c4200503032403244030b21001d200030b9220b4145005000c5510200807611a40e81031102d41e207104100c05004080120081800410b03129183c40d1504101114548145044000881d55900b861051426094043c083d40000d8103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 654737508 1250 654736258 654736307
    0x1080402060d0f0f020c010e1605061c0e06060123180607050f060601030b1801150909020a0918090b0402090606090d120e090906070f142701 62
    0x2405641c0d40a00701000c42c1c6034407998000850a00d034010030b600f5050300e0f0700c01a5980092450f42c1e08540d1400c0384d414440e005216080f80b00102c03280d00d07105035132007100c1c0c0d40d94a003100c80070090100c1c45240d840240c141014520b544c5007002061940c4608400c0e00c07000444000b0054103c2041c404005810ba000e9081c014040d0308010400100d03013a8001800c40e038039014081c0c96003171400c4200810200580c0c8030390208540c41d6454020048031410a80d2410807080f01c6108880c00740a05000c1c82e1100068801248042403140f25040000c040c2d003501150744048442005016040314042c1d89804811044101e131121003501c9070350660b6070003040c09a510746841c0c0c200818254040d052a5000c2c1d070074440310030140c0d1041d0055400310b100d0b031681e00e40c0c5606141e0150444202da0b0001c1d10802a080410040d40e02c0819402c4d4445a1407a0034000f040b03882009032012030300b440080d845a0700208407806a0750840c021071460740f4000310320340103032130f023400044480211640001601014020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 654738758 1250 654737508 654737513
    0x10f2c01180e0c03061813030e060405010203030a020309070f120c171e071e0503060f040b0c090103061d10050a180e07030b270604030c230f01020a02010614010804 72
    0x9003e0342c1c03c52001081c01417403600c100601601b4100071380388040f20300031580c89401050b401092009602c10207503412400c161403c00080e4036400004c000702c08058001002071150002171182d0400f800150302c2d800d505589440300d40300480c4541c00304541c018049440400c04511115071590b182c4081c10003032000e03901d42c841c0c500d003100b00038601c0f038140d200e013090104a80d00407101c038914150301103034840c010b1441c0804042c60000090610f0a4034215603040c440412114031710181c0c0202148081e590b11200f880040300105a541c5c0010f8140c1c40d00850140d1000241d6049405072210506410709240c0b28410451000d00078843c0300d0701101070110341e240e510f15640241a0410160050302c0c8255a66240c240c88a00c0032100c0010321803101d800035440c039290b03001a042c9900308200811440c542030303030040e180440d000c42c060031030385600c0b10b2010a00700c130420008040700e081054941c41012500c1c55400703034100e5239510780554204040400d91007000701c14895440d505968000745512a0f4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 654740008 1250 654738758 654738781
    0x301140a0317130b040b0a090e06101d0a06030e0d02010e031c1506030b09090118060e1c1211160611160308010f2102010f2c01180e 58
    0x68903542c96840090f00051140045001c5c0c002015542c0c84140d45039075120b03004026151031f130421500842001c0034888141c8480240c242200107500f406502405c3ca203080c881e1018031505901ea00a09032000401c1459058000155143c1d40804039048140f1038503003a400e031800a16142640d52061003501002c1c4c0070b9a443d0103c00444040008524070322007201c000c5034803160040d8011a80f98250500c441c00c100081a030b02400040003080f000031090710702d08130006002c0000d0300c3c81d500c03203030001c1101005000c02001e1040c6440c50f4810074840090140c100c03010b00407403902c41c40ca40040e882003008020202c94558001c1820681000030640d50300006100301030a00054000503c242e00c01e5503242c09030500da00c4c3c007a444010156140c51680a165105500022296403a45019900c40000d40d40f410800c9a82404c14140c4a12050340c200c0f0140d400b04c1402c041c0c8001c0103031800c0303000303485a0740503801d100a0f6920500c10509035041c2c1181122441141036021140700047c0c0d001c0740c0b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 654741258 1250 654740008 654740017
    0xb0a03140601171f03050309120f0712030302040e13050c0312030c0d110307021b1f1202130b18010302070308011203050f210601030b030705011b080309030301140a0317 74
    0x120b56054801c40c4420341300404200f803640080790107a10024001d001440c00700103104402c41100000c00f95090352014007030703e07a009031007203451060803540c09008060294050714080c0c10b00c44000c100c0c51402e4440c0280404e2075141c1541d10380203041141d0040e0030301050032900d540c400303620030b403541d119003081e11555403100742ca2950319552810f451000d41202d0780254000c1d905a13005060651a5015803e001400d04da4040d10440000054810782c03001c000e0402402c01c42401e1270701d102c1c240b40100801034490384c418421003e2202c040886e80d240308002502e1466206406000e2020751000190b04920a410f030180c00319184000402c076442c1e608800c003061742e10a01d062810003e003104c0c6a51103401800405c42001544404420500282010700c1da01900902c1c061059150000120b40c507841075000e03150400c03d0310301902403c855080326142140c1d40c01146030b6906c0c60801400341c3c40c0e81080c00b071161070302d2944c1c060242d10710f012200d02c426284c0081c0006441c0c8103884070061154003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 654742508 1250 654741258 654741271
    0x6090120010f1107030207081b0628050c120306090f0901021c020c06070903081e040f0605270307060c050c0a141008040b0a0902190b0a0314060117 65
    0x484030b09036844070140340103006450740524680f68680040f4a006410980e0131340101714194031041040701c100045505c1c3c800e10032010b41d02d140d03032854908010a9560300041e2288042205503480501e82540070300203101084c0752509445e405210004458620712081e9481580209600c021070b01e44619035521a0b0890b0114000600e4110707014180402c0d4520380d1041391120b50301044040c1031190901019500c0b80261038800303035403070071903a41241c54021220080000c241010041059800d401e04960140140000d290760b499607508006080350312188490359805403c2d021210716228142420040e14070080c0580100360400c0000c6664041100301a6080d120340c06a4501c103807502e290b1080600400800d810074003003044203002d1081d0b80c6902c0c941c2005048010030000c101e4103074040d40c20900b143d002040c2400035000050003950410800401034160b050b0002c1e00d03110240061011510701c0d24140040c0056041f8102d4800c0308845442c04203039001c81c2c0500c0340000e4001d5691060 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 654743758 1250 654742508 654742511
    0x10b0d152615071e050313030e010908061906051c0611070209040c0302010201051503060103060507140d020307200309131e06090b030c0307031101140c1006050609012001 75
    0x1a07504100d61080100f5100b08010504900902901401900d1820000d44403810b1862440c205120342c00341030844210080d00300054021120b660b0380c412800c060003000a401150828101900c3c184001c03090711104a031101d103041030004890402e000a0113802e42010140010485144c98920191034020f055441c040d5042000000590310b21404a000d035000d80c400c2201241148006400c440e4043c011760400810200b103000a079400007138080c1034079800100841e172910383c4a01950352001a051085030700c1d40115035040940b0b581d50145201c0c0340c8594401034500c14505a0201a00c1550b203401c03100c0e042009220314504004048043d80486001c001071200c1c40004040390b43c2072040410f0503019111401041402c0443c040c01040f5070040780901806140e410000399142c445110051002c8110400c44034941c0c001e0300d00a0280e03041c250904d41c0c60822580b125160500503042032811403030b2017008503560070040296168284181c460900084003403000301281c1e100004400c2c0b040d07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 654745008 1250 654743758 654743773
    0x60e1b03071a0d0509150103210203160f020307120b2203080a05060d060c020102070302101a010c0f081812071406070609171b0f0d030207031205010b0d1526 69
    0xc4141ca03031b0b603000f0340c021911241c6c00c00d180d45110101c0044038034603004652061000000d11030b0010980c2149a51182020b41c22071b0240c07010a05182c41580300160501100401d84203100c0460440751050351010f101550b0380307001d00c0c507070390040000c40c1010300081e24a00000c0c03a140002c0c1d000ca0b4112500800385a07491102e95103d2041d103481445001c0140d4020400800301a0100440b4501d59001c81c400d0228040aa030f011620701d01900800b4100095402c3d07a07424000c02c81204030742190007602482d40c0d10b40d00040541c454020201d07550041003100d1340d84507504c1e004140f141c01c1c0c0e00c0c4484240920000c420810100341c100329002d5075020f90707802580000a14044e00300201e06c00e000f003825110007a240386145d2100088406a071540c000000d200300040c004a821107014049090042c1c490700b0b41d081c101d910700362158a070444141b50100209003e40c5100c00b5108900001d48284140320030580042a4125203128030a040b8962240c044245070a0300405000e0700038002c01c46600 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 654746258 1250 654745008 654745033
    0xf2709061503060f0e0120070227040209070c03090e070509040e0607080919062c07080c06181507120503010602070f030b13060e1b03071a0d0509 64
    0x1681c0290b02c00c07581c041d660000c29440c5041e034001c4840a01a200c0200540900a014003c45400c50300e10311402442c00076800701103690b282c1d80c03e0000c0044042e981d480b000d251045510403103041c0c0d810f03480342140b90009080523210f034071200c104950507510b1070040e902d8510310125400014010130103000341031068008a495900c2650740d401c85160040400e07041003c0090484900541210a56080010070f00106081c0c0d01c0c09000701e41d0301c9140080c504d07400c400d0705c000030450384003010040d180c00340e52000340c14000141c40003501c0c4601e083e59440000e16003044040c1c4501c0c400e03441081c0038240c0201852500b81c1c801901d140800040f10703d0b2076900c3e0b0307030b22001504250b210b5001c01c50200c014001e142c0d041040b40094012030300501c2e103c074116115076003c003030300500304501a50700ca03210303000b0044140c0000c0a851000822075017181c100741d00c903803a01460080528001d04c110840010450711200c1003201d4882441c000e98906903450b81c3d0f80000e0303c801040d1400070310a02c27555480 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 654747508 1250 654746258 654746291
    0x1009090e0304091d030a120204150c02010315080c01080c090603090a3302090f030304060309061406090609040f021008070f03051b1b060c040f270906 66
    0x45880d8041c6070741e98201500328080760031400081d00c51440c0d15100398030055000088440702e50607800c107070000d415029441c001900c034542011a07a008070300184103c45400c49400700013203200740c07070900034101c1282c28410301d401c1d2841012000e81c84408603a0f0719500501085400081d03480c0041d10382850100400c0c04d42e031040e11010303040d5211b10002c0c000d02100240b003920010180360310140c0010240140c5a40003200300c40200e20782d41c0040d803415a603690242e0100c10385406000d1b82d480369139500c0064001d05004105440b0b09040c0b440d0018403066042c030583c4240c5000704443c102c4d494901c14080500e2008000701c030b552400c000f078800940d076650301e102040c003450744d501d02007482c086000034150340700040b00c68241070808051114001c1101d6121010002d03100042d81c643c1404120740c1441841e01e8403400f040d008071828001210700b50801071090740c6541c004586401e540d01c248200303c00c0c00c00380c14040c80c841d850480342d915034260003802110740900c8000c07a8040800c01481e9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 654748758 1250 654747508 654747521
    0xa02060301120b0c0a05120c160501020408070f03023f0a030f05031506160b18010605030a050d031505030f1c020c01050d09030203040f090b13060b09100909 69
    0x810032001c2d5824908201420b180345501459104d0150704008407040003521038055000f00d0031003201040c001414903151642640c00b1040b401c07440d000440100d080c0702d8000d500c2070203405014040c078000800e00200001980048079409410780309020955646901140020309901941450406042c1003410440c405002030044142c0588050307031042c600608510480c030341c0c1d4400d010b41402000102c0000c40322101c174200d42510020342d00c940384c4580d456102104000140010b481001380134141c030781c0b00032118514080740b0081011641341c004040d0fa5a103403403801840350740200140d040880c881d4001040c1841c00a14201c9007a4842c0c0000341021741e4405d510fa010b03841b0b11900d0340c5404400742c90203a84238460000d401a00301c40000203000d80b195900d58180980c89001d640101442001101c0c010301c54001d142400c581c8519100e4042c00b480340180780301e240c240080f419401d0701882500e0407254001c0381c4610741584a0107112000c0300708107800b014060841c800280d148203074000c80703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 654750008 1250 654748758 654748769
    0x60c1f110a1101150305150c0903010204090e060c0304080d02070c12030c0629090c04030c0f0e091920062a012c1f02032e050d03020a02060301 63
    0x50400340003030002d2403c54506103003105410200c03040400100e040417840c60b494650b03d18107090f20756144101d69070a40b06040c0403941540c4001000188100740d644000e5800d10b1603000e0700d0150702d0702c1340e40400600041e200034000030f80070043d030510040710b0b90003041031601c54040002c036655561030408110a03c1d0704141d010900455005081190318462903da00c2c81075021b00610603400d80b100c40c4080d00b88041d644c09200c9210114207402481c038195030017143e001e03201e444481e03260f980d4007a5134610b900c00c141c00075800001080c543c80b00401c01c642074840401f00700c0041c81c7e090310707002428160605145512080218894643e48540d4000e2202c0f4400c004030004600035511401200101484140d409914015200d555910000b0881800e00c540c1138107251038445c0b090080c2c1c1000b2449504d14410f031070244001d980c03440e960300036511a030850071021486126440b40d8403400480c0340404401c0300c0c100340c0300340000d14141030810f101724000d02c1212600c07101a4042035490f8801e030080b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 654751258 1250 654750008 654750017
    0x90d171012241401050103090807080301080d0f09150e011e050a1103180409140a061b170a0203070201060b04080f0712030c02041e09060f0b060c1f110a 67
    0x58110418040d6042a41d0b05945420001c200900003541c20400040c0034841c10552070311900d40901c0b050206550246410a902981c0c3e5651008a1aa12011b61004001141c84c1c80b0280740224068000441128922101080c00d0350300030400b00c400b0501000224144003140c46d000704103600b81804880d0b07508994450742c2d501c128185024019407011080e2040740ea0081100c05040c40380181d1102c000c2030f041d68045051403071071034200c0800900162501440c89200c024400348135468210340d0701c0700054148640040b0b140203040b03a041c3e07451030a001c00c000c120000b0602c1c009243c1d00642d40204640f0000034043d1301d4141c442056803107a84641002d90101c007440c1c122201c14400c905c000c0020a22452220540713aa01031700442d1030100203845947e81b003071040b40c5500c14051010419400380000c00049505113400c1e00144004017210303034814a01824540b650900c40125099500395200a056a01401814148040c803042441c0c20564031414183d0040c0c4091014001100c0307103484 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 654752508 1250 654751258 654751283
    0x1c0c020c030f012c011b03060302091503060f07050c0a0302150109060f03030c030c0611070c0e070507020f0415030305030114040203011d0a060b21090d171012 70
    0x105031914880c1407403102d4a0345400303900181d031a40300604d85a0200c02c021401900c42c00ea401c55070042c502642c28407105029069003102040c1c0c554440c1050b00c3c8201d40c88821030f04c5018110700c9000c4036402090700750f0703c8000030400c4909040481030384944075182c42880c100c03250705040e00701006044101e0160b40903002d880780e0458180c000360701418200c10200130141c500740c02c154507040180700c06414030040010040c0de0601c00c031406600d0b01d400050501404a100818550756440307504152000310403114081030a141000166014640d10340c0d4085c180f034055002c20480b0580e2581482d40300f55030316840340403001240d0300c2400035406070301e5050300c0398901030315042c070321100c0e109a902c030707520420050060200447c450b0003c06030007590b448550b40c640c0c00b00b0b8020b1a4503003003120140c07404111400c3c000d0706500000e8109031015105400341c0c581c1000c85a0b211003550201c004100f4480c85a912962148130103035000920403102024695646000304015007840380c2a101105da028 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 654753758 1250 654752508 654752533
    0x603030201050f09071205070b03010b180f031f020c010e0102070201121b0f120603050d0f09180207021c0b062b241407020d0c0b010603021c0c02 64
    0x8540e5902c44601c0b080f0305114a40102c0c8141c0701c18030750260b61400301001c4010418080100030740c3c8090802c6400065032941c43c1c1c40501f10540040c48a0000300130b802039054a2400c081d003000490316409801080741d00c2103000240c514202500c605003581d60f0074401a400d68100b4014000d448508900040c0d0f9540140001840da0050030505020f6a092200c92080100d401c080c00a08804e1880d0122070f01e22000f50840d089803001c11860445410400080f09020020440d100820115141d2130240182440240c6021100b40b040303040e20740d442c050072100389200345c004006051000301004104229200d60982c1e40c0c2c1da615042e5405c2c11108108051800c06000e001c182d94103c504a01c0c80c07072281c03084a0000002d1a10041c0a0a079602502c0301c102da40081500d55021454000d000746242641c181a02c01341c101d5007a001449000d402401c405d0141d5094007410307400481712003caa09001050b4081d41c02699603403488100c3e10007007000e00c07600d84501202010140d014210066a50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 654755008 1250 654753758 654753761
    0x120307110a03050f0d0e06090d0f0e01050f0705240f01090203061011011d100b0a0f030f020102070f1401030b06400f0807060f050f03060d12030603030201 68
    0x34800381155910851440c40801c0d00241a035007060105410b00340c1d69a0b2100c0380c0c1010713140348054043e0512988040c00002c4034041214000c0c48120350725001d000510310700031119404520f0f5501e001c02c008224203e025003240307004010160081003181c60f00150ba0303d400702c003200780c260301142c01e1074484280300c44240070707080c507600400300e116056056040c050f00181140200041030020310206000c585040031080d007000356030451070814115505802d42116803505910491320b26950301d48550b02c4034a1410122603000e0718042c3c0134000c8800d0030744e611545011441042a419482512400105e2150700040800900f038400c031061282c200040025081d00d103d103050b030740310700da040c42814591545100710002c032030030140c40d4045052510014a00400540d042d1120300c001c2094003103606102401e008003180c002e00101c1d000c2d1503950404680401c0d80c40385510009108000324130411001602842c0c02203801040b45547c034065607202c40d1002c6241e440600801c0d1148010014190203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 654756258 1250 654755008 654755027
    0xd080f04031e0b180106170d08010e0408120403030f0507030204030204151404020702040b120705090f090607080a0e0106030b090c040203010f0b0a050706020423041b080c0903120307 80
    0x10721030251240c80b16a92041c980e840c005000c8118001a00e030340d002115001d400c40700c020600595000a0344001d00001502c0c0c40074000c03102c02140e115000000c254007290300c42445030750070004503810200920a440380d820300241081d000c054840c0c1c2d0707107490482d551140d1030251a050300d0040e0b881d4034605c144020341d03451441c80e0b0b8a44420640c10480c2043d0b0f1118a402c1e80f400b1240160345201c3c501c0003e0050850f035640d00c1d00202d09100040500000150302420345800300d41d011501e0b5500000200c102804848200664010001080341507002d000006d400c0140340d070000c180c0c0984a08050b00312426540305548036203d850a0040840080c8001d8007411002e0700c0039869581001840001c2070310920609258003400103403906254421410b8880e51540001c2c1956107565038540004640d02c00c10f00f07084c8446010120900c285440e01c9402a03811081894a40301000000103950b00100144803005024082111102c5990244200700700d0225040c40d0b203869003406100200800403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 654757508 1250 654756258 654756293
    0x1b0f051e100e04090c0b0408060c1c150509160801080f070b0f09090f040203010f020a0f0c050c18150109120803060d02100f0e010206240d080f0403 65
    0x406940c1592a40300c20354a81003100c0581040380341e040301c01e03010500402c00110050882d00b2003032000b060410944008000f2107180c002100c440343c840304504103840c03003101914616019006000a54000207030131000907803030001e40a01320607640d240481c0307000008031400c0b01103280d42140f1205003a00301d5a82405010a00f0050503400f85c00000d095961419010b69039060201081c0c4a000016580480ba91a18060511041400c00070020b0714428000d407001c9109500b040c02800c1c103040c50344265404041181d480341700001203004203540310b120290301a00d060090b4480c1010507120301d4460320700040e44644110f05d80c03901c01c05101d0784554442d4541c0c104680d40204000110050800503191303600120419600c1d120200015030800720b0840081d08150310216000039150001d02d4841c0720a16911083c610010205c012078850104a444100b240b070090303040e1400c101c1602103440003540180ca02d82c03003a49030741c40341e8171036811440c0e900b94164800141441003000742e0414000780070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 654758758 1250 654757508 654757549
    0x170a08010e0a0615180f0609061809020a05180f13021c020309030720150a020309041e0b040e1c1205040606080d05030c1b031204030e0a05031908071b0f05 68
    0x501f030a800902c4000c0d9403003171000300900b5585110351308090f85c40042c014401c828003195074916800015010b90080e54031204010600e20b2400480d00303041081d0812248003c0c1980f2052540405220083d0060700d41d084400c88800b4822059841030b20040d40100310030801507443d8060f134030300250728124040c0320708001103900029404c283ca0307903401a2788080d0102000d5444031501c0d00200d01d1030103100ea095601c14201300d001c1c260000b1203d115000703400b100074144240c1e0040010b12081e9089584001041c0d0b00c101c4802e0300803101c45801508490081ca80220714200040079601a01c4d801e55065130b2035a80c1d00000c02c000c440402c0407261140c15800c020741580b8010905018a0042c044e000c410411816441440441c0070700071600066442d004e652325605043c20000d02e50b111900d4a2070240e11000300106141c41e00250042c10018a03c802c0c1c3c203141400d80d121f91158100c5001244c486c40b0918035a4107851000800401410940440302e000d141b0f00400c000a80c0d2241542c4214034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 654760008 1250 654758758 654758789
    0xc21100b031608030d0221010f03060e1b040f020d050115081806060d1e0c08011514150c10050a0c09050d02010e01180b07170a08010e0a061518 63
    0x3d000210903110001c03403003400144c49000e04141150a610350b50151028410244004200401d00314500c00540c1d005100801c403690110000941d200140306502080d50359000c3c1d006201e2402d500421204902102e025007040740310540d00d0241c40c400c2c2c2100542d031090f40c84150806903c0032840d07501030561aa00e90300c0100d00e101e11a2100c3c005040180142103c031000e0f02404150010114080c2c0010135400f410002d41c01c0142c071001c924000c0c141a03508001d282c0d80d0101d426004102510300c1c5005043c00206041d00300704820251080150004c001400700454200041c016034030700c00f070750350000f1030300740b610410083c03c503901e005089092140121082c001c0e6128a84c52103105903080c2444051408403e0041e1005905003204440b25202c402e4003140d9280a10040c00240e4410a94240c4607400c0003040d42d842c0c0107001840000480c1c103c01000b02404040e4015081356800c0d00004081e45c485119401d4030510440c404041407010300311400000e007442c0ea550061800203a0f00804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 654761258 1250 654760008 654760019
    0x130804050a06050d1a1e0a0b030f0403030c0e0315060a03050a0f1106031e06011404060215060d12080a0209030102030c09011e05030112110a1401090b0a020c21100b0316 74
    0x740502c41b807101489801c820100816444030205903016119020f09261039140c007000400701c00d4003c8600b10000b90412064003140c0b4015070f200203841200901070408243e1440300c024003998010b2503141d001a2f1080008003088041c42040c03000c0380280c0307070100c658905040c20404500398a120780c0c001e0b0010010020000d403810440d800d4102d1a13034034108681c0f24400101d515001d1110394909010300003400140c0540c0009050810010840001541d5542e2004124103070294440c0a0081c2c0301d09611241003a1007512882d91000311014010f0402c507000012a08a800031247c1d80b02c0641c0c0007078014125a00b00c0e00c09103640d00541401d18840c05280780c01081400184510181004041660000c000c1140801a800c107009046115800c1d52190002d44800c2a08036850205d45d00910104e0140c8611085864104050f0000e00601c00e07180c050080b50010250916040c81c80056280712124090280c1380421100c0c02000c51961001ca0400d41000c0042c01c14016007841108200003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 654762508 1250 654761258 654761269
    0x203160507020105120a02071b15170f100305010c020304060801080307050a0210050f030411040507050301060c120507120815060403030801090f0e0f03120a05040209130804050a06050d1a 82
    0x30807210429010854a44032241e401038010003030018840c04100c81c0314027444c01c0386a003000407905e0488000e41151203541e400e44001107080c821400311340c2d4407400900d48030f07045d0317440c030781c00c65405805600c0440d40e1b13441d4603003111501e20a040060f000000c0402003650f0004071a40905228801b551800d48160b98850343c442d00e09000900641d010f07401004128020000d031040e21203800190f5030f0381e282504e80300c1980d204480082e803041c3d00c1e2074003241d00548a04141c9040e40d0654590b00c2c203103922511401d080407501d011000403c20108004000110800c10f003d4440c0c209444104844c00c01d503440f1403511561144180c0600414041000070a40c090b910300e04650031a0300010b10030b400740352020041d000c0701c4c441c20481d200b101c012100301c0340008014a030421009444039096150010b04000780c5400fa1000f95100c40c0d01c40c0420036090040400300182442804640e01d0642c1e260003140240c5816030084003c268007044000e022403450040c10b040c00200d49030049180c2c400c000148 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 654763758 1250 654762508 654762517
    0x1091b050a031116030306090510030f0f020f0a1e0603111206130e07030312110a050307031b12050c0906031303030b0d060204260613020f090a0203160507020105 71
    0x2007056140c1d080e900e07001a4050499401200c0b104131a62240002c0c18064040c222501c036251320b40f441c041c001941c07803ea42d03044038152584001030303803864082900c0f000070700600c1401c1030f60300c2801c2c500c851149540381080c0e4002400c11448807e010a84052007908101e11940250141403c1072140b0541c041808110303141100e40000390011511072401003001400500b44040d0294a00707080c80780840d40000354501120b00c0b84d03640441510b2600200011b868003484040e1015405204000f241400360000e164052150715000840c42042207503624206148158900869100c0f00d40409a40c1c6502616510581c0c501a4510b00241c8601150051000404a03006400314181c00d80802d40310340c00c088020400140030b020b0395030b140d04182c00254001d2060018021203000c190032115000e040740d512400140300900036030340e0381c560031744200282c0741c030101e0b801004042000165510100602d004407105d200040e1a0300d050000d85030840b0701d85804005000707050101c040142e91080858 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 654765008 1250 654763758 654763777
    0x30308070216090e03070b010311030f0d08010605030c0c06010e0601020f0604050604081b0102180a06020105132a141804050a06020a1403040f0b1f0b090a0b0c0601091b05 75
    0x1c2c0701211301000fa0709500a401000b00882d024100002c14440200c3c00d88007550000ca041d9140b005042522030b55644513001000d01103045030004020381401080070319403260209000324546003910102c40d05100e000d8100b41040d130152000c1c004a942e040008000f450380038801040c05042a80310301da0387d614000e00c02412910001404404130000a07441500740c00709000070744d01c82c54188080c00034030600f400305601a95201d000003840b6481405500e00a6101d4003005c10302c080182c80e40b00030b8115034901341c3c880112042c1040e40e400c10380211100113148414401844807aa20104170400080010442c021000314080c071020500101d4910202a881180145d41f40003020302594040d80030030380a52039603808000c01c0144440c1c5500803a4144c480c180d0740f1707d5a40c44a4840b680d441c0c0141c0d1101c0c4004481c003061102014200091903030b40d034001c0070b9811859403400c00035544e5200804480007500002c00410490405000c0c13102c80d034074014410302d600c400d001c3d40245a401000c801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 654766258 1250 654765008 654765011
    0x71218120311093003072d1a060a0f0f0f080309150703170c07050616021f0f02030c0714010b1f110d0306030302070911121e1003030807021609 63
    0x1c0d0242d01d24808901131208440410781ea22000c0c0c1b41440e01c1c84854034800f1000751790016481d0b01c0702c44420011001d00503844802d84200b683c100a0398900d0000003800d40703401071401203000c40c0c40100304840320001c2a00c440c0c502c2406081002150740351680c1e0740a40004e510034401905107541c2c2d00e0b807004821520202c4189c0b5220700d8281210114101c140400d40070032000d0030b1099170000070300109001800340d012601d280c0c0300c04080410b0340700440c000200581181070f0030300011807041156150320040140110314848003400718012640705450300e441210b40094003100700480f180f0359505000f0102c1c000c006500f0100045001c81061201401065038004c0c11103043c1806504056140305641c000c60f11400101207014004283d9401b0580c0540308160300003d0344401d070300544071050b400b0620542000075101320b511695002901c0300070305da000b1040e00b40e8024801c0c46194441e0a00540300c0d4540341c0fa60401a090140c0503001400b103410040c000c001d500c80301401482140d401180 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 654767508 1250 654766258 654766309
    0x100c08011e05100e121c050901051b0105090d02060106050702040509100f0e0106080a12050a270f091505061c02071406010f03050607121812031109 65
    0x84098441d660000c0da40007981c1610300340c016911449141c48507409442c0c0c103402c103040300d00c01a541d10340d0f480315050600c1441c07281d00d401032241c0007800b60b081c07040c10442e051042c05081042e01015400044007181c0d940d804002981e0400c218141031680c560001d03258650604c10010301500c42d04002900030382c0c80d1b0b00418030b812420048041c000c000b241c0d0400410054000c0040640b181004e54a9250300f010004688004041031440c5101d80c08075000e224240026401e0303805402440d040410f00984201d1500040740c0d850b01c1440c08003520045005490a000606040c3c85240c0c00c40340f51140b0b00126803001c03142c8000c0480580e0011200c080d11081e00c20a8540d008100c0e0303030300151560010070584208070304800c482f1385c00c0641c007003640c4050780c807606012aa51340a20000c2c2099001c400070a010500401011350b508401d1400030400389841c3c0b50500c0940202d8904071605250300b15010521a40352043c5c041064454030b06071314104c260000617004810b03c6120745024121280c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 654768758 1250 654767508 654767549
    0xf06060126040c0302060a0c0308061903021203070f050a0b0c040b0a1422030204060603050601020a080d110f070b1b040302300601030605060306040f0b0402280503100c0801 76
    0x40b0920007144d008000541e621401c47d070042461050300400c17408540002e0128002c0d00d032410360704000e400b20040200c3c04a05d15003c00c5004282c111161490f800200301e5080840c040b4a214131210707000f14010702c00c041d560b180540001ea001400b800d1025001d00003403001414210445d11040030310b10f00b007030740e0000320300c5018141d210f03a0402208040c06460150392603d0700b40e040c0d0048034002c4404021040c0c1d2070368290243c410854886005030081d81c00c00c0c0003d40a2009030600c0c203010200007130710420801404001c0c0c1d005450000700002d001c64001d00300501c81024a900c09904a440114140091102d8100d4003e6000007841030704400c450340800c0c1031520315110145801300500d14045203440c051070316940c00b070109580147c10080082d21500b0001609801a0343c40320b039051180b0407036150801704d03640c0500102d0784210010302a5460b13150348d5890903151850642502c000c0f030b00e40340405103000c038442e80c5102142c0c2010302d20300820f60446019411140c41c1c00c0c02151002001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 654770008 1250 654768758 654768773
    0xb010e060a1815030608061b160609030c0615080303191509020a020709020a0503010506034f0503030a0c1412190b1509030307140f0606012604 63
    0x841492000c0c690b8080002e042644020b2101070703200319202040602d40f51400b0688400e4215105481044812411009030f000743c8000d001c001c545a400040c14212640e4960964400c1c0340181c001230102c0808009000c41031240072203600580314003060482c0390122194503400000c10b07146500e035506a03810a1f05906030030103d0031002205003001815241c140b00780094100107050001840303031280214074000303503100300e80710341e1001d407075032400c5030700e04020008940c0c40182005a440c214411420301c80700310800444420030320701300f2a014140020f02d1400000000550304540051404a0308080342c00841240c0d0003220340540480d1007020f0110940d104010318010358079080c400610001070080b2482c1040c010f039185018068a8003084290806480741d107001140d000f6480304a200b00c03c003040300103010211024003070b603042c44c520fa10355080303104c44440c441c140703900203e04075402d054042c4401e65202030242014203114505403411100c07107624000b0780c1d004841c140c1c0840c2c24032021 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 654771258 1250 654770008 654770027
    0x30a02030f071d01060503060607020406080114010e0c0f0d09030c0c0603200c0d030f110f090307122a090603051501050f130906110a110c040b010e060a 67
    0x5012188480501c8122541d245614414640414520010003a00150425001c1d040f10b49668500d0f0541d22030000708002907102e900100e80c03240d42c8400000350303142d00780a0900c2400410340c6000395507143c12b001501155005000c0e00b02541d040001c80c030140642c1c0300f070304d0314842e407004000351464030303403400341ca5407036189102420b1494003010010311281d143d0003041d1034604400c84005100046105442e10b405010420000c503040300f003446191520a500c030301148201a1404a02010841c0c050080c0d6804101d00d20038061002412521a007420003800380281112032494448154507290407803da00c040b0808110400710074900350410b20801009005030041d0442085055604d16015035a4045006840709072000000006046d29181840112004c40600385c0c9600841103100300c0d00130042018101c960f030707903520b45000b40088681d001d000c2d0600d01da2206455050800e900614119009004074030645c1809414070719643d111260021890082e200a03448610b544001c1d91864071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 654772508 1250 654771258 654771263
    0x2202040209060f1305180403030e100c020102361c12050a030e0c090109020a0c050d02300a030906090f060b1206010b0415140c030306120d0903030e030a 67
    0x8941103105400c00001025000c00002074189001e81d90700500400101040703e40034101b551a0019000c00d0180d003296002800301002d68090032011401c16003120944010b1100507940400d403016145c007a005a641c0002100d521083d0250005011041a142c11840c0c1406642d07c405000c8110251060410034030b64031460030800a42a8940208079820415645002070306000050500703802c00f143c17140d001640600041001ea081c6188200690710040d250020014813940b9140811010b024000303c60003141d02508085d008018981002c805503005032007084090030114800034032880807114120014100400d010b082420014010043c200c00645140340c9591540100040d0352b1020b00b4036002181d080701082200b0340070a03500c400c00d0107140302c140710401007072004524074121296204a80e1800d001116030303070501c030202a0032845032008198008418012103107009240c2280d4402403400800d108134602e4001404108030388005418403150580038203075501c05000d44800d454 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 654773758 1250 654772508 654772519
    0x30c0c0c0306140f07020a080a090e0405030c0d0503070203040e040f0807050a140f0604110d0c1806060507050c091005270c0921150f041205032202040209 68
    0x50307581c100348002d446a081c0c1001e94040400000b02c449201091281c00b0f4042035005150320300341651561549e600c81050305081c403040c6000002d401203a00c1a0303502c6140f1072000356032202d030081036080c5004010030984083c040140204440d00354000240e8040750691074507507807246c88a0800800130442820058102c40f0001001001d00c4000564983c00511800000c0d24a880350041c540c1c40320708141503402583c000d20007041c04101c41074458100084000e010801100036959210140e010340d600800f0403003034000ea4400c200c1c007103104480c0180f546013130140c60040c0b60340e07500303480300802203d86101d180c3d944081141000c807560603a01620000c0c08003104c82030700181901000c203015003044010b82030500007a45d940007030420b503200311201816080d850303011b804800b00300d01072561441900780b181101d00c1c480190240d00d8140600c1d1000c0c00742ca000d042c581020700c51200940d0441c01403000070000e0042c107202c9492080d0441010b1810800c0d00c00d42d910020f0b002e40300d0110002c0c0e004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 654775008 1250 654773758 654773783
    0x40201052209020c1c020c0d0b1815150303032502010f0e0a150608060103083f09070f140429120d1e020307051b010f02010509060403030c0c 62
    0x1c03400581175901c03090b0120102262914102d040340c0d20034815051a4108280384c80910026191210040d042503c50200702c03c1c181c0c0001c102880c1c480030741a0700d45d0140682e0107100180c01c0070060100302503020780c0607501d9450507883d10700c94800910002800c3c10340120707500240c0d40c400c0d03100103909003031610180207108000360640c0d0781e100d0100d01a940b40741c1102440c610242d00b0b1117010125039088001d400e11341e18540b12078030b20360841d030349405004062012102d04268201100d0b180140c60a1001c280404914070500380304900030003038000395220ac00280520820030501c00115182c0005c0345a5500b1400041000703030100c80b22500c082012108242000000d160012014071030503150301c5d00d03409081c00c0296542002da40c078440852140d49800c15074501c018000c807040700705e5004407480c2c50326940d605440c0c0030140d2400c0080c18a8800307243c00643c0c0c80b00103101c1031802880240458102a0307000c988509016100600785a07642040000f103500801803890190b0f0000100d0850 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 654776258 1250 654775008 654775027
    0x9021306060306050618060c070e0a060906050108040b0a0e07080303090c03010c0212030a0507030605101d030d080f040204060b0301081c03051501080604020903030a111504020105220902 82
    0x5030200d4001c81000c40e00300303480401c0d1401c05400b0307900c140700300e20400d640c8060048103205095000f188207030098081c0c01d20100d1461f581c0315030b090090104c40d0000500300e140c0000c45049800d117402a604004464050102094045850b10741100e0051400502501012a118a440c9041d030103080b150002008018031580c0c0407a501e01d903180c0c00e9009001c0d03071000110032621040c090788207540f051400d2021031072809aa41c0495813007982c3c0d0070001045074881c0700047c000903011030850002204070042409004003c90a00d900d05410350081108001c001e0001e81011001000c07800a07012410004080d5a00e030341207080144804217919581e540c607504007a82790701141044145081038000b20203845131282c0302d0300e031003240140e1200034001c40940c0111041903000d0101a80540c003806000c21943c1e0502c01040300c5801600d401544460000c0c0c81d50600d100b550750114217202c0c0000308009030f60864215600ca90400741111074500c0d0003540961041d4581d0450407480b403020070010315 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 654777508 1250 654776258 654776261
    0x51e0a080123280b010507020d05010213090203010b04210206030103210903080a12140a0f0615050702060d0e0d0804031220070812040f0209010e010b0a080a090213 72
    0x20602d001c140860043d584400e40c1115944501c0803601580074440214802d4030256400410200f005241c50391900700250005141a05070007815a0130381d47c0020a400489a4000346000a022911065003035615002c00c005440c002c0e841107001008081c2c040c4040c400c4440711108440c0d50052055450b07507140d04220402c10f10704031a42d45262400b100048013a80140c2180f07040700e900c407101c43e161940c041400c503074004001141e00030064a40b0b141c43e118014510401c0c1c1b06211054000a00850303e8080c01d041c5c0c2c103d0303800941c51450074004c0480b01c550100131600d099805032105a031340d108034003040e03000344100c090b0020b00340a030718030039020b007584580014002c900a03a240007841c04c001c034403082190915030b6040004401e030501c040b171320040c40c4058031045000c0c0d4001401c1500c8513920001c43d10040300d048540790700c0184a40111310781700c0900e0740074104a800c0b581c4150305209a210841c400c2180c0c12062203503507000101882142d41211300c3e004e0b03000d4510203200d600c0a01000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 654778758 1250 654777508 654777551
    0x201090615061202090604120203100504032c0f21070f030b0633040305012c07060903020405040c0312080403202505090403020a03020c0406051e0a0801 67
    0xe00260805080521803901130096400112004048619091a0449000f03004007c0c49040345c240c011586211003040140c45043d00c00c078060345942d4180b00b00d079001c20824601c0000f103c10402120340c41d0005640350010500d4405009030f42214001c4003284d000d510041405042c035129100704080403550002954000701103910984a10805d45c0750001080b05103180904d0180741e05000702d036540c0c09460402081c0d2800c80d45030403050300d41758a0f51901802d45480301481011401c4104204803502881042040d899001a0140c40c825003072070001842c019451102a1185440743e0104007401182c0c801c900080d076201480101507541c0000150440b1812a03040d404203c1d070b03400d900781500d890340f1000030b20721825003d80415000f000e0301c044100300c2e0030000c1650000d815400302e50344c0c44504085001d68003130340081c40c1e40c030300034603000b0302d000ca234036900a01550410703808004545402290141540031511300e0719401c4c0c900c0c804505c00c401c480c0d1005007150b0a005e01d08080c403d0070750180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 654780008 1250 654778758 654778769
    0x703060507050c0d03200c0106030212010504170c0c091603060803250f050105040b1024051b060106030e010506091b030a0b09010e0a050906060a05100201090615 71
    0x38000d907994907209039454000c90b0b03007420068101d5030802c008144030398040414100e00c0c03010f06441c5c40e10240d100000d42c02c00c0325842c250760364501041c015484c10070111007205140c0b40081c0716070329041da40e100c10074000c3c60302600b0401c80810510201c0405002e000d0000c900a04190800e151408104920103402d0341d4130b00110345805c50120396030002200300c501c07164103507502d041c18145030a42c8600400c500a0151600c2451008400020b80203000d502c1c09107000748441445814500048030b00795040c1c3d0f0020341070984081c000c1200940b003149503c216003542c10880c0d04c1d0448100d188141c0d07000350342c11100d107004e2030001180c00c3d501a88201d0420802c0c0008110a1386d85800303004010a05807141f0544402c041202194195020003e5a018100300e0011550304103040102703c00500c01e800070200c180207501080788106c9544103099005d8001c3e001011a400c0c07800c0898095440303801031a0083c4081c8000c2c0031000d00175041440c1d4964402d5040100207407844008c01404014002d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 654781258 1250 654780008 654780011
    0x92403070e120a0818060d150e0702010b0102070521010501090221010b090910181d010903080403080a0608100b0f0607080d0902040906050702011a18010e09070f08070306 75
    0x140281ca03000080c03011651640400e09605c1d22030300985001007080c50020356075121a041011803400010350040c071f00741140351310300d0100090820403100c4004000500403811a850a500b40070300c0eaa0009142049850030740e4001c03009074032840d141d842d80c0700354190504290701b41000001c0c0600540d00500da10b07160b940d005010300260000d400c80f03a000c203102e01c01d1800000d005081a41c680005c0080e0810303e1030f81d10320080b65880c501c0c5419800c00601301c0d100c0640d40c02e00b407003092804100c100e080b1300910000300603028240d5406000098094805020401144000342120180350300c01001f0344010011151803140f02140360015155200605005040e801148061030800fa010b8824541d848100c0c5414041404811401429290400d0342d1081d21081e220002c55024840d040c080d030305c00d600200d94448046200104c40c0441022240260550000c080c03d40441d4550726054400080e480b0180b91904c1c2c540301e20789031079600718624503500140c2c0000d83d20f4000a0314000c070f921a280 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 654782508 1250 654781258 654781279
    0x3030905061014010c080306090a092a090507020a060b120a0804090e0d0c080f0d2c24130c0803070302060606040b0412261e0f092403070e 61
    0x4480c4645c5c40d5400801081c0306001040340e51900404035507105010740f80c0040c00e508182c540310007011000400d040010b024402c1c0312940d01402d2010000741165600510113401c265000035510100c521015020540d140c1008a05651310818482038042040c2200c541c144075051a0245900c28480d2410052800032046a44100811002a003d059840f51500c115907070f1940940356102c0e000410401008111001d501ca62a200301204030011008241c41c03d503600d211605e41040500c07801c50241e1205401020b030800703401c0d40842400c0c81d510032005d143c9401d00310b0080300c20b405200601c0c40c0103100e03020403038400c00405001c581c0d00a6080b92001c0c0c5980051082502c2940190403c0701820003042c450a00714a203601d00342403140002c58031080301100158014980c2c00c58103400c2d5140001d0741c00130030301e140800402081c0138010f0303540750403101d100d0042c0a210310714980d400b50204d820b8407201180c144c0c0c441640d194078108102d9036494410f02c010900d10000c001c181c0310b0440403a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 654783758 1250 654782508 654782549
    0x3090c0f180c021905030d02030c0a0e090103050606011d0306280603050304030845150313080c06040506070908060415020f07020a03050a12230304030309050610 71
    0x210300c0480d840d90050542c0d120f50000400c2d10181680017610680720070803100f158a509440114802d4507900c04071515a00f400c8001002c010b280a80140304034100c0700140089800840c1c000c2e0001c00908101682c050385040d800320340071403900314652602804042151003a5000c074031704200d0400d107074019034054490a2000071940c440c0005045680f040c0010b00004400d0801810a44000e422040c407402d295100e10099007485c8202e064a10810288a00c04c0090002101001b00b0121400b0481410304500c00c0003a010003081c030b4010001c203022600601c0b5039007003101c1d00842e034a02901c000345440e007071140c3d681000303961900c00035560303100c00035611902091326405030358001c2d20507105481611b204d10103504518800c16400c0d00420210300140d07901140c3c18006e610880240c000726040f03062000c0c1410b403100d08003080c844044035000d20242c5203200c3c040e090f006003642c180c80b5261410114010030020400404903c1031006020140b5051060142110a101c2c55060f0525050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 654785008 1250 654783758 654783761
    0x190501050423030306150d0e0c01030606020102040e0c090d0c03030315050d02100e1513030c0522051b04140406091a33030a050105010e15070303090c0f18 68
    0xc00c281c03070b80364000344040f07141450122408014001c10f0340781c603800c18200c10300d80404c0314101d5100081540c85000003000c6942c26000d03c0340204198002181860729250214440303820051400c14080380002d03e1054036a120324504800503003001c3c08404580d201e04d0050010701071001c070b210b683c418505000031985042c4601f80000c2d98040c0c401c0c41c2d10400000151400c08600c003060390300801040c0c15001c5030a44402070300b6070104051004120914508203500101441e0b00075602405401c403019038044c413520a407004005030100d0005003070340c48541132004540500b441010810000400184190901515020402046900708003075540d804010b802c8540480d0702d24050999145030300b0321450035148a4004c045102c1c03000d4402a556030280600c0010005080580680403040c042042c0107803189078098002802c24451990810f000158068400005024030001c005030450815201e0f400545e601a40980340814030b540310b400c2c00f40003e446000389038105002e29410660725846 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 654786258 1250 654785008 654785063
    0x110901050a03151b120b030d0207052704080c0606030703150b0f09040507080708060f0c0d020d1401060354030915020d0e01111905010504 61
    0x205008901c520b9603aa22041588000b0300b000c00075510900c1e00b043c281c181c0b0680c44240f0304d9544201c0001112042c3c1c1c0308891030f00c056107010790703c90741404000c3d640028100c415201c0865035030b10096640c0f400441032105040030301003034028650500042000704805020710a1488066803519a911401d0503a40c021602c00541102e0b19140c003c1a9019180c0c00318516100181c001d24041f11180003081c88140150740441d082d0b8401401041001e000707010a0010309801c0c07005c1d081d0750900308020000004041e0480048010000c3c2c01d04c151100f80d0304480c84400400d41c140081c0102052a03081d04509120303400201e410890b810540b43c041e1032105488141000300300c100071508841d48100c0c0c0040806030750b2414400308625044c8600c0b08102000d0310311940d00c5054035801c0c04400306102160304403072000d550151407403040e8150440e0891820f40d1080c6031040d042d001e80c03030f40c9910700700c0180043d40c18526005200300c1072200640000e84a24080e0f146c800144402c840c80c411150321 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 654787508 1250 654786258 654786269
    0x30a0c1e080f1b04020c01090b04060c022b03090f0f1104020c0a060c03060515030a0b090c2226070803041d040f0215030601120e0d140f0c0307110901 66
    0x411040c20343d80d011280c00c107944a007405000141071260645040d421900342c902c05850b04d4002100b00400c102244c010751460900da03201404045a1012000300075000801c8844207075003041c7c040c0e0f00c107079103e584010341d02e5400411a1021a0450030074003800c0844000c1a6010701c0c1c081543c110906160003210341c01e101400c01810814190707210300d8010b200082d050010103454080c0052180d036503000601c405404001015507c0c1021100c1c0000c40e415546c0e02401881076004200c0300441000545003520314502030030b81c41400c44c00d030031214005603802504c0c0203003c100001380c00e03c0300d42200710380c0d800e844d40032a01460f403108640380e500e004500c10704100050141c070544003403e00448140d005441100e01d15001200d55000884015194105d06a4910003104014880d0b0340035090b145078100c3c0070020070a04840040054072810145017103401d2114103015107030540402d4040fa080c07158200d82032a2503400110205807250700100050f10006131201001c000340c900b40240e10704803031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 654788758 1250 654787508 654787513
    0x20f0108070e12100501061e080613021c02030c120108070b040315150308031f03050d0c0f020a0e042319061d072c15030a0c1e080f 58
    0xc02c1c2c000304802400e585240003014007400042254014131030061602810458882840804100440c000c51800e80f00703884081090f000107028084d10360b0380544200c1e608510001d80d940c8441900204000080010441114400410082d9255040c0050301e40046c121110700c40f10799a03a810180c1d584058001d0f0402c1d88410881000080c03800e2200b19016200350300003007481e440d40c20003444281007039402910f0b400000003c200003013020408411000c0101a840c941c107600750784803035079148031414107041803000d8001c06506102001c1c080048159000341409103150b200c0b100d203c0c43c501d05580440d088400b08002d03214218403141508000c5035048000d1a403140440c0906110500c0b002042d209542d490403002c40000780980310061102d0b0300300c001d09510b031900e68100318030b1104015424564001101c503c0204a041c03d03a41d402411080030400c40640031340000c0c0c1004e50350381c2e004210031651500081c22070016000d41c150944585500f010f8280c0d92411991141e0076000040c1ca281c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 654790008 1250 654788758 654788777
    0x503150a050709080d03090b0612070603180f0c051804080a0309020a230108131e0c08060901230402010e010f2601080705040b100309080d0903030207020f010807 71
    0x14001940700c1c69100015141c10f040ea00d41c1d80c8090750400170149604800a40c85444500c140b110010056800201c2682e00c1c200303000340302c404152a40301e940a070800309916600c030185401c40194170090019004900a46006118500684601640c2c82114040c462620321103040340008002503218641141c0e8061801c0320002c0c044008000c0600120781c0044000343c0440d007210030303000ea0b802a801029805035564802d2001600080c0c0c0204400c2c00e06000c4401c14000a514071000908400c40c008030740c02003c982d10f002c0c02d08d0242604100440d0cc5424201b2501e0401504101c0309c403241008200b0b030082c0c040150040260048038081e003c1220007401280952141198800c03140d51803415480b214101c0c0c0d45008c002c0c2802d40340d00c00c4400c1c10343c01071209940601481c00209421641000005020008900b80f401c0319010f407810f00d40d65109210501403050206c0b01e154007010f004010a52041c5405070003500009004d80c054030400b2641c4040354040c05150b8080c11043d20782e400c86 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 654791258 1250 654790008 654790021
    0x9011505121003120309020f06130b030c0403020d0516120b0f04062a11030a1707090302030105040c0e10060e040b031501060c0b0a180f020d12030213050315 69
    0x2400d4040c11000b0b003000b0918001010540488482d40d600002e41d50104031481d035401084092061403190350701c81c030000c0056008001400000204495514410b1622640c3d2588500701d40e000c0ca6102941156500300030030304006020400e5110407540416001c1c0e220785854107000032000800e00200b104884101196180c5243e92150b07510620420300490000d441d081120340301541c1c41030202c4500303251004840d0040d00041c0001c1040c0f0741038000d40c107102031284001c1c45200300c07181103d503510503200403c0e081880f440ca0080a150050024000ea052a16080b4120300707603885001c24002d040d602007410f49504800c45000c544103a55520b080c041d05d1000c200007000d030002020351600c50000310f41c8050a42910081c020020754507001da00c203099040c44043c1620040903e00754034608004811140d42209800781040d4109020724400343c0144080359139000e038514040c2414201d0b05500e0640c5078540c00070880e01050035551100580d0f1241490707034490a940301e403001602c01d00c000441 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 654792508 1250 654791258 654791287
    0x10602190f020618041a040c14040504050702030c060403020718090c1e0509010b340b0a09051005070216031a0408120702010203060a0f080d21150509011505 69
    0x181030700d13080116200100c940700003c0c101c81c54080744030407441011000945615051045051721906800c1103441d45000c80700a485500c034500402c0d00c219581d001085000d4420000e03140b03000c49000c212115820301c0d05001c0d41e40c540f0381c8181d44c0c003078035840140d1910303e28034002c0c103404a6100e024015824101401070040315810400305c04a1000101c00240300c1c0d503141003041c020f02103007110b15075411204084176020180b02d058640100500890b00380161000b0400008094018191080caa01c418200501420b0ba148001c0e150b4880e164904408650310740c0040d000f03062640884000540752509100184024407000c1e000e08c0c1440c20780c0211011145e28154030621503090a49420312604083d041c60390161030000050303502104012050400c2c41c820750150003405d00c1001810310342201c0565440c69281c11204021b42c1c00d000c80c1152540203d02d11a1120100091142d01c1140d5030700c0614468901c40e41d4801c1e00a40d00000700d200080c01958081006907035158944030500c42c0000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 654793758 1250 654792508 654792517
    0x7020d060507020c060d0f111309020c031306030c0816021207230601170c1f020a0c0b070201031515050a02030c0d0c1a010e06120109120503010602190f0206 69
    0x154002c4884007002c4d41d80b200001c2c9450840703250002010300c2500e10180c00c41d041885111002a03003001102d560070701320308041c022034900460260381c51591048003819030292407011980360451080224540f6050341140d4a0100c15541d502030540e02c840090050b01030802018016800001c00655007050100003802440e00412502c101c2101c958880c0704004042d06000c01e02ea00b01a005000f0230411074003550019144200929801170110002080740b180001c108184442c2d15010f588810b00a0241c0c540c00c0c1d800c5407d800100b40c1c2c8840a400961107060100d0000e0b140807040c0b280c40e4400001e42017610300c426040084a00f502a0a580d180c0c802500301065100921072007944a108103d8000c179505242c1d54014485003c1c90407104191100090304507903040400188400011002a10752018007181c041035802d0107613203103900500241c0c3d805003003004101c0358500e140350008001c504032351140c0e0884204400e11b101040075103646000080074820228035500161410f0000351 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 654795008 1250 654793758 654793771
    0x1091404020a05012a0804260601050d0f050607110d0305150d0c15021f09112107080a02030f0619111b07050405070207140d0302030f0a030203150607020d0605 70
    0xc007410301020780d018050300d10319041195105000541844223407400e550103001044000641500c42024605a60301d4200502400b400f841c03581141c40c0c180203e04150405c50303074120080c2c400d1030030005030050100e21003a08131000c511840202c52409031280c81341c00d104256500404910425a2042000701c1d6010402920f008a905201040107040400c1024103441c3c180c00801e44884c0c40a41c19803035060901d0200c404610b08410200414540c1d01100d91040040f110241e000081c10741c401d21000000c1892a268806c00f03002040101c000242c40c840f0718000c40845001003c030312100c80d59244100c032460039055900803030b4455005aa0440b001074200302600d5424880380202c1044010311101a8007041d600c0b890341000f0605040c440c8603000501031015100e0070f03040040e008201144d00e41e0b880c1c0540c07a1031100b03d0505100380207a610740b04a4241c15982d441054000170065041540e195440208207098000d091074a5012a00c182d079001d8200c0c0e218103c10f45038680281802440c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 654796258 1250 654795008 654795047
    0x10507150e0a150506091018050405160306020306040b0901080307030507020a0306140403080f150d05030f043b06010806030a050303010605040e010909050c2202070b01091404020a0501 81
    0x94200103101c0343c1c0e005200500c9544001032520f40201040219070300540301940c08400c0ca0014410214a120004482e040680e0702060903103071481c0c0345141000140101813040041c030404000c2042d1034008501034a02118140118034100c810000015001e00ca11310041c1d20420801002900840107000428001400848016620345400c01603540c10341804c807004144100308010540c00c1807013503801130034000d0103103981c1c90410002120400c0700718005200340103500c00d080400008104840d070004804048989490390395a141c80444410021101400b889442491103c00301d2041045014481010070820f920b0304001035404800c013a00c0c040c1c143c050700760f00e000401c0d0700300000d500074412542c0c1d26a4032031920140c0f9450f400181c0141c0105070410300c000020400004100f5001c14003101e00d280600b1180401540b0180795000401282d0b0020940310180148141a14120340d0040814803064200c851030001040301294000d41c0b01841c0f45040c0101d52240e0321000d840d003c013000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 654797508 1250 654796258 654796273
    0x4060c0804050603070c1203050403020c0f0628020d030513140316080a0201060f0b1e0c0d0c030305010510140f0904090c06090f0303021b0a051905030606010507150e 73
    0x1041031903204440c04070103d81b44a068104010500f100300e440384001c0d00d01044142410340e00251505420b1490505c29404903101950960303031981100d42002c00c014501b109203500f0924428208900303007641c00580150424416800d000e0f0058030310074100346811320b030340100e690b646425110360001c001c2d0042c0701c1404207016170408010020811400303205410307211000e40384001d0030b5482540160500380b44100080218580c4181034500340d810000c3c0d030200704050030508114900413800100918401c1280f8881a00d4000301c0044555000755401d121903a21f54052100c00e40701c0b8004040003e0000011041c405240800f401c407820b00c00d140d4070320b00005140020240c4000400c1078a0001c60b0301810080c0940040d00180284000d62a500c404c600c5c0d920065207944020010031904030b046000105166141c100b07800291200030218500700d006c007000030100001c5401420301074820803010608541c06802034807001c3c0d51001100d039000ca0000218806880401e008406600c50b820 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 654798758 1250 654797508 654797519
    0xb0f0405060f0c040314070315110405060901110d0e03060c040e13020a090606080f0601090518270f1006050a0b0c150118060b0f070b1905090d110c0604060c0804 71
    0x10000c0d286c8038450000c00c0001d095003030a02403008100c0d00107101d00d00c2c10403d107a5041145040e0740480d4021076045841e808850b0060b11901e400315024009070142079030f2000d80b140c0015941200c000182c044890701d59840c0c1c0c46105038400c602600702d0300812a00001d1290b6907800211030f03010310152200100036901c611140655035280c008501142c600000c01464140024009620010900c0c04040142ca00030104404d00c0e101064103a04030300000000d00003480300c0d401041e0000c0b00c00c4000080c1c0f50520070060301d80b10380801c1c078501400b4003040b00542401e94094402950001000700a4940c07500f10300340642e07406517104a03994010005031082d400f0103010520f000340b0403190300005d48405450b44404440013034000d0848008180201c01c19940c000e01500c0000b0751101ea284c40c1b03a150305804583c00028071681e401c8203404c0c00c082001c1c841d030100703511140700c245803a01c41d040ca01d00300050743c95903d00f40c14960801014041040001d1203001545c4185001e5000a0b1070a41c032070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 654800008 1250 654798758 654798773
    0x10c1b0b0409020403140304050f09180601090e01140103082704021602010f0503014b05120703021806131a09071805040e0115080a0b0f0405060f0c0403 67
    0x3540070b003128550114080041c031010500118440340720760007440c61f090400d800202c40d0b4004000003401441140000741903940c552a0000070b940c0e00c00e080700c0c0c59681d250240f10140c008105446440e500303048102181c20100d08925041c0c81e88090314900308101e13118480c41000054980e60b15611030050f2003072485d100c1c2d02c0144000c0303100303004010400c7e0040c0005040b41541d1504c400801a0410040000d0065400c2807581c1e6440b414102080b080700f601c203000303404c03881400502d0550100c1101c100c010b06040540d422100d040c3c0d41b003050f4540030a01107448041510000e50000b01006a05610000c41b2105503071100c40104035003480c400140c80142111019030030304914114064130440707249081d84c0c80d10303070290851402ca840d025801752040d150044602c00e80c2e01441d20303a40c021420b01c6003908170b045414403045081400030b43d42c40585a544041c2074041c3da001d00e129000c120740c804881e00c01445250000020100d07a03c82c03204094104030018400418142c0500c0701200281741c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 654801258 1250 654800008 654800017
    0x9180906011505030c1804060815090606040605011709010e0a080d0f06030809090907120606151b0b060d021021020a0f08130209070c150902010c1b0b 66
    0x4490080c1903030740c1014601040340200010400a2040603c01c00400c805010119001d082c06550001102d150f02004140500034680050f5010f0062b1400390600c4082d10400c41d01c10050700d02280c10684420041c40100d44103070003821700240c00d83c403812300c051480030b003c0d9070450848400010300410400b1100d0901d50315400c12150300b07a000034600410a0540074924441c69040030030080d0500e50360310b5405a100d8140c0740d9020707400200c0081e0411390b041c0a9000100a59035450342c81d40706e07d01e40b4800403c41c8e4020069540348518018100910400a0000184503c10840901c54094648d6900c600d0010290365000d0090b43e59000180c50f100c400c54030310151601c8034005d9409000315124406016000040a14410b2082c1c2180315401140040c0014050810001c20744428425a00840c0f8015020b90000c110001b8442e4003580289440540360207802003803405080d250914055820700b44019001034000c4142d0408507800380340032071541c860b0200c801c0742e55a6600e01c60119400c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 654802508 1250 654801258 654801271
    0xe0a1b0b0a11060f2205010f0204060e03250e04050309190501020607020a120e13061202090f0906010306020a05191d03030705030a200a0c090605061e0918 68
    0x9603480d4540b0b18a01080b5890f000030040e84510303070310300c1c00c2c0d021044e440c3c015154a52000d0b501e040c213001407110a600c16400038510a109540d140d840b400003901c00c85805400074001d12800054408040c5540c08a40907903a42c1c00070b400c02c041c0b078a80510369a180140040c0c803030f40010004803500da0b40300c0100204030079045010b40031183c0340400190074160018468403c0d0340001036000c00240507000d45100070f021504254581c16141000320300404a03580008443c5071070040e0100d036001005015005043c400c4420305076a58441c44903482c451001d0341c041d800d5034407206c01480003410079000340501684130301e4411b052a9000640c035000c09046a03034003010401011111316a40c0918403c6024244107074000d42ca051000e0345c415580c1e101d401c0c2031004014128421801406081000710059503081e401c81d110a609400c1c194010070312480f4100b1018904400010389042c0300b0243d03078800410f4080c03c1070700210b0140c1034000c1c2d030003007404035441311490f480c8450356101043c40600800f0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 654803758 1250 654802508 654802517
    0x2090f24060403034a09250207050d0c03050105060a060c0b1b030411040f090f060c020c10020106050108060406060e191d09010c05090904080c0102040308120403020106090e0a1b0b0a 80
    0x1407421140c0d28a41c10080d066002d803165400f0047e0265880035407840d00b04526540d0b81d01e0b103029003400c1703043c10b566400c00b541c410804250f00042c820000c83d0b99040d039029030000c1105071a64420019511031500c115000f0445802054001c10f011a07545c6502600d401c24410035407813f0304201040d94030403141211782c1c104071500030700303142000c0c4260f94402900758401c02c4902615142d80650704002d140040c40213444d500d0600503144280a4030292840290020188410002c0d01a02800031230103050f0000d81c481c40080d05500d001c2c06120b08950194664900d66200c00b000e00c4030b86004804c0c0d1050f11004100e00045048882c0c003000312140c681004041c0d90709104041c0380c2918102034464042220500240f00d07103540300031606420903809841c295542c42c2c10100e20380640144d81c4050310f210340c0440c039038500e44d46140f4054400c070311030340c0200300306138803080002c0031904200e041e010341ea441030fa40900000c00d4101c403203118407048400003c2490380c500f002001ca0740404203400002c3c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 654805008 1250 654803758 654803867
    0x60305100902070f060b011d09060d02030f1b0f010906050a020a050708031e04080d1101090501290904080a0c0204020904020c07031a0f04081602090f2406040303 71
    0x806100304001403c003448c1c10b03840c1c3d54035003103c0c0c8245102c1d50403051280124002040580e52449001507015034060300762814003001c2500b4948427810700708030004010001506081c03030700e003103607800c2c00c00b502c1611146006410154115141c1d08042d108109501c101180840898401c1003884010800034009541d5900340c070890103190305000d00350320f68102e0180030500011402082034021904641b80000d03d00c901c20310110b005d0120220003030078039468000707a01300b58121038602c11a01e162100903030369460b02d48018042c00f1081140d014000ca41d05102803da0a031040c00c00750a118001080941032600482c00642242c1c401d50070080c0c0c560011508204100079214a040301a20005004460b031038040c080f4101503030001c200400300b250000381111088640da000038410f90b00505041c0e02403412280200d0201c0c0242c43c152100400320451503241003043c1da500d26180c401521041c03d03e071543d50169403c00c003c000c02d503100000c082c1c58071034007d610706140c0c800d8500204150840c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 654806258 1250 654805008 654805013
    0xb090303070f030204031109091905060f060f010c03081e01090608240f061f0806130b0d1203110f07060b0f06090d11030307080d061d01060305100902070f 68
    0x20b28142d21000018980140000c00200c2c07421a11840d0860341581c4400640d6104191070741442034411101c01109440c0c1540c0c010b1020001e50b03140b040340d8600241d003058070b1780b2041200f250a414141c0c0d0000d000e070320700200028880c010268000d03846ca80e40c8480802055141c956550090304003070f125540d02d1008000d07901042201c4030304a100084000440b4598000c400b040712001041c1501e00d22a01001c00c0c41926042401921500a04003111100d0340340003009200c0602906c1451040040d4005000c1203405441f46203900d5400400000707403841c4035621800400b5944107160b0074540d0352009140707903094003002000c0f03142c242000107035900c030340f8542607085a4515a00c0c50151549a51405a82d154202107546c41442222030890300d0f800c62a00d001c44a1402d40303115098040030070f204003080b1207200505180300d90f010b03051040301d441d13050008010760f504168500d2151a0001040018040d51125820040f0a0b9855056540341d0300d150040c1c0c2d001c00000c03207100c41c407411004203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 654807508 1250 654806258 654806267
    0xa050705010f050406050a02100c0c0512090f0f040f020a0c1712010909020d141b0612040219050a15020f06100504020a090317040509070302040605030403030f090b09030307 76
    0x40d25090038103000010040b03500a20038001c50141c0010302c0000202015283d00800012504017040b6034103111410750320b0300041040c0b118100459182c861840031020781c4036207e060358480c20001c1c21100100c400070040145102c0080700c095046940c3c2c4891999241d014002001501c2e11601e50192000f042d1500200d08151030ba0000b00c03410b01400b103540c0d0503e00210321411242001c102044558150001540b49254860014a901d1900350720841010011800d54250b070f010400d4120b40420340e405110241c481d01c603084650780101c0c1e00080061902e90700242545200d0f1040000d4140c4807004a514125650040c0140142d816031150300e05a04120304818519804080c003181e042800599003020200d000c3c0e00d124940105030301c24020312654002c0000c50300094213002c2600a103552511503481070003070034083c0d0011800140d00e54024000c4804907410380d40c40524580e11500c0441c000c200340030100c60215142c0c01c1c1e1001048040d0180f501904049000d59a6410302500103070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 654808758 1250 654807508 654807523
    0x25140d090905040206030f040305090a15110a021c080c010509010605040b0f03060412030207060501090f0c050313020904060905030c0105150a0b043804090606210e0319020a05 77
    0x310780364240403c00005032200002e580e00003100c10101c07070680e2120b180940b00c50240021132a0003030200200007840260000e03400386030f50800d0310f40700c2c100c0c11158940c0340c0340d03610000042c1d0085480988203d0480901d69810741860142c0c450f54140441400414292281038954030b41d00e070345402040c8814a000d1181c0d44200604549905002d080720340030a840f00002070000d044801b121011f805c405010350111390040b640300304100125a195089240180b0301402070071083c0780b609100190340760103141100d001d10340c0421060001e103900d60030840100c80042c01151100c0e1102d0f911400281d08101400c450140c038000451103150078210790200190403110144aa400c132482044810035500480d82680c00e00403008800c1d9903042200c3e04000d580c2204140928161000380f198421400040c1c02a1100d00c6e0041c030100765254030403a040425800c0c4c10504404034400303082c0182455000010b102020400d490034001100750713171541e8607e0900a0702c05600102d50034000c200c1c0c00c0c03040d01d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 654810008 1250 654808758 654808769
    0x506040204050d020405090102090d03030e0c030d09090e030d0f23150607062003041a06060d09030c060f02040509012c090c030303161e0525140d09 65
    0xc50401d46090001842d0707082c240c0e00680100c1d603810103d030f00d4003000e404498440c030010b00000020802450004d0003865040d802c401c1c3c40c09003c0d07545502d407802141d03181c005011a5901003400d401d120504000b004950050141c911080000701200030990040382200c0c10080c030006a0412440c2031000c00d412141c60030042d451010f0100a901a85080c80c600140000e9840075100c02d04c2c2d15210008044071250301c1446002c00c040c2110f0b5050781c0006511032849850f511825000d07080740c0500c0365200762945640010b0a0180000385290b544c444080d01c0c0c0a464040110a19900c900c01124030701c01c0a80b02480c1c00040a12107810700e810640e004207084403200d40d210f00100040509011260100d85c103c0314030700045864640100206046080c00500380e03960303400c0c2000c0410080070011240400710388060340c4961081c0803960b10031401c0e5141c3e151240303003918846090b020700c5032007040c00f0f41f0302c00051040004280014991588840e20704001d00078001c1c01700c00502402c949500c031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 654811258 1250 654810008 654810011
    0x1002180109051f17010311120d0801120f0c1806080a12050705100e0109030306051905012a0602070506130f0f03030f02070b1b0c1c090f03030909050604 67
    0x10401d039100c0e42c141c03850461000b0706200e101c44428000b1505540d0300014840312480b040000300601081c84e0b681444104102c81c0701c501f040081d0051504e0711045c49c0a02c000c10403d100405c1030350040150341a00521030051f034030302c1203890307501c0e0200320030150401c0c0c0f181d210160040b010603d0034071030100038014031401031008030495514043c100402802c40c1040003400f04104080000402030800d0405030110b05009807840b0060b0203009110582003500000d00b48030b80001c10342803070b644003104500896414134989e030604005540b0540320115440401000304020b1080000c0d03850311020f9180700d441c0140e9a030406043c8103103080c00240c00c8543d416075207600d1600085843c15440d14559200004004020303c5050030740080c80030b00c40044451f400002c0c05406c10006004081c42400010240f0940c0d80c1d00c080201014003803040c0d04a80c65120150f00103c4603004054046401054a00291540e8581044418030f0388507a2003100820456407084c04010307940c1c000c141d44203a05440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 654812508 1250 654811258 654811277
    0x80703061a070204090b01081f14060409050309040e030324100f0207360204051003150f0e04060605030c13050406061e03020102060c03041a070c0510021801 69
    0x20603104003400600c1409091030005040021034503250810002d15401000200e01b66075100e0860340c941450f908a121a41c10041007a07900304464402c5e00141148070300d402c0750503612142400010207012074107540521090024503a036130703114002c3c0520060f1300c001035912828802e0003481050310f68400c1c800e2805a030143d01c1000c1d100c24000c502c0840041c600310412107090301c0141d0900103160404000080b01643d0700d8080a20100060188188003820894107907983e5181000c0b4000ca00075254005141500400254400d4100522a80b40b925502d0011035651300300da5098145580a240800d124108000c10320030300380709140c0188002c1e8040c150503d001c100045074101c400741490b80a031344e80d401050a00405601c500301400903016408813410342004015150003092004a00502c95100040d041603400c0013076900650380100c00910403105a0008148040014417280c2001000c203018008245d04000c2080800880c00005035910f0710010309083d40100f00300751070705005a415 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 654813758 1250 654812508 654812519
    0x303020a03080c120f04051917130e010305060403120c0c080f0c06010303030e0d1d0f011412060f01170708060103060314030c010507080c0a0f170a0c08070306 70
    0x1a140c5800c56140c5041511681ea1140c00580b070b000e694003a4031412102c904010403e448021841e011324007400485002d00201038010402c1003081800030610300803039400003c806900d401070b01c1e05850000000740300e5a151308241300060300983c001e13182d6038003da00740300c00e05402140100c0c081c64052014803008480301000750011620700350051880000080c400600d4910500356411102d049064440344d5940b41001805068180072605081c002d070801c01d0b4425020383c4001c0420918403020320038500002040002c40d011001030f5074140039061859010442070742004024200b000c881c01070756402d000080c00550091042c0150600851602c43d118043c1b1120280b684074401c1e00e13100c0003a0b5940d10048000d48100e50005104841e2142e088016610100c040c142c03060242000300850390342c0d58011118000b058030407403021181006080034480c03050a5074500301d4a20b003844c1581d08a2f601d9200380840302221800d4009a60b409510b04455202d160b454100c00c1c1440c00f80b24a03810003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 654815008 1250 654813758 654813763
    0xb0f0c130605090a0302030d0c330b12071205011b0c0b100812070b10060f0323040803151219020d0501020c1005090a03090605031305032106030304030302 68
    0x1c1c01003a06110012480d00c5483e0f0720304c3c1e5003802440e0b0244c1900c0700c810100e180035084110341c8008560180301c8030350304100140c2c08166a010300c078607490f288800c3c2c40c00790010b20085c08c140ca6082d421564007555118840d4040008030006c0c815000440000c0440d410000d0840b100b6412100c1205880000002110341c02181c07120020341100052040351140240024100c0c940d520203842c3e4020230b204d4001c0041c00901400d40d142c007400320900c46135900404e6211820860003100003154030440308117502c52290707105000b161036520440c02c00410001d03468840d41d0b01201d0403141c50000100700101000c0c56515200c00640a80c0c0000d072403c01c1e016056141c1400c116202241c0301d4440545080d96500c40b0310301060741c0c002000719518200c2440407070300c2c1c6d200450301c548110f00744404101004400165840c01c241c041d0790f4004030794107080040b562984041c00c1003100a08181c4071101082c01840140681e04c4c400040302032080401d00f114801d000b0041406200350000c0c0010030210360017 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 654816258 1250 654815008 654815047
    0xa09120305030f150a0b1b0114041b0e1302010f0206040c1e05120624100f02010b040609020301050112140c45040903170717040b0f0c 59
    0x8a864800b9130740c0010300d1501502c01c085456000c1294600004c424901100038030030f2218036840804410003105065080c1d03000020400f1015102a0010f00410f890720b421b100c41d17115140f0340e1503180daa900401160048103461900e166801140c0311011907030410040d860441a038005402c90345026150010b4080d40e9210f54165030300106007401101c07890403030403c0a81b00050020080c200c210325515034460f411a01031150381001001e48444501c031101407010210000c01c9035100da02c138850f01700c59000d01000b60001f5592100c5078003c0960f140e0042202400c241a80180c4075813500000501298008003034800c43c500c1e000301e00418280c8202034640c001400e0700b44230364801c00c0130603c0c0190851681c15100400c2e5400d2168404280049000945604540d821b0f241d46003090400086540d0020700502059040040c4050000c0c1c030515168001c0309400e0146291071100c0c18102c000030121001c9a0f02d2418404000c0d00c228544407040d0070120003c211401c0c22001d00406001c0c185 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 654817508 1250 654816258 654816271
    0x1e0d170720070b1305090903030f0705161203090b2206110405130603050d030b010807031d011d162102060714030c06061903030818010608030a0912030503 68
    0x40700040e06a40040100c50010080c1c4182c440e55450b1081d01c2d0300c40164140640c0744141d004001164110000100b6a0f00603241d007200310f41203846c0d090040d42d5a600281103140c0c075001d0700140101003032003104c0403104155692404a614100c1c1c1c0b4000440f200f004040603400c1d81883d407128070860584001e480d2407079001e2000110001d483d07064540764025903018641c0010480403100c1005299006001180e02c9039040350101e0220507421303001c0d0f42400f05910300064200000980d0f99100ba040071180001e0b80f59041c94902c03981e441a404c1d140c000320111220300d900f82000d9a444020840c900c1103200300e00104801c3da0802c5c0085207500352206060911140840f20482595110310890b414154881600c80010000302042500c03a040720604007041d005500005010303041100c00407030109442541d031595203003036950a44050300d02038404042034060520b00d09081109118401c003038907098000315160f800c0020003d15200b03203904104002c4000c401050006600102984e4100a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 654818758 1250 654817508 654817547
    0x70e010915030e0c220b040605090406020711060c0f1e03030115020304120f030f0309020a05040218031608071715061206040b0106110327031e0d1707 66
    0x142040607074900010f039844185d00c000795000031010098140e40782c500804030440c00340040710a240800080341c00b0741c0300d0190440f100703a0000e40002d80c0b070f80c018018180319400c00c100301c1c501e20001c00d099800003440d80301140e000740b091000d540410031815501541c01807104480e20035029005880e400113104100c00110103801c1090040d0091080d034000d000102041200010142400c12903614651410780200f00001d141c00342c0c0310f1190141035081c0d07401400c40c04040d46040140b1000f540140803840303903c421030040707904555040c0081c0d100301c1040c050750001503040220040c1480e034241d220354804050030001440000f004510a0710940c100100d041d020f595140100e144004203020f147c0f81d601590003008100074100c0101c81c1039481c1c1e03030346d94180c071107444c0d041c641d580c414903800006a007140c03112030b0801c401c40d581240800c200501910400620008059800030b03607141c008070a60071070710598420b29486440500003031007036565403900741080c0d0070260866048001040150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 654820008 1250 654818758 654818771
    0x9111204050f0d030c09090515010509030106030b0a140711061605090d0606060e060c060c1e03010e06041116140732040603030801060509180c03070e01091503 70
    0x2081c01c0c0321a0340c00030660070644204206070140100200a984407904c0400c180b80030218101e9028403805100c1d814400c40d4980da40415801550150001501664550349805000c80080d110b5000d040c001d40b0b402d00013017007413120010350131850140102090108203e080b41080074040c0020307141e4001c0001c14803050714240c07580d021034481c8960b5146035009443c5190710001c120b8580d0180080341c445560348018085100704000080c42080861503407640070030007060343c048024006055200d04040d1504a030f808204808465070400d91049801d6801201080020f05060082c5110814020143c91a1070401041d450a1080d12800904080c14071400c0301103624080103031201070040d030400000664040c3d44808880c0894038100d03100c10b8090904100603003014090242520762540703502499a0902030115a00c0c0c021910306039104048211070012104181c035454040d181e90020310b5540d15103c8009000c0082d5120918100101c15404000b100c0c007811014004940078038022800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 654821258 1250 654820008 654820013
    0x80706170103200d03050304020a14061b03070f0c030605060109030c09091a15030c030109030e0d06090c031121030a03021b06010b07150c02031b0f07030c050a09111204 74
    0x4001c0c1c114410707134003d07070a03203842002e158116001d5407244d1300c200d94040c01c5640340c58004c0c85c1c00c030b10502041d030890b5050242282030a9035005001400103650126420030200352109800c402d092001511040c80c4280248140072541c0a81079114000b800c0210310350345580d545404000e928414040344170ba45502c1d4908102c0082c066454036034008801d05010304041d1140c4940c0c0510b000340d140700b8131440444121609045c000c45110a0f0507840345d40c041c1c602501400600325803044100d500507030f21002080052a4a010300340079500076807c160542074210140311003400c2280c8240306a14001c131070b5000f4054004215803140c4446e140158451800b03010410080b1540255851103008201c004900081c44402405145009043c24180310520748440700440b8005400200140c00400c040504c0e03c0d40e41c0c62400c0c02d40640c404441c58110340c43e40080c140030f4160012034081000d070608020a15188a0385405461100010030510210040c1522507120b6000c542855411070320002d8203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 654822508 1250 654821258 654821303
    0x50907150e0909011a040504120f020307080a08070917061603060b07051b01050a020601121a0f070207090209010207140a03080d0f050f0c1e0415030204080706170103 73
    0x2000d201901000392810041d01c03c3c1c0c080e01e030103200203162422004001400e0b18282c01018001c54100c0001883c1e85c94060044580b41070741c0c040b0005500c0200584400a1549030040000c40c8080d6a40259403e010800600401d4a584421b03480900307194031100000300413807015000820426944400517a41c101038011300801d601c11340400c007000c07840c0c3c4103222001c5407022546c450006c60f1100c0f809510010b643c0e41c042c0401c01070042c0e204000621824981d503458948503400b40144180e0301343d0750010300018403012a45c890080a200701844440b81e010051000580113090096041a58050000390344403084d10031044581d1009000064945624190401468010402e00d40d10001100100054105171490900707245c034120010340b511138003101035070044054003041d80c544000b511280c60080303120030020555100403c00015040f180142c40310074004551809600c5610f0150f40354140f0760390340c1c8105c003404040200c19050a4540c2c503110b040d240c2c8003030b08004000b400440b014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 654823758 1250 654822508 654822527
    0x5010827010b1017011208070803070c020402071110080c09010e0d02060423031b0405060109091505040e0c011b080d1d0c030c1c053d05090715 63
    0x54014503912040341c160b0380c1c0804d1010640000c01191000c5981c2c8981c1080c5900140c10007500c80341060000600143d4214000d58005c159481d1400c004029500003c00300d80c00040e00310b480840404036003103503040119040310307103840608000d480c5252800584e503079449503402c160f04001d5070454010326550303107260209010360050000c0380c681e82c0b01c0e15804d0500340c0b0242c44400702202c850400b0158a000a003604404000340403000545014a040c0005003078050507282c1030000301c1c140410307040309600c1403d03801019000100c449501e01002d10ac100c03241400264a5508400410017499800945494900350410094544011603080581050164100c90405142402d00c9120a68010828a03035503052040c03c2e220035690401c1003503030310600e0083e182d802040350f0302480602e811940b481e0641c14026001e03141010300700c6440001003035000030300c6040075191084201c0600b0201d80c420231940c200703c400704090705040c00a603036101418824a0440019041d410f15054801e492a1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 654825008 1250 654823758 654823781
    0x90314070b071e17060f0d05031c140f06030a150c0e03030a0801050f12070b0712020610090911120d0f023004080d050703090501082701 60
    0x49403100d429140c440c050721015245940011120b01803111240740091400306990b440d6260700041110240460b0304032440106943e0340200240300052079030b26100c0c02030b015144560095980c840c14802000d0b803028001240684a500d03180361030440600700001c07107030080d80710989130240e591800006480d0540780480105030354040656400034440c10380016601d08030588030b070140e207105201419928028241620001104ca01c010021801d00c2d0740703001d0f01c0c0900907141e400c80103890791040d40f07862190390200c00d1b050301c0050340009002100303a81c0e45c070482c4944007600c5142400307400050100034501035003068564071803054042101c1c000d11414580e101424842c2d070012100d45603501c81d000b05400c075022038008003c0c0a003542c40803503000039a03c4a0204200046440c4840341942c00e56020039001d040b00c20400811091410130504074904002e0740d038240d8a10251400130076420040d4402410b000303040040c1b00c000e480c21580c8820404400007c2d13045201c0a0401da030140c003248401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 654826258 1250 654825008 654825047
    0x60f03090f0319170f0a0902040b03031c0510030f03140423030d090b0f1305031e0106090b06071515120b09030a020a0201050d2705011b0e040903 64
    0x21261408152020358203c0c42a101c44054219035a00f0829840c1c0407540041a880d80c140040c020001036400354013000e001400000c0c12005800c08246103505c004405a900c1d1300d40300019030482c0050041c2a4064820201c003200d40d07141d591158500d07100300c44010180f040c80340d255540c041c2070505441c001c1c80705072120b4130301c0b66410194004620036072400c0f130b00901440554507a0140560b000b82c007104c02105007940351030601c04041c102a008034507000b000c05c040f200001919501005041402c200f00341c0711011b0921005040c40c21140143c1c411005142464055220b0390317101400d40720215040f81c108052450050018001031600000b40b040352010600040b0b076000134107088080715840f584a001003500c8002841c1d0f0307280140c0b1900710040c0d00400401c0010751190019140c12a12100c001c00c140702001f410049100c4280c0581d0012900c4030140707414030000740a00030b01842080c2d282450320303450b06401080755040e0b0f002180500c1e214403d010070188030f08000544050348040c4c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 654827508 1250 654826258 654826267
    0x80a1b0807200904030807050f0d05070206061903020d020f190602012c1903110105070c0b0708070c0b19110d110c031c0e0318040f0b060f03090f03 65
    0x100403503400c014420801c8003a5480307400b5102030401203240390041c2d4054444035816610514202da4503403000000e03203402c003018040080d040400f80201805005c031500900001c3c03400d60113010341c0d040010081750710300a000c401000940c643c039118046190b015a40e1000c440140000300d061f001400500600c40b409050000440075410350083c41c000c0301032140901101d50a41c6080c0202c0c880c0041c0e0600ca401c01d941c02845a600750112040c03c62090600401803400f03207007442c3c03c44602f02c48801c0440c254000c44800c201441f01c55503400621402c003030382c103818282402800c3c0c80e1103200080c5003050300000b03d0056040003c00105a80240c0e40600103012a8800382000d41c0241c0080410141064035000e003241e0040290303a02411904029400c201904400d0401500325007441303152155150440ca00403030f0140000c05512081030f132400e02c00ca5082d0140412111040032150b100c510f44502c000590b81c0702000c0b21910b400902c81562640c03621080c25046c80c1c010051903055100004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 654828758 1250 654827508 654827513
    0x21170a03140f0604110403020109050d0201180617180a14010b0307090f0b0d08162103201c05040812160210020f0306091b030106020f0712080a1b0807 66
    0xa01a101d040e083d04c081c004840344140b103401d94012800024045a1410310038000ca0502100308552240149482020f10720342d55000c004080040e00030078001101c8520480c401c0d054040c1c1c0a41020554030f000c049e0301312102c80c4a89892804500034040806601c0080300343c00250064440c4000c0102500c000a5440303052034018102c1c03410009650b4109103a2503601e2401840390168690420640d80c94021100c03a0480401c82d10342c0c0c2190728524110011407841140c1910326568080f54400103640441201007941680341c1e0000c40b820043c08000305d05042c0c003c0a2150b000d086a031001140540317603450640c4c29800f0b4403c007200b212102c0410080c0210b0013001c40154a2040d4003074139401d02600424100b030b80300f9980c050108400c204080307504d0f82081c683c400e03480740c5110030194107155002d05450566100f03a0210005a0265881c40c071000d01c28400c481c01071160b580300041580459440c0c11803030141500f0380090200e8020b030507500c0603030302c1c880c0244203900c291a0380d552801231 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 654830008 1250 654828758 654828781
    0x60807080708060103050618030708070809180c0d150504020d021b0303061f03020c0a0809040b0909060705031015031b05090a03110d1b21170a0314 65
    0x40c49440306a00c01c094000031002000300300c85040e00c3e0048054100e503070315402030014862090ba407440c05803208210500124081c64040c000240c46801c156680380122010008000c41d00c010580500c90034206100e0554444800ca480c6601c0001000c1440108405103c6420780a41d00494001e80000b500c0c6c404c480e0558014401c038804050150a10f0f0281f424070380c0e0383d001c111002a04919504c140c0c8211101101c42c040030454185409881c001048482c40d003081a10b03041202d40385808920700301603203014042c030200f500c0c00f99a100b0052809402c2c0d2951960040c0c020001e004000010400010745c0c5070b0034502404180d10700f181c1a10005000400500701000300c550410420721512030084d116a00300c507032114006103600c9001d400c64603020005081d00720481c0e4400c1c900c0040c007000560514200b10040c50750041010395034606030680e03601518402244030a08811405040000c41d80f001841415142d00d8002d83c03203011600082c0d009042d07042c183c0740e4290000701017110b040b000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 654831258 1250 654830008 654830023
    0x9090504263f01180c0908070302041e0f0516020c031c090302030f0601091107020d020112021c0b0406090b01020a14071701020a0e04110403150f0204151b020f100207090608 76
    0x100101701c2a00d80d0380c8103c5040a00e0301510400b0781100e00c0800140c90b007904503842c0f1949110910301c00546003c500e6049450322301604403a1625801007000301c000187c0c0c2a4a41d08150024014400c03500300001d86421b880e40d003c0c0c4c00c0d14513941d4000142807080b070844000d103502404643c07081b1ba1710090305643d86824400c031065070b400d000c50311030a960701c00c00f40c2e80450342c003421001c2c41c0d008590040d90000b10032170b82c04128a0342404144c0d2565051480500e0780700c0204800a00345003401c050005a50340d07908540f06150410354040b00c5642c1c002022040c1a800a0030543e410144521440c01c05030564404085007001c1541380707400340019402000f0304d81071603c03181030360348440e01413205958800180c2d080300d40d02403004001041d440040004040d021580020f041c0f001402e02e03000300d80054101c5d04a0b014220fa40c4050140c0260030784845107130285200c1c403203403002d500103032220401e44162801841d69110b0a00c4d41c17402001140040d190400302403100c141c8440d891542e5019 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 654832508 1250 654831258 654831299
    0x2070c0321030c120e250914010506071403691303060606121e090203031c0b0a06111c09090504263f01 46
    0xc030901048105010b03209540300040c03951101c4d418070301d0148541c80140001440344000780a05000480c81c400d2078080c007041080c50744404407005e0709201c50380080b5120341d140c450700d891201d4010710655031079500380c5503107503030000d00c0501500c00e50050a003103003d010447c0c18100800303001c0103542c1d81034450000038644030710000b0780580000d0260b018510000c010300e50594800540c00b803444c003400c0403400c8901c540103011900d8110105c840202000c40d9610a48110b0750f2030b00280311040d0322540c250591301d0148028041344031907001c000000c00403403c601140b19a01c80403070742152810300680701c801800641d0344e58082d80c6003003118064030100f03030400c0c0310328808803000c00c405019604107a244060f0100420007950b5026000c030029405200b45801d00801400000c0c642c402401120300c1140703d40b01c001000c1006180e04800900401582e0310301000510201c090308020b072540c0e6004020045525144c0d485541c03c07964400d902d02703c029070401c030550000c0f540d000e104061004a11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 654833758 1250 654832508 654832553
    0x40302270f130203030c0a0303111e0711060c0c040c0507051b0613090615050f07022209060204030b1003021e0303270f03010605010f030f02070c03 65
    0x600c08508810040241581506450040c0216580e6010107004680c001031035148000c40c04900e8002038a5604942c07500e41ba2680000340b80000c0503031600542017403036140240182080e80f2002c4120094100389440d04510b5404a08542807221103000502c48d0351000c2d00542d940c000e030040c1e03e9112603079100524019400c00030b8005190344074074111902c2c290040042c03d842c11030780c06504004d4103d5258994401000d00c09601103840c0072019000800c035100300028182c0c0750800307402401c1802045c1805101d41402100200400401111001a4100c0b92000800c10200b81c0c011311415180f0038140b0f15160100544c10082d603a070042055a000d40c1c030360707502c030b03034810001014201241c000250031200b1020b10300014641e1110390400c031140103040d40d01b4899000011078180c56440d0307200301c1c8030b06040c0a00505080052480d10240b5054000b40000b40c207040000c3c2c0600e03508000641055555410740102c0100307541980d0165a220124007010b582e03d0070040520b5454600312560b05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 654835008 1250 654833758 654833779
    0xc041b030c090b040506032a040e0606040f030b07030609020a030209132322032a030806010f030608060405030319020406090510020a05010e1c1b020f060403080f040302 74
    0x540540200c0b000c403064912103501e0030b810141444413503040501200d510380121080015003a8604903032100422282800307544492a002c2e88060440000d821540034600410050154144140284040c1c0381c001200c06170544800300120000c0c190390b40f1104000d4804030743e504416515800405105104444d448200707a2494081011a6812080c0301c01c9030083e51490151340148900903548548000e40d0412100c0f81c0351b030348841d0303011582d00c12030000e1503c840d42c08a82c154540582041440340081e072a84c40019034021340b64070b001404043c144251540c0103c0b849110360041d1001e003500e00207a40070b6040900d84180c0d290010b03a0000608502c3c002100340c100030601c29507046402d0ba07034a02c04114500001e01002c000d41301d15110440c041d0010810108609005960304546084005e00c00e640884990306041041704ac0c00b0410440d0b600f269070680700740403010390300c801c0d0115144189403440c000041c2880c81140c1c001402e100f404a0340880e600b10f441b001c0d00441c1c2c001d55940940 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 654836258 1250 654835008 654835031
    0x602041508060d060504030212030103060c0807050c06010e1302060409060602120c100504020a0b0c0703050c010207060e13090c0807030c0f03080703140903010e010b0f1f110c041b03 80
    0x100e100850b2420340219080150b00d0200d100c07508a01e402c00e00030300645902d0341c5040040150b6500903002601c0341612500b03145500395221145a50201d1a49003440c180744459652070386604042c403440702c541c4444008503418a00d1000b034620165802401d840d607031580d4912400291a5134803800700940030304040d00311480c0100084454542c0104003034441c02081c2e101d040010b010181060381c1020168202060400d1500000e046144402e002407460600e50701e44a440c013660007124604640002e07104016450308800110002407048502042da5192011040010028120b0250004800820010320340e603001c5507540680707000d00a40c80030b890b00c624510f01da01c0c070980b0006005ca00c04001a4021a00c14150703603000e02007003d0011301e40700c02000001c0c00d444400c0328240d0720342d66030100214280303000581501c02000c1510355040084040e40c2e02e0043c40724021004040c020101507101ca106400c1c81490b44144000b4020803200154420000120b101006c038030001c03c1c0740011000c407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 654837508 1250 654836258 654836267
    0xf03040e1605090a0303180b0f0d110c0a0b09070e07140a0c0c150801050a060203030c0c01021e0309010c03151203020c030111070203161202040203041a0406020415 72
    0x40d501005042619a11125a14549012041400700c200302060290b0103950780e03103030444002103029650303000c0400c004048503c9440c82c1c0340e00420712503508100a80c001d0070524162040756142c0000090500c41c102c2480b0310301d2041c4441381c145400740f030880c02c0c200103131001d5007030103140307042c0481d054607403034880804040c4410f40752000810b50707400c10a10364002c00760060102c1d004514141c0c160388a150703641c08070005103422418008903220342200c481a4013020082c01082d0850b800103506280c864061344034480a08101c02034a00001e0070b2000c41003d404a0b18410320709103841c009400c4901411016810039034101d8190b509008440c06098424007a0542d411400c0101c186418540400d540800558880171810f40c09405d6000c0c40c296000e110342d0f466030864a0030583c0d503901d03d00c1010b081c00c1012810400340c5820070828841004400c20281f007455040e5401aa6511039041400c58a150b8000c141200c5181e4130411041007800d0f0041c20882e00c01c200d0740151948401d00540c3c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 654838758 1250 654837508 654837517
    0x40902130803121605130b0a02010f061a0702400b010e06160b0c07030e01090308070b0c04083703020606090703060f06030204081005061e01020c040c08090f03 70
    0x8a0180e001d1012583c12994100c00708000c02c42d17810000c3c03904400d11410740b068003640d88120950384001c0b0b01e0002194080c040c0c0c0c144165450010889076007061503005000f241d41e0b80396450008041113000c11911a204420002c0003240078130940d1503c140303e1046210742200700091005040074072240d1104031402812107251058540c145003c00000c02d00102d40c200b100107040d00014140301a020a40004185003d00c0300892a0750340c03140c0d282000f5101201c4035500d0b1741005070700070b41000803a0515080e5441b00c0c0d40700b01400341c56207440c02c0494080c0034540100c01c0f41e008001d00d0444010304608008400900311406c82c2a0a280c0c1241100f42481c5490140c096000500026400d1400209613588103c3d14240054001d072a8108140001480d41054012980c0001c05004403201040a06c0750144010002e214a04d884804100c19444981d0b01000c405000d00010741540c0c001c4c8040c00c202a4080d03c20000c030240701e10014400c030400e45034500507014500c200b1504040110490f03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 654840008 1250 654838758 654838777
    0x105010f0603050603030909091f0b1203030c04091515020114150312370909060f030809040f0f1521120c0f0f0302010b2e03060b040902130803 63
    0x31400c00b01701d40c7c28401c0c101c60081c0178642c0390040040d030803280c1d0b0301003a0445100904600c0054040101c07014013420341c4403100500c0c0386074018010000d0b4005183d088034191344003d800422101151441031212108507007180c003a15102e0b0f110640403590540c0840740e81d40c1200050741c3e0075298003200c240160252141070f13805030020700110b0884010742c4000c04001302d4403801200920404480c0704104410044900d0241540d211151105540116640d00ad408109030400c0214a01b420303103c100c42103440000c150b901c0214049110784d980ea84800040078402000b8400c004005141e10300074203000200f0b400010702c0e210081042c8030f20020360224105200c61f03800d040450b5850f041e1807203010921000030090b80380d41031400240305040c0548403501c142641030030640a4a40a402d4403410321549019500041022651500c0148164000c01e20700311085e4076039034007050483c00341565030003111220100240001e2107080720380c001c01c0d180b40c1c151503a0f20345946401c0040d4607842040601c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 654841258 1250 654840008 654840013
    0xf06140d05030a11031c0f051b04230a0306022205031504020607050618071202060307050708040317070b1e0403200f070e0c0301060507150603051e07060e13050c0f0c0105010f0603050603 82
    0x20320011848000d8685100b00301c0220150340c0d25038bd400034070000c2e1590421100b2a4010810303540040c1e908040165481000f80620349407410a000300ea9602c0308292000314882004020a095440303910880b04010340000581d20103140903101000100354002201030341d84500d08000601e0860103601c5001c6a0307004008919540744c08000b122950055607007603440c0d410400000001426244000407034101c100b1403a0f44a01d92800c0419800e0302c0140090000240540a0420342d60000e82080d40641d15080c0320714140d0071003422200741044094288030343c1c81014590b02c1c102d40e00180e101704442602c2c203828240d50728001c501400f0300003031040e0804a107051081c1000100000405c85454040d0080010156526154a46010f2844c0ca1800728802c2483d02102e04c00e00078071020000c0c0c501401c120300c03040725200208080580d02d0607410b07001741d610360205189400360003c40303100ca000d032603070191244d0780f098559000701828440c40c80d410041c00f60004680d40640a40b80c840d0900501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 654842508 1250 654841258 654841267
    0x90913020a1509140418050a03080a02070f02040c020316050c10170c09041e0e060105030c0f1201060e2401140403060c02100f06140d05030a11031c0f051b 68
    0x84c1d403203c125808040c0c0340e2280d2280442900c0d803464910b400704042c0203500501c4182d0309414094543c4501a00c141a0b81e8010401c1c1d401141141891040c0240c1c103440000e000b1455540c200e003140106802c0c0c612441c80c1d10550170601200080c20361071454101e50751005008a03520649600080c01003811360600c070000000e8100c1d442401404404001801c00305906001560a10035900c0c404400507001d80e4594107440440c4c0b08100242c0904001c0d4001c1c542034110702c00089603401c0c0501128400c90392030314a1901c0340801c1d00501c004200540e10094103041040107102d41045602c20301449911140c06d02070300350300c2030100d1000240d00352441458075003140c860390040c020202c4000c0661056119515000405206d80c1da20010146400241706080c240d200281090954802e4807890203000c1d4080401c40100c1101c00d04051802e1140d084000d0695a50850141340d4004ca0300d10070413888250a24602d40000d440350652210401403a550b24001d100070b0b00da9000da01110000901 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 654843758 1250 654842508 654842519
    0x6030b03062208071502030a0c020c1516060509030702090f0c040e09010209030601080f0c09150913050a0c0518130602130807090606020106050a0e04030e06090913020a1509 76
    0x1909400c0e2901491010f1314001c82611010b10b0301d8002152692110380c0041040806440340c411803c03502c03140d202030820b11070f41d040054101003040c40103075001324000980c0d2a219060390000080f0b15488501400309207001c4020f6a125005610207074040c0000030001034a02c1c94a08000c0d10414800c59503604050800c207107000187c400800c2c0d09425903080020001079641003000768003c210300b4006041c81d481880081d4142030602580500621a000501c100d6440310445080c0b0010107030f0f002c01081e0354024001d00341240c0380c54007804500030544c0301d80900c0000b00350344055030003c1e20380300c0880d80c06e0418240c0a141c1214003000b01c440b81110b07400041c80640007000c90b0044a40440d5205440d074074814109100c56020103003d960b80ca2080040580a0140c20300404d4201c038001c50091400400c40ca848030000d0005040005402c5c0108041e5114810741e0030341900582034403403618025900c1108801c008005a120f007419040c001b80200700a4804015401c2d0355075948a0719103440e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 654845008 1250 654843758 654843811
    0x5180304030f06021209060a06060e0f0f030114010617061c0219080d08040c0603110d110f0c0a0c0503061918061401060305070c03092c0106020706030b0306 69
    0x82c60221003580d000c0041c80a20f5080346881da0148405c41d000d4180d40c100143d07240101c40c1c1640c404024850340340c00403c00da55400140072285807099400100d5280c1c0100020300502e44800640302c082c06070070001c10100d074890722481e1901000380034804952078940403c1b503940710304140301c0d0405250b2075050f00113042c051001d5a1003d21800c81d090305036220811a410160a01e44c150002201c1104002c1804041040c820040c4000d040801c94030760750490786005485000300003007c0c0c0d80c890314032000c4120000112540380c48400c03c40360315180034002d803e49a0341100400d80c1c1101c060075000c9008d2801103480d40c041e0741000100d035441806035002d03e000c7c229011410b2601c11a00c030002c004038400380501c4207145001b0105a00d41e44c140389000e41110000f031705203002c2000c0103821034000f070b41044100040d109401c40c07980240040c10940d908030020729103023649c1d080c00900000b50310358001500e98103894164406200100c0340788107056403002d04807101131400200032880c42c184180b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 654846258 1250 654845008 654845033
    0x9150f060e1f0210060f0518100f06030b040b041e1d060a0501150c05030a03050903130b09011407020303030c09120105100608090607080a050712051302040518030403 73
    0x6000541c0d2620500701d03140d2250380807030215000d07070080c0c006105440402d102c1c6070b01911b4846000681c981c101000f0460249540d1041000f482080000c51520b40044001c680103000c0307660311000e020746800c0c006000c4c244020602d03002c1c90501180d121203141500406030011030781841d602414a001e400701c03003d80914210502c1171101c038209044003410a00c82944200b450707407030200e02945400c0c05071b43c0c0701600c044041c0401c0b02000c034810006402000f01c8820b4015071501081c4c0f80c5500e030307416003544103201d107000011240810003c1c0da070101e00003401050314241c076902c103400442980004c0324854404020b5042c0c0040000940e1900500040e050380980606105032541c0d0b0700d140700d804c48100380c0d05a40700d00103000003086030f140d10001565008078540c000c0c00b0607042044001c1c20006024005d505c100f40c1301d41c0010842e520905400b0b0944202100502141c1445e0221450b03e0300e40e880280d01490a2000050704004030382424001a9a610b00039407820740f80d510f80a910601 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 654847508 1250 654846258 654846287
    0xd08070e22060e01080f0303150114070f060b01020a02210307150e060a0e03070f1e0c090605030a121416080306030d09080706080415050903030109150f06 68
    0x420020341003070900d20214182030403498040c0001c02a080480c48a0042e1050340001003d0380181003a1040f000b020007560f4000c20402c805c2c6403010468001030b00c00c7d210b8840000001d11001c40d690050040003880785011500805003041910320b400012078851503114000703500855440c05088900346002c083e59240b03407111007600c6c142043c50340c40388105100d010040711030b82d445a24a201e484018041d451b00301214180c02c0010740c0c0706100c25510b90151440c042c200f44c0465100c802441140c0700100c902c1888007040704200c401d20300c2d0641038003101e401206504c40c5440c10200b500d00f80041e1804020341c001d80301c0200c8210000c8111084591a030b40c04400000031302081076242c4001c032441400380d1203407000c1354072482c00009152402101d000e100f010401480c40c00c2180b59000300b003a8003035071400d00c1d00b50402d07500c600704490442006c2c0d08144486152000700701061b00302001031416100211020710228000b50084203a0810030f004507203448040810401615000e403669245014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 654848758 1250 654847508 654847519
    0xf0509011a151c06050d03021b0603040c0b0a1202030c0a080f2e05030307080a18030c12060e0a030801322815030b09090a110105070b190606020d08070e 67
    0x68031a00411501821b20030110b025074004200201c00082680400d014002c05a544504501e4552903803c00c0ca8094422003200304800505580e40b603204a00201c62100080c4003955039040c011003005e410340c82040c940c0e0010b0700030070100c0c9410780740300b00c4e003800b0f10209044800003103901c100c05100810300342e1200f24140035410002425413001d20203080014025103c00341c6070561000081d19241504646416030813415500744009040101c0110035501c111880481000d40d41c03400038010441902c00d41c408d44204000d0404041e40002030030b0607560b03450741c18002010350b4060b40c0724500c41000c030441340c4044080030444038207001008a1000c1b10907441180040005031760b4034049140e0ba04040d541924a58600307411a800d4010444031300000c1c0c1d00c2c549940b074003132240b41d00d8030344809004051040c0f04c0d80c0c451160788107505a0f11900e401100041c035600704107440410954002050940490420320005000c900210341a40300c1c0700d007503e941c2540c5d590800101c1b00b00e42c224041c9503010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 654850008 1250 654848758 654848771
    0x2090310022b050a06061e030b0609060f030915070801060810030f03081f12020607020a0509090109031b030e0112060b04060504050312041203120f0509011a151c 71
    0xc480300b64a0710046000024009050304200b100c0401383c48041d00702e07405008810f0000540e06a03869a11281e4515600d40007900c4020100080c04c1e42c4180c0240580c03196012461403205401c41004501984980741102c1a0070041c147e40400341200300c84c800041031680004001d90760054011640c0540c0c2d07030500300d92040d12903840c0140b2440c0c007802a80010303020400c0002e4441200c000034042080d4424210503d8503200c104e00e25081100002800751801180c0c0c5021501d904080e803001d400000e2860020745000e44140d1300a140d0b10784290000342c0d4061514500049036464540120b801d5603070782429800010045d190080c040f101d98000c2a030303503940041c0d582041c0c0f0242c00607042655801d030384c7c3c40c0342c20300301890540352071410345003090100010488444d0580c0c4405115615041a45c0c1080524040000400503181e24031800341c04c00c010002d101c24107601940303100c800030204402107001ea0041c81826914803020030a5050200001004008200201c101090100310b010480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 654851258 1250 654850008 654850057
    0x118080306030c091911090303040b0c070f06021b09060f0906010e0301020c0d0e0a0f05090405030702060304060207210503070507020307120f1203020309060105210a0b0610030209031002 82
    0x71410226141007070714092a07800c0c0701e20540c1e802103040781b8408030500d40c00c01402c400001d441e8400c1d8407906042140004003018502d03420b101c3e42c8010301c030800d0744064581e0b5030390019450b01342405d0300c0d40480c14080c1c40040c036481e089201c107000d250058552400906450140810188041e00e040e0503c01001c0c80c0e444280e500340024006691494064445011300310405400300213060000344c031034880e0540c02e120202021201030111030089070300c00126261400e105055114811001e50400d00010410060003041d800418181303120b20b40d00910305801d0b0301400f0580c40c00b204d001000440810103c1c3c4540c0c070540291180c00d0000707040d90403060380c816240c402c00382e40050450304101c0340e01212091000050f20180c989500307080540c95460200007141c1c84481c14011a88074070004aa94003000c140c8411204144410400700c881c082924107041c0641032084480318815031125040c100020300c41e00a40344d6006001e401440c40b20700d02071581e400794021903030104490b640004594170 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 654852508 1250 654851258 654851269
    0xc0c0b09190c2603030a1503141609020a020a1106091915020303010e01030f03090e1906080115051309020a090207030f0314180c0a24020118080306030c 67
    0x49551290b1034aa80852501e049075405403d94180712181c0084402440304050b004400c03654401030642e40000c0c12502e500188210010580025100d10120240092074080c0041c1c0c07240407044001d0401d0f03000d6500c00812044e4401e42c40b9060041e0400c0700c2000c001030380405580c2d4142d0b070040155082c1081c030004250041c138000310035010b0380018401000b112043c01075005055038103201551942d8144030300b030510440184001000b010f41c0202c01c07028540308400190103806001050845810124003070342c144000c110300c00d1010352604400040da060144140d1031114518040544450b10303140c20882c0c00001c0c084580b10103a02d410300c90f801a076819168801a18148100503103030030007403d00401d46000340c50168141880c00ca02d541c54440300319a1a60302450214410514a8410458070308002d8100041d81d00308861001c086583e2941c8044020140d4500070340100044600504030300b60741c55804001c09401882d007015000c80c804c0c0006507400b61025044035000c1d80004003080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 654853758 1250 654852508 654852553
    0x211401060911030109050627060118080f06060a14010c081201060c0614040206042310210501060e1c0b010308070204050907060203030c2104140d030c0c0b09 69
    0x402c5080000040c0700b01e118521032107800180a4445c0c16050b040d02d200c55900e201d0382103020510018050000b15140e125440509070010914194101591ba6203107140d81d41000850019182c054075000500c6818986031440841341d05602d01001014810010b5403c5181d031041501d0841e000c00040354181000d0400750b0003842c040c0d4507101c40820908126040b0350780c015500528240c00e40a0201680c3c23070708251002d507224282e444c54602950040c02894109100843d41c00216a80e0341d04401504150f055aa01c204041d1020000e034040d1001021034809024000106140d446018001d061000c809108840005008545140103450348620f900d0241d0088a17189000101d05046007481d0084540080c0ca400081c800c040c2000c0d001b94983c040240f130400d29000100d0b4200c84640b02c185580c09205003071031000d009081504040214881401c1424043c1c801c14801d1610075120b0320548031142250340e035201007001c0b039655181d0341103009800d800340d070b01c00c4410120b81c04c85000c01c400c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 654855008 1250 654853758 654853781
    0xc020c01200303070f0f0c0305191b0c1a03040210140c191a070909150e0a09030801050d1a0c04260601050406050d11150712092114010609 61
    0x81c03807035026000b0200c1128910740340c00c1018029a40e00020b800c1425610b1400d03840d035060042007140b08007181d00c040c004032081c00030400380f0405024864cc10074402c0c103a9406c10380464506005100e9444170784804e545c02504450f81e84194039070148100464448602c80d050194682700081c95400d03e0301118490b505807809010311504104440141c1d00d1040310510840801549008000601a2440e40c440c0544e5941c4600100003c551400c19010251150840c0c141c020b08103594800c006010b844002c4011400e2040041824684044c12004955010005d0940304200101507a04504080c1414041c00001c1c84003242c0b000006030140d20f020700f040350140c0c0400080c60062b00d404010b91109018600d01134041c00142c032498000c060300e94110480f000100c003401c0100d101c1c0d0350406040103146801040305c000300280c501e8450010701c0da503900c15020f2500e55041d0703a600001c41004040d0034000b03128580024003510800407201100e18000039090f60303111241000c0c2c0742c003560300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 654856115 1107 654855008 654855017
    0x6060d03230c01060608010f090504020603010614040302091515180f0315010e0a061a1b0a08031306060e042406050d0f12030c020c0120030307 63
    0x45502c0c20102100822440e9620b00c0300500c010740c01c1c09041d4103c040544001600d0000380034240c0515001041603145900c1d2000c02c0e18509104400e1100c0074506110003c0540c0e0f6801409204031080ea07551004251355004000595449100c0c4408100040c465410454031040c18140b0007242511403042c0350101d01c000924003014103001d0060180e13a0400420300b8500b00c1059800707041f4840c4244055600c5042100a05440315040e60081e101844210046104012151150030313041055403905a00c5440f00d44a40d40211030b81820280e52216407010040c00b803050300d004052820a24480e400d103640d551101f10f034880d14030301101d200d08010f02428465588244001e00303000b058900c544549223802d0800001e40702041d22601c07803e00402003041c0c02409017621460055010f41a4843c2c000c1c015100010303100c40000c494102103516840480040004601803407440d1503 = true := by decide +kernel

theorem cover : BRFrame.Cov 654676258 654856115 := by
  have h0 := BRFrame.cov_init 654676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 654676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 654676258 ≤ n) (h2 : n < 654856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
