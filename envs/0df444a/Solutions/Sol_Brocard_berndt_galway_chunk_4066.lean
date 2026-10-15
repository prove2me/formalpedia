-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4066
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:28:40.497866+00:00
-- url     : https://prove2.me/submissions/1240b6b1-0eea-4ce9-b833-7b3de83d2e66

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 731115107 ≤ n < 731294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 731116357 1250 731115107 731115109
    0x10905030a1205090d0c03030210020c1b150d0506092d09030405040e0d14040617180f0f070e0105010f120b03100f060906080c19050d0f11090103150b 66
    0x112131070031071301910500001c1424101120450040c0c48210010311074800c6040b40101c00d842550b00c1e03841c9400180c05a41017100680c00002a40d59030305a01451064400c0000303480c030001009401c40980c2c4c0070500e450144104100400c1c01001801c01380104040c510880717032900100e200c0203482408400198450007803da2541c0a9504001d400502d0040d51250b41c0000161403a1030113500d558001030240780c45d04003450b601481c8100c2d008a103500c81c00104141d01c0d8003803280e100c01e92103a483c14599200c0505460084c00c000794603000d070440c021131200c0b0002400180302030842615440e0701540341c100002e03c1400c4144121042010b00340380082e240440381c0000e0b014040c01411201d206082812600c02850310315459000d06240042c000b55400cac0d00d0050741c0c11201420041d000d036070704030818003c400c10b8035101d06c0c3d44881d15800100b115a104507081c03001501440c900c1400c1e080614110b07140710341e2800315a100717a009030010000541c0040f00000e0740038159a010809000101c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 731117607 1250 731116357 731116367
    0x3090d030e03010c030509011514060a0c081207020d02010603030206040209130606091e0608062e0e07030606080907060327050109020f0a0f230907020f0606010905030a12 75
    0x240c041c95143d42031890300d003c075982c50740080b80107441c484009c012100280484100c5081303684601984010308111480c00d40c500341003e000345d420f03541815542085155a20b140c46d1340109284458840742c2d200740141039504201381c03482d5481d207000800c201425610003941da11402400244100003074000964500a104002098907074000000d001e403e0b00d400807000606003044803020b50f000c43c0240310546c54980c0c001c140858000102415039600d562000a0303281d80110001b021618030000301419030240100b45100a00c1031000781d028505090000030140c035841d070702207820000c0c000c051100050001c14020b04503180c40c10300151a80000c3c003506000c0302c400800e0000b180301082c0000a000c3c6c1900402c26441c4202c5244c040040b8503000c1268000860140d004140c4090780240495032061004011850804060400304002c40000400d501c2c411200c001c016040f5420413901c01a08005058110344242098043d0034184000b190b50780780c0e1104003408280e03841c0d440d20341761400360b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 731118857 1250 731117607 731117627
    0x50603040b06063f0702072304060f0f03020a1202031e1e160801060b1c020d062315090105090f12060702060924040302010f1a0109080102070503090d03 67
    0x44c00c1c1c42c02d07411114940000c5000e800c6000d10801c0c00441c1d0026000b9840481c3d8101a601c00d049586050311039000744c80c0d082800000500d400541ea0800400c0b6907410301007000041800b8082290f060341140306000c03500d0300943c40200400c190b000f0f590016070b004102940c01b200c1c0c00c0040944070a00780c50007881c0c82800d403a0456124040215441c1c2e50401203103000c5040e80500d4110040c50741c4510440c00c90b1400d02c11005141c40c14480000b2145c050344182e0340100ca18800540bc0040010009040303a00591280f098040158909264503c007090800740384c4108444194010601c04122080c503c074000c01c542c10810b0000350442942d40321184d0300d1b06030030040e00c1302c0800040007540341d80d90308061300e036a0054801c4c4c000281c54245e0006400b07034646006c40c0e044074501d01100c0701c1e20050070b000d0300c210159500d41605001c40303075041c0f09501d480082054008801c81c0f1041c005000008a0b410260459004214034000700d50000111070080030f0564616000070f00b0303401c045071003080c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 731120107 1250 731118857 731118907
    0x14060306040b12070806090724090b12220b06010e190905040b0f090d0518040e070f060206100e0910020c010203010603240b1303080c03040807050603040b0606 70
    0x1181c006501d0404000900000b80c0da541ca0071a0302d01e49030f07241c7d125910b4150b441000c05084802c440c1c00303142040030011010514003800c00d07154180d02c995001a0755000050300c9403500f01c00700304200300d0040b07034080c6d0a121a822900c03c960808039850342d00740900b0081c50300d414044070140900075611140030480402d0840b00b005071250351603000a00103000c05031010b031800e000202c00305000404128805000e09403607401881c041c030801c9020b0382d0710741003901404880100b104009a003925180105505460294080c01c1c5040c10302800d80d944001d541c11a0085602a4003004134091004807154141c1d031030b0441d002d1080e582c1021292920201d0410350f0310207070011031442003250781500598143e0b501d9440921018040180e20000d544400502c40e5031140c0543c8108140707181c40b401000c40540c2101850441c0d500c03074540001503800003030781c910740e41c2c0002030401490106000034000f0b808102c036054603506042c0c448240b141070240035140f060500103502c42e5013021480d101c0c003141d40c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 731121357 1250 731120107 731120119
    0xc05012f0307031e020613060b120c1003020c0712060912050304060b1c141e16050d08040603020a03020714030c07060e010c0b09030412050d0908010614060306040b 72
    0x1100210460301e94010210031004113200c02e00003c1e540c203400b4181264030b4401d13402080c05540c1e0443e61800c06152180907107d555442000c6661611440c0002c007006030800000d00d241c03441082400412000341190804040c8140840d0a030000041200700032181c040101790b100c240b490030614020044035a00070300511092034140d50752a00300000d14410350140c1010001d0909207c01e10203140220b10610610f0a00540f00c0c0300000c091941c82100201c0705002c4544052203080d010301041c0c641c107415019907100c03001c038441d2030302c0d44e10114010b45801c0e0b51040c1d5a80d01a40c5042c246e00881c02207505250300802c5d020300c03881c441e60513102d840307410000100c00700030000c000740e80342e500c0b80c82007003282d0050010100d2024001c40046003c1c5d00180d480406400640c1c0702c4202101001d0300b06d1820b4007007008001601c54055030000c1101f0b010304064403074900f265801503c02c0341c3c940d00014050341094030400107964803001944070302c6025501e840d078a507602000917004291191201c0d901c11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 731122607 1250 731121357 731121437
    0x50702040e191b0614070f150b041b020c060c01020d0504060f05091f0209010309080703030c02150c04060e1c060204090b0d05100c0c0506041a070c0c0501 68
    0x400b0350311003881000c3c00b510b521100400036180321680c2d5101c03409014082200f840f03481c0703040d1210000421040c2d005038603208024016a0326100c0e1542c01000c980441900e482440a20345418450124031000916404e0081d050b50100030f9101e00130000c1c0341d44500c0b4080349443c1c048030300390110382403141d1091003000140750600d402d900520403404110051480e100004d8084c82c0c0005001c44450700001c10101e41011a4212201951015000782d04040d140d980b00d10000701c902003d0f2400718440d0b00c1c041108403d41c5402850250030b448507031000d180380c20501c0b04000d002000c40742550001d1420349480000c204c04980e0542c09003e001e402d03600e004080c5024030640c0d5000d4000c1c3c1e690600f0500c51030b15880c5c100003480a030010003078015004800005120320203544154801282802e10300181803ca0311307a17900741101240e00b80c4030900c099404055803c8c0386102035074000c4031800d050b80850220389658103400d00d14084c0340d043c00729100d080207500720350349850400c3d912041d00c54040d00d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 731123857 1250 731122607 731122633
    0x2104090e0d170f15011106101508010e13020d02030303090d0e0609060f070606121202010c03180f0c080d0504090507020304050d0b0403181409090c010906050702040e 73
    0xc6500030445000111001c400711040b90003128124014061160502416240c042031800104000440241880004a80380c82c440c076003484500d200d482660002044d0910b000f0101e0300c8004008003007000c00c8113020041c0039480c00c035404503070420203103800249202e00902c0484c80501c21007a000e58148404010055074000014102d2111880c90390368070b5540c226081400039074045e01944036800103040c403910380da40b10a00302a1000601504010400302d69075001c5411003c2d0b1800c0503181030344610603211225409004075044915a0320b000c007e54491001501c907040807080e070047c0f040e1000802c03a0188a42c440036840a8141c4201b07a5100002604010b050b9a101d80f09014131641080e00084181b8008000d0b101150000f924480550882c2c0d0b48200135480c00078022404d1248041110106003c054100b0b40a44150300010740740d44164000c000b038a030b8005100a41e60350021562180c1a60f005500034111800d5040c0542c0300c000c41c0c80014003603c0303507150740101c51041c00907074220 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 731125107 1250 731123857 731123863
    0x301230402031602150601020d110c09040f0b0105090f0606030703110a0c0606083c0313090506040531060f06030c0b0f160204090203060a020315040504052104090e 72
    0x4420000e4084840f840500c171604c83c000b2a0485005001d6088883e121031264001c03c4541001001c0a050340c01e01100c410000d004d50704261820344160850048502c01c00c55245a01030140c81c00711043c0000b80f400c010a00304900c8024035280c000d04012002c109190f010341c0101c2e41901c1c050308aa511289001c4005090080c0204103641c0f00e41003140c0000e040d5000305010001007414441d010840003400325500380c1e1141c0007040300d070b6904241c1c2103070700c241828409040c444a042056803a0340d442d0000e8501074600c0900918461803800d820b110341100940303020441807416062000c00000c3c0304a04103491440360b107020305054113110190324001e08903401a001d907442640140281e68407060009124003420300c2c1045100070800000308510540d04405000b036200810100e0040c0c41940403900f484000d81d0b8102c3c40c07503004070131701c90105061449003903a00400d48041202e85055250030b55110010540d41c03240301071040b1074030071040700300007268060074071030030107003c00079100d081c0c560303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 731126357 1250 731125107 731125141
    0xe0106111c11071215020c2803030e0d020714010903061812050310050f0a17060a0c02010c090506090604230922021005040f09020c0d14030123040203 66
    0x40703402242400320341416060428401d041e000b142942c0d0401280d107a0000a41c888480341f0290320984284808a519000306182080035070286512050300b1881c0c050141e540b58002610306400c092626020a640055070744100c501064161440c6d403100001610b4089243d00301030440b6003046002146040000902501c0e81d228012510080a070140300b2190b50000340c450042c2a01e51700000c000c0b078035004c010307070110345402407220f004150744001180e80a4864914061070350409000c01c26102003901c18410f403004140000c1c42918910000148600e003030f0301845200d10801702c0c503e0500d1300c45005603000f0f8185a0800f40410f4480169400c0c0550b49415003072292081c940000c017482c0c2000c588411144151f200c0140e0720a03107a0801907000010b0000c2400c000080c040000c2c051203403d4054002c0503601e00069a4400c0001110705140d10251403d09000990f9548850071018508803030440d2402d6034400207070484a0b000d80c4d1031240d002000c1d80c0c00b50012080c02918840212040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 731127607 1250 731126357 731126387
    0x9060c0c02060a0f030632090c071415130302010605060405100516080a02030d0c030b0a1809080a09050a08011a0603070905030a08030712060f060f0e041b020f070e0106111c 76
    0x2907c8041c2c203410440410411a0503c804010500c20f880005201e54151155034020304161444c2c00c10b610780352040494202c8080d01c00d1516a080c1005058083c8a003401a103402d8a0042c0740030b0500300070801c1c50f1654040c410410a0020f9022a500421240303c0b0780e16030b01c040960350b03c0c442244001e40e207801c4404242c001074640070030592558024441e06d142c15001a00144829242180300030a008c80b030780034001c1860715921281300203040c1c0002444600030307684502c0016400d103c103026055006411980481c0c2c1340c030704d44000c070781d00c031007403046042d101200d08a0b070b29990b0850485191245510103a0107118000c1c00404108031100650300c00c002680c0d800c0d41c0461568907003010b513212440740250960200d802800090300c242d40c45605d500442c1009a903100c5000d02040c100e64131104031075600e10700400c140d107996506000da4013070016000c0c024084141440c0f07600140c22410301c90181845070316408101d0f01241400402c040d10408400a03881c007120443c0a0f243c3c0c3c001503030807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 731128857 1250 731127607 731127689
    0x2604050303040b07030204080a030305130f0c1a090906220507050307030f09110907180e07030c020610121a0702060402030f010606021e0a0c080109060c0c02060a0f0306 74
    0x130b061036100c0e200b6203040341d00c0702c00100986046601d00790003c00300135100d43e18070090602900089541c640001c48494030840100944030b1070800b003c8214400d9419841c003c000410421901d550346440303954001c0740450b66500a240349105002010915940724600075040c11f0400040c00c0d001809544100440d80341480810501d140000803140440300c0140060402c8001c000310f4180b0009007036010380181090306070303003401801401c1d0181d41580102d4420b4590300070405143d615016088501000b4001001c80d400c1000c0f1358000d0b5096030003600c5850284003d07410612032085990381c50160340d504024914181030b803000b503c031032048900364001c0c49201317204c1c2c02d1014148111021100c0720341c0902001c410002007201120700c0c1c0401d10815105021601000c103060070b144000504401000103000c00f12440d182007641e041c461201700b0320912002500258072004111010000180340240c1c0c1c004075884140c0c0200140e03005400010b03000c0c0036504006456001d6129030090310716003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 731130107 1250 731128857 731128861
    0x30a08120f0f041713090501081005040209011701020f160212071404050c070203010c081e01120b10030605010f0302090c0408071e0e100e0609162604050303040b 71
    0x10501001c003040e10001c40d072206482c0041c0115080c083c00c0048070b011000c400d07282030a581c0a98031030049540158111039942d4004100e081402c00400d28100e203040c10500051500b90000341300c0c80300510920285110450313601d40b880e9400e45c1103581107801c90311420b484185d045140040501c00e0710049000301074030b180e511041d440c0000c03410222115050500340c80300e400780070b010260002428110000c1c00901080006903030a000c0c40741c0562150b0340b080c0413450030604d016407004070b6480c1041e80001e0400117003c01540311000d4034000b50011100110344c0c030740300708808044d4803036807010b00f0320b030b203004004035484030829443c10459000711104840d07a200c1c0a10085d251290b0710407804181d008040410039800001512441d0130041070080c0b0080f540c480042c124020101c6a04050380b420074030a0022640d2074100b560001c40c1614514098070300402d0f00700c0b051100903281c80c1030040385060f84011102c1882080311341800300314480a40c1c206843c2c00c82d601d405c00e4a00720f54050500d40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 731131357 1250 731130107 731130121
    0x10051504090c1409222a09030c0608040201050d1d0d03020421050304091a0a0e09100f0908160b06010809331302130204050d1b05030a0812 61
    0x2500c80030462445580f80d1400250108000c40d51009030034001c000c800700c85280c065490355218140001006905001c81c152000f00000007070b4648500f4982401031810051011440d01d01d130754800e8075042c2c18400c005460702e0005032a140038a440c9403454a0410a2452405c645412604c001681e500d0031141208400003080d01640500c0c000c6106190780080c0741c2010000c40c0e01030243e05070081045d24034090304c920440e0161044000c101c0101c5020802d01c89807818400003513801403c40e0400d6440c5030a105018545681010307480c4040c05844170b0004072000501e61160300166031003040d2554803011013a41c0e820181d00594161400c004100005203194020035825110700f69850141903038028003803440d8003642108040c07211181032101c140c44034007114000c0c0f0340030b05003510000034180c02600c10464035040c805100b140340380c0103200801158940c5400c05030100c1d48100d031940c020903d29200040806245c2c003030790f0325210342003480041c084808010443e082c40b40001d21050741c2c81c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 731132607 1250 731131357 731131367
    0xa0201060303091208190302120703140115020607030c120905070509090a0803220c0e0402030709020f0f0d182a05060307080403031d0706020106050f010e0910051504090c 75
    0x703002400700c5e40d0802c030100e5070850a103107001c8001c00d1402d0050911240782c0070b1000402040340d07040040395407602d0b095480c852840722103004141c50b8200002c0c0012007140203403511000b43c0904145511a0742000c4001c1c09401c00e0070049102c5031003001a00c440b810042da45d010307644030384c5010300e5030b18006c1022400003003080810141c120803400c0c59608c500e402200c50160601c00005140400c0044100081c0c0301c41c41c1e24010b02d10201c0120355418603004050502c0d410340e0044040760720400c00c84040c6240003041c1c9019060804640b80c54ad40d50b00c100f000507000000f80e81e542c04812100513020003400d40d2001100307035104241c1903000d043c41e03000c0203d0703480f4a008441d40038800b0f1002504003440307820b5556000e440303890081032240e80e40b4800414030b403855460b8001a041080e0a00015a091184c40001c010803501591010350131400038018034503842e60140540b1704130340020851060a10700800500014012005421204c0c0004100e07422a014103100c2c2414141000003051040c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 731133857 1250 731132607 731132639
    0x30a02130f03030504051509090a061e051c02030a0b0703090302150c030c0702040902130506010e03060c07080f040e07050423181b12040308131502130b0a020106030309 74
    0x44c0c803020301e03060605040004412605002c040310980810481c421911081c81d418050b24aa80340490583d0500001089000000f00d02c1e6001c3d00b60080100301554074040c1c8420703424602600b128980d1180e0011a04041081074090003001d925828484020ba041c2e0001c5980c40c080d50039500d001d44012a1100ca500080d01c80a504020a10101d1005424007000345a584d1000b07100182d0886294040b40580000010410b0910ba0b01d408001c40c80d40c1040c0d40b017040c0740e011800f03043d40e803502c4203940d000c9000c0d00d100640184004580341d0440e401c1c02c022140541003c0045900f2071400107802001980b190048403240801d034002510940c010608092107114010100001212503070100c1441e0230004145125405c0400c20784021040c440c1c0c001d0481c030320400b0314424680741505000d41104c0003d8908404d8a05140415011410300301001c0c404201400c40903907900402c111103210001c040e0492070140b000014003542c0c2c5030b0150f001c8005c03070344030383c80d6007003900c0c0d50317410260a0600d2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 731135107 1250 731133857 731133863
    0x4260c060f0a020c06240303090604090c091d1006050a020c15091c140606130506150406020a03020105150a06030207051608070303021213060f09050303030a02130f03 73
    0x1060300421a0050030030803041d4804044040141400300c0c508016280001c2920210080c5a4524090034100c4811400b03110710034007503004526060000010810791310451180b02c0c2c07419964008444143d1007280702000400459603000055803400c0519080214241c80c484189054050006031090084050750640c0205802400a00114005001352414000101410781d20308100c003602c143d445202d01203940c00800c800322000c9015241c00034014441c2030403540a07600c62410081166141610340000808902011070507840721000300d040e1070746440c00011403d01c003240104102d076000445501c201c0c040d0703009100580300c2c000c6051203c4000341105400400c402d400b4003626010f50000d20000e0b11480c01c40d41d0070703150001c2003c24500742d0b4101d04115000340c41c04006050b41080801840401014003d1500d00303941a034009040d41c0e4802c91081c0703c900388821f07603014054003101c0001c0c00b010301965a24a44039103a400258042440062003030b112131408900d103001100414181d0342c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 731136357 1250 731135107 731135113
    0x6010e07020d0f08330f0301090506072a0602090f0907090501181205011e0c0c020d030c02030a060f0c0801080a300e151309021804020304260c 63
    0x1001c80100c0304044000d201d40c2003100d0005c00601200051402c040c4200e9114400b00c60080c41c84040000c0708140c0c1028a11980c14a030212021420200d0555009000c50511161a05070903064010503002c002d900c002d0040070900d9041070150540080044080449280e444140190100914201e040e9800400240442c50034851940200350750b2075856088d016503440c0c580d542d01d150403442071010045035035035120001d105000ea42e00c0074003a901d100f41c0c0800d009907407038134030000d080c4603148102038820341c0e54603c803200b4180500c521b038401c0c60f00038040c0e0361107103502d080140140c150104090312203403801049203040c91044110303d0603104c00d80c01622000c001610f400f01031501442c202000440c07102c1076a400101258248000c03e40c442d01c070340d60500070103410030030503002c18a055107d00d0003c1025901214102540800b5551042c5005840d01c064022070310a0000c03120b02650003520002c1400305021a650f610388207114407000b0580003180300c0390f503030103540901d0504405541c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 731137607 1250 731136357 731136377
    0x60503010213062111090a0e0c19030e15090606030a02130504110603010602010906061a0a0f030209060d051006020321070c022e050f1806120906010e07020d 69
    0x511441c42502e2400da518850000142c0014413103040300d909030f05804030f16200080840b00e60a000a51000501c02d181d0440000e280c0701c880f8495a1041c00c2003480920700c02c0603a071500368001e0303020840c000015411104098009901840b108200340c2d1405d0a0703110f441d0000d841c0e4a40010f40320380d502d40c0030300400c040745004696000a840003810841d41168818100c0c04240c4580f805140241901c0c3d00115400f0164103084040f11442c0e000705400c111a00501010000ea0408031884213880d4604480f0264a1150890003401100b6000d40c0c131000001d481602090745400080c0164429480c550b401603540b401aa968403a00282e081a05102d454000210301000003281d03011240e4144141c410034160f0000c5c0311500c0c08001085185c04120f8250b03800c1c144904c1400303503840b035824003500e00281c4200e4486107008641078110021002e41105103a522000d0130b40d00940368a0044210f0b5083c10f00c5410f072118024043c1a20046d40cc0002900c0c46200080c80c03002d5200c16180e640000d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 731138857 1250 731137607 731137619
    0x30409020318120a0e0a030b0c0d0e0102130302040501050a05012003040b0d0507030b12100f02160c0317030606030712140103050c12030f0318070b070b0604060503010213 75
    0x103504000d094090000302d09604001c503000a010000041500c060200e07660301d90804090205099a41c01d01d005000c42030080c00002c1203ca515504003c47c01005500e40c0401c01d81d0002070100c4081c2c0d2240c0754004110400c41800c2880c0d85416039200b19000e0040360388440a1150500c1184511400515041800e02d0b1003500e0200070801850740c1c43c1903a01d03081d01c48900d50142d910410300205180c0e80e5800300301c8038680c50322400c0e110001c11aa805482c1c0008000c40e0f5039040364241018400d50342e2982207010481ca42d04480707000e41403902c00c4a8444040c24448110502440180c4609000b9042c001c0481c078000e045038460701d8020480c0c0d0864480c810220382d06003a440c0404c1c9841e0380c0d0780e40b100181c0c400c1010b46008502c64001462000b00c0310050183c25000e4506820440d4000e200f03c03a241040182680c0d4000445428800c00420310380d902850692180d01064401c81c0004408081c04540c0196a2140c001034400b07001d0380341e03110241402c078881c5903030010326004007440c28010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 731140107 1250 731138857 731138861
    0x6010501200d0c0c0f0b0306040e01091208071b0b010e0906090a080904060302060319110c0715020c090106030c090b0a020c0120011a030d0c0c0b0a091d0405010f0c02030409 76
    0x407640513024014886480d0349411500305445c1e0031a450b03500380030040099526041c09450740411244000340208101650341c00844501e20007008240a03580d00041d0320345106220000c1c014418014a80303c0c4640d6040c150b4001000780251810700b1030420020b090680005040750050300f410303008200c280442e403201b40c1c0542250b1840c560242e11510f0000140e51030001550003500c2c80c4000a06451096507900d084a0401118004500040c008207440c22004901ca01c100c13035440e28510862848840100c2c1404914240346601424000c004507000758103034004042442c168440301c04180d1114107201403070185000748801a4401e200c48080e6501c01d5030580d50000804140390390800c00000f0b81802d480d0341d4510b042d803042c02c15065003183e240400003810070011364109480008900e44a00c2c0b028182e0b4003c1c00f2403d85c00045c0702075075501c111103010041807440d0391940c2c1c1d6130340400c91208518081d0307410340f103660030010b040850441603c1507480003a095001186454a00640100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 731141357 1250 731140107 731140127
    0x603020708090901170705011d0f060903010c1d032a121c03060b03040f020d050c0618030f150a0c110d051c1404140a020a0806010501200d 61
    0x4100e10240804001525802e602c3d60180010030001030100410903c1d040c038080c035590209040008000e0140502400711680711003e841c03c1e00c400c0c100e00780da140410710500c10300c001075800d50300e4030000c0011b0650020000e42181502a180003c0381018801c0681d038043d141003204528100070b118415000c0880d940d150100d0000e04624800d0015901190500c0362101d42c0510b940d02d40603062407016070611036040940f910403126411030502d40c6900044c0c420343d1300004c0c010b28141c0240e60501504000143d00e40d440101555a60881206e05807200701100040c01c0c020302c0f0f8810030441022011540450041100704680c2e00360742c551002c00f003e406452159814401c50742600641004184680280b4000329168682e4a8003801500315408500300c007150b003a1850300e41c2c1d0400d409100da11150300103821064100080024540481c00c000301244000d61252500c4c1c0c0000c2c0070103000c25400e04030f40003601c2d108441c200c2003100c16806e0a0b055040341058104500712040240540f041b45 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 731142607 1250 731141357 731141363
    0x20c0609031215011e0914010201021905130f14010e04050f04060c05090a0305060f09030c0a030c03050408010e0601260c0d230a060c110316020f2808150106030207 72
    0x5e2001443c00c10b03c0d010000c101859800081d01c032a0041c07104e4103500a41d0541c0500070310003185801d00d8001103a500380711070800b00d020444002000003000d90386200d180090104c01200c1c030303403017070390345e46e070003400c01c10000e0501c2c046101d103840300b1498a01881507074810440320401c00282c2d50745da41c66100074200c502c55201804014450f082c4941c0750076090303c01440c4541e00500c2c05041060344c0700c41640000b0000201a4000c00880300c40c1c41000c41c94884440c0c2c541070036042c1ca0800e2401750750302d0050390401c0031590710f852024036058000044060481d18184003500010003141800c140c0c82c2c0c8508009940790307002d552142e841307081c19100900e03942d001e401101d5000080c9014280e6504030000b150442e6403125055a080c803c0b58800c25400c4000760624500ca04c0781501155100d00135104030001848003181d00724199250740f00c5401910000500014421107000307803500e1100d00041208000c61018207003c07034481c0c000211201d1071007107507070b00007001c0c0c0c0b80c018101c000e503006140032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 731143857 1250 731142607 731142617
    0x40c02030c0109030c0b0609162307061a01050f07030503061903050a052e02090102010b03030d0204240503040f0f06052502060f011521020c060903121501 68
    0x42469880a22402405504c26661040c9480359424102620680600482e110f41200d07410700009904550341210706800700c0c01c0040c2c0381c1140e1407041c005201018051380c5204000183d05040048079408420b40300c80c8605072840001c40c1500448442c06020300c0801c10500030026500030030702540142d40c0c040c000500c624062101900d050f8001038141c0e001312a1035200307207a000304010050260444910a240c2c914440b160383e2607442711210b4141d0900c1112550000364612180d00c01e4102d00749280d000f03000c82e0b90380c400441c1150001d521911070401e03101d094039010407404116080d0032a407200580c2d00c0c1c6045440d203840e024005600494112080a42c5510150008005004c2c0d41d2241005001e60f054402e0a0084520b2409042001004640001003000120a01054054107540c441c80344030340c1c03002089000340c42c205942100c82e084515002440d5034030810a07002801b0044107001030700c0c49500d4081d2010364038010380c065417807010b2140380042c612407420a18200a01414504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 731145107 1250 731143857 731143867
    0x50c0102040b070f030206011401050a1d090f070e0103021815070506070309231b0a0b0c010b010207050d1203090206190c020a12080915040803040b04090609090f02040c0203 76
    0x2c02c01056000c010229800345603107503040700349601800303003a00512524200e507820105100008001780b013240d00c00014481000300042c000c01c011060440080c1010300760364000d007402c551901c03404808490a80000740c4441400e00c45502c00e000342c900410149903001108400d00041140039000302601103090a403e10400000c02c4042112a005042c0c42e20000340d20012070414020742101c1101c0244000b0046040303d900c480000f6080140046d200385040071400000001030b01c100465020f505418008150a8610705040d440000300c01001d070210764205548006020440805d0f0301c01070f1180c41e44401055400b4000e4101055251004002134940b00f154402a402c02c400b04003040000b44a000b4900300718200f031550385025250540240465111039501c1c0311841c4111480c107402801c11010510554907000c0581b0090040b21050340d894035190f85071455036030080c0c4280c483c190300708440090095000c3c400c02e80076a030041144200c0c0901034080c0405000c84e0062542140310401ca = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 731146357 1250 731145107 731145119
    0x303160212120415050c1602011206080601081905071a12040b040318150c0c0503060c031605190c11130e0705040b0907120b030a2409050d050c010204 66
    0x209518000b000c84604103007001e0034580d0700010b400c0310303020129182c00709020340b10b01c0460030f5840700c4100e1b181079403119405100413031f80c04e41c03807000e1485051704143c400300b100f130b0011801c18103030b822460407151011648510311646c1d01c2080005001900000c1d010700c8004a01103003c0441c0c801d044081e45001810301c040b0000800c111400d0300d9420551082c00100350740182d42807040242c012002040d20708004000980300100b400c40c60030304c241100440104203000c0540b40c000e2000406589036450310704079250566204461400718800f0342020b403840c0c140200c3c1a1445240100d402509008080c0c07400d4500b43d8522070141c400f05030004d240001a5079500d00380d00c500700300103404034820b0000340c1194a05451a00071500c11707800c0503a11740030f5450f603046041d480f883c3d51400d110b100002901c08001000d0100303005401d405540a600d00b070041c45021a068209011508045080084d807028119401d08030010a1a045403910465480c4114054042c40b5021400185400d81d151 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 731147607 1250 731146357 731146393
    0x60603310303060e07180506070f05060406020c0f2a0301140a0b0301060501090308030406051b0309030a09091509052e080123040b0a06030b1503010c020c0303031602 73
    0x400300314006a00c3c1c503002e0202ca9450354140f50844207a0804000c841c02883c2c00d103c13442e00364001c06024590124000051196841500340c0603504001520392504260a05034065032040d5210b41061040b4903080351030040c00159805503044a81d03040307070a40e500c100e03010f16882c0d140f42d413298103640b501b80000c0711700d0038603407414011b0170754241c0080d2030b03030b0311200b8503094812951105050101c0140c0c02c1001c5040001140d40c810351000f00056250340708041e0300542c03680c40000400310704001c01007010340b01c000801400c0309081511425800daa59000c9178007a03e42c9243e102c54204014181041400c1c03058000540042815890b2030341170b10145d00201c500c00120300300d561094103061080012600a1003654090b88034403440c80c43c0760603107180e503102981003e48028a00d010f284000385202c030b0294050f1000d554041c040e007500c1d040501c0c022a000b4082500c9031b1080d480c040d05503c0b25400003030301406408003d00550308680da4842ca1268090f20f410f140000e60080824968174101e0750 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 731148857 1250 731147607 731147701
    0xe04060b04020d0b0f04090b0609070309050601060504090b040605131d0f07030c08010b06071707061d07050102011b180b070807060b0306011a0c0a080310030303050f060603 76
    0x50180001c116130341600300300e10841c81c1400343d8052803404081002082d0302002c0c2580c84003040d2011516901c44070811001059202c0713014009020707000003c120507034020010400c5444005003840603d514104000440301503104803988242c800c0040410a03200f6008003e50101886080c000000400c5409040a83d5040d100e015900018002d00400545010b004050464400200009e41e407400101d186481001d60107000b0340c80c46040c4024003056181151481584144c042c01000c0c0c004181c0d0b4009000423070109a2809488008903042d40305104404620408090713110301c91200400c161200452686400f22800c0c140c10042070300d4000e040284002c500c60407046640303550074102441212141c01c0258402c1c4c001c00010001b0b11000000c3e410003c2111590507599050080c00d107280001d1002c00a018074404010043c803191001c43c06800c483c000d0314244011707540c0c1070f120a590310084440d80da0080d0107002251000340341c0200d000500d8846a0703808100b1200c4e00200c81e81900c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 731150107 1250 731148857 731148877
    0x607060902150d1d03122802040905041505070e040222120c080109020f0402210115020705091306020c030d2a2309030c0613060305010518010e04060b0402 68
    0x1e4540c08151280b004482200300c8544501450030403a04240301626250302a20046001040004981061f403000c80503005070368400d0700031951a42d031100c01002805040303038203460801803403039018004c5c950303030051500c200000d6480005030a505810040250032a030034202070569411040148449044c44d900080c000203400712405014500c0c1c90706945c40741d5004240c4030f9052441590040e00c0d007160000c03503044210360160b2507402c00300065000f1042c0c00703000d8119a101e400000b66510064403076071035040e45542550a05a1203009204010000b6103c400e00d4020010b001408682c2a0b07025060036181e50041d02d02e801d4102030380806813018007661540d42880348034513240c00301c40c07414101a400500c0c100340c454400d00360008031245400e00f049509204000420516981d400e1100500105004121b25207074100c400b80245608158014503001c86d01c0c1c140080b41c140f8003130844020140c405d030f5014595030708007224544480000761084030401e071030782440d10301c4d51340300d001400b50610 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 731151357 1250 731150107 731150111
    0x8070204060819030f110a0309030203010c1d060705071509080105060406140f190f08120412060f02120f060108010e0c0d09020a0302030321150607060902150d 70
    0x10900420003103828036030003449107a00c01d014145101180e002401c0c803880d05401e00c56a00740c40b42c1400c2c2c4035440540301c1e4500340d0007050f03844020940c0001c0f848050f68001c0e0020089945080300c10740e400310782088115070261086003a03070700c2c41c50301100074054907118100ba41c500e01da0301c103030700300c040250080000041403500d1000d0020342c03070911580d54030a0084a0502c0043d2070580720709010480d070702c4424007420041c55008215280d21140305841e41c1800302c840081c91b9210341a91400110380a00060b50003401080034071030038180d0075101681c0900c2d441c6410070696986110083c40700b0141008003e40030f200464a45038402c803090711070106141800300500c1e2a0300014028a4140c106104a200e000144025401c1c45015150241107400c0001603442541c00042c2401c0c0c0580e000940c14403001070f40c00003500407801c0100d0803d50f070030382c0c4151640314159014a6908440803094001d04280700010110385507800120302c0074009003080030100000c010342c1880b684200035050310b482e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 731152607 1250 731151357 731151367
    0x120f010315110d2a200a0203031b070b0a030c03140f0c0d0e030a1e02240a02090a06080105030d2a021c030305150603270c090408 57
    0x12040346454101c0c54080104114110410b0444041c00782110012a280c0e90704131003d40801401581401400c10501283c641c1e00700420080140c41c4035134544403c0310380d00300b0441c4240000101c00c8030030fa5008001d1070401c440280c1000400d030446a03507003018421400c00107484050700c00100a4196940e50104800806410103019070314056102c0303492640c007208004603c1854841c0a401c0b50701510810398610302050307004081e10f0a0103003c95140000900e100ca40e40c2c001d034070807012400888594104500785c89040c0c1e140d00c01c0f2088a40131840345a1744101c044000303041554000340c1c10000505100400c008503590482d540c0054010031f100c84010b00c41b030b180401a9181d0340e5010310301a502000320710802c601200807244452551a0750141490441d603a02034454808039070a03d1000c0c4403903950600401904041d81c101c0003440005607240e107241003c204980c4254600842070068400b0310b2031141d0000c0c0503984c0c5403954000e085903c60951364050641c0c3c081c0703020307400042d222 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 731153857 1250 731152607 731152613
    0xb130c031b0b0306010f18090515030f03040b1606140a0c1e05180604030f1220030a18080102040324020702130b06070602070b040b0702010b03190602120f0103 70
    0xc4107a04110b02020040c002c001c007982e40461595803001640ca0000c08072a00ea42020440c44026007080792407608240030410009000204120102c0c0c0443c11504103030304607114581c591003580240c85840c901000102603000c5a000201300c0c0307620034080001e840128002d1009441e109031038000b031064890043c030703260030340c02881210004404008a281c0d5800110081e00d10b1046070b042c0c028240d0003403010701c41e9a655005807001940c0003051050741c0030b11890001d041c02c209000e15404038402c22460009c090940c80e40904078540c60009624010310305e001655410314a41d074044030038000300e0740420703040002c2c00a40015845200e07844032400c0580b40410a9604040400214510500103070380541e48160001c003401c2d1141c02d001039556001004107234a480b031440084c101c00e000090700d4080100d4041c009100754001d030000c0e419134903860000ca0030781d03a400301c0c101d41c036511202071902031502d03882d500c1031981c2c81480010720744404459000a0340c8002c860107150b102190004000b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 731155107 1250 731153857 731153903
    0x2407111206161107060c06021204050307050106080318040b030a060c030b0901080a0b01150c12080906103f060b0307080313060e03030d0e0303012607030b130c03 71
    0x2101d0920305109400c1c050f0b986030241d0300d1180f44508030070495403510b4403041c03000d258100c070f1203040e41038150303c0702d450241840c1c0c0c1e40c0d40c000041100e6540ca080b500203844080802900c00c10040c44210680c004d82d41030800010b895420780d6982d0600929007210001a090f00c10210301d04604e072004110026100700f0890606016030003440107800000c8c4030000500b000c000c03075040d0382102c095030210400c4403104482c0e9140a810003420000844070480315140c000f42a60f206a59100403100c0940d24010855152030452141000c40e141d40007603548050100c51101c00c88402202e98006683c0b0310104041024244042c10b403009941d03425401800d04003070141e00064001c200003145000510300182d00c2001452041c423082100804420115036000e2044401c0c03a440d01c6400c0c006400094415502c0358000e01c80ca81c0c00c60819605400c0828800c500c68a00e281020041c20405d4696262180441c80044c1040031428900c09001c000908071101c00c0d0166014100200110751217000c0054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 731156357 1250 731155107 731155141
    0x1e06020105010302060f2b05040606090911010807021005100e06091302040518010e071e0807030618232a10120216020a052407111206 59
    0x42164180001800542ca83d5030442e5143c20346900103e98501d40310380341802c242c8000710080742103082500d59004042194004a00560240c00200720855440b51b05008660882d0720042012a08059507011503014501842d8400114019609940c07081505601120740841d551600140440c1d000d0010300002a00c5581c818010384145001c2c0c1480d0140800c402c105040091065440b0800a0501d80d4401d0800c4101c02c01c041c003e0210966051841da01c50002e030086200035100c5481042c591645211040b0031650360f500900305080c29501c44001405a040710101c25010030280b4800180b009941c0e84a003e801a01080c0514a4540c0542c01c21100e1140b0105121502002455184506020a4200e02d01322442c4000e85c6800b001650000d01c03480d8003100d6036102003000c1503684040c070a06187d031032007140e140f80141c0e114010000d46140b0400d22109580c806c501c00001004070000524032180102d40c481940c040e0100012403e110340081d9a9030f6410180c00c1c00051503e02500007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 731157607 1250 731156357 731156369
    0x111b07140102010c09270c02010e060c0405010c0b0a020403080a0206160903020603130f0506070c2603010e070309060903120b0a05101209021206061816030b040f061e 73
    0x4002010541d0000781100b545001310680c02e00c424040f041620148000640f0351050403c00340302d5441f4140c000390092903134000c4600b8500614000030072a0300d288040f5415294161102c641905190b101c40e4084007000307100390300c007950801c030200206100c0e5001c2d0000c1388082d401003c1a140c903010f00340c011304056074440144091000300f40700590381d00c2d081d00c0c1e1010150161092211039810004140c00d2005409000d5005d8170007841446a840300d400b01055004105100c2d441404494443c404601c402c03090100711000d000501098011346da410b50012424a00411108056100d0608a4030280c201300c0200c1e039820701422100400307001e076004140e821120401c0592514010030044203841c0c2021042000300c2c142411a042079030310414480d40c01402c001482101c01c0ca005075581740941e4503074443c42c040302c2000e40044002000900c1500200703102d00556541078400d602404140e680d490344103440f101c00c448808203600c121402030251007040c219404a62400c6027294002d6007000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 731158857 1250 731157607 731157611
    0x61926040c060507020f090613110414060310030201140c1002030a1a0d0602030c0f0c010c0e1009060c0221071a07020a030f1703040609020a0603060810111b0714010201 74
    0x90050398030403100c06c20140050b20514419600c510010300110b52101003000d6031803070000c0c420b0b010680000a002500c00d00d2892800070a00c020412820380001c44400c3c00e8503024140038401544074164440080c2d41540c091401c0c469420036541c00d00c0448081d00a2050303000c4100304080318079016a02d01c6d48043c0700f0711003001e40038401080144c0e0314003402a19181d0000045001001d8003011500c1481172450350540707520603158203502070958019407200269000b00442403034a440b49526520100603115941442c0c6072400940b40380030411001da0317002901d440d50000c8881d180c12021041440f04018211560a00310b500300c900c80124440c00c03040000303006800c010b84a91005d5020b51f42c100c6109000c4020078900204455264817100200b03642c04070a003c104107031508100f5010388200c84000c5219107400c4c0407812908107104034481c40c1d020b070141e150b90703000c10340c0014103e01e2503020251a00814070f000c09000c0329003d400842544c8101c008110000401c400030070303030b03440910003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 731160107 1250 731158857 731158867
    0x6050105070807032f01150608061e0613170d031517120c060a11120a0504050705030d1808031e0c0f06040c09050a0b061926040c0605 59
    0x1400070503020f08280202842505490ba441e84941c0700d100101c0410b00c4821102513a1511403545e010340502ca0460326034070300c0724001059090040041d00e10440d000f90040c1d61829801c1c40c2c03000b0040f49103034400d40000e010010807070ba03988080842009408140000011300c000c03044001e01d885002030349003040518245c0b194900010310f8215404446144c407043d42c0c080401422141005225804101401c00010f0484000078000c0b03440c0c2c5c0324100c0140d00700080320038850560b43c5403054689854940384000300103915040310b50701c40c0740c000b8004c50460b150a611030303020929061100da03140004c00c207aa0b100031060200100244040c0c41494090b44c2005020b16060710b502d0220391124284c0c15000c1000e03d0900c004010800058412a0480e1000e003000d00700b0b16811225070150800f00ca05090000760042468040c143c4d407107402410883ca04140000d5121100e41c020f038840d420841400d01884031050520303603c2d0783d95030740d4201748041303400c0c185400c4000e07004d268010300a000c02440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 731161357 1250 731160107 731160113
    0xb0906070c200111061f08070308030705030a09050610080123040b0712050703060f140d021306030c090507110a080d0c120c0f0306050a0302090c07050a140a020102010605010507 78
    0x102d0000c9000740501840b84604400503140c403103402a26003014822101004062820b030050707440203420040445000365203844072591100c1d0301d400701402c904c40407c0402c0c001441000190343c00301c16a2400901189150780e00d508120060f01c200e0000d0103a0301003480b03500c030203114620568558155000a0042040700f000403140020009014498900d001503580c034001c0780c2c00c14003500d2400d004c103c6840c00780c1c0090001e00176400b4844440f00f0042010500f1070410b8442450518014003402c01b007043c0791300b0002800e202305401444262152000070000303151588039005031261170800719640c03401c2c1d440140b0103012500803410980c07100c1d01c8440495a514100c4014500c074030400b01c2d07030700016802070b5041d03415540c941c0240c45c07602d110240300750350054018442881c60741d41401400d13518020084011031a000207544802c1c220003107140340d62044020420140f1602c2500c040404a0700c2c0c5104212031a40b00c00d102d500064a90f000719070303083c03103600003411003400e02a080807001c4d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 731162607 1250 731161357 731161373
    0x80f0f0d0f1a09010e1506130e060121050603190515130215220b27130f0b030106030c0305060901090305092106010801091b06020c01080c0403020d0b0906070c 70
    0x840340d01344420100d030224011b072000c01100c1c408008041d0a50f035592092800d0340103011464491100e17480c202001203522503115000300c481d03a0b0380356103955481e42c0000b800007000340409011a035240c420242202e40f502c003800b00303600d0f000d4080c20184c14208000c050040315070340010003025440340340b9030300d000060742e8104007029045e89188090380c807410024254400c103c089200501c520b40110030000350f110560000700301300500f04008500340241600c13600780c00110112400e6101d10348410010000c0c0d82c545c0984a40102c2500c08039420010501190858850f908282c4201890000600c14403004010098109a40308000c2103c2001502c008003a0b0140000b1640700d2a82c0c10b80d025121400d00760100c40b14460311066a0242d690398500500030428a54112001284040b064110300c9a000040007100c00b03640161048011080c011100c80d0310080c42d41c851440d0901010001d1389404139070302030061044401550300e0412840031891728800030861001c12421103036a00015800c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 731163857 1250 731162607 731162609
    0x6020c03210f0a03020421050d0e010f350106090803033c0906090106140f010c050f03030a06090b0405101e2112020607050304080f0f0d0f1a0901 64
    0x100e1001c2ea100d0004403411030181c440d507442007889000f040c038900b050440d81d1042c1c0700e415114030220750414403c0d800c196034107080404c41a001c110f201a50010f080c1c00740300c1e00203210b009515406502120b14000301840d4000c800700008480c01080140680d680090190010349400e00003941189000002280754001c0701d007da002e0302c03060070034141d800c009e001c0c040060151412441c41c0350b860030071025596a401103c0143c0c296007131000029407580c030110004c5940201078a1078030152180c038010741303081027400d0040b1102c3c0303d5001034140440c000e001550003503c9034100071801520300fa40030303401c2c0c4002d4004503201d01c0c503102c20b00c01c07540490f08401f4211040c68290440705002a40600030285956000002c3d50704443d0041e045100300c0d80030464294030507542c80c54080c002c0f4104070380d52981181c418000c07450400103e004110028003a00d14584804c2040c2c0c548804600d824005812175502086079503102d0f081c01c082e8a1503401190080c1b03114640c822149420200064445441 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 731165107 1250 731163857 731163877
    0x806120c0123070f030801050d02010503040b06120a0f0b0a1e0e070807060306031a1e04050109020604060302190311070206090d0206030115030b1c0209130c06020c0321 74
    0x10b80c0b284001c8101c281d440403049000828420750b100c41142c1441031090a100c2c1d811400140721000100e41481c2ca20200a0010f4040e960f450541d80e850756a00740700c5002818280e03002e040e2940310001450200035404030135128000d280094421841c104848420240034800d070a800d01d0318a440d0b2404603544001595003200c0045104132405c0c071034500f020b000b0307000a0280c0c0a031181c04240181c26030080401c40c1e2161010000300c0c440508458281e03241902d050300e040f44d101d651900c032100700c000280d4215008000000d05c60344e01e039000401a9015610600c0440c0d00800c408074101d40c2401001e009031800e0806001d81d1420f0820301000b485080d00081c4964004580e090590301c60b64408000d150340038003595606e5031540e042c24600e03151100854006818941c1c121180c4c01e1251913031a0b00700500301c0d02001e9140f03940c204190940001c008203014644003e0b0030001c60000054070000b4421030f0050421034900005060074034840018461009041c001003c0c0c540c51244100c400b201c0c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 731166357 1250 731165107 731165117
    0x2a0c03070e1627060e090c0307210c0c050d030507020309010f0909060308091009050a150c06050a052a030106080c04090905010515010c1109130609050a030806120c01 73
    0x30520020b56071040d01031600c0d419811441c41d061a1110748600f40e5095801d1600c80c4281440041c08110340000c040300c20405070309041c0007046030b40d40200c07030080f12684140c10640d1850b004031040303011140700c0c0070400005580494420203001041c00704590054507484c0c2405a480d00880203907880c0701c0d480c503490412080a000c0d50003140b10301280b0024040d40ba40a0002541d6414015515000305c94098031405202e12400300c0940100c050300110385001c1d02d200011850070541065011148819000b48410200b082c0005000f510806209001c4100006941e007094000c40d44600145080c020300300c0c9409a00004c41019102035a044816926003001180e171421804901c0307015035481408158182080c080400c901034000c0e03441b6003d103111401c0c09480d400011203c0403148170f000781a0130129110704001f81001121540d2005100035401c00074a030594610f0102d49035880143d5498010041e02820103030301210580c0c01c4041100c1680c8406004148107490b0300020342c0d864180f103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 731167607 1250 731166357 731166391
    0x60b180105060f120907090608030c0c010507150c09081c021005060d05190308060f0d0f0204150b18040b0901090b0d080d0e06060a0f0315022a0c03070e 67
    0x4038215045520140c076640702984e041c2030520103180d070f030140ca0003030300481414544042420301002040d40d1950750500000c103440c070703512801502c0d180d015450070386400418900a019488460141d41d03d007a28503071f0380200081c40c05161504020b80a00343c4072070301c46404e403000302d80755001544481000e16000c0004031929a6070004641c0c0c0316425009005002d1040f088000150114041d624076010b62a428030cd5584c280c104040e00180710505a030048030710590101184401e02e080f43d0941c4050000030b02644c10b400c0d030f840811625804024103200c00a01100c88d01200342c1d0121103924242d40500001c0007450020740c00c0c0c40c0502610603083c0c0d03101394102d0b141d03031088a01c1100640103002950340702182110780014064078002d9002e170380300e6000412050700b4840c543c5005c884800c9a0102128115030392302c40f00500d5108100803054003480a681180d00b280c4448008a4041a0300821000440c4aa608201c442c000315842500803440c1080010f02d05012590b0050340a90410f000c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 731168857 1250 731167607 731167627
    0x1b080c0a0c05010f0c02010e24030411030a03080403030e120f0a1214040b07091809121e052803020306090703050121050f07030507080f030c0c01050c070e04030309060b18010506 78
    0x44581310840780020802c1854480410020380f00841c01140039533070b158101d1004005059403800c07480070040c0007c040750001000710340720307900c6a8955602103041c2d03495078400380100c50194015800a030312082e400100310501d20b030405100c00400c801c0c43d1041c005000c114204028205004002400d0326032100c0024000707a1260020b040908449075074141c0e040b400c3c106080090002600844e03001e60b8650b0704114060044141481d410f41c001c2008042020040c0201d481d03801918540d191540a07110320002200c820600304070b5221150340041c0c40340f400c50204100418080e2404060520340001803040a40f1004860041d907610303034070403403020303e2494424505005080c3d401400c0c080d8880120400101240601c02c03500c0c040704441544030444900c0b612442000440c0203180d000700c200080e42d501039409060701000e1401a0b03010303640d0320b1030785d220b400004a07000c600090b65170315940100007807840340c1d8082801c15102a4580f1880d1800000c14442c103002e414420745020a489140c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 731170107 1250 731168857 731168869
    0x7050d0c0b0f040e0c310e0103050a0b0f040f020114070b0f010317090a0504150e0f070206160e090a0b0a0902040e0c0304121b080c0a0c05010f0c02010e 67
    0x103100c00e4020303039550030204400b07101c0c54003d8001c0080c00d02008000c0703050a07280d0015140684a078030308a400b20070104000d1300b1a8000d100090002c03038291000014203a50340500c00d40250f0050018007800d07185482c0106283e14020301e60b02d10740d09010107000114448100c100042682030810110b50790420a02181038000c1c43d41c02003091451504100c0f144034080c4110741242d12a110b020320f0282014008543d90207000c04041c0c001c0451a070030002440d164019904000300481c41110325601d404a0982620f01151200c407000d0500c0b040c041485d504005603070781700c0708401c002003039090f840c00001c000c2180014420f200745140d00101c2c054820552007044401d01c014201011a82c0e80d400c034501075007142c410f04400950754000100f01e42910307003c40e8440c550200411200c41841c80042c2c1d1080107200181d80f07540e0721000941c0000b0040c600400805490900903e1070001a01e05200c00040b00d42002e4104500099000d010303e401052030b100302c03039090030070f0b400c1d01c000540402c80b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 731171357 1250 731170107 731170109
    0x6060c0f03121d030702040c080151090b07021f2007080105060909030906070f05011515030c121a090a06030c082b0c12092607050d0c 59
    0x11100e000c01941e80f00f02200100a0030a14400d5600340a2440708020607900c1450034030038a246040b4040d86001e05856540480c0e130710100c21241d03046105040d105880100103032200786029080082000814590001d000c140200304c40d18505181624941c0400e501d942e82410361001510210781d0200e000e400740c0943c603112002d5401c810240b5240e46e0101c0c4d60f5030b0b01c0c0e1040405035468440031400b20300f40750034114480c940950046160003805418044194801c15040d80c5a4900419010010b04280908140c480c43c00c2c81c260882802c014070744105220140c0c0c0720060601d060380c42e140140e0051601540f00c01c0e645400298101082c50188141a91180387c55010305004100006a8460f40c041f4003982c1c020410f4440c00c50f01c0d05002a611100c40035045c07200524200c00b0064030000c1c0c28103610b0102d132032811482c0100c1c107580c0c000c00700c41d01401640118411400034040400184c0d00c00842d081024902410b0880c1550f24078ac680140b0b0250394083c1e011b1240c030805008102c1c5d1154 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 731172607 1250 731171357 731171381
    0x105070c021c0210030f1d160501080108120307020724030b010e031e0703021f09080a0f0b06010504030f050c0316030c05060a17092103010605030630060a06060c0f0312 74
    0x228034070003070044c01622030010510750140c900c048c1801085552140440d94140ea10140062056599580018650380c0004142108501c01d214020407118030250000c03c2c6044480001150300c065000c014082d9400240402d0400038031401c510b180d03a0740050184c04240b01140800944100070103510b0070801c1d1600069000000140d80b0311502c0000022000c0e6000e85640309c44401c1e8840b0b41c020b8884480b000050900201e81d000381011960340100f16070040d505041c010315140d07413651030402c03044000b0019603003a00900751801c1d0f103080c1409480d8605112140c00001103055a5a5030310312030560182c03601402c0042541c5d01c0c1c0a0060b00c1c10035220440306400b021501e4035441c141c5e901d00015060406129004000c944a40801c5040d230781030307130740c01e07140c09055585103410720503114040000c6554100b248410401c043c400c92462030b00c200d98801c06401e0a2501e030040c0d0040e21042e920a2080004d00c1440002241008803203002d031551503c2c10201445071510f0600150401d84551 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 731173857 1250 731172607 731172641
    0x20f04200a080603060f011503020a0c060f02090f1f11160806070e01050a050901050702031c0f08060303040303090b0711100c030305160e1507050105070c021c0210030f 74
    0x7821a590015201445004100c0c00c5034110b030b07a40384426594500a100742102c0c03443c00904a91002e0181c3c010b4440d0880510b4031740e030b0075003054944400b41c89804100c15209035000544440380c0c02c00d03181d100c039201015504400008403c10085c1e0201450718962303400c000d02a80c42c141264014002196540c024180e002586511188940d803100c509640f60340c0401c5c0707000b84000b03407075014001b598501d105a454650802c3da03800015a45540140000c03030303040c0584400d141d400311001d40e00204124881d510402e221010f140054070103640500240d00c06e034400d000410010341d1104a0005444081c42c1503034413000070380380607881e20b0b220003800c0354030023030031011b0b01d003000e600125080c0300c580295806c0c407503600c9000100c1201d1580e00300c03120010f5112003041e0968200a8456030058249100142c42e105294440600f168015030708200050b0b403843ea91006d5180103030140b841070030130020448507826554000361381044000e40070401d054440032100110822075011111040c010680 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 731175107 1250 731173857 731173867
    0x90a031401050105130e030702010c030c230706020a21140d020a0f0314010501140c070f050a080d02030324130506120a170d0b310207020f0420 63
    0x140c5010744000d00440b801100c074861580115441800340401d50100e1030003861501d00070341c0046901d00d9480394141c01340140402544000743e003106030440f40c0c0703403504046150090100713100ea082c501540e0007481150301060240d004035001c0000300c11040d0100070300180700790541030140c40d405c4664411501004020620080c1c0821680092062461a41d164003071314020b58419011100c031041010a040c1455006104650094800d4104035030844165420030130180c02443c5089a503400118141d018850100401d08280c15024081c0c200d11001d094483c1105c1c02c029500d001c010040340c410688140c2c2c003441000760141c4076401c818040c0154440c600c0d2980954043c01096919501032140d440d16564502c070003061814082d54802480c44600700c40b02d441e1202c0303400201c5031501c11130751516220700300c0c2e40e002149400842100c3c030640c04500008a040f6507540b140c00303403900c05401000464010f956031180508195800c55001070710f5848105000041d10406405101c10100010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 731176357 1250 731175107 731175143
    0x120a1505151c020a06020f150a15140a09051e0405120408010e06060901150f05070c0803070b09010507140c010f050103030207180c0915170711060115020a02011d0303070b0405100e070b090a03 84
    0xbc0600c1c1c0c2a6804e0315002d58484c1d403038103171000b213070704c00c80380c151740100c1038004003403c0c3e22192140f0390080d0082c41151a90105d001101400d41d0003070f8008501c0b41e43d1550000408102880015800902151004180c0d894034481c0d020348085030740403800700500402c0103018140a8400d8039841a04800c5218005445000c62990382d0300203441030741c21511400005140075414020148143c0107652180800500c0180c2a4043c1d0440c00115021755214416054902042d108071802540268001c010807403a28070707070081c1c01c1c040411410450b420020010200b94024800a00300d40d00ca0b0040d0131240303640c4000300c8a840c3e110001c40e2100e10b2207024003441a42c03200a40c103140c0c003490243c400d43d0340d0b2044c20042200c100080c1402503040f0032030003005503010f00740e542c400282d141d804034482e2241c2c1c0f0029007168070000046030358400200c140410700c502000f0040c521490440d041140d00554070b0744545d00c001c540700c2c0d07040304030b400601405d031a12036296210045900005003224044084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 731177607 1250 731176357 731176379
    0x8370602040e0a05060f061e04080a060504150b0a06050304050a0b0c1c1e0902030f060a0c08060301050601080402241305120a1505151c020a06020f150a15 68
    0x180350300703150f141403e01086952038059003214603210003c017250f10307000b0261544800413250641149152100703000028403484140280a1294410300700020075242501c0e00ba241086040ea1103112a407420001c105245c0b182c11010b025a03416040c45a103d6440c1d141142c640f600050b4000d0040805c00240480c20400c0d030090b01a044502c40110321002180c01e460781210350f0308100f511404c3c0030000c5c80c0c04019055001c614800e0000d020790304115080d0041d84e00c1e049007914106845991140340b421704507840382400350001c0c81240240000d080840c0002e00c081c8000d400a0b100d146016036402c400464418564141d0741204c141c55115210900c00400d90403c9101d028050761001c41c5203440308070b003c00c0240c140b40e402045102d07104503898001c002000300034035081c800c0d150703140c002049075160407410180403130880d500d0788101e09a00c140141d40c00d06a00420a5600620034480c1110010070011504840d01204004d0f558a144044010344800c030440d0712100303140c500102c1c450300b01c0307 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 731178857 1250 731177607 731177611
    0x8030408032e0e1f090c1b0c1a090f0108060a12140717061501090909061d06071b0512030903030a180f0204150506040f090608370602040e 61
    0x2450032070307100c0ea2010120707002e850a0360340d0644d040700719400c184002070055100b028100b08030701e0400b0011407050a0750342400803001c01540ea072039814904100e142ca00c0c2c110007034a0494000314909003032910f00403800c81c010892120b070500401c0d4000803c0358030f903612072034004d000c0144403d086102d2814000031156903090720b0201405502404030f41c1c180010300c51030030274128038024081942c81203a0703da01074a005120038104242408002002a01c1e030203500c0150380074040c0000c0130403c1c00000e40a4418007a040d0180f500803604000c04140c00c03514550501030500b03100e0802001354a070040c1805205000d884070007a0100c20b005034a0400000745101d001d614034108041070b240314107107012880300440141031156000b889401828140c00804003607088040b140041900e48001548a0f00f19800201c1c007214420002c004407401e40c05100002c0291070003400340f000343c40d101e0704072a010603164964800206001030606034409680110b5040e0080390864440b41c5034040c825018500f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 731180107 1250 731178857 731178869
    0xd021f2406030f1401060e06030a090507090b0f100e06090a03080c1c0201050f0c1b0106180c05070206070f08070803100501110c01020a0b070923030d0c08030408032e 73
    0x5403605002e0649101c0e04ca6605981e080e458a101c0141283c0410046030710082199221603141ca00150004800b00701c060701070109043d01281455158041c400c041c2082204175106d024072106c4041c4503500509034204030781c0d044c1c07451076076118150003192384015650300041c0070a400040b540780441c00420401e5824079298030000c18a045502d0880c00c1c0e0b8015034001c02442c1403540071928484c03810005100200e000c40a0f03480321145095920700310340281d800f07100c00b10440740407030060041c0b03482640c46e19501030500c98201001500860a0350140d22401084145507213102001d002025040d1000c0076402802e10f40d070ba281c0900192031103401845014086104603004150701071010881d0882d4410603401003c401c15030307484240090101030800307018001070581c0842c020090451072807000584040010f400c040c6c000c241843c01050364000400c02c100681520000340f0074204607904140c01c0b8203220b0b02c84d200d0110710840e00c000e0180c6100d1070540211549268002101044100d641d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 731181357 1250 731180107 731180111
    0x170c010b0916110304150315030b0f01030b070906121505271302030a0f1106040609140402041a0a0e1c0302010e010509070909110a06110d021f2406030f 67
    0xb0201160b50303401980039106c40b413025540800701e401d01c81e83c402c00b61344070f55100b8001582c2c0da945410144010036030f1034024110070400140180700c1c0c03c0d0013040c4c1003180f0340b428015581c5041c200800f4801c1c40c1ea034028032103483c0c1501003410200005a60b000d800d009201c005014140e140001001c290311007140d04100c3d0b003000280300301140d081100070f1190080c002e460f04110a07629203141c0000d0440844214000c420300301c40e039803107a0303010388054039403520380030800f5003041c854a4120460a941903c110300400c01800408240780005205101c4280491740304d60030144245d4582d102000c003550003904480052584814008100107864008c0d00208961590804a203082e1201110640021380c00b0740d40411803202a54840f80d0301c0c7e13004010f40012143e42c0d40000e0414403956001c0c9002035510b0881d44511941030145c3c2d201c200d13182c002052440c0c201601d03141d40c0c0d015010720401030740d6680707012211500000fa4843c0c1c1129a45015008584c40d650060004e0a04080580040d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 731182607 1250 731181357 731181377
    0x602040f080c0a030c1404140a020d06090b06040e0c0f130e0a06140f010210020d0903080c0726070f0c090c050705060c0307050d020c150a09170c010b0916 68
    0x41810303c0110b0603290031584200d515030130305504091301c0003032110003508550740e0000c075252411301450250003944690800350340ca6003650000344c25200070360814a116880c15107503466a0303841004590469041140d0000c480c1d44802c001c039600c3c02084100c07001410006010304981055412407429206400403030486900c46921010840f000c0d40100400c1040322418074844e480c0c803030002c150b50b16052040f5501c0b44011109001a6004007103c0c1401c540c85140d02c104140d0008402d03648410380700202820040540c50b01741014255202c01901d14860403040c5128480b1141290000358210090180010305481c2101b10a01e480c0b0a07400d903246412480d1442d54400c004681599400100801c041d07212444142e182e0f610180c078100c00d000080003030005a14450001e06183c14500000c1c007613240c64821f070b411942c02c00400320440c40b460003404c2c40010714499288040d07980c411225075154050503090f00c1c0107003c1c0c0742c0c0e2035a00c002583d003000000e0308245140145041660380d101c0e20302c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 731183857 1250 731182607 731182609
    0x7060606020303070e010e0402090604092007051504020f03060906040c050a06050414030a15020403050d08072712050c150f040614070f03020307050d020d0c020906030a0602040f080c 80
    0xf070100342e40600008108081c044000d6200f190018a04040100010715003108280060f171150b20591081410b15110740030b0700c002e244902c2c8024446035400070320034645207d5907502615240058254180c2104000100c1c0030354403060261001000003030201c40c0b150818862255036140704440c00c50301c0e1503103c003002c20f0303604225500300200c810707548642d800c01c3d0515849100d103292004a5681510035280c0d00d401107841082000803106030020300581d101c2c02c40c1450350402250f11011000c2c040c014060001d4282d0003d401c028100350070440710400b0240a00d084041c524076400308044018440300745042c840b020034011404074044400500c1c28503e14010111801210440c1d002401e0900040003201d008040a6447c056541c0005152160740c0e620f002a07840007503001d50042c0d00208000e0200017081001c112140e501e40018410004c60041c0200181c03088800207016007a5180851001d4804000c0308094941c4400290740700c0d6101c0303040d010650218410b40034140700e8510b80c0380c11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 731185107 1250 731183857 731183863
    0x6060307080307030507170304230303011809050c031f05060a0302060723030708040303030c0c0b06010f02010e030318060f07021504051615090e130201080405070e07050706060602 79
    0x201da1000380034608040498800755520342140c00241c0e40303d002e81c64201c1d012600c0b02c0c001c41c419880b52500c20f131001ca071010204045044c003040a01d0b650f00410042c004487d0f200c2100314061810300c404903030a0118a0f1039420041001101c507010311a200c400140022205940c0f1510610384204204990744c242c10401c5840051101941060080010b040860002d600418205842c0e000c000c2c844d184420f2a940303164000d20090b80c241074003103000d108142d818014400b44a41510300348240e0303400f545480841100c00f40415060024945000ca00d0302e000703410204e1200782282c2903030388034540244002590f001c01e645110250285000081070081684da1160280000da8010301610009c40303940702c840d0b03c1c060020740d48c6102c0c2e411411444180320100401401100420740720314562468080d20740455a041146900c0054080005c01542c0c110003c10f01ea13024030f0204030030b807a84d0601c2801c04116030415a00c0c4800300c0108080d80750400024240c00b44500b204103e05a070b41c401c200e0b1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 731186357 1250 731185107 731185109
    0xa0b0303071a13080f044103010b040504050102031605070c0915030206030901140106020109031718060906060310020414091f081f0c17040606150203090306060307 72
    0x4000c40e00100c800300c03510740c10a03030240d200c22400034000c0d088155498041050701700c134015401c8040b0004082c42003c20403c3c0e88200d8248420022a842c10440070005081080d0350103200d00f00c42c00c460000595800350080703c01e0b04d070060020440c908141c181940030b50700464002e5070348507001c10744002041c81801150310158100d407034100789278140107401e4003904c0450760612460750240000310150307403450b0086014901d545d000240324540048041d211080580c09107095901d46103207580070039000415941e4030801c100c05201c0c41e42e00c01d40c08140625000388404403030b100740b2013040051400010014040c182c100c049614003200100c1e284140e00c528002d11200b80c0c00561002c4003800d19400e1036070049141140e01031100741001703100012494640c0004490360050034000c84070149200c5031401ca8019036800d00c90354201100140008002d525010055458130000030113016542d03200c4006440f04c1140d107000c0b2500304500a41c0c2c1e810082500c1d200e40100001310740c0034540018400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 731187607 1250 731186357 731186363
    0x10c060e1e1c23090d020603070c030207080c0102030d05090f030406020303010603060b03011401030902010c0803091b1905011808011125150e07170303010815130807050c13050a0b030307 82
    0x2900306076030483c49005400c2050426040b42c00d0044060040e0344079030180d841900c603030b9118051501c0506000346480ea4a5014201c640c00c15807055a032a40d000c001c540103e00f4510010940c1e46541d000946800511481c00402d400003240c0824525404002103048134061340c0c2c01c0c03110381e40702d818150300da100a205800460040c1402d1001ca54040e4119101071381c01410103043e4548191166444c580c812958155070b608040d08400602180554044000700290740d24600114610300d411018032450007120306105107071844001e80d94200080320060300c05480240200004040214500e80000c11401d807541c02c620452086045550340c2c50068a81100088140170001e60700d00004102c2000010618010050040307007201181000412000043c4001e590f2580340c06042420103100c0b14040d00003401c00018841000f010282d04100340e40c0148146540d40c800d85002c0d0710b0503032008070081e0064071000040c582c0000c40e030300807803050f4100e800c14043c5040100425452b4403a0314402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 731188857 1250 731187607 731187647
    0x20f0606010e101205040506011503050f041416031a1e06130603051c0e0111150a0212070905010f03140408070c172a010c060e1e1c 58
    0x206552034402440c0042c210f1a044c142203071480a031003582a90001c4505454580c4041e00401c06180120b500d07495812091804000301c1c102401400035120001c0c00181c048169149102c4611000b8049a42e411703401802c403000c2e4a41c1e03850551222103140120405040710903001444040180145c1807241404913045d600aa598508001c09110f644c06500c5002e40c2d03c40e400300006a04000c2c902e50802002c0e00500040204c40340204005c0c26058014100b0400c040c07a40f051000009001803400003001c0c01a03856969181807100a020748030400c89000c80d0364091060094000707500e401618400e0f0380d441000703d040032082d03041d18402d10041c94011500800030b00814051030103171061502c40d00c240203495a83e44030021030707042545501100794000100c0c210704514490035651002c2c170b0301480020741d040540b002a121038018107010b018561901d1040501c8070b014068101c407070f08480041c00304d6020914886035900380030540384840d20b403214501c8002c503000b45040c1d54803100c2c541003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 731190107 1250 731188857 731188877
    0x7050607030e0c1302030108060105060708040605090d061a130c020705060904090602030108101b050909330102010e0c06040314011b050c0c0a0b090402130509010312020f060601 78
    0x4128014a00b02020100d50300600148102c0ca0307441c6110090510b050325009a02d030f5041c00c650300d0403c103042e40000d1141c84104501d0b40000c4065055400700e81150a109403100c00f8000440c07600003003458000c22143c0307010f08500c00380c1074078000c002c2d00b14016031740c4501c40d143c001c0700f017421161807a20301000340c6d0202c2810480c030f10b800001440b90384000342001c124445d1907a03940703050760400e80001c00680c1010f402c92900501506c42e00040c11304840e100210140c800002038800c0c814601c810b805003402c940020006014040e111040060088801c0403040400442c00d0340e030500443c0e402c0c01542090304c2d20034612400030381800000001400741d480d00d0300d180d03a03044c220075801381103598954840c100d848150f220041165054140da8592664070080b0030b80a508100040305c040d84102200c51062002c21420410b6400c80c2c807056400680d203004070400303101c070030500c0c0e80300c0c643c48844080040208404c40707841841d0000036400f1a444e008640266540340e40080f100c0030f00007682148 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 731191357 1250 731190107 731190121
    0x6010503130c030210020105090f01110708180306070806010e06090a0e07230301090b061e030604090807080a02150f0714190c030801060302070b04140c090a0b010212070506 76
    0xe522445a4801c46090303180c0b50341e0b54045410001d410141c00f001d80d42d41d02c2004081002400941410365040008001038828105880b43e10701031034901034088032000c01c074011840241e07500c013000514001c007211403914041c00c000781000001c49407140020f186000c90100c80c141641551400c52008040c8402c240c14a1120503018500030b003d00c00304030108405507003003c1c0c407a00c40b0380c150f000d1010766641c070341c140040582628050100c060190f6001c000180511104408040b0b48200c61201d243e501d4481c800080c0242c05144009002c4540004002d01000f0340c0d02d0090141c4030050302556040d01e000c20036492004022920709204030188800201024400c808208414041c2400c2c2800e20030301c1c00180602000085000c03012918013440f000600d600300c2602c1b80100824501136107402a0b40c0d803001d54030350018000910301c1c10200c4801140c04410b0244d41d01c18140908200035615001c0810406866001e482c50701602500e00c144150040000403581c0d1650810010300d04d5440d521 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 731192607 1250 731191357 731191381
    0x5101205071a09120601031a150d030e060a02160503071809061503081b0303090a03050c120307090f050319031211030a1d0307020a060c0f02060f0a0e01020606010503 73
    0x5003589650010400c406583c95907441c02c055240c2d41c10800401c2e2035810f51500c41c4440c1d5442e90325010252462081101d05403020010900c4104151150040a8407d2806460f80450030360803a522a0020a4250000343c1c000f5101560945004100c4c84d0303169244185601e492407409240621300c03806919a0350030440343c11840d03840344070381030024544c0020226402d4107400f40d0005c56a0300030020301c0a0390020340c43c54204040140d17001952450401c03c004035512002ca0f0320040500001003a00070301040c050248011091814040301d6032482c28a1000b030500c26180079244002d01d24100102d0300e820001261b0082801c40d401c401c3d1040480c1e1400d44040381820803c4050369140c1c178103007080d10000400366020394200c80c0085507401c0e041c19003854082e100f01c1000f00642c0b040c44a1000b5994404116080b5411401e10341c0c0724800608204a41c1010000080d4001c00002059034203c54118010611280e01c3c3d5200080300100c50700480c0c0b07030ba00c2598400d001490a002040e1105905 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 731193857 1250 731192607 731192639
    0x81014060621100914041a0106093501020a02070f0506250624060c0b16051323060304020a05130605040914160303050304030e04110d0510120507 64
    0x12411160341c01e669070205800303075089017054040c030030780020034401000109a454542c2428110a25417658140a40285118440c1c032800c42620b0714203201c5160884004401e103403d6140b00e9000c0000c080035441c0394080c0d806190018014800c0d805c000a00328a0180014217031140100b065190000207401d1820718003c01c0640c265400203d40300d4800030315144242100d28419502d5041c0100e0f1820a02c2031a04a560049042c0400014403600060070304542a5100c10104007071000d0031680c20b0112070ba4020351808400b9018050004160034102c03010b00960440b01400d8021840d403e0320a0100c43d000507100207401070f428050a00162400900d1003241081500000841c950380d40c3c000b030240c03404880f09840d200d000c0145018814024491020744010245580c850680344d640d0040c0360307102c001c00c05000c001d4403101c54100c0366950b40103808003075481250281c45101010341e4400401064420284508040400107542c6248450302c00781150070402900704a454848190703052070407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 731195107 1250 731193857 731193871
    0x402070204060902070f172802010617060103020306070e0d231b090901021e0c191b06080712020304080714070305070801051303030c09081014060621 66
    0x5540c0d003c140c3c02c80a202801c010386c0608100307105450b850808003e2021180f50314021040304105580620760700701c030442032080d079a03196410400d04103003007240105600c1d00400081c80b10700f2401c516480c00018018180c07070080341510f046031035841041e98902501400545c20a030f8003448a40852210941c000114007075034180f01ea4820008001401c09510041d007403541c1c0f030845440b0507039041241980781d0007901c3c1d000171441c0640e0070010b8114000303020012401c580d4002041100100140f180340c6070816610300e4140c10f600d0354030b401051151403900b1511400c0440d6800a001442440c0c02c42c003c0300d86032503140705000c5440102c0060751005000780c4903000d082200c8800240a010140e90b41c1011801078076085046242681c1407100035840880c1c91780c1044240b2010300c884400c0c600c8016814200051039041c80ba605640b00302d0241e010150034028002d0520403040b070b58205411111103120098401d41d01c40c0200704440c0100d0880990303250000d107640f0703a1899255181034000203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 731196357 1250 731195107 731195111
    0x10603060c03091407050312030c0423040b0103050c0406140909041a0c0a17180f0606101418010207030519031b0b0609061302120610020313050402070204 68
    0x51280c4a40c0d0507185590310680010740c2d00e070190b03428400085240c615251240c1c0180c1100c1c0e140030b00007581c61a811482900441000000c02d060f000460300300e41c0108401503101c20a2040f0000c9240c00794041d508a600450611594440c00d610a100d4103119917030510307989080070b08008046443d001405003000d03403d0800c00600c2030954034160054843c070721844d00c0618822191a0007a0b890001030b0001006450600c41d040400c0e8000045815009050b003c40800b176640b40801402502001d03000c00da1401240c100c02c0584e2004522141701d010f040c2c0b00c00b8120141c402c3c0482d200210804e005c1080b2105020035038000d80c08801015505c07005104980540d9100d446190421f90042114180700c15040045401c258102c21041000399030000100080180303511054082d000c01000a032080c8180400521541c0e03030101c041d1320080c5001d0f01152220502c0c3c1d0140d2a0a50039500e980c0f0688480e80d45002240c4000b049071068050a4210203010340f40205000182d04000c00417640a6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 731197607 1250 731196357 731196359
    0x31e0f09030a0c09060605190f0e041404021203180d24140627060312040308090f0f060a0c02030c04020c010218060c070e0a150f060212030f06120106 66
    0x40d8040101021060050f40180e0000340342900040444003141d01c660b00b030000501c80402e8800314841d203c400100769040c0004601c0310303124201d8100300303610710b00c42e4000c4c40c0c03200311071030084400802440755100740c2d1004841c0d0b100d00c0701942c2ea4010b215810700013030310b03a607490b40a0341003210103116060702c600306081542c26081c140c1b04920340c44551002d40c0075510303602c40e1490805a4000c9030800c0040c2c80d0b04d11409017558160209640494505413228107000c0883d4803074404000c001003c1e680c0d01c4940361240d4480c58068039070fa012105203441030104d25808000ea2070065408048042c00a040b5403500724030440031303102244019020b07a4503000c0d81e120030a01391554001045000f1114000503a190382c001400798255445460040c044e081c01e205240041c0d000003042e0081c2da0984000540582c2c03051070460141400814886041c203a41c05d0024070700c0c501c4010401960070399000c0c0c0b118082e54119400c03d0f4001103d0900700c0c240c6580c0850202e00703192401460200b85c200001ca191 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 731198857 1250 731197607 731197609
    0x3040c090b06161a090d17040f1b05040f0608120426030c0307030804020907080730060605030708010e061026091c02060f15190602010203040b0108031e0f09 69
    0x1143e03045407003030115000300000f090920340c403d82d03005200110784007c0501c0d013099107814111441c601c2c4021300d4a58a21100034011040000c1c3e81c0c0100801001840070743c40505001c0040c0105d84103050281c410024107100320828042504c084d1401c0e0b041554000301905e68a40300e2141a04500049002c01c01040413000d50900090400c14043e490700c0560b0f09051040c44001c1c90300602100030002d22030284007a81d5800302003041810000742103202620343e00d450307042c009010500710064040c58070400040d01504803001d184990340b00d407030f441a241c0e030715005030300595002c4410a91216411043c50b51050243c811880e181030031640c0c901002400c1040040314000c140e45103062540701404041505859000003048003541c1c0c40a00810b0030440285000760380007400c09a0340d00740041c9620f5070342d25189041c0c5284200300c0000840d0a0307960a0190013540300750b6007900c41c107c030140080743e809000000c503581150410142c00485004450241003a0084503209190020401000000f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 731200107 1250 731198857 731198903
    0x9060d020a0810170604020613121506060f02070e07170406060323060f07020a0c0303050a02070f060e13020c0111030115020d0f122003040c090b0616 66
    0x741d820788401100d41000c10850b6030408003a0b001010300d007022003079a41581c10104400d074100b0707415078616440342c581c100020100341ca2130b001407005070030003052001801058011140803481e440c4007000503907100d80701103801e103101070030320405071f03001000c10044a10b00e560100d0340f0540030b01d003240300d144c5c02070120743e40c41310162000c1d14816141c1c0400c0c41440700b00b480070b1210f6091070795a103203240c119518171500e41000401c201c4044051000040c22035000b4440c0103030240d80030812520f02c584074134028140e0b0b040609400e0040c800c0040c08626128964407840654039641c85500001103044200502000d442454112143c0c0a01070054405801d0241c0a44d01c02500c0c001d40d12581054040100000f03407aa006c8115440300c2d0000c0703040b40d04007041b030107194641d02c2c10b504401c010152100141c45198070b82c01d600382844284044800d800f802541c00b03a8425000e102c1502d554013061000e9481d100c0150340c2c0508100140c070002d0116861040e0484d00c00c80c907001d030b200c1510f900039017 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 731201357 1250 731200107 731200117
    0x110c13240608360c0306090102090109030b09010b040e0f0d0503040309210212010e150c030601121404030c150e070612090f030e13060e0106030e0a0c0f090c030e0309040209060d02 79
    0x507913018084071001c078641409015800b42000c0000c509040350400002c00c1060140700107020014104042096118203420000c07003640050001e101c08100d10700010703a5100803c41071141c82c040e007110b403141a0b2040b01202c0c01150156600004c45082c00031015262150803020f84110540954000c0181c0b1600344a04032031000710000641000c2018506042c01c03042407425044a20140c01c2101c000c45400030380340c0000302868072010b403800c440c0003c1e00038003032a8500c82034004201c082204155200741d440302c40c0c602c10000036006aa22086285c16144039103510031a41d007182109002c03062013101c91010340c500403840031420000503110708100411000c3e0940c0010001c000072641030400001131b004211807844104115860044e00148809040c01040e0030151620b0603100452820081014015003120241c20011f82d038403036941c03c0400d14030071003958504013802c40c80401d009100c1c510343e070b500e1903010b58a00700d49082004020750000c200c0303a030300860611207024a080b041c80901 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 731202607 1250 731201357 731201461
    0x70c060f1d070924031202070b030f0106030b0418032105010306020a140a09031709091303120b0102070e040f0506010f0620030a110c13240608 63
    0x4803c2c108008802958850384139018901000b011000070321164402510459810130a007024410034034400701d00b009003592100e102c4180c08014000085010b00c060780c100c0d0358540b030400115200381e0030310040d07500080d5030711000a01004c404010030300078911940441e204403106081001c1d81d45030007040b03a03001c0e041940c0c1e030355003c200118590b42210081c2c5404030071002050519250020041000d212800018605011885d001c1100c0341007009945611100a0003002280740600c80540f040d11100d81c140c0020f41c4807008000300c4499441740c20645141070f07002d490306a0600c07025003000d45020b4011034500780600800310120b48103211003406013120b0f0207a14111840d014005192800103060680d928462401e00340ca8010300204540b030102c000d0402441071100401000d040000d400b02e0550010501003d6110003001c690210440000d90042e4222406508012000e4801c440c007a00c0702246184011800c1031541b4207005c0d00d2040d1006615810841c260707400103800902c030040c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 731203857 1250 731202607 731202613
    0x11040617010615111f110a020f0105180c12101b180e01050f12030c010209180903160609020d03050405100e0108061203160c03021503070c060f1d 64
    0x140b100c060800f0740c0100c144420b1a002507004440d41c0211380f6915142c20f20603800b400c90200381c4003585145c0007001c504010080c0282c95542c1050b02079201c807040c0c01e120b20154a400c000424000410071003074001d40088006060700d20540c024820b2103541e48510341102d05c692420000042c2490150721a00c0c5440e21f2000c8000022607400f42003c01c0d104070800c43c101100d40c0034410701410708051070454804a4080d0340c4101c201000c50604071881c07a80700704a00000030907600031030054000f84182c030001c1d10385031a510100a200c441d02d00701030713400301d00b640c104220b861601d502c098400b0f49401c0c028140040d500f10560b00040c0c3c0e00d20140400c502040c400b04003004245051850341c110540030341400030740c001048000820341d99000304214032840010380c251403000d604205403880a400540061007035401820700c0701c0c42c54480d00c012482050324101e00c03255181c0340801e6078040c00007070312814040006540d80d280606840d481c0c03407090030750300c2e100703400840703030030703000042c80d08000005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 731205107 1250 731203857 731203859
    0x8090409060213060c0f020915040e010e07140603460f0e0a0201052d030105030c03030403080403020112110a0f020d020703080306100519020f0601051c110406170106 73
    0x1a500b80c4201135880407083c0031070880d00d40042031210034070f56144e41d411035112820703586688101402c1c8900d2201d0ba034000d4235103a81405e81040540c0450314014501e4122030358259229003000d40e019801403501c0e0400c0303040c40803402c20f030004010800000d068040d40c140c20a400e0f000c1d038815201d111f55100b44451030042046460901e40300e402c2c10268110300600c003516030401c84039950400503100034104000055a40c6400c0005401c400d41035500c0713000300027088115001814a50001e000c0d8038841e0040d0072000809140020031941102e610409a0b400c10380385400640d00c1c1030290107990240344d11100000941004140113050a40454595880c0300d031078000d00900d8018000104c00555005481c14408a404441030f00d5000400301c60f6100c6810134110708a5807405084002c18030403440700d4401201c260003141d000d1907050b038803045481d16070b0780750308002e03201e030900800b52810030201607038801250340b40c074a601c01c1010290000c90a07070754440381034854070000c104000d1143d6660340 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 731206357 1250 731205107 731205127
    0x101a19141518031006091401080a05190c050409050d0e040e430602010c0e0904030522090b03300a0e030607050a030c020a030f0c080904090602 63
    0x1184000556055070340d800000400002080c140c032a500c08181c0800180007801907654003040003418819100034248070003552580c0400150092500402c20103507048008a504c80b00095114504c40e0060000c0c41d0301c206440c42d44010001c41d10040d2551100c404d00481e00341c85074082c1d07601480c0f0032070051506043d42c10006000465075464540b045040000e0700c1e00c10030000038941c03054001c6001c1d08000e9000ca030032050207800020000c2c4100e18140c0000d81d040c10412100008a541030b070000d10a8041800048038888404010a81d12000c00e00108000c60301c5100681960140c04a0400500b0700c0c090004120300c0b0315900405040351220010350440c2400e201c403074241a0408821146000070810700c01000714001641c030911680420700c1c9112611407502c20035215130140a444d494184120004c0060b070060011101107410310281210062000405a0420340c0554032408142c0e44040c0031180540066000d4400f400e09101d24500c550303842c0b003a683c0301c5e0700c074a1006944014101c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 731207607 1250 731206357 731206379
    0x2001020430020310020d090606091b260601050c0708061902040812030402030a0803040602071e0312020f0f03090304050a1217030c0c010c180512101a19 67
    0x5141e4880c4604016880050710001003036003041440000141e00c503080c4134103890081440d1000070f042d042c102003000272001000e5201c10700202e00c41e10b803102900e0800320309840c0c1804054807511103d00341040d45890134842c008042e080300c4145465850b044040c1d46403880c0c003245401650294109006100070f1185c05087d0a200000c2d50f0b00c10f508291400540e107032105840040c030f18600000000082c1151f07020b00c0750070903c0c0c3d1710071503c50b100d00341030a01e540290009001141c60301c0c50204c0000194511040368a09190b245d6a00e01d00c20400c0204800650080301c090918410b046c000030001c0c007220f501461180c5021002151101d103060108000c1c58426030040c1c80380c1e40082c0040d0081402210760310000c1c22192080c0d9669215420034056900c502415102103502c1c2589440d00d250f480301907030008100c7c4000c0000c403151190100021403207007901c0f50401d580003108088451040340c00c415203400746c0c0000005488040004950301c11101f107005411114015003d00c54030b2450 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 731208857 1250 731207607 731207669
    0x1b0e0307030507151407030210060e3d180627090f080a050304060506091303030506190e04030201050a09080901081b0c15150105090120010204 63
    0x12801424001d2950316195140d0455002c3c9140a410722880c50100d140500444244a000c8840442d603a07585410002e413a04c5400d81c0590505042c0940000c0c100c036032500c4540070303000b49070f02e83c81040034400d0f450010f00007070515032100c020140d4170030941e0b240c00f050070b00040140d0920000c10b42c03140c0c000d84089510b16082102951034190042c5141c000300700403104260340341140080c0518090804258905084400901ca40030001e0141c5000ba40400a540200e110720340c103020300d44a0900700007042004842189d0f40c992200804004644240c00c503640080000d800d1520000d4280c036803406d40459a00030140414205091100b0554244902341e4000d07801e407400c208807911030740e43c00400d110340b880e154100022240480d44001c00d62030211081003808101d950344569620040d9195800800d448000c4c0b00d1481c00118410403a400102d0b01c240140e560a1505e0712281c010341d40907070307100c110748002c10450300c060030001001d200030300103041c010340c9a03045c1c0034407604040c0041c981 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 731210107 1250 731208857 731208859
    0x807081204121b09060b07022e030b060d1d070e190911031606030c0302040b04120f05060403030b0906030c010914040207021807090614041404020903011b0e 69
    0x1007044100300d494502200590980d91050542d01c0e034060195444001c07800341c2d00902c607254600000004d04802e01c03001006011700c00d8840700c40700d03a0f000c0841d108403810405022020300e007070312400784407904c00d6008001560000300254140160b00041100b201c2c441c10094056144641c100c00a6800820040c00242080245500a841c180c1c0318404c4408035801381021150300c2d00066010011401c2e000040070310060100c07080c5140ea419204602110352050102180ca80191801c049129000316010359003064003541c0303810724150b4840400540c0c502c007940e911030311702c1e58100081c40900c130081c02030740030369800300e015510241009150071b806406244664081d10368088e01366040880c282c12a002c101c5620070b20101c60700030601a02c6400d000a501c0441020391344560f9440180b841e004604640da460ba8507601d800b42550a801c80f086000c82004040c0010489001e0603100744040c1d840160015041003103180100f406e65170101c1807070f0344908030300b02c50881e100d0303020103072800d05c02c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 731211357 1250 731210107 731210143
    0xc0f030c150c0b0705040909030806011805010903020d0201020a35120601030c02011d030309010f060302011b0501060b0705030903060c03060d0605041a04150e0d080f13050601080708 80
    0x707400d52001e0580034444a000303003020b8003400000c0c1070380c1c001c80585004011384001440024400d2900134229001210311038041400c404900a14041840c524400d07a1410384800c0309860554082081036660900124114801c10480c400003400b10300d40c80d8007540c061611074881c1310b00718640030000c0d010144d6003000503a0601146907040d031413240c0260407410070700300082c8081401d54220701606d41500f869031850120340010060200010046106a89040003003019407910382d21003058034003500c0083d001600e6500c0c0c0b41e61141901100c8a81c00d44580000a02d10b9610112084a50811030081d2455000403903006040d0405028481c0d204103811666407441c900600003400300c1c40302c000f003e014103946a002504200f922100744000b0303480d8a203080114a0301d4540920702c4e1000140b21800e01e410040000151640003d0100401712152550380c1940d481440c0d00c1d040c46401401d10441700d9001450700003040040c49002d000c0c040d1200580b02d61400c2c245050701c2c040141040c05a40c3c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 731212607 1250 731211357 731211389
    0x90b01031109040e070308031905091b060a030e011118010807120c020102160803010617040b2e060302031e040c031101261b0705061b070c0f030c 64
    0x40305801100e02c00b15088030000780c2c0c1c1d4805400d02d850204642c0008150b514000180018494810b9511203040300e0040700b8080c3c2c0e95000380c000d0310350b2158109604a6079a403c042c3c40d107850880098808640307545000140780d07925400417400d469031343c024806645400548200d00d6500b0103e140d040310f10a0815404174106804020404000c12040012543c2c0c0e5034103c0d03075007510070b404a42161115400c0c161a0000070304018030107074020b1060303e003c00e0500c0c1148001c88810110341384920780182d50b040c20303a1341c0d8021340c1c61070b54007041c00d203076031401d0490b005001011020780301005800c46580041e20b030b20b006203104a8418180c10307641140e1011b2010000000d450b4802d0380256076000c83d2400c61900404016509100c03188005542c104181400101c582c1440b81158070a2106280c02c0d1340101008491200900c01c1c01c00141481c2c2100c000030359405c000a020403a40f000b1074024614011440d11003601014180d0807880040500140400034480300800c030380d0141a0321050703810b00c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 731213857 1250 731212607 731212631
    0x2010f050a0801061b02031605100206040b040206030403030608060405071a041a0c0c1c03030b150a0810050d0602121803070303090204020f030c09040c02030a17130c0e01090b0103 79
    0x400414131a5604125080c40d01c02801858904214804c681c050203c5110b80182550313030314403403e1402018003a80800141510b081e1001401034000c6411031158207440d2125028084203510050050b01499250803001a064100f0001030f88101d0181019041c0e95040021165182c40345800184924506000a0000803001c002c81000b6280e20020140d64461000707030181081c108c4030019912141e2000211300200c0b00e0f0102c607000c6482581c0810142a43d0307810000541c1c440d110405010105200c0040d059002e040c40503008050f0031040c1240d60340d11400100e000094140440c0d1303480e0041064504880c442035460307000f45078001035804070391032003034095506c0c022000040c00301500c0d00c0c01c120954907183e045644182001e4213050392072408501003042c0303500c10703011280104d281c02c2c900f081c0f051010094401d803404a581d4584030640d0310500b22075a1710043c1c400c100460342034840000040100c5940001000ca0240c250459031400341814204c03014050040d040c1420184c60240d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 731215107 1250 731213857 731213867
    0x80408070210110d081b0c120a0903051006030f02040c02120a091403070305060c0d060b070b06130b090c0c0c06041d25050304050f010608062e091d06010e0402010f050a 74
    0x40301110031000e0392100c7c22071421918000400d04001d10403480010b81000469001400e0700c10381c0d00a070200e0f014900c60121075000c8615520003d0100c00c1c4107d412401480c1c541c000ca41e015410f48101c41c03070001003c0e2200c40350362000c901d190115060315401c00c03504802d02965590540210040c111080c956150b450320389a00515005072150b001a0403064507545c0c0e400b49000d070003916403894071514103140c0300c14000002d603203042c401e07a103c5035010804800d83c0540c1c2d00c80840580681240e44410069104ca0782082c1c0004225005081d000005515108081c000401100610320596002c552509401c00b40c00307014183d208145006000c01d4501c0103823003140342030b0300d440c04954a595a04000d41008003115801900c1e5081c030304002940d51000805038015041c40d50603c4020002020100e01160a00c407206040884004100091580359000c1040102e4440805428452a682c1c080c1080000d1700150a481100401c1c0700c15542d00c45040f01c08101c20341002443c4c10b00040c0c010748 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 731216357 1250 731215107 731215141
    0x30e3c0607030b0a03240501080109051b010c08120601090503030310030321151406040503070509060117180c0603040b0f0403090b0a053106080408070210110d08 71
    0x50540b1600c640310345885a060020055030002d50201c50381b42590348080e0b500391b1031080040358600f03000000c0b5003030006124110380076510500804600c0450103000c803180c0804c010300c1d8144101d07041c01e000420341080017800b00c1202000400910324000c40058a04d0709690043c2c1d00a40c000d00c1000f00b0b1302207294501050f00d03010705102081800d54805400b6100281003405681c60400e480700c1000500f96140c0030544070340c003154440d0121800240842d40c0107511480342d060b0702502d130030005401c11a15090700840180341c611f81d01805070900070144d02c41038452009943e000c01160315094414420480b407000100ca8443c03450403c0d441d2803205090181c825804a0742c0340b40420308150050382404010700e0140c6141e40c48450100000e401d98010b06403c00560b409081c1055000701c0642110040c1501d401e0300040250600800319005400100215401d40d020004140035a0b200c1c44414440c00a03603895a6240001100050800f80d4540d403502c144200c0d0010b104441c11129200e0b5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 731217607 1250 731216357 731216371
    0x906200322060b0d0503090a05100207060305090109050d0507030801060309080d1d100b12030f040614040e13060b03010621210c0209010b0906041203030e3c06 70
    0xa050035a082c0600180006004694000810315221042001c040041c1c80600b400b103810541d00c50b5035400380260440c41e8000140141c0080750107200181c02a03000030741003c092800080c1312805ca40c0c81d1480c000390100b48802190000c03078000201039101e0021130250510f071405000c091980c0d9036021403805049031101c9810388502c0ea005000c085200d580040b440080200c82005001c010000010401110080d016060440b000640101d0010861f011040741c00e10451400380352a0040701d04014182c20200c25138030401c0000307540e80001080134025810080d100c4202003561501408641d051400b45000742d04108080250501c007081e0120280301128a0402d00380c41480c0a030700e08c0742c408500355201205001c01318092680109045819032080c3c9040c18143d0303d9841d114514007400008036400401040180803240b000480b03111035500c0303030801050345074110000900b0108e200207401e26030314400c5104003842e031000b0607940803691404201d21194071988502c54a40030010400c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 731218857 1250 731217607 731217661
    0x50f01091a010c081315030b06070203100902060403080f180118090b0105040e0115110a0f1e06020c0c030709060311040b0303040e010902030f011a0a200109062003 72
    0xa1404d010004088410300e111400c0c20480d21512841d01700c50010b0242003800000e890941c4400c140c0c2001021100c0094000300109400e0074070013400030182000d5003040381c000c074042c0000000220090007130100d0003501d10095495070382c0d0307401e0040320100780310b01c0e03030304100c4000110041c003952402241c0545002c80000304400000d0301c01621903208590000c45009001c0d400015041e002c070145260000003070f500c801c45d0f810a1044507582c0c2d1702d8a407014140d18150310040001814409100400e41c50001c60904503016a4403488100c0c0c0142800d211980c000c41034101c242d2600344500005003c481030100011411500c4da10b2800c8002410309004640e20040151151743c1081038400030400f00703400000641c0c5411001019420036503e441e95141c0107800822842030481d50307202c1280c82010154100f40c180700044a00d92004000304031541c0204010418028003030044460050050704040b45072480d2010741002061030458403811040240280710311b25500a9042e02e03a00b0301010341d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 731220107 1250 731218857 731218877
    0xf0e090412051b03040e06151918090e120309030d0e0109051903080603190b040303140c070b0c0a0c080c0c04060f0320090a0c0e0d0501050f01091a01 66
    0x300342e03800c0c8902c400b0626900082604008852000002841651082c00050041c0c1d04d0351000d0040e02100110307100740c040020300620070261840341880140180510340f40703094010402c1c24142c1401c82d07400c60686261074a0030044001380400a86214618181040e403941c501000f44a8583c000c0e80003951441e900d81c09450342e034200075004405266000000e41b12500541c807006401d003504200120081240b82000070000c0c40c002c14080210031032440c6001602481c0d54800b402440018003c5040c1170381d40c100000d845100980c2e1500c150380c1e44001075692801800d002d013494400400c84001240c2c10041504010707070100003420141c0d440041076848627111550503041c0041d8941081c0c1007442d001002982180003101c0008890059100c0340f1003020103401325031011100300d811a0005504000700e491141c0c503901401000b482803504104a6080b030300041c07644003e2800950307560391181e05101e000c0c090f1200c0c0c0ca0050a00034420091101e03044000081c0c04c2426000e80d060080d040300b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 731221357 1250 731220107 731220143
    0x5012712110a0602010c1d0607060903030212040506060112021305191e050f041b1202070f1a1f120804081606020106081504020d030903051b010f0e0904 67
    0x24206400001c0101480750b00d41e00c1c0c482c0207008010f0f51550800091201c09422040c201e000313009081984098119868481c031900c44002529031090214100341d0308000c0d02d20024601c8003180e000c0c1e4440c50180541d402c14a00050040e98414280070740d26104000211030f103880c00b00084102c6000ba03520043e030b17100b0002c40c0d100e5071541c4d50004402c1c0381b407655409000003140242c0d0027550b500f211001030380c0b02c40c0020b00085900b800303410242c00102c0034840191f42d018810914110782d03000005890506995500d000c0d603041b01004407904404110003103462034503001d001d035005100f00442406141100300c0240300c0d0300c07180700388040030041280c0c01040c40342800c21074028148d000c0443c1d294118070f09070a010341e0a030740300d010010351a0881c08151113038040b03401e0407208841c0740500340907101e5408108603102c11000807018031403040c01c00000101c0c203000b42a48506200911803074202c5100c000741c04e038222072850a0420409a4000740b0b00e03566142506e401a4001e0040d03488803141c05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 731222607 1250 731221357 731221373
    0x20109020a08070812030f1b1309270827040608101104050303071104201201060f140904090c1215050705040e0c0d020f030105012712 59
    0x800a504800700e07070004109564001201c07800c4034101c0c800c0300c000c0c5aa00d242411170b40001c1e10306041840070407000c6555803103a03007800a181c2e240ba80c2c465242c8080080e1240400000da40410b00b02911900c00c2140c074000b8075188801e2501240c2c03000d810b21615503851646205c0c6100117442c012a818014100c00e01c02d0780c070304000c01001741080000c0c54641c04510707a50382e221001e8424040c1019a04d40301d00f0b01c0001518203e9101030b00031400c0003020703030340c05690520040c0b901c0d0f0010b603038410419114130040500d84c40403020b0f8201c5030761148001c0110071b442005030000001d0200c28442c02c4080f55015501840060403164242c0d258611a000a40601400705024092844155000c1088004010100c080c0b80c400c00c098a90318003004200740544204a8200002c1902480108644243c41460590000441d4145490300560404035000c9810a40c168030f5010300c04070051146503001a84140c07001c10b82c007207142c5440308520325004401c220740a6110610381c44211203003084401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 731223857 1250 731222607 731222621
    0x105100909051509070306150e032802130221060f0306180f0a0b0a0e070e040804030c06180b13050402030a0f05061c030f110f0d2615010201 62
    0x14038042c8914184111503074a40200026a0ba03c00d41000340440e0510b8081d00c80c580403501d05452103096040c51103c151603281804c084590940240703130b081115240c40d501203918120404030511040b68050050203003090960194806503841085015100311050703840012424880c02c1d1a8010360b50302005c00d060315080b0400b40d82504c190350500103156541d12880d0015071200c81202e03080703e150b01d0a680d0351411180040e108401041c04100300c032040b07030840b6851751091130446808a59030380c0400c40d120310072103081e41c1c0130002290a104102e1403034002002886185022212a03403406807840340440c0901c1543c0d545840018124182c07080b02307030084d0040c00010700440d1030b4540161004003034001d0180002007207240c9400102c01e46440410720a0b6100c0d01c175041402c09a00e1782e02a68084a0151100309206401441000542003045a01c05100220025107082444071001810b285212442036465101404050240b945200e90741a03000701070702c880c444200c1d500c0d00181d00415003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 731225107 1250 731223857 731223869
    0x1030c09050a0204180506131116110904140d09050303161103100603020a0801140a0213051002030a030e010b0d020613091811040903050a210507020f070b0c0601051009 74
    0x2150298005d1150258031503071040c3c400b81d910026407660440560101d0384207010982c9008024400403400d01d0085942100007441918402900741850300000c680b910f00301c83c2100e050924120319414808180f141c201c82851034200700c042ca43c20840042d03220300809904031080b03101d00c00558280609054030b440900805015900f000008030005005008540416405060075800000b60031105103e02214803084001185803078071251030f03107406948488100ca108c001440c0020549548100ca00d03034055806400442d1b43d0010b5806c0541542c42c001802221640b42542e050026151046c104030b505a0440f2510340d03c02ca6101c1082d08007900e50007803804203162126007507200200c440003c003024098000046226000b0302000140c03055030328020f00107102807014684d000e00039030381c200384091011005034105e94061001c00486408480c2d690040c3d1104408400b001d10600034900a440401c3c1c00c01d01c0d007013500c030b0203a5903448103201d024010f4424090700c0301702611501200010b810 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 731226357 1250 731225107 731225129
    0xf0b0106030c0306050a0303090b0304080418020d0e1203010501031518091406060a14180403020c040e0705060403470a090c0e0601030b0a17070e01030c09050a0204 72
    0x1031540030080040c001c080c0c180010030300d010404501c51a0410401088a5060341d40d4503240741001148a80768201a01c121103251040c840441c6244080f522030b9081c00c90f000c001a00c4005821320708040e50039108500580ea0030401c8241c0c0450250000c03030b41500c10a00340410304005ea0540240004500d611074a00440000880805403540d500302200041c00b071680741c89407421401103640c842400384c0c1c03181d170b109180c02401c00000c400c00c2495070b13110000401b06084d4180342030b0100100380d411901280142c20140390314610f407401e44200c5402c0003c120040441038100804610a44501d0101030000d240f0418a44a401c1c000c9440001d4403901d02c0542d0a00c104e0300c0052684c84801c1007404280c09038030700000740a40f04520442c08125000140148000c0c80c00c10745110038040a000c0d81c0c101615110042e8090305c507040140010240c3d0301800b80040c54881819080041c0f90f004404039408079001000030401e070449480558007250300004440c0c03544018503000344030701e86c0182d940704 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 731227607 1250 731226357 731226359
    0x26030601021218040e0a050105090601121707020301020706050a1104050d020d020a150203130504020306100804030e1e0f010e060301031403040e041208060a05330c03190e090408070f0b01 82
    0x5c1011942899007482240240055203c050b0f841d504c4883c01d0050154038a0149107003004544013203100b110060204c80c0480c504881078010a00f603034003e07041a1042030310b520034000490f01038030a840714038490451080c10700d0704100c00203454400b0b07000081d110b04c0c0e103921503909640d1003480c14401481164a10398034042c1a0038081c3d140d410a041203940c14203903040014281c1064002c480c0f19002c02000d600d14502455020307540c850300907000f90f042042d403245910603901c03040b4604040c0d60045c1c204111f605003c0d4204580ea02c0c2d80c14240d0b0401c8120086030360552940820340e810740c0e034000c811204a600320215540707140203139071110b00350210600030f22041c0b1080c007900306109182e0307650701d12840c1e03502e40900036105a54410f05801041c01c107101c44984c850040001902c0640038602116003d50200407003427904441c0d282c0d006038100050b080c0d1017101c800c2c003161003030b030090a14003950742c2004001409000c00502c05403015000040010400c4941d903d0521035079440b004000c819 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 731228857 1250 731227607 731227631
    0x40c020a06090c212901050409060f0c0e281214060a05180703210c060e010c0f0e0306060103021804050114030708030324060c0601032603060102121804 67
    0x81d0a01500c1a45e41c0a0350003a400d0040071044000f03004006031202403a92031b4a04030070300009010104007034482994984102c500c9190340c0c00790210260699450f591136001d524204400031002000c43c203100703181c421984c8040700074088140d04807150041c3c4480c00041e142003000c0464010f0404203400e015240400c044c4c14950360042c4c3c040d0300d030004500608141c0300c41d86580e41004d400701401d001581420f02580c07507900c0a03004105002c80c541200c1c00320140e0740305030a803a8074401c44000c80c0d4654907a0344c465a840304194040c2d040e00c2c034158600e0010100840d0301c40c040a00020304060f000036900e184419200c2c0f4041d00300703034050802c000c10360f910b00340403900048032a802c510074051020000f175645d00000035240215030303200c4018079501051410400201c81001103940148060050f0708503500c040c0300b118029401814800340304040080782e9060020340c05900030008030b0610030301c941641c0c001010401070418900f0706079130300c400315040c0300c0c54001c20710650b030300904002c086d07200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 731230107 1250 731228857 731228909
    0xd0c03050c010903170610210b06030109020a02060c03070c0609020d080d060807061106060906180405030301050f010f080f04150627020702010c0326150f040c020a06090c 75
    0x800741c17002070b0141c0140c60f0b00d000c00a05958020b10040014803150122007007510400c4000c003454104480000d04407040004100150800da004113856a400b09a101805070140b00841d03011b01440c1c060391441c9030080018012041b03050000c2c2c0000d80e1030b0030800454941d80010100300350003041c1c00707441e00b01d42e080b9031000c0c01441c000d041d0b45018140002420341d00842c404003405c81c2800240c40107941d00414880491f100400c0a40d00c04055405441d021109001c0d80d40114042c3d0055950f944c102814002542c2d0b200004904001e658500d4900c1541e000405c49d4119036020948243d03a150790074203140403000041c07008202403a2400006040101e00712a802c080c042c21000e08401500b401404103d004612002c0c0c045076400c01e007680081d12074400724031a0b0018811b01c2c2c5400002d90139119074064203c8a0890f124820390840c0010b04e009030381c170f40902070b003160140018050444c009448100d102802460780b500e03002d5080401144101d90070203007403802c048442410700d552035000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 731231357 1250 731230107 731230127
    0xc1407140c1c2a1802040b0c0d030c14030403030510030501180302120306100f02010207050d20160902250302071805060109030b2505090103060b0c0d0c03050c010903 73
    0xf60084111100391000100e01107084201d204001280160a18040b005000d01c00e01d9804213044690800000c02e40081600180070294100e030000d015075200d4000140866592401600600881c0b216020700d00c241a800c890707010380d052070040b9981d112211064a503040701d4100400300c3d400e100848410b0303120f10707a03058240d9000742d00300c0b1780184059000200e1b500c400e035031554100e00443d0340c080c1442d00410107000e0840381440010320746106500e42c0ca040071012600c40f00000d99807403006034400c4003035100c19844c8900d00f01074101d10702c001d04200706100191040800103034011032040c2c0d2040021203c2006919100c040300f14802d1741e0b280094840c0c18501030303d041c0303280300c1c01d008265401070700c2114810300060f150420013500719110f90b2002d808c020301445d00c605c9460741c0940d01480d20b6a51600c144000d803141034a031034a0b5800542640c00940208000340d10a02035a860007030001455501100e050804270701e8102141011101c038441c0740c4c1c1203001d56003403038888000c0640c0441986 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 731232607 1250 731231357 731231363
    0x1501090c1701030503041203051e190e031b0d021f09080f030a0c111305070e040905120f1902060603070501030c050d05370c1407140c1c 60
    0x404102150078440d05000c1c000c1c0070103440c5900510080c040c012004080c1e100c0607000e410260f050090318111805056040100455501c00100e80514003803500190148424031908003140d4820074440403030b5442107400080450070107078600b03250050711007803c0351260700d4010706040340186030108154000c1c4200c161440c0041d08c50710001400c0038000c0340c11401000b101004c1e40c94041290011100c1c0c0700c5480060340c0046c40b079a850382c3c1c2076840101c041399404188101158500e03000001400c21399407801128021030400d13008800003540440d1240a80100304103480d107442050501405902410309103650b540e4a501c0b06400750b5800144891041c0c0007102200c40c9a07813031f0300c011000c0c6d403900c28043e00481c03024008210040c420341c0000d0f501c03a0040ca04281030721640012442031445000028540c003803412119072040c03002d405071001010403402d0240e00307940e06400c00f110a1044504c060010541c107842d150502900380030f00fa80041c401866048040d1030550021069401d0000071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 731233857 1250 731232607 731232617
    0xc110607020a05030409240e0f0f090a06050a020f03040c0e100b0f0304050a12050d0b031507080403021015050907032c010902060a111204180e1501090c 67
    0x403890341c40040d060b2220395025000d1810145003003260405001c11080b000101c03020801c21b84e4441420194080c01403a11080c0c408042c1000200c00c2c8404901800c04080103011200300b03c400c03070000a007040a503070311240000e000d41d00c1e054580000d014031803026100310790010900c0140400c2d035160b1015640c41c40e01c50907a6442e540d24007002000103214142040300244212100707a0b003164080c0d40c0c070901800541d882da90315699100030806110101e00041100401c8000d401e00203071140ea04000c40c268000c000030f500b1104064060140104924100541080080d08261090111001400d004001402103100020f00c8126002181c0645405604514002010f892003401060140204a101700709544444080004800a42c2050b0700896480d40480030050b22000001d1804194682d9040305a040e045c100078204144811500700d8502c050006012080c452081c00501a40b100740004038401460b1940c1d04151072104900c060044074800001d8900d0980c218005024041c2c1d18 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 731235107 1250 731233857 731233861
    0x60c03030702100c0f0f020a330e0c0d030c050303011d072c0a0b0d020405040606020609070915050301051501080108071a0a021c020a02010306050f0924040c1106 71
    0x100380211281c00c0d959000098910034102005c6011303079110701c1c00b90b0f0148107641c215241600c644030700da8030180c610455807010f00780c01d2002c2d04000c0765012600c20301440904c03803581d1a01025980354002142e0314481c410150110040500940ba2091510752040a40c0d0300d0790386d5103c10041c04214150301c0b05016168800007032a081c4078500003106d83c03151405290320300742d00c680c040e2805080032241503003099406030081518041c0340090700b0b48450020000d603865003080184420344203644c0c00402598400c2c0d081c803400e040c000c2180700544001c2d150002d580c49603001e0300c0000c44100d900131030705540707010140200c3e0005429000c0791100c0a8840020a0f603035550703400c0c2e4440c20351241000189503040540b000396000002040016190320440e20294241d03062800099080d4190b5005640f0850a007821941c150203407400822003112110854001100440c43d0030074020401240001c100b02405040301700710341486000782004d1700c104075205401e04003034101101109040b40300e124400c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 731236357 1250 731235107 731235133
    0x6010504020c1b2116090903051b0c090106020102030609180316061b050c06010e1017010f02041412030a1407031407080417060103050706050d020405060c03030702 72
    0x3219000d110100c000c169030381c0d40000c41c140d036424401c04160701c0060200ca01100c03076000140c1441500044010b4600ca5116810b850171411141d44140140750801e4010400b0a41240542340c0020428035010085c003400c0744900d00b421001d2030380341e5124043c8400403851960541c003562080c40e0a0300d5002c03480c0c0b00c0d9505603803140035800025075950302c01c01110382c0001c4201c035192a018852100403500d0780628000801c55039201c41030340005074020401c141407010821284d8010300454494071402e0034044448207071084240285030000e0200080009501000d40c441c0650072450442103440d6502d8402070b1555800d4490305c14416880c2c03e55420503e00084102c4100183c641c8800300c51841c3d4034402d850b540c016280907014044044a9503a1441400c4010207460f40710b500c0b62986d035418240d0000c0845410001c005030b030b8bc0801c0042c13000440011315042522030b60b0600645585864a261020f4452600810382118001c114144c400d10000091800b400c00c40d0265801540102 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 731237607 1250 731236357 731236361
    0x30f021e120901090b03130506102139081f0905160303081806070905010809010f021c0b010215061512090a030f0c0b181c08060306010504 61
    0xd4500361890300301040007581c4012201c000c10b62054181860766260b40ea0382840c15440d002100e00d41251450200303840101704003840700301d52013034000c881c00b944981440c0104c014282c400c59200702c40d004001c01c4205010001d03107140780c4c0400d03824444004120280511440001c0000104507030454000e001c24071281c007040c03c0c10006c074180386070102400c4100380300c8094a103440040e10140140094042d920f403064001d030703001d14000c0d1540704003403c0020700c95103407011101080c07405800003024441c078140e001c0b66800c201e804c00d01e0f284206481d8900e00500511540031001c02d014400900ca003042d003070381d164041202c040464200a405116801a07072a51000c023041000a60741c031002815600d00040c030300043c0310312910f00ba4103084d0341060098001600381c0c2c0d000402e62220642804240e03010503c441e80c49001e00d4500c0701545a5075418004440245c040d44402030182a110fa4044003003141c1802e0b0800300c043c3c00400c180d465000b4240000640e0780c00d0090085800109090034a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 731238857 1250 731237607 731237653
    0x60503120c030d1112100e0615091504050307081027080a020304090c030f0e1c08060d020303031602060108011505040b240901020705040c09030308040c12030f02 71
    0x100d0185180c44040154038005000408401c032108409000101c07102403100d1005104421a40c9665034040c1000c2035645600e1f00100018402c850301c03000503031110b540405903901004191681c20702c40c140c0c003510410901440d0000750300f41c401c12200280d102000240e1182d03c0d0150142009110a442c00c540d01c1c188a18610300800d0040840c4440050041001011654014070680307007003a484081c0352040d42d8543d0707010702c006610344202c40b220030151312500c01d80a61080091103e0700e5080b0005003030600d501821004d004003540001d543d9290020b142203030036401002d681e960310308940030b4507011408102143c0148540e01c00803961038014400c980410740f03603844003855180b515041002405800125a030808981c046030078070164903842410044210509980d00e81c109103000904c1c0580550046129a00b007644841d00540c11003ca90305417900f41c03800c84040c2e5207604050701c030300c05035500002d60b42c1240ca1641d428581c0c0200310980d043e20079426185021444001c500c4a0900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 731240107 1250 731238857 731238877
    0x8060906010c03180f0f0303110a0c141206010b07140c150d02090306101505180f060412030305071412011503090c23060301080304030b0402040f090606050312 70
    0x8031000d0b400100c2c2c02100500c429104134681491499241c0380701032500007440d03210840b0300e520310400703208154019001c4556443c440c0b00600310a101600d800e0341708103141c410044080d60300c90b080105900d03190700007001c0340014000c03070b0f003030f0750f550032840a142e0300150081c0c0e009030f202c4180210008000c40c4200d81024002c100101c004110300a41c1c101e82e00401443d403102d94200f00480551300e0a000e030070700c02c51745030043c074414519100091701150811130301c600802c0010018160740c1810114824520101691541c041480d41400704050780704d95000009001d600400c1d01c4101607154104134440c001c203554000c0c0c0c1c2808050140310701c0c0a8621190142d000080c0180101c40100b10f40c11602c0349140340c013207194900783e219241d004a003030b003040540c0000040e003004c2664842d609020078a005440961840d89069107140c0c980c00741e03000080c010071204000c50103560b52504880d001e280f0052041003819900d10302000100014494507001c1d0240c08404a6003101000c107072201000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 731241357 1250 731240107 731240117
    0x402040f090509210d1803080405061501050d110405060d0501030516120b1f0620060124140c0c090f100e04080f0f030a0b0402040308040504090201210605010806090601 74
    0x480302c0c0c030400180c0200c801c0c08202540c038130300c120701b45820014668040e4041d0b01d5040751801c003401d0490030f03c14000c025440c0301c103000e1140e541d503991003c2120004200c0744000142038444024038240d501c15507014541c003000100b00d191207036201c1e41c0154120382c4900c08941c800b000b9490743ca041d034450382c4118004c1e02c039010030709000310321502080c03a4070401004540e140341e00303007240e85003860300241c000e00001032003000d44041d118a14101c0d81c50400e03050008004030361500c59821001d804019000c06145094544035818038010700707503400ca00f038030191001d841d4031a01c3e008075540e984500c2d202e03105a91040114240703610005100703004242111321480b80034104000c1c46807500700a03108a031f0440007086940f1056000002424849440c422001e5503810304078501000e5880701c88010f4801c40c81048100006202401100c003116400c0d40c01040000c914001a10745d81081c00b150071500801200c2900d5165070f5a100006603042600c42e1141500c0e0300040c0442010704680040c0812 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 731242607 1250 731241357 731241403
    0x1f0b040b0a0506070212010606021b0415170f01020319140c1801020c030a0b0103020a080705030a030f0216080319030213030b2502060402011101090c0e0705090402040f090509 77
    0x418008000d00d0381350700281070740c41850200a051400c5a181d41d2200005802072019014003050754a42e20101c880115000d20404507030b007091502e90b040d94415480800528004441000700a011b0700712400074042c021503c1c1e141c03180c624410000c0c4d070800c01140c0c5203014000c803404030326103001e0341c06015020700980c104451800c41d4100d01008d298038a0540c0710f16090070041d0740c0d04009085002d0b20450382030440d5459481031100400b502e0f00909d242c1d1300401c03800d001c00d4500241820355142c1604d049101c002540d1800ea0501d401501503050031a61124040b0b600c0800100802c412800110300310040c080140c2d04400724051030b5a01c42c80b1404100b01040840c02d6600045d4100f04030f001460755030000111070741c46007641c4810b1b03000560032810800c0117540c0c12108080030140950020300c012800f540d10010792928130b0050088111301c1d840072804451041c02550543c860192046582d0b5407105100781c0c280080340708621146040c1000100b00d42000320320f112504200f400001642c1c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 731243857 1250 731242607 731242609
    0x2006010626010f0302030613080703050d09020607240b0303090f18010801061d0402060d09051906020d0b01030e100207031b140114070905130e1f0b040b0a05 69
    0x2080304000780c601c01c0050412522407804074240940202612403080403003074610700c1071504105c0d005203000540d00001c0c540740041008041151b81a5030326107015a50340c50520b4501c0010b1200da100a50440804a40d0804010500742c44e440c0309058600719480c0c0030201241c0b00c058410450720303e505608240074066081c14000d0a003003d80000921078540d43c403c025008900315400d84c005c208980d1540f0042200d460344400f4482c09043c4040da550b200d1030301c1d03000b246191080503440c01ca0a0f0340d070b0088809002e009d0110a4102c1110b00c03142c90036203030074101a0b02a4004000b0149124989280d12400398001d2240c020302e4100f00014103845515000f481d0000d40201c0750550a22074440c1004241c1405600301215031072040d0900034842c0c040031800d500310b80040921140d40244181441901900b000000c4102e440c01c0312640e1409180d10110b4024025070445c20b00a440360b01014102d0601d070611b8a00800e11007c01040001d0307105c01040265401c50070b0070754006607191802c4c002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 731245107 1250 731243857 731243867
    0x82a0708012f0d0e0d090503160b21090d1d0306071d0411070b10031e17030a270b150102150a020306011106010311100c0c0f050120060106 61
    0x9002100e041c00b80c2411400c1c000c5405941d16080035030702c2034229000c0310381c859410092050242006030b000300352403d07090210a00781c01c403900805403440004240600580d0030040300d07a0a440f480b481407001c50130a00e00e01990340e00c0c96081a00402c08840354194451101d003e000a0b10500400420007620745200503030303c0d802c140230b51445080501c40c503680e140e00c46004014150f0030311140d095669810303040c5481e41d000013030031302c1c201000b803001d00b04080b50f2680078586007100098403c10801e0b581e4a015442d40031000210b02c00c0c6a404420091200354542c010b200782d4480580c01801c41c0c440b9441d0303c42400007401d00601341002c080c0403903052503140d090740b070b0282c5040c01203550307100350140141010071044038000c42040d00041008059640850300c005a0070500700181415410342d80e4882501040c415a0f07070145c01c85640101589101d074205904894014055038001a110300050311101001e01030a804643c010080c440144081054108442e00040141003641d00b000382c03c40e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 731246357 1250 731245107 731245181
    0x506300108010f0b18060d08040b130803090a1401050403020a0305101d03030a150902270f1302030a0603170409050f010e1f081603061b09060309082a070801 69
    0xc2c0090509140d500008d14200c000c1018052620620351500314801c450785031451503030401c44450700180515000d40e1104600f140c02d0f50b802004044c15503500000484003400744c5c1d8400f03540441d196000006100e800b03d914103c1c041402d1051001c0910130f90941c025415030158180b0a6108000046240405521020441148040102515503101c40c20001e9030130482d80c1800c104148201e1444030414054030540d0b400d000d82d001102c0305081d40010728041d400101910850790000005080c00320154418006540d00a40320020903480c030500000c641c1090207031716092450311022600040444000328106e501360030b032000d05503072a42c1040340301d80e81c000300901c200204c9a802040119042c090350710000c0445000a458900d142084402d803a80441d0008807007a003141440c481d55446401c00e41a64024100070507250201d1400c0085031055290180c03220611110701042d420880e0841028000498221008a502e0755580c1e802c0304e040804400c42c0724244e0701c0e801102d01ca1003045034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 731247607 1250 731246357 731246359
    0x20a0e09060303030712051b18121f020c190503040306050709180207050a0804060c030905060c0c010503071b03090302011e0e04090507030c03050c150a08010506300108010f0b1806 79
    0x20410061032070100100e400c0f01e0a40270160a003881803144500f4543c1001c800d4404640090a800030000311410200420117050502c1c250009580e21507088100301f4020300c1d80c00c8504810340d071880e6040c6681c49801600080f80c0503410b01d00400d44151140c0385107405e890150114603003d900ca021114000d6001032000c407040e02a10f200a004507401724051b00c0140600c0c0c6a030091800c051900030041e00711038100c50b11a0714180401e91600d2000140300400040030308009a07652030703002e0182d0b00004da0a036540002c40b83c014000040591000051342107074401c0e02e078403011413444020724031605800e182c1d4000188080c40a10301c1443c1a0f0861450a070280701542c21454403912020103c4e001a0030645440e485540910311500381618489016080e811080d03041042401e00102030381300c180305480c0303d0000030a00d081008a8600344485c80c007075001034415100306040550440d91424807900815519010700421040c8090103000044240100603212248003040002044540a0030701 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 731248857 1250 731247607 731247631
    0x1807080f07050f0d1b090e030310091d0a0c0608070f140f070807140c03060f161101020307080402040c02010606170c04050a0b07121b0212010b0301020a0e0906030303071205 76
    0x2660101c1d5805e44c4100e0810004180804070b1810203107154140c411992001c00154000c0082141c003414640d2040142c034a83c4102040d40b200c0c01510010146152002002d42c1c000c070310f218420054141c800c202210415200d2915a035105c3c0410f940c007503036070701840011505903418110249012002003915210560503141001c0303641d15511040e80250000701c800b00e8260460320201e46c42000b040580000c12001000240751030007001500e00700240111510f000c10745038000d510f5005102d030028440c0520300840d2603103884040100840d0068800783d010320315003507500c6400c0e88180610029101c4540f280440ca07000c10040c5a22200300404640c1255002d110208042c3c0d1490b647c00028492000b01c0b50705d68141d070400c466078212000300c00c000e00c5003010400503190304505001804a404403003c2e1241080c1c00c0c2402c0c007602d40051b203d540365200090300c03900142c1000502c2060f803400d848a403050703a2042c06150b070340e00c07081d00d07400c011941120749172141541c990440c9500007040302c55 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 731250107 1250 731248857 731248879
    0xe1e06030a0e07360e0703080702010311030a091109070e0d11060c030a03061401080a020a030b1903030909060b0f0c0705030a11100903020609010e040e03031807080f07050f 76
    0x155150900039102d001800d074501041001401c201261540601d5900e03402c200304000401d02c0461b501c051a210040c2a0f0401051a50540e80030758000441c0b01d500c6240c65030303285041a50f810007000d18017400c9031120520500d810143c24100d0149216a2041d01c541c0407281d409030400102c6448040d00301e0380c01e589042d04051648a4a002c0c00b440c440c2000210344404072500701a0541e803281c0c05c24a614441c09003284010380e8011502508845007140041c1d6543d041c0704101c0180c407085010a410180c0100c3c500e200c2d1603840300040c22240241c0d903405100f45c45500d200241c174021300c1040c6030f102c2c05010342d840103503081c00102100c103100c00450308010ba540d4042030910007131090544840303000c090f00242c2e0341071036280c090f4108030b02d140140045c2e0642e070008036580146075606041100c204c0c0c03042003544556005403401004501100c0c3c50f49000c404070004040c000c400c1100c1c43c050301394005008400029044501103502002d084a5807c150521a5020241100d1541305452403c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 731251357 1250 731250107 731250119
    0x3020c120a08120702060c0a05030f040809041401080c1801060f0207150203030105040f05090601090f020d09080d0605030706020303190f020703030b0a050f09040f02010203070b070e1e06030a0e07 86
    0x801840c1904a01c03c030b00c825441d000030040d0400b02c0c0205200d0441600b0801d1480041e80b0004882c0d10410006400145460b00e0504100a01684125540040c035044241020b1a00c40311064101c8418008458800d4180810301c0703000340c0103440345881031182d50014054580503407a040d03400e01f03030303441103e1070b0994441b2450310b0304900c80141e00260704004014009400d1038010220340e036100a000f40031a040010f1020f5a800051061001c140d582c2c564940c01d50406804032000d40078900c40500c0360400f07502f0141300d143d0003da640c4082516140300081c3c181004a1124121041da401079800c6556007111400c1344420210448002c03955440c418490360494806044020701135038000880a241c101071100140c4141c010303d10440300e1421441c0c3c0c0d0f0b03503a500100e921907840042181151002d1006030315500881700014160141082001601c40d4000254812050200e48001518100e0307951460700402c4e030306040e60010000c00015000b000c03190880b0304c02c0d8a40c1e03000c40c2d09545e5a0f003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 731252607 1250 731251357 731251373
    0xb1204060e01110406210207150c031d0709061202150a020c100c03030c0e030a0609020a0509040b040b06090408070f02030a05060c040e0a0507050703140f0d050a1803020c120a 77
    0x40c1000c00401c40c6c20b10700c4201d148a00103600c001890083c1e08525290858640401812130b640d10507505946400810560034820b81149003a0720019200411030801258559120f0076540035004402e1b1604c1c070000754028050440ca5202d40d0050301d001181603816041e8613080e40300791a000150b10038841c6850309511881002419a0309030365401c650001c05150080503180711966820400c2180300c01c06855940201d143d80d00503a00900000d9032031018404100e800409520039944002804c2c100001e2184c1d40d1465031085110b600c4583c4a6500d020402c680848160b40103000044184501d0000a03194541503501500040495000080310766445180a10880e02421042030208041000040340c0361503d402c011103203800d00440c681860700410078083c00c0b40203020040790340d804441840c8a00d01300e400b140000542551303075441c440e034a180580401d0f2481026503161102580450b601e00007066200c0703130715a004d0440710241108000b03a0100c0c40d072070340e51240a40010100016100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 731253857 1250 731252607 731252609
    0x1b21030d09120305060a0b0d0f0516020706020102040f0b0702120a120f09210804080124122301060b07050c090709080d03020f0715150b1204060e011104 67
    0x11039020031052810301c0d280c45000200007000c030a02d420310080c45100d5407108405002c0e00c81c000c20454542d240030303100c60090210b020303038444124601006c4c0685201d203500d00c0890441e041c0c00302ca1100b9078442c8100c2c201d2003140b04001100714041000d1001024000040c01558001880d14105815006a0500f040c010000480c4c036000705400000445802c640c84940010302c0c5d061203000c02d458254000a0b00645004484c2c0d42d0303684404500821071349a00b582d020700a404000c1040310b40102c0c490143e21040642c410070f29100307400c0015001d480f0a0040681a840081c110148003001d20300d8610b00780200e0781441e555201c030008180204102c020f00100340c02400140001d5041005000000002611040400c1468101403040340c4001440051a22091400503510740c0400d00b0954180284040282046100300303c081003c0400d800040522484061070007074942d4030500552030f84580689062103002600c0041d010031240d90042c4001c0994000101d9a4250a56010304941c81 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 731255107 1250 731253857 731253877
    0xc08030c010f06140a260604030203030603010f0b1e0a120b061009060503040b0405160303030e01050708060a09020f07020a120b0a110706050702160b0a111b2103 71
    0x96080916448403032802108000c0c2004590811604c8000000c01c805000c107010f4151281007007500718013054545c180c04a4403103105c6040d80c81c0b0703041501d002512940103980842c4250309040007031980c050244142c10b49000000c00541a103000030304420644042c04480320b0340318044001c0000d0416040031030000161080f20149070324944902000442c1c81000d0b00c0a0070000e03424428007140b90003004990304143c21190b1000159214a03010b032826a00b00303908100140105400410160142c00903020080300500030300c495502c2030000c45040d4070483e100c6500205411003007201d5800c640c01801d0310041202441c3c6010010307008940e035000541d1000e1341e01000c807441c510900008a40315500300152000030300010804006010b21f44c014800301410a075a05c0d004949410b008103c0ca003241c0c09103030f4203185025600c2e400c40301150041c0d01000003003442c811070f240b0507810205003541c8204a4070801c1e0f0b21010400709105031441c001141e925a00003464100701c2115041000d81010b6403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 731256357 1250 731255107 731255111
    0x1112030c040603060e04051207050a06021603020f010b030607030f110a0c02090a060f03020f0301090b190606262e03030f180302041e29100e0d0c08030c01 68
    0x129045000f800c40303016500490f2206030040c24403002540214101e650086001c45580e201c46c02d80c00d1541c10b0012015008010a00c00501031010030000d050889090b802a025100702c10b002c22002421f03075000903807403a03060304101d000440e0303107000350b201c03402c10326040c2000526607003d4106840d1590020882c1400301e2601000501145080c50b60554841e030031301d000348401858032266000c0441035000003031003000724450b0800c1c1c54170700750300049129411111420365420b105041c451045656402c4074009402d002000c543d05000d40c05801421120300c1000001106001141003103000142044801da0140d5110311804d00021001072041c3c150119074070380746841d616018010140900b41d01c010b0100d0390785a001c201c2d5460050f80100c0c0c2e0162030208200c0b014421070041031039000010b4400c42d290004074103850b010318010781058074004013420311516044c02081030240d8482c881c0000505180910110381c24a0a0300304013141c49800b49840280c2c0b43d01425056402a00200070142c3d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 731257607 1250 731256357 731256359
    0x102072705043e010c080913050603100c140307020a0b07082a070f11060f090f01031e1e0f0c021002040503191a0108070303110102090108071112030c04 67
    0x12580c080c40a050b00e9071000030007103078088191984203001c0310f0720720703050118409290013404090011a048104020540c000030300c42070f0780c901c0080a0945440d4080e2041004032900d1640e42e00c110059078403552503c012055a1450340100761303000415403000c5004010440e8000340d00c03070b604c4078080c0f0010345440200e0b142401c14140e100080c90082102d10100c04d84129003450b004044804c001c3d0401030f00701070344c0000e04100b00020f104680554104200242109070f190008001c0d1401c0d0204490600c40342406030011010b544049981c01100e010b40f120091001040f42d0292117019040880104155401e20300c02089404001e042e4100d40c1c0c6486000b04100e50500510040c200c070105d086080c2414a40801d43d160500d00d0655240c80000c096075040c81041c0410748174071804510541f50660f101d0741c00341c5e1204014401180803074200200d81c0c450241c18003d4420f05801a9907d101d40e40d1801400c4a4510404041c4025806900602d1001e45800002180b0505240c060640d0303035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 731258857 1250 731257607 731257643
    0x91806030203240a0903050901050703090b0c03070b0f0103020a0b03070e130f1503120f050405030a030c020102060c0301030506040308040807060f0b120303010e010b1e0d06090614010207270504 85
    0x443d03c010504c0d00d4051401071003c0001c0c0c1c125054070b175810420318001c0c0d114902843c05031100304050300b0881603c400421402380348640040180038042c4504c82e404180d0301c8211546030140003c2c08000c5d84123b500405014003452800911340c00300c590f00d40030702c880b80c1500200760070140b401e0103407c01c030f42c85050300c8542ca182400b13010309120007088030350315461458460005000c3e0b800d904108000e282c104165007140f241d4241e90161900a003600c6c8400c0b807d180107404004001340c101e015000f5080002d85402c2e109054904894008000d411250b480766421100750130014022100c1c40024003010b0f001c02c05510070b40342c0c941000980081c2d89810a0208000749010504000d00c03a07000300014407900ca0683ca040d411608114070701c545512904449142e50b9400c00036004015101003100c162290241d000402294204e004c20401c0c1c5031030340c6038400d483e510054114003590044500b0002410318039034540c29280c04078010140b907a4004091803d682c8145c2c1c05444500000481c5040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 731260107 1250 731258857 731258923
    0x7030e060f0105040c0206011a0c2e0e0a2406050604080102070b0903190c0609080310090f0b010509121921030902060a0c03110304180c020d080103080306150d0c0e10091806030203 79
    0xa003942c0d0060403d00d20301da99070340c694162a1003000071481c581000244800485d0801c5010c3d0800409403525503807100642030007508404420b1b11085010381c00700c0c100c1c01c0040308850140e5000d40c032f1202e0001160703e06495100181c9400c441e220707520381d00032000c204a28007642c003405505449441680c40c000b000002d41d65400c82e0602241e181019a00c4aaa044001c41d4021403056406200780492000e1a9040c90807542c68000c00c0c0c13505150100c100520301075502d1841da5020703141284408908012401c440c01108001d4001104010624409001d01000071840f8882e1400301c01c651074004540d07046411961140c800003202d00c00859101d0914081c1c1d040e6034255200500682e000440300138216101848041e0005030300002080032511100c490a4100144006a40c0d0707458103403085c0c2c0c0051005800d000006a200d80283c9a18900240c40405280003a40e60900440c10100c02460790090305c120107160698035840000140c4050102070b28400013280002c0d00304d0100596650 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 731261357 1250 731260107 731260121
    0x51027050709050a141212130e040c03110f030708010204030209060d020a06050711062803090c05120c03070306090b1f0e07030e060f0105040c0206011a0c2e 69
    0x100780849444203000c2a01d4240e0b130030044400b8951407207140c50628000c0b610500300840700d4200c500034900c0c41103000e50490010184001240b88809155545080c1c1c86e07140403040e24028176500c4125030810100d441440e0318001800000d25101b41e05400381c00091410003558050091650003040c00c105501d841206681d120001f50303131178480802694006000401180a0b8205001000c1010f10900403c06108154a0b0000d425541d17200c452900400d0070300b242510510781c4881034030103800d5880c481d0140c0149158804102c4021900b4102007180750404000c800010f44104071780b400c016034040095000443c00750800090704c0c8041e040c000c1407004020b0400202207115800e110303c072490091561308a9045004c015055200c4080441c040c002c0350791214018400c2c14180408948160006412204d0881d820002203407002002e0342c035450244038405908140380307a0b0140718003046000b82002001d1400b5074988842c03442180d50f001702c1c11032030b03003095103080008203074649040d11880c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 731262607 1250 731261357 731261371
    0xb03340b0f070204050c0409060b0310060c0302100e12030a0509011d060720010c08070305090a0309140102030c03040611010b01084b04060c03061805102705 69
    0x80c903000c030041911141d8802c0960080c012681c81000500102c0c800c0e00340d8001e020018000e1001c16070314544ca4440d034001351078000001c58000f40015a40e170142a50012480e07064014001c0081010708c81c00041c00601d2001c83e0300e0140306550700c0081320a0000b144a6882c88000181a0a2141c072a07400c4596071480040c010401103015402c000000078052360000d800c1c50000f20035a020b502c0c089040c02070540c0307000250300b00418200b1854016030755901c07855007950200099a9603410441d9104c03551030015002ca540c0079403d001c1e15464920400c2c2c5100107004076450311030342000041c070395400342d804030001450b006c1481c2c446440a00500701300305401d182c600928205080880506c0c50114540d98080002c00c1d07030078007076110540c00b04500c001c400d800c1510203812080c207082c5401301120100d45840c600844408114000d1148400fa114485848103440720044030a1008010180194203501070150001400ea0021140d40c11b07a451032515807450a24984031036002e94030040d03c64 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 731263857 1250 731262607 731262629
    0x1810050607050609160f0b030c04030807030237020405150303040f06080c0f09010f020a3503040f030c030c120e01020d1d040f0605033405130b0334 65
    0x20032004062000c603030281d0706d9a007e143c0d5603484140d840126446030303500081ca00390010075a4018503801007598006512542d0700c101e04014403007040e88103412079030340f00302420050030109030241c1010ba000b42d512038003561014411885d0540000d00e55000f0b54000d48414000d400d0900c119580280f010750031a072010f03145414205400c0c2b120102e030103034400780750401c02800c90035003032948200100300050b900450050113032510b00c400710074501c140d004145143d800600c0c1003088210140200e91007140c00c03000c0b01000c01d850365011585142012015030030440b00e050710101060241e05040e9038114a616501080e00311640068180707684414940d0912000c3d82c41a4012515031091040010b01100c00103070409807401c0d4440104a20f402c02c1e0707014071501e07400c0301030030301301070101a90390034128034039100804e0b90481c1041c411f01c40d0054a82014601e00ca181141025801c12080088000c0c2544c0324202c14041c4803810101400c0320041c0843c1c0c41460032100169030002c1006807a400080d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 731265107 1250 731263857 731263859
    0xf0b011517040b01050906030c0a0303030608120c06150604030c080109151b0e010201020c1b040605091306051510030b0901090b060403080a030b060a0e0405010e06181005060705060916 81
    0x83c0050b0480c14426613004118840c001001540c05008014011100404000c907854503414000c0007800c2900801840d0312800d9090102d424080b03041e41c030450040342c010103c44e03861120485180c0212072815030000d50511000c000140c0300e0990a02600e03102c40000b9207042141030210000080d18400303c0c0c29841c2602858285c09800c0302d1100300b84c900d041c403103810302031040100d009100f00d0410380c4040c0202108541c2c00040910b01d042c1102c0e040382c090224a841c1c0c4200320340000c1c2990000b04000080b04020000b9565030000b5038080c000d01c080c8003010341d210000c9402e80f1030359410100025981e020500107807814002c05400b500c2c00b8242040842c0e0001d010512901c11070001610074440440c11040d524841e4000c1c2c01e9154014021a48560716604003411031042801c1e210302c51410480081403510400c2c617944d11841000780420b0041c8040c200b420a5a803010300700856074119014041741c91307100c100c02401b0441c820801443d2902d000c2c8002400c010154440000c0340a001e14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 731266357 1250 731265107 731265113
    0x109050d030c020102030f040303031a03010e03040e280203041b06120b04020c0703050d02060c25020112060f05090a02070b04033006030b060409080a05070f0b01151704 74
    0xc0c0846150385030074211854105800180e180d80520401348203400c400050120405601d40c01002a100b400d11040c0059441c4404240c26104e082264000c240e005100170450f075005044400e4104200c05000903071141e1042c81c0c611465000414100b9484e000010720040000344008010488001d005001c426400d00c80004c0c800080299400750312611032210301d0080e83d8960460711511104804c4482c40d958a02d0415120030074441c4c48005801904000b0380c08114601c222083d240b45100669510110b9050000c1d01200e02c1109904010b01042000c4808031035109803001740c01e01d05a00d4410134a450b0403c40c08107002006040e20f079006109020000304200d6140b6001641410701215604480411080d020000340b01140800300800c0d00c1340a03607041c0d41c01036064a019001c548c2c1141e1700d1000340819280382000040182104106140070280710310040e0000c0c91140741041880c200323580312084c03109403e030480081207410480754066079402c0800c5000b4050b01218100080c07425407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 731267607 1250 731266357 731266369
    0x121302010504091d01181403040f15260a0605030f03030703110705010614010f0e0a03060f0b090c0a08010609030819050d020703080702160302150901020106050a0320010905 76
    0x4481c03d1002c07034482c0c400a00103400f40400d84481070b1440020044041c04210b480055135031804199600e0511390a15070040002000303c0f0162019121404901450180040c01401c91300c0c0454080000c407039055201c41300130b5000c02c0044209016002d007581810240c0c81304403641e035440144a41d0101e000c494031100c0100a403980181035041c00203200c0c0880fa0101d50a1241c1c3c40c0040055203002c901013090800700b1050108084280da500284045249065440c0b4000c451440d5024400c12420000551150040c00c1c0d612501ca0000c1119550500403888400050f00c082030320304c90101e48242c1f4541d0200c00103004040341e00e44070a916141d6100c40c04c2910a030005001d2024105800c920304e10302410407115030321b465107803c44d50b401460500406080301651721000602480c0801d200c01c2841070744040c1a244c0040c10180440c80b007151404466000d4a1024155502c0e1100090a0b40d202350401e0011070141c010381c03411010030030012005e81d0320443c149050090f1040180b001e03480788 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 731268857 1250 731267607 731267609
    0xa0506060609240409050c03060d0f150c08040212031606240b070c060816030b031e03040806160c030809070b13080f120304021c020604030305121302010504 69
    0xd854903580c9a2142d004214410854802e424804101d945090f00f40d01100c1c00600443c0d40440040129071100c0c17030f00b142c1c40d2000f6621158010b00b50140040131034003d000f005055445080c4400081c4101c900201c10b0b10390049182c0d02081c3c6030820030007075050808400c0e0310303020524003452800c44424818a450782c0b4103d0b014200d90381d03071400e03000e2048401510000b405010901d224103140d031403c01c000b4940c00075078200d8921b00d00040c00184940200d400b80d003d50000b0f41f05100030740000c07504030014504448041c0d8035101d2281c2d20810826004030f41411460300710003440d5038500b001d0715607191480151050505145400b1f1444055502800103250954107280c0319055489040145140c20040c0d08040c01040000034480700360700c07482c420324007160500701c26203c0c1a09001c0030380791100c42440b200d1200010801c009070040c50840c1080440c01a084030030204e40089402041a54209400c1180450030000702450856407000c2200c0e03001da48101c500c1855121640020f15074012 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 731270107 1250 731268857 731268859
    0x30a05150705040810020912070f14040b060a030e0f0c0a050108150a06030b01021207020604030b04032a11030a05100c12180303181e02060903190201110a050606 71
    0x21002284070944150101c0e002400b60301d0880d18805500305511009610004280d48504250002c1c80f07806080420b255085a111110201d012494070b600804c503011500015580655518080c00341d90b034413880944502045a0303400502d4107200348000c5d180c1440e00f44500351650003040402c000e652500f00080c1614402c0c03820000c29200d041d03041d00d18007202c00d201984a400f410000c0346095056210203084e40e026821a0881e0180e03c03143e1070144181c0c00d010707401c214104014070228500118054001e840703481c04110841c0343e503d4200c01046400c8d14007905042c150951810721003841031510030110210040c00c0042d8440c0c0d542c40d600c203e0340c03640b00c02054640c1600401a801007030410b10206400d0b1080c001980141e0b804403600429003c11404685025002c540c0c020140c4546500d4581c0f0959400c0c9036a2200c050003041881e6040407a40300700100142d403400e880034042070f145440000c28001040c00d00e44009842c2040c13140c030101c00c6501c44198000410700004d02c0d10b0308004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 731271357 1250 731270107 731270143
    0x91214040b090d03090518070206070f050405040902010504030f14010f050702060f1503031605010507030c1202070206161a0108010c091a07050708030c0c0d0c03020f0f100309060b030a05 82
    0x100d1482c080d45e440c19030394401c603031040c40d606919200c443c1460500e4400c90650742511500ea0310180c00355007a20701c102501c0c0000314148400d0003582003d501241c0340d00c2c0141846411302c2d0391795961500042240364100c40a0241240b0181802000d01428250013a178031014401d030b1514a1000b5a6548001c04021403102420041050300e039066a2084014001505a075583c0700203400b405c0416203c402c045509618104c0080c444910a01c1283e04410807540c480b1405c0318525481c6019401298040e40c2c0700c6001c110162400080301e500c015490311070710700c5c1010400b00c100003075a0a4816032003c08241d040032000174105034821996807d40b143c10000b40b00628820604240a020312103009010303102d200000b09091a001018110400d111002c40f001b41c021107060088090450070b00801d0a141038805000618040041010600001d8200700d01c0c200440002448062071a4010002c640c0d12a86e60040c4180d80c0110b030f00c1080e00b90000c0c01506569604e140d40c070400400c0c0000580 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 731272607 1250 731271357 731271379
    0x21f0507050304150f1b0810061709031303030e01081003021c0f0605090106080d09180506242a0706051e12010e062e0201090501091214040b09 63
    0x504c99000c6038001e1221042088042040381000e2681b1a00d0b0380e000c0042145240082c001c07040e00399020f01542c00c5aa2404450300386849480701e1020054400012800280600c196255400b205400154040c2e903035403120703000d03900c0058085180a17107140d0400f01410380900158881c0445490043c0d912815400c04064a0901000a000d00310700202a28100380a1286d0324a0540085055441c2c0e042941c51582803240155035051092064030510141c460348000d140c0702030780c0000d40c8114050104e00b0740c045070a601001580300072070245040d12000c03804030074603205a00340f00c81c84616200b0071b990f1100b24001c0250355920a02c02d440c1001000103201112803d88101003001c0c2c404401d81e00c0d03d0300000861964411001d0042d41c41d54032218001903007500e040c24a50b056441c4007580d007682c0c2c0c2084000d0140000f1100052010f540d01c9468000004400748600030580b4010014441620180f103401030201442c0d00c00720140c95000d010510103040d0f00c0048594461044400034150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 731273857 1250 731272607 731272643
    0x30c090c20010b1e0f030a050c01030f1b1101060b0901050d02070204110301150f031a101b110901050a061b060b0604060c021801061403180607021f0507050304 70
    0x15100411101303412001101e50594401c101c181c07201584401240c140d074441c004241416035440000c1c2002e00315903c210036507001d5500940c481507001c0c442d1003020402c9626110b0703e0813090f4595903000300160400c08104031866080c400c4101030110555424074029207440000c0c40fa005402c0154511a4009031000031135840b40d210311006070344d940086d512981d603456400e01480350f40b545a800304410740ea145464510070f2040b03040ca075001005100d2841c41030400d0080c810f05050461091181c058020381d05c1c802280c1d000e6864510400010500210340d50a002007000c2c1a4421030203540c00c81014014942c0045403001c1d0b1540e180c4048440c003c060070101c02814040300416003000b80020b0100d0359640c0840e030005001d009581c60103080362000080041a602441040300150a00308040c0c00c50302c2040046820602c500840781111240401090804001740c0354503001d03038810403c0681c403403804014840c0403c00020200401d1601803405070161200400051244501c40814160f13 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 731275107 1250 731273857 731273861
    0xc120b09010f18021b1c020d0801030f05010b031b030114060a440c0117060402160c06020715090e0708040204090b0c09010e0303031909031215030c090c2001 69
    0xa03c5045264000d5290002c515692507141b00e20078035140c10400f1000900081c00000c0b954240e1609a864030302aa107151207041106084480481e0325541740c8510708a283c0c1e00b008003401010b105040003e41304503800c10582111400049a21044200340400c1020f5503441e011004681202070120072802c0c0c4001154140c01e2450100200c200720b00c903400380054002d4002c2c1c05400b40345411071f400c60305c1100040d00c0b02c3d01541c04188480700340c00c00007011070031301d0b030060140c440c03030080048004a000d0b95508050002c6820520060b401400c4c10041110400001c86000025050142c9464104012200011402400a41031080700000703d011502c1d00d61208004d190404014003003824180c00c0c1504a901000305540010104140c2604501d0b01008481c01b9588544080c0802419060560058080c9043c180c06004030668101c44c40852802080407a12180700600001410342c585003c84d5403d90b00200c550a180c0480740f03140310340100c0b0903000000003925405101e4440711103a40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 731276357 1250 731275107 731275117
    0xd0c051909120b280915200c030409020415021c0c020f0a030b0703050108010e0706081f0e07030b100c1a1b0408060115020105040c060302031302040c120b09010f1802 73
    0x14882024482c0034400c0080e80030b1101e29109691000a0318030840c009030a441d070301d92444042c0201440c87c00020500500140b00b4018078030141c81c202a07403025000100d0700140c0c8010140c006414030343e11441c0d03040c811501084400b0041020300c0d0034026009020580a190090080448244100d00d50b0740d00307a83c0c0c41c000c50340032107900c2c0d26142c21701307000340900420b00c01c020303880d82021f1344041d10b03d50205020b01a11915030b5100c51079a1070902c144140d4120003001f1041d500d00301c901044009055174207174030034446504c0114003d8219803c1c85614050850306408004841c000600019505001003500c5440310b240c03644181c40e488801c00a14480a981d02040d040024000407000e0020880038121500c41c882c03004100c9494405900743d48048800800080c0030b20420702c5210700a07800340d40c01440d4500c0d14007000d48142d022604491040c078441021500700c10358500c94500501800201040c00d40340701000e54075200556840c86a20b02800c601662408c21a4180203803660607a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 731277607 1250 731276357 731276401
    0x28090504020d1407020d170a061715101802031e011e05100906050a09080d0903140a0203101112041112060c070f05030d0c051909120b 59
    0x5607161204940b08004146180e48520a04540070000784030b0781c00402c88010f10700309070326500505c0c02001d003480042c4100414900185944007008549808984403e248102700540209005000070b4003d68144500802050222400140a000103505516058030f40003614030301507220380300d0708162402c21061000c01e000d540340d0240005440810500c1d0400ba00e1001c076002c40c4035030b40383c2d0107010b00300c0030048150340807447e10798041004512640081a20300702515141c0c2c2c2040d21900d0440c140f0000980c6400010940e04040c000d0010005079002c0d001a840c005001800295001c2034859001c580c0c2060040d5440380c1003004855070f141140c2403444800d40e10800e600d80b91400061348549008401d015914041244c43d500704001003440c002d11100f034019041c141c1c0303a5100321440b8507005c8110745502080c0030340c0f60001c0303460041600c00f040d95120161a680040210a21141c0c800041d20130404003500c2001103080d90720fa103203500c98216941004d190354410358022080e4461100c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 731278857 1250 731277607 731277611
    0xf0302040f090f210516120c050a030f140a02060606130512031e070b190f15140f060f071b0b070203011503030f0f020115090603061128090504 63
    0xc2010040f0600d5520461103d100d02e0500c94010303075408071a58060148404c1c1c95160032041701c3c02081c0c80e02003c61f480219071408603800c03641ea580b40744c02c2c443c00c8441107010641919500085a030032607038011401814500702e904203c03218900940e070b6032020300340b603008210018601905907442da070044060100505a403000940340d40a0b15560380c01400740c801030701e250350b4003040281805802c0f4ad03076094012103004041d80700e5107441031802c8480d00300c1698441c1d45170303201d01511b60300d03004500a0084c5c1300310900115240051510040310104845481010010000d141540c1c590701600c03500c400e200522525210f8900d8908100527400340712420850444070001803024980d4000c0c28807901c281e000b880030300000f640c1d50b017407404240001408101e6504052100e40d110390b1920400504900c0046944000440c1480031034807290040c07102951110310078014403c2314040c0c003120695401010307207409480c0100040b000b01070794803640313003160f9000a4480c061287c0302203c0604001481 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 731280107 1250 731278857 731278883
    0xd08250f0318210204140405150603150403020c011205100b071103030c0619090c0506090a0306061404050906090d180b040f08010c0c150c0c05030f041e0f0302040f09 73
    0x340070103101441d41c1248174504080040f50030701c1c9507807411800b81c3c1d486001418031041500d0010f40b04000182016054450502c07032060184280b104940514002d40190441200d0700340010919282c4840c035402e2603040205204500200400903001c072107180314a41e850b20854a81038551001e4246c11a03411b10000c03904484148000c1003250140203112501c40d41c1704c03d05c14108054442c03c1401518000c1242020803d41c1000f6006060900c40100860b1003961280d6030241102c0090300508404402d401000d0f555007410710030309800c600c41400030100c51410080741c2da601c2e04203049410030030080d014154050380e110341031540645401451305807119181d501410070307410300d4031409442c1c0d030800b621003091501820142c0c0305036030042c00100042c80da09030b80301c029094102d686010007180b00880008a00203101514408108100c0c81d540c551402d185c1c494030003074842304503059001181003003100001080001085035415180898440a0f4592100c010003c40700b025000318440a1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 731281357 1250 731280107 731280149
    0x30e151b090406270e060a0c0e09090303150a050f0d0503071e15140a020306131b030c090b040e180f0705012304090e010b0d08250f0318 60
    0x24032610390982050a1000c0c212260030000e06917102c114540e01107410090205504950b40c0c0c1006500c21640c3c10a4011300040001007000c42108840c50001500080709010394014039040b52504018210703041e881181c10311002485214a2005007440344406a215400300306003401550700e4541c0040a84890400b48041c508405100300e8040f40c1107401c0040c2c1c1400c5102078403400c400301f243c0b446080030300d030380d4868040c000350720141c00300c2da00038441941000100c001c0e000d841c00700e42100404949000140030f015083d500075040c043e0921040c89004c0c40b20341001c0e000d44040b03e00395840c10b006500c0d82c41e1255803c2c41d0b01d20001d900e50140030100d8941a50000c0e400b41103400aa840500242e0300c0e00e0b0307070100440204159400010200820040c0d1715541d00729821480d07043d400003411110a00016111445d200b80071610781c0c00201d4018092503890300040c0038401100c80000548029980383d042c440d100e10320003000e20078041950002440000107240151420856403480c142c0800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 731282607 1250 731281357 731281379
    0xf0308060f12030d0c090f0305070e0604090210031107061b080109020c0d050705100c0c06200d02070606050a06021b0402070309050d080f040b0a030e151b090406 71
    0x100c459019410405400c0101d0400d4000c401c01024800007542c01c168240d40c080004c4d1032030384c25000401c800100e002c01c96504a11025004611030002001802d1400c01c44040c1114001c040901c15898207900d03c0258031405500310324035090b4500020b041185910390348181c061000007030603440c40c00c85412004911608410071002e480d0303d43c00c00c960380e50f02d1200240c0c4903940ca0245260082222440b800340110003500400b440351040c0e45d59407190504003812544d00702036400009244034500014007001d032241505130000d0580c090b0140d92100e4510115214003c03990018560000f09a401c1c84030b5940034202900380100f801d115995250002175849101402c200c0715802421242c4025150901c215600306900d0746078111094036090400070860080402610405000c000040c200e060034001070010303103000d81841d0b4482c460328200404a961901c9c0e004801d50080950200340c1010662080e80642c0343c6445403240008040064180e01075240c115400070305010010500302510 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 731283857 1250 731282607 731282611
    0x10f270608010810050702190206210105280b09220b010314010e06060304031407050319170610200109030f080f0103201906020105010504020f030c0d090f0308 70
    0x10100c0305102e010301d040d00e00311131702603c03103801507400019904030009500c0c81ca0100ba60008222500348105c6016510562904819070381c000000c0400500035440c1c4007540e480703c8401c0c905907130510485800310240d504a907008135998002c02141d07600c2942d8882020001001e0101e04400c00070200707850b520042d00c07807044514086420803040c9240740c1c40c10480c0714103c48003035520b161942c840344284283c41c0c3c4060b1041d4100400d08943c07103000704a00004250161107040215501d405415035003408140c50441e203010008a40040c003610025001401e4109800310b0f40c0c021200c024510944001010306540b031400d017018404407c041006600c42a04d00303000b40ca90340b003a103400010490718040111202c001010701c0000501c081012040410300c040f085090f00e4030310013101c600184002188003000a40190501002c1c80303810782c28017900c2e0040c41d080d5400e40c00c0c601030791500d58850000400c1d4800c1203c01103810070340c0d0811034120741c400795000000154450b1050400814030001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 731285107 1250 731283857 731283869
    0x602040909151815020304080c0604080a120b0f130e120c120903031b0a0807080304060e0c0f0909070f080a17030f04061a120c03011a010f27060801 65
    0x90403c00040690343c00043e403015560101c0c1c0c001399041c013124043e000790006041995960018040c00c611302c0000c012050040e13009400d0162a0045500000c0100180038140c10209041450203030460701d27042a10b11040030103c5d096451300100000b60001464681004007c521070030103105084007810006040e421684000e4861020300c000291120b13101d0550116090360003003000380c40084041c0b203c14008803012082c2d0707458100c50340382c0006940050360706480d0200000b050000b000810f119070300440340c2a501400c003400b0840002040c0316010480d50f0b02074904840000e80740031091102c140541414105007000e652644070340c654506142a04503030321903c880d60608003087e4501501d1081104400710100355032a545c42c030000c2c040046075490b0064128040505171740d904800e8043d8141000000c20522029200b00740c2500c0ca200707200504c01d07500d90b00c20031040c3da01041e424052082d80c01c1402c0c4c0f00c1104d04a81002625802d000c500e0407100b003101141542c0d10004180c120740c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 731286357 1250 731285107 731285111
    0x2160b040615090b01110f0705060c0a06090b060907020c01050307050f220518150f1201050712140609010b13090f021201140d060b0103180b04051213050904060204090915 75
    0xd000040b5a036101c2010460025561084108005924003600101080d03603032f0405490900c84169650815500c60f20401c0781d007294484c08000391410110b102c1948904603200824400041c180060720700e03c8040e1814081200014110081400c084212811100d0140b0b040020401c40444c032511030049010780c038402c41c0d2092986078461000d60441d805003000d2090b1101c0c0b00c2d0700004002001401c2180b4079080925040080c03903404003885020300ca5010f81e00c030f020070311441d905644201c80c2c103240c0102c0200d1000d024800180c032410402e6055600040f03d0580d00c90440b40c40d182000025489030200c94140034100100030840e4000d040d00b406218103006007643c03103081392145490801c01c0075400c1201c05103184085101500031225020040c100020080c44540c20030410840d601c0e41503411700c07902014803040100402c030300704030072540261785400e0040301c0c000c09090603072900c85d6a2050304803101040038022320790304032002090042400c21003030701c1600d41600c80c00c5c0039000085a540c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 731287607 1250 731286357 731286377
    0x15040b09070b031545060301180f0201090e070c03031a01020a0f0204021e070c08060c0d05061f082502070b030c0403060e1f02160b040615090b01 64
    0x5400030240d90090700300c10180c640f4100c0400034443c9034400030300800e9020400030b010000f0b2003003c4803001e20000300118500c521178480c1081d12020030018000e1406689084029804032808000781c03140c0ca58081c0a80850010600040700c81c0711a0343c100341014001a400d20140903080984c1d4005d0522a0710148803007501d41c1d003800000384503280c000740540c0010792200e0000c4c4401410a110301c0c13004100501b8040310000340641452802109003a0344000a400c40c01e210f402c1500000812b03480d070080c001450564151178481c083c2011700c403500b03510341d030100342c00d03aa41d100d00082c11400740651841c040c0746000002d01c40001070303030095a1440c03049c1200348401d0b44c4c5100c80e800869140c004111040c50980c0f9900c50381d00c001d04000e81c11000703020100c00920940150010f0702118801400e880302c0c0c0100d200030980c0c5151600c50790301e10400074102d5a02c3c0e82c4d9640286680c00500010f01640d4500344103010340a0700340c0668904603840c80c04110110766601203840b6450a90300d03003040b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 731288857 1250 731287607 731287619
    0xf0b011212030507050f1b010c05120f0105010e2209080409140702071e0305070801020301061704050c0904020d0203010e1c02120d050709090905010c1413150215040b0907 75
    0x50707030b0603200d40c00040d104001005071b644403a0010f0150654240070300400c1028016140d01710b6440604410000b6000103000641e10706480d40e841d0000780c8549007c689514000001c1c140d10840584540641485490104d0a00171030f007841c6585ea8641c44240b240d60401d18086d400c59226026513005036203048500c00303058060029440c8201c0311500140240360500401d6042d0780e40080500e550340e40078200c084000351040c072050004020b410300158030395043c0b010140140d910a02d40304083c8899404000219000050f505104d0030155801c014549a50000c100705003120031740603401d5800c020744450a00030018a0b01451000c40b001c108005041250803a00c40c602c90080707201c02d14051008201d40c1c07145500013500201541001c0b08100e41c0c80d0841001c1d0360788528151000d0755622034089070580c11640d203040d081c0b1164280d80c5001c0e800026001490410302401072420140c00d00d88158500801c1104200a010038625901385040d26102802641c11986030740c540c000c6040025107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 731290107 1250 731288857 731288861
    0x60e0c09150c1e060106091a040915210302100e1005060a1802030615040e0712020f04090e1002130e07020109140a12020303060d0f0f0b01121203 64
    0x251a00c000c000001484001c114000c06400c440720036020380c0200003900ca042c0203982000409480010040d06456152441c040c0c0404429407010401c80700c10400e44402c140380608440c10780d15100c10004d950750301c000741d1464490f00e5800081d825240407d044e00007104241d414100240f0980c211100d00c1c240d42e40003070944118140301601b5901030601d1120039440c58000c00d610800140c00709245961314001414403c9042c1c500000302030b40002400024208410545d42070a00012814039043c5003550410445034002c0c8080100021504000b01c1d24590fa012201c4143c12000420303215601c805600004102017107041d00c10f4450103070759420741e403504d000f55484010030000d0810303000d280880010084000030040e0f01155681c444030000100346610f848a10100c0d1001070180902d180360210f010030380f000c0c03c1c400b95842801000280e556106500c500c04c0d50100c1f0b6446c40600502d802c51031120307240e100030140c241c06800844c1da20b01c03401401c201705000720f02c6482a10340c68407007a02 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 731291357 1250 731290107 731290117
    0x607030e030c24030604020c06040c0305011416030507021c030e010b090105061207031b032301150318050613020a120b0604050c09030f0c03070806010e13030c0510060e0c 75
    0x36a500440780e503075180310f8000e0003440c1d00070b1020b400585001112007196041140480d4112006c11310303140140140507003482050310801c41a12107120508041100b001c650b04141a160304054880c800509100e10900840300d400103034031125405411000400350241c001c81b0403034002580780007103c0c0c40768608002458101d41d40039008610b000e45401462030040e030002c00540030706d5203900d10508075200c0d49410b15501d00395a13038002500101c1d1200d410070840071401c110391000f915001880b24a401c00c940c00714a80d06405c00050441d41b941e82b2200c1d1118018010700540036a80801c0380c0040002d01554030140708a814960303040d213030b03403100503c000360100203045100c0a000144550a00e136000f19000340b2843e500a041c0a42240041c0ca012079900207481e1503002803203076081300d040812035007015040d90009800f6540c100180d0340c2a80e40300902c0e000021a201c00748806141c002c1051204041c2c0100c1550b903140049000c1101400d03280c450858914500400691170704040d0090314 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 731292607 1250 731291357 731291389
    0xc010503190b0118120201120203070e01080907030b04050d02061b03191410051009030201020c15071b06090506070506070c0204060503030705010b0a0503120703120b0607030e030c 79
    0x122103a0780303100820000c0141880711414450020402c0400803480140c4100825111034086580d50903480010301d0920b801c0c481b00344990052040c416040c0d000400c004005000b881c0c001c100f41c0d140c00459203040c085610181181e060303141480107107c4c011030340b1100500107400319405500c1e00d0000380b06102d4042c164a401c0b880070b20100307000010030802c222282000d044041000a00740d580c0e0300c44014155907a209020100f82c0c03c004d9030510603140c00c0d4040b01d500b4004c049900d0750700040d4581001d40700b80c034480d001712031a000c20140c0d22010fa60b0f18a400010740c47c0016000040100ca031502070003603d0103d0214000010503217813200466015940c0100074081548960340192102d4040e140101c0c2d1050301c40d58045842d8504101401816004000100d003400d21740080c414414110f4011078003d170000764103a0030b000e981c5400c4031015179040c03400d82d0000c0c0b507100d4400014654144a0703540801c0010f000d00505a005900303003684c0c1022400c0c0c42e0f141401d0340400c1075100c2240000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 731293857 1250 731292607 731292631
    0xf01030305130f0e0a1a0d15091a0106090b0712030e0a050f0c011b11060a0302041a070501230a0b0d15021209030315120f0d020f0c010503 61
    0x1400020701c141e01030070074803110894803070a0a480e2100a0706003c403a8000108400300c490401c18164100e018600c0c00c1291104000010900840410742142d605100071303040000140900c0f5101c2c040d940500c14441d08050500824220542c010800c10000c0c0f003458006044881302081000c40c04048030880e80e4400000c0240d60000c5405070090b0078002c883c200140221444030000c01c3c424030030703200901c0401000d004458240c07000900300843d00d0700c1da04c00e444280415400083d0010700c80350458801190000e07145d01c0c00d04002c5010344203c0d004500d44072001300c0c040300302c0e411031300240021502c036000902440401610106000c06100440301a0740c24032000704425117070302ea0001801c010040c10880d52415241c48a2800c0d10503003a907840100e034001407880e803c103050364400d900500c41d500698503500342070000501128004401030301c1442030f03c80ea0030300e20104110b048900301550056403250000030001035212404044000502e02030540990040d62040084911407804500c80e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 731294964 1107 731293857 731293859
    0xf03091008060f131b141206120d0807270e0a0e0303011e21060203060402161407080c0901121a040609020316030312050c0f0705160506030f01 63
    0x140c444c1049070030b034045081098072a01f2515035110b0400e501c801529140c00088010034080c0c2c00c4000d074030038800070408080e00403412602c00c09036074450080c60f008078038007500007550f082074900c0d071441068004e000c000768441045030001c900c40c0001071400b0b01c0c03501c1140b46902c2070704801c180031b400b4100703900306403504407000018003040c03041c80900342c3d004650844801c142c03220080c55103030080005481034440c4d82c191001d4100103907034104510218141001d041600303000b60280c0d4041c01102252081000071602003000e000703042202c0580ca00080c00001c4038642d0f80882e0440c0e0324100780181420350845c1ca600460240360000b4070f22000d031040615200c2c0c0382c00c29000805e0b0900b000c0010941010762080c50401d01c0001140c15a1100c68001807031041080320840c0000101c0d0030418404006542d4866180b07000782c04508940b18000c10445000440d0b80306400601c80700 = true := by decide +kernel

theorem cover : BRFrame.Cov 731115107 731294964 := by
  have h0 := BRFrame.cov_init 731115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 731115107 ≤ n) (h2 : n < 731294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
