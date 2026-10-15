-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4136
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:40:31.274162+00:00
-- url     : https://prove2.me/submissions/5119df83-391b-4ca0-9cdb-fba95beb79c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 743705035 ≤ n < 743884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 743706285 1250 743705035 743705047
    0xc0a0e010509011710030506070c03021c03180f0b0a02040303090909061508061902030606090d02121b0307050f03030412150e0d0e01050a0917120a0c111e0105 70
    0x211031301c0c140c280c000e0449048003442c00c1001c039042e8802c410740411100e0707000b04400074180700c0c414001c82400f0b81d0103900a00000704199001030788c2d0540103c90004064407448500b030188000710b940078442e48920b0750040c644041c1c2c1080403040038007400380340d00319004000800c0802c3d4052442007c3e5005030800048030205031500c031005243c40448130031001c4000ba070005010401150b8a80708000f1804c1c00307810110104905006c81c44210b640c0e0703a001c50f042c840001d0605080e10881960f92018084e41c0300b40c1d0031824001d207030078260141500d83c1e032801e5801c010b02c0d05061059000414080c0c2d0486402180703000000d131280a075009000e450105900d01c0e00500150b40018440461248070400c9004240a5955203a151040c540004100c860180d000036520441c2150743d21089a61084912403c0c800d443c1e650310b40c800b6a81041d4480d942e4101e031501c150500a20714071003103031a005014425882d110807008900c40e14103200705401000c84d00050040f0701524a8102c1c00d2801c641e843e1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 743707535 1250 743706285 743706287
    0xf0d0e0d0b0c04081204060f020706120203331e10050d11070602040e060a0b0a0c030c05010e070e180309041e0f0506010e1e0114070b0702150c0a0e01050901 69
    0x30042d540413003024840c0d0507121754801c025100400568a0b01e0b690130721299400384003a41d84400078403402c80018442c000395581c419265000d190000d0400b415a26000d4180c1c2c01d80610b0109098041c107002c0f01c0c00c00e045d2a51030311309840d0003c011084d20100b0817201410014480c0941140080c05015001035481c940481940c42001f0034040c402d03141e0380751007407800d10000a400030f0180800034100380b008030b640391510003500c20448000082d000c1c501046106c04455a0010740411010300c803922048000156080c01540864401c0200610b0130318074106600050748800b6013501c2d00a41000d0b0009030751913010085604d405000c1d00c0c082040500100f0740601c0740301245000103c0c6260604115038140c603508180e0141000741c0c1c613131110034008410440092a100c1c030100101d54500e00311600c950207200050b01c2004480d64450030b001243e11042d00981b03086400c440107800000080810711242008190040c3c1c411354420b041495140c000b41884280c0710906041c0080864010816 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 743708785 1250 743707535 743707537
    0x105030403022103010e06040516110703080705010f11030403020705040c0507080325030e031204020d020904030306030501110304050d121b20011404030305060418050f0d0e0d0b0c 79
    0x1500701a03884400e040507208401107400a02603206c0314032082c4041961071409004082c02403000b841003004040050505665140c19000364103d1805100c00000218030f00001411445000d40d0010502e1461440c021084a04070040390603496418818800800d41c000360030800e17110165030015045008600c00c1d100c0d405803400040910000101300302200b506a504e03100b101e485529905c603181107003401a01a01d2030501100c25a41c000c0c0001041c01c108202e05941050000d464142009003d4011903402101110f0031f0300821f45400342007040081c2403041c078081c0140c950099042d400c1c50341d01c2036103c46001840108014940304625110307080ca07880000c1c200a03241006841c0c0c0c2c201140541444068200054201d00c2c8003110600c510040c06680025085410001120f030b441c0e82d4260010305001c1d1099420070354911902d1145501540c6002041c0d0007600100151a100d03268540b50584980b01101000062000b608083d00c50800d409546a4400f600281c0369407044a01420303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 743710035 1250 743708785 743708803
    0x140a0617040c12050c010327230a0803010320060a1101141e0a090804210c1428120302190f0b010602030c0a02040b0d02300c0906010503040302 63
    0xe9000c401d2003d01008000608210038510a88040c050351008204040c028100c480c40d41c3c0071405085031013000201d82c804814515000700041c1030a004510410034038007181d406003210201c80c004018003d11100745904103410101112862114402c0808507410380200710740041480340b81502c00f1075020083d00411050100c807a140a10f900d0b206210040d920000205c0122060f0514041884c0c103020380655620240c01029152509180a42c074140e400440045864010489200300000440415100000b0543c11503003900104c40041045910701c044681907601d4200d000c90a02c3d0354203c604c0000803285020b0344051602c0c03050034141d00700001c8104140504404841103002c2000c0c485950348110b02400b03003110f8a80c0c0f64001a03950b4400e072401040070b5480800a00c0051419400055082c100035101056507080d541c00710b8803940e0301c6001c8518440942c894400740c10204c6a00c0e050500c145001440d42c22110340114206200107000300d03042180c000300080505000b0001440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 743711285 1250 743710035 743710049
    0x1090308070f140106050f030102070c1509030b07050901111603080a090b070b0417041212030212090105060103110f0301030602031518270606040905070f0906140a0617040c 76
    0x1043c1d82140b14228001c1001d4010144a00c03095a101001030905100740ca8400340d000c100389005904140b69414402034094013001000510000400010001918140524160344440b034603032000f08009030007104044149022603021141e01d080324202d0407000c40440f604186125603d800c01d9204640010654001152501000500c4c3e400c001c184038900340701c0e0340209034442d8003d42d44100e400030391040348901c1c071051100307021707010110f10750402103196014a8200185000782020800e02100383c111401c0d2250f035911804c01c19256094043c40001e1782070340d0091403400c981c102e50030140780010300015089580c00300c0000d00b4520005540c014201000300208014000c4400e4541201c40484d90002d83e03030700c00740120401c02c0880b1544124402000c020b8000c940da54814040203010400c400d132a20301c02c64400241125803052150080c00b54408007003002170405d0508204942a1560785000e807425602c01c108066000322140f0041c644a990349140d03846d03e08200e101c85d00541c018003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 743712535 1250 743711285 743711303
    0x1903020f07080702151c0f090b0f041104060b0d1e140a0e070312030902010e0a17120325020c03100b0f0108060f060928030308011401090308070f 64
    0x40c00340b01100307001d825401c0c0b08540319141814a410000002c1c000c4d0102c410107002005010584400310741c0044080c0729002d80005400c1405484121003944150340700d2040300012020300060020010758000356020542c2c092100318038192503034042c0d00c2550440b800d43c0707030f5907010383c1c044c000e0610584095070100d402c203106038681a42020f20506040c1c469690307040c80d000c20f2521640c0f022503458112500040c1102d9500c940d00c0c010f5000d042c2410040381000321000fa940825a40c04c41c11202400c0c0c8650754400c81080c50507030b50701e041c0f401480d0542d031920900801182100c02103118039070b000390244000401c01c1c41c00301070740341c451400019503140c05980c44a009410b025440700c2c0e84940304444819960b02e404005480c2c942d415200c15030000c0e6041c440003e0390401c14014240520040e01d107140e00c46140c464a40701100c00100e40c6036860900e14200145a404a4807034058040c200c203500c000542c03500003820705681848000e041010201d00081449400d01072602801d400510780 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 743713785 1250 743712535 743712547
    0x705030a1a0901180201030f02160503040501030b0301090b0126030408010510091a01200604050c0f090c03011a0909070324031e0c05130c030b060f1903020f 69
    0x910044805254040d01d0444040c0040d84a14050250554942520121001c6181c0c00d40044000d00032480305021119002c0108803880b41418485010440c0108091500c4504000004040d1044009030711b12a03814110003a01051904040301d0440e00703d81a0410014182d20700c0000451102603204d070207001c0810001030070702040d0000d912510070506600305454540c2103560840710381004000c0c0c450843c41110207994003600d82c4240c041d04c0142404103002d80807213010310f4640c041700d048909400c01c6000c40b4441c00c2403240c0020b80e000c1101c2e6581c141c03a0900100c0381d140814498001d00c034201403081c0302180203040c02c45400c0040a071010075140b0708403801801615000d4a00f06800e1441000c5421169040013454107030f0f81d0000c51f050400b2090410860142c0c0320300300642d03072010050000245940d4642610b01f40c2c145424000c9919088450042c084400000c603141c05940c1c00c00c000da689140140403034040c5020001820309500c94140c00701c0090041e03506103015440300240d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 743715035 1250 743713785 743713793
    0x61b1206060c0a0f0c030c060504081c20100f0509030316030204050a1e171b040b09010e0a1b0e010f0e030601090603053304110a0902070212060c0415020705030a 71
    0x1503402902c1c00780f5452880c523a51044c04680301d100d14803a00c40035810103040126046284107002c25001031038503140200b01c0b80501d00e12048401c0e100c045d482039002100f000801a540e000300440c14408030020450f030702d0002c22907512444003d01d02d880c1300317051107941904275002e64140c40251030090a4002040e03110b150b4004140c0c01d06180104510028100040966040d444424852601006414040d0880c030189010303120381c0306840d503c103440d00c6120001c0d4843d0040d0034000d11140100000b1418a08d0310700040f2030703809a2205041e03a4100c540c2030019007040103507103001c0d400e1a1032194100903050880d03203c410418000d9041c0500c81c0001000710b501e410850aa038026401c3d42c011508610030343c50628402860701c030301c000d0005500111203c01443c0f47d980301d40141c214844103a000720001d041507010307400c41c4203019030109440f030660506e044e101e210301c00064000c01b16405c1c201095001d502032813091108a172110403100c04100c0c400c0c450000280405011500440c1203490 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 743716285 1250 743715035 743715053
    0x191a0a0314040f021801230111030c010501240e0904050a0b040318090501150f14030a020d050f04020904060f0e160e0c03041a060607050f061b1206060c0a0f 69
    0x1100341d1288481488200c9501a19100c00d4100e40a03941f082d4207041e020844c0650b040140081e880c1844048190f21408503024401071181c1e11000000155070b6040030b02240005610510002c20790698503040140e45402c89088680f400301110168a00d60361031500514101005600501406048007400105500011610440c01a40c2149107540351180e03400740440e102441044000080c10700d507070521500541c480c0c030200b4140d28110303d41c4000410001d80780d50060303400c003040030350000c1c203040c0400b500d1203050303000034000d48003102904054000640c1302c1c4001d070002e0007090382d8981003048404d403540a4096410075205450101a1041400f40c1c1e4000d0342c0315040015a210b0006081c4900403c01c4030302c69640900300030340a0400000300845490001e1800c0d801600810030700340452400c00c0b440351800200001071549141420641122100c0e21000e5000224144402e2404000701040c00381d003c00159042070f1150340c100c500c01e1030140c100d10b0160440100c00ca82d1014062400c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 743717535 1250 743716285 743716313
    0x1f020109020405060d030518010203090a0e01180b03030d0e0c0a031506170a14070b0c031c0b130509010b090c0301030c121101110f01020a0905191a0a031404 69
    0x10b904005551300d04003804501c0c4000900240081c0d020080d50b030b055209861440b09988043c811203081001c400c2c041341909449800114148481030010400504038035605804040c2a55013442540352400100c0d0b5a4042d800480075519210711051030711160400c65501c10580040035030042c01e54a08003d020382c2c90481d4810581e034200034007c00c00000c040805c1020040d048002c4c6031040b01c0c1c1c2c41d01040110b4011106201d40030f81c100015001c41800090520020810080c0d07564074003820094101c80890462130070001e0a0411b445200d41e00d80414007035500a140d4003240c1569855241350060075400c41c207a601140d0300c6c0070b06c90903100c1c4901442c16241b080c2215154030b40c0ba01291501d000b0401c00080807800c07034901d50480c82d4482e240030340c0c140349880106d03581005040038031426604400e01c010000f4031030903000c000302d103072841928043c211058038030540135062141d58003070701505185451154600060100b2241c8c400d601801d201545442d098910381818581034002e86069 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 743718785 1250 743717535 743717539
    0xa06150602011103060607260a1220040b0a050903060412110604020d06020a12090b0907050a18051801061e0e061806010521010617010e01050f1f02010902 68
    0x4441c688407190f40204032030007450014840e0303003401c0c51759980c0e00c4402502d00c08958051840820107030484001c0000d4480c1400c42d4807803c00c1011020001403c0342c0da2041c030030b10010135241d03048407071440b40421200ce540da01c09002e17a848015450940d42481081d2115815108035070402041c007034103e0381e5140001681d544c1400300e00313940450690f41d1342d041d02c01031752124181301c0300d90000c0e020768001e11040d01e25051211034030400e0321075002120186103041d12082c0d01042000400c4905001c4c200c0070340001c0307a109445c281404503410210340505c1c0310300d02031a80c0b10040380e180440000d81070045010b040003807201035107d02602c0e02c80540280510a2501c62901c04900301d0041c08802c0e01c40d1074050005205612041d01150041c8801350110707040c410b04100089103c4039203202c0090300100c02d440c180f03a651414800801c4805051042400e00e81d4050051102041c46c000ca541100c604881000510328201c00203429000c00b205000740c6c1604050302103102c40e4064108903003190003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 743720035 1250 743718785 743718791
    0xc0305150702120427050f1f122006072406380705060906010803090d110f18070f02030c0d1209020603180c0d030f0e01020a0615060201 60
    0x84600590340d5015645010a803403000b88400e02951a22111402e04454a110b82108203143e0001005c11680290b03210400e01d4156020040503c0c01003654079030401c80d005100302074502d410410080050034650007441040d4401d60b2a03403080c0c202013401c605030f80c0203080755030700c2c03c5a2408898150700c180c014008400070581070300b82d01d8001c0c41610121140104500f0b100302a40403244400d01c501a1070118080765581d000c10440c0d207100c05085080d11400052501d030420300300381864418140d1051406900c10880c400c000c1e19441548001594000c201c1048c0640c408001103c040c210700c0c0c40c0c0d070001f2641c50150030801c9000391050254017542c55280c1842c492000481c4c8900c00e0700d065101d554060038a42c91a14411580d900ca08072412100085484041c2c1c00200f032580700380d442547c015041e0a40207241c100074040840d0002c002c9036210311041e0269005006100c00200600501075459114942c99009210510301c2591010040140b0f0320080c11103614900c3c03500a2100540c030b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 743721285 1250 743720035 743720041
    0x8040b0304211b03090b1305010210230403020309100e01080601080105060307140d0c02032a0a12020a060f051905240d08040602060a0f0207020d02010810030c030515 73
    0x550602124415507903070380c1e4012001c2e850030065000c00f070307411011010440c0e045030008404c0c0685c0080c00ca843c0c02e918100c1c94043c5040002460a07041441c0c101c001407404801503210240403070006401c8c0034125883d205070741e80307090607405c1d4080c6110b2207400c01d91208508007201c0d8010b0518070b03001026243c040030786e103e100045855100034081d050300058104003140c4220b020354810b41d1101c49100400d8500700c183d900d01e4050341c9403000e850015900c00700d0030f85044e40e101905120340180741c004005146d00c00380c50686c1e865403100400740c910451a41e00314034a5100340304240006800c44000c2c0810344000400c10010318049510318600701804520b100145680d00980780900303002d120368107182d0743c2c4403003d031400003042d0461540101100d8020300080c041001400040c00c00c0d8014004624014030010161001c40300300f110541d104100150051703940d4550b03a40401c0c0c081c40c0c0001c1e95643e1440768880d11409400240a41e901c0d14070000810400141851000c4618210400c580d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 743722535 1250 743721285 743721323
    0xc16030908060f040c060809102007060516050f04180906021305010f180938090a1112060109050d080316020a030c0f05101107020f06190e0d08040b0304 67
    0x3400235141c8001e16044100700c5910303008180c0180100d4900c802e25081060094000724400d58040c203000c850444c0c445040180000d403480c1d80d49a20242800c10f00d140012003907080c0c0e024403842c0281c80348462000000c2c20071000d05d9120b00140d9900400071981d41c0c085109100090610f48121030009019080d0740301c0080c407454100d1082410b15842400d241d0408500002130405100b032880d545050303050b50402920b094030445000c400c210b003400300991030b010a01038665002000202150b00f4103a0707049144800b041101c80c4e91b10b40440f902c515850b40801241c1c1320060741d2003140d01440d8464144c1c103100c0c50740015802400003c04503151081144820b0340c58400c005005008211804020000703c0c050b081c1c00c0003240d10403002d8400850004940740c04449000c10103016071100030400e1021410002c2d40000c142000f110498200800140500c129880c400c2c0d468003004031080c1d5806064540c40c909084c20b540c466540d03511940c540c5804261a0401c031400d8501080c4044501d100d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 743723785 1250 743722535 743722547
    0x90c03090210141c09020d0c080d050406170a09080a0509030124030236060102150f0115090803040e041509030507140c03010504080a030609050c16030908060f040c06 73
    0x1c80f0040040e82000c031510894140c050b0402c0c0604075140d1110141d10040c0d80d5500701e00c00451040440340040750814890510301304100704404180142004203000481d00080325402c840500b008400113503440101c40005030040050042c034601c40403954a005e603030042e024150000c0c06400801104040c844e62071440698661403000000c1401d10078030250511000c4001030542032070b010400d480004183c5512100000034080201188000348486c960b4107008001605d15175606d8021241002941c407e103c1c42e0620409035903229145414050314012b6064000030003600e816a52600d0380c601654007041e000303c0b0101c13407100000440107044506071061140803034165454500380303107003a900c5880f50154503001c41c0076031080e1b06150010b9602405141e1040303114a0481d070f12010050006000d985041d0444100750b400e16080003070500741c6505a0b820303a24106249002d018240c20181c0b034628850300264024040e00042244402c4581c00c2c0c80c1c0a688200081c0e5003180d981d407011568 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 743725035 1250 743723785 743723807
    0x1a010f092409020a05120a0225021e030a02040f14010b040303050301030807032c0906010905031f140a0507120606230c032101050d02030607050d06090c03090210 71
    0x40741c41da65034144a42103140d03000d048000900d04105240030401244184900401c40740b01f00000c0c0c00080c81d5050038900840540416607012945d0012030311580003420404110781c0000c0d00040140b940c5050340e4040149021090b000b81041180c03840f00350080015022000600c0391580c10780000080781ca0b542c104480849408d5510303141903900b55070b0b420801d640021016420407490702d010411744901c02c00100c9500c0c0c0d10005101c02400a01c003403000c2d480c2c00500c518148040480c0070020f07501d0120307540840294581820140604103076440c0001c123045101c0001403400401085020596548018016249a104d220403005540b490b501502c4160190400149018205090030010021a1000d0041c405006400c0031710f0138401524603040141328a0149102c0d0105680401c110840580901026a0b5049070408550040f0750f40342c0001d040e07842007050026109044001d90360000004c0d0612150a210b55025100024003030450004185c1c1f052246102c01d90029000c0c82c18000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 743726285 1250 743725035 743725091
    0x1e140609160527040e060417040f14040e0f0a0b0c03011d04060e03030901200a050304150209030d09060305070206070912030e0a0603020403140f15041a010f09 70
    0x32034030000c48041011100303d0740c1000340007880040c80c80250740c1d55000b81d843c9000800003c202918141c20b05c00003450b008420b84800300340400c802e109801849402109540c124030303030b00101d0b800100101d8000c0505640c0055280204002e070710840501040b0000c0030340c013a401126403911054421803641c8020b100f8001d0041440e6504040b15100040305035010380200d9000441c070f807072400458115441128000c5c0e580c3d54895800c2da0203602c82d0000c840b8007841c3d1a5085c1003005c06e180107040307440042d20240030714600141103040d0070140c0c0c048448041001d07040d030310340f0b00450002406d100310300c0c014074000c03070f050130000b40c01d56100041d214419003081d44d03800c00d0546418030001208a0060781901041040c3d01c508510380c42d41a0800000d160a0340d0040e6281d16606100c000441900303485035030758200f03103440b1450800c002911a0056601c100403c2e040e1201e150030084c0c90141100100c1071400c0000009a600f940d201c84070865074964024465200c20010b10b01c501d0745a011030382 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 743727535 1250 743726285 743726287
    0xa0320190f2a030c0501110421020a290c010b0108090307051e0f060c0d060611100b0a03050d02060907151e090f1401030b010503070e041e1406091605 66
    0x25060b032804035907003055940641480c0c80c03003207019240ca07429500403812880b0740d40d0b0b001404010112181d421022509490841c0034030300102540000c2070000b10344500b0030254425003509480791001421840070510f00310406640c2c3d1000180a0b01070804207841e01e0101e1214000624200303400700480320a00d6202c006001500d07284a8880d000307401e170000e1320b00544074818464911510411030140610b5241401c2511111110f4002050322801d401200800801c1a03894070040000211418240c0c1942e0000c240000c03c1c002003218403159500150041c0300c3d4040302c500250300802e03c0c60158000b60143c500060b01c0d080e541e0842d0319014104400954040c0c1850f003008020800031406e620f01380342c0b08912030341d0340c107003400041030580160340c23151400d0700314003801c1da014454143c60031001e00b440d03410340ca4071003c06060383c540403056901450304c41e0f030000c3d005280c50544038200005000100440c405404903000c510b10100c1e2850b00a03103101e0301145034502040305032501c0b001079035681c0d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 743728785 1250 743727535 743727587
    0xc010912140c06040323030403030206160302120403030b1302160308060604050d05072907020d031205011814010b03062e1e030608030a0320190f 64
    0x981001052200042a00444950320b00d140d503001d00401c01140107000001595940c2c00c13007000c058402d104042020f80c8208030400000e0380200c0c0403a401a81074001307411112081000360044d126140414103080015800c1004150301503108485030b40c03056070003800145030b0b00546c108a100e01c0c4520100c2c4c10700482b031100024815113056510440181a07142007035555804913400c02201d2030116050b411102c02804580821002818509545030031014060b20403080380051b4403400700007a004814403001c2e601854069042c201484d9020101000a0740c0d540c001c01105049207522005503904007009400078204807011103060710504812945184ca0380c0c1c0401400003101e803c00d05a0013000074201110124a5241c0300d001411a00c441c40e140403000460001480c0007a41da10074189010418004208000306641400025050014444d4008008450351040705554001120300c001110b14003001d03c501400841c00240d210424014074000c810b440c401c1c1d2042206100d07400280c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 743730035 1250 743728785 743728793
    0x60907061e0c06052a1206060f07120306140306041e0203070b18280312020f100603170f0d020a09050303030a05090c150d050901110414030c010912 65
    0x11001541a0030201c00a00241e55000141c980c02c8505044008643c001c0a03c4a441130305d40c0c040240c802e40ca540e20b0080c0d44001010050409040203025130808a1030714140022032007140c03000303600129207400c0b5111101005010341014094512150940c0865088a05001a00601881d4070503003407280ba43c81100020f44c0400184401c0c0c0c0c1c507200c0c038400000d003446400c0091682c2c1c5038400b8030100001c915014000b160400380010003407182d4401750842e94100c6640130200340c03940b10103034401d11411018200d142207071a181c03496071400f81c4c0070903020703117800340d0302c0b4008491060a580010700c40f013101c070301194040e285000b51050b0040041005881071030340100003008a90410903c11074440010078a99042150001032640c3d96500780110f400f01002001d039122000c40e119030030250301c3c1c182e42505000792646202c4543e00e500100700050400e4010103100d54410b451f09407540c1c0d035142030007914031840038081d000303000d80c140d0b41c1000d5103c2c084039402d1300c1035041030164807012551 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 743731285 1250 743730035 743730077
    0x12070512030601140414090f0919030e0411040f0f0b0f0708070807140f0105070c030e120d0c03090603110702060a030603020901080a0314031608041a0f010806090706 73
    0x9140d04104990359144072880e00d20700a070000c0c20701c100c803400911401c10140f1024480182851168448100070001c9d00384000403c031003030390a07180380d5241808131880d0035513140041900290f40281411042980d443e0444080c00840303061404880c1d00d155039050188030020140210300224800b040391882508104d001404030070b209240303243c030b040d03a10749440100e0340212030200c030a040c40402030074140310300b003100c008203100000080110b41003400c0054042949180001d040c004c01ca01901d00039612210f0710511001940103035000036607101c1d0010103020240c3ca0890224402e2000441d4452207442603005400420002900c0d02c0e00e00e40801c0182c1e0010350a010130191a441c0120041c0c4890800368024082c4000034030b982c044601e005040d00d213104158285405013442080b201602c1012003d1031048103013043e07a09a00d603401c1c50118501102d001c400c880a02c9000d00410300c0320f8404003412504600f003900e8140d16080d034160b450b14990311a00000a0400c9410410010890 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 743732535 1250 743731285 743731291
    0x120e0c0904080712030608010e0609071e05090702010b0102240a110c0109060c0207140a140604150206010f0b03130303020310180504020103270605040629031207051203 74
    0x30ba05036040070300d150746103120b0001c074a020340300094071004104250311090140e50b42ca002c1c03050141c4040e18003540c890350744100a00c206806010100020111295441c6524002c3e00001c1c28001440c509a13202070f0180011410040c0140300d0b810795000c00c41c0c0722032409051400e010200f02555100c845503403014007040810341c000311008101d0051140e03002d2050020300380c407540e800300c2c00082c00d00001e41445aa81e2084c030150301401c2c81c1080c01e5a41240d070105590500b007466010400020200382c450040d41c0198200c0c4480501003100281c0001e0b005040302c002030303600c000c010b490f2544044540001e588a40c510303902110240c4c0000c0c003d1b00a1680b26142c100070300725850352043c92080742e0706140340c03d001ca544c2d6682030000350b581c140164a4403260070075900c10f0825000300103a1800a44007000361125566502150030080b154001070044120455501d42266289424070440f4011000d564401c3c40b4ae0550950b504a448060b14901900800500140b02c00c0d0400210958001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 743733785 1250 743732535 743732543
    0x10605030f0a06050d0f0b0106020d050306060c0f060c07063b160e0a0c110d030f02040314060708061207060e06070206030c04080c1507030522090c120e0c0904 70
    0x4020215407920b90781914a48603004200080303116081c7e00308514101c4040e0003aa0464202c04400c9030803030740180449402540913030362156a01c190719107413814000c0784e5060200f81e002311020b000c0305103034031070280c155980074a004000a1810002c00703006610300a002020071540c02c9a6a280309421000c010148002241584c00f10204440a01c1c103218107604810381d01e045078418440c0d00410b5124141526025060848034604030030100c82c1d45010095868041644400c04204041180d4051f50011030740071140e00303803a100400c04540c43d4602120400300055030140040c449103880209010b60a94079800307440c4c410b080034401c8a1241da01168150040e03000c011040050320340d01c00842c8201110404035440d503040c0805a800c0400c9170b140c040c03280100044c04159541c0c84011a040e260741400d00c00e84e605010b000b808100d6141010440c0125540c0340000f507004480e40044010071042c0d0b54101c008480c28400b0f80445000401060342070b0f104d49441e001c107040400303520340c0050003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 743735035 1250 743733785 743733791
    0x10213030b060d2405130812091501060c030e18010b0705122206050901050a031812080106180b0403320d0f031a0609060702120303180303010605030f0a 67
    0x1900c2d1078407118011400000c603e80b0740c6421104c181c41a2240a410544100d070310500580c240c1c99a06081c02018148140d03803481d03c2c0412420304003001680705e80c41c400001c40c01c0d29a921507025256180740300d426404604c241d18102c1c030302d1804c8001120709000f0001c07419150703400c010103102e20307130001c0c50201d8091150760185085501ca990242c02420031650b000e90513004001c240100083e05070384100e040c44001e001000851ba0030209a035410241d6180c00681307506000b0032518a1540c001c23000d0b03c1d104866800b02402c60344194024165289511040442c0c14440c0d04075011850f10b00c100349000c6d0082c002880010300c4c0041c02041741c03550708820a00101721000001064601000b03500c40742c0d1000d0510440b094016807490400d68150504001380c410f00e1a903845814145042e1a120740c400141000382551402c098812042c0c0140441c10040c0c00c042d001956a4415140115001e4030942c2918084100108484c1a1030b0345a4640341140c50325101002c0d003c00103090808000e071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 743736285 1250 743735035 743735059
    0x601021020031014090702030a0f09030219150203040506040512011e06030201090e090d080603120a0306081006150302030a0603140303040b06040509122d0a02010e010213030b06 78
    0x9030801443c02940700c075054603031043c500200040080e100c8801140660f0700c00f400c020180b500481510230102c0c20f4180040c0100c0c14100440d041803003500700a520500c00e1340510034141e14600351009460348983c00e4030410507031140a990b40c2c05140304290f07106400f000240040e080201140d5442c0100c03000226030720700407402d01c5200100945400c0d48140d40c4500070015523a01c042c044c401440705041c004198103111f001142c0700d0014030408010b2040e40400300303004d501d0800404081100803d100ca49407a140301e00200a8010351042c94060b20070200f0500303542030340340b04050031140c84c501c114085080000d42600039403c010900d0703824640d18480080402c1406804030320382e1401e030010311b50305c0c03500e450320352240400500307140c0c01189030004024503400b00003001c4801049101805481e0034192040300d4040c99000d29417210f0750070500c4620901907040025282032200f64009101d0382513004e400500301c1c0030700e4204a211191910080011868400d280b5401c0389000c0c01f102d14500d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 743737535 1250 743736285 743736341
    0x403050c0f0a140607060e1912210c0c0b0c120c0a081f0f0e2205070504090f02190807080f0303060108040201120c0906030f020f04150507050f1608010506010210 71
    0x6234440c8a182e103803a103204c0d2010090300344104400709407203050030401c60051060412595401520b2003100315626400f000c0001d000311030903840b00f50711440811182c60f00d10b40950b41364211803942008181c2442c0402c0c00e1280f10400e45400d0382c4699603604030341d60340c4400080c00030140700c1058103011040c0d4011504440441d89040988540c1c404900316060900c503051545522100400100790a03400c0d50780041c4020940404442007194040b9081060f402d000036a8000c0100081d405002d8200321003115003500011403c0b20b4800c025124aa55140f10540d210402940070032101d400401c00590304e5801900402d81060061400c0c22884102540f004100e07050303142180e01142920300c00700483c0354140140c0c0946c052240c000d508141403070032214076601850241c0c0410b10500300018070703000d106109507150260810300320380c90006241c44003034460700800ca0600f9461146100810141c4050050500811701a4010305214101240c41d100070220684800510607c03003456012036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 743738785 1250 743737535 743737543
    0x3151d07120308090a020d1403090a030b06010e10081f0e091c0c0b01031112070b03091902100c0309090c05030a0c03060f0b0304020d02060403050c0f0a140607060e 72
    0x1501c03040c030040c5460105401c02828030032004103540e074958080b1054000580740d00382c10810040e480b5521480f44c00c12808000d0442c091015115002140c000002041c4070385a98442d001b28001e0300e52400f041c00d007405001203820f1700c92640001c60074020100d1604d01401c84001c00c4210038111205d0388030349802502440003000d0710101c0c03841d84a41340601d840d0600550b112100c0e2401c1c140000b003c24156602e029a0380c0501c0050604500c00d40c0c55807440c1c56000e40c1680c0650944152020141c441e042401d99401c10349542095200d076200868913001610110264290020208001081c05100481d51202809030440800418410004502c0042d00414052098945561341c03a4684201944100c4046000c42000c00d8100081000743c1d040070300c010401d641400320182d40c3c035600c50020440720b103500c04009410000005001041c0f11001c00d0408401c041100d211208280000070004205454090910500080b28140d8881c0c50482c00a01059105032404a40215401c54a6044c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 743740035 1250 743738785 743738789
    0x8031801092405090c030d08090106050d0b1e0c0301120510020a170c070c050d060e15060405060d0c0504020d0b1e0108220305090121020c07050a03151d07 68
    0x4040c0406280d034048440c5005113548168400f000307003e02c50a02000135610000c4c6120b503014001040301249e000381003904504040c0c0700c040c2000100c0112031803c44001d40e0f00302c0c1c43c01c1810402c3d42c2c03034038410240c1c0f1103514080d12451864600f0750342041402c1010010084003103074584210500c42d0b4580b00303a40041e01c00c002c4c498950045e500002400c41d0040e000040c6428102c030000c00c81200002e94201d00d00064a6040e1411202c07035410385042c4000f0040e038400640e2038420b44140d180d030700100ba8142031003900700b900c0c01d00c500e45400b014003003a1b820300e04000704000405003040c00103040540c00b038400d4031440c0a001c196078112354045a210b865040d045e01c2c0c2000345601300b0300c1950700150a0b503001070f8081101c480050a1007880e62103480c5407031009040080c0003a400086a2080280028600e080d00f0b51040c0c0c0c120b0076110800030340c4081e010070f15900403024005880e140c185403400403260404604224110803800c4000200000110020380c0f040030408002104010040e10f40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 743741285 1250 743740035 743740073
    0x4240509030703081909061b020114220f11040612020f061309060b04050f010c050a1104060b12070324031509050303192702040c1e03060312020105040803180109 71
    0xc03c8044000003020f2810501508d8042d681044840340801e208c01035095400402400950012903120100684801d8101c101500c001e14110002d024070541d900c000c41840300454040010540d20a00142c00040c50308020350b004401101d407004504142004004d01e000c07961110008540b900444001c80d502d50b0080ca142080208041c81182801d41540070009400d0821160301301140c5e0301e6079920000588000c008900c003d051036007544075904204041c004084005032185149803900500c020212400c0d00024100148400381100001076102c0130381555648180321400c50b2108001c1040c100b410aa000355540600c0300802c0e801c0c0b014500661700360054000054805981c0c1040e44c800034040c0c40141e525035200f081ca010001d0398448083c0e4159004180c650070b45105564140c1140094040d19040c01004400300d80d05600034001e80303108021424401000c100100c0c02c80ba01100c0040401908001246047c3e103032554070001c1d401503100204805c0314541e2028420869030000d10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 743742535 1250 743741285 743741291
    0xb0a0914040c17062d180d08100e040203030d0e060403140a200129130b0109060516080403060b090601030e030a0c0c0e0424050903070308190906 64
    0x4100154504803030300515920300c8519101c2c0c0d07202e200d04d0322050007510301824203007000140003200c1100c0c800c1c540240c580c40120b66035440c000710903022031105082d110729503000e5a00003035103883c0a064000e01510460080f00b844500341015074000b04000b80041e41d2612092003002800a83c034040c207070441c80003902402d03c900b05480c0103004551030103c404188942803000c050041d6005500a103213080d1040c41064451540442ca401446802d40c010804000810101d564501444c402c0c000540c041c2ca085600d04840c1200800f01c43e95058000e00255a4110070020280710303001030810f5010011410100c0c110b1a0f0b00c80b5581d512a9004548294541c510340c1e03452725011001d181c0c0000203080920800080032a2243c403442503044503401d1010f03240d031788400d0003522480b407006410b0480c0c0f0401750382810f041612405181c1c3c2448011801540c0210a00b0403c6004d400d019440d800000d50901e400c2d90b6003500c0450008241000111205203041c805281902945807a1070080c3c01c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 743743785 1250 743742535 743742541
    0x122502100905011d090c090112050403020304061d09010e060102030f0c07090c0c030c080309070506180910060c0f0312230915040602031e1503070e0c0703030b0a0914 73
    0x150441030110410801503203510110405925031000040c1c0c0100e0302c011b00c0c0d95445a800c0103a824400044a0300b441034946001c0108040d0000020029504030392108501030b0354101810a5201c0c0c00e0031080d41010404004110449100c0e030141c1e0440c0b41401600d0500c0c1c04c0441002194111410030f83c82c0d0303440403d040054204500c20205040150b18001e4850b1205440152005806201c003d00c085070000c0011b0203600144021005041c0c02800c035555926aa50101100241e0a81d10740c0300c0c9280c840400c241c80c800f0201d460480d02c2d1a11a40e10350180d90b114000e045c0a1084164140510000828844103040c4544a04203581288542c482118810450045900113140c411140d000002840c2c1408800c18079513401a400b0354050307529030744c4c205170f04a20311110000113186d185a02c1400720200c2c001d20000b00840f4150b049400d140e603101d0181c07007086400c0c0d42c080710003401000a180441e209400c03202400c00090071505030203668503003510403140a21035822080c41c0394024 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 743745035 1250 743743785 743743787
    0x30a0605091e150c0c0606090702010f0c020102030a0e0609060a05072f0f03040609170a020a03030c0b10120303050a09050609010c03140c0406050a03140a060306050912250210090501 80
    0x842c40c4c014940c04501030501130300d20b16440d0740b0080900030740e116078045400100100d2003500580320b16008a60705010408072050042c0c040d400035500154003d06050b4040b0304001c00252080c801c0034404002c0c40303103484104019004100c06480101004000b0301804030b40341c40d10750b99000c8103180345481d80403040a00c0c0705900b06a00300000d410290000c000c02c10440341d02c808620151810440c4241c08400c07140d600301d03d805584640203410400d9544000107158200c81c130400044d009229000380750381d60010400303040394140206001a00b51148080100c1c2c403c2c4d0129510062015000582c041c1a490b9146000d074101c4030b8211580d101c0c042c01e030005e540341c05038501500105415940342d00300000c5081450280c1d00402e010010003140342c0440324400d8110a034043e54801d2f1040d10303414850225409080c01d40420b803003480c105400b16004500c0000c5150f600d250042d08032341410b08243e035804103080502c0c0001c1001050b01c070001c3c05603903a01d00100752508291283c031921854100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 743746285 1250 743745035 743745073
    0x10302030114070f1101022107110d140f07051005060f0a0e072109050a0c06021b0613180b120a0f120311070302150a0b030a0605091e 59
    0x5255480c1d4402c10041c0041507401030340e002c80b042034500340241c00c0c1000c0d0900301d0090041800c0c0c0460400e4403440b1200c0710543c1da104a000302c45075134880c48000381d201481940d6000180300200010310031402c0c0c84600c0e041a028219140709072600e20326201d807a03114585403031011080c5042140c1c0e03610034440c0c14502444440c01d4107200341c03100341c800c52400300748038130580e0004d01c040c0500c81119450240110341050041100828900400030302c034070390405a9480d020001d048410403184031010413952700000722084d05e0490f1406590310120103070b00340442034000203030b041c03600040404007040792a908059046414030302400040d412510300100a41032103118450010762b0031966005020071010080c166100340c1166600301d001c181100202d00401c00310f40c06901c244008030b0075108055020881c0514401a80c188080e55199983c0c4041103445101c0079552561101c1c8240700060f00a4000f2644500f814007511980810040420340c80900005070781c40a800c007602c1741c11400c01d008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 743747535 1250 743746285 743746301
    0x6010b0715020d0f050109060506221d040506181b0402040f0b09030d090501020d030902030c06210a0216060e03120112030809030a1d0a0510030c140a021c05071a0103020301 76
    0x1140a0142328542004902c0d60b1043c00ea002c014091058a00c025400600268070001c1c0000c08607184c503024460f158841700310081d41c0c02c84480c095000482c40203042d684680c00d64140b040d001d001301c5100d040c03d65812421030802c2c96001070f0284400030740c950080c0718200c02054484080c0341d0b03034000c26003014108400e00c6d0f5007900b40f295000c0240f04030b90307002485000a4505080024100c60a800000d107030440f2880c01640c041e1000915058500c03600c1610aa001d4010080c0712344e5854500e0350718146d010326664002a15101030000d0302049180d0040001c80d220201542d1400e4140c001a5060031030903080801e50540c89007904040681c4034a059501451000c051424000031540041c50054543d1010f428046071018500c02380d601c06100c2d80041a0040098502d4550004041d010b040000d41c481d0200e10f00d02010b0514070a084202d034806005c40c0c1c050510040224410410790001400c1c0504204c000d01600c000607000740790002c1e9102c0100441103a5600d18810542926094 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 743748785 1250 743747535 743747549
    0x1e0e1f0906030807031404090603030e180f0c071109071e1d0f01032d15081216080408150105180411061c1b090806010b0715020d0f0501 60
    0x70550400205200f0780c203480405505207812824080400500c0980340556006200b21074686003001003010b801030ba02603242030f019540a5001e001c080805d0300c100384110303100d8411542500001c4c042c1007001005140c914400c03070840c450418408007149002c00308940030b0000c02e0701d1060101000799100e0030092042401d00d045a07141c48240b415010480e41d06030414010000c1d500d43e5050340e80250003500509140ba0043c3c1400352554040d8510225445d45a0440900c0c00303c202810328005003100090350701920017411010039402080250754020601d004000b60300500b1800041c4a10000703100500103880140710041c0002681540e141041c0e10140c855021040f90f07004009210f0408c56000c0d400c9900505841001d40105001303104000c060382042c40081b2074030000108a40c8403402100f042c030114000c68069010541d404041ca018802199015500411442c0c0d06c01c4000c00711548149600001500840c2034401603801c5502041d00441e1600c000300c500b60110b1203054018201 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 743750035 1250 743748785 743748791
    0x30c08010501150e041d010c120e0705010c020d030905031614091501080613060305010f0509030a0c060e0a0206180906010519050d0e030a09061106040c1e0e1f09 71
    0xd0f0600549450144e0a801d4000c581321010300c130100000d0030b40074200b150000024030500c1d1980074003d00f0905003905250b205840c1080140c000c240c001a04000d80d20181c50b510b0605a25408000d102d1241100c1101006402d16001c00c17291420301c03800780f88000344a2640c4605007007401000a030040015481e000d4007210f070820a5003042e10f0b0b082848130900f82880215600ca103004210560341d0381000e98455070805c40c1c000200501507100c2c0242e42007034101040306e52211104140c50303100d9494002c001072541d040100128089034804070001c6100c200300c803640352060707001c0340d13254202e0880074140704080368500780941019100c0d158401c01c02d1070527514010701c14401d13081141501200b401088800b299030303842022309510003c040c3c02c0f040b04694481a0401004020355480d01404000032410f00b0b020f0007818000501d0b5010f150b0100f098400c480c20050104951411811610000d6034483d8000820083c0d0140e1280034440382d180d01480700c0110b00980303036460031507800000e004c0c0ca = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 743751285 1250 743750035 743750069
    0x4120f12080c1c06090606090807080c210304120b150306060310360302150f0106030e1e010b0f0910090b0d06140708010b270a080106030c08010501 65
    0xb10b42c003140d0200d18488142424004075880410042400d5004a40098980340000c224541c01ca24010100e461201c1202c0b201501c4440c059111502c00b441c41d03070840c180103951010100030341c003c800c102e1450400c1b60300b4260780e030102d06180f450485041e0b0b2009008410f020b44910081419078000800364010070b280d00340100440c0e47e42071086900d2154580d91604800000b4441001c804416244c40e4040684c04031102c030301030400c4410b00d00701d003d40b098203040c0c81034071035044000780b00d040104160343d02d5030f00e030440c107501908690100e110b207806000b2480580f2404a16200e8018005900002c0c00421000070311484c541a40b01f0759100d0f01c030200c00c1149608016001c0d1060303c500359400700312100340a001c500031004060005200e0fa0800c46a02003038520700c82c51901c01d4030317a5506c614071a40e0342c250181140c41213288100071984034415200440b219820a0380307039600007800d002002c0382e5400daa40d085030721680040700e11428011040000903000d0083c24054004100280c2c2d00130 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 743752535 1250 743751285 743751301
    0xd1a06090a1a190f030803160c030e060f09060c0607032004030f021f02061501050901080f04030504090905060a0f02093607110d0806130e010204120f1208 68
    0x2c40c0001000d10500b60408200103850201c42a00014007920310902001500c0b0710b8298215003007201c00d191584185c04080341d81d103108003580002d00760035494015048582d4014864140c0c000110307011080d03400c0160382c030340d52100801000320840080c05400b960400c20001001c0d03c28090844080c1200300440606014050b0110b80c112940001404040c500502c081011500e1404450342203403100f240d217014698000c0f030030394403d43c200015500000000001990980100c0c40315a00144082001900c40c50381c40c1c0d200c0c0c1d0018003900380a410196079610300d4040e00e49100e02100c051f0850000c3c030690003100d0140e4014050304d03403800e500f012400c80104140240c0c0c95480d43c1c03070740d0b520034804030642d81c1e41481c01218540e4001300d00040c0341c40a4060f10100b040400d0a41c40d00c02c0e40f01aa00140c42000070b240508001000d580ca003141c0f080196002c0e00b0310031943c1c246035508000c00601040100c6411000078810000400c56803003a003800c5480d00e0b0140e09481c1405007035000c010b542 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 743753785 1250 743752535 743752571
    0x80901020705041505210a0c0608060303040f09021c020f070302011a310609140901050907091a0d03200a0203070b070f140c030d030e030708090d1a06090a 68
    0x20328410750b484251081b104003068204030100204190a00078003121400340310ba5491080242c41c03139a250b4009030388446042c10748d684110712600709500c0e404501406042a1030f001483c8080300d00c003004428144802c0002c0481c0d008161b400b1000c42e0000e80601003603028043c1c4500c803512030704186842c0b00d080010400004e4204c40c144c407403a81c80090740f5000300d04000c40701c10720f040c0301e9001c1180743d07280c424080c0180311071100700700f5400c014400a80d074060b0500030140300d400f410b40070300100361a240e80702d009480540c1814902000700d0b080c0361010f44840c2800300c4c1b0507000c0c1d43d6608130040000e00e01404c1620b036481402283c0c112054040240e2030000700780c421107007850003165a569403801d220b540c440f00710100424440000a100710001000074099810310b03001c0301581d40703007140c1401c00d804407030401c42c1403102500b00744070b9040403881d00f002074000b200c00502504000e205654900c0b991540d4480d6003000e041c0682e0900080d414219807450344154203800801480c0210500d000c44 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 743755035 1250 743753785 743753789
    0x1031205070f0f11040b04020a0c2006030f1012030c23030309100b0f03060c07060e19031229031e06040b060420030c160809010207050415 61
    0x103000d000a108020008154800030b101c40d0003c00018209490b4030b03101e00e105500c204481d10072810701e04110480c1c0303080c1c0300b03c0d11038443c140c4809420039020360710303003100349101c18100c440070351200480c050b142c8075440194070850405002000615000c041f0840728403598003d2410204003400350300c00603801c11002280c3e20340261500030145000b8419480d03002165059082030302001c030501c03889500004d000c40441d0f80311f2105000d010b1500003440b2500c1581000c1079450b40c8018081521051104014844540541004138000307501520b12882c003818030300702c21880d03018554940c0c1810791090613a2421188902c0c20300c103a2520040c502040030b01c0c8114030180da82d400600d8405c580d401c000280c4480e0003002c2171703000b095642e2061500c80030120741c241e550590407400150716140c80c1c490031581504550038803840b521181c0b00458246c00051040164441c00c0081c42c980c0301c2501101e031203051082481c19503415100340028201030490340300a00441c00c1c944130911140400e20000c5c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 743756285 1250 743755035 743755037
    0x2060d020306030709020a0807021b06090909010902030d170c0f090111011b02012a020d050a17130210030c1e03110a0c0c0b030702060c28020304080705010503010312 73
    0xa220b8559000003403e20505520044845200241344074030b442e000103510340300300711980903a602c00a550701001400b40e180b58000c1c0d44042c00f0040001540350143c040754002442c0d000005101300039a0219141148020145000c100d81c004950740e4003084001e03035a404844d151803c0d0802004103102603007030041c1c002d518184480b24018802c00305c1d096000f1049407001000c02a610140300001038020115100d030720150050f000310f50004204490005803042c403141c0c0c024080800000d5003100c55421185246041040b803101003402d044004901c64041c042005d5840f4401156104201016903050000c40c103150a1081401e8559041800c802c0207181110a421380d060103114118009c1131074012032050a0000b1460b08812a0300080d900765091085c81441445074441e07600900c40d001c1101c0c0680140c0c0140b0000c1e400509040c0a449010000d200038226104e02e40c00d0b100840700480c03684c10041c0e00100e800c00c01e100c01044668001c007400c1c02c150f45154107540b2410680e0001c40b104da0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 743757535 1250 743756285 743756287
    0xf131a0c1b0607050715030c11030d0b011404060206070305091b1c170403020301110418021c0c0206090c04060303480506060109230a1710061202060d02 67
    0x9079511480b00700d0b2402a4054191407006468001501102c084a0000710000c0c0c07401000c0910b29018090044000e15002d0055040c0110104104c019001901031941080580c6941d44081c1c0041c1c0090f0000d0100364029002501d44404000c0881c0c030000d004041941c0604007000d1a00803400d0220100b44040e1036a5032021ba900c80c0a003001c403440c103002003060001002c0c0815000c0341c800540140c0703108030003d01081107007801c0b1142a01607805070048a004100303000b000c06401c1e90042201c081e43d41c0120502801c00c0403600c0803915190000405a0080720400102c0c00c03051042c0c02403c10100d40c00c000003400c41c1c40007014501840303542c031030341c403c10200304e45500b02d481d040c5800b02c80a5030191200c01085c071400000101030410486080c407403000400c6556028612100c2618058580781e418410303150746588100034200045074002225600c04944030303070b40d88400c045d4200010014030004100340c85000885207580c3c0321105660285100000503622401200d1406014800c09 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 743758785 1250 743757535 743757583
    0xf0c0d03050118051b07051b090106020d0e15030903030a0f1a1c0516030c060f050a031d2a0d0812071707030911031c030e030f131a0c 59
    0x860a0107083d05c02c420440c10042007110410000003124680504003070311200801d41d6150030300071456007e004180160700043c0e8000f114034481d10712404001c100500700064200fa03a400340c10161f005503203010441e0800402c101c0212a42e02510300042d060308420010ba0314040c01040c1881c0c41143c800e4482d41c1d144640c021256803005d0700b08001500101654141c0100791121046000b04d17210840b5007030700d504070010f5464001e00c00407003c40c0d42d98aa9514001c00d40e401100240000319031560b0200361024103201c0b114040103540e418840e40150b40310110030803d40911030b1075080940612901c00504064001500030099415200080a20403840d4680d0300c000e0764441c840c0499440b02c0c1002c40e04000b120351380b54201481c0107000b008007500c12a00d1405040d1903507500c0410b441c18003405079441d100c13640300354401001070400005880c1030408100f4000c00a900007481e29130a82041e840901400c0000800340c0200c0340c2d50600c42d03150118000601c0e0310340c0d10f142d00600205204c6164 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 743760035 1250 743758785 743758801
    0x71409060706090b25090e1b0d051602160f090902130203070c0b06040c0e1003060b1305040c051303020907110114160e091504020c030f0c0d0305011805 67
    0x403042c1d0715409030416203145841010a810450703a078400d9011041c005112464175800b60141e50242c5581741198521599001161144860b80f0071007141014000c10114510000c0380c8510b42c041d500c4807100c2030034000d408a00a203030001030303ca4010150005034081003945400b407104403c80c1e009541c04107154460b0b000103140b684d1712240300d0120343c0c00082000441980301c5a0403098511a03210040c0700d49480040c48202c4070980c44020225030400f00300f802a14010300100c0c002603d034034010401d2502c81182e40d141d81c00c000682c0c84540041d1074244034500d0030b80101422215685425030604042e60841d0360b0200d942d206c00b03400380a0080104140b5481000050f40100b0319000a000c030317041c00b803113040030010104c0701821802c40000442007c3c0b4400c4450441041000300115003644a032000418030030400e11280364081e500304a05087c00c201400070304000c0542001c11525040300000e5641002c0c81c1c1c102c90300030140f900340103100480e405903a0700d01280c0c40c0c600020b856a03410203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 743761285 1250 743760035 743760041
    0x70506040b28421d19020f04030f020103050a0b060a030905071e1d0610050a0e060f0705151603020309241503120406050304061d030d063507090f050708071409060706 73
    0x40007441f040360004000c0b060288030844104010f01c02c0c1e0b000c00540d0b135030140e0101290b107060815a840359007049103500d050301c26000180c80c1c074003806c15aa8544d5a076000e00d0148203203003410100503044140c00f00300c101c100d0121240e0710066031100c968145071035000551010207040300e6406104020944022680c401c0c0e25421890002a01c46561540403469089180c3c01c1114110380780c0c8184821070715444e03041c504540c022001e0702c403803081542c1200000d0b07020313420040100c2681d11801c140c50200c540da02010555090360205622214100790a80040e24402c03003c240d40a9404600441c0344104180e08940c1100e18901e0550703100e440324a00040901011550010252207107440c482d04024044000d280d000500030741005007580d103110070558050f84002141c03c60002003000c95880c85002c034510058071803c42174070140741d1110b4881c0126091002801c1d03005039500100700740170b03401030b00527608450386080429241060f040d0007801c83c4120103049000c2c0360040f60341c00420040b17030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 743762535 1250 743761285 743761297
    0x2130f02030a050415140106122a1d010c080c1908040501090906050604050607030917160803090a03030f02030c03070506040b28421d1902 61
    0x8005659a0414405880107002d00341da043e101c142d44884908086081449132808141c0300580a04e034503841c0081c1076032081c076a000c0b814851915901c0e41245090070000f2072000c2d0300110400607403542341d048001c168a0b801c50b0388584817181070032901e5507070b03070842d1500030301030b0f4011a0144d681d08014951401c005548030040b01d45e10713095102d0010014490058420b1751001c0e41c0320090030b595112080107440880c81266003025040009000e10308145000781820740c06400c04004c0d8680e07403400101100542001d0420386d8001280e040d009400a8240c5001080d55030015030502e1031403400035244514611000382405500060741650794020300942c1d80303601d840030680303440303100c02e0030543d40b1401d04440c21a5a0429400001c1d80586c01c1d100b5004080008940c8030200740c2144a044000c100412400540340c0d040300d22a40d02510076130a05050142556110244603032001c5412a003a246400000900300c0300b0807a0b248015461102c40c0c0e100d40d56640c1e40307081407482180c42001307105034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 743763785 1250 743762535 743762561
    0x10f0509131e240c1701090b04091a09060106030e1506152803150911070f05100606031b1b0602030f1006030b1f09080d02010e0c040b0901030213 64
    0x1040e0400740720070f40140e40040c1c0c241408418001c08400751012121071104003041d0603090106001400101c405903c2142c182001400c0090402200d444040042500c0640440014240344c10008d0381c000503c01240104410308080c002c01c2e0131501415298201c000b0360910985440000680075611071207140c2e000088440c060b90b5a000300e071000c1051b09111040046007020110b00d0040700b62280c4219680c031501429030380515410118594080c0110019419400e9018820880443d160261803d030462240c00101a00f00301040b880058813402d91164051516214049020018480180518030800c0c41e00288031003182c4038084120030003a0340900194808130800c032010501c00305c024060740c1000d4100420300c2c4d60304d0040b07003941d407040d0b0603581007500300e0040700800c2e110b41010142c0c0d41403420314048050b01e4081040c500500c4020040040c0c3d110703904001125800d1003030714040482550306100c0f407000301002c00e00058040c84001e020303d9540303000851100c007541c0014010001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 743765035 1250 743763785 743763803
    0xf0f14190b04060c0c080601081509030903030406090305010506150904200313051e0d1103090d0606091103100302060309160603050f062202030601050403020315010f0509131e 77
    0x21403600800c200d10700e444c202e070f690100d43c0d408a400a0001550350403510b08900400420340400c030f072030703501ca034001d058920344e844180321149556500b031018001a00035031b41c41e2440c1c6869414140d0944101a0081340240e00d00d103044c0d10664072880445455038401c0e02c02055151108071002c004030950310032590000c0010040c4600f40c10072109100c1498018001c860500c001e4070321f81c2001b105202c0d018481580b1942100300120b004a01c040c085041200a0342e0030000c400c404944030b070242d5a001c0764186da640c9002e0010018500c228040c01e25481613507419032400030702515024080d404064405d140c08000124051000c011a100491000c5c00e00e0f640075a4030075001e4040c02c070a4030141255105c020026100e404c1ca140f004010322458a0f9590b48044414903c0c0d0084d0700180280d0704102d02000b021016032070400010390011742424052a09600d81014001c914a280e0000380c403d40d2000244210030200140d2402003603040680d1400c03003a42c580c0c0c00d641400c0c0d4440010f04c0c3c0d0b0a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 743766285 1250 743765035 743765039
    0x9041b090627170601150e09061c0b01060f030b030c0405040602041d04020405011202061602030c0406030b0f06010f02100f0618021b0f1905250f0f14190b04 69
    0x1240007100c14040b02c0020813213550b641c9400b2032010b20030720080c0c41700005080c841c4d151902d00e4030280c495000803001e4016000584400c07076010070f44445d10802d5410a1140303004001300da500040680c9445070a240030040b050301c081c0029181d03d69010410310698544000c00c041c0603182d0704850080c40301c0205801461000103c8421680086805901c514a48000010703806007901d0444001d03617008106501d880c03420b24030840c01e501c0030403059070540700d681d00300c10198980748210400341d400742e1001c810900d0307c0300752000700c1c1400401c01030401001c0851450020b400064450060042a1010521031072074051500106000d6100244c0e0800440c03070402400a070340e005204100700d0f100030426000200542980d9003029481136a12036024440400048250102d41220107104038166111b01a62401082d4420350100341c2c80d810b2852034070304001a480c02d080e108003e0054540c400001803030401d00f03190311169003049034080c995502642c1070100030700c9807050140068074002c0d0b44441d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 743767535 1250 743766285 743766299
    0x1030f111605060a0504080f03041406070c061a06250c03030e03010b040e063111010816170606120403020102040914090309060a02030d1109041b090627 67
    0xc0180790035075960083c1c01c0859079030101402810f10960b04560402d00e80a001c524031381d00703036000030801c1d0703403200e1418200b0f0420780c1c05000312070161510b42d5a0b4042c40005080c5201150030410020f8220382000c03e041c4241e403100c13800e030742e4091030750140000d103400c450400b07984560403494004d003082c040040100130550440100e0740840c0055001304101c03000b0a0502048075009030a0311601d83c0b2000004410840134645402c8440c500d21013110280d1290b054588001d0018600b107030111040a841c03003ca590044160340c1c810381240804a01c244035940c0502441502c41580c1c01e188900000507130692110411212001c3e580d03014a8101d28181c20024001e42007030242074141c50909104c0800901d025a0841c02100b16201561500d122842044103070390246a140d070540c081881400300c80030242c40313414040107487d00341ca03036110303020401c11045500c1100840d00400c00e002e5207540389944040d500050790340d9170401c142c505902041c100f150400651071060884801c402c04a401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 743768785 1250 743767535 743767567
    0xc010c1a0a02040609123503010b090306090d0507030c110d0b01080d0509010e06030a1b170a020a020d2f071e03030f080a0b0604030b19061401030f11 66
    0x4699913554000100d891b821007000006513a1000707044021010007000d40902c0b802e02d0b8a200092196080b250102c08140303a0740b01e90803d13401040e40c42c2000c120000035090038403100d584000744c0e0020741108100800c000d0000e018102000c5c041216200460041260040031607103420002458014003135000c1c07425204002c400d024610f00340c01501410b643c0c040c0103c09580e0f11180584561940d0a803d009014803500000c2c28059000d813503c610600d054101256225039890558651503040d11001d11120090809440c2100c8075204004a000321580400c02e02d54000c0a45000d003015550100210440110f030720000a8110318006180d5820720002034a00880741c03000c12800c85044180064103080b800d0f448081d010a81c3c02900041d80c9228102c404e52025000100081104280010070310a4000d50000c50786110658240301000c81585150300a44980e040240020340c1441803143c1c2d103051120300c090605865101510811595400c1600c50100c0c2240c03a6440e08070800b002895 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 743770035 1250 743768785 743768789
    0x30115050418050a0c05270a1d070e0109050d0206280c0c0509010f180207050111041d07050a0f0c0203060c0406081b09010507060e070b0c1203090c010c1a0a0204 71
    0x880b92400741c2e0170020501030000c0d1084901c50800d0343c20202804140c2ca02540c500c4180d45a202802020100c0e0390b1000980c0c6809a040400d0212964600054080c4c142ca80c2d6520310b44c1440000002007100d581c98020044106505850203603c1d05011005485e459031500c000308082c04148214503007441d800342c44004283c0c01074800400381740c6e40300d0074032800f02c5003801044251000d110342400740c0047c2e5402d9054404032180d00618050103521198210307003202c0c1000c441c004001500300081036541d405104900c984c0c406861240c00c01c8140a08035108114080050044450140c4c00300c9000319081948240c01400b0b031881031802c44010001030f4410302174070740410901c4012030300e06440340651071034041c0303540c00052512008134015210f81d04030140403904640c0310030080c81882d0382030025100805000d00406e444000b14a19181041d00a008584800e6030520400581c0000000d11044500c001c0c2442c0801038150300f08208540124040c550303000421034140001c544030343e03004000b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 743771285 1250 743770035 743770051
    0xa090b13111806070f11010504090e1e0d091e120605040b07050c12030432071401080c0d06120803060109050409050a031d040608010b0901120803011505041805 70
    0x182c00038480301040803601400c1c40c040c1180c4076003900300d400241a08464010706105040050230180da410308413040e111403840c200156000302c1d0142040c281004d2034054035080242c05040e03c0711f400c00d8014541003c07440307000c0c0702030710b00740c04416541030840400e070107090756207180c0720b034040c0c8e03801c1c0100606020703103088071207000c00000a40191b00c070710b05a43e043c2c041100503040c088000d2042c0760709508058020381b007a41942c01099110101005650200455100c22901c0c12110020b110304200b03859000d03440046035909007042503a40b04950795031201142514541b82c0c0350b242c460400403c036542202540d40d001000c0d0b4420700143c140030b14840d4000f40e81d80b001094a850a100580b0308013000108070354000e900c0d1100007400350140a207844240009024880014000501660315542c80204a41d5444180b000c481c00c045010074050084000c04040b017165558680480348014801c0000700001d441c0c0129400740300c4d0b41111b0040030100e140d0141002c03050a0360300101425100c00d8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 743772535 1250 743771285 743771317
    0x20c0303100e040506181f0905060604020c0718060306090507091505150d0e060115080108030a020c01140c2b030c14130e0a06060219020a090b1311 65
    0x4801e42076001407485913502401130f2903c2d403102c00c03088281c42d140c1e03074101405005585858000b06624080743d4034255924201003107440040c00c080d1704064010309030340c1c0624010403806a2541e0700284860443c0d400000f040341141d024400d00009140ca03800080c40c980c1000440c0341844400210305d400c0e00c19250342040017140c000d80c2d403a681d6603a8443c0075004403d4801e6420304040c1d07000a42101c1891030804500e5454081c6400d0415009070001d0140e19103040403a0b01d1030b5400031401d07000d0a911802107144c80402c2d82c02a65070310070b0710421810014681a0b40150349030300c009403a0610488412a621a0f40804516030f039109000b5882c0941b120380c0c0781100c0c40078030038020ba031420360481c0c90b1504041c101850850301c0c1c0e48140701800c4103034820b20001584451030841e4034440c410800303000910a040403002410b00310142e8040142d41d103203910200c09640d07140310301c01c12541030440004c2c1c072500328400700d410f540000980c41a003d141a42141868520030f00030321000c40941600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 743773785 1250 743772535 743772539
    0x9010c05100c080916030f06020d140c04170a1a271b010507030921021509040b0904050705091b0c150604111206041416031802240d020c030310 63
    0x1001001d2501d201c041e120610402e02c1d031008c107209070b00074420702c101c0d00004108122451015001c512045d250351614060003c1c0407c400d40410303a6070204860303442e0180403015100c1d02d0707480c1190b10903540c111a141c1c0c01d0000c1003a08880290f56142004c0c0c03507000c088181d4000541030744607190614101c600030a1504801d40d50341c841d00c00c0b40c04003581a1108400242002e065000c542d41401c1002e0100785921980b0000d41d40d42183e00c3d51450706060042e5642c40042d0038002965a4110168020740107007003400005030011942740c064030019105608180d450441c43c124998040c0344010807408001204150000040768a680100c03030240041d03450780703940050101319107414041400c000030a2142c15821000200f0f00d40d08260700400200d44217a105002c11440e10007560321130907211100c0061902250140103900a0002e080030600f240003050700032812010720a5600350881d0f6031802130701c4415524030b0544442d00d81c0c541c002c5494031091049503a80380c0c0151100c0542000b08000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 743775035 1250 743773785 743773813
    0x6020d2909011d07032f1c050408030c030402030304050d08070203061803040611030c01060b03011503090f0b0a110406030906110405061207020709020f07020913020609010c05100c0809 81
    0x5554683c038200d40d9a0380d182d0740c020040300102010200000c40500c80b407080040c05203c000901a00700140489542d01d81203110101e500d1401d45c582c18510f5810034040001107100c1009890340224100c0c10720340d0b00c2d500c0f880080e00f90703c50354000030781c031540f0919101c05200c08400542889803003503084034071503180d42507500580c41c005080c01400768001c101c140b00ca030780709454941051400e0800c603400c0261907109a402d5510942246501e09000f000410441ea09684800d98090203800e0070005241746480303900811120703140c06801c900e5207501042e209a4554446c400c1d50600c10380321911a9101c2e04014060310200740103a81c00c03420018110000302040c3c00b11011960010a80c51030044026400c4a001c04010300e00b2055008442001986180600061058800815169036a031400c1d104025440d50060a800810400d09000c040180c0f60301044440320042400d013143c10401c0303403803c40e19005d508003032210004c0c02c158040400581081034540102e01840644149403941c1c05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 743776285 1250 743775035 743775059
    0x21206060f0f01050706020325030c0804030c1103010e01150807140d080c0a0c05010f030507082214160506030907210f11240706020d290901 62
    0x2180c503445046062035011a1410900c60a040715044c1010750a0842c00c1d2641070807a001101c00400f801c0c401303c82d900125190641d030240040380c07402d0800a00b10754040c010482c0350000c1008081c042d28000c1c038803d101c03c0100c03540311600002e00038404000e85d10b07229406002d58000400721004908000300d0500b401280f80c4041e98040b490f144000c0c0003031400c0141401c0305c224143d42c12841000402160340092000060042c0503480c00040e40e8070382000145441144070440c8101841c0c0400d00441d20303406064250070030820380a00e25080041d50481508010040c4000d090383c41100c1d01c10255400410400c140020750403282c41c005d551202882003034401210244d13080d411103881404074090b030b8420403c24501c41e15045c00c10405d1581e40681c1400d9041090380e40d2602d0341d0386040141381000c51070031100403080328806280035540d4188154011080010301058001c038000310300030a10380c40350f041c1040700381404211061104041c212051001c2e020390064001c00004505466151 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 743777535 1250 743776285 743776291
    0x16080a110f030703141605180f03061305060f0105030613051c030f0c1407120306030f060e0d18030602070f021c030f02060c030610090f0612152706030203010612021206 74
    0x24440038a0005800742c403003239008a180c84254001c14a03c4403414035101002201d01ca42229a6049038250090400a01e48100101071000703003514880140305a0710085007140d040004140c001883c0c0410f0f150050410800310444280c00ca82c1011414140703506070890202c1c1a4001c80410001c9100c09048500303030003101200b071980008201010014102401da00b0800c505440c00041468981da200e00c80c3d5141135406a447c0c64039815008164141070110044000e003905041054204104404442800e140310180038540d010403580c040c00b180780d0410740e41c01e900071701c40015052a0300150140c0c48012006400190986100d40101400065030318058525454a01d040d80d0b00e00c01003148100405494000708400384030700203900307204002030401801c2503407502d12400a108142e14216480f9040303465210b000104104180f44000d21180c0c030b407104066105000800405041d8091700c61540000c0d01586044000070301c00c150b80c14800704052080b0b403000c5500c010741c5003040d03482500b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 743778785 1250 743777535 743777537
    0xf0b0a03030512040c0503011406041505030c01050a1205070f1202030403090e0a18140d05122e08010c0806010519050d090209010e040b16080a110f0307031416 70
    0x42103103891070050808066401485280c5c544040764071000841d0a440c22400c80411442c2203005000103450107006914445100c010740e02059868200042e40c1c1d003680ea11001e060020005080b461280b0030070032040c0c00184104184824105018003e20302052401c01c1d1000820321109403015541c68021603001e1601681d6590300c440c101900780703615910240c003032007003141d5500c0d4407064109030b41000030f20320f4020354505490b000401c100c2801d281145280320104201040108100c44d2010801908600000c3c1d04024149002189400d034015901c0702d4070f0401ca1420000030b0404054002000681c1103030740f240e100d503c90900545150040e05510f0811761035680c01d4001c410701c079201500d9604623140000c24103a51540106117042c50a800c19408130601c4000c00c030900031425407150b00100084c05407e841412410003c0c11910054a05c000080d11400d81009040815040c1d4480b64030821a055403420301c6c0b64041d00601112403070f10a144883c0300050402404076031807030404201 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 743780035 1250 743778785 743778787
    0xd05030c0304200301090f0b0907060804150605130e070e06010e04051b070813050904080307080c041502030913111c020705030406080a0e0d140d0905100f0b0a030305 73
    0x5640e58a541c2091103100d0f105040100c10b6204120b540900401360b0240c01410300840d074031024140a800c603200248007403000d5003c9074040010301e0f030203485d0170b51164004000310150058910180c010700440d9002c185e10101c051024944030720745510070051440341104030740c00a82d4400400800c200d04032a10707408107201552880d0036040580025500c4084020300c080600f0b00e02820760587e0300440c41c142c0b000800492002e130708014114820000c0c1604032118100b5140540c3c2d042514400109090100103c0c200450340e10b01d062025070b8058416040c40c0700d00d400701d00300c00035235030340000070003070b1080d05503802c41444012a4410307003507422140a0200d252030759500750003440707107800d880310b200c281e5081261202081c010310151020b05182d41d02c0d4006810035581c0d5a05031232050010072940e41003d209061030b01e4001e003030b40708110720100381291902c100c07a038031100405a0190103400b600a8144c00c200c01c180a0780840114120031070300b000904030300024820f6280c2180402804540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 743781285 1250 743780035 743780041
    0x60f0904061d03030903120a11030105310e060609100b0c100221070305090604020d0218090c011b050601050d0215040324050601090501051b0a0c080d05030c03 70
    0x200c16048008000c0d50011905055401e08941d0780c95035004941d10007054201040d09041f4001c01c2402c123810100c41041444104003074101071043c4d2106110b05071003001418aa840302c68091826010480307140d44080130a02c00e0286c0f008040c1c10144441005402110700003405407070000441070042c2d10300c140d21142d40381030810b5030600c0c0d8000404000d4510a841e8000384445860009008010155030000180c500000c40e20201c101d003d494030050501780130420000c404d0018503180c0c059012107030381c0c3c1004141d002240c40f11002c01e00c03145204039203508010805000007412000c80c102a0f0340c0c02c10705008590200306540488500500310b0b086480100240d2410f1210780c10141e0000b02100042194040c04032030640c040c1c0c1c01260304034012101000704558104d03c0c02001a100311041c003507417400d0000244807038814055103040c800701051010398402c49040d40303e9241600002c560b08070849050040f403880c041d20650600c1d00c03541c0c4822031224402ca007503d00a8043c0d00a10341151 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 743782535 1250 743781285 743781293
    0x6080a0e0109200301150b0705210d150b0c01060609150804060e030c030d0b040b0a151805040905031909060912030c060612050c010e010e040e01090605091005060f0904 74
    0x583e26220180e41036480e43c1214498441a101800c0181407014049a0310180c42c580300781404000e80601c80001790440d0754241c035074400c804039881c000c140c410000b50103060080504124105e60000c00e2810004102840c88200551000c4103840300c5441744144240d6600c60014802e00d0a10444001942c0101003400101385400c1241e5544121060300d040100401e1100d26582148240300841e0343c07070341e011131041d052070310411000388000c0c1c40b031036076540c01c00c03592004e5151400c01050400006601c000c42d64042c0f48007d0015040060090001a03d641007070b1307030b99030489040e4051599016000d40413290040c08884100c60494a5002c03c09160441642c0240c61441058040c408400c0565001406512074003001d000e1030f11924191010b1800e106140c0111503015906200b82d50146840a80c0c02c40610202c901c01282c0208014035664400c6014081040e002030003e401c11091240ca501c000c10358060901444400700895900c00081003129200b441c4800c8c0c124550f180400c1c045 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 743783785 1250 743782535 743782583
    0x50604090e0a02060f0403030905030c0603070f020a02031603030305011d011203031b11060603070b0912010e150f2505030a090b010312090801050c0d1d030406080a0e0109 75
    0x1c0048041500d82144468002c03c00c81e074042d544004036143d0010f81070040503000114100030f00000c1d002400c1c5207000002207042d91001400301014402e1280003a42030038800c001c81d0300030581c007500781d0b04441c840c0104d007043c03400580000c40203c1c0c00c003800800c42e500b070100720084590204e07445091036440d040d4503240601e20302d2800d401b0540c4940c2c0c09a540e0000715400030074406240cfc0d4460f001d007540d1820500348500906581d200b904504c8080280000801c140d6003058400c564141110700c400b1b00f41c40c010955440c00b13403050301680d2803000b801c000007a00319225400c000c1c020151540d45da904281d40e4070003410141d1024000d0045159101d04c181c0c041c65100b02c88100000c0c003040141c60f400c00c9104241c0c81107038040c00c03000e2100041a40131642c039000304418802485141803d500c1d104250203101c000c001026510600c0700d0803000b241c4042c80390001e07182c040d40d0b80d8036110f250080c46e41000b264411241d42c1804403600c1c444005204034514590032030b05c200602d00c901d048403940c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 743785035 1250 743783785 743783801
    0xd0b0603040210110304120c1701090f02150d0f06150903080d090f0b1003051606090e10030b0106050d061703090108250c020316050102031c060f17010b0a05060409 72
    0xc4e8030082c440404c101500c0c520038120340b40601c7c3c030052524a00a0a010103000d44400320000340d0612000000003142851590603259044500a00c08040403041002da801a000b8890300d1506029170055250644d0f03120100b030398441040c00c90310215040040d9480c410358031008000403802c00c0011300da03241c1a8020040c440c400d4001817451521505d0b4810220030a0b505c0c0c030007004c50084200100309080060340d014101541041811074900349003e0a00c007254411255220750b4400040c2d0b03e1103a50004c90044c69102411404c0d40d61a2000200183c11440e0101c0c1c266161100c080f038104c19003051244030060080c011461708411400440340e085020304842e1581140390341c2c00300c0d00102060b0200d03e140f40da039a2422040e0341801014a000e107a0149404484070400041c030499901100b12203c51240240c06244003010000002c001c0020f903102a148a00480f400b0404a40103042070400000110003031100c0c0c80054200000d03440d80d4402ca551004080004202c0c050498101941d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 743786285 1250 743785035 743785067
    0x114070b06041e0f0515060a080606090d1a0108030f0a030e0c0310091704031106030c0904061409090c28050a060315080d0507030309140d03020d0b0603040210 70
    0x181015101000054400f41d0b1680080c4207602c8411141450101d44140c1d940140f00aa1100d14001124049900c0b441080c82c000100016403002030395507151103045520940001c1d200c00c000c01103600b07045014a00450320050100f158400002d0f41500000540da0514002980c0b41c1c900340c2307440e4080d00100040161480b0350b0180043e40c481c507a81c00d010142c415059410041440303500344c5440942105004112401000b05100520101d82c43c0c01003200c040a041c0c48455490321614040b00301ca00940b4400c81d48241044004902030b030840780803c242c17501c00e4450354001e84415480c0b507180c9a0b58004160003600d0300d1050011540c035100403850300038180f19480400d58540c0d012514030509030b004800401d45915900c0b000101d00f0007050b0041c00521702a2510f074402070b6004141c0e10500740003500300f54446122405010314002c01d0710321179404004903500000401e0018029402c08100b4070005450b0444001440c103040301102d228036401043c8030740d8058060700980d041201d52001003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 743787535 1250 743786285 743786291
    0x60a18150f111b130507030606140c031603050c03070807020f01020c091501091e1401050711040b062110060309020102060a0504031b06020705010b0f0f040c0e03031b010b0114070b0604 81
    0x789040341403003071764090500c5a40c00b09401e82009005003550305910840803c081c41000f04010003a0003000faa094014101c547e403030b092107142011074850041e00028000340c000050307030701c0400c4803030303c020300c04607100740c402800c01081c800059072180c50000c0d41c1a0030440c0341c03001175002500c0c8512007910120504103d6412a00c2d910086121a0b06240301d13514a941d0500c1070040f07998000e20011403000900c2c0881c502001980c504c00e90380c9901030b030300c7d006d81c1c2c0b1090030800c66034450060302e204417010407810390f80b0355494000541c850390940340d651010481e1140410b03050721900400300c5441c2c040e00200900e449045103213004100c014015010022494008074a0126500761481031074040c000141c2c17514030132708185084840b550341c130910030445003907d948030307441e4048020001c503400c480000301048900ca065600381d20240440e40d040c0800100c850300200c107070140c041c02841c400c00170005200c2080044d80c00b90112408140200c0c8103100ca02c001903c004142540200d01078408 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 743788785 1250 743787535 743787559
    0x90b030a06330c05100903110d2f030f07020307050603070509010306170304050f19171b0109030303150905070306031a150616120f2c060a18150f111b 66
    0x582014484272941002400501d0b501005d600701700c000c0e040550110101f8004042140803d554a01c1842138000c034900c40030030300600350764050010b68001c010150460f40d0b80d140c8480c00425590040740e0380b5001c02d00d46040881d12002150040e41400141002141750608140420000450356000030394004000c80301002c0d40e00c20204054002c0c800c8418a10300c41d07204c40354090521711900c201541d0030007030b200102e04e280e0b1700c60748501c1101d8041c2030005518000b83c40c6405140640d400102c5898180310601089a90643c8500e080301c3c080e243c4c170404080000a040147c0d60181c135040c1001c41b208425070301030b10b42900200100c000349640d60b80d0b01a0540d0302d05800d4006001d001020600700130011214a41001c0c58150010225000b41011080c80744010110003c00c041d803401200003080c40950342e8040c20b00d2260440207442528106a9500c0b0b000140c802340480110010b03a8243c120f0744402c1c0079a46c2c603004c03d0140c00161aa220070401662407022207007401c1940b04100c5065 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 743790035 1250 743788785 743788817
    0x3061f030c03080a121518020c0f10060b070206070b1824010e0601140f0c010f0603050d05180906010e0402070614060d03090b030a06330c05100903 65
    0x844030045204011203900c0ea090030f04058007405c9071070302c81d00c04542485042c0307246042c46030600c004d40e0310200d4a02c0c44030380300f81d00341d10090003142c503807901c1441222862a0646030000c0c030f8680d002302d094020320155850340030340d40340f07405003c1c03009400a01c140b0013040042c80e07941c2c00c194028030303501c4000c884080031640a4608101303924958a02c0c1d000031801e180000100c6602070150803003155030b200c1c60515200007020f400781603850307103101040031421803002e107100c40456000b400f0000c0240440b807941d04805009000611003240c4902c2602ca080c900d05010b0401d4510364400d0400c10410008010305001c200080101000d0400072284403040d45036886101401d8114003c40000811040c40904211031260142807540300700385241002000903407004012040d2180c2c200c2443c2c41c1e803610050030001c0d190a801200c2100c0b0b071000e40d0200355400b180500803808000300300f2420004481010349064510280281664108034036800c481c0600c1e40014110070300c245050b13030b400a88540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 743791285 1250 743790035 743790053
    0xb0a0e0d17040b1c23060a0f081f141605041505070c08031e07020307170a0605010506030c0a0f0e0402040b040611030c0304051e030604080912070503061f03 69
    0x104400d1000c0119a44c00511048401250000780c10641008100000d89031040340b40c0d220540300203144407400006e801c6459880601c070043c03444442015045441700080e0b0b458600b0300c8010405803401519a00c201c103085d01400e200350f07102e1342040540d80c640045454640ca5a0000b580500c5020030000460b520708a45291450305640e9a890301c13a00185001100c403c203983c000d20350340e402806502030703404031030800341c07040d414201106564010620100303003808601d0b032102c805440d0600ba851411200858a5440e403840b0301300030040b0303a8035001008080d010980e1108a1080240209544a030103100ba00c5002e802c141007a04203002c014000905a80c02030f00b000c042224040380030048103402c4092455447c2d401400743d070a104401c0c003595a01e01071481001c2c406d041500d05c52200007080c80c20300380905400380580daa07501c1c0a05002d4050f60065440038011100c1c1c040b402916440890a9020f0b100000c02401040d1101c48800d01c40f0800e01b10080300b100548a000000a50404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 743792535 1250 743791285 743791289
    0x20307082701020a030806120f060406090515190f140709090f091a0612060702011d0610061218142b050a0c0f0b060a0b0a0e0d1704 58
    0x48203400414101d4032071034420380800a801c90540d80818803c0d00040e40012141d81c0c04541901d203600c000c419074480303510702414451141d4050040320306000900c01c05070492040a8040c0f800c4400c8880c00c0c510b050b03048030080b2801c1500910103510204c40b9216034100c28880301140300c0c0800c00d940c000701d107030641e020140c2e0389101141c2c0300e1208005225070b50140c82003440200d03108115a08190301d5500d0a0030300d0440a02c2c510215000042e42c503a03401034100c044107440000c541e07a524140e440a4000d011102003080c06000000e2003803400030002480a1192494101c0004040d2a150040c0c0b0118610309004001a40711a860108480d204620000355809000c40c3c412218a050045040c811161000980c09644400b82503d182c0000c42e50610881d803071030241e0f640c040e81c0340102d6000d101144028458084c5004c2c2c4406d0002c060041c50083d00d044848468180e90362094907040d102d52502031000c14040e529414040c6408aa0382e101c050058071a211001d1500a804045901076 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 743793785 1250 743792535 743792557
    0x1f1d0709090518010f0209060304170f030a02070506010b03091b03071206060f0905060d11010512041a06010516060911060309061f030f110f040e0703061a010f0f02030708 75
    0x5000f00328011100340551740680340c0400085140c03c4445011030031520005102034444260075401500d80d060341d42c211291080c070343c80125100c0c140014180040d50200000340ca851242c00004030300ca80c410310440340108521320082061001182e1010004d002915401c0e5050045000000e50641441c10104601e4401c00c000a41c0500344200e481c801d1000350441c0c407690f450308081004940307400781c0d00000c2da0340090020042001401c012140c074840c0d803c0c90a005407046050204118070b10040c040e041c1c1c04d107130008505648a000441c2d43c0e020f200041070001c101c042040340031440960103500c0341400748141d003500070703040004140141c0c800c1e00c0c07002d234aa12031001c015141ea00c1d800782c030a0b2144401d0000d041c0910310303102d41000e07021410002c1c003460640024100c03155220b1184851465002d401403010b020340d40c2c0300b1900d40d141840180c0f5400c2c00d1045d80c04040c80203090000c0700c202c058540d40c41080c4074507004c4610409840d10300c400e5200070400400802c00c0000584003144803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 743795035 1250 743793785 743793811
    0x30b06040605040f0e0601080d201204030809090a090206033d170c093108040501020c040b060315011205161407050d0e0612010e1f1d07090905 63
    0x142c4945c10300d0110140d10858103074226045150751903520542030620500243c2c50403248024420146042800340300c8a50380c0300da1300080000410050201400800c0011243ca0425640f02074224007920b11008000790301c1081013002581148082545115078407030304206160040d0441c03840d004901d102030560454000503601088402500b850f91000003040c1c10140a0050110700030a01712240a0a6900b0200005030030a407401c044005803009014880103071440c2d091981041c0c003090b0f21a01440e40140204e203114540d0342882c0c01500637182024001519540d40d400313858440402140c240e50401007652220304910071a8050305014800c41d002c800c032140701c5010094400c20b003122403444c408109200300004201c001c2030381480f04c4a10b040c0a4008000d19000503103a10404140c1406480000c0021416000d1062940d210310500c01010701c01c0000e5404c4100040500c2c0300c1c000d000741c108030080b118040301d103440c40d0b0448030504042540c2503c4001010a80301d0450b58980000c00c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 743796285 1250 743795035 743795051
    0x1c1b08090f060a1202030604111215150711190914070c02090406200f04080c1c1b03060f0515010e030a0f02060c06010f09150609030b06040605040f 65
    0x80c094524088010085441d5850a001914084d01c0d0481c6003056400032030b03000c0000f401c41c0d00e480e0441e1808035640071515036281d4080b180d5000f0315005507551040b441c1001c1241d505400c00c4a160011228091140d50a0110a075941889210240c01241e00110010915030040710039040e104050220340720003052403110300444415190340248074500300014904d405001d40ca40808590b040f9402a40115509030040c94010700c00707001440c0221028000030f10030004030302c148050429102d0300c00c203a816126001c0e041210b05600482c1140720102d5440c0c0c00c100248550746a400d40051900c41e104150b540c2e516030030121543c00e03280007107803912001080001c1c80441102c18101809081191214801001090781c0e0180c1c4400248103a181010a00c2956202d8041d508080c4134a402c85000d90b864011000b02e082c02881810f1302c85040c21840307458403c107800d90600780c510980e80c81504514607150645142d030042c00701034105565010201b0a030700d45000d150340c0744001c1e80c00400d18103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 743797535 1250 743796285 743796289
    0xb042d200a0f0801030f1b05030f0f010605192105010c030606030c1404060c030302091f0908060405030f03040f0c0e1e090d0e010504090e07030605070206091c1b0809 73
    0x40d952401d90412610314014000a0070b901c4c06c01000c2e6800051141c0d004249240799144c080842d0010f942c944140d0040c490007100015091102020700c10003440f0340355880040c458400d2188918100440002d00306201ea80c01d0048890740d8081d454561080041c000d4444608544d800595000040d40701e24040c03190726014081d03d81b8201592402c0710340000c103a44e6401490003036001d07480401c0917161110040c548aa010340394500c800401ea410340c5182849039001d444100b4076443c000c10880c5200040500c00405d070203100c0d07500807002d1841c040031045044010b0b800103000b1520f40e221070403490041402006080058030148561a1680c10248099108500014071414210120104020035440c0220b4410900300ca5400c1030511014500c005030340f98007844d04225002d91a01040c201000c20010382001124050307082000143c4903540101d0720742900721404d102d103038041e10803940c180300500c2a00d00804043e1411840180c0507030700b0750a034845030500c1520740c2c11010544002c14 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 743798785 1250 743797535 743797547
    0xb04022421070819050624090108010e0c1623010b0922020409020109030f0302030418060806160201200910030b1c0614190b042d200a 59
    0x8106050004084c40e2010b103200503042c4a60400318421307110380118070b003500d0f035030200c0d142c104c800c20b10183c490312080b0851506421440750741d400035118400010300c601c50b45403064024031280c00400d10384040c400f0f0b41d900042c1300020888003503c20010550811f0980c4c225048609000d0001148100740c900400800032000b4080140c0928070101c80d9580d006607402500c078566050300c1c0130450010074001039410b40620382c0054600390130401c0340c004040d4080020320507110720b1032110f02c50b810340896000440306a40100d14141e40004007048150429510003441c04865100218021403d000c4190840f0101000c60203480d1002c1007084a52910140000c407840c0d485c54108003c050380030000f040c401101400220044030480f04500b448031541103600012003007492910070b42031526180c10b906140c21032607074500c0d18001a02c001450280940f25007840c0001c003a00001d1200c081d50007410807078400c0090700694401e003040c8145403a43d001030815500303411642e11041d42107806482 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 743800035 1250 743798785 743798791
    0x60c0a0201170603100b030a05010603030f090b030402090a05091c110f0607020303060d110d030909050a0501050f01030b03010f1406030f030f041a210603190b04022421 74
    0x440c0b2090742003010a490000b052400800182400300e0b81c101030b10003090520300c0424000d0300c9542002804001e0540081e03901c0c068803096942c01c0c0c103083d0b031004c90208502090714025031208105c80418900e01c0303aa003003950010035400aa44490035001c3e0410741401002d4060303004201a804418a900c0d4207004080610200c0d8015200c0303450030700d0000f074681c4000ad019911405400241e081800071a400c0f0728000c48019003d00b070401010304001d00f91082d280324080040d400d000001c6c0140c030440c09142e04940c4081c1007943c541c980b010064010b80203400784940c042d980d50240016248150185203110080408000a141003030000e1504000c40da1001c028180d204018101e20b81c00c445040724215000700c0c00107505a06e24420490041c452416101c0c20340a80171100000302c081c038003800d4003c001c114120743d00a1601e507003001012034403140181c010301c250170000c0d002d0b080841c00c5030b03051149c0340884c51460300004264100340d0090030381d07010740c40d007016403404440c6012140990 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 743801285 1250 743800035 743800067
    0x11102904021810020f03131401030b0307052b0f02040e1501140619210606080a02030901090f050f1e0303131b031109060f0a03080c0c060c0a0201 64
    0x11800300c0c502d00e141c1c80311034261111805282d0a00f00b004080e4402e004074518a2018000d80e41d5491408a070b90500b0540c0303000c2d00f00f036040e00c125640b03000c0d0b010b44144686200090050905185407030700704104a140f92035003c8480e0704040240883e913104401c40054140300342c4085040e40a2401400b0481d05050202c410590150500c4040d80105c41015030455400121580b14100407501041c294020700c01990880d9028001c1610100d42105180346260051000b40a06040c1404c0102c1030300e0040c8504404924813402085c40c0c401e0540045502040681c0082509111566040007580c100c0c0e41c03e41c2c1b1504070f001da05038000c03030078825000c0150040001810001c081e0200d83e07180e101c0942204a0703040b802c181d48080203903244600701c045004448182040d9641d0824404040a491200c0c2c070604640c00010032601c0e06480e005030703d81002e414500c3d00c90840ea50b14542d64841c10300c601051041404945182d41c4000c014840c080340b01c00a4030b80100644000742038610903500040e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 743802535 1250 743801285 743801287
    0x80115050a030b31140c090709050105031302090c0a080a1a09060d0204061202120d141303050a03050706570c03090f151110290402 58
    0x200e0f160f0b0504a81040d400e5218020158038a0010449808014450203200020f04e05100521003001590001c100f800010b44605001002c204155850102d4501001c01c2c02c105d401e20107948680040c5032300081c1c0300c0c1fa41500b02166000a045140201d400040183d0001030980c0a143e0150400d13401c5407080340305000150143c1180b0402268122441d07000f01c40c110005022950b517131382110311450b000360007003001c1602e640e0794041c05280070401f81e0052401d8a40302030b00c0d0100290f20008002207a03074000d00c0e056255038500865200b120080317408c0501c09000b0001c00e0003480038100d04c07032090b1a247d031b03909520700e002030558041050030303001203100b049010300d00780c60041200022420100c06034007a80380480b003039641000f680c42895011254040c000b03003031030b00980d44001c041d001340c4440307202a0340c490256a681c051b900542d00061001440700c00341602418504c0712984c0650702b03880080c041c480240c0c0841e910080c0031f15804524281c10510b103e60b04a00b0412079006840035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 743803785 1250 743802535 743802539
    0xc030c05030f0a1812060203070e040c050309011a0a06080601140a02010539030604181505101d0403091503060923010b0c01061211010306050d0201020604110a0f080115050a 76
    0x3240300030b45d03410b400303491107400000003440c02c2d2151618004035540140300b0004580d44440041c0641c204990303411666182003500034211030450000072a800004000304211410540d044a04a1010b0f080c41d040c0549420b6540e1003901410240c104441950300004040ca41114610140c0c0c104481c5049280561341e5211001400c001c22051420319452403680d0701c0d00c2c1c002c04075004051a40700303031360041288031449041012000f1807460072007050b0014003164692030404407141802e881a80c12a285000c1510004101ea01e200d552190081c1060801d0f03581d00c40044030300c0402c0c42080c0000a555070303400e1010251a03c648003500c00210307016807601141c421807021400044c0a690031034580441d0042b64180250031400103402c0d43c00c218000c0c0903152400949569030307a496540413a00b003d4010800f400c1c424018528030346c05a00a02c81a00c45464003d0140d40c41d284594200c100c40c070020424209903800c1d00d0003071030407000028041d041c103222101c0480c45604200e11440007600d003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 743805035 1250 743803785 743803799
    0x7050a1505070516050309030307050c04050a06081009031e0818010b030a1b0527010e04120f030e070b072a0b03090123040209070f09060c030c05030f0a18 68
    0x82d12101d54009084040150b59424254510b001f1203d9490303240c0305c0041e5400400c40042001030b81c071402904c0c248231507103940e1410803c0d500b00340104800d5034003840000b20000c0c45074200c00fa1050180c28071006031401c080128054560f144c1d0040f021400220134004540c1d01d0048444076100e041c0001c1140b000030381c0000e81c0740d0242c01c03000341c08413180842c1d00c070343e0711000c10141d0002c00006000b01030101c0c040b43e01c400c09c4401003920ba00b25030110307800018a1480700480511440c1d112070f100806d144a000103581300c000880154040544d1031201c1c080449081108901401483d21070b10b4661641d032800e96013070100208031120304910400c0c000010840d103040b00b420b07159024100d503142d079100c8100a0040808004c42119181d0030303000b001d00650302087c00c50090780280c1e244040b0740d881c0041610f4405961500300300207084203034108100362140c61250004c0d40310380760500a081c2552601031550b0013035400c40440c140c0c00101c1c010030503007085e000011100818220310406281c40c0d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 743806285 1250 743805035 743805037
    0x1030b0a0612060803040f052b021302090312030a2009040c1205011401030c021902060307020f010e031b0a0c18020c010207050d0f0302090a1a0f07050a15050705 71
    0x1c034490500141d400d102815107040d400290141c8840001c40ea2115951070b11800e06c2e1032030b803081c1d90140302c4511180c946502d400c0079800c455803640ca11842c4911850b800e00940c00311070805680196428040384803d950140003071958018a8a5081d8890078458040011910841d940c501c5010300c1c00382e111180e0003540240c85030b9010880c0e00090340c884070754054425082401d4003082c603e1a2000200355a941d680d00051a810280c0c1d013044052141c2c142070340d6851032103840c00071003080c0c105c507500186480d00c001c641c46151317441500c9840070300264075420740d40c01102c5481903410108aa52458030310a86075025090500024040e0002c0e589510303025074024042c0d00c501400e401c0d6907460400d103580490700110300c038200856a54404c0e05041d925808a609001c3c0003415000c0a0840d29200e4001c0c0c0320110b00091808050364a41151400d00018401206880b00c40034480f440303504c4000300143c65418040c0c009442a5041e62406091080c82c0030042200203140a0910080c10750141c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 743807535 1250 743806285 743806289
    0x111305131a0f030106030506040305040602150c07060906020f0a050408010c02210c0a0807080a320310050402120106020106050105120a050601020a0203062412060417090405131101030b0a 82
    0x650b201d190b00d282c00010a001d00f40b1500050958814642030004060b40440100b04a035090f40c2658001e411081c8000358108003510741400c00c00c014005080480d409038003454030756105074801032804a13014810000f81d0401c00091021940c00700d8200402d100038050002c1c8006107102919640024015841c00400011000700c5000004076030545411400c2004101d001e030442c2d00c40303480741a81d241c00d428607481000024001803556500064203014034a2000340c06980241c0c00f128100d1800c031200f00781d00002c02c80c101c40316003148002469240d600c002c009580004071606002d604005000c1d095441c25030050741080310400007100e541040e201003517048940031401041032744440c00100e141c80305441c0044d5050145509000314100d105e401c1ca921002141040a4011181d0040101e0402c46201202551b005113000400040315207a501180b960806c19840c2000c50200114040715400c884254900c48440308030070900c034034009e488850300003d103001d010118010f404910061418 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 743808785 1250 743807535 743807539
    0xb070e180417071a0f060f0f030c01030c050906040801230705070213020d05270c1018170c011403040c030b07140304060c080106090b180103111305131a 67
    0x11403240b007005a840c41c0d044007008007108450190402d107450442d917850a0310013502c9200b40210000217414002d0021020031402000360061099200055020b010803071101da04000d810040100b06644000280c00a0640c1c0c400002d0001c3c3e4002444c001a100400c0000c2a1a422020803080d039034030034222401981e05841d4503a004c5c0404072041c019000d180150b403140d5040c903080001895201da04500503000b40c25211540968102c401610f904d0042e24068200741450a104406802a1042c3e00303460704840039400259584c3d0346c03105114000d03440a46040e0041500400c1035a0f114020310324210a10082510350708090362001d511183d10b1200400540418000400041c013843d04401c4441218410540d01e00d41881c00200400805e1100d40106140b0400426118032422042082c1c0360108000392410428113060044192081d066504040c0c0314a00030100c420354a000d0400d80d903141660050303040c00d103410004100600640e04545600d02850010fa601030802904910002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 743810035 1250 743808785 743808787
    0x302011104141e130905010f06031a060d2307060e0d0b0402040221091005160c080409090503090102010f020f0412020d02040e100e0316080a0c0b070e180417 69
    0x507940c0c00742e0964004101c151300114004c2d0381100d00c00150401c3c00c03800c1c8190003c0081803040b580ca442151190301000e0000301e50241c00e00211504101070b02d4100c0e00040060449031341070b983e60a4413000c00310f031102c1c01558003010020003039400c0100c0c00180800342448010b2190100c0400c00440001c1d9015082d5100c0c840880e00355280c1c0d40c1141e82c0f501405042c40e10640e203074032146158100c295031307032181d51080320f04a81c1c01703a1840c4101800346803000102c94a00b0101141158041100c020680740800d08000020f1944854415911820b01c524040d40d1503514180000e400c58284908098400d07004018036083c022070385085800b901d9903082266210041400030510f8104a0000250054a0503e05440d81c040024070001c40345d04040b030511811480ca03e280f92207008070366454400554080c0d0301030006084101030302480e0214549801c01100d01c1c0c44001c4082020384278100810280000008070f410041c06030244024107039408115814035585650440600854110110b00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 743811285 1250 743810035 743810059
    0x1009090f1a0610031d070f06020f010506010c08030a0204081c02160501091e18051b040806070305071e0e030c1807050c070b0d061412060109051f0b0304030201110414 73
    0x4420301ca05840050410840301c070141c03581c0c81f6040c5e00e8242c0c041d00300544138840c1b07500c2c01e040701402090310034041a074820100c030015580707180064101811403210b9640900002c110b03510304001074114200110100d6011082c40d80f406806c1c0382c070030240d1800c8650380181c280000e0342c000810780202c621200c08880c565030080958466011550090304911400c040c051040f0041c031f400450141c0d40f039a181c603007184c0000c20440c80354031443c441e49034550001d10000d4401c90080e0302c2107034401d4403810000612507030b03121412000ea00e40066400412403c180c440e240303050420007241419001e4034940c240c00740382c414440305860005d100d142041800031f00c00800b41001d02010380105004404640c40b2440c0403210b2001c0d20041c00741d082c40005841400d2030b01c2c90711150984d0a00456806401264201b0520b00081c3c00002c10122140c140f2b152100d00d0043c86010440c001c1c098040b9154480c00c05103002825240030011402000109102c2440403061424020805440c00c0b06c511284038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 743812535 1250 743811285 743811311
    0x140109032111032a03071b06110c0a0b0c071109070c081c05070c03080403030b0f030f03030117032b09080a03021306110a02091009090f1a061003 64
    0x4920ba050141c1c280d008001d00102c9040c41c46030075002448080302c8010011304000820450104617469800a01e01c05d04d112000d1000280e00c100040c0a502d0204045051844074030a640c00440c0180345640804402014401081da0302c1c0c0d00a1030f0b140b00075107404025120070f10300c0e600c0c41106622580e04078020500031405a240030205550003580d9030f40f910000384164030103005400490702d04504120002e40400e2192a18003105545034464000903110b54604800805040300225080322a0300c1c46405140d50800c00481219161001980d4a6040496422903414000350038034040e4000d201d60140b8070b20410541408078100c01006a04031010005003000c0c09546038040c04c070000010740c2041c50781e8143c0013400703102001d4000402e210365400040324000160078120000c0d4100003511001440d0102889400620305030b02e486440f0f440701d02450403650305440441c0c03100e00207076804081204038011041c0859a420742001607140000c003040690340e0710800e04040540e1114107000c86 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 743813785 1250 743812535 743812541
    0x501140d1d010905030714070f030602090f041b02100605060a11030d05040c0503060906070203090f060c030310030c0e0403050403020409050319020c03010608030301050616032105041401090321 85
    0x107003204a00074000d44a103420b01179240c1c1d00c489010b440ba078101c0d909400c441500040d20404503840d05d0101c81d0101c0c42d503103c4c10300940046002c207601c24083c40321102c5980d0344e0f000344540301c800040b81102081e842d000182c80c1610b0007000c180541c0c1060001c010691b90f44054450011712070809000d408282156030342140320342c0c5c14402000f440e00c4144070500910729418415164140c00716104d07500c882c03600301d665000840360000164010000301b2440d080a40e071609140078050482030402c41000569400d640040f1844620354400350400c1090103003800d4042d0050404001d0040d00d8107198030000c0681c0714600000e4001c07a140e101103000c000041085900c850385401c034441d4480e000c80c50080d2100101300e4668405c0d0f0800e40c001c1000e52010044904880c001846a454145d4070501c0281c1e141c0800020340600c89400c2d00c8241074128103005603644491000001050710701440c028130411085064040f5507031501c1590070000b50000c0c0768100a980f4000c01218240e62146d1200103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 743815035 1250 743813785 743813831
    0xd051207050703151d0303090604142b080c1603180b1306020f030414131e0510060e010806010806040e030703030906060806040206030c07030905061603090501140d 72
    0x24100c035280d41070700d134440c2640000d581c22005000c405900410824044d5a4001500c40c060780f500310001103070001c3e0380304d10003680c0d0080f0141529a2101d2024003000d135180c151003000d8003030b06000e86000806d507001c51800e0380b14040018950801c0060b0164a4541c00007000081c01d0080800c0350100c1419007011880c01440303d080050b42c1c0b0080813101c100180b055116640140c03250110fa40b03154272010040d00d068905031813002c00f01d50400020007210045400902c1c8600c1c3d40e03000d4203644000071001444484e8400708000c1198200f810040704021034542c00042005150091005c1c0d5030b9010480b00c0c3c20110903e4101c04603192070740020300504245080e694244000a00e01c8201134158005030300030bd0103508100250740d41d4400b030740c0e100d8a00310f4000354809800c00014200c03440d10b202520402c1c1c001d2500081d415100c8002c07071003035880140301030002c0e02080801c4041591101d002d01c0a880b0a103010780750000000d102c00d1250082d03001c0c1c00c4040c1d80b14411920180e200030303a0801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 743816285 1250 743815035 743815043
    0x6041a09010b130905060609132306070c050c012a11032401080706020604080a0e0a0f0302040f0608060c0702010c060f02130e01030b04020d0f0b04030f09050d051207050703 76
    0x102c003ca14000c040300402108070112518080c20b00020194a420b4600314070079540d000c661046200c85036150b03800d4540510000c03800e4016401c410901c0c400c03c07c0003a00c0341e4280d4440c50184096420700c07a00d4050091541c40c108400300707036400f40c45034008403800c040b041660900c891210051038a00e4001c1c808080d1541c26125881c40c1c0b22036100c61319811a00d40b0300360007010f03505176281c5140c142c50b0183c83c003406015074000c0000c40c0000781c1c8580200540e04003840d017401c064400c54000342200e40326038881640119402c03020300c1503203014071421903110140070301008080d107842074403626084020300805401401003450b40959000c0c004148100307030300000400540c060f20058500075082503c00401042200d41c000c94030510ba1101141603d03044004080c455450303600b00401d00307002c030300c0440300ca42210032084002003042c006a030043d8406d4450480e210001d40004218203801d5001c54801d050001c01c110114901042c0f611000c45010100c940d5441d140c20910301d4140b60b540014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 743817535 1250 743816285 743816299
    0xf01090302010203070f03020708070308130501090c052817161e1d0415110d1d071809060605060a05040504140403080a05250314070206041a09010b 65
    0x80101a4107500a520400b03003a1a000c085100d1a07408804a00032404c004101070410000345011901030740e4401c0d840111890380b01c403112000c0c0c0d9a942034a0441300e08440105d04d04206006605e0060300b204400d1385a83c0440765040e840342c24208a031000da04c24409030490f4207071003220490040c000910030005840703501c1407240d0b5613404010032008041050040541c0d040c130103c1c034031202002d15803446a01f600301000d60f4440b81c407114203580f007543c01140701d19902d1000003006106074010b460b1010013008005018084020300c0e4150781003402c8d030180d2540080500b03100350110000d4000007405406800111209680b0300f1030010401e1760861344c2d0200d408a039804902c0d038040010003d07510191410b02000301d401c0c44001c82603c0c10303140100815103480000e1002c01650b400154400d14a031504642162600004468009090068000240c40f0354020072040c0090414942040542c80100f01d03500e0300d80c0b01d45089114400b150007070321111001107000b1071025041400390500c010030074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 743818785 1250 743817535 743817551
    0x1a070e031603020906010305160323090d03050603160306150f0f06031a0105030a0c21060e011a0910020c03060f040b2412100905010506031009020f040507020f01 71
    0x408400c00140c0b00882c414460040021003551080c0903240c0a90407801c042c41c1005900842603024184102b227041519030303c3c3c52106448841c3d002024010301c5580013900740118400c000501361180140b40a004e40e01c00001220401644910401103a401c042c00003003110300390380c008051036001d902c2014100c2c603001e000301d41000e00a5030b6404841d2030b40c40c00c00c140042075240c42541e00740c0f1021240814024000100000724a402c0043d0754605858811000c5c294680410081d0f02032041c201c2c031095496500b400200c040e00c0c1031502401c205a0581000003014010700e500784100c4900c03d0140c429a174414140707074000c200c526044e42000302500d00a2402c070b02c01807014030b0102c40c10b551428281c004103000008942c07566800c3c13070f00040407005021260050001c5c0080c06010101a03108150311403a08581c98410120b006115034004150f90070008101490951500e0303400c42e4080c64281804010390701c104540c12040000da030040b84c507a4a542c816810101d600b003000400f03508000d2031b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 743820035 1250 743818785 743818813
    0x2604060606021005091c201b010503010e04080f040e090c040f050603070b2d0705280b0c070b040c0f0f0305030d1d03040b040f09091a070e03 62
    0x80060380e099030700b103883c11150380142405407030080d00c0511085d0400411500352202d1501c9a01e611201410300031040d1030a50a41458078402c608264202c2d00501e01d09610400d20a4104029282c01d1911600315411700c00f60713034041a40030340010305c2010009a0490741d141410203540041280f482d11841600e46884e2007500c401e003180850348680e181c000807841000e5144510f13402050082c0041050505145480f0040e60040c482601001c00c1e200c04003a0607100804d401c0015501103440c04d44451061416038548010507081e10340d0140c2d907001c510070f8000b8000000d50345130780080520301d15071511124044544203a100141000d00c1c0203081000740880c82e00b5060032900c901d085401142e654542d207100c00c040d18000184585c01c02c000304414019141c000c80c5020b0214010911228680f110035031a40d84107500c4038449000100301041a80e0042031724800a03c1040428083d602c915030750b075032002034550703505c03440b40c414200420750306072240501c000004005000c64502c1e20946030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 743821285 1250 743820035 743820041
    0x6040c0303030609020f0702100302191205100e2d1510030618020721020a1101020c10030c02010f020d02070212300d05010e06030d030e030a260406 65
    0x80c1c0100342006800549031055100b15250501d22103503d50804949500b0400c00e10740d07013070004040640030300c0100c140c1c1140101002e0094480e8803074140c1c0928104907101500e200411521310b415950f84200160512081a107a0080c80101421408083c0c2c5e00213408400c0c01000e5001d02c2000342d0304100d1000e100442141c1d000c40200c8034841e21084c0c000048003a40c0b1103020f101100201d104600102440e65005402d62a2160b59404c400c0c596210350440541c440403800790050b8010001c48003030203650b140191a944082c4080c002d160039000102752054030101540b0b04156517010580e908510070b42c000d030301d4890260010b40d40c441d204000307240a90040441a48aa40030f0b0928010420000403d60009400b2002c04c02641c034610b1204944800303081d40045500c00c2c2080440451030440c851280640340304402d5440707500340103090501e8140e5440140007810310f0190641d50f010800420340b050b032035291070054401024040142e001c00c070340351000300100c1c2d8000140310420aa5130 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 743822535 1250 743821285 743821289
    0x10540061706010803040501030e01020c0609030a0f030902060403300e040e07120807030c0b0f0a05011d01210609060504260715020c06160f1d0405060d0506040c 71
    0x260020030007500500308507445680070311800c1d80d03d500c10001006554000c0d0000100c440b0244001411301100884450420008443c680034542001804043d4141c210354079040481d402e1070100708415440d4040b0f4018495400080e046141c1e042e5503440000100340c1000090218400c0364407441d00030314000e014010400032a81c4900d080420010000702d00095010407a82c00318072248544d095a10b4200d540d910511f000ea08100b907140c507640124190b0300f00107000390340314108000c2c0c5142004500b8110391042e000485900a0b079075810500511101405042d19038130a0080f034810315250040c0c800e40200d950003040d99003029062030034089550700c003511650040900e5407600101c0c2120f5000750112030170440e10502c09120b25004107560703194401c0c00154040b8014545400c102c121840d0002c01c54045281300300c01076038035149542c40303a072400004c20795041c000724401043d512110002405100c49004a0b0368600281803540c441c6141c5036070a412a007034541c5401d050500c000c2000b00740c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 743823785 1250 743822535 743822549
    0x12080d021b0a05071d01030f060b150c120301062705150717070302030409020d140c1e0f22030f0c06110309180a0b040501090605150301054006 63
    0x20410019420303200c0c13900040c03d0354940059805c140e0031507691000c0842d00340000c0d40d00c3d503901c0040e00e00d582ca401d90345200b40c2541c03860300354440d004014110304c0c3c548526a03506014800744010090f40d904000d080141003410300a5510a0103a924642d2201d4507070f038003039548000e01d05281e0110b018050000c4c000d25000d444503059441c10511710341e22070300c110240180160304c03c002c10005501240d001c2c0403c084102c1b004619100c1e25140c3c140c070410191000d0b5800580010000501000807541c0d04101d484d188c111030411030b060610720074902032200d04401505107503840f0341e0040484501e0070040e681c0420f0700c50325540d90341400c42c1c98110900418001c84d201c001516007890001080c1d035000d0784014150030182260400d1f2181002001d401d00b28040d0301c034204801a0340c0c450160324040c04580a0009400d460201001044980c1070110303448130004000600a07a00e514032400250401c000403c82254286c5150207201810300680d25010500140c51440030000c40d0041c10031513082d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 743825035 1250 743823785 743823793
    0x16170c03030a0f1706010801052701090b2403061e040e03031e0108120f091002061f0320130e1e0f07170a152412080d021b0a05 56
    0x4130800c01c40c220744180c44207800b080003440100301ca803620b0b0928007500c104001c54440c41074a0b02c440e144c601c1800782c0221070f24580340c9009400740c1c1042d0b001c00c036840c03080b40a41d4446038000e1448514030b100181023240140700b01d40e002034484c0c00c54850040a400003a0041013080003020100d51260403c0e100c500c180700e1049040705051040c198114140c0741000f0281a2244500136042c0107035004001c130421006050064035078a81c0d9480c2c40d2410755100b23401810032460245107600203090124030169007011510030a002240d49078840107456156049082d009220040000300400102d11010204074141f09202c612000c02207080d1211b0411080d400040f0171007412a26155078180c1c04a10295000d80b00400a482001e28400075402d10030041d2900000300d6243d00e521100e8180400b100151604245000d1421520444003d19244100044941d04040407015121103d1402504113100881c2111102c49030394104d80106224250786c8a00d0940107000d03d8030b07008001c2080d2542d0103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 743826285 1250 743825035 743825057
    0xe0a08070209070c03050f072a06020609010c021b010212030c040501080a0209030c09180a0317060604120b04021c120f0f1b06060b0a0c0606060216170c03030a0f 71
    0x8018980c40402543c56101c0c0b50030250b582207201000d40000c00b00b130700c482c118034071010720480040401c00450049d1a80c41840207080c90303c0a45040d03405409900711760716041301e00e14155404076004d00541c166880700da101405420041b481d180e42c0203100c030080c4000106100c41c188030750b4020f0085801c01c2c0c03603246185c0c3e9102d80d2030049004201585415400c9030042d800103203490f000782c9038400c1a40d0000340401082c40c000703602e800380b03e2800b14089504840e68900b9100c4140d56603074080c500722801840c1c03a081000103030910b011668000c1a6101038400700d011991002c0800030442c2d05026000c040010368100350400c500504518404030317002c0303200002120700c2104021a500401e41311007441401d0f40d802156480f20080d400d59040c0d0740e5520204d001e040f00c0d0018078281c44940c1e11446005e4070b9040200883c5c0b076a5201030155401620314008060364070b4069800c4030501c00f0b004404c00741a140160030807800d080b000da414000024000c8500f90401c40440c01c68005944410f80f140c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 743827535 1250 743826285 743826287
    0x10602070f08120d020d0f1d0705090403140a0309050d0807080a050108061909060c031401060207030512071e060f06050904320f0607032318010e0a0807020907 70
    0x10070030031103404042010448450001c004c1d400506520482c50400960180b415007142c08a50040301101304107d09400540503460b000c10940c00544811605084241029174000d08030000541d4903450480020440180e643d02a5001c0420030350050290f60030709034501c4005201c0e00e0100d80220108900c01b01007400008180b042c0c0d41070340c3c030110082ca516104c040071080c041401100c4103c01c5500e40014100080b83e6003d040c0d03600d035860300d0208120301c00785000010120141c108504550183c50704001148000031400344400d0b0080c0003a41d0399450b8202180d008200000f40081c0c606030081c0c4008000099000110320b4581100400c8003540740c07410000451000c0ea03000c0d00c60210b800c0f00007500c0401a60303030200d41003a04040c030284540070b49036509081000744d50b400607410020070000216010f0099409500d0031440c916001e107201400202844800382040c50924203a070124002034400350300c04103480001c0000c54480301c0c0e02e40f405110940c48940d04134040c41012010411407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 743828785 1250 743827535 743827543
    0x152404060f0f0c02030d0e0a1a070203010b015901080604090804030b070513030c090b01110a030806190e0105150405091306020d020309061512070329010602070f08 72
    0x40f5900030b0140c4031600f920142101e862054501c4603500410005000442e107030144540c080e5200c850700e4a58888082d0b004142c2142e0b842c400c428144141e000b4040c0500054160fa00880d80d480690150b409801c105808031401080d00b0f40a01c60080710080c41d20003040e0706806000c88001d9070340301c516607115410700c402e03640a244010100d000500c41440050a01b0300c50302d60064180c5440c42c01d1040e174802c283d4003149907900a5410003d018030920005990f030144400801080c02d1802c0301c03651080103d80d940d41e03030b41409400c101c03004011580c20741e80c4698515002c52400100260f06480300b142c0f000d580300038426544102d0074103044109100c4a8400c3e1030480c0c50007044080d060f91107502c800d030400d91000c01210010342c00c1081c088951701c144061402179401d45c00800161608401d0622081d01c010100c500c601300341000c89085001c006810000e40340d10414039220051100a20b4100b94841c0d00292004500300001083c0ba40d40015058112105081484112507440c50b035681c607 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 743830035 1250 743828785 743828807
    0xb04080c120c0d050309010b0402160303150f14010c06050732030106080a0b04020d05220b0c070212060414120a1b050f1005061206152404060f0f 64
    0x903000f00f00a01030341c0303018401039a40800380e00c1c00402c0c0442010000340c126841213941500100d8040c00c2002410303418414501c1e001c4031000100021400d1013103034910f104c028410b1b2403c10910045510f01c5074450940c0c0070020f54000b0060010f8200100042d158030040044142d200158401c605540ba0000340180100d050581d105440c60342004000c82c1ea00d40010302c1210081e8803584e1104035600d45100400f0118030640d000650340c01c01c1080c611200e034030341d0700c2d00200382d091384604008110040089074125035001c03001a5505d40390b1000c594005196990301e42640919010803003849141c60000d100c00c4100c200391185981e80c14003071545400340c0e4000d40300199080e444a4210818590001d2202c0c0c02401100c0780400903c840620300050b10106a88171503d500502039542402d0030f04074400006400581641c1c40c00d4410844541041c80301180b06064156448a005d0300340428204140307204001c06aa940d19400e010b01255013910007900080e40720f0700c141c0d4089d4818862031130 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 743831285 1250 743830035 743830057
    0x120711030a02131e0b0a0302090c041703090901140109052110060e06120a030e010522170c0319021c080307020c04110306040f0b030f24040c1505070b04080c12 70
    0x21b5114199002c0c45050030b00101516018a410840426030442c0c2c07903590460102c0c1d9000544d500d00101040c41101d035010303072062810980300e01c0c9280b610303a040018130054030701c10703969409a4080c040d40c0c2e5804005040200d00c003409204540684482160400c40c1034070700e0800c0d46e4550b81c580d5001e10015048890300d0b028184c00000d044000644a0801c2c0c1482d5881407601c40d0801092240380fa00d1703a98188110200596040f800300121741c1c544511840b003074841405016660159000719807240c0d1200c06d0201a829014442d900310354a20540d095003889c600c0900c1c44d00c040b646807840c5a5807080d10040050b10420500320700b04c7c40d06015803405041d182c001903003907445850602014080c81c440c0140d04940381c10350984151010003c003601d0b00b00400041c000180f407207022440c0002066000b0211110000410001ca003013401c0110480d082d0a5203c8000f441d1402c1c2140c0c40e0190010081c03640c0741c1038080c40306002e5020080d1a81c90341503001e0300d64400784d08050f513044e07108040b0580 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 743832535 1250 743831285 743831299
    0x90f0b0111030d020304020607020603070815150406050903030c010c0503102909130509070905090c010c0201110f031204111f0c0f050f1e120711030a02131e0b 70
    0x1503c80c585801554101e44080e111070b051181590001c0c8294000700c4000c0001010320040111044034400301418641c000c0c0d94003904000c01c5c50300c007140e40c8180d01642d014080b000618503800d482c2081101c0d240c05030b00008021011096200a0040e8400e454500c0003c1c0c880c0c802158000060356041900303a00010711803506141040401e081c2e41102c00020742c40b1154102c94032000f041070044a00c40c00c070301e6015043c46420b207021074040b101c0181031049668070026642142d40d81040211060750780900b8003200a4a039540d05607d05001c11240e00414040441c0f81d000d8a07420010030780c0a0f6100703044010403040d00e01e00b13011803a880c0e240400c1103881c1241c8044500b90003400303400c0300300d400b8000004104000d42c450600e01910200e0b00d1000c0e90081d406050000c055200d5812541c07001c0380a082220380d16100a02240203211003e04142010f040c02e0040717581c01c125181160354050405103020718a91102d0004082c0104444a403401d005903410000d501c1d44100384845400402d24 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 743833785 1250 743832535 743832547
    0x120804032a1406030a050a0f0e0d02010c03090f0314070813031406040b01050103202703060114090a02090405040f0201080c090603010e04050312150102012003040308060f0a090f0b011103 82
    0x701003d806c01905140d01c040e91407500c0d0010a1480c0908a4101603000c000d040360300c202e800003070858010b4440c00f8101031030003800d00002420452003c07585a090310b04280c0c440100b05504800b0b00c0303445c100402c0c81c42d0018800740c0350842c2020040489004850040490850118603500c6802c2158014408614180140b11560080d4090400d90b06021114000c0922421800c0000d902c44101e880d580c2012036400703000f02c0e02c0100e201442d460309402400c2c4552404040044104800d0b0b903c42c031814081c80014840d02203039041d20810719004106210906103810711074505102c4280503400500031a00080b28003443d0400c8035a01c0d44c0161403507103544c0c43c040212203e010040e00c21103150008008544545001e40307d218001c102c0c25001103a03502030500007a084408903410712403000d000007240000b000300d01096075405600340c108640d180c0e07a96800107400040c2451615400406540040783c095542d601844520005280401c0116a4030740195900e00403c1222152503000b0820307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 743835035 1250 743833785 743833801
    0x10020703022509090501020d051003022b0c0311100f0c03030e0703170d0b09010b030c0703030e0d02033c1606110306031c0504120804032a140603 64
    0x101c582c4403940d04044100c2d40d84600340402660b03100d8000fa1066900814000c03400c102c0c038809e941d00100401d1785060b00c285542d002c505640750113000440001541c21032054100c20412070441c11640c02040442166200e01d400b000a8684601503405a80f5001d804c0309400e000e8200e07104e410040c0c1c1c4131101d1038803080e40c04901900407404904918014141c0020015890010305010310204007400c0d61110340d0807080170215880d0511240c80351004000401c1030030f01c80d2080320f42012500e050382e1366421060900742c0203403601c2ca5a8161620410042c0303910954044040d001c0c101d5059401407440071041480c0303903400c806000c10f403484582e11401d85182c100d00304c0140114100e00d00e561b0b8000340c40d44c5500c3c045420816154010040001c104074851a013406050540703050503a00d8001d207214800f00034140d014a025403a800d2080001140602420307074207480007150300910303000c10844024900b07003111000c1803002c01e2120380b002c0301113005e00003481d440c107080c07001a24160031950340e100c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 743836285 1250 743835035 743835073
    0xd0f140f0403080a020f1506010e150c061623091002071e0f0602030a080406050a09061109121207030825020a0209010506040e060f010224010303021002070302 70
    0x204000c001481000000001076a403006841c8591454020705070311410010120704102003808210000000a0104141c603a00150109003100043d140e0703d8000d4080c0144030514451500703198994803400e020032a01180142c141d003540c040c140d840c48c0e030b03410034a4880312001c2c141500482e4104000d1107075031031a0614065030103002955104480d0220781d503880b0000400107a110040c000303043d5043c14048881c00001c00c3c0001c000700d20003140340c4030304d148005088401c0a80010500e640384d00104002d002240c10050286800003002c10401c203421940854503407001802a00909400c4403414500b0b50200355400e114071a400194a001e807c0e941c00c5604010040180e140300415454956041110b0340070b2610071305441d001814003000c175004111a04005a1010340714050400050140301543d442d0306411000984105080018010061707051940404810240003a01000612451442100107040701c3c026000c4d6074014141e00c081c0d074141e2041c000c0180c0544d100c070240c10049281d082e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 743837535 1250 743836285 743836297
    0x1609150903120c0c0e0601090b0301060206060d060204050a120605060904120f1803050610050f06070f0602091206010906140a05100905060c030c0c040603020306060112020d0504140d0f14 82
    0x114060300d07102442e0f41c6004d10403005402801940030311504201213075802c80c54000c054482c0612850131907141034402552040000d0070940035008881e400d20404c00c180e010303240900001003d101655403036012202c25903000420035a544d50900001c00c2d03003410290304007405950040782a410905039400c040d1005880c0f100d8503070070010641c07940d86419944201c0700000c0d500ca500541024140558202c00750002d03a0844c80c480c0c0e082c04040102a41c0746022102d2441d441000714820750301508060b0000c2c0220354003180c204920003904081a403010070301c58181e4103590010840035480f59014070b1803100305181e080e00f10004143c103100b0352030302c100310f034030301c6c83c100d24003010704540703460210b06560054082d03140b203540003148086d14038105100c0a201d4400a40b4100320803407035900001d641d808080d154a060103e023001fa102c226031240c0444082840000d800c2c80740e0306180c904080c0000a0b05604141c1307024104040d03008920079080d5020405456030b500c121a1024501003074507030300c00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 743838785 1250 743837535 743837537
    0x21905070f05010903050903010b01020d02030301091e061d09030405090411032418061b030c130b09040524060306060c06100510020a05190c0e160915090312 69
    0x1d1440c2100260b801d01424a540e44030355100e0f501c03140114185825246562401815500300290b001010355000003501c1c111005a640815100d01303507621281c18a2070200126070080c1040400300d007045001a60003400321080e91000700c0d994400088070307128041e070300607a54800055404603002c203140303030f24620690000038161160307041c200103c04c4500052401107507004281c9410043c40403690422061140040780140c0050324002e258203005102d05094007010803c084040b03030214908405844404244c13400c898842d949419850754035030080d00c19544102d080000240c0390031041c055512441c038090046c40b5030310303102008002c040c2d000100302940054050182d050202000c000c40c40c02010b00d15000a03441d0700b02030511400c041e90400c038030150b41c020003000002850000702d0501d50311600300c08040c140720b5840c000084402c50340c0000041130000c420b10250100c0c1180c4c0b00844221500c0f050011569001c0440805040000c2d813008103aa1030810000700302c180f46000020801 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 743840035 1250 743838785 743838803
    0x181b03010f031104022b050a0b1c030e0901030507091805030909040203030f07061b0e0117040c090c0e0405011424130f03050f0a0b060d0302070f06020d1202190507 72
    0x8408001103136030701c0b2079540100c0703144c0702e44101c3c030000c00340e21803590231200c002d00a1005181d804c000c20844905d07440c54035801107000e04010181485201101c00c0d07040c7c0200841c000e07503520304000340c0da400e081c000c01809d9072903c103060104074600c40b4100308450f4044080c40c106a4802c1c01c015907064018010380c1c02d030100f003000c4182200040c0082c007105218000014404a0b1498208281d010b14103521050080710302640f10283c1e00800c0100210f81d124403503845503682c03460810800380f62075103c100f0482c00c080da8100f200c0c0d041650a00d213988150340820940c1e0381c40c41130f821041040003e01c1e41104004034580b41055155800319031054280234154580194580d88a07001c80c0c04e035016020311241d000044c010810288103810344503042d10024158481a42c44101403c24050b00f120700c00d50400080408160080c041c000003030012001d4069119582d10000c1c2d22000e4038901c68000801100511030610b2483c42a41c807a10158040210410080201603a450340005401c0c1c0350000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 743841285 1250 743840035 743840047
    0x5060711061614011104050d111903030e010c020639060402090f15100314010f0609121509030c060204080a0c090e0a02091005181b03010f03110402 65
    0x58010040034007042d5901031880c0011142420128081c04146070070050741424110102030442400b6070b030642c2c1049070121100714803481c10004a65106103601d400941074008401d9000900095070100d03030007030f19240001d1030204011620b080600c1d800a51000052010480007105042d080081e062200d0300701c41a400c054680501390f5070003006039551540302d44204000c40c1404a030040c0c00110726520041103060082b01c00314101c9100500e10301601482980040c1d09120b0340007841c815100c0089580caa50b100d0100750b11114540c010200420200c0c20300044001c200b030014481c490300300030020300009400c81034101230700c51030300706404001c9034a03248004100e061000b07100400042000304a42c014902c4e0190b404d000d264000104035141882c1c696524001147c0b41c0b83e90765040750302c4103031541c60300c4154a800140c1c0d0005070300514070041d680503901c0c0748035566000e41c10341c07144e882c42c1c4841181c0420b2544002d0249034410020140c00300002400c24900382002c500c01400035041c08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 743842535 1250 743841285 743841289
    0xf0b30030403060204081218010e0a1e060806010c11040506060702220f0603080d0b01090f080f061005150f041d160f091a0d1d06100f05060711 63
    0x1070030941081c0d030440d0f40050208011003040101d01c1e00f04d207800c00f080341000c2440c41c15603c014880b44c0312a041c40203410104e602c60781da012100c0082d04081c800d0000000c184090304000260501034207000c1824039000c21007640c090489603580d241d1008525150240035003e200142c600a0103043c1c1000c8188540001aa15204865580c00c001d1202c030460105450f80328041d290300710b0540c42c24a00c3c0020502c0490285030484000060200e03020034900394400040319048841d40c00755548103100c03000466501382c0855400ea03080c41017800c8032400d894078010042160024426030f64030038030800c5240086554140035000490003030b4402810300350780e40182d0034070810444040403042800350030854a1107980407d5074902c43c1e20b103088000600c800001903c0e80c1c43c64011540c0c80c018110100c80d28407900030841d4044441039009118008a40d881028030050842d134a1289004000c0020041c4000c1456407044416001c85da030a01b600e42000e00c0181c0e440302105a03180b0b000c0e204840040d07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 743843785 1250 743842535 743842537
    0xd02060c0f15060d0804061b0210120605120604200315070f1103030a0f0e030a08010501081501021b0102030c1e12160321050f06040f0b3003 62
    0x255140406008010100b4038045610380300209214418410711100c10045101c0c0d90503241980c0b8103080040301900306114000d111a80031000075440b4001d50401d0025a43c0500340c1c9500c0c004d801414018a038440040080360107e103409441c459010000280200b15040c84007845140004040c6580e00d8801021900305203882c011040318240c0c41e01840201c940c050755003020b0a01a2a0000c1029241c09403a0340380c1c4409029103121548901c582458a44598094151b40c0c7e1010304581d595803169070054580341c000d11074540841c10200005091321211803020b801c001c0168094003201c0d100c100e80c01011141601060f0440c402808082500a02080f030f0221650111410741c00c640d1140c00828582540f1000c007000d400014024070300c25428200c0455000d0b681400c06811110b25030b91080301e40401401895040c50510381808812040030b01901c0c0949803d81e014000090304981c808140c030f60b9140131135003003021a100840f1142070741030b07180c3e0114140300d0003003082404c0c4820180340d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 743845035 1250 743843785 743843803
    0x10308040501080702010e06240d110307060203041202130e01050a0525080f0c190504030606092f0d0207050c0906030d090614090406090c0305071b020d02060c 70
    0x2610002424070056800c2003003168401402d100a100000038245140c0c0c580e0f40c040c10307141740050942801800141c0c2d208410718074001c0603005900d907005a080035030350f182000356014003c0c040c0b2100400c183e40b002c4103c1e81900d007002d45019941c18103034240000003a841c1030500c140c995501071014816000e02545005502111002c5424108013100050f20700c0c4500604141c0c5074640000c1841135004950a03600800e20152041c0680c0d80858580c0c1c5031103103030005100008c032045501c04103034210303001d4403e680c0110000c0110540f1348442d002159510140b9180300c0000c15607c030b659003e00301c9003d608401500d902c0703080c0010500d60f03006903000b80504030785580141c480d0310300c50f05000002a600c02c4e0300310f004201500d80300c40d010340b4065880c0038480800c1806583c070908030f203040c4229010107001410400c00b003036440ba00034005015006000d800241030030040350311140724451044008070010300c4d40441c08402e608001500c0c03441d07101281c00420034010a84030000910020308 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 743846285 1250 743845035 743845043
    0x60e01030f060b09032a04050a0207290f0403090e2a18100905120c09040f0203300a170109050907081506010c02030a0c0b0d150b0901081b030103 64
    0xe00c90f10000c00b0107081c4008002c80000c06c5605100580c1c02c80c1ca089078540c0740701001c2d240044d030f50302e408920310040e1003041c03005003109121840e00030b480c02c96981402a60380841d90801040d455402c84031070520b9080c1d03000740001e00d191201348014100c14018940103801e9004030f980c1c51400264103482c60503803095020580f100031070010344181d0a02c0124010540071170386e0708040d07588100301421034080c0d4060140581208000e11511140030802c4a002440091003224107180a107810010310444460403400703030084e903030103001c07038003a8030244e4440076012034000a0045d210542c0c00c0441e00300c0103180040124081c100c1030401c550781c0c80c00303002c1c0400803008100361400619081c5840d50a41c404c500f142d0001800320007045846040982142d42440c3c07518103e1881d000080c50548080750142840b0b41548000074482240e40c010030701c4025480b4140801c18001006c1c0c00c440140784589071071020300300400220340d881010080c1d0b1004030a0090b181d4550307905145005034000b604111 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 743847535 1250 743846285 743846287
    0x3020f1909020301080c060c030307032c010603060b010e030a0308074b050441090106030c08040b100812071502040b2b150e0105030c010207060e01030f060b 69
    0x71080200611100308080f00581d87c46141407501c0c80e21a56038403000700014109036651840a451040d43c40745020341c5441503c1d40c50780701c0e00515485000306810300c021135035107140c049000d040354012400e9240342d4000502503c003c800e00c2d2026956148001c02c40c20401c155603544074508400c001040c103801e0143c00c500d4081340f8485112080c0743c0c807042802e0161014080000340081c0c0e02070100c4090340d800e01c1c0190b03038002d440348000f40054600c071040d0000b00c000d2140c0203040000c0b080c41c1c0c800301d40d007100c41d0091a643d03410140d08644c0c42e480c0080006040c1c1d000a4080b40400d10f101e50030200140c0122089550781c03d4150a01c036807003074200c0c0411400942c0d402030080d480780b904c5040702043c6045140514088040100344900c031440380035000c24405042c055042c00907440b003441c0b4a11420301012862150444140d4106c0c003405080001c0840086201d0a00050740c07504c1c00e2041c2c006003582810720005442c545d50000e4164100758031282c0039010210140200300c01015421034003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 743848785 1250 743847535 743847539
    0x110d0c02090c0705031c020712050d1b020309120a06050702100501062a020f0411040f0f0305030a11011104060914040c0e0d0219030c210b0103020f1909020301 70
    0x4224448080e1000114020901c08040402c5002c17040365030110100c1038040001c0850304101000c1e0241c80780180c00726080d01703404c00c41a904078004240e11800e0a0080203086100186280c5031850b9015060059009221a0ba5203040207501c002ca00014502190202050b03540c841c025036204489000060f0000d0030406081002c600030319000d4081ca00b0210114085100d030004508404510300340018420022407055440320f020451340c204000c1c01c20701182c24201c0c100815070b8000d110b091000d0310341f0640051103d000c1c09a00303007529403000203549400900002103c0070020012840d50555175164810044003841e03000344010103903900c4030405070b03103403181030010400200d010034091801e05d0808540703154801581c08455000302d9102c1500e61480c0003140290504c41d000000d501a500c0c0040144206140360004588401034190310007120780e4480807a5280305c507401400820000300500051504008007480c01c0c1d0003504c0300310f003a044141c0c81c40d4401069484038258035400001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 743850035 1250 743848785 743848789
    0x20901050409050412140405010c03050a0c050105161107030b010902070534060f0f11030c0703060e0d0c0c0b180402030a060e090c06041403010e1606120e0d0f110d0c02 74
    0x851b0f41a40103800d1014103043c500000a00254803108005042110000d003841c0d9441c0101c0611010580203c020490b52911121414100d80304182c0403003c03801c61861650341940024400080d04c4d4041d0140f0750a91811181c00c0181d00003080440d00c9008205c02c0026510f102284482d220206030b8411201104c0c1440d581c50a06464105200308114280d10040c001d030402034140420700c0c1850700c0e254240c203000c0744901358042e1202e0324595011b588000000e00c076081d0004421203281c0b02c1901d40b2428015010b942000c004280107040c1c403c0170004120a0301160064a081b44c14800ca00213445500d50006089900031560528030302d6030b4045c144412802c141d101603100b10142c00030300c030543c954000100c10f4003403445004151036040c1d0010109403020342140c140f4060341c2048500c5001402d202c240c04a21278020b800002d034000642484c8001d45014018034007281d040601610140981e013200d000075110080e10070300c6049600301c95042020416000c025881e5a10304540251601c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 743851285 1250 743850035 743850047
    0xc031703041e051e011b08040b1501021f1b0302031b090d060504020d020a0312030e0706050a0e0a2d0503030f160c08120c010f0e070504020901050409050412 69
    0xc1d0b84500b40d81c041404030005100002c11242004841c1c0d282003048a01c81c2c1c003240540402c22942038001c510102c20034486030010000da0103144101d64803500c03540c0709882e80200348000f058a80c0141d018100c10311400d140003040d400c2c60303200040c01042c94502100d40c01080408050385000003540001044001900340c00d00030385480241d00000d00d0309400e040065200307102503002070300c1e02c0e07950342c0410210f40c4c03000003c2100b0307580036111901159a0742403000b5000d251650603030219082c142c0494050c000444c0083c162803003900d401e8144001c0d62011107959080b0054990003807a41c0ba0081036550f460240d4510181c400440c0340381800b80000c2c260310030203190b40514002c1d48140141190070f101c580079a100d803014254141c8044aaa0a000400e42c050360302130703082e03409408841c000b6040703060024585800844024810b104410300c900d41104c00d00358100c061508401c0042c80300c0e1078150010309030710205140160078141c607414400200c40042c0c03401c59101010f0540c058800350044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 743852535 1250 743851285 743851313
    0x402340816031b170c0709090506040c1e030b07030f06090204050307080109020a030b060a121a070e0a0e0612150109111801050703120c020a03021c1b0c03170304 71
    0x8503a0300840003681d134402c004000d0003100105138008a540c80b46403108104030b01c0100f6004109120501407070604130b895080a68050381c8203803002070007043d41210a1943e004400c1c0340c42c058002140355071070301d80310700901400d100201510307041c4d070440f400d182d03010700c101030700c0030210041e55185040c04141c5440c0c11a48510300603410f01d100c64025954206908084070303040846d019903640d9100004054403415000384070012403002c240024002604a05201801000446845525000025600c00003001580c3c0d501590200c010300440c13012040050300000c0261160060112031000d071030405107080ca6140550000d00010403d10fa4107000f50301c1c4c4120001344052030040c0e01d03000650074100210340c0c0c2d4180030001881500f054450300c800c0643c00801101081103900200b0020f40307030617034000d06070700501c6104001c01c02203140810403440c0360115242c000c000190444400c040080150b02914244184400080418040f40e00d1000c204030100c1c0582e03482c901450b201398502206 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 743853785 1250 743852535 743852567
    0x910050111120f071b0603090c120209072f060405070f031a04020a03081603111906091103010525050a05040e151c030806040234081603 60
    0x81e00c0855500c1d030080007111840b03038801121690756046800c10090380700103003041076200701170002c001690503819070004103031520a00e1106901a6034207042400d10640701c2c2c02a41c00101000480c5125001e000d10707509040311802034107500b804d0109510440c0703100c40c5140040e40c101c0c208000030800107000001c041d03c0ca9080c41c0549504580380e54007180d0b00801c2c0078801c0003581020605558490340b0300801541d00c4421580da51284400340c3c48030f010325580442c01304041664200a50101180304500000350b00c05034401141d440e1a142d0180c020b003681a24215400c0002c08102d0310203000d0240b16400d861a6581442c0485510390620002c0d29000c0d42004014040e07158441e07030000c1241c3c111111228540d0312500d03001c585510a003803a4080726030105002d030664281042030b00c0900412806a1a081290b503076240521050b03114072200c081040e54800c1d2038007000c448441c1d40d03c0000c09004000b60301b8444560383c403c0c607a0b00103204008150021500c2404041d4800c542115031405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 743855035 1250 743853785 743853793
    0xe0901051002120a050903030f0d0b0f13090f17070506010b0405030717100c020c011805090c07050f0d1817070e0604020c03030a0b01090b120a05060f0910050111 71
    0x2403500025181e59090000340021080020149130b4184110207859005800806480d50303022031030041c0d5815441610f0010300e1700d052a030030329101c1c640100c0450702008090940040403a01c1e141e9100103044480003220104640703c0d0b0f0b40c01160703468840d882e6101d0000c03141990703039803a400c00c5032404405911000d0900400c000900407500c0c085000d80803100c1480c0411589540000150b061602018480340058540745030317051311035400580c03095120030a8842e211721b125410007480d006007890042e107800081c280301240c07041109000500c109030007a0b0583e000b0a290081c19400c0c8801100c103000000c448903101400d52402d4106000109186081402115440030107d91140340c0c07803180408035058100007507850348540e0103c07040d50602d901525500d1410f054100001c090590b00c8500040c20b00c10080b8000102600711240036140602d140000d03030b6a0484140a0100280001d412086034543c4403425190071503840d010300c18040321185030900300000100342e20304103503801d1810b0340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 743856285 1250 743855035 743855059
    0x1106040b0909071704210c230703140105090123040b15030312011505040308041413060b031b09280b120702010b0613090f09120e090105 60
    0x100501120598003055642c404079030b07030345103080e03583d290320140d8420244155002c100c1000004030009001d2405019181032500d1810011a02c41d030342c000700203003028038129802020b2170b580280902141e407468121100180c0f20b0340c803410404400c010b8403825039101c405102125500b070203044d032090a41d2030300701d001085020b50400a004090030103800c090130b4001060040b00b403105800e40442000c0c04407540c48184400d07900c042402440307a03803410f940002050281521850840701180d400582190400b414220b00600300c007580c46050354082c4184544d41e000d40418040c0c10000c0841c00202c0b500d0b41703000c1d80c051400d011a180e03a03140c0004100049580b9541d0700c010000c1d0000c100c070701c901744c00f510b251440390a404640c0200f2503c00c400302c4d268601101c00c1c0d011038030404241d4001d000c007880e00d400f4007949018402c10300a418070a1074080c0035459460744400000000d0000100303103400d190b11503190551000c4041c10008003000031082c001d0508504c8079004110580d00242181 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 743857535 1250 743856285 743856299
    0x2090d0206090a030b15090c0708070b0a02250308060108040b190e030d150b0415031a120105070314090a0b060105040306061401030f05092503060501090504110604 72
    0x1012410003445040041941c680548aa41c1030303070083c60f4844509450f41c1007080000c0d13580c92405644a128079100030020302048030400a50715030741c2c2e00c0104241446e80c142e441c058408002401030f45069070900a10390000c407680034003034594507030003915548019581801003170f10500800c40c80c144680b180510002503012007210707500049500c200da100d88980300d00c600c007034626044000741074170004c10080309a54142c1d10035a64810011400c0c0841079036048100c6080c06284102803c10b1500e21001000a02a8210050103443d10822142c40800380002a000c01010400a2441d81d5100e00300b0200f250148103281a403c020000c502c0286000450b49980700c400d0580100356a0135400031960b00d074040e200360307005035074490001c0c0010b6844504003800c060401c504240028101f5003610450307202441018010003020740541b0079032010715060140c0c03521102110500120031040040811001d20540c1c0c06020820000704003404e10341440d41c01e440340402941d200b0f80e42000308100c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 743858785 1250 743857535 743857549
    0xc1b1909020307110f2a040510090507020a05100c0e040504051006080c0303071205120901020d0b1c0b07091518060306051014070807080903010606020d02100222080a050706030209 79
    0x911120400706d0052404108141d04110400b507107140c01070300700310034002340c0614001520192620888100143e5031001c0080f81e40303082843d40909540c10006214420b0115070700909104040740c14000b07020b548070408542140c000701c60580c0e43c6c0e00141002030540c00307240a01c0d8002c0070b9403801800b039004038800080c0c0700e2068440040581801c84590040306000b041540d400328024045107001c2d250141c3c1c518043e50085000014082c50001c2040291510b1081854920001da120035002c2e48680d0310110907130005001081800401c103800125507082c1c034103a03045200c4c1030362040301201da04120601c1805460b0024810b0508001c401c3c4216110005160f0950a051a0854400c80001e40106142c8a880c4002d04540c400081040500007020300a200d251415070080100070398542d405c90f10b420b0100250b1005170829088013189000d90303005030091307451100e080300001525001151400d001940800c0743c0780c102401a405100050200b200280240c5c2000c0d8a007816140c0082c0308 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 743860035 1250 743858785 743858803
    0x504170102071709060d0b030705121c090f0312140c160f030506070c0305041206021c0605100c03020c180105011e200a0506042001050c1b1909020307110f 68
    0xd140c1e17400914800d0f58003003014400422000c0c0002440191050405807901514240000c01240e33418511882601c02c507111411034a400d907400383d0960640d690880e04181a81e0358108010103500500890001900101920403004c80140703d1b00010403001d00a4054642c007854000020000c100017144010038550381c040356618000d1b240c80c019180542c2d01340603c3c1c220301448080010f43c403040240740c1e4000e05420f945180e030300e0310700c8410001c4c070380a03134510340900394010440042c1b06030054002c40c50349003001c0c400c0c0140d80803c19090003103602d82200c0c0a2002100c0a4000108802d50b0841440f4100c0c1c58040d403151580e48018002900d0441a0114104000004c031240701c0940c0c2d0520100d4039443e0700c50705455031400d00381406050b00c1541d07030b030000c14440da840140440c2d42c001d204444442200074054210414000e010f098103400b108100ca40100c10513501c000c0c085210385c0d040c8003521706940016164149404020124041502d88000a6109015140c40d0074000229803030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 743861285 1250 743860035 743860057
    0x914102f0c030115121703070f080612100506041413020f0603102c07020a0c06021603020405060315070206070909051e0405010f0c030902030f010228050417010207170906 75
    0x1c102e00d00d2609134590342103c58014000790012041c00423440d40040001c075110440eaa441e825626010304000c510302c86000d6004140e0f0000800c00f10703100d903640082d43e001400400010f403081603640c840040d0702c0d088503420b4a081d454061501185040d042461034824155070b03060079481d000c3c0c1303065408012400f030880304011401661040c42608960f900b5113800b1078a0082440c100040040e40d01c005441003114048200703400490101c0c400109954001c50510b21b48541901d1074003844000d22014002c190940240c00250b000c1c0141c201040303004002640c001e00503890040b030010b24214540c1c000e004401e04020500080c1001e8015540c080b0542d488004450748030f0b4a0010b006000d02d803c000c01541c20311501e1690aa01548507148490094094603800890340d54040d00300d110301d55000d0903501040d03904d0823080c91884c3c89030a480c41c460500529060b01e074400310304540c2c0d40c0075000f80326030340028480040000b911080c1c01209170030303c1101c0c05c1c8005480000e00301c1c0030b1044c482c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 743862535 1250 743861285 743861309
    0x9020705190f06060e04031101151205030c01020403030f08090a080d021602150a17010b030415060308030a091112030a120b090f0403020d0914102f0c030115 69
    0x8800e011030191400642e96000c070003040050b903035254850580c0c0c400c4034142c0124086210a8914050601440002d03c03191100f0100c00c40c1001d01d40007900c110303004103071400c2c8001d104200401c1d40910091002d180a6200c13440780b4585094010114032000340011841d8101d03008880c0050340001c1982c00d6000c0ca0340c00943c8503964004036407800c42840001a40c80902040e0b0f4241c40700b0000700406200c141e603920705c03c2c1e17110300880400e0390308420b104400d4851401c000040c0418100346d0070400e03842010901040056503034a4081464100390740c3c00b0761050741c541400717003046100e1002d03d820000036521810720130b0317107082e200c1d03224001c19681c0001c0c080c000c07900800b44010360b4000c000f0301d58014282e28060500d07268680400e0400c071000c40c05403142c3d00402c001103004085940441d5032000003903550b11600b509202c03035050b1040200082c440c09184c00d0f5105803a501c05d0002200410041118603080d140311a86800781d0010b40034026450880448425202061410b0070344020104c45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 743863785 1250 743862535 743862583
    0x10020a0e0411120a1a1903080f040b030709050a051804020103020309240f0609010f05060708270a050a0f1e080a0b251d032d0709020705 60
    0x3035203d250344a018400010081003503e41280c1e006400180c00c203e110b840c40c071940c0007401b001034003042c400c2240701d412038401c200147e03d10004200f01c070454903905086c10755070600e00c40660010340d0040d0200ea0401e40500c2a41003580b160001094115040d000055030301314090b42c00c072001380019040540000c00a00c1d901d1041011780c0000782c10400a00140707045c41da0701c00c140c80c0c0039a0705244142908011802d18a000b0030101e05903424461800c00b8180303400201f00c555403182504441d51072040c08a00c0c4150800c00051140d481c40005c80d40b140c0f664803007080813951494100a100d030400303070403e1110300c2a041d1010305445014040d40d880c084014503100c0c540c860359004601e1445075412442c1000a05820b4030b000d01d00c00c03540707021640c1710300c1c240c0c0250740003c01d8038100055186461420704109401c810010311005420f8400204007aa41d201a01454000882d8910243c00c00715101c0101006814020007012108504100950b940da603122040310504200041c114900e03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 743865035 1250 743863785 743863811
    0x614060d1a0403180906050a0503010c0912050a0b2a0310030f0f12050d0e0601030f0209060a0f06090602070e011a03040614100509160f14040305010c1110020a0e04 72
    0x4129480d0700301c1110800c44c55466804102801c81401254025004101d000070a8201401110000c451a0300e480c000b85080c204441c074038213260740e01a2000d1091420306400700c1c09502c030903401990b80d0715201000c2c0001098850542c0003503042c0016035601007042105134071003030f000703130040d40d50000260250440504100541080080c40548001302c20074601e01e0080d00800103060080100c4010b20206201c041c0c040c2c0c65107000d2101524412080400000600d0151803055102c140280701c2c540142d241c180b030b801518001c0c5c00c6400410f4802c80c040c044640c040050000030404403a40d4100c3d58100814900c0e15481a44034481c003210110100e000c00c055030300403088034400201c1c25a402c2c079103a2901c8200030203511800d8040d48160000c40e14275454110300b181e0030030300e54a60b100201c4c8440300403034401e07140a0154403401414800400029820b0250310808642c3c1d5603240544a43e0004c01402c2001d075201da820020710400c1004941600f00900c82007058080b240010300c44103e5003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 743866285 1250 743865035 743865047
    0x60108180f010509030703121406040b040e0a110a350f0a050705042337090605060904030f2d09080c010c0b18030c06040614060d1a0403 60
    0x49400c006500f007004022400000002030b240c018000d42e07c40c140c01103110000b404441101e040c1180710302540340050382a04054208001c2800301400000706000010009402d00022103070803a503a02c00e00d440d00e0070a2929032051000742c00341c1203524003010b0340d0f10740480740002d81004261400f0080f422660100320103010303241c0014a800d0070740701c404103180b52194030b46015004040c07080d403034520902c02d02c0b09005180f00c00c1d41244c00983c0301948440e4240f17842000d180d10205941800301305500d0b01c4100c12030381840c801c140d61501003808030403480c0820503140010301490040030118100710100e980300554400007141c501b0084001420b564001d01ca44030120035813400d240c4116900100260300240f08421103a028040d1600f0711b207084011200181c810501401c007a220001140c1c550200c50403e0360543c242e5022a4030380000000103e04040c01180d00355102542c40300054000200070010320b42c400304c00c0b280980000b0382d55642900100c06100c05002201141c8002810940260 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 743867535 1250 743866285 743866303
    0x10090e090705100c03020709140a0e0c100801181e05061c0f0501110a021005060d062a080f0114010c0203030f0c0c0f0d0b0403120609020307080f06010818 68
    0x1510f41d80d180c1c01c8100d001380a00152113402c6006120f007143c00101900288900781d1f0942c22118442c01507102e0042c442c002d064590b1a5546902036000c50038120303502c16a00c420600d8a40d10345580d02c2d803400c0c901140005048060b42102814201e103003c070705c961000d02c0305101800034000590794039048003050050b60b40340745c4102d2400c1c0c400b210b20144424000500002c1e03110341d0081c8101c4441d1055644680503110b4604096800816105581004d03600650350145018041402c0c0310801e0f1140b009484580700000e80881c1d0907406207400e400da1400807078401c4e00358282007015080c14025241d601905100b03805101c001c000c003a1026a11510850314584d800070100c1340ca43c1410741c4001440d9004821180c45d034819500e00e6210750403d403800741c0c00303114010301c45900e40005440c0c2140c04031005000300e08102d08007011a07444902407184901500c03000d640140c40346000300015102d040040c201404205160040110b540e0307000106950000b9051300c566110803000d0296403402c1c03105 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 743868785 1250 743867535 743867539
    0x20d08100819060f1a040908120112030206012c0705070f030906170c181c0f061a0f04020d0e030415180303020705040506060c160603060510090e090705 67
    0x16403514800116442c2594500710b0080c041000580540e0281c041250240d48840352110107143d281c070003d1900d40e100010040c01946142d252046c0712300c100ca08440260006581c800d040d100c281e0606034100119400740040c00550050001c40c1d1585401d040044800c85004c5045880003c280600c610241c2d181c195004002851511062402500b00106401541700283d007201c80d50042040750a103160180032030a580c6403030041c1d21a4298030300c507000c0c4e900c0f98104180319903d800c002c81401c420032065001d201c50401043c02c900c2c0941c02d5480540d0213411610394032000540940e00d240c88414407031002c841c01030741d5205401694002e000300c0885010315000c00724000454100e082d900306050810b9668241080356a04640240f040c038501014006a00224080c4070500b080c0c1c0c04a6004000245101d092054401100c2d2405c5480708110002d8020301d00c0c01c00c80c03540c0500882010302000c4600950b640c0410340c000341607000903c10080c5590b0140081030a000d01404078801130180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 743870035 1250 743868785 743868793
    0x6020a09030b190c030216020d140f06090d030b01021b010318080306030c030111121306020403110111030a02120306040b03030f071401090b0105220e012a020d081008 73
    0x2c400d43c0d03c408441c00e40280802c03402c00e5000c0010340d02c24400c984c0d103202c0d041d6031108950b03c0c54081c4104c0001d812800c650a4590800d4070b000e916080000f0000c62003018014210340c03524a0b6514100f01d01140f400d0203140c2007222210b4182c0e0045140d10100800c0024000c0700c0d0680f1004802802804000781c0e44c0403580030011050010f04c40c003d6208600503030490714004429401e1608940c90300907803180403081807041c0045c2850b200c0200303401c03511040071050101c034152510380c100d078840d034411518200c20880c1c1002650b000201ca440701d0409034041c45c02e101a48801139103030040080c1888540030000000b40315a0788581c001c0c02c0000d805002c49440d011841051003960340104025920003440d280030406c010360500841c3c446a03407044444000c0d0340b0745030038001c42c19481c840485911418040300d40700c01c40d0a104082041072050b0000c90701c039080c0705012034011241003030312008410b192440f0740c41c03039000a844403007503803945802166941c445138038842d075000d16007110900b401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 743871285 1250 743870035 743870041
    0x4020c1c02031e0307090308030403090305011d0d08010303120e100e010204180203010503070315091a06010e0604031a07050c0615180f041401060f08060f0106050c03040306020a09030b 81
    0x1e0300201404803043d9080308800d400d41042c00d919024001150350304000784801c2d605000080340500903540261103420450300303050316a6030f29403c2d10a060507070135134542c4405200e8151074040092881d84002800d03d01c14030b5045840051019128116003904107071503107458103034882c040100300c82084a0301c40802094807801001381c0030b90b100e4803c0d0548400d0368020207400c0c890500c00c03241212802401420013924590b1814003048180c440026059915410403001c40c46600400c0c01c074065542c0d400d0f40c1450004005099400c80156403070080c0400d10051000982d2807110120648101c80c2e592001ea1303516408031458031400c666444240240800d000c54520084000c49605000311076140c0040d0146800c503500c00c2c0226030b818000025940414045100100291700d41903204001040c0180c652003021268541544100c003168418030070004803050005040d8050083c9141107490b001e10548030341d6a034011800090901a0b00040140742e050268668000640e03000c1140a624a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 743872535 1250 743871285 743871287
    0x206030a021201061e030903050d1409070b2104020a050a0f0905010626070509030304030506061c1709030a0c0b0703030b0f0a03150f0203091606090e010504020c1c 72
    0xd08140401a1503403400c070004513040380601030340f0f000040f0b10a0000140e41301050f04902a050360002682409410880300c14070103d9401a030400401104e06a1039505040042030f01e007500c4da5000903442c0300c040c005000780e2503094080340c0808030861000c40b25503c4a0002030340c10142944500e42c48100900700082d07168000c11110f00310f81c2058020041a0b80e039207410b031030103548290a4618062100c000e0320b8015469101560001c00503c0d145040014100c0400c0c6541d00a810644080e444103082004511307000700c01d036203221446803800100080564038600b8412103110107110900010440e030307034251410040c1c1c90031241c0109000f030703996a41c0c2c1400c01d141e900112056000074282240341c14141443c64070a80a4440a07080ca840c1d01d165880b103c102c21015004844119220400100c00800d51700145018400789000b030304803002e5000d007200181c0001c0e13204000b80b00f410041000b28031402045141128402e480141e900c000200700141000005142d61a00d06941c8e08080a85 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 743873785 1250 743872535 743872537
    0x30b1005061210140a060f0c0203011a03190b06010f0c120c02030f0619110c010608030919060504090f0b04050f180613062f030f06060c06071b0206030a02 68
    0xc1d404030a40d1040315130b210310700280c182c08414040c03900490b502104021092040c225071101d18028940404040c250b580060f0075a04484082c81041c16501c1e103c0700c1514003070107132102c0d005806042d07030603c060300d94620900c800d000300081e040c040000c2640810b14007a80b103d01040394000318045040403035420107000e500143e40b00782c1c000d100d100d00c582c07071302c1c540001d14034010315420300c545001c0810700f41000c01525103013445241c050303000d004240314441c0c2402110080d00b1084041c545400000e418400039111050081e44c83c0004500100002c13a003140807601503458a840119071969072510030780180006508080e0400d280500300891000d00203036043c040c0d907885094007810300c0c56140a0381d80701e00075581d0180b50210341ca0507200050340e950100185016180e00440c1c8129401c13140091003000d0140d00380d18480000030804400c07884104540c0c1300c81c04803151414400d401c3e40890350794900901d03150901070520401c400485c111400060f20b03940c0284080d0b660b1400070005006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 743875035 1250 743873785 743873791
    0xb0325051e060c03040f0b0304120507021f0507150203060108060316030f02010c12030506040506191203090f0b07031b08070f0204021903091412030403081b07030f0f0206010f030b10050612 83
    0x18ac3c0c81e280c1d44008074148240700301c03241da0742c00400900b000384c44480400c0707807030705048201c0c0d051140070080781001450308060320102c145101001a10ba190200c000342003a000181722a00c0ba030485a9089140103400204c2002e07070f074000c5511071542d07880b4401a0340241c65240b02410f9100d0010061210a03815003240d4402c11055405010607203c10061001c41d08a031004101006894581402034107131f2b8100c1c4034101402464262102950381c008150180002d1300215048900041c03458280350f0054a1181c0c440c00c01008034030300c5000780e03c6040780340c090030700003e01c1c0c8411580124203540e03498044e2038403081d1010454949641103c0064014440941c00312441d4800781c019410b81e07480030654810300c200142c1c6c02491a41c4559040b540c1000051911b488988500e040c00c001000360f10103040c5143c800d4682d01e0304d01842a001a290000f5607a0070f200719030140b0014403170078480303041000490707500c0b04840006807200d0420058010b0550080c50700704401003118144c0d02580180580 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 743876285 1250 743875035 743875043
    0x30304030f081806030c18030c090709150504060e100c050105090a061a03060c07410c130c0203040b03152e050d0b0325051e060c03040f0b0304 63
    0x1c0e02d44501c03c103000c0b4600048461041110050014401402d40c0d60004207a90030b008054580c1929068000340083c02e00380c032100b0000301c16171401c3c050040c07500d14003a10200305090082c2014981400181000010700000c1d00403100c41d19200d01143c0558250211142d101c4001e04c03840c40d0030154282e44548040c0b013550f0789402d11036280b41d0700b00461611070390111f0103000f42c0144d40d5030700000141c55100e40000c90f882ca0f2400892000210303101503140c1209110181d107105a40300004015003a141e04180700c0c0385401190078100715982ea0f4203450182c5c0f000f04030105c1d192001031740507402d40c001d9500025441c50300008001d450012000c01c00e6103640101c80403640d00c090002d0900390b54001c48181c405d420307108610304d01c0c0240600c020780f05100348a603000c0f174a0044107000c2818401c009000c40c07002d000081107130041c800051031401c0500801d68034145880d0b00c0084144c102c000700600345002c0c1f500020b40c0e0320000d109004540c0540510340712220701c295165440712140d0300c1158252 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 743877535 1250 743876285 743876317
    0x6030b090c0f100c150c170703020309071a0708031519030308071d1e01031803080a05071107150314010302060904050a0209122505010518030304030f08 67
    0x52185007007040c0000004003d401505002c2d80f104003600c0404804a00341c030881924000c3c0c0c0d03002180e84c060580d6055860384c0390500015031543c802c0c2c105602826034428940140100304403a040001e00780c04075a00d800900d1062924180c841b00140b162140150045000208110360f0594540c04410580030035954030003001c04a810404440c2c0043c00001c00240c8410041118140702e056999103504a000780e0500b0300c0000c40004244c81000038050000707220300507103c0310568041c444c4150040c6040d1304611030b050701c4e44d0001c2c400c803001410b9003a007503a1000894921885590f010380c101c003210049411940c0c40303a8555101441c18124500000c0c1000007a040c06c506940c509812281d010700400e003403180d44020000605401400382d01425424494040c0070b54036910440d0946d034000b0043e00e00d2803030f41100c801d00002c50501300345489401c2c076020811640d00800300d810315910b2000381d0700140f06600019046105560001d0305080301000039000344004003006000007030000c0020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 743878785 1250 743877535 743877553
    0xb030c0301020c0d082503090c05060313140c0907021f02040b030a0209131113120b0718050d060f0e0c010f050c030f0d0501031401140106030b01110106030b09 70
    0x5082c1c1c40794070551030607030300075184040c0850300a0503529000140a9203026044400e00d41c09040c8003d07030b0385000300080d01c50400c00d052200b03521180c405088265062444d40c41c1490902d4842e0782046001000650b07400c81c0c20003440300c10310240c41f881c60003c2c07803140035080445009580728803490b141c155801e5201c400d044400b207e8400c980c1220a410401400e56442c220200d0080d081000c42680007100064489100740702c6220b1920200d0f100e031b0845c1c0c0c44075400112070849240c1604012440e03036661a404001c2810700c51010b038801003e142050900e86454240440c584041d0b008030741055500e505901000380b2134000044548450070304200402840f140745581d02822012540801d580c0d1840c0140325100303030005c5c600c41c46200b04480c9030448808018840e9886048441c98840d516001401004a044851300d503480c4500024044c444122403440d80c0e2000c10700c540d4083c1640d80d5030320001d0764020000100c1c3c810400000f008641d81d43d040c00c0c3c5003078004039202d1015003d20220 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 743880035 1250 743878785 743878789
    0x30c05060106210902150c0f010e061f0506040909080c1507030b0f09010302150405190317041a181f0905120303150d050a12200a021509040603060b030c 67
    0x5030001c440e13002800e0212040803440c6d11460b035400301c0c0e50342085000d08900d014401c03800740070750240c80390008001c01c030615215a00c3c05514204280a410710321001e14100705696485054405981d4101c4c000104402e0a180002091054041c106001d004034280b0841400c150303e64148601352544061101a9018041000c05e4451001d0390745d0104001c801071015061042951100116580040786056121800150069008480e26000c41c482600910800c9130040d41c17012141001a9070311700300390401281c51200305100b20351400c10300010a800400070105610003000c86005000c0034181a08000c0c1c20149580008180000c40c2e54680e0015103801c2144411f15854442009542180c640440c5660001c8901c64550340c01680c0385000804910f080c402c1801c8140301d04250702d50030f0030051025104e041d03c18411a01d0724800d0740b10b07400308880450850f507217690440e444181004c0c0d0302201a00c5004076070007540c101e454641c01008008060b0321905402c0c0084049031011008002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 743881285 1250 743880035 743880041
    0x6060702010c0605460c021b060706091505010609080316051c08010e0f160c05010f0203190f23040305040b0f180102070b03070c030c0506010621 64
    0x400070300250308080d0300404034400713134003564001e008480036180d6204640709511540134001007104a1509011021128180d500058050180c028506001010501c0d10281d104c0d401801d802030b02c40356010b810241690f40c5811140e0480e0f00030300800c010314007814604005c0c0203030120020401d15000001c5902c40c0102488000c072a0b042008514000d140f5103e0a001740d01c800040300c4074800c030310b0f041e20a2185031000080c440c40c00d80c0c80c08013642c50210b01b42c40d1920050402188620361a060010f1540c4d0010b40c2c41c008500c9080c504400510341c500140186501e1000c445180e101009021525060080c107208441c00c401c2e013480103507038810b1a10201d446d038043c2018031401d9042901102441400120b5126010b13040c91818242e4500b85011141d012440060302540f001030741c0000808400f4180012010a1004190031424005059000d00c4068090818040c440c2542800c16210303e904c54003841d4441c040d10125651180c024242d51030070030808080301c10580e03004100c22006c2c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 743882535 1250 743881285 743881297
    0x9080114060a091503150b091003170a1b12141204060903140c0703020a1e030b06060417070e0c0705070b18031c0f03140121020a0b030f0606 62
    0x9182c20615880d04507034000405800d04480300940d4101d8000000c01c0c0f00840d074162460030300201044403c026070402c030340c02100a01680d4140303809001800490146011100c030358012560340387e940c03041e100c81500c61900200c014002c096020000c04100181e0020b4903062009940340c58051a116034081845806030215040340b2055402c0000c000c100944c100d010114002d041180b2184a09090040c50741d10503034080d003007640114410411402c2243c0894005c02c650008414005404100c021060a85110190000b40d5450101d62903503541e8045900400040512800f020080c680b01601c0303080601c1003800c06070380a0000b840790081c1c60221113846900c503000d0315006040c00b49610341a0011000c0e10390080fa502035000701c40e01c04000100302c403400000d8402a1111000b00100401e4614000d142010b0505603032a52601c001d03416203064504510012000700b17102e060b1400701c00c0300168003962100d00300c400010008132150085020321011001000156500410301107103109003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 743883785 1250 743882535 743882539
    0x121f0e030408120a03110f03040515070c060b040e0a0510060e01240918090606050f101b051608060a1404080304140d0324060f0c0317070908011406 65
    0x414240c0c103624143c0401004502a5030400280944d00301c540003041e80c2101021658400c2e001060000b40441040710712006145001e039040c451800300e200614840301c600000740410f4a031111640703d60f549402090185400d401152181203580c100903990b8130080c1c0704c62500034134065022490b5103000e200030341a101c1241c88002104103107503500d10300c54010b40d0510200b15111401041d003c283d1808402c1d00d0a12900120b516511400c00504443e0a503000c2c901c500b00820080c082a1281d10160320608018107240107882400e80200a1000e0b8140006010b4010b802e12441c403000300400e0074045c2c0d2418400c0b21143c0d5141e10480d0110b500302c03418041d4403181c0d03100040000381c00138000c56100d48154600f0362272110b802145031810300c800400d000840c2d00d800c051052005402c1c0c8c1103c2281d011074421408a280031700181900f00840a14002c115a40c0356000030305000b02c03c0c552142c2c5c1c00188140061902a40082152042d0700580159500341a4080001d0030109201380c002c0d500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 743884892 1107 743883785 743883793
    0xc1314071205280c02010e030c0106030506091504060e010e07080105060328081e0d1b02030a080606091306180b0d0c14121f0e030408 59
    0x40051200c0e03448003000f69900c0d1000c452090050003050080000614444211070407405458400ba80310342c640f00005000e00f0620b0154000000c880c06941603c40c076480c0c0c1c00b0040c0e100c0207484501440b0108034004540483c0007030703002956541c807140000078840403c101d81828085954055586039544008200e107605081c0003e22040ca072041c0c00c0c1c002c000e0701803860006501802005005064081104c00c1c0c2d0b40100300248080b030000b00300700c0792100318081c40223000e000303c0300300c800342184140c00c0b90700c02e18000410f031005070340d45403586400390b51884c050002d103820040c40c00d2342c000ea208042d00303451071305840b401010300040d5a61038180c0d003440b07281500ba02c481d5022140164207910081c0e0103d0811822001591a444807484207520606c0018002880302540203189004421400014484819040d040750441304801d10944001d818030342d849019030b1081400c1a04 = true := by decide +kernel

theorem cover : BRFrame.Cov 743705035 743884892 := by
  have h0 := BRFrame.cov_init 743705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 743705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 743705035 ≤ n) (h2 : n < 743884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
