-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1568
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:42:52.644002+00:00
-- url     : https://prove2.me/submissions/a8371b47-f479-427a-8562-2ecaaac81b1b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 281834532 ≤ n < 282014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 281835782 1250 281834532 281834561
    0x8030c01060302091f0b030601050c1b240307121b0305070905010c0206040e0405070506030a020c01050a05040f060b010e0612060405060604080703030f020a0f0305070c0f18050a090204 81
    0x40c140150b20700ba010003030f00f11003100040c2180344001c44040345c94100c10711460891a40c040700050860b4012002c43c3c64500c250010f031429016000c5284c004000022005401010502e42c0407009114804801c0c03885d16490444504503900e000017101c49410641c2c03255025034441c0401042d26981401c403c8904d8010303107001c50189003d20006003963741507404103040103504d0f01842c003d130300c9000c1241d096441951051f035559986040207440c0070080c0d446560411000010000360368010b5019024403005200240703d2a260f880f0782c0c0c425200107940103480e05481100400000d919544144009a8103042803c1c0c101010707030001c1d1803a0030a01c00700e1554031051040100314a828810350741d10010403201c5a05042c10040c0c4203544440e140001410b001c0c1031034000d1041c0d8003c121a002243e8840300030000032185203801003007500304d44400c40c0c42c06018417000c2a031039000040c001c145c400e0b060450001c201d81146a2018010217400181995529058580540c495028000f100340640c1f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 281837032 1250 281835782 281835791
    0x204030302100f0b011d0f030a080c06070f08011e030b0109020409182d02030303011203030b041b1d0a0b03010f1406090f19080d0f021c081008030c01 66
    0xb01a1019030309071101000c0b0301ca2506400200d280e800210250501c01c0307080300101144880740126900c0303a8002d243c1580741c03094913115410813650304c3c014040c1c16012030a45030541c541d01e0050702d00144940450020465040044c00a4110040207170903501d070440311103544c25500d4450b00e10120083e00103d0909800090900c948182c601411800000040400c0c10f110460340f91810400f100c00f401c101c201214004103082028026451080035400900381ca40d20350b910131210300000c01a1400310042420303c540f010003882d20b481210050b135611030b812007204010a50445490203240401040b41038030443c0359400740c03034074034040025000070302c186a900e50403c14080c5070340d06558490f040c8260040826159521400c0940d190400140d9040c00704030758100005800c50224641e805402100d05030004880c140003660103500300040c0c1710001880c02006049803074034416201c044209503004041c1610323903c200034030380c3d104c00513a010314113080d1100003c07030860b401900040c005a448 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 281838282 1250 281837032 281837053
    0x405030114040809011103040801020f071109090706140408160509100605040302131805070609060e03060c03071107090209011d0904030e01020c19030b0a0501031e02130204030302 79
    0x244200801007115000007100307032820f59600300040c400c1c400f682d8100a000e607506c58030090200260360182103260020364440746c40092440080d008990180d90300c1d942911042d00360f040096165002c0d08010000c0d111103030400c2c0c0140c80c81c845080c44170034008810440011555003d2009290000c000b9160b60300c400d1070041000007042001d40041007000e4114010004030382c1110840d03088946c140c2d1108010750751002040010320b00390707811250b0190058002c1003040000702d903600c00ea545036158400c0f282d403544011a510491060a1501503001a011410000b0b6660103994050801d281c8084100c103149400c60501c803441d44000c075070700e80200c0c800a0319a04640003501804800d0003880c1002c0d40000054602000a00b01505101000403540ca05910134404c1d12031210018180d14840c0c5260006000c00b00610710050f1b807031890010100d1260401401000c1c100c940181440040c1c0043c004000c100d024403180481e489400304016003800c11030b60000d04010f41c040e40161001208 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 281839532 1250 281838282 281838289
    0x5030d0c020303100602070f12051f050402120c030a150b0a0b070b010b0901120b010c080412110d030804031805100806090619260f0102030601020d0801060804021309060c02030405 79
    0x113140d0004d10035504800010300c86100103030062012281c2c141a031001c0d1030602d041040c20081e43d1121030b901507807046540411141150441c0f4080c034401c0e111510084040346515440d50100310565034590000c0c19064081038881414009604030480c000030880c0c4242d000901032030307045d8056203021030042170395020300103442c0780300e401042c400c4220745c035103419880000c140440180c04144000d07925901166280d1184c1b501e54886907004000c180d480b074075000c8810001408402c210b88000c1c86091070f4170503040c1884446601549601e0381410b60b1240c0c3d40680c2c41c540030708444000c810849030002150b90b6140200ca01599080c0c45030030f580e00b060414880420300c0207001034010500c10300a14036003500e00b404801219420781601c01c000300360302281c40810b841e8081d10300440c45800710a10000f0010b5000718005c0c8000d0b000c81d2003520642905881c10784091103a08007203520040001e01600b0445801d10043c100c2200000310201140d9585007112904000c5000603400840d00744400d04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 281840782 1250 281839532 281839561
    0x80910021c030608060c22060e120c0d240908130b0a140a030e0a060f14090d0503071e080103021507080f07080c030301080a0c0b2505030d0c020303 65
    0x1c0a140a00c01d40d410840c0199981d60007411000c04c044c00001c00f000036408400c1c0084200b040d11108907a40d6988400c02040e8184401895110b030b4585500614142c0d000518040500005013480b04595100d449a40340e1030f15115803140848002d2074601c0b404092840382c4030705503101d1650386840300b0a40c02c1511507400309400903c40340904204010f411340d0807400c0c2070740741501000f80c1c41e40d030800b02400700c004c0c000950402010703102e0076807844100201c5802020300b00213840b00070000110b11802d100c000c09015142c51042d5003144001d500e50b1032040b401035511810702d0421001490480c1d10b0420000c1d0000c2142e00005c0180c8010301c03c41c9000320608501117070304481e090902005803100c048510a00120046a20700010788404000288050b14490382c03107901601d407030b5039403a10803d41b0f805d081c8104a404041c403101c0800c800304001d09035144100304100e1482100c00c1b00d00801700e04a1500c400b034400e071005002007505e200703940c0266400e9503256409551641440c0b881210780740c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 281842032 1250 281840782 281840833
    0x130204122a0501170702010b12010509060c0405060a1b0212060f06090705090918060f070201150e010605030a060308031003020f180c0a090306060e091011040b0708091002 75
    0x600700c0020016607a000c0c101c99980c0c00011000c01c0503440c1d0a000b0f03801420058403494001001000c86143d1040642c003040c841c15000342500d030a9a60800c0800251056010785980074900b4043c155150388114001c03401140c81200240403040207400160514504910480c001d50005040229140c03109940c0e03608000305459200b25030070b0210001c0d2190050f00310143c0150440c900150b6045078005103007100e076950300151f90399410400b4080c50682d44c210b6541001d5800e041c0070750034074110602070100300c622a00c00d0541b1a42046821261030384040c05080b911900c4001c040040740c0c1150055000704469010416868030758818001104410120706108038003400d0441651000141919803100c01c50203215a500855102902d0b4203c6a82000e03004500d05100406c00701d02c00b812141c080c000c0c20b0101c951032a1500c0d03100d420384076a00c0d52402c0c1514288010400204c0c03040141400030b2140b4500c50405500101241d401203480c4000c00050f41701e113151040c081034020fa100d900 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 281843282 1250 281842032 281842103
    0xd0f3903110c0a142e0f090305030715022809060305091e12030109060501120228020102070203060906040b06150702011b06051608010807120213020412 67
    0x1200d05010028103007140318810001018000d1440b1041c55558401c0560102c0440c0c1013441c4150307003454245000c152010801c1c5c00300700709032045101180034500480889a1080c0107615210403030381e41c0001840103803104401550207100402e55005040010355081422441c10a036032a150305008105080307550104c810300d0701d07000500c050007030042440340310584440c01300c43c600803100e203501c0d20b0b010141c03030000b00e210400b00c00422103074001d404c920200d44090f40e51003042d00030030005008a110756054240c8101d41d140c00d03200410780d05540b036074003503145000050402925401003414450200c03076181080d084441044200148010941d400c00780949403000e40302c01c0401070003030500c1190700282c140003100b05000380d45000790448070081039011800f4090790030040584000e0255184003100800c108100224400c1000140d03041150000c60b0700000380b40d0b1540900212003024000c1501d055020400418070316041c004d0100e40c50b10507104262104410342c100d680425204c5180c0c0d00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 281844532 1250 281843282 281843293
    0x607180609080304120804030b04060b090c09100c0302031b0c030615090411041e1e020a0e0f04020c06090601060e0301150605030901060305010501140307080d0f390311 74
    0x1540600109880503a00c640e6100306208030542802d00247c0120b6000404612011081104000b070301e4020413091001540c0c501c0302c5480e0382400140e10700405005a400445010103032803c64420446400300078041e0054910744800c8030465000004242e811060650003100041040d0404001c03882d80805d0386013141141c01020b400040000101800c05030250f6114188280c565a5a80c024804020008005048900c60840f1b99001e8440240092200760004008840b6482c550085071441e03100f036a20700c0c1e400801c950411400c00c1c091410306421950038001725410000805c490f500884941c00204520748c0750034401450030f200004554081e9041000400420544140000955040b801e1450302c130b540780c58080d401000d186c0e00c06041582007070300000d40450049002840f14005130f06860100fa1074800d40c40ea2072900c40c602c8000501200c40c0c00074103c2c032454001c001002001c5044c3c3c0d06079610496050706140e906519410340401640c43e00c101a08540808103014001d4080c08 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 281845782 1250 281844532 281844539
    0x6061e1403090124060e1e10020c060301080a0c0f0612020703020a0f2d0f030309020d050718051f0308090a03021305090601050a030525080607180609 66
    0x204025220410300428480c00300118101c0c25003034020507130b04d510f807500300c100b43c100d0030540c41c6a00825110340408070328000301050741402c111100e040d641110007461a1704c10400810b000f5400d902100c00000c60094280e035840950701e10005500825030040203000441280c20600c203507209950043c0c00c000c02500d010801250412143c442c1190b00d0400180c50351000c1c1001e80c1002203141c402041101202140e10030860b14100051506805c4440079075200c3c100e91550b614802c140b40c002e030880b484050030b500024440e4010780c0b0b15510251805629103310344d202860001183c02100e40d40000f021003840c41822480382da640a10025407800e40b080914a2624402c00940006400c05000080500040d15451200401940c0c081c00d603107050020100c088005200a4541030651f0190200008031850300c0e060f61425280c11902030b100d60b5020310106240f20902c181d5000b400c075580308001070191400d004040c07040a0a4540c8280e01656003910b00c0d84248540200b03091003140081403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 281847032 1250 281845782 281845787
    0x40b040603061d0a0902060714160504140613020405130e010f02090904030804060e0d0e0315010b120a060306050103120305010905010b04031704050d050a0606090513021c080a0306061e 81
    0x104d0300f0207606040081e4560050000c40c00b14414030201610014914090004040c400a10420b1150178245c103c0e10701d03603c480400040d15601e0084000780941d030f6011078500d2400d11250036401200c2c000c014078150780d48001c0381602d483c052141d02c449684507001416070303600b0b00400c40c00c10400c100c2103140204440000f400004044c101408001c402c000050410500f903018507000100030045135404014100000c0c42205c080b403003075000e401007503034101c0620020f40c1424169812030b080c40741042d07007100c06c00018410040c0051070107030b16000f00001049003131050501845c000c0f01303601c0e840346002d10090196401a8800754000d49414010030a841c0040c040c0c8050f00d50064591610361070141a0307001600854000c168030036400e08081040200018441c5902842200c0078000155110328030310031180101c508200f6680c40800b800014035021b2810200030401003040301c2d0038100364849003002e401038008031012032341d241010300490b5045040941d40000d50880c1060441300a03400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 281848282 1250 281847032 281847089
    0x304050d1b0b1201090f0f0204080106080f0609030415030612030822020a0605090102010603140c030706140a05070201020f0106060302130f0b12060d080304030207030c0501020303090c090903070206040b04060306 93
    0x148135101e951ba0b040fa00044800d1742044602c0342d0340708015500c99880e001200c0c000d00251241c41040e2146030300250380d102340411124802c00b5943d003d1801c3c1468040c120301d0444ca102118010160348010215140c000a0701e05140240a41c1d03e502e814a0403148071110b031052041c5203c0d015844464800042c0c0d1541003020070354090b442c00d55258010000103038058a9103030001443c2c1c0c0300700580c40c0300c0784000161b0500c402d03800300e04442c0f6056585405885070030080d10441c0d007854040060000c07042c0030303200030310380e0f548184112000c00745403010003400c5400d2a0894000a0380004152103541c5550001d00b014164039181c0182c036515150700001c05100d051109030300c0100381400070320250360310001c2e403030b41c5c5800610540d601d15280c90001d4555140d80070850300c1254249000c02d42d548008180e034407a1400c0d000900c07200b88064100000705c1c9006140c251584010404c2c2001030721040064001030030901d03541502d03682801c4002d02510110303004142d10307038070050b6440907103c0f4201a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 281849532 1250 281848282 281848289
    0xd0f0303180807080c15252c0109170c0f0409050a15060e0106052d0d06140603190b0105041d0402120d050d0506030304050d1b0b1201 59
    0xe000401500050103005254140c40e400380c00210003140420500604500a0215080c0e90301540c211820b1007515003102ca00a0f24241c0c0e000c4a503419071043d245400b05180f500030070307608000142100000c00c00e038407040308480b2202300c1e4800c02e01c02a040e5821141034800b030a4101d40740040c80c515048000c0e9100c620552891062103482c0405010740c54036449240010340010a44080380c0c040d05261f01034100300e81074040d8651500f9000110074641450341030580300a965902d29140825a40440c1d150503a00c0d1510700e040c10681005140c0c2c1342c031008211941176501701203810751404032242c24003c0035038a414011081007040200c20411302d000b0004507000c00700e00250308011107004032028003407a0082d20b207200a040010003096440815a803183e0f00c02c65404a20402842220317899a0300c0c49a2031010800c02e00c00100e030001c2c2904042d5200b40094100c83c2804c1d6a03500013201d09100340b0003aa0359428003226180008080d9103600f001d001c08a140d140303020084000e0500e1528140b1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 281850782 1250 281849532 281849537
    0x3031d09070e150f0720090c0304060b010e041803120c050a051602090f01030b0a060605031321081602060c270a030c0501020c010224060102120c011a0d0f03 69
    0x1c01c699090407108058031444c01d40c001d50310780c07200380f1807074003803401d00d4041c42100329031040b0129070040e071801c0002248a120500602402e50301c2c1d07903682c10040c08002d91a175042c0075895400c1411502e0b10f126264400e00c19164040e02c00441c0d0501a03c15130440c1c0d00c078180c1d00d0404006c8030400c1c4c2c103c400c40382584a545442543d60380d490350010140022140004c0d40045c4d06018442c45440f082d0040741a40d00840906442c0d0b140e020451040341c1c944e1241c0303804240180300245807006c8007010340c82c0780c5009048488010a00000451010024101000c0441c41c1c2d4028001c01c902140d08808112043e130000344a0f41c10080e0403c1600c0c0650321303102040040b60f20100044607028400c0c402c40b2040a040450900d44a1416041c60351070750148074010311030325020300b545610008401c01034980c2011038000034041d0740400c07500310384002c01482c1544940365121000c0d0051600900c1d003c00180c000183c0c11400c5000c513a0281c8982d54490700c0340c092850340202050115644210080d40750 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 281852032 1250 281850782 281850799
    0x5060901050603060a0f0f03032d050904020708040905040c0503070b0d2703021b150301210b0a1506111b04060b07050a0203010b1912081303031d09070e 67
    0xc00010745c1341201d03078002080b050140c890000b00203440c444c01744240e030312030340707803180c0060b095a60b5808840340410307011942e01c0303891450441d071800f8800030014810050800351411911340c580c1c0301554000c1d0301c22248179079184100028810304d209094041c2000310050500d003450140d21000e40d0095540140290703640b07080358105404a01690010301c01041444500090503003400794440c0c0f4000d020340c0e648100700d08207604d00d1902211040303400c0341400390a07085900b410781c1c020fa12000c110102d010380452441040c00b140c0e110301e946220303070000074000c1070040340300c42c52091182055110000f4040502088101c00c0f8011540c1041c0340da20350b001070f80352142100014040c0c500c43e4440d1040074000141401400004108942c030306000343d000740b104009400c140402916015001d442c0e0142106040c4013916840380c5001225010b10051410300201d00c454500103802c40e4001c4000c600c42c000703080075000c806c1c00c4c0e603051500102c0700d0350064508110060241c443c540320382032040340301e07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 281853282 1250 281852032 281852041
    0xf05120105010e43022b0c06020c03040f090b0102010216110f10050a03060807140105210f070210052401050f040b030603071502030a03110c0615120105060901050603 73
    0x100c0000c075030a0481400001850709115100c48480303000c130001c100060040040000403101200c40d40c002404900d42c0e00c2d85250b602032000c0342d0324030828104a41190b000c024003110b566007040034002400c001c1100035101440c00503220b0445402e4200f45040d6401848814101c94040a00d20202e5802103030840280754250005848180c11280c1542d00a000d0724102d80f590b580440580440c00b2661410002d031510b50804594444052142052424120311540d40c47c1d48650080c1100b00c0c2a401002202c0403c041c00c3e0b0041e10f82254114548281401004840341d41003040484140e00f8100c100a60304000c0018800403005021040314800714600d08282640300350125040000c0b910a0240c55a440e22001d11155000b507402d40c1c0b0078428880c0209a510002519071381105080d001580780101d4440c0a038050300e07061300c1c08088a40203000400d40c0801c14040d01d4420151001c5560083d401c1108101c2d561f200b00c560480750303a150004200c2c0b42c0e100d03820320606464080f108070340c0b030340e44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 281854532 1250 281853282 281853331
    0x11101110301091a030607030c090501020601030213020c10050c091f081b040b0f030604060509280209040c0320090f0d020312070b040b07080c030a110c01060f05120105010e 76
    0x107108050311703018030a2400b0844940c4e450392010b20b480019075034040600da40e940c012a42c4400070b0002a500c99a1406840140b0349603600030001d03c280c1e14162030785009007410f91340c11960304a90b070305003d440014000e0744c2450021a0603200e10348491552002c083c80301c0009000280c01440c500c1240d41803501400d00181c00c0040d5002000d002c0d88065843d894003464404607002030341c445000d2801c02c040441c280c41d1646569100d081c0684030400754903000d01450b04803080c00007894038000d50070030044c56152070710300400794008110303200880c5994050000c11031001542c999000c95802c240f207101c440340e440c01a00c01e10b0080c2242c020442903140e00019041906422000b00445000610705c2c040145113800503101e58080c4030b1121459482010a81c4c1020741254050740c84030042000038100794080d4461140d90f031185204900345602c00242c1401c40c2e07510f420010750b842001200304000d281001c0c0f1700803541c40e004000c0c000c951414450ba6100f01c80508082552908410868249030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 281855782 1250 281854532 281854571
    0x20d0e0a0810092102060a020d090b0c0a0f02160308030c0d0905070602190308061e060d0f0b04060503070312110703150513020916170c0901110111030109 68
    0x9a015150000442c0c0c0b80c03200100441d0004031098044820708085600804900c0c03600001e00c0c1d0040d00c400e983e070821040c02540004202c2c40429a02e0201d403011580c00071400740708410050340142d480400d1013005d4204c001c526a00c20840d80030300f40b020840d87c01040032404032a40a10050b8590700e4440d6440b005004054903e12254540700c01078092140008044003101d001c0d408bd01c1102d030a00705400307082d00b003681c000740114450001240080c00c01149100d04d5402300c4d20019046207600f0005080c65001205205202e5210705440500c3c104900c0b4140360031608407020024545454003294480d02548009011050700c2d2241e12030702400b510b89038010000ca8001e94507450340b280745c1f0121040001070740f444120314000003c0d00c641492101c040e040d40c0c0080000c07106607120001d289803030310342040240400c4004a80c0c82c04400c1b4200c03807540180c1d42e03e51b1039900d618414000522064224580c01380076810204d60b8040804c03108106c83c1540d12242000c00d200a6000c0e4404281 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 281857032 1250 281855782 281855789
    0x9080901031e11210f0f04061b080106090605030610050a050706140f0a0b0a032301090507061b12030b040e0f01060303091e0b03040620030405060a0507020d0e0a 71
    0x41e04100d00c000c21481d1410042c291380d0096644080502104c40d03801c08150f0003154100203000c25079002c50318800900c101c0c01d030f000748109000725a04050b14042c6c0b190144a91554010808050050266a80080e04000a0b10040c9805800c615100c3c0000d4495102d40d9900000d0040010b21217440c18402c0007100d48450300480c0a010b41040498001e9104108440010b01038607800c02040c1342c2c1a00d40222450181e0007003440034403a0035919140529084504a040650402c600201305000e00380100c0030990300075005040780074908100501003d1a000204805e10088128200010314415120000c0c0d00c06140010310406104045001800c100020881511130f080150f07220309015084007066034441c1e6602d1031040c0e522461207400c448000c0700b498800c07125007018091001c0020145070b00600810700441d800300644000058550301d20030940d0341d800300004202c1801801c02c0042e070041144c40c02003200d46040d000094aa40c0c4c901c0e5220108841c6506801d451360300c400e5890081c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 281858282 1250 281857032 281857091
    0x5031c05160804140c060c03030412141c060f03060e010c020c011e12020c1b03010e0d082707060e0618060c0a080f0706150b04120f080d0203040204050a0908090103 72
    0x45201440e000d55172278000b01c400f10b4040403031400d820610b920820074181001c0c00a600c05080610007030041c805940103c40c44660140c0e100d40002c2d02e40c2e0f01d13400010055000399000501a68583c03111230a4608140841c010b55014000d16030356a44e200403540d41e040d59030103141c42100c42c0202d040b5100400640304000e07045c0045090310260070086840c02c280c00180d401d0454a01074002070600345c0e42042d0000d5001d4028600000a460043e03000030760254440c0920b03c991410b0b500381c0d2900d92421060311300309510071601881095040010315603034140c2204c0075400c25154010362000318030b00700c1030603028545c00302d40842c40f076004011255170140e20000007902d51054106400c00e0f074021310b200390303100d40c244807909450324a0260381000395030194003042d14003401d02e5403100a06d4000101210b26034401c100744d80106061001030071030994104000b503030700d092078010801910300140035200d02d2440e02c1c0501c0700107803c1c00201c41e683c00081c01e0201d0340d44580002d81c000407a000c44107010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 281859532 1250 281858282 281858287
    0x309030910030e0115032a0915080d180b09030a02040e0f160807090506060c0604050a02270714040503060c0702240a0c08040305031c05160804140c06 66
    0x996a016009030740d00b00c580600800c000103034044c01600c4c514451101030400f1f08010140d801c541c10300982c48002c02190110000a940c0d0380352450102c0f001034100c210300300e08100701804400418440d520b00c00307100d840c0204141d00e0b0785d8401d408902440c4140c24203103100041c500c1c4161801e02c028417000390020400c10240e070400c4c2c1070b2501c0b0419078908540710700a2005181240800700301e032a00380e5030884005c0c07405a08118801c1c00500024081e168006414071000d0140704080203000d00c25031141300034000c0005a841032103200c803444104200c015905220520109104522141e0b000601c0d10340122401008001003405103c0c540059030103000d42001c00110b04184002851071a10996114143e81c146103040004110342044410a0680400c202d4100b507126108a10005001303482441c83d042d602e80c0c803146590700c28841c08040341042c08400780c2d09001449005d92102d0041006080c0c1ea091250040c408000100010012a40c0207200c10500b0340400c01481000f101a20455 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 281860782 1250 281859532 281859559
    0x907022a0d060e010b040e06060405040309080a0804050108010902040513050c0c1009140604020919111603030c0e010e04020304110411030a0507090501090b181c0c050d020f0603090309 81
    0xf07848035402802066007400300810450629100d1030015201841c00307420b0301d4803408100400380001410581c10420000804615040140100c00f0300d90311590303407503507218034200000d40310b410305038040c4014505c140010409611014050341c0e000210100000e06651040c04101d20ba01400000200c07621404042000794403082d4019010b8501401180310f40c040c3c400102c0e80e0390031080350000c6d001340f42000820a56a050810581c2c1c5e00c601960225060310ba820b103003c0d20785c0084070101c1600544554000903d90144a440601901454030701c3d112124a000a0080c40b04011020b0081c1d40c000005400c0c800401820075102d200184144514611108600c020303400540b6080b651900e420045194280250100401c840060b1565000c42d481d0401d80d142503084012040c00c0700f80d02c40c103186035541d1010300881390f032007400d0081c0d079100b0141d040001030705282e60441c034003e45110700c008002d41c1e40d00d040240e00c41d034110381d1207541e40d80300c8501604601896043d982c00c844445001e5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 281862032 1250 281860782 281860793
    0xe0102040602150109050103050c01051633090c18020405030a06051b0a0e0d0f0f030206010906060e0609061605060406200a0e06090a030506010e090c0907022a0d 71
    0x10003440c43c0b820440c10720345d8885103400102d13030007840001d1566100c88698803803075000720003400b01101814078082518201e62504100d1250143c0c0c2d00d501c540c4810f021203882e1640c600002c03508603185104109520141d039501c5140002ca0080041d088a540c2801120041540403240030b80409815903030340080d0761a01001401c026680300c01c1d5803600300b940700310105614080d9031102d80325640e1071007565007140600c658000c00a00c16034000054684e108040341d415995024400c3c840d03401845158500401c11044654030b8100c40d04020220102400503510341c02070b00e01e4040100d580e0f03036451103075402c0510712102c01c4c2c0004106010703070304c00c2000303104003503208030f4018510700160b8044000507034a504a41c412081e14001003904000c00c40b80b00c1c280300b8043c200f40100a01a040c240f0745030784071a454204242e000943c41040002081055981446020700c00e00c0e041d50105118200703160040d40320715041a209900400c1800302040d000d40103c2902445017002d01610312488860915 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 281863282 1250 281862032 281862043
    0xa0b0f06040b031012080a030207020a091e0f0207030c12111501031209053a05030705010f0e07090c1701091b08060d1104021b030d060f0308070b09010e0102040602 72
    0x500b01102100c4001003000e61707841d104460640c070200192505a0302c50041c0c0003500104816a00810301c0803002c1a08007040c030401c0114050400c210350202003843c41881a644500308a0fa502d5005000000009800c003040d0b6502b20f501403005000c10a05140c101e503028590344c0f03039140c82c1c0b01e84004014050440b41b0305071b05130781c001e00c0c010b1141000b0107030541e040d08241c4103498100f81c0348800101c0c00d42c0c0115202a41803881c212885c8a0300d040d041c1c19250100c2440c05881c0750b00001818801c0050900c03074840040d010300c806114110241880c9a00e405a91185144d990b03203038648104504e100d40714012003680c20150044031355071902d610000504005602240c0480d920f0460706a05001c3c0c00e03010312408000380602c440020b995130715001000500d1a240c0c01c503070240b00348000c12030340900c1509038003407140046482e2843d51490300c0940d44507510011079582901004c0c0041824541120315043e0481d800001c0c584130090110b0041100c460103084551021038003180e6554003140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 281864532 1250 281863282 281863291
    0x110c0a0e10080106061b050a050f0c0a080f030f07050f010504030906030509060c0a0c060207020607060902031908250213050a1a100c150501090b10170a0b0f06040b03 73
    0x1d04901c1a2903540060880b6000c1c000c5802254034640c0c03000d500242400840c0c0300724864401e60f03442c014650342e1503181c44140100d244141d00030501120450410381c2c054030060024000030f102080c2035a1082c0d84a203d000340805008000040e8a41486010045402c40d15607000007041103180c142030080034034031140919000030f401c090200e510b41100042e01d03401a01101c604500d003000c0d911007591003041041c070498401b6002c0c0306160250b5075000150200c280504400304090b4054410581084260b1016294038090083d8250200741c0c1d080c155200084c2c1d454036030f4400a03010301802249014100000c1d071281e09031900c10742c0e00c125908810f016003800c200038080c80140208400c5118125040c5a0300240f603601000c5c601c620405c402c082441c050702281844a40d210796080940f03d00b600224141a210741207042c2038140113408100040703e0b0702d0f0101003a0720114004d15400c4014111031a40307a160520282140d54000400c403040c100109a266215035a0b4a814400c1c3c20846 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 281865782 1250 281864532 281864551
    0x70c0803091b0d170306010c0503130f0e01080607050306040f0515010905010e1302070317090708100b090f0a06080d170903030108060f100506070503030f06190303110c0a0e 76
    0x540918541009001c000f203c5502800b2404c0100240c108003544e900002c120030f04110290102c040811801d00052113200b09035007901803003c0c2003820503c885900303070f40190719010803100100000a40400c926411054524105a41341ca520f40010050000320035070360b000c5860141801480350307010007408001d031400c1e2150fa4203941d44100650b414001f2001254000e0001d04219040500a6008003480d9102e410640038000081c40340c0020a4400c82d142c845030343c4013600a001255040145510000d905001880100003403070100f07100d80d0018007042028801c0801080e90060300380c1082001d00300110803541030f4910010000e01070f10a030a03032041c4a180b01004190800b01c00b0003140d05035a014001802aa110a0340003810345000500005001c140031001299a90302e04004203803260007140216202c0c20700e000c04003c2c0000190a0354401d58a003610840d6003038440544030102c0341c150030041080a8041e02c401d00308283c200d09558018049600400c0060300105807900903031a10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 281867032 1250 281865782 281865823
    0xf05010b03240301020c01050112031202040f06031a03250803070f0807030903051002040312080402010212090301020913140a090302031b03070c14100e1503070c080309 74
    0x3064030016a10050b14000c00503009140207042c944030181c1e8206080b0405000180b0308803980565500b110000c5e08800c03e04070f1f0904a090500d0b5020440d465060032030791085250030718010003020351800a220300014151514140d080007005410a40e50040c0042c080d5580d90030540c06190203500c05624503039080c10104000b1a1541c4000240c400c2c0391f50240301c1c0000c0e90010784170710342e40744c0042908508100f160100031000070340034041040f0a06101c0405a08c1d40d007146400b50304a2203000c200781c20086110104400f603030b4002400101c5200d1444100d85d192a000c0200e40607200d0842c4041d08611400815891082c00e0750107998a02d04031540f001341c5494074540103082d6510402d01400592003801060810105442c02070b10410005003202e20b0b010683c0d0710007071400c0c0d89078070078000c10480340b02a00c00382c201101c40300c407600d24a1818551818204c00010308920900c68040e40ca4400440001c51060194040118a90700020b203161240b620b4483d859540030308581c0703805019583c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 281868282 1250 281867032 281867039
    0x6070f0c1b0f17060604090813090507030c08090c01030507030f0914010e120904110405090405070603110909010e0702010204080a050d030b0418020d02061306030914071d100f08010f0501 82
    0x603030f81c2442950800005001240c49050401010304507216050f182e0000801030721440c801d410740c0000041a50340d1000c6082d151448000d000c031891401464180030851003040701ca20004964845021000d0030009603545602d07400f10001c0030074442d2080407a00d4081e009060200460100301c610000074000d101544030605010b8507400d9071a07500c100158207001e80000341c5080d4011002024114040c2070516643d0300005c0c070102c2d025502954981c00400051110b141c0c98001d100c1d50202c55039001d480d01c0641c40115007820070502c9010042c3c510400488c03003540c805e404440080070400e088541d0003d403402c0041d1506000c0e103141010a140101102c401c0c1454083ca000314244458500c83d08611a000c0c04150368030b0b040100d0348101c00b04841c0410300d08018070f10001d02040d0ba40040d21985515007c2c07071041c50f61589510951205008014440a4005094240001403074000c0c0c5501c40c4602c602014a00c1e0b0845404a02c0c104c9002c105c1000c150700040e0f003405098410710017a40d9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 281869532 1250 281868282 281868299
    0x5030f1b04030f060906090b090d052502030f120a020118080906071b120b010b090d0215160b0a18110d0c0503030a0f110f06070f0c1b0f 60
    0x2000d0541040c00240010004101c2d04a00111540e00541000c201502d5a03603803201110500c001c01c440380700600080c01050360041149208110203810041d01d00b02480c8514500c0c038136803101e100060b0f0784030b4084104644051140800c4440703000c040b21300c1003c0c1004008102d03000003802c400190b11304001842c50000807502204140e401c404285e183c06d20348400c0c04020742c04504290b03001c00c0d8000944c541c6101c0030089400428200001500c000100d00e0b21710100744043e40701e000c00b40c1040c8000d480940c0c5419a110800c1d604842d454165007410b61128807134001c91000c0f5135004032101200040c428603807c441c2c45604403810070404403140ca0421075011a4480d40904811500741c0c207406941844100902e0740c601603094044034555030000a450759101c01408000510070555040006400400000d007012601c4090910b0184065090740e580754014050380400812a01501405006041d6005c0c0307550001c00c0541c10391070118515202d03000a1003000540e90542000092840 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 281870782 1250 281869532 281869561
    0x16060507081b04060c0809030f0d0e090114060922090201030612030c0b06010201020904060906090501050a080a0b06010c0b0a1e0905070b0c0c12060f0c04030228120305030f 76
    0x200002c6154101402d150084070a021110700031902c1d5001080940200e603810000340d40304401c2c0c00001c040071a4071020081c5400700c18002103004502c03800050059034540c0c00c80014885050303d5407030300c0790302400c001032380d15105809200842c030a00285241003800c0d6004842894000e0720180020390f9a0000d03143d2203c500d040241c00030b40d07042c01b218006850741807c540c104805100150030a038112000400312407443c0d00209100d0760b42d210402c10b003500c60140c02c1c010482124209440780c545214640c546500c448001c04d0400b0354800544940e010f0301e2001d0030140c010140d40100d01c0c09951350300040c181e1800302c100781401c0400540c1c0501c1c0c940900d00c0b0855101c00500042403604031600003542140303c41e01800e01804159222035103807014888206030100780101403a0401c00b07940500c1d860081e14266116030f0410060025031108840152003401010300c05112003500085c000c9102802c2c1c01440c401a0303000b48240500d41e02c0406103004035040b061011007a21041800140507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 281872032 1250 281870782 281870821
    0xc020f0d030c1b0b1303120203040602122101080102030405011121040507030215250206040303050703030b1003090b060f0312211008010b090402010e04111606050708 73
    0x10319403640d076030018107034030401d0700344400c00c0511100303494071580130031901c0d000100c3c1008001d40c03c00c010824041750111100607d81980061481d103810144000c2d1a00315811400365610382c000749800065400f1000408101c050204800595031a40d14190107540305031740907a455070a10390b24000c003c400c50225801108100b0003624021030508428034403c03c02842590b41c0d0251000000158075480d0304034500000710403a00d941c4000d03207150110203110308501065082c80405141005841c0d11048405407609070030310a848044500c1d08901511504207a00e800507803611030059810f0700340c0c1008225604c03c0b400080565120b80030300003640524408154164060000c0182119480d8002c11408003106003400d512540c45042500c0c1342e0007034890840129071301e501048449400e204140d020281103683c004581050b4000800090204ca4a0b40c49a83d40b41c0700d4664000c403090403a03901c10907950700c0d0341c00c4460b90b0510100801048035008041034903200003c8a2428141101084 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 281873282 1250 281872032 281872037
    0x503041130011103012c040303051608091b0d0f030905240304020409080f12060111011a0f01031e053c0c0c06090601030c0f0e0105040908090a060c020f0d03 69
    0x55a01c0d06d540604250121801d41c6840ca00340854140c00c281d907182c82c18400c1e070282e01c001c01c0d941028070b0000da41820301b143c4501040091000e0100c440e5012500581001c0310070940307141861100c00184403100c1c01c5100800f01000d2101d08004c140d08000c244044032800c540d1030747d580002001902102e0f000622400d400d1104000103401864558001c042e214054040340d4148040320030300b00b5466006c41d090101c584000340801c138403981e00c949211882000f00c4000e01581840300d490544089140741c8040c40340320030096241c0349920a601c440c0304490001031a40350001c0d6040c407180104410b960910b03244480403204882e440b05200c0c402155045040f075503192081000c821a6004000740c03510024401c10080d0148401d001c004003130091074480082d0010794510b1070075215070406540300f1644030104c02010401000c5442c100e40c1111019a80400c60600600c4d0624552098003180e960110510402051701a40f00c410741c1c130413510076111240509010020042c001c81c584000800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 281874532 1250 281873282 281873287
    0x201090213020c0705180114041b030e120f040f0803040609140105070b07020105060f0f0d0305090406030804080a12020a0b04061812050c0606180705030411300111 72
    0x44501d501d0b401040b4085200007030310400d5440e003001914440d10404034103070010703040c1c00500a008280391140b1000300100d80820100c001c80b101420000300c545080824166143d4a28052203024080b03149040c0301c0c004225560040040080c0b81a0000d000c0c000e01e070055408041a1407000104480030348001d6212901038510380001401d4844c007840407a8108807061190400007500c01d0840350048e048cc0e000032a0519040c2e0030702c4410450440d07110b104400c2640321070442c2d1900303110101c0e003980518005903544007030780201b0041d0140d50700042c010603002074000703074201c4081800500e6070b124205080c115854628202d0b81e0f0102d100f8054148011500800d0015199500001000d441c84549601e4118a0f84650700210300c2041e609001c21800030740c6c281d00e4281400340384d92041d4111512111403c0c044141c001d030704002000b00c03043c01000400b00d8107000e40c044a007108400014040034150701c0c0108031619400141c1204882d040d0084880c1d1202e20040c003071111155100f594490 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 281875782 1250 281874532 281874559
    0x206041703070503040b0705060a1109120109050a05060708010f0e011401020a0c09051905130204090c0801090804150e0f011209050106090911010503130303021822050702010902 78
    0xc0c804401424145041c4420000c0b030000a0007440a44000c0041015054481e54181003190404200910600d0380a1400550440d207184440607079541d24004e4480741c0095081001040c010000241c01420b14030030403040b501007040000311607108110603514100b0b640d0341c41c0a0082c1e081c100d4082c840510b07003540f0040c81035454421503500128014070465901e084251035411151040b50404544140c442d020000d1031240c00b18800c10100b1140fa04200314600005c59074810503003050000c0c86903403240011000c3c4085012400040c2c01000c0080120204e6458400f086a000c0c0c410703d1460140242003aa0960090340e0208003000061301600c0d07504c44050044030201440c00000c0b041c25907990440d804240c1c248210f0018180707500000030512503034103003441244110349050741003100070002c002c03601580528040a20707525042c00350710b9030500400f42c180c0080340c01031550030a5145440991442e1107000309541b8400c0c00e80100030b0b64880140413400d99410070400b03500841d4560b60603 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 281877032 1250 281875782 281875799
    0x705040534020727050f0105030106050a0302012102041d010815040f0b0702030c0d0504050a05061e031b0703030c0801140607020d061401060216060c0f02041515051b0703020604 78
    0x80800042139440c000f05200d403034203c6048850545020300b102010700018810b80c2070900c28032000d0702e000ca07888242031340740d81e0000f490102944200fa1858070019402c03540040c0a4042e100030340f883d6900c8031296050702c0441c100799002403003144458402d03448160031451080c050513004039080f603601005a039054480000302140070380440210b110400c1407000f12354052180304130b480c801c4d80c0c43e141e0ba54940303001c2007a5411250452440f90800b00854095680b18640c1d0415030340c02d06403490b840e6030342d9680440d01419500c2c0008018200020a80700309641036100f04944c01054451010b184d03241c490200e401400091559003001c3e003042180003615141c0409100c3c0c900c2007a02061800c8802020b00820b0400e074003e802603400145890249502c02803888040d01061400010a810b6074a80d0b402a80c880c803006070145030390300d86036080c40c000007400c10060700c8010860900e0003201503009205611640f500c4051142803410f107c5481408690b8800300ea4000380203608107030a24102 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 281878282 1250 281877032 281877059
    0x4051b030402010e0a080d090e0c12101503091b0b04060e1314091203070906030216050111030901060b0f0d02090111190314161407050405340207 64
    0x1070f41440301060011080d580c03803404036009448083c003c0c1421b00e034020b4025206c40340c103800146174501c240c81040600030b1039000b580e401c60300750401c0d03002e41d846a543d441c5a01103144c0109050b00e10744400d4401c103980582011092521072540e00a0360a80211940c3c00c0301030302d000d20b5203840c804101c1001400d20601608034140001412800c1340e101c03840143c012100300708200c0000500510410400c000140106a000204041c0845c035509d032a9000400209060151100785580400c0c00210500c14800b00d505c040d46c8a0000c00c00d00c52440c58082486e001241d00c884158202400070a4800381d202c2a40d100b1001051200e00b401100c80c444000f035000440340c28104406200710000c203d100b0441c022a501c03404e4080e0f0284074881c20300500c0c010603203d0400480c0710801c04504401d0903445210b030102d402201582c8030990f1611120704001032130340501d40c403038148400d000c6100c0c800c140740000038109a00d4026400302d2004c2042c01d000744041c03500f0250704403500030803800215004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 281879532 1250 281878282 281878291
    0x8071706040f0b030a05060a0b011815090320120c010c021c0213020702010305060a0e16050904020a20060403050412030c080309030c0708120d0b03010e010608100b04051b03 76
    0x101142440c10341000ca450700682d03170020358840d407001c0140522041c03284280e1075401020300c0c0030806003018040d210340500d02445103e2900e440e034429002d01c188201c003040d0103554084c4140c1550403101d02d124502000618803140314007298511f058080300e00040c0800c4404c0181c44002240b24142c0070404030070501850310404122b64800f001c010b80c0c1380b003c103440440b01e0100c01a198606800010115000140f05e00d016002000080c0030f140110964582d00c4403640c00c02e0494052031240031141c030b010301d00301e071500035001082480ca41c1c0c0d00506410b4001808403030007014000c4039488159030f59819200603001c910104018001d503180c2c0342c80030000790b0090414140d00003107680d61968952040710b4800003500081a00c0303030031400030700c0504020700c00c1030b004240f24440c000240c416407084250003d0040e50f5183c15070480d403000c0d08001c81c07521200b1300030040e02d6500c0180340c0d01d40905240d411201c03440d00a840700d05107050f102c1c0d640030300c18000d0380303004c400c100d44c0c601d0300b60341d20140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 281880782 1250 281879532 281879561
    0x111031809130c0b0a110105040b041509021f120b1018030803070314100303020c13060803040e1603020a0f120207150e1002070f0219030b01030b070807170604 70
    0x20b4000007080c04481900c0040211a10300c5a551314009030003000500214251041a4144414007010829200d050340e04207070080d038801806903103610180001d05080000a41002c0c440c00821105448490303000b408125540b43d00311b052145110503411210b00040700c5500499040150b5041340c490a41810580900952455059100d499026003504210341040c0000d0702c41d00c2d211814200750109642001840b083c030964107096990103520f64405a070598060645400380c03404146158104200400345801640c1c1da0310b0b1600d40004102e0000c8480e108040d00001030700490303034441e108446d00d9403269540c001000c140600200d41d0441c45014003182c0580910000700443e0741c508c01d0131042d003449d51001030f5690303454004909081c1c10078079017420f0520501c0540041608038690303048641c1d0443d40742106581c81e8546d001c0c06e69007904068a8850207000200800c001410f0041c02410a80c8840d81d141d50391040480f40d880071040780c4203a048602c2c001c9201828550007010b909480749 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 281882032 1250 281880782 281880811
    0x5190c050f070801020712020c010c060b03010207080c060601020f0f0309040207030e06031905100612091e06050106030b1c060b0112020c0c091506040e0405120a08060111031809 78
    0x110384146000c030302e038115510326540010780e0401c0200c0c41c3c2c500c4145403054006005d40091003c00a0060b0300005406802142c4071048458103503801c1d8115206c0e1b40e403044100f41c50701038540c40d00d591008100c451501611518081c032007910000107d0402402e6000029464031000b04280800313174001030022020f101100810480036540d000181d40709004241054080030724003171140b410b84501030015140550040024814542c0c81510b8982c0711031003480c0400c003280140750004981415103c1e000d9440003070348209081001a401082c101c840d165010300043c2c0740c0f1000c0083c1c10850000886800f01c4e914024400540140c1001c4000a414180310344003120802c403c00c240e85c085485840b0381d400c00010031070b040c5003500050b0340003200c10b0f46c0741c210410200701080e8948114011140b0743d00b400400601080020485480d404540c4503085403100c1c0c080e14054041001a00c0060209905503000109500000240c92241c01c044d0404540c40c2ca1610900505480252460100d81c242 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 281883282 1250 281882032 281882053
    0x151505091903050c0931020f0411040920030a05090f070612110703020309010c08160f1505040c05190503150f0106030e0604020f010e040e0309010f05190c05 69
    0x10710000c004601400280c129a5480300800008000091070102c04c07240308201100c1c200070320650040090740951440416400c40e0000400001d190000d480c1d0103414945200040e0070710300d000e04201d070091141406124918050384000c0030442c00440204041840021024070151b0081904600d02d01c1c1541c0c00d038880c005409041c00400d0300400302061620b0022460a003052246400c09035024022908101d25503800035124822400520b04100301d02c52130390207000840040341c00c0300c01c0c6524030b1900c01c122442c0201405401d124241e455041c1214024407070006030240c5481507502c41e074180c0b0014100030070081c034001200d0700e40b495240030000108076a101044103480c0304079507000070701d80d41c6010040110070781c2050704500d0401d070810186590003807000803555005981120384018280501c0c0048074100d1207950304641c1719003854007040001d14040000e05081d10280c0e01d071035032482142c8042e600340c45250041c8860413034064500400307074403030003a94101501c52401e48064411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 281884532 1250 281883282 281883319
    0x8030402061e1b060103051207051e010603030e10080a0213090f0902030c0d050a06020a14071110031404060504170d06181103180313030503090415150509 68
    0x956090b400144140020810a4036a003900c1d2410040381c844002e01c04d540c116540c40303490b00080038990200315404550b004c10454284a08044c007640382e00000c4000c005090054042d000030311003030340450300d0010000c3e180c4c02c1902190613000300750b4540c003d8a448440c0404000d600610210752207030010347c400304203c0824000e0521010b4255004a01007090303004050500d0002202e0901ca1850710f070b10440018400b00f100140c2c5500080016210000c0c4902603d1006c842140f503202d040f03002900300704006400d580341c009000199080f03290341c040040194115580c481c43e518601c840c1c440000c0c000340140c0c00072540180310f0025218418810084900c164218941e82101c85450f074105014000d5008054000312041710018444420b54500c04840fa00c030103400e0561141c82103c2d2410004010011902c000e00f10040002c280c40d030300d00b0030640780e0300850f00c4c00348207a0800c00b9040381591158881c00548078401070500416101140590f0b8035072003511083d8210759501e240080c681d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 281885782 1250 281884532 281884567
    0x306010f0e1215040b0705120a0b19081005070206401211030a120504141209010801050f0127090c0c1a0114060a0203070501021b0f07120803040206 65
    0x10f00c16146080241424a071035086024001c20a104222090110b4031402c0c940d000fa141d00900d0319100000e400e010b0780d01190710038500000807002150b0200c00003c12007400900940b20322908003082003251110310040343c4589054601030041c00c01d52648801d0f4140c0c2140b1100d900002940d10041030107200088203071214010000c0e110003400100056042d50046600c3c116030000002462a042c50528041c0501c401c11031201c0d20b40c1e540b840014104854003140b0038824400300100c83e51030760500c40c13690156000b80728260000702c100000198505004908800800d01610b8003205510034000c6400b10060230f941c06450703941c5600e00000c00001d988211401000709503509610b0300c20b83c0c100b41030f502540c030140c82810300c404401040501c802d07503001c1e0348198003100c840b0780d01c1640b244228618000c3e0200600300d944006442500355a5152541e2103100182d800d4850a000000383c464131000544107945810314011488000646800025503100d44000d010301c2c10301c92441100c0d08410b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 281887032 1250 281885782 281885803
    0x8011404110418020919212306150d080304080307050f0703090617270a05010e0714092809061401030303050105031b1005090925050306010f0e12 64
    0xc0c0e4001000080c0d414101e2446288a01c40000021524548103600310115001f0403281c100c4000c04160780300f04a28802180c6540406510480d44929620740494403035500b40c0d0954a0b000041003070810303d0511503540a40300d600101c605042d035407903441c2c52586500050020741040000c201c11030700003003a800a4403946009566210081d800d01402911300c1d144420b4860340000c46130104a00d4604403801c1605000000890918000c030074501680f800d401c04c0f50052965080903840001c0f1040003440e9800c031031480b0840710314000301c04148000964162000400d05065080031810f640101080d5203900035030a1000070074003969114141221741d00b111800410008030010010300d41d25010b024098902200606443e45405041079440001700c0c521902540c00f43c0206588a0b0003202507806589024061072124076104502103101d40e059420140100b0a6a40c070340c01c2544200c05480c803902040e1503015400710001d0064800c240082c80d0158000000900919492424444c81540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 281888282 1250 281887032 281887079
    0xd080403030512010b1c0e011104120b010911030f190e0c0111030a02070509060f0d0f0302060c090108071b0606090b120a020108040f050111160210080114041104 71
    0x40301240780f00107600c61010381c0503d03115030050248600c04081d01e00c20440800296600144514103603d40601506409110b55035586011500041d4030b0012294064090303ca5552000c59a80b03556a0800301c0300c02c2c841d0861340200600004621000c42400180c00680000c01c500798014420084819100c1910800040d5044400401059604540b0059401101c007010b90f00305604068001c0d074030700032846594030401000012a0f480c0d00c85800b04141840e010781410b00c1c983c8c441c00c00e00001c040f4550100c1c018844c110000302c01508400944a05050503034480400c0c2c0c80e1401c003194242c41791800042044408418240080c0d16841807500920707503510701080098008080100e55000a102840d16400000901c40140e07031000142d5030050380300c068841541203905000d4010060801002014840040c0d00d80035850040303a0059104c0c8210b809407642c19a88000303d40e406000e216560603c05854070040c0c0030318158100c484040d41940c1194107155880059050b06100610380010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 281889532 1250 281888282 281888287
    0x7050406030b09090d120f09050109020a0605040b070206030a0e16050a0f0e010603050403090816090509013b01090b01051504060e06250b061c03020604110d0804030305 74
    0x180d6010b0061151038002154011620b10749030340200e4070760b401c1d80303100005c005902d80e4000c40d45034590712940e00b0003030040041124401d41c0c038000d8003c040c0210107910901c1c0890001038175034401c000311400d451210403458208083c603424003d00f500082d04078001191180245121072204200b1808200c0c409440c0d0031086291505101007000b4a4000104502c0e9500c0184a152480d0312064111095458001040d6030343c1e0408642a250b40d400403001c80c0a1120204c0c0012100c602c80000e440340004100041d842c0d030b076000c9080f26203580b2604034a01b41180c80c072504207003292800b11a54240d5207000e00c400c40a00125003104d000b144107c501520700070040c0111304085024101e2800c0001c40f02c2d00d005e080141c040d0060743c0701680244035960001d030380c0ca0a0746681240d5040c07401500c0841650403901d240001000904441003030180160b104c250380b07120804a0741011240c1c042e005040180c5544d00d840090403400b0302020381207032070341c1039440014040400900056001e50764458 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 281890782 1250 281889532 281889539
    0x906081b0c06010e010b3c0406020c031027060b03030a17060103140c0304170a0201020309010c050a0912050708071206050105010306030305090907020f061905060409030801050d0809030303070504 86
    0x900765013040c0c100207400102446680140090320b0700011000825036440e105440907000d0030004040010700400d080c0d003000c030780051680e030005107012140ca411815038900d11002c1c0c045104544002d00d14000d0750342c1d003800c1c0b94845000c1d0300009400e14003940e000b0401035222004645075a1020851800182c0fa40314140308000d103403195207400c03a109180c1449a1410041a14001034012f41001400f900000c0400c04100b8100c0d003a000c01d40d41640303902d4480000010190003504100e44440c617550a01c504204074500c00d000303c60840c0d41545030000b2050801048804d1102c02800841b0a44100100410f0b5010200904030040800c8860342c001c4555a2511030103072001070788030a0501d41040e02c04c1c400207400c501034079036101040c0d440101d00e5840b030404038130b440d1440c1d0110010b40103100a00002008001c0301c81840c400709074080c00252120401e1004492200c03402a00180340c840040c041307031920381d554165190107141514107001c050000281943c1c8141c801c4008940d0004042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 281892032 1250 281890782 281890799
    0x30b120309150705070312030b0405040c0503100c120902010c0c08030403030908011a01080705161202010c14031f0b0301090b0a080309030d2f0304030302060f070906081b0c0601 78
    0x1441c2400c500b00440c2d0030702c442542d5603a541d00e03460000030b020440042518100500c00da206407800d1314000c00c1400103041604143c00001d1480c0142c502901601d0716030283c3c0055030094603002c5c01603644859442344c0855540000b0004150104c0c100412084071801140310304240d14090301a24001d560f40c1e1b491854040c140c03000590000d0f00c26410502041072401c4070b032902110403002801c1140082e41c40000843d0140325680a07032682c900114030310010300c070100200300d0701a8510b030001c200c16441860182c072042c0302d00585101304801000002c40906c80c402180318144042c80c0050740704c6803500c607803c42d240c00980103405046d0351612414124600102070b41c0060807000c01551511001101180e103a40c140c100c001e00f805001c10b1075100010140501003120829000c00c0000210351102080e102e901601c27080d001449108040b440e1810303201044c5001d6103480c2c60340c068036840c0540c180d844c110024281100d46e00002610360380350046034001c142c20300140300078003019810070000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 281893282 1250 281892032 281892049
    0xa050105150f1203040b090f040c0206070e0a0302030c13020c1906060e0f04170c03071109070f0f03050a18030c0308010b0f040902030402060d0c05070501110306060a030c030b120309 80
    0x11601c91180f980c3d40d643c2d4540e010086405a500c0e081c00c883c1d4800e00718010402c500601c800e2550040d1410146845407039010994501640c0075580e00c0325040403070420410103203698000698103401114040c241460014200c450311150004058207000d0300c0341c00c840c10000700b145102c280c070b00342540450800810b482894060402011014410300307050303460090150000f40002c0c03140300c440c50b076000c0582160042c1e0b4189078250702101d0380d4507030038500034414a2a2040322405412a0000719440e5130041c8140441a507a80d0340b002280c0c10500c0b0218068040130340080301003a0340d0004508212407100703100000e00e0082d103480081c8602454020031280050f446840e6a002c18060140d18014440407542114160706015803282c40724000030386144521800f6004161401210342406900300c0050600b00340101c0080003540e80451030411644803c9400b564842410041410411300070381c0b182c013450315140390014407602c80e4004030320800c8008484041b20717800445c8904807071811000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 281894532 1250 281893282 281893309
    0x717060301050f010506180a061d1804031b0204060608010510020d1d03011112091b03121b0604060501090b0301020702100c0305160b070f0203030f0402040b01020a05010515 76
    0x20040c5180000d078440300b2443c103010783c40c0b20310390016414020075140b00b402e0700c3c010300003044009015907944024000c0c00b1041514020240800700b480520b14040c140e081448102d071030b48010315520b42da011101d504001110100881c240102240982c46621074100602040d8076101d03400c1d414581000300f07170304141115000b19403190308035490690380203000ca115001c10025544c00300c600100040d000d400d5030380f0304030705000000c02c080702d001818a2074240902d80c0081a40e03250081c072044032841a5490450703030f41503409039607811014601a40100202c0f540216030b0240c2c0117040c0e59050070f1160070703602506c0560712203006110140d018812140002c00c120f00861502d443d56011809008c0141810020301c0b585441910503d8058000c8414004d141041d11918500c0f52420f4981c0c3e40c0e060319403000241c450702203901400d00020449000f50640c06101d603459a403642000040d00d0883d40d558114000c50030f11703070006102406404e0040465001100e08421068140311810840d0744 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 281895782 1250 281894532 281894539
    0xa11120102130501030e010507020a080c030f03090106050f0102160b03040618050c030c0406050d06050a0b060c0304030c0e0112111329030a0803040605061f030c0f030b0f1215071706 80
    0x1010700850303540002e80755103410340c880d5400e500d0340d05c5461402c5c15070042600500d404fd00c00003c001451006612200503642d0858501080c22208001240e440441150300030f2400c800c11010320503504070300d0145600c07034840c103000704441409009100c081041e44030104d415500c03101e0f0141c06850284a0008100d1080e60b0810a503842c01c0001502a66210f401a1a040d0b8410203d40c41c1030154201e100d800c90060f120550b600150924107a0360340c0144001d41e00300740e42c2e00c8041011a41d083d4054100ca8400d40400700d40c2090751200000301e00c1c62003801d0b83c032184002c8001d8071030703402e802504414461481c170304d0040180c00398850054040c001c100c0f031090b08800c3c050000600c00200b5288c11a4101e40700040c2035172030300c000c240d05440b0312200e240450f249038204180c80b50315400010014915544910307044441e0700090307040e07850a0f6589036200c010101b00212506203c0c0691102950650848a0010244c41c8083d04c880003030350729000080780452803002c03d06a041d041030300230744243e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 281897032 1250 281895782 281895791
    0x1715060906130e01090f050a06110301050618040b10051218152d16030605030d181208090102060f0f04030c0503090307080c210a11120102130501030e01 67
    0x841c0040c0d510692140c4032074105a54910085071900254080415140d00003003140c06a251410900e07070324480c402c0c1c1106c0640c03d125060300c01908640540703040301c20141a180c1403401d041c020f1103c003403007510765540056443e84502c1042d03840f8411450100201d4a555aa64400c1c40d403400e54468018440c010302c0c9244500050442c8000908081a9100180c1c2c070300c2548800c50709070450301400400d41039208445004090602c42d5004140c010f107403030018403100d03905a8106400760b4a00340300d965819041481e5140c03509000300c04240d00925a4030141a05a482d11040c00149410f0603080e140c2c4070010516170311558041103034030b80001d09507044c20110720b031015001e03451500c024402000c1120340990107042150400503a0030701507000b420741e0103860f22042070300c0d45d484051401e44d100f0414201c4824280e4200800d1580564980700903080119032500c13020388811414002d1740c3c0140700012003082450b02071001e84408514040c1c00c400d440d241c0000181030b50b040044101c800d9160 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 281898282 1250 281897032 281897041
    0x41506031b0c08030604180b010306020909061002152a0d060b03011202130605040c0f03050709060804140c030a051006140f040f1b020106030c0603022a0717150609 72
    0xf0800ba01e03840741e01210701041440c1d102407001d0410b9080c150090152425400110400071b003a00504000001a17070622129074404041151561040724400301603003006140b00c1411109540c9035901a82c01110a41d0781124200b00d0142110b44810019420f9008a1101c9080c401c42c0503400040c80c2d1154210b0031941441c80d01201c1c0005080001e101d007045000441a510042d00004e000b044010000c0080f001e010130090003060364410307400b0001c0c1c038103400951641d0080c4001c509952442c2d036110000d41e6181c0d81c2201030280c01c04900ca1911a18440584076501005141d0040b4880c2c0b01904000607118019026514290046880d210030400504a60b4031114031094542c07004540103e1904001c48801d001400641c042415070284002054155601500000201ca100d09013843e41e40365174103412030490207091052210707410340110301a0a0420fa400040e0030f803a0030701c26204030542c1e418214142039a56840c0c001d1039003000e94541140302c0341084591b03200c04181c40340146031a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 281899532 1250 281898282 281898293
    0xc0102030d091a0403110c150d020c0708032802070317070204090c080706270e0403210c0f02010603030f052b020304020306100e0f0402041506031b0c 66
    0x500d074074101c4841d03942401c10180110070707403490040d030721031444540d8a00381800c0003481c00140303078a880500e219035400071065040c428812420b1f039094001250415016090310b00180d400140042c03801e00c1882000705460000340008c1c00c1e100070800302a003058031112407074281030a040c00003605540181001300041241c6c06154402d10142d0a02e0170350f00d5516200150052028820241050a4006021030041000907819013034a4194039440804004801e00b801e031003550b0701f120010024445410440203c0168401b0340280c401d0a12003228403180140c51000c51004031927070003a944508010f5a5660445410203052413603100034000d290854601070315142441850400b0481c00044804881e024400c0b501d8500c0e0310441c047ea802d00700d054056000e50070680742a40710f405000045584402e41c0848a011151242401c001d83e5a982103c3d0b80b1503400200240c1e0482e4070342d0007071300c0360051240750381e4040d01c07044d203001a2451042c2c0102c1203071044402000203100c2c40282e2040843c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 281900782 1250 281899532 281899537
    0x2070c0914191a040c111b010314060d0b07021207060219180303320a08060a080604171216020c010309051002090604030c0b040302091005210f071403060106020c010203 74
    0x46060360702154200442d0011950740002c8550f07110103008481943d1f5090701c114a41d164000026070b801e05c6032842c000d24840241009807501a80000e07010101000551106000f0b60700042c0c600560301e4100321603e036101c0c2580803110840700309900080c0c2c50543c0381e1004104010a6261a10005103403012000008d02820381c00090144004000040d201c0c82d641090b6590002c47c9806001c003860352114403c045070003020b280000b140d440b10010b0306074240841e002c0100c0307607000300810098456450700310010180310080b8903215800c11084225000440d285da025032407007243c515600c86001002030411143c0f2080741e04260510b00c0d19000b1910000e0710b81c00c03061580800503500c1008400040c9076115a510081106052100c0004c003c00e100003c0d00c00caa0090b54007051658400002c0081c010250260961190781c03074150007a054010703980552902200d0007142da511801c0d4408a103005d401c4d61001140c440851680304541c02c0c103110141c010300c9980001d010100b812000030b0b4490 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 281902032 1250 281900782 281900831
    0x9050c0a0f180b040e010e07020102070309062a23010b060a030b0d0f0515010b0a0f0305060f03120405150310031b09050a0209040b0901080303060402070c091419 71
    0xc602c039500c44502c804030346240018188550155035403643d41507100c0942c4003d118240303041450000040740d2500600851f50345c1e6a040c1e4880d01440d007004e01c26286004640d8050042d803507107200304006903e9003458034519074018aa500d2050103908002c0003a180d0400600300b041c3d04148201030a80c6030001031340c101d580715007004160600782030003050070580c03800d501411043d0304169070002c0c48000315a15800d0b4402d00800c040036030700c840c119007052140500c140300140c0c4d0180540c0001d40300f640320710303000207005000401c84040744000030b01e4100c003185281d100342c000050802651a1940c44048a9604c0214450851614500240201000784406061559120303610580d501274450380c100035040e50b650030800360601855540003500104000d41c0102e15048803d50b06180c03ca000350704851038100110b1540d81d401d400d02001e5000024100c41e180071003e004200003600b4050a8440c245101d00c580c06071400103c41164812800152418540f82c011614076013505a044403015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 281903282 1250 281902032 281902037
    0x180f070e010909140a0308010302280608090c03100606120e030912030d020301060801050f0105130510050f160201170c0901081003051b121504060c050418050109050c0a0f 75
    0x42c003c0e50900c82c1c40442d00700031100c25409400d0803a4100760300001c1e0541600c0c02901c110311210303070b00b40c010204413010040c0c81c0c440c88821142000024442c42c08998000004016a10090352445c00300b407a10010131164403900b5283c103018400103600c001000850120042d0a1106401c80780040d901d03403040e850014082d18090441c9600200200200c0d1210f0448178002c541c0e1390b944403402010702000780501485540c0703034240c0b1003943d8490b400356400982c0c100e1001c424240b40008201e1840c0204540c01c0074480d06200854000c4924005014403100340e80240995120341e10005124030045111090040302110602c400070f2070700b00035038980d800c0a080c0b1540c01d407180f20130040030841507880201944101e280c2503109000c640040c484410040d91440000c1045501e01364640c060320f000c00e02c211441e01c00103004130b401c5070045603c0070800e051a600c0c040c0c0719421260050805951454030300e403140e0040180c000f10f840f0300d0368040150340d0180d00b8103110000c01049040a21500e004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 281904532 1250 281903282 281903291
    0x9050a090515092412030d090312020406090e01170a06020904060b1603030b04050601020d050d110c0a0c090501050a050f0301060b0c25032a0e180f070e0109 69
    0x3030b0300e01c246240200100500011043c60490b00307252290603060303007a00382032500c520450780a08101ca1485125050100070b5400c010306160008014201410243e0410458120110854040e44010405462582d03181d04d00d0340d041c801c00d5a46c014ac10b07030000d030103610344040c0e010490b9404a0056141c0354440713070251b030703591050303001501401c2550412004814001400d40408449101181865100391814041c00540d601008101d450403901240503801608a0b4103506100740c004241c180701352440069500e01c400002c00142e040088011f00c95444003802500b40200100c6d094020610004244115818680810018000761145c640030700507000b1344c0c49207960300b9000301d80070300030040c00ca54455145503c115590400b0500018881d0001c01850741413132050300341181542c1e0480c90300140d895901c41810403030f42408281c40d074015014440802c6901d025a4124050141d0f10410314503091584107035400c2c040c070001040401e510803102042065001c1ca821411100c20800001c3d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 281905782 1250 281904532 281904541
    0x304020d020402270616030f090807060804060c1d060918011e0f1a0a03090f061a03120703050a02070306050f190c0c081e0310170304210f020607051005060109050a0905 74
    0x200c9c0407699802c4251240a012000300c2c0c0d0a60180e1081c0c4210701455084c4030740241042e05641d00b1685508500c8265a03036094851a420818014079190f6009052a401881210300c590008402a040b041d060b510210b154141145182c003680c0251404a1410035118036101884103612002d41d20064604004078003c0c403c13a010780d1080450729000282d4581194039032401400601c0002c200e404003021b04244201c1c1030500054401021054002440c42d19035141c400b5107030f030b4110f003014008611600c5408000101c090160340e0003000c101e05150071500f41344d05810460202c2000c40740d02545031440c403011341c4d51b20035800400c8076040385080daa43c1ca00100009940301200501d421115000000d2050402e4040c41500480715007850b1514025840c0f8040c6071207201b14031030700c00071200700ba0005002d02035580003254110710410041c4080c00c2035a0220319180c1169005844035040454060314100c1c0314016a0390047d000d280071070840d402c220003d180d4143c18026250000e903a0380004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 281907032 1250 281905782 281905787
    0x2150f0402011d090415150509010905130c080c01120c08070f02240115020309031509070e0708040606061b080304080906030c0a030e01020406080c0304020d020402270616030f 77
    0x200f42d10f601c00340100d0854500b0b4200104481c11480c61a843e00b49400303154801d14207106003150a4803401440340d09141d2030400f64070003501c000b600c003404101c0039180c01000500c4052120008041d40c1000c3c0c00c0710515100050200e00a251504507102d007021945c8080e154403034201c550040d25420600d0842600510807454403030800501c0d5058500e10103210b2004103030461706412924041c18003580c1c01c0801804076101c0c050001145e8059000801502c00240103444141d0300182c81c4c2d00f00c814803a6100c0104203a070b402503940c18007046420b028001880818000c09001e4421fa080422089004406494162541c0000640b240d440800420204000c88089501900c4010329803922401c140c04880701d181c0c0860a50f00103c0d03e4080000c034221010300907034003161042e881c0c0d0303851a40c1d400c825124a0344020000c9a10542d000e0840300140c0d10b51014040a088800103140307a80c5134280d4540559a00c0302c3d54622411060048181001200740c4680c140c51f8140303428000701200817020b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 281908282 1250 281907032 281907077
    0xe0408030f07110d03091104020c07291812010903091503020c0d050912060702060c071115041a180118080712031b0f0303050c0f0706060602150f040201 67
    0xb40c2e0113030045024542c14243d0603005035001c0f81c0642c001080425500c03041000300e2055940e8043e890704141e40401c0403801c40381c2483c4103481220b40c20344071481e4032a044000355206000114039048134403082540380c141682800c1d4240c0100008000214864601a098043c0c51142c0860500012480600584a07406444030101c500086519180c09104040d0098014035209030040300340e4129551500f600003041030084003160060001f9484070500c0c8005680280c03425030b100541c002c08003e0383c0c0c07281007000a560b100064069100e81c00d1080e680000f800b0444011419a8207002480340504510b000040784030742400c2c21040d04510315400d11840d24654440051030188036400118202c41e000040541482995500000d5150203c82107105035402c501828940200030100b0019000b40d10498200d088000030030b003031a99118a070032071540115011911144c50305002c1007502d404011030501150340c1c0c0d4200505260518070080700c1c0e000280068104980404c0c007a4844200a09 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 281909532 1250 281908282 281908307
    0x80313050a12020105061e0d02060408060a0b0f040213230904080a020712050a03080a0f1814010902010c080304061112100509240a0503031209070e0408030f07 70
    0x16214032072454145810803500400078000954203000000340c46d454501130500007242074036441d005d070401403403e1100851040004a0700114200700c0800c0c405410840940b092001000210340d0030446024080155200c0074014016070052002e8041c506405140805950180c00400e0002ea88141070065400b083c84900e07800900901c24013003400302c0017008243c0030840741c00700e441d690b80d105203001141c4840d50f0080c115421486418000901c16040c40b42c000740e0241c5d001c201c040e5a0032558007220303103203050081c3c480c1804c00039208001c1c540c921100412041070080212280c0d60300040e03c1c000d5486801480300300004001400c200346584000c1d55007019415031500c648548001c0703a003c070700a41e00c800c40101c04440c0042c4500c1c201c1d00c00b51062140003030404402011001c0c0718540d801490380d40e40d21100d03419000c1031503241003018095803050010121380b01d05000741c995090030110f411459110394510200004100c80b03808a0341c100c504500c0c0d0b6802c41da184541194204071050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 281910782 1250 281909532 281909543
    0x50309060a050406090b041a0a0306050306070908010609151701020f0301060801080f01051506090103061e030b07180506090102010b09040803010f0b03040507031101050c031201090f0c0c080313 85
    0x6070841140d50300c100940191381440e16444903507030322070350b80c3c01640c021441461031211032080d60362124080c10010b05401c05450402044094640c00040d0514800b101c0c01e1f80000e141c54030030445107000340190230090980c0041007000c00b0002428800b40390303050003031180c17406032001400c8000d1801d5045840b0341a441891315102e584684001700382c540280b06004507440340a2100c1008038040c481c0d10700840e0f0036003a400c800f4400005001040d00b040042906050707580c040041d0000e4400d0141d212114104050310620782946090a44184090242c80070044c00030344036640c265000404a0665a00b1101c8688031b00801c00100d000d88000c12805e9005880032061000304030780103003e107040c4c0c0c02003c40c1d10001911482800a60302045502a105a21080041000c078245480402c81c7c0007061410f189400f1200c04003601d154055616401514854001013040350494480c02c824120000d40900c10b60f01e80f9103000382aa01100d41c045e103220000800b0901540c52070701c089a03010f9104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 281912032 1250 281910782 281910787
    0x1002030d0c09061106060906091b0313030206071701031502040b0c0d0e030c0112020f0c1b0405070f170601090906080a0b1810020c011d1b060a0f030905030906 70
    0x2190040c8841c0b10b91141001082090040b43c66103980030075010311036007020f4100c00069454000304070100b08080d1860503102164101c3d2143d464506001f188600082103407141c20301b85a00d0001c0c5043c0c4001c021004110185c003541800c04400910541181e03008240312807100300300400300c0d0080c803030341c0c0c4264101c800008051594203c08611100015859201c80369400d4601040c5a11012003130201d0780001d80c1d40130720900030320841e4050f1060760f40b002081c5052590808003a45424031403000035039128400701d260030882c6040c3c0103480c5d21214520300798212030055070001e801d450300040b111108071804400036126034802c0c00c0e050002d0200d03007810300c070840e0344100c169140c900c400c1040d50340c0807000d0009032180c0c1e80c45000c40e200c038800100425011112840f02402500080204603c65494038140c0c40000b440003060089150000c2c003400c84001d100040c0003040310425003180c011441448030416643e08440304ea24070080c0c0742030205848800b071414600350301c03602c400ca65101001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 281913282 1250 281912032 281912051
    0x405010305100e03091302070f0f08040807060306030b0402090711160905090111160f200306060f030c121903050a09080111030408070f0f030e0f0a0302030a021002030d 74
    0x754805244005000400455500f04092a00c0344216088250020351024890030780c1e090507030042030024050710b80d01c00840070a40e200d08080b05090819903005002007414480103e051060304010a0035040c10030080d0b2840d6104d4251890040001c0e2040c11100d00048172140514401854071100d982034a040301945401c0002480e81750080ca1401490180060210f0b10b052240000c11944203d05600b007646c181c66150021038480d00031034060b540400088002540c00a50000003c4001840e1045a400806052420078010400d40c0f24103410301541849441c0815501100c0c4002d8411800c0081419106881e014294102c42c40c24608010148203255000700680380300300e000e542d003c8013030b5559803503617080c1d0b80c00e403c06400c8000100080b03030010380c5400041003002d115003411101112562903260002c6c000440c10750110b01c05185c203d200d46000c000541105001b113034220412400c54020941e100d201040007402401000011031a55008009a0700f05014021003402040f00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 281914532 1250 281913282 281913293
    0x201110a050619150b120c0c011814210a0201020418020711061321080a0c060c1b02060d0b1c0201021204061d040b0a0602010203010f080705030a080d020904050103 72
    0x62142c0c1c40303003c4a18015040030b1203941280b50604a032804d20a042c02c0401c040c440d5005000060440701e2404401c0160700316546e030a004422201721403a00300d4005070b00506001203510044583e040d03580c0c0208800704852103141c41c041a885288408103502d07140c041400780e00901c104e030030001c08000c100342c0c1c08411603032640084c0544c42c4151400024084003100788045d60103200c80c00010038400c200c003402560904808911303955130104415200c2e07038864540e000660320002c0c00ca8001226403e4032414040613026841032150580b8002183c207225402480c40704000020082c401c003800104181d4012041e0410440403000030140705481c191024003020500c01c1060490150050724400d0001c0105641902d04a0300d0a8030713050f5191a04c3c1c44040b02c0748120001e0f507540a5a00d810b0b0a029807030720910100130344003d4000599950410800e03113014402c1e036108030a181d01038041440329440100300000e14030340c0310010a4407078045080e064003a0080544064005207414000802d022 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 281915782 1250 281914532 281914561
    0x2041214010609020313060f1d0d3509010f0e0307200901031217010b090a0803090f3304170c1c020102030f0408031b070f030201110a0506 61
    0x40c4803034002c0290719039821441c4213038002120f1035a10715110101e8200414665000360100c0c50a80c1c0c000103807403030045000c00d150206070329170300e10300d0b80040c254840303a50300321503420034454041d182014881008103541e07014403620b01c442000c092400002c190200740035005020098a000e000b40b1610301196549941c0b50070514003640c4480d00101110f1507c03903070800f641005000a007003488181e0031a101c0da180c2c100da40c8003070f10130040c1c0705a004590002d920412406080540141590342c1428000c0000548144d0020344007504108010109695884001c1c0001e4005484580013a2054140f07600300b044030318015604014848011044404500001c00649804910340c3d609030b0040080b491342d81c42260031154028820400e03000541407140461880036205204030392401d021005181007a41280d03010501c0c40c3d001081e041184940c0c01d07107a5030b803c400c01c00144034840c5010302007622a001440b000c3d050051154000d84094424401020400d07041001c60b480360074400d24154099 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 281917032 1250 281915782 281915813
    0x9070309031803030c1716050c010e0924030a061b0305010b180105300402030c03030a090608100b0a081b07030804021201060806010305060421021f020412 68
    0x981c0b61405801030030380440680280ca0305a80c07003a461443e59034132200c00c198008103c9118402c2805002c01807508003140402c1540b26001800805c080d14001508480e0300d603860030700c0307140800f007004180c00d1601103100c0c2030045040300d0004030003c034000c02d0401080d0314015084508000c1040802e001c0141c11001c0c14246da0380820083e070303071000f81d80424069070f03036180558050840004103540c0714001911248402550030070065400800c0110048186821003480d83d59000070401035186c14449009614400e8000d50710f80024030400074007800c4540502000c1c002d00b000429070004920042c600a000a03010301603880c0311400d0f0180440d00c04031168407003164540c6c643e04030981c625050340d02c800da0540750f8050b1030302d680d82001160005a6800c004541d03039a10001104c4804120780c500030350282d07001d000681031506110500b1104a1103070203020b9898411000100d0340024800d000303155440703500c219140d1503107810019100e5a0b00c0b0301c0040c0781640b906401d0107000320100220 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 281918282 1250 281917032 281917037
    0x408010c09120201021c0302040b041706010902030c0703080405150711100605061e0c1c0e01030606080f13080a02012313020d051002030708040615150507060b0907030903 75
    0x110341d9555003240c0080c800b142e00a0068001003101e1920400540600203406140d0030054200344c1c45600310045500300b540202c11600300c84021094990ac1408914003600200500307600e10303e8072010103440e0b4821b00c00000d04205030389000906101c4c0078041003504035510301e0554101c0c05c20840c01046501c0044417101c03240100440550040707010b1160320b088903400340c842e50078500d41c1c4010708a04002c1803d000c0071050204400c0e4904201802402d44008001200861242900000a0105841c4a04c0c0f6040c14035005081c4000c58206c4086030703001009070300440e00c582d280c0c20f02c0724a180c00030300c00904a240204541211503010b42181004000180484040c2a072444840c00c00300c81c20760710b03600c0f01c1040c0d235110005030030403c40390380f0f083c1e006401300c941d0106850b440e0800ca070700407a600000144000140002c11002c4c3c0949240c03007040e000c2903c059410400b091805c0502c02d0300341c80c24848001009800c1004a40155442c95001000d80b1564a00742e00081c000d170800b0300c0c04400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 281919532 1250 281918282 281918297
    0xf0b010303201b0307090608061b0f03011203030b040903030b150403122708010c030605040b030c0906040b19170304080c06070303020c1b09070302070f060c090b0408010c 75
    0x30310301011400e0542d04081c4200410114500b450480f941200320f98065426001344100440d0101e20f03401464000d000c06001006030307103403011541c0040b010140c0e0481c007403401003000d04030180c41c1005481c1510b034104001000c41c522840c05800900f030403014540c001c2e08250b181c0c0c2c24540c05900815240340260354000003c1806038035001c00d0721581c0401080168260510030fa40c0e8071603800b10000b1049800810503400c231a518a0014003125880b01e0720b903a445000da072001341e5160007400018101618288101c5035028002030315160128180c900520ba00320004005545a030401022114090034aa001c040c10368189800344803d4014407800f4002c083c8007504506000040f03504481c241c0018001e4080e40b041040b01503401000107030101a028401082c01c1c203410700107180740d41c800d0411166098414014014140c00007000c00d418144103214032004a8240da807003100d11940000002210200d0550503198400c00b5000001c052001141c0400c650300c0540c8010450590b5444205 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 281920782 1250 281919532 281919557
    0x13120c05030105150102071e050d21090303081302060913050411030313061413090e0c0a06020a2405091e0a0804270e0102040608010b0f040302100c0f0b010303 70
    0xc1030001304843d4010780c800b002c1000901d220000030220072084920842005548800203000c40b5440034041e551070410030780c0c042240c010705a076050244d0441c00e00c040311600c2c0d0340f0041c1510343e00418400a84030b40210700710845d1345443c200c035014540203064010380203105201c58001e00d01243c7c111206241505060300910700001038030070403a010320a04e050103080c0301c0b0803207010941c1111210b10300c00234400744000e0303514180d907000a000c008400080950314500100c1c035140701c210540b030003101845002e1040c16404107443c072859411003100402d056003044402450080301440888142c60312060ac12034038004078284035150322420313281703100080403092240c8404100380000c00300c900412081045100c01505020b4125100500206d540c62241e00341c02607401c113101c5891541d6000030144a1310f0b4110305a240074002c0300e58070f1401e04400c288001d40512540c000640300f0320700040300900c82032050202c444110750101e0903c071840c843c3c1c5010a178491007800100c1c04540b0500040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 281922032 1250 281920782 281920801
    0x5011e0815061902070e0411060f0c070e061003091211030d0e070e0a0c0203040302041805120a0906020331030c030c051e01021005090c090405060702010b1504090213120c05030105 79
    0x2e8041c030381191240a6a0780d92204104665110355112142035800f0300c8142c071802e50611410000703741d803403c143c0080c0b03460b5041242d151005106501810700d0700c0480c0022601071030190001071000c2c00d112444a541c00b00c241d03e58090005c80106450030201041e0b4038039804101c810803074060601d00c03021500c80401c2e41c0181d841f1920f13450700580c030510080001d0314203600202c031081e0f2284040820100e103502c80504010b42400754500c40031000400030703180c43c0d00a130854018001407004d141002900050400c08940410100041c1403500b07486050680303103020914002c40d400710507100002d550745030240e0307000c80034841c0c0d603c1003648603640001c4041104140d4a4000140d01824004448801c0d8400a10f0080c00783c5c8200c2c407600c61168100d0f200c50300054003c0d070103800104024070340800002d094a0603040000c4c06500c0c003191540343c400200d401e85084d02c501c6500540c03100c9000c14054000501988201c03000c10780c04032070106004181c51010705035141a0000e00a640e03804014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 281923282 1250 281922032 281922059
    0xb01032001090b0d02030703140708010509061c020f030106080d0c02030106090c0806040504080906070501140109140106051806040b0c0d0305060d0807020402040b0309031305011e081506190207 85
    0x142100243c0400c06003d10181d16030003190b01040717604000440011040801d030620604035040d10100c0c80d003100500051407c020380c4daa200c0c10448804084c203243c208051188400c09100900440c1d26151b620751a0350207401c00d40140401004566524601c03010041401c0d9072044241c0c080c0d440c017070700403441c511a8080e40c25884143d48840031503494100c140801070200130030940c0c003008103003c0341705180c1d1500010403125014000119a81e010201141050b1030183d000110a5140c0800c08200300d8502404e541101c65504000c2d444001603e825580c1851201100c0d507c0240003401003024000100a4003070710300b800007154500700e40d03031030300345c088490559950343d021452044d10000070350120000e180140c805400581401d6481018203d00d030003c1d185100550008510140c42200c0000307028001c0501f403070080580c0200880740d0b50701c1e81c0c411488004000300c190010b40b40c100d1503006000c00c004007600041d50b900b507140602e2203603030f40d083c09100140214080002d1a070300c1d0000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 281924532 1250 281923282 281923289
    0x6200a02060f01090c0f180305010c120b03010c0c0f1a070521091b060c010212040512091e0103090c03050715140409020304290601030b0619080907030b0103200109 72
    0x100d40820303203a07403102a0340e10051f11829150000200d0404000a03200380034148030019207032104200400c244403440b06540298100034026032405038501300b03903503111405100746074000c900c2d419080354034200040d10702c0e203281c40703100451180c0c0c0512180c01e0b4040c0c0104165890b81c0840040c81006060012912400740d500702da0315030000307000080c261548000c154801d2001130989241403112a415030980e0004402a5104442d0004200c00d2107005c1c8140080c0f5503810041c01d00d40a0071000040180e005849124208048c1101c10004c030f0b40241c3c0070b03090007900248400040340d41d904c1c01e5590b0303500c51b02842d058854144440030f4228081e031944540700401c011854141030500360803500a4000810a83c0c03003030103941c00c000c0400454000d00505926030305c0c0340384072403420740009170a84581001450061504110f081d03841d03102260a802c1846041c6058003250f11164030840c6040d15503040580605c81ca07400000c10401d60258280c2c203c5440608010703448010401596a20541e10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 281925782 1250 281924532 281924537
    0xc0105010e01051003090309062105010e07110f03030a020d1107060c030b030f03090d0c0e0a02070309052b02210106050f0f0a0b130f0b0a0311090a0306200a02060f01090c 75
    0xa1052190900602c804207054880008810f01035035210080000e40e4803cdc0d204a6450f841c140c1441070040d40004200348000e5500010f1a2221040028681d1b91100070b001d941c2444d404240c20516582d50703040a600340c1c0c0703089046520780c1407c0c02c01500401801c00031002007850490805117070300b004204004504482e03009075003459800307400d100041208160458940c0300c1540042400c041409205005201c2c03400010b03111030b05490040d000b0300c000d4012511800c01d100801001006050f25040340310342d1502d5402c0000070920100310f50801c0301d6402e02c00c0e580341b1070404080d00d0781544158100c0e601190144100001d01061064010349104181d40003200e05d02d007030004010100003890030095424030b001100b6503800c10501803406903000f02c45040000a0807803400365050149108008808110707500c2c2804100001d000c45034140701c02000075454040038005450403001c6401c02c0c006400d002595075140807002074489504407028031081d5000d20000c0f03455a850b1082c43e0900c3d0700398 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 281927032 1250 281925782 281925797
    0x90f030501140f01052824020105150a030201201b1e010e01050c0c1503091515040e0309090c040608070807050703081513020a020d020114011a0c0105010e010510030903 74
    0x180311400000d24200c241b1141800240c4000742d90500444c2c00c0b03010b02c02001c00c05650340c81d402e1001b425204090040040d035001c0c1c02e51520035540f2140c65404072642402e02d40c481d4000c4080c00241c0400802c01444c0034000c52170b2500c4200d120b5010989415012501c0101001c160081d105011030805589400030356000003c8400754091001000d0140d0f08404940343d039010b50000030904841c4101e46000d100c40030051200410701080f21030304a03600d4440354400d6241c01d643c8010605222640c0c18030443e102c0a50b0040d200e0306008503010100c026100d1071061404000300307865070b40300f03105e1400000c070584c00242510f4803c1c0e0780e0b140640b0f0f0558409280c03403895101151561000f0349002c001c591514048a030303940d15030003005243c1c45182000340c3c584000190281c02d00003117181d20300640e41003c0841c0408822151075505403820090034074904801441c1c01c415602840c041203040d076181000218070780b0440402c05040380c008a55040e5010a060000c6003075801054005000c11140c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 281928282 1250 281927032 281927059
    0x105041203050f07080705150f091c05041a070201090803030c07020f0103060e0a0e06010f0302031c02011e02090f0402041d0a0216060e0f0703030503010b070201090f030501140f0105 80
    0x1d03002007100300c43d105505030401c206901d824005a1000d8000c8440764001803e007011002000c8516600c5014100c20480f585848061a900c0d203000400c88200c194600038005041c41c010b40541d009050345102c40901c40003440e11300216540005002e03404141c16800005400c4400000c8921a2074000155401d0548560901c0101903030740c04a10305040e103808010510302c605107150b034840c032200754000c100d80e40350481542c213151042e0002c0410080d038040500142c0c8000504200c1401a081950390002c0c00740001c03401031042c000c403185451000305040d0403a245a03000340c403501804580c8402d076145050100400c030300c070360301c10304950509811420116140691210790b201101800251900442100c0c695192005201c03c80d5465520ba42e020300d0801d040000701d81111001c001018002d0458401510030300052042062a07100082c059086911904002004156014003a2225034030b03407403d54040c001240120306040305440004a0003050b40742118121403001c0e0040210104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 281929532 1250 281928282 281928287
    0xe07090c14030f0a060f0503030f0c0f0a0c091b0c0f0f02040f060e010b03040519050708060c030f0a0b0f130216061d010905070b031e15040b0105041203 67
    0x40a032000000d0103148880d207124030380c09400651080128944101070351030403045520441d906504104444a0000d505104075280042140c030364041d01401103456203801c004051910101d0004503490380291403401c020010400001419244204414416445050f0008034070f40c0301d40c1c42c22400038441403640d501049040125000c8503006640241e08d81e40550041b070242c420500a8198050380c0d14003c00450300c80714051400b5041500b00309186040c0390702d44039590344242c40c1100b1083d6000c1501d100b089001c00400c1d0040045c0300503250750789000440f25545400446801128803090700c0003421110b014400c0300c0050314002c00d4034600c20b016001380b10140304032030183c020890f82004441c0a1145030103000f02007910030740700425120240c2c0c1e01c241e40501c94040194080e8184800740c0c0000340c01098640c250341c5200d05050310307559075514101c801d40ca0f07011110420704110702400100901c690031a4903240050760280500010480112224803541c4a440c00d072000501d9003100003031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 281930782 1250 281929532 281929541
    0x140702010c030203091e0f090c04090221070c110f03060708070306090f02031609120f170720100203040b0d02040e0106090e0a06080c0f0406081509100e0709 69
    0x81c00b80c4101d0f81021010004510005140d11021301884a8101c070b03e0702d613180c400404240c1480540c1c12001d107040c0542104c481d801103001c2e01c0400c0d50041088080905440714401100a02c81241c3d8a2400d24500c05803151010180c165912100440902d099042541d440d008000010700101210342d5480f20403109504050081002c040d2501c0d00020101600d005200203003040d003000595a05120031280c0c40c080003101c4200034400900010040303038032a60f6100c00c840d5042440b00c2c85001d000d14100041041500c05c400074400f02003007045c10300c090160207100320390310510403640483c030450070031001120760505400140d00401c0103018025110020b8504ca060411016040540f20035104035030b41002d03046500000e070300070f004200c1080c0503500d041c4c1004400c2803c10205042c600c41d241c4440880c55900e004640b82d440b207090030b0b15194015070040592350180d0380c0683c0700881b42d00c1026010f5506405078032a107060380c1c52084051241080358402240100415890421000d0103030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 281932032 1250 281930782 281930807
    0x405060a032c07080c090c0f1e190201050114030a06150302031213050a030c050f01092301030e03090d1401020d0507080403020f0a0c06140d0608030c0d14070201 71
    0x1542a151042d54082041c8110b1900311100c0e4064420141040407643c50501d0340901c4920502c0746030b041c040301e00000f6084544221113025000c0d42e81030041c0c603044060310131145800c00d08000080c0004802119180d002c0303403051950003803240da6030f21031648594202002805a160704240120000207001761f000104141402c3c207100c4c481941ca40010341001c0b24020f0300700e510f4800082900c500407122041c0301c003510302280c0403210030b411602d541002607168003a050086400f840b020945078094055400100300c4034218410120100d40b03074814840418900c03501181c1032000800c0c43e12400b00a48991034409807122428603507588415a811a020780c0c0e44406541c00c00100716170000d1401032900c585040c0c2c03100d070391030704240c0780080c40d041042103101d2403a0840c15441e4005650303035103201c1c200c070103d1401c500503018503800c0514902c0b82c4d003500d000c161700d48400060b0071100400900314440c4900c0c1a10030040c00c10790190f5600006c03001e51540d442080080e20015030156041d03403001d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 281933282 1250 281932032 281932061
    0x2150903120c0d0f0503070503150d051213060305040b0a0c11010e06040b0601020303090c0906120703050105010905090d021207060204050415030507060504080a060e0c060f040905010504020405060a03 88
    0x51100000c014000e034007400d5681510740140f400b40300c81c150000c0c400d08040d445441d0940c50b610702441c5c01402400040c184040000d90130070b00000d142d07100181c1c080200c1e00881074409800865109415650103030b4070708482c0c603551390310000713405000e03105062140d600408080c5040d034411010f03100a103949182c0f02d040c00505001d84104c00000d02c01c140388840104014412400c1ca418070031004040100310341d04541c010070410204200200d00c0500c0450103850b49069a20f900f40080c0100500300e40e014920302ca219400010700105400190403240c03c01c40c02c006507111940090307107410740c250ba8400980c0c0440705c100f40c00303202c2200402010380190f50040c14292503000080960704074030440c50380c3c80034002060050200a202034401807009080040c42c0900c0c0008240d02c1d84001c60f805409199103402d45000c407041071005d9252620000c10a0f0b0782e564070816026001c0c0c0080c010180c14528140c008245818584201e4003034031001413445081108070402100900b280c0710442c0300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 281934532 1250 281933282 281933293
    0x50405070c0812010f0905091b06092d030d141e0d02030711031813150e2406090906040912032a0c02010c06020f07060c03140402150903 60
    0x7040340b000107480400c403c440d15002551521826640c44c3c1e01e603410000c0664a0001030107441880028030603499902540010f0b5030007949400107425001e10740c90150000d4868004004120001e4020741d580950b41407a07141c020080024981c0d0740760040d440d03901142d60404200e01030481c00e0040c0001e000d401c500e003200c591080c031190616811035041481019008800d2007103583d0400105545110030300002c508081002c104007414800c2c0414180c003541d04c1007005507050005400c20400c84030a0b00c201020780b0f6560544608640d022105a00012821280002d45d05603800344002c9025009102030b0614241c03c040245490015040716403080e80c403044400050ba4483d18200400103584000652001c204154070342003410603100782144d1000000e82c400d1503003003c4104101c40d0207181c0315581350140d00d0b040000344036504100e6650382d004a100740c1040025001070204102940e41071008907500b00400560341e034151402035002d800c4113a10380200c07030a00007625005a00408440c2c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 281935782 1250 281934532 281934557
    0xf06040320030703080601020d081b07050a0c0f151e0e0d05070303080711060c030f060307210312021911010605040603080405040501150e010c03031e090c09021305040507 75
    0x51655001035821130104000c0000c0050960f0140b0415070030000b40c1c00d24001e9407400c0104444050002c10300da28543c40c020550906200c001c2102e0078002d40d0210440e4129034460407595031086a0f48105680b40911144102c40248a03c0310b03031210180e000320b500300c91042560190b440c3c0481400868000c1014500c65020a400304040e0009500a840703c0e107282c1004074004203001c1000ca841c01c01c0741c0c050000d0115070030720300040340e500030a405480300c60384e102c82c8002410088254051000040300065858007281020403608e0402e22940b20311108030480080d510581c000c0d809a85226028071034603409003400303003070301203110601d81c000090000d855070002021141c80c0c1e00250340300d0b940481c0920a6003480e03c10540034110040e20704911000b03044009010808007040241002071a1750b0303450415000f80c111009207030300d40345c020090042000420004052404007a03031030100384200026291aa0310850f030700e5085060034208018180400d1001400025001c182001700703440426 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 281937032 1250 281935782 281935847
    0x121d091308120a06061106040803040303061703030a0b1e0d020a0b0c0c03010b0301380607030804150516030e070509040c0f08030a20070b030903040303030e0f060403 73
    0x41070b014003101d00070b03041d9003020341c3d506044440c241c01401c2404950035007201165000910198415400700000355a6542c6141c101c004e010715a120031000b2114100e512911500440070714820081c10408005240c01d4008210358400c60260b45940d4119031811b0a00500344603480c00942ea002400341d00e0816941c42c8050720035030101c00c017460306401003080c00e10346107001e010303a850f02c0408078000d01c00002c0c48001ca0310503d428003650004022400001c1c40c54202c501d441c00e0415030001d080035101c90050070047c2030364038212000c0301d008407404001d08580707101b031003000e01540c5010890146030341001c405a00510b1080510001c51044038800251581d840d590340b4030941c884e030042c0c1175292030082040641110f0750444800c5400c02d00c41d40203038950000115600b4101c60071a1031a60124112450500d03519401940c10b0b40800002c01c00d00002c002300034000c40b4843e0307904102007903e0214054a034410001890b100707400440c0400c0c0401d208409034004100a15001401014040380c070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 281938282 1250 281937032 281937037
    0x506210c2514101d070e0c0d06030609060f0f201606090f02090f070527090106030e1b18060109080f0115150c03080705130e04121d091308 61
    0xf80c8002520342218102220f2210340c4070002c070700000000c01507141080245017540714002c00d01d10298001090126900c201038001d44001e41c3c009008000200f00c90901001a00800320418403042c108400c282252000380316044407440072640380b0030007000d4a4444c5080b5402149102c94403283c500322038010038120b00c59494080c1c824400c00b02c58900718414448030210052000c0005043c0c641007219458001c0c04986404601c0b80ba9000603045464000030700016808110390803640c100e00100e19541c15500418a80c082d00040300d0410100c0085240c041d2550b03056144c00120555111100c0c501f68646150402c105041c40040191240c2d01a883c00310100c0c0c04180582d1644140c260345541c03004401d01030883d900181034101d15242025241a440320790050812a03c036001030745852064081e100300510822543c40030940e102c90103c0048015681038500321822502c03a000c09000b10001811a540542014080c118050400c450010014100314003040500700c0580081d010400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 281939532 1250 281938282 281938303
    0x513080715110708060f101809020a0807030c0e06060c0f031801030605010f2d0c020405070f080406050a0906050403031401290c03040506210c2514 65
    0x14401440300c0e41d20030080140d0388804216003503070000d500510003404045040b84d800510350002040380e480700000f0303000d403e00c20352000442004820b5010315160f13903074205103c030074000c55640d8005074444280548905061000801c3d031040c883d0300700120701c00000700c1a03100c1001081c03603090845850845041c10302041081e032013a0800100b1002c66071070601e020301603820a107410041d46003804000b922041c003990340481400400703d03080c41d0400021a000c0b0901c51441c40f13172144c0e82080c5c50701801501c01034004078031503420040000c3d0b90034850007440303a403100e0071359451645840307030b407a5440107210141030b84960b20b442e9036000012a040707000f81801175100b540c0010b0002402c0e21408903401041c0c0002801c0348a40c14032a00b4024200c1414000410b041041d41d511034186146501e0b61060740d0240f508410702040310070040040c0755074980340042c410584a6156501401c03031070a80301c1c0240d00d000c808040112103000080c042c0b00c108025100d803000100005000112030f20345101c280 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 281940782 1250 281939532 281939549
    0x6040308040c140d020607050c150406093c15050c0d0806031b010c050706030c120504120c06150e071706091317040311010f1e05130807 60
    0x1400d11007084841e00203200100b0b106000c2c41800e1004000082507540e11355806071180002013044003d1180900482c0100d0b0f1008016039170340c90082100581340c5c2c02c5403040c94003042d142c500009400d4440d0b05c0c0d1a000280012044407108014003074600b14252412214035800790540c0085090281c03950341a04910664550540b12043b101c46039240c52402d0040d2400c2020b90b60602003e510700003408501031039200c0501551580c2000102d07100341001c0f501801d00d224100700020190f4140e406500c6000c3c2c03d585000307280c010710b2104d00136140c043c0c170b004207005082401d5160b840d22a90710211450f20410b000314180040700d0b40305004030319a400411280641c00309000c1101c2c8c010030100490800c1c2c020700890341c60a800000e03501c0400038045001c1e55003500000c010010f00780030205c03c4200300a0f500e81c90301d40340c1c01c1c03126003d48150b5109011030b02d4800001880307800b9903410a811480ca9201840d040342d1080d007100d06800c1001103d103010401a4003140c00f0034148106405401d04d031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 281942032 1250 281940782 281940797
    0x2060604061517090f1f050f1510030204080109030207081903080c0702030309330306030307030e030712030305040203070623160609050a030f030c02071202060c060403 74
    0x15040200312407440d80121030303050407071403908001c0c3d4010595503191010074444811a5130780c001d100e41402502652440705009481040c016400758003804180f120306d10008214690b500302904420303101c00e43d404a80000c100c0c0106009241c265003001d41490a80380141c1420b649007562402d541d4140c2044000d60060038040c09400400c02401704c115040c2c281c40c080c84010b80c2c4018214240107000075549a50010701030b0150740301003084030346181014040300300c80d182ca80c05003017880e00d142202e1514001802c0803107203040c2c1842d05517801400000c000d98607210b0280d03010745042c040f800b101c0d50507004101c0005401926590704d00403241c00390b2408565880e01c0c1c4101402d01445804c05410700034019024a400c00980800c2d4546039001c500c04c0e5658080c0c21413400258001c0342000f0100c3c3d040014890406c040403aa10383c40e14880d88a60704404190b880543c161140c0702010740050340110010006041c800041d55000390024001515281d0000000d506202c01100c0950220701318 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 281943282 1250 281942032 281942041
    0x603130302011427191506030803010b030906090105190509070e0a06181b1d0d06020702120d0503160c08070c051005120112082205030f010e0a0b040510020a0206 71
    0x294007580010b10413030009844a82c12031000166402150f082c080c1c4140350841c240c00c82000183d01c131801664000c010507440350794a684041302503000312a201e40c0f41c09500e020401f4042c050003002d0140303aa06800100004c4010500c000811008000b910a44250368000072521500700103c0c3c002d24007214003007922410720742c0d0201c108501c4a080d489144c0b42040c400c42840050300c00300d00003142440c000303040c00c180c0c03811a4004407a02013041d80c444400e62a5504014291f402080403a00c2a1b4013810f103085c06c4071040e5140c422903d086400300d0002c00020324101d00c1141d0182107404c03c1e0410407180c880b203480700300d207a4206401c00c54044006038410b00881c540103260f200c0750b07201032038140d03d020309845076001c0480061261980c000081456031080180354025140c020b41410a501d242002c1c010f000d12482c1000c2c403540d8024041d20013922440c48040c00b40c0b16032041d07058010f00c021080707030340d40d00680d4600a1041d583c40c0180030005007001c0c03040c0020701c6030a802e540104402d040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 281944532 1250 281943282 281943331
    0xb1f080313050307050d060903020f010203131101080f1609030b0c0309070e13080d0b0418020109050f15071406040b01060906090e070f05090d150b06040506031303020114 75
    0x41e580c11441c0700e64082c4004204036511440a404543d6200c038010034800e0032450144c0c6000d1300710300416410350000c02080005a02c18002c422018022450301c2c1d600103400005480514040e1800141c038404180043c1e400f81e10072900481c020300714074000c252581e603600c60103c44ca00a035481d2144000020500c221640304101e060007a001e141c1d14083d25090001103107080f003500c88802072000c00c003c0341586110042c1d81c03100c0c2c0304640141c02440110980038500d1010f00c00340e081280070400b60400441e250400700e00e21608020040c0a0b070b46140d201d04206c0d040d60304141800c440401c1c9401c494030032014140070381402a4850b402c0000315506100000c0e011060682018040140b00c980c10068420322110150b00035a99042c400e40045d25071a0840b6030f40b10f080c501e01c0d00001c0803103404080111020000c40442e07000701d030402074102803408206441c8203030b114240d8001800d0004c00c010301410120504120301c240000512000031004d2121488021070b4036600b84a40e0701e106064004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 281945782 1250 281944532 281944567
    0x2030d14010815070c03080912070f050f030a022a04021c050108031204030f0207090e030d0605060c0c06131d0f060d0521040905011707080d05070b1f0803 68
    0x400d010a610b072a161013580105151242c00307014040012580109060500c2840890341ea610b90f8222182c0e1071446082c5041c2030b2a22a00480f403e00c6103039880c0e400882d01100703690080000c0d40c040c040c01005540c070316442040003003442c00c0d182c200b0300c0313015050f6a4a100410b216000c60090111080e14030300c1401c11108140c3c01021580c0080006405503042c0e10700c840d03442a8182000f4682140642e0124a0001c65070001143c1a24014040d003001ca80000648050300f0100418803485890b0741c18800340b4000d40010411541c00481100d40300c0c58802c001d0040c0c54030000d80c80b03c1071940e59181d0202030307501009041e050041e18041c0a111000d21074100d070f003c1801c0d542e90940c0d030155504c907940c40c0040907a982800203840210741000340b683d0300300c4004040e904000c1c001540c48880368402d140f81044004154032903104000303007100340880c03100c000400c5070311101d0404d19161640d07003221b1002007a2048881190030592000b0007200c076110085d0940100454840101c05620110b14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 281947032 1250 281945782 281945803
    0x1403040c0e0c03070507081b010509010209100207180b01052b050619060809010b0303120f01121205090609061611030c22020403140c0109090e0d0f02030d140108 71
    0x2c0b030100100704809070824100d0301c51641c445069996003242030310703d400d541095544001c580d400d010078041158415009002060300458a660200741900000d0780e9809040c0700f070704a9a0b0030044162042034440d03009140c42c03103040c105035103800c0d50f40c0c88034032445800415140d400500180001482070481c8206940a1400c0d10004005030100101800556441c410032003001100000140310440030f4201000d229800b504594803009061308840000e0303c01c82c2c186485c5207400000150b00011081002000c503004010306102086003007003212281e129482060300558100021002c640302c14009110b1070080c180d02018071956880e103030308a2100051094829888012092503e03a01d44028032090108501c1c0c0c02032858586600c2c0e030180c00355070b202428158002c510410003850119400301c8072000cd80e66100043d8581058400721082d68400000b29400540c1c900400c03802610204000e03c0da40c0126424030802d2040c2c031b42901c0c01c16100100c1d4050705001000100e20070000400d61 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 281948282 1250 281947032 281947051
    0xc070515040c080607113705030c0f0606060a0c0201050f040902120a02090a14130507021c020a030804021003111c0e010e0309090a061802030619060516031403040c0e 73
    0x5142c160700c5902d0b41c0b8140c5c02030440100b08892400b0070010291301d1511900764101c03803c45080151428230584a4000c52840c42241c083c10040d241d00200c0400c1f118420b0300000c21007070070030060b80d83c12103041c00360100480c1400002c0064106040511000d00001e162080016a4690a44030b803540b4402015180d400340c20700501101d03441e69540d01b080400e480a859003070300b01d02410800504020b5280d4501c41800e03142600340900203070f000c98240c5103c4482e46400040002043c02260307035030f40121000c2c00062220010400524007150380380d080c0c550030f15001c40d00b140e80c440041d246a005d140204828104180002e4a039906070286030b440c0082417001f04100403100850a0300ca1044500061041e581d200000394540c0d400e6001c0c001800d4016010104030458201c4030000750b000713136582da1184003148100d480e5580d03803824400030f540083d581c0a080164402803041025200d0000301c00b03204682c0803420700d00c85100b016500c030700e002d400030854841c07404203020954840074103042031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 281949532 1250 281948282 281948297
    0x303040f1e03050315060f1b070b031003020d05150a0507090806010f06030c120c0302250c051504080f0c01030501060906140732060c0702090c070515040c080607 71
    0x119400c4000e60781d1003ca44180d054030044902d0020703400f481800540d103075a940200d04c42003600d004001f150b503240c03070074400c945289d9141c200304441c902040b0b41d515030f500380c900018401420441c098007000340c030502c00c9849540070b10207110240c2c9030032034080c69025030f20000c100940c0c0c1e03c024103c0042ca48000030308820350619075480c40001c0d5134001d26043c03544400d440a01360b841644548120b250156040100c42d0441400130040c1d03000d81001d0340030340e0202c00014240b85041300301380490781c1e1141300400850329180c24481c2c09a100d01c4800008003080c840007031040d6044c00751801c0502d100b40500780d032401080c0054200c0d0b1060700990208002d243c0c050011581110200e000c156401c840303c0d84805231440c0c18100d07017070505521a0300c400000400780c811031500340b00980f102c880c4402e440d45542e41e045e190300103000c0c1042c0650310480e0507003c035200d02030000003046950301030300985102c440009003404800748240d80403a007025200301c3c02c2100400610510ba0080316503d40b224 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 281950782 1250 281949532 281949593
    0x1c0f050c0f042304170a0503060118060203031306021b0a140a0b010611160b0307021011090126040b0403030b04061d07170a06050301050603010507090b1303050303040f 74
    0x144203d5030005080b910700505004c5000e21080345100d040c0307001c2c0b40300e01c980d890880c004010801e400c1941c070703a4040b859031410364240caa80005001d09030f9003594000c0d42150389480826810706a200e109480c6a6800c001138402c0d10410002502c0c4041481c2c000d0101c400c1e946030980a4840002021160741c01241e030110028404150341411140780e032510070114046010218101400c0711102001900034500c0040c1c864000006136101e400681c00703039075248200061580035030303106c3d0070b100c0c1501c801003040a00300c0d0f01540c00041070a0902940340410900b502c1d17181204041910141e455680c0345082200701135040c050841000740980b400d0042038034006103090016034100c0c0142103108200000b42c1528800c0702c8210340320010402c0102581050054180209001c1c02054000e5081030300040b01ca09050140c0790040909580d4205070900c2c3c41e54042e03141e0808120700e880822141c0d00000400c40800142d402940941c0084400c5c0e55946088070f41c100304c080d08040054a084c4040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 281952032 1250 281950782 281950811
    0x180605041a070b0711010b0907110d140a0315030f080913060f0510030b04060b0301090c090806060d0312060914090a030e120a0510021207020304030503091c0f050c0f04 74
    0x11a0032043d44d04002d8030217840c0700b000714007400d00c1d813007041d401c05804c104100d41d46078441c3c021803158584905980c0702c011b80c1001117892000240085403062030030051540c00900c2075010007902051400980e0390380381c50f0382e2140021844803105503442003001c01d800510b46000728510b440c0d1003a80104100207440c0907002c41c805105e92003510320036400d841d070009006000c6d030403098070064010010440c0741c1e221981d60409401c01e02034441b0040c5400c07030300386036980a0303224002614420401096603070303143d9040044500342810120f04002088285210b2407103c0d01a040180440c0308000c625000c09141080c200b4800802247c01a400300301000007203038100100e44007440c402c2c0c440c03080d0119600c030074038545844404010114401e400c001310501c41642d01409034883c08001c3ca00303503602c0e150300480e5640213501020346103420030048991a8034040c0c220202145144402c1d4a030440d20344c4035403e040c2c084a00a4985402001c664402481c0c003241500d10740c4001c0b00c04118008042031310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 281953282 1250 281952032 281952053
    0x319050a09120206070503030f0124021f06030803181618090c15050d05060f13022805120c2a010b1908120301030b0403080601180605041a07 62
    0x101c5241407564008901951100000c40709170b103401c00c0840eaa00e050441a820030b0120900c954890004a080c8031940c54103c0080a640013000d54000d1001039101d0002c40050203c86900e813504682e5180b00000040c0c00b0703005948a5103050806542100d04418054100059601840f100b1031180f0010300c07050340e035000380b04462800c00400051207041031801048400032504010262018a03031300c1410b40e07900c030300242509a1040070500c03c1e502c40c01e0030711801d20740c103510031070748030b01c41d035100c8806540c2d154082c102d0304046c55460a02e00d00c60396030809200c089000c941c40000c07000107000e1070b008800384032190000c40b8510000d2605c80c0c01070070b0f201c090500c0041c03c0859200242142000c0000350040c0303490150040050007045000302c3c030382c9022000f81c0b2440426000f880180303844c094005095a0499402c80d41c1c00b187d031f98869400300c541d01801000030f030600c0701c8101d0700c132020b80c1d4840408000c0e041640340c59a4a60822060719402c1c06541c40d0601d00e00d00c104480c0c00000d058181 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 281954532 1250 281953282 281953289
    0x11d010b0a17070e1302040315050108120c21030402040518060606070807021c1401091e0203150705130503010e0a0201080c1c0912020105040c0e060604090207050319050a09 76
    0x604090316100e16808842e0180e0040c4016446024044280c174200031550041044074801c0d1081240d07007801a42d410207441342440b4030760007034104a04442223400c0540042550380096400d8401d410701403045800c1107246102510b50350003003c010001142054410143c0000300050000d07820303245070300d01c59a40c560090086010324800b0401401700580c1009031458130b0317401010415000c024100b180e134405155001691aa1400784801603061010f00c00c0c401d2840e0402e501c2d074040c406080d0108084503104030100d0b018420302e2420a058200c19940b0b50240085035209591070a0701e090b504220111a0080d601c07991400013500590f100020380d03041c56641c203080004a582d10600c2c0254030340548030300b0211444101e411105821450303480600c459201c0c0c203542c1e41900d00c3c60022070172a84201e40080c0000f10300d0790203000d0031902441556110398010701c00b51500d40c4645a01c4140e801040d01115154030214802240d5440d64541c480800b219140090412098900c0184500303401d21 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 281955782 1250 281954532 281954567
    0x7080a05160e120f010903021606020c01030b060d02180a05030f061906150e0901091802091504020711030c010e0d080d02070606140405072c040e06011d010b0a 70
    0x5450701181e448512109901201d602c041c3d8084c5034010110074040c0440c403204030014007684984403004094440c141066031388583c000c18580d001c0304015002400320301c26055020f441031001c4856610140001d00640c104180c5968a0b40c01041c1880040748064000b80e12075000010000084030000034030a071b0200103c0041007182d500c59564400a202a030000c202d0020301d040c207041c4581c0c111003504000107094810401aa0741c41e044041203030102da17400103003112204200d0700545046015540c00640c00c01d000c4541080a03000a01240d00149080700e0010300e0210a50851a040c440342440c8a402e0070914001d14a20002410340c203850b120003042c081000ca694001d00c6200d034181e50354150f01c084100714480d1500c0702c40f1040484c803c08184282c3c1400001107000b407040714035210710440010700d840200400c1c07020501d002036007110300b604503580ea81c0c05080f041c001c010003030003070075000740d1203034060042c490321104594140c01175025040200b10501c4e90583c8065201001c1007941c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 281957032 1250 281955782 281955797
    0x9050922020d0204240605120103030e010908070f0905060904030503061212040f090b01110c010302070302160b09010809030a080a0513050105040b070e0a0510051309020703050307080a0516 83
    0x41c0300092041c1c054400180d0424a04001803407540c80400304200480c5090701105c1e50140c0d2a00116017174860745405140b0304d001840100006030055840c0d840c541814100200d22070b481c1c4d1506490325070184e01c0011301e0f0603102c4081201c14490b20030103030485002c3e28240c0d0a89030503100988244405032186004a080d402110907a400501409026201c141042c0b80d07100c0c1d940403003000c00360303550050209030341c60700301151600c0d80500c020307440b01030313400b4058500000c0d1500158001d400100f4241c095000f541210070340203c034043d4180245c0304c026425511a04100c00040c22400000c1002031aa40308020118050360416203041d03100700300203404141030360349000301a030500c00c800c03000701740d582400d00340000c0006a989042c13060206540d007a40da0010034003002414060391041c15000f10040c900420b0300752042c0c004140400c11582003a01099036004814100c1c0d0218800b9000a4000b005001c40c25507c40780711394009105800030f02041c02c190944440d50141300901c0360074010304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 281958282 1250 281957032 281957101
    0xc07050a0c1412060702060a050705040b0c0a050c0315060907050706090c0305011506050d0c0933030e0607120e0d1701061e0c0606030210020d090509 66
    0x100a6514020352001080d08482d0b920309400310000d06030882144114108480340896450010f9054400d043c164001c008a48490510100130200a02002d040010410000c03e5900594008049810042d0000c048020707032424080d080400100c0600d01c6130704032540100e01c44071002d59107600301400f203494014980b01c0740c03000d0724a803107220f0000f40301c5810281501d0030302004410000072640200c00030300c00707540d800118651084d0380d030180c1000301c0d0040c00300d005036600a50204240c42081e0074240121a04c8481e40310f1201c510304d04042c46041d910782041400c0920854003114070465003014040a04440b80340f075211280100003804000d0b00c1c8429a5405030075800103508030600e07000b9107030744c0c10a07850010400c401c05a441c000c003094a0000280c200d200d203140c5505800d002503d400c80362401c000844000e01d2411054440648804020016079502039101c248803015070001c00d005070107500003514036030ba40c0e842148680c00f03010800103500c14803030321061075042c001541a4280e81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 281959532 1250 281958282 281958293
    0x180605010f031104120f0209060102010e0d112107050c09070903020402070501061a040e3d031b080d03060b0307260702010204030b0f0403090614120901050129030c07 73
    0x940c0d0300c03884800c00c800c1d0205090011030610201ba050003034030420310340e58601005900707880c0444400101c0d98440f0043d02481e07841000c502035811188019582900c001041c3c0521011b46100444042540050400204501080064103022090350b001500380303040e8a0181c00c000e042c0c4406801940c0000b82e0004200c020360100024100c42e160303551030300c3c0c20b1040d0395205030007601a801049111002103000701e046541210b602c00600320041590410480351280d24031408e4540b0240c80d000440080300056401d181c204040070ba400c046201685094003162414043e101c540c4249440c2000c24490303400e100c03048070f901200310f0038421400c425034208a022101129a40300c2da006400003400030700ca038190010000c40c2c0c0210841035413612140601b031070507070040d5001008a400c801041040e03901031462054180317210b4104a09101b08031781520070816080b2003840781c0c2d9640d200140403654503045002c05220494070044501d480e0303180360b40301c0c0c0e01c4003230004102e4000101d100704c00c100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 281960782 1250 281959532 281959537
    0x50a0f0306050d12021e160b030103080f1309020a170c1201031b0803070f061103190b0d061802130606090512071502030403061406010206060d020111070f180605010f0311 75
    0x1ca20802e000c90002c0b81d074040684030003d03d0a03031882c0400c0387c000001d1400016041d40c0c141c80d0070107100c914201125540741c41e690301065040d020500804000240d10a07070388003a0215044c95110f40741c0c0703002c080c14a0888480700a22140c8240700a0000309a8417100b401d0490640340c0c410311161081c1741c060115812000ca5a001341204c0c40000b83d0340c0c04024000f40001e114510543c030501c8910030301001e54041c0d00080b24045254864014000003800682c0c110003500c40d0050078945a08044e521003105540e02c0d1100c00303100f401d26a80d0038007141013006207882141ca02c0b06081188606101004021756801e03c100352003103070048182d200402e0f0511030701000748102c40a502c840550801d010752250010302c07094440c5494982d0b8400b9401d908035403248a098140d001c0d2165075101010080c9108040909074100000c50940d40745014080040c28080c02000000c0d1142d18a0144146030b03444007003600e0304000d403c1420030003450b600310100d00e0588000d800d020404c41e010001450090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 281962032 1250 281960782 281960803
    0x9020a1d040303090c0b0f132405030712020f0702030c0603131b09020c0d1b0206040e15040501170615030a080304081312021e01050a0309060615050a0f0306050d1202 73
    0x8000101c104407c1e9001005094944021550300c07821950b40400b04201d00c4c1003144c03181d450f0400034560710481c0c07040d40156403010503400e10f800c07905c000e9080642240c10018090544c03220001c0c00e00e0a62034200000d0740080d8044482c0c80c5949000443c2810389050f0403030052641d190b40344550820741402e8144005414051011526982c400030401e0390344a0114111011490b0003903a10200403901c07103242c804ea60080e140c6854030740f0f0400300203585200141100110010b10a4211480da03071406507500a151030012465051321300e040d5603080140180003a0701c249502da000030b00e642c42c040b8442c0701b1240c0188809481c0c5d6181c0c10565102d109900004503501d0b5168008103035040d0000181000074025121036800d0800a2610f13200600a4035500340481d2050264071003ca109400040000d840f440010034646e0391201200c05440310716142c030001c2080031440000043e4020f10001c42d04055240a02103d4603103008124500340600010704100c0c0109802c50300b4900030040c16410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 281963282 1250 281962032 281962049
    0x50d031709010504020109080c090f090102070c06050301081608060403030209060705060106020d0f050a080a11090402030103080d150e040201050a0504031b030506010602010b030304090c0c02030d0309020a1d040303090c 96
    0x2078640079107024002c20003110b04a000c91035203400440c46500024501c40004400b610500c5140c40c0c8420031076000c000100311217495902004080c0001e05110002c81c018500f6460f4240c44e07506100619061103040c03200d074113002420103400c100a2000241c03454000350541401651503009a003c40c91a01c180d140c0941a407103004000038203142d00154440c1c1490040e034540520320003008003124288695007000c4000740078540440d04d10600c1e030344034403080b4002d1481545410520f0700882e0598000368000e868500001c01c0092100078140a12001e00208081d0000503501303000443d0401e00d00038102074100580842d0155003a400b410444010303540007285003a400100802c84c2010410b640021101401082c1c00010340c2c6005024001074488010051803d00d8148126600200340124502003000b0101c4501da0150302c0900030040a04195540401c0e603201d18018407880100652081e2050b89141c21004a0801a400c1464206a16141c0801e010a8505210b42601c031980c201000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 281964532 1250 281963282 281963327
    0x30f0c031d01050724140402180601110d0305060405060a050904110604090608011a061e0c1509060a06080c0d08030414010c0302070c080109030203040b0f0c16230a050d03 75
    0x5c20b50080812800104105407090001c0d24080b508120382890556000350425000011031440c0c05c2c100003050b500c0341040c50003290000481141e2407070000c4a05002d00820343c0d801c00e01100342024050258007100640b07001107060700e007101081580400410241c048101c2c08030080140da01c020858005040300481406000d4072a90018000c0800e04481c2c241120708040e902c01e1401c0c00b0059403040c5110104c6000c000790780482e00000d070703844820b5924403030103980710081d49441d075060854080c03a09500180101e02d8845d007484100c40d00c03a04030f03841950100b244c03068503540c0d1074411000c05a101d01210b45179140c2d0f1a00ca46901014561002c2d19424008a00600c42e4180d024000841c01002c1900045a0b40d5510740d0072964040c0f00500181c200304000e2020141c81d40082202d1004a042d8a14003024104030170700300505001c0c0113210102c604000c00c0190001d80c01c806a0310034803003c041e00c9000c290300059011480b8400c0c83c2c066040350309000706060080340343c0b00c108410309502d0306 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 281965782 1250 281964532 281964563
    0xe090603161502030708040303081f0f1a070203030409061a04260c040519241401051909030c0801051501030c030608060c09042003040209060d140a030f0c031d010507 73
    0x42c00e400ac119100000014a0403103d55540002c40074041140d0365042d541350007038102106d000740340f0000c209803e00918100241c5005032400c01c0108000d144200000440f0740c10135600728411608030382c80044810041c40b09000c2c10b1001c42e15641811707540600712019100c180480c9003490140071a00d54840e15000c04c001c502008400da900d85c4d0080428104005400d400103000000c0100078241094450f060080c05200d010003a60b011041050400909141407a03c42580304c0d10f089000c2e40015103a46c0042007042480034900010384081402130000380341110013840e810310540e031403504258680e004208040c1c041d6002d00701810142e004d0350b20a141072070043e001c9520040c2210700a030311704003401042040d02650010824240071509185071501c1d020440c820342d018001a60201100421200040e07400c01e0070594002540d025000e041c1482c10302424542c0f000756041e080c03140300350034a40000d9200b8140b03107818281107400c3e2520020900122000d02800c080104034002940301d81c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 281967032 1250 281965782 281965787
    0xd0b0a0503030c15010602240406090f06090203011a011706131a0a0603061a0309071203030507021510030605040c050402030108030d05070e0619030906020a0e090603161502030708040303 82
    0x1501c400b0409101543d50761b0b02c400490f5500b0200380408003034030b2454825802c42e142084c45581103401104041140011a1912a002c88000008603219591048000f007107060a02902200340c1e8041d031a100040c4041300064500741c0c0750480c809030f1003441c2000940560f50000ba00ea1800ca04105c200a06541c280034034003d51082840f29110750b400100000e205440b074000c0c503080d03590f00341000c50340708031080076015203400161030200d86018001d0f0104041d1415103004110324043d680200d101e007001d40e8040d0404030b58200c452142d00614003000055107444070703104101c942c08030000070741d562242403190003071011340c00c00c550090001000140d02000000904035400e0b01d00000c205d680c50343c07882901c2000c40036880980001043c412404c018080f000c0e085001400c81c107000c1480d810740d58a0b6030483e403194000070041440703584000d0140c00c080080d107900200941c01400c6140c1d040d5010410b20305039100f100303940c080604998111901c00e1040c0c07000a45d0144141d07441d15240c4c50007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 281968282 1250 281967032 281967043
    0xf021603031d0316021921080715050118060b04120203010e01050f0403120510050d060b032d030c15040f08130312031b080a140c19050f0d0b0a0503030c 67
    0x1a8420400c242408690341c000a50141c11035245208034121111041c2c1c004104048000060b50202020321410010420303812a942b0207049000e00001c5641c10600c004010340c08200f200c0d00400c1c948542407101045007400c4409890015103104000040f610000340540030001c25005194248414401440060360b080380c0154420f03141c603502c84041e1481d140440320102c030303040043c00343d6550030072150514940c1c100c81107000d0480401c2200803140402e28102c40707a403248040f030060a46d031140c14203d0010050303032040000d010b1450700c0081058107640b03010820080003800c0071321011804200301414007050b101d9200c41c5c42d50300c44202441c9281c10440520042d2107407217a4501081c079143c404c1c4240002040c0c18580c0f42d81b42c0740d0404084480c14401015820015070701e42e05281e400b402224540d11800e2101c1c0d0565481d40203850700c125410408078048180035041c0a0320b8900c500d000c080d1050340c04000d03000101144c03010002020544c80d9441240c042c040041c03680e2102201040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 281969532 1250 281968282 281968327
    0x121906050a091a01031a040f110a0e0907080111040810110702090106111006081e101107020a0614030c030a0f02030403050903010c090602031e07120f02010f021603031d03 75
    0xc120411441d011b4011200d07050071640202001c5184080c8000507034404444050840050a81e0303060a03107400d000900300c4400d940001d0190f00182c001c008908003405810003c0700c41c050303643c1c100340c40c3c021020760b100b80c1c0c040c50519854982242038000210706050300d0001d6001421090296502c0c1c0014080880c103040744909030080461890000c1040d015003000c40d80078100408032058000210107080c480c2c030382c45441034040c250a141003400c682c0540190140855407040d5908420310411a2044151380107d040c8160201052544134021081c0c9900400c031546055581d5600200800103054111108506030b00c08001d1109160740200a8200e04109900800401da100a425154500203100c2c120041c1d008106c00c068018410300c1e4101c80d01d6102c80f120342081c45030382d2118018004c00320404001181009400c041c41d40c2401104c0c101c4214042c21440d26548205440055450030300c0a010706880c1c80d869444850310810b05210f091007002529211142e55040c0784080d81c0158 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 281970782 1250 281969532 281969543
    0x30903060e061302010806130e0c04140609070f110601090b0f09010522090c082b050a030c02031612020f0115060806060f04060509121906050a091a0103 67
    0x9074000480100098140c0200096500e0f02c5621180794011225084020a03083e084101c550890712409401e002d02101074a00d1400360180034042c40c14002141c000e142a1035140005000380b040944641c02c0c12034009000d8649403e03000500c10040e110489000c48404651080200004480e0440d07030080301c0c1000c040312081902403803c010052018000e0040a606c04180c10b50704d500051146601c00c002e1400300320100701d002145d12038422401c03880d0b001d2201c41c1c10007846c4115410038000408004250115240081d90101000078402d00403005c400d02410341d10220030211134000c0003034460300c80402c83d41059002261403c01c5c010707400c21000201603c6040c01e141610301d03040c01190444180f0103014080a460301600300c4000301c0152840360800c1080100d4000c1c100101c0041c0040c14039515816564452030081c00002844842103140c242c1048452a4000048082103c89150000808105501c2e8a00404000c01d81f0f00341c01068010010800c400800030b0300c120302d040300d0184 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 281972032 1250 281970782 281970791
    0x20705011704050d051b030301090b2b020103020f0c0f010f1a1c0201140c010207050606010507081c0209120a0b0a051006030911060307081b3c030403090306 69
    0x7542600c190302400c0d2401081c1c4d03000800d00b001c920744140007804e02c00d6003d00050340c024507a110214215031081c0c0101c1591500c0b10302107513941c1030141d441401109489036062607003080c40c02041e070401c41c8840c001d04140d0001214480507450070182c48078030a194041e10940c42203101d0480c001c00061499031842401d08001c40209403014078006040d4001030203100c00c000400b4003a40b03144803099402c9040c0f0851050354030159030007901510610240c1400181da507121800c040e8900000140650704018040109038000381c14a010b40c2c94140c0200c00352441c8100c603400941c007900602c0036198201c42050281c40208000241e42ca0b0391078003500d01c1c00380c40e4546100ca14281d6108440140049400001c04c2204c94400e030f00241c8064000e40d0080b000c0681e40d80050350960040d6010390000d017251061148500c0c540c200c6980c0c521100e900280b43c40444151008003c0c005907420100c8c25500d220410944502c0e0222111101511800d99030b0340f4003403034041c01014040c001641c409242 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 281973282 1250 281972032 281972057
    0x1209150907050307050103020d180813150c03050c0a150609110406020309100c0b04210810170f1e12090906060d09020301060303031a0103090c0e090a0c0602070501 72
    0x40380314030030b90b8000ba0140110a007450015400707580562610f00c2c00780c1d40e8032081107900d500d0740d01c0c0440f1288079a0f481540d5210010006841a155810041050422054500d04240c00210705c1080c207030b040c04c060391968104a40b80d818294140c06c0a8841103080f14041240d00641d400344c0b0a0741c400c50010041c2e0010105400e005020764010100540d104008959543c580603105089001d80e03407401c1c22660b28141d44445036a4819601260440c40c0b415410010902e03c90035000115010318052985141000c16940c94072182e103d00c43c6050401c1040300c01e451010f0001010120002003258903446281945e039140c1c120900001c0311901490421021082d041d00c11100b142c080100380384440d171610010400190700c800c240c40f928075035070b051a50060700c003030203600011030080e1030010b00320041184118600303030003d0095041500d030002d00d07030024061566020503518004c0d01182550f442e032402c4c61401030039400162030285c2503a00081d140307a00103490307070a585c0283d03107807141100c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 281974532 1250 281973282 281973301
    0x131b0905100618031b0f06050d0e01090f06020c0309060c0c09060108090607210e010b010311072001020f03040905010503120a0e0f060d0c0e1801050303030a050c120915 74
    0x106205100040f0b800d1603810404110481410139050b03e0900799030380304a41d034000c1c60340200040e501a00120b18040740700303055a03080780b09050710044a04000e01011000b661159042ca0b28948001c2505502051030b4000004c10420303200d0001000d0b003d19692180f800c10207503201003004010b441622410001050ba5101d06102070103644a440184180e031641c981c280d4100c0440808010712a00a64450001c00d58a0003568151002d00d00000355441c9054001070503920010052400c1d00401c01036900041c01103500030381b5902c0032001400a5020140c0103e0821040481c4046280310200d030104580c40a540298120740c3c084013100e044090788601c0d814107024864451002c604030748407861150074100d00d00841d101c002132880389490f800190340b008031448440c00340001440e2070031010103410450422045a441c4806035426589048006507032803000602102542d9100c3c004500a4090320040e51718035005e180d44c80c40360340740180d5465a201d8402c001c9200c502c40344004501845e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 281975782 1250 281974532 281974547
    0xd020d0206071b020604031209080102040812031905010e0709050d0c231002030c10060e06010c0c030203100c0210090507050d1a0901020c1006060206131b09051006 72
    0x88160068007440d9038042e400d50b4028100652011a40f1940403030b0380042e03407110010b0000c2e500c81c01c10203800c0700759014010324842841e0000c0c00d030740e0720402c4248504c00700092031043c00420362600304c0d81c9607103a0032040307070f0b40f00403c00051030141080700100b6041e178441d1000384101c0041d40d46921442d03503201042408940104040e0290b03028410903c503074503004000c82001741750400c0c1061542d0885001c0340800c550302da40c800c01a0030100300b81207488401e0111000180442000340596810703c101c040e01220060006810b02517100c41c03060400442440c80c000542c3c008041d6400b000c2180c1408014204900c0200014040d81a0301810f84101c1d01c10182103a030058000c207880303400c1000340142980715a10a0307076010200104c0e8504042c5d40403000b845025104000341c0c40d1030352009102d14043c80b0051600d5001d05010080c003590b03600041030307940401c84c41000034900b000c6042c00105001c079403150900003041540041a60440c540103903001d90215292007076182e5480100301c3c3d544 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 281977032 1250 281975782 281975803
    0x403030f051c230a0c020706090e010905090f030a08040309050d0512160203010603050114060603071704020f09040c2103080c180a080c0a0b12040f0c09090809030d02 73
    0x12105407040b00880040c1d100d94110442801007203c0703a144107070002c16421045400e484600d48a41d5002d2059078184032a00090415003062840b030390502800201d0507405000e0451256600c40020b07010307900401c00c0084c080aa9425248c0e61070300200000c0c1502d074219019000324015100000d01070400e1540d1010b4940c01101400c0b00408118841e2416841442c40ca0a070402c1e401400000d07903403e00c01c11000714032035030001130f48070001c5d068a0700110b401451644120014010001c0d655000304074134000c002c102003246601e994500c00a210b04011420454118010000300010010035421500640b8028111082c042911180e080d52881d00c2520080024100780301092038411302a014015808150b10450b26001641000c10b480000c680d2103906203500000440b260f44c01c1400507038018008140d002454122307007601100b12244090002485810071441100502c20780240c00e201522820710140314a100f28102482281c00c8076a0080c03082c041c2d140d11090b07441c00052500c821 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 281978282 1250 281977032 281977057
    0x60301080a03030e0c0a0914060d02090714070b011509090e03040e062103070b06090105101110060f060201180f08130f0e09010c0804031b0809040507050403030f05 72
    0x2a16641d500b14044c2c0301c0504406603d121310f05031a901565404041030203410781200004500310400d6110100e40700143c40103016165180c1c0a6001d601c030000b51550040950402d44c194405c042242001c505c924000075281500300710022a0056003114407508400d495034840740c0c09500c40e060802140d0000306031880503070042104115219040c44820360225005007820501e0034115002c2070b250884007403080c03040c1c000040f2102080100c08410303421010685505850390304120110341c81400c400c102106005050190003503030790041001070f400e0f0711406404d011469a40001a802c84c046000341e402650130002c032040b000c507040d118170f00c510b0f4015918030000345141c0c4400b9002e522600c1c2c40c00e40c0e61070308403010500707003c00c140ca880180703ca1094084c0710b150200182d800c47d405070b4100010010048140700103c0d074400c410410a5690140c61444074010f4507061485110b6000c08a411038101410004590740281c050401c480c000d03103940c441980c0307c04049510b0700c41c044a9041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 281979532 1250 281978282 281978293
    0x60702070e01091d0a0c0303090f0810020705010b030a0b070e010314070f050403060203010806070e030a0308010504110424020d050a02100902121516020c0d02040504030905090405030c010b06030108 87
    0x1601032540203000c00e01c003000098214500c04d042c1041c1410f2403036406a4072804a00700c20001c05a00c134000000600c80406000962401c00e03c605446401d01c140310704001d034000c02c4035000d0203c03c5d40000000e01000f003c9401c0900340d4508003c124104955010108508209241a55010b4010300170f210304e44000c09609603941c1e04042e548007003010020403c211080c030000c4001103682c40103502810261000b040507281041000b02485030040c01d40d4083c2d0815214400026000070025040d00c008a80203c2d40e50a01401202980030b41d5024001c629a1300c8022014400c958440402680d004d0b426100040b1525400342c681d4841c000f030701c20050388000e002041c440c5036980005202c5200403d4822003202045035640303880c072000078190864900d2024003a01a410000b0210301d89a580090300b50500c10500203043c25403001ca01901454440d000281090b104506080140c0710040000e03e00d4101030034080d036660440d01e0300c031055619000d031011180c500071059038100c0300e85400034071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 281980782 1250 281979532 281979539
    0x203070605070c0f1a07110307020d02060f0a0905040e0c01090311031204060509030d030501060c110a03020409050a05010b091015020c280b071a04030c06090605040203060702070e01 80
    0x2401000028841010003566605400c0000c40c0106001e0465005003030341040011103a02188200001506c4441442140c070311101500901005503502d2980485030b243e0484054008030303201d4810240c2c2508031500015040040c00d401c8940314060b200b06840800118038042003055858000100d600c0c0492811141000050b0368400300203290840542611030b407560307024141803241c005402450100350003080a15003801e0412089100603003030724013804254074010002c1d00c2c0802c5008044d10700545102c0c48003860301c031201c44800455014104000e203a2003030410326203484401004407440d50030444124102e26008103801d01030b0101d03c00c00d0030464034218003910351038001442c2c0310560040300b02101c1103590b481c0300c0c10303204110341c11010305003054042032000240702da400c80a06c05105110300b001098942c40d190a0850906103030000030380b41d0b805c0c1990a050303180760082400d03051603010382c2084034581007140168820740845404c1d4980e13240580e103030701203402100e420400000040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 281982032 1250 281980782 281980793
    0xf1a0306240915030f0d080106180b0a031e0e07090209120a0309080120070f0203120d091a0f0406021e0c250b09060a121505010e040c020307 62
    0x4004820300c18040100c07820282002c1650311000b151030701c0211050002e40b441070f0a0512100080c100800c01500a40781800c0d40500308010600440080041c41f4468000101d0345440300d0300501007600d44207803242c54281300180a801d07071490030040b108403003035240e540c0e400314040c090340000c0101c0948081410220b071803009401c40c00c0003607480f1603000d02c1c1214624051044400c0340d4001c3d600c2030403250400c00c1c078500f96801140081400f0140c146c0a0820311249000d88520550140400650741e80328000603103050718205221b4503002c0000381c4c45002c00300e0760b4019030a0710f22411000001c01118403482904480c02c480b00d1981203d04000600094042d5008040e0461461070260044e42c600f118000e0710b40085440e96403070360140080c0d001f406088007034440c51040140d00e0581d164100402049030b030090029841c096400801d01452181c02656a40a500200708003040b0042c48160a00c100300740c1c2d841084d01041210340d449600381000e0040d110350000039001149040419a0b84 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 281983282 1250 281982032 281982061
    0xb04181e02040b041805160e0c030601090b0408010e070b070201230d0c1107080705030a060c0509040905011d03090105370203030f060105030f010e0601020f100f1a0306 74
    0x80b0390080d5a42c51070515680ca601c201800803590300d6810f40c0c1c1206610b007440c0303003002042c1c2d01c0721450898041000141040c0c10b5603584030302c08180440d00c0e5101d190050700e800009070030034044d0340c802041c04200b41c101544100b154889040803141c0d119a2032641056070f200304040a400180d4403526410440f080524203440b5004500d00d442ca0102107252810848050f00e0301540061141030741040051010440e603c00351000601801a41d490306002a5940003000001000c0a8550300f480300501c1c0150290740b03035441e02800c1032183e401d1038034180340240840c0810800480810b022824a264004181c555490040c1c50340c51800c100b10006c00b610124641440c2c0d4842084c9004040c48820740b4140c030480c150980041d604d07420700303003003244000000603c900e040007001d00c20401741d104000c40d22411610082c041e100c50703455443c0103d041c2000110b0b121400d2180c0703442410f0411550744040002d401c142c6080048140c0c000c450340d006e4100c0481980d03d0341c08480030500304c0003004d01c2d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 281984532 1250 281983282 281983343
    0x120a080a0203041407090204060e190614040503060106050304030f360b0d022a030d021b060103030503070e01020c0f010503060604030606120c090207030c030e01020c0604090b0418 79
    0xf03a40a135001d0403501450040c250f005480c8640e0080b03030800c9065005240b0080048007141e00c14200c0510301c0440744040c55600c215170402c660b00a8020000c04141d040390040e0401078240d503220340c3c641c02c014046600546041300080c5040c1c040c100460320070950001c1e00c0003c400c86680489000005802c0f215209039281ca041180c801d000071412000300c01040d1a441496015031541c0580004000c030b5607002494080b600742144118040e40c00c040f00319500a8140c43c001626403000000c6000401a5800200e81900c5001c001106054100000e50722801955503040c0120308900b0049884000b0400d0294000321026098491b0b0340c040e0f409981d11110190880342480c3c0d40380c4a14055070556400b103085040710101d030702c09011010b0b0000700030300790440c419840c101b99503030f0040c0801c188200150030414a0070071002c5580c82803003400c000c150014582c2c1d881395161405038005051078019184200d192082c43c1c0414540d080c00c03050740c01d03000030156104510403942d919010312401c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 281985782 1250 281984532 281984543
    0xb030a06030b0f24031216140303041101080a06031e14010605030303010b03090f0d0309030f050a050319023916060807020c0d0807061109030a020f1507050d02120a080a020304 77
    0x18000c501031b00403034018001e5803030102c0940402d0a402d040612104400030100583da41041041102040803004501d0003104286040aa55a100d940d420000e0035203802c020700c1e43d0a0211880302070340301a1103103900d00d4061030300c0c2241c1c0d500360b1030807508171401ea100c2c3d82d0305230b001807004010303072000800595405281c2200356080110114201d9080c0500414480c001c60707541c0340d04000345640420542031800079030501ca46400200040640036020003458444c142c039180c42c03401c03012030090301901d03070f81c10240d81041042e880d0b0340900b9030441044c1c0290100d01c0d800354020036040c0400641c144907500281642e800c22410190125040e03800201000c0070340c41208412103060700c60090950030b160151800c3c0707494128601c0c03e8002c0d2001508140c9100d90103200b102036640d00030030031075080ca40c1101c170b0740c02520702c40005c20740d016030b207118400d812800810004240040401e4070f0f03031800030310f900750b502203900f840c0080c0b001c0c000e0702e00740c4001803005000129006042c0d03004642050180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 281987032 1250 281985782 281985793
    0x6120c0e1e15030a050706120513150609180501110307050702090a090c0f091404081c090807080a020d05031306091505270109080304030302130b030a06030b0f2403 72
    0x46003c01e180c9a040700d001c03074107580000d40411001f58032181c490f0b02008451818841d6040000c1641d0800ca600d5030080d0920100300301902c00c202559120750020701c0594400d1081144038528444102040003060303c1039401d000001544100d950100d034031a112a4a8143c1000f40729020b0161450005041484a503510121080400c1c0744c840100b0091051400000c54103061526800c00e440e548000861600601c80034071001132880026138400074810003111f17102140b0800140007620140d031024021810002c0d424060200100040030301c3c005a408a030700010840804a1f07a13880111940d040c020070b00312040c000a07140c0d802504000380a10b904555030b03070801100b5022104203aa1b03426282104103001010104070403103016000360558001c00c40b52000d40c0300c2d040c00d0300c00104010201540019541040050600300c1000b81201408541d120701d0451411030040045020075142e0840c5100015003086600f610039102d01250aa00006064151816810109a034481a80c94005c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 281988282 1250 281987032 281987071
    0x60a1202100c02180a0506130b01080a0e100f150e070509060901050c150403030c0f090306050a06180209010305010f080a0210020f010e070f090c0801060507020f0406120c0e1e 77
    0x40104c45018a003404800a200d00b40714081012070040403c0078080c040c140000256940e0704401029480200d0f090046480c160140505040c5070925083d206010300c0c02290303170b100c3ea1032984810b07144a44e03085100c032011345070300742c0c0b210b0403008642185c00600200314030010743c1405c0001e44195070060404506114400b003e850a1043d106030301030b210101c403401c00081c540e16010321003d45170141031145a00c428800c1c014040001800301415181c0c840c0041414103205502c0740c8020701c0451280c01c83c8069100301030010390300c034012560000781040004180f1550b540034880440d203800005181c40c807140d5003801140181c242c0608158050201c0040c803850007130042135001075a20b00a007203950305009003592450401d030000310300c440c50f00d402c4603034480e040154181900d802d0305181d45c58003090b200040c0704d01242c007842d607006030800000040010050340f0701e68049110700360400701d071901c50b18075180126041b01c01c0c842c806612000300c5044110040041e0308030030220006100d8000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 281989532 1250 281988282 281988319
    0x1b1816051c0203010e0f070527030a02060c03070303060509060a0302011805060c01020c1b010c1407030203150a0b1822060c08010518040203070e2508060a1202100c02 73
    0x1740e2103988410907060405c01c440c000c04508136802515818401d04018403540c03000f96480301c00c85d2002a10a00c1745410700e05a804020b00540c223540101590381c0d4100c102d0045450350040c02c1c040300880c0c140500440c4920b8030900d00c0d84501c2000d081c450303a01c2c0c55034004644807842202841d42c41041d103200442c4648800c1c005101040f480d400150795003005998507450111050b0703141200e9440c1040d04902603034840b04c205515034104544001d51149401c038507040026991000354075106034480342c00039000410000e88140000781040080c0a010010321241a0349032099045401c035510000d56410408005011460b403094209070718080b03160790300000c80c1c00e47c2d0541c4002c1164030004000700d2900021000310740300d05202c44540c030f04123940465940d075994084d0f003010110f007000288024114506070641d640140318071621352100c0480c06042d241082c1c2d00071380240c4c0c8054010600140d615040310f00598060410242a03040b40421100705109107422070380310210f445020114038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 281990782 1250 281989532 281989537
    0x61401030503041508010f050409170706061502061303051308150f012102060d090b070804030e1021060b041805010f080606010c0606081b1816051c02 66
    0x41c801e0004555813130410700c1c03400b281010300300c1c20700410809400602c9540b20b0404102c1c2121001c0d03902046000691601b40780b142d015801c2c008014502107204c4043c04202d401003c00c90742c210400c0c00c0589074029040380c803883c089aa85601104654030600000e2042d001000340c0010303d803610dd0f6150311415654140705913a00350000c521145414084494040d0840d1340c0107020011459460380e80c05e2200d1424549407000180c82038401007010b14601c94150408548144d1041c05100d05183c941800392a00d0400d071810703800644c600e90000503600300a2640c1e0070000098540386103a00c500c1e00002c4d1051080580e0b402c01c641c803403400007182c0d410300001e0320180031001c141d5000d00660310099030845034141d000848406d0960f8080080000116803550410303c2032030620b440c8011b504000300a010168460380c503a00c6030407948103600a541c0c242d441070100449010b030403c1c0c001510000c401200362100310b015000d200240c59a0707402040100303026020000e50640301207000c0301500803078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 281992032 1250 281990782 281990789
    0xa0e0f030f0a0b010b07020109031103010b060c010c030506041e150b040605030a050901152607120203100204080c060c0106030c090b010e01020a1106090a0e070c0213060b09060304061401 82
    0x35481036400c0b50400c005030041a016281e5400002e050540c0e80c0c0000b40000c0152001801ca400c41c01e00300009910207403c0304500b004060220ba940f450340da04114028400703c0d822070b001929210115200740342034000c0c86000c0341c90f01d20030320320710000c1404c1d100189206031210403502c04a484c00214022200b000e4002480317151922a180d103803002c01c1c0803e80d90010004140e903458100c20814040d4006071000075520140d58807144007609044400071402e41c082202c00c40d114114000a80710a003d07034103248140b00703400f913400c2e400002003240140c2c0168090398416400030b00d4031004506011004d0000c40384000d00200d0034583d603491707000c0320782c1903904228441500c0c0c406240daa542c0243c003c03004c0800c03e100410540030a41c4a0318001c0b00d049a01e00d02c0303038000081c071800c070fa41c480b240240900b06120500c80c0d903040070710b4040d051501c0c060b812400745124079a04404c1c03800c2d0344150400c03600404000d902c1e00c0ca12904110459100420031500c50b655040c0c260000e5403010940c6029 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 281993282 1250 281992032 281992063
    0x3050609011506050f0301060f200327090f0402011e09151e0509041103090309010e0303120a02030a06150206190209010c08070212060a060f0504020705030a0e0f03 72
    0x1015030b40d910035a4161a0061403d01c4401c11401008a50071001c0724111229851300c0040305140705c0c011240b074180101030400c50b00352808007010700c00000c00101241c00106016002c2401e5088051813541810000b00394020300c02d90004440d0801c0c080d20a81c000d01c14504003002c460800e01d1400030702903007110700001a802c8075091103000606c0d41000009402410015451041100d0300b031201c14044071000d00f00700010a1004c80f5031566000300c541400010521910387c913285096a1b90b981140350034900040c0104011b221a0602108403000da00b0114002405540e84203150380296002405102501c0e0355414005504504a11128810a4964041c02031400c118640e5030241c1c0501c400d80035114810840d4485517a04010349000b04c5078442c24540c0c4624007400018250302c40f0102d50561030090b0310400c640107409500c840182c070701549402c50340e2515170046c40b049005410009100b9071007001130b00300c214002c0c1e00000a00c1030050540c180f142c03c0b00c2c0400c0c207108010ba1849413 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 281994532 1250 281993282 281993291
    0x1091b0e06011d01031505060f03062103030a050411060309030c1b0f010c020a0b0c03070501060902030c04050613180e01060512120a170117150114040c05040305060901 74
    0x10480e030309511070340040d0240780030083c80300e95003008a180300c40c5008440c14103550b03a07084000c003044804200c00600c8000c01180d1103a0000c502e100042e88121030b45d510420408211b8039403000d4207000545a580064000c50a5a0312444402e00070500a801920800080454480709589803402144610300080c00355403180c040f8003107189011a20403507000c0f41c800105040700141c450f00e40714070080f1000d103000b82c5154841d001140310714046403c00e8048400000358084840400030092000300c0c404c500030000c86c0e5907544010f080740400d442c441300d0714208000c2001185001d202500e0a1081a9690910f07039640307a0f80c812000c8500542c2c0201ca03500c480d1001003101080c40341c02e00400c0706175232304181c0590b50060691183e03e4003002950b490170104007020903038415661000d236800c0b200100c05c803a507102d41c803140c1803040442c941000303803183c800071610610300840700d00d04940c10002420020250081048041c042100042042010078000040407030340c1001400e0203040743c00300000c1d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 281995782 1250 281994532 281994539
    0x308010b0c0708010207080903210d020a0509090403021c0207030506070e2e030605040b090109021612201b0402090d06091406060306130602031302060705070f05040e07140301091b 79
    0x10300f081680500a1400c13541030482810b02b0320041e00303d40e030303400035042d00503503c0c9c002d600c0c181c41074042d61002c01d0300075036650104010560009007498842d20429088098844001c4080b6a610f2807800024038580046010a000c94010302c40b9480c1d8a100030001481c0c011303192201070194401d0114807040040003154181100c0d01403240002911007650144142804e0b080841d0b1690011300c6020700b956070006404105040590418110039441103600701c00740c41c00b040041592100f4600a0340300d20040b602815032010010f044a0480305024400c0048080481000300941100310307201c1d00002c207504080d002459a00c55555154810810640400c2e076070785041d03240220052207e0b00a910440c280304111002c3d205d14004641d212401581c0ca80e1034030902181c8889900d0001d401c8640403801c2c10403c500861078005440c01075402d00e5140c0c0d40e49003000280e8142c148401429040301c0b8081c081c10b42c0300c541410480c80d0180001ca404d02c0c00359a0048604032540c04210311032102e810030b2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 281997032 1250 281995782 281995789
    0x7050d080403080a2c030c061e0d0f0b011106130606171b061c0b22020309161503020705010e03031003030e0f01050315030f0303150102070506070308010b0c07080102070809 76
    0x14001c880b1999004191740b1039040200e03a507007000540e031902c241808120362000c4541402c0d000404820b05400781c4d1a0020400004040d0000c144415031680c10f11030402c4403944202080b0f1108a41c0c40c00521241e21401c03502d100e07140c50600c0594a90703403030310008102400c1c0300c0d5504500341c1c10f034030007400d00110034030070501b02c4e242e040002c0f4440e40007003085240000129800040316148446d00103549001200000c07000706090306c00304001006c4215001124010f0780c0910720a00e00901a5610000c0040d06c1401790310035030090500001004030081103981c070a0b80904040d511404c00010800700d00180c5500e0740d0402c0318040e0714460401c00600030540d101c2000c0d1404c400070740b090000c0c1c0203250000703001d81c08018154048008142c41115066030200540062420786000742d0b90350741440c3ca254220342804201460142c494035070006100d0424508880d40c440d0035503601045a404d100441059a01c41441540706101e0100007041c421000e02c02800d903144651030440d5a801c607003090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 281998282 1250 281997032 281997077
    0xa020c010e030703080a0f051201090c0806030a120f020a020a1403100e0c011b020a0e0603010c1d190b0c060414030a0905060901090b04080d020c1207050d080403080a 73
    0x41c00d000740c001420820015010100351001c0e1107aa041c0742c20329104402c0c0486490092804c0344210624820000403d00641e60019002500641ea026010b542c0d0000345681c03080f45003001400c0e042e909194603001032190401d110b03d0165031041da02070b000345800140344802603400c0005490400b089950107441c0810104007075100c640414403100700030102c4c49485002144c03010b41070200c82c43d044942c41841d0b06000d80f401f90b00400840d002600c0f4403e042200804942840c080d41c40e203054400c0c1140200342254243d00c0c1382c1120217030b00f01c80005100c0c488800b0b1460b065451707600300e00895042c10f040064030707039100400028141e9290908020206107412805440c41e0b400800000310265800340059007074807029211640d4130f17008040101d079402d11a6202c038501d4100402c02284da00000314080092149035400c80740112181010005c0540728440d1981e0030f42c1c0100c2c01007003182403031240c65090601555805041c0707580c2c0d4459516551040016200007a40d003c0c0d41c4c1e1000101109 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 281999532 1250 281998282 281998307
    0x7080c100807022503051603030906030902060d02070206090d0f0302060f0103030c0b2203050408060c0432060c03070311060705040311060c0a1a220b1b0a020c01 71
    0xc00080e1401c2c141000380d110303000160f81600801c42801c0c028281982040030400455202085800300b40151085c01d000c140f00380411400112004400a180b42c0b0074051158481e0b0000c1801d031421910340c01840003548000b5040303070010303418020140703da40c5052000a1560042d0718410560710589002410810020b10f001a8292048010b2010a50003254808900ea01010051154440d084011550300000075000c440141440b1140d080542c0301d4040c000316466001200c80c503481c0c042c0f8a450b13034003841c05511030000420a0309040c000c1d016241540101500c188503074030074801d4003c520b041c2e000700032201d42c0b0740c0002186010941c0c06031405403c02c44c2d1801800300c03400c1842008001c0d22079444058488070103506100d180f60394250031100c0034000d000c121000c494072441e0980450b400d0425090554410000003105d0f040c52159200e44d15090450017030300100144d8441e0300c480b1001d00070f0403030040114029034150449000504e905000368008000f052941d04c001851101d042d031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 282000782 1250 281999532 281999537
    0x1009060e010f0509100806010f0303170c190c05010f0b12011e0917040f06021209011e022d0106050f03033403030f0501060512012607080c10 62
    0x100410a41c40c1110b2080c1c1d5812100c802c8981c80c1d442c00d054041200342c200d000c0a0080301c0c000030300340c07036062207120889201c0e4845540945001c02c100502480031500200081d5040000c616024440413a1150212007418004044d18180d102c0a007121003400345081140c2da1000542c126140c03203101d151580300b05500034011603c030900800070030000c0403103480746140c80e00d002d4000c00c401c06082003411300c060000c0544a9680e0980b40f0307114600ca09c60200540100c00300c86620700b202c1811201c0d01d4406844921800c0385842010350100240e004046c00c40c002d80308542000c4408000c3d1880c0301100c0105a96803584800a8070b01712485a171016204003404286140c8a44011080d1030300700306011807090044041d00e014400030006a10950541281c21030388508054141d4081e24040a00c008200000d031f8881c00203440700d00c10310741444000f400c80340041140c4181448000c10a036480802650025003180003203151100c9900140d400b60030a01c3d010f03406041840d0003050609591 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 282002032 1250 282000782 282000809
    0x618071805010501120c21091403070624032618190303170603010902090f0108060f06010c060c02070801090c080111040506040312020a02100807110f030d1a0603100906 74
    0x41b8000303000c54080c0c4101c0c01182041800b00601542d5a0303000401c2c4a030000ca1740310414260415503502c0e070f405400300b11403a618284d10448011f00040c480281d0000080030064601d0464071104120305000301d0104d011070600c01e140e034401520328080c2c030b06200405d240f150301a110714100715011040402840400c02152010004644e0003500070303082284031000c4c00b00c6da44603600803d0140501a4001e5008407480d001d20050f10a03101d4054100c80f00c020a40e01940c59264034407091040a07500f81c0d000070003511409000c1429584603100209184c0111a00241c5d0b8192a9080d118070003400d4981c9004954100034024003802821a2115802c82440c80d09040000160340d42c0280d000250510b09051107505942d03000300147c40b42560014821180624100c40003098108100d92003400206441c401003480400001e00480303125142020354100f00c10b0180f020000c210a45c101c0e54403581c0d2017550146515180020741c001c84644004400300b600f00200901511013075030040403100c009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 282003282 1250 282002032 282002051
    0x3022d10091b0b2d0a0302090a0f0e0901050903090d0206090307030b0106030c020606030111070f05010b090a0b01030b030a0c060c1511040f080c060a0309140f1f050405061807180501050112 83
    0x144c1c1107502017916410016103444070744000c00c2c1c84500303d030480d50840384030b0400031441060900d2400d02c1000c120000b4042551181a025140d004051b545c64200e1002c0078040c0c01403501c000500700a040103011259420f950f030b2580d8103200c0b000c0c1c0c421000b09944a100c50b200c6030f41446080da00a90a42c0288641015840c95003494481c0900140840100d0105241080070030b401c402032007140140500f14030708200100c04010702c0840b141d140843c0c40c0070070b281081d0602140e05d00c0101d4105811105803840c005041c2c6c0c90f0151030700c2c101c0d400650721508201c3c5866500c1121070301780440810355201c5040000c0090351060a4000045907849154041456035460b8102d1b0246041483d02240720700162a000c80c0b410030710044140daa0143e5440310072091400540c05841068021551070a198007800070800c4920940d000b9046400181c001000032078003403410350f6250440f4003198003040e138900e020050035205045000d041c1e5100c00042060750307400094142880070403401008075907103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 282004532 1250 282003282 282003367
    0x1060e0f04051e040314180a0e0708011806030803270303040f030e060d140402040f0b030c060a020c03061003050c09090c0f04061203022d10091b0b 65
    0x18048042c071822500380c0001400c1506c80d074402e04081d030007110b03065110640d45d4585010781d00c89008042c05062484400542e00d15401d81d1240a10848d032500103240c3d0030803940041c00ca05000d6982c141c561120000000504a103008500c10343c04000d03001101c25112f00501c0310110341c8403c01e10300398018800c0c8004541d1a551410b86107925003000880d003040c0001085850203a120f000f640c261403c41b281400a1001030303094807480c400c4404200b0382c0e09124981045074103200010f43c142d8040380c40080c05080c0400104099074003801102d03941e00d1844006171800000b100c00540700741d0068420400c129040100c500700c910b044510606502d0280c151a03a01c5201c005500d104020360000d26100e0f882f00d50103407000c9e2009c920220500d0140d03040280d6072b0304800441d11180103c8030012403842d0180c1030208070f11940000034011600c004864003014081c03951003a20944218410300800002d003490f1000100055905a902d0700e54483d0790580d43d8803501415055000660280010340d50b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 282005782 1250 282004532 282004561
    0x30403030f0c23030d05070f0c060216231902011e11060702070e010807060c022205010303080a0f06050907180305010e06061c030206010311130501060e0f0405 70
    0xc40c18a4215107034501d030b00703041820002007416601c00852505106401000c04402005081484c0c4406d02c02901d41c00c10803500c2c01c83c1c10f113642c0c0000c0e40b907205040c0002e0240e0010480003003141c6801100061684078200d1460112841542c17200b00f030b070000d410030703078060040c018140781c3c00c0317208142440030f900042c00740c141c505529900d030035007140c801104c580900000e140c210140811a11685020070300603650301c16234050503500b02010000082c030b2010004d001c0044c0d51090f628250050599070a0200b5070310302849514100300b4412043d40f00204a214290085010f6a210a11810000481c0040b5240c040b8141c510390304000d42448113854640310103400140714900b00e4003400c8046901d02700240030b03801c010125401c1c840804851070b80010103e018076011512160f50b0384130000220b01010170700c503005025803c0031004102185c910390b1884001c50000d040000501c1c1ca00400001300c80098000704003162100d074030841141404040d0000349501903074200030f00d04100140300902c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 282007032 1250 282005782 282005807
    0xb040209040204020c100209012a03030e0a050a0c0609050105090906010e060f030f0103020a0b0406020c01260906010e060609090606030a0b221a060304030c26040f050303040303 78
    0x6500c250085011900c03158111031a0703034048030548944d140c6100c01c410281d48403021883c0025220751000c4200c10010545141c0f085002d80051034800c01c680c0c05402400704201100400d000320548400403500612550f50842d200f10010b442403414800050409001500110304110050141c404503880304207103181c0008013400c045038100c40200002311244205014241005004810300c20440030b80b1007214162803007240d1075440f09454a803001010700aa04c2071600580c0101e4920f046035010f0814880740d09103d040b00d03045410400c10040c00e10405031404281c3e584000010440100d0542450343c0140c801c0b034050f45001e03818000600b01c1607018040500c900d00000c08500d0503a001d6105205550f805000c800c0408030301d4140004032101148001e07075140c00c1144c01101d101d02c085260031404070013002d440c25500e03161411500f024034104c0403102c0008074440e0b0140601c0001a101c0d83ca00224140c5640b1820640d00b41c0c07004080d0350141d8001e500074403051001940101c4c080052 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 282008282 1250 282007032 282007039
    0x6010c02010815060d09060506031203011a0405060a05131401021f1808070b07030902150a110105101d04030c1407050612040318030b0a15050907020a1e0b0402 70
    0x95840300c4880900d801c0c4100f00d001ea2003070b0005008005501c2d250440400180541c000b0856981d4003010301d41c076003c070070107a4902c1100c00c100500201c1001410340400c0b68204450f0b904158a44012a20035031000780510f0205001040d00c900040301c007040a00603003180409009086540350010395200c0c108801035440c941131410441205409500107402440440b140710100702d02420105c0072030344020401c2e070b507019100c800110a00e009001d141407aa601400e240000b450705141d407041030b00004080810845011001944d000b02406828003605000c2039042c4028a07003000040c50004407100c41d50704002074420007011075003000024003a0354000c44030400c1503183c6440d0908001ea1074000b254000701c0441c1d0162100b51064919104622945030070741c41c1888503215059140492200074520b000c2c030300010301070b00843e070088041c1d11000c07442080700700e803194000b50900008640100040e84800c00d0f800900268028030f81030a0100e440929001c01b41e034403030b07120420005002a00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 282009532 1250 282008282 282008297
    0xb0a0f090b120118050d030908040e190c031a010c051203042102060406060503150103120210110a020d1103042c0708060f010905030319020118080a03110306010c0201 73
    0x740361614018940c60300c1040c4003c012003a03060701c50403044d90315508142c641d44104401d098145019104021150340c028004030b06191900d020b842c03034440c0060500001540c0c81c8400c50f030501c414054110301180c40d0714041502d02d004445001550300d80ca480300e041200c41710404003c103c0200da1820710070b00949450ba034030b03981c506100720059034000c880000039840010b0b040906a010608501841c407864080c030481713030384900f0503544c0d5401415140491540301e004100054807031020356001c03070300e5006596501d91050003010448203100c10030011741100190750100d213541404118046140b03420f080c440300864070260756a0380114043c2130300507807101c0000c9503918642a1108034158003e105a5072601e0020401403155800b030719a05d015503005414007141d98001c03403459098030320140c021070820030030b42075161140020b0450f560a55682e2a48000290384000540304414000c050f041d0796100d000000600301c41003084c01882100b0f040c0f0500c105a0f034001e83c2e02c0d482e1502440c0c5105c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 282010782 1250 282009532 282009551
    0x20702090a151e090c0512060d020f03010c0c140d1b060908030703090203010e030903030a0e0a03060501060521010b1207090b0406030e01060b070c050607030e030d11010b0a0f09 78
    0x6000300010f80002918982c0100f0944a04881240c480300341c910342e010510a4804084064a0b14000c04640400b8007004000080c00c608020404002242c001400304d80c01c4500c50000c01d00311000054000300280000b1006800e2006641c249080720001c0385c010001444024401031040c80c466025901c0b1140c548075003814413505410402c0d00c1c640049901d0385d00e052150b0050020306501c01c00300d00950800c903490300d5480c00441a544503d1000d00950b00d0710020000c101e031000900b84900313a001c180c1c0c00b40070022601034402d050183c91144c0381d043d0b42c0c0300f800c225401e16080302c100d5800c107000404014080203048009440944c400304249901d2525000810b4602721010b80145008420205000545503450780014894a10310002040303404e88039409209141308001c0050310ac1c020b00c0900f00818200391005140e42d600038030b00014481c450034000780c1080f07480c4030500005800c8be890707041884000c0c80b40700009501141c4082c0743c5460060070f500958481c0c4106d005860b950203040703 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 282012032 1250 282010782 282010811
    0x6030c0720030706090e131106210108011d010c020c0402030403050d050708010504060e0c0301170a0602130905090a021008091608030d0507020d0c080f09061201140301020702090a 79
    0x84500e076401001c0e03d240a0316007000030040300e80783c407803204c188a14001140b0010302480b0201d0b00c454012042d07074540102d2070180903055101c0d0700c1085030f034450201c2146401804a05803070190a1400c00411010b010860b1041142e080440d00020390345003c8004491079000203100703040c14800d94000d0b841c0c1c0e55508041e101c41c0a0300a081a010b42000c040240e080d41c070000381c83c141c0c2c40445042050342d03141d02c15a442d007001254409102c6400300010300c80401e1840c540760020310290112000c3e5071a554422040c0e8105184c039544a0b074650600340240d810602826500003500310080032030040503000501d00408081074681408203101c003141c0c650a00340040c40e008840006140340f010b541c4c1e0601c990f00e0b030014543c00f000394901782c0800d0130381d880800d6442100069560748000c244d165181c1c007000e035101000d1420295008c000390210380d101c20010707028042d290036080d0169898064400c10b0742d10100d18083c0303e039104104440041e0703105020b045d0490b411845c00160054041e100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 282013282 1250 282012032 282012083
    0x90b01060e1206220b0405070e220b04020301060b0d0e10110a21140430080a0f111201150909050604020c0a080c0d021c1d0a06030b04060506030c07 65
    0x9003144032000300304007e01c000050500201e9039000d00c2c110b59907480030b0940000710115008929085145c00c1c4034808268030a09490b041030008000188503a600c0e0390944040d401759140540d00d40c0c13500d80b040d0846c00f05014580c1c84d00c5001c0d0f024046501480b0b02690284035a05540b410b101400c449a4600f024440e205103c4084101c001c019030a00343d00c07084010070040700c04072942c1890088900301c0107000c031a0940d8610402e88044500c80807408169413091004280140450340c901543e0b4100405000745800d40701212505076948031514501141c00c1016003086691142c2d8100d00d40c41d00764080b1614089803411240050583c584200003800b80c4180b2046c010180304503132256090000110007040404c103004100c40c030846612a0036038036007080705400b1000c0400319030030b000014001e501c0c1c541c00c5c100c3c861420b90042416800100c3d01d0085800c00700c0040e58820412500e403c141c41030f10068a021560380f800e40c98042c205e40c0492140c110024042c1041109107a015000242c0307 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 282014388 1106 282013282 282013351
    0x1503060106121b0c02040f05090c0d02030a0b360a1401140403110706020a05191b0b07060b010e0a0510050d090b01060e1206 55
    0x5640c660b40395941401900e859800030604200b1010030095074448a8455000b0300809005110440780021401c96a817440e20090001004000603d1014154100c070f6680340014a0b20104c1c1c140b0302c00c20001000c40035800c0078440d051004a80c0e0b8912901d401c04414002c1c40a00c001c10140b01c11113040c400070307403c095246004915510300514501c100c0e0740c00801c40701e0280090001405048074190001944007000d06990801889040c000305018401011080425240c0c25151070558014a01c11051070070050200100030201610343c080e24242c104e08590345890168660b440540c0403070315285000501c410543c01542c0360606690050144070030941000700740640c0e0600c1c02e040c0010b001c814804c14043d405a8041c003800603115001440c1c42e54507050307020305241580f044440c4140c0c2503851410065400007031656000740107001e1841411409103042c001140004e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 281834532 282014388 := by
  have h0 := BRFrame.cov_init 281834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 281834532 ≤ n) (h2 : n < 282014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
