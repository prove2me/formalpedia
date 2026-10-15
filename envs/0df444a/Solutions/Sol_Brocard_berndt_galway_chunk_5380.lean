-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5380
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:40:50.255722+00:00
-- url     : https://prove2.me/submissions/28d0f9d4-0f10-4b5a-a4c7-3e58f2f7d36e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 967446043 ≤ n < 967625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 967447293 1250 967446043 967446083
    0x90f010b0a0f0e06040b04050c03090706020601050d23010e030a0207050f0607030c0305190c050c0d1518051b0a0e060d0f1401060303051e090904060e190807 69
    0x80300344030303204154000380b004200318006064020762107907004000103001e2030484000f40485d6000c0d030b58002c0810010007002900d890401007103001d00300c1400145842d40c03400c80091460480440000c00740c0d2139640c046042c91032031003001c1c142c1b9080840240002c40340f5a0666640f41c200e070340b584005104281c030005c6d4504005400d407084800c06000b03145052065101a204200c180804800b081010030640040c124240d01e40381e10400310303540c0c4110301350301402c10a1134840508415072050009024a01c0000c3d0820604920503908580118401304200308982180020700409403041c09003c41c1101110100048103160300b07011144401447d031100c20b002003144d404c8805541000120b5410408103030301c03000c4070590620400350081e4100c00203041034252440c91380102c0c04241c02040e0101c003500c4c948005500b07080e224406609002d814000646a084041c00180071a0f0b0f60b99283d44194009105401c013400d0420580e04d82c20103d031030101c2c1903070f00c05e010030f591680d078500e4034500d901 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 967448543 1250 967447293 967447309
    0x31c0902030703060c0203040e0901020310080316030e030a0c0b1201080a050c0d171c3e040b04060c02030c060405010522090e0a02040e0712080c0102040905090f010b 73
    0x68015004040b02803c60781d880d001801d24a24041c19131005103c001408072581902500c611350000c0056100c0c00d04014900c903444080d000200980c000b44031100039014590088000d2a0305490024100c142e103002007820601610000b0b01818280b510201e80c4040180007426003480312140104241c0c0c1e10100f46071201e50381c404c014029040075441d0602d41c40d02400c1b00c03100c98060040b8048401c80c1049401095003c40c0c1c84410f000342c480341d000f000d0032480c400c04a60007020500d541c540060a20102c0c03001408103000ca020241d0184a0143c040903002910003811001d03880036034643c1c0b00d0101070900c5603140c3c004c80c42403140035403c900c9c1d8103084050b0b03422900e040e1a80c1e401d00000c1c48040f141c003207880000e282507010f0b00d980002d400405001d048c800c0b2400c0e8000d494510258018082641c0c0e04506060a6611a00007046044880c031810500c1c50740202005407036041c2c4101603806031061341d11400d080c07810311051000014020a00d0041400e0030802003045882e0001484245 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 967449793 1250 967448543 967448561
    0xf020c0f0c011205070e12010f2f0c011112010e010815010e18011e1103011a160c0b0309160b0904110d0203010306022502060a0c02041d031c 62
    0x15220000071010401d10381c04c40e58018102c2d0815010030720100001c5541d018807000c009540c0ea4640d40380c070005110500c15000c5070800744840349402e4140c4030340072107003440c08140d18605103000a0b12480c00c0c03500b0b5000a1060490490142e61690100c40e0580311600030f029034922030f801240000389036080044e240146420300302c0b040002c1d07842c0c01d41550801400601000d91140b10300a00300c0c21600070b100b0790f03d42d411410b4895484440c0804010201c0d50204040f510000c4c0820040c0100c40b07500d9006031400c40c0d00803c4030764484036071600305d0580800c040003c06604480c403002c541080c00c3c1014501c43c40c100380486038001d424084901503078000c0c0c456824054000c000003010380c100f680011140101107901c292412111102c0f80c400c0764800d900a841c1141d020400307002c4048104c2e4550b0a9062110b200068102c86800090b41881040200e1040c8040400c4810454032160000403a083e080d0161510f1801c81c1c000b81c5031240c2c0246126030218444850691810115100716610 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 967451043 1250 967449793 967449797
    0x301290c0706030b0121020408010612020901050d080403050a1505090114040206030619080d020c012a0606030b15030706020a0503071415070302090109090c0c15060503010f020c0f0c01 81
    0x40079140c00d4081d4003c0aa044030300b410012014070804505001104068042c0c40d40800165150b1a14648500f154060380285102e41000741044000d42c0e191600305042d500225000c0007410301600e04100c0d00c3c480e50b40020503901031441807800380948901c1480300c549190409001c0c0e40c0d190700034142251900d42c030310700d482c040c4400400c0150400300040c40e40b0810141c191100c02d5124484002c4400b0180d014050560040070014022030703050050742000c01303080c209030fa0a100290800381014800c5000300302840040c4041400380282c54201e17800554000707100a059043c9541031004254151104038020b21400e100090307654800581c00300c4054000c405103040161a41e07501c0350135845c00143c20558428a80308102c3d1140101c0d00c0c60203042251001645c9884c084009844417141d80d02000d03001d86024240500701d40c00002035402141e01c550341c0c800b004940c0c1102030007480aa0000347e051341c60660a1003140c01141d0041c00542d10000840b640203c000c80030070782d286c2000d11802c0c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 967452293 1250 967451043 967451053
    0x103050c0703080402010e030f0703020a0e090d0e0102030d05192f1309050c03090d051c1805030406030f181e030e09070c120c03020c0d060f020301290c 67
    0x1010900c01c101140e0413501c140b40c80740002c2c8103000024600074600c1103d24098000c180204218135007000c18030018000f26a55920518202c7c1d001394071031603c401ca5105004000750031a090b43c0c424400c07107610000c0240201b0641c140700035030310040c9428450490309186040e9410f08450a01e90b07200d903030086201c213003086a40c45524102d905400c1844802400c00e042c010106010b000c0d4024580300360750351001951280790a00740c50740307081c840d42c15040a001040001c103411044103091030941c4c0000300000305403940040082103042c01e01520140c02e9010100e4049012541a0031401c40300400d031034140404034007403540740c2c40c1210442e00204090300c020390000c2413505490300407150a00070308009844103918804220540310440c1c003100041c000000480400c1070110030680703030120518142c0e0042d6074594001c5e688072403160f4203500c2650004600000c200e400d407c80303282a2000340c8155201d5135544080d29022580c100144210a140e030140d0619186010a4030126141080140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 967453543 1250 967452293 967452307
    0x110a020d140a050d2306030d0c03090605030705070501111803011e05090a08042c04110603150a0f060201050f13020423130c1d0115180305010203010806060103050c 72
    0x30f02c03554003e18610703250b2a101c42d10116842400c05112210041c24614082d06141403400c00d8102110150000306100321541460b01182d4002c0c0090152102802d16503517036103c0c42c0c802d6035140900b602c004d00e650b0800402056034410100502504170b1404c4081d035003100701604040c01e8404108100e80c040c08a00d04d40036041e1360a420842d000807140c03007a243e02544135151070440d80c0c01394000c40d07203c442c0c046549404080c07002a070300a84c0d240114407005400d01e03030380d1001414420082d5074402d071340110101c0e8040e51100301340c040b600f0b00106152000ca075244d088440d201014400d140140d4649030001e60700c1c00350603004610031900c51403030100412a0f507080100404030040c41010240c40c90300c0b1101103c24420850340101c10b644003607007090704945402100f0110701c5d08016144885800318019080c000c4428078192980c0041c545900011400101c8003c04508542c9520f041500701c00024088198000e5060b030344d4cd4010f81d0201da6440b0010b409603401500c0402c0440c0c0100001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 967454793 1250 967453543 967453547
    0xb150f0a0b0f0702040e120301050a0b03240301240f0e060901061101020d1a03010c0504120b090f07180b042007050129040b0f1810050301110a020d140a 67
    0x503e0564401000011010071005c0d94074905003000a008420500000c0148014500032459000038240040310710b18626112500c42e003803c01205003804030043d155411000d6540030b4020a00740080019806100d04d032a044100910f4400e1180e808050b0800b4000701da29500500c20034031505000d000f40650b039180680c11201d500480d00d421482e5582071180700c2c9055158003c00711458021900154040103980416003164002028902401800c101c00c00002d18116495010990000010f050381eaaa071801217007882c402c244407490300e000d110b07000700340d54460459000c85481e41c8801001040c80041c14002115040301900348030410460b11051140c02c440c00804104d40310701700200310383c2d00401818042410000b0114040a2498840140350405100d11040514220345403a04d5103007040208080c0442400c001101011a030005000386a20785000c2008001c050001c20404095201c8200309801450040c4014003403078142c000c02d00e114403000c40644101e04e404510341400e451003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 967456043 1250 967454793 967454797
    0x80f0306180c041e260a0803010e0103210e0d0c080a052b0c021302090a180f200309071706160f02060f072006040507050118210b150f0a0b0f 62
    0x5050b05906c600d01c520000600c5581c0034500900407000144059415858204a9911200034040c13281020030682d002d8039501404a4003100700c141d0308443d40c03c4aa00300f52030501d85179084040c0034800c15442130100000090b0a030040788041c4000154181c2c0301540f0308801c0604000b00d400551080c1441d000343c980b40d40300c2d4404080c50303800141703442105004110034140380e43c01207004956100d100e540d41c90085c022440440c0318004200000301d04400007404542d002c6944004c903e4020000600100e02002410082d1400c5030850200c10040399055940b1082100c1c842503440c0003050449002e401001596129003a503000f80001d81d85030784507200d050700010003010400202e0f00441d050220070a04d080d1520714240d000d03010502d000d040c07142c1b504540d64850f034104070000d4181c099006200b0ba00310f0a0702d1140141013402c1c902e6204403e01d140350703040301401d04000b410621420f2400400d9802d000c0e0300c103850b1600da0107204020482c03003c07403500c264480c4003c1042a070101200005c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 967457293 1250 967456043 967456109
    0x6080a110105160b0711010522080901090806011e1401020a02040b150703030603050714010c0605070c080f030f0c0c0703020925080f090a080f0306180c041e 69
    0x4030840c20342100d40341d1134400f010550785040881c0c8198820440c10b80c0a01416900100c0b030780329140381c81d0024012501d4035500441c0600300712404179501285030300c0b983d1081d0080c98074504690792541c44041c00c92a24030400600c0841d04160400018121a907040c05448043c050f0003401d4124003a4080c04050040e10070b2603903200402c40d01040d915081100642407441c000d41c3d00041a90651911900d45501604841004160b45540c1c00c4907a07448800c1c402c0f4141d100c2070108080d100e40c001952241801e0200500d81c2001044840c8024054030140d403042c0c1c5003014404803600c8114141c091846003108a00a030b8004800c14809820042c01103504a0307100c200c29104003444032040d8003850014444007000600520902180d0654014219000034041c0090b1101040a0341c82850030721480020206440021002809a42e00e0600c9240418042c081104c0303140b41145028490354814043e80903600c4224402050442180100d2015101004040044000c44144d87c501c4884c0c050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 967458543 1250 967457293 967457317
    0x603130f20010219050c0613090f0b01030b0907090b0705030d0c02071d0943060f0503040f2301060603061505030910020903030f0414010306080a110105 67
    0x30440d00010219091203407100c0e0a4061094400a03000c0028148416440d00130f0400c2c1c1a860702e14041940401c0007048150b00705c40040c0e940b0340c145100b21800c003055001c0c2120704e00c0d00311494014141c6400100d241d000076a020130114803610100400c64005644000010300c00d180140300c5031800c0d600821502740100e08680c02c004821090000303950b044203a0b100140c020800400c10001c81c8584402076840d1381d42d10131090b01d03124502d29a5002901a4042d40001d00f15500340c545001c02d01006008100c0060f8110140d400c4030003d40502c2c3e075200d81800a04055000d656642c4604256030040b80c1c001c2d0001d1807555180c07101d228458280744070282080f82d503900112119030034410480240102e45003c075500f03150111480341e250701c0c11141c1c401d0087c10800c00080150100c0c64a03040d4182070300058445e40d904011906d10f0060380070b041c921020001c2c0118807000d925076a4501d4050036602070103425250100251207480d0740c6001054022400a055002d60241000e801160440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 967459793 1250 967458543 967458563
    0x16080903070b0d1b0c0510050a0615080103050d020a050309100e06031008070b0c030d0c021903050c07080f03040608040321090308060604050307050913050f060a1a060313 75
    0xd030036002c80d0764407289110003503682d00d104691034160503041300d40c6222080e0501040440e400e4907500d440e500100880d400c85a1307598005030300850142e00000241680d0000c49402d4041150040c281000c203001c1074640b8410510503440e01440091a00b5400d503014003d1410060400e05100c42c207201000503000344111011000540c0d22140d014600c203405d05d10302604aa0300c1c0603140c506001c41d82d080b200302c00c4800c12001074108000003c5a589405e001c40001c5d12180c1050204d00382919405200908260f0030f00038000d2542c804050880900004140c454442c1d45401c05603480102038210078132a0030500c000c01c030040c043c04101d0f510034041c0c00c200804804104140d100041508112620070b0b50360fc41c0d040c1071660061680b540040151038540c079040c10070300025550481d511071340344a070004000141e6146041c01792901100d074403004486200c210034200c140c45600846408141924203452541220300030b489907070103820042c040c41d296172908403480001c076807000000c1d1140240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 967461043 1250 967459793 967459799
    0x5040603050a1d1c1715040e1b0a080f211306090e06090415020d020f031302090901090b01050d0305090a15030b0a0e0f04020d17030f07051608090307 66
    0x14014646403282240507010741071124215800f04441114100d0400417500310115840c40140c4040d80c1141b0098a0410844101c1000401070003400c0c90252090003290034620010910940c2c1d03905901040300e80c1c48280b030311600d689070307030f41c1c00b01c031710013803142d02c00055145a92140d14810440c03040e070008251070444150f80c003400710442c6500c901e000415108040040c200310885103a0040300480c0e034002e10781408d898040c4400305014401c004a680015802d081d5545a4121889600a6844503469103488460300032000c0070081d090b0300a040c120001030032400180304480d070440e48040c0681d40d0742d00301010311080d00c4006e0404c0f014480100094281a603404c500c1c2030082c84582d400031240c1134808801030944250b20b200381d001d210b140109000d01c400842d00c040e070001968045120981d510f00015204090042c000b500d09032400e200103404e0350802c4001c501c0742c42504030b203641c0d645400c00100c45903c2108041204032428041c9240010000c0c00200300055000741111a6035407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 967462293 1250 967461043 967461071
    0x4020d03091d16050a09090e0712080c0705120316080c03071b090c0503010504020706020708040801020304060c0e1c0303061a031006050403200a0e04050102072105040603050a 77
    0x1042c4941508108612003000780e0020808400600c404051811600380049410060003902007401135030f034800c3c1c80d4000a00244070801c400c07170041c01d10501040c40f02c0d43c0c506040107164003a1110300750a01603413002081d903080402c4000110303d0b10300015468a501c2c440781207114440d440048a80f0b0314204a007030000750081000e016038a0090350580c1c10410b84d00c101d0420041e036035001d00c0761036043c40480014150001c0549045070303800c1d100540d0311040c61504030024460380c003000b801d0110100d40455500c505501641c45107209200803c10684040700640302d0060f0020a6a070203240e9900f0030781b10710100300c0940c410920909020810903215054182101100044860244000320030271860086407000e2900412107030070701ca441c280c11a102e8000380400d014108485250791103044926403501e49820004101c1d09040700c01c14140351609070b010750310031507050b181e2526650544c01104058508a40c800e03485807546441c0500d4040141c01500300203182c0c001c195078501c4403040d0b4034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 967463543 1250 967462293 967462319
    0x320090412030b0a0b0a0e0d0606030b10121101030c140301060c0c0e0c0f0a1101020703170f0906060d081b030a0810060219020415090e0d0c02030604020d0309 70
    0x74807034000114034100709a001012114070744400c030f00c2100308a1041110400d004211400015640b0700a0315403010003003c10300a110f0b440c070042043e4900340700001440920660a405510050440f000b0584c0c0e50010601c02e1700a0400a005036404001825180d0700a900401001020b410425800c450461403804250000da0100c2d020468203c0b4178410007560050a078007425403a030090358181001300024265014254411035010400161060b940380a030175840c842801050003503507200d80e94500241880000181c81e0b81100325540400d0034008100c0120344603110100080080741d658404101055400c04000c0c1d030a0030042041c1d0700e14102c18000d00090580090003187c1d60003103a00c008100500c0200507030010300d401d850910903954041642070b040058886400501c80700740c00001c0c02440d202c00d0070328040341c41d080000b8002105801900c0fa01d0301c41c3c01524104a1a0760090f91a07190504002b50302d03411030030006e0b0040ca40b07a810459282d020745407082460ba250444031001c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 967464793 1250 967463543 967463551
    0x30f03150909030a2d032304060b090112021014360105070c15030f0f0e07080c15070813141306031e05010f110409060b040609032009 59
    0x55040094066101074006104400b400400c082483c00110500178000c0721031880d0000004050b00c51400307141030810401c4910104103070200b6182c00b400d107860110001c00043c40402e00645040300002085c124070b0007180c4440f42c02a15140c040c0410682c2112400d0000c0000798002405004140c0b08104c40103c41a0b1001c00c40002180c80700b451403100440c0030014202c1d81002420413000000a50080320802200c1d50361100000303400c0c3d0388a0541c09021505001840d451400550f45842040d075088407410364004416907039401e03205d41405848030326242415801c0503907c0d214196180d4084010300c0114050000c5038206800c03a00840f100305c14540c80318514210f0f83d106a101841c1410170007015600b030590800070145540d80f98036031902c40402d10380313481c100c41c03480c481888001e4000071042d0701000701c100900303074201c003954440d508180103200040e0b29061f4003160320400d00701250141d031116250f0000d25817655480500314203154039850003588085001d4107040d2030f88490035001e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 967466043 1250 967464793 967464811
    0x61812030a0e03070905061c1110021b060a05040e041511040e0a06151d04060f0317180d0501320f01030b070c0c080a030801031a0603030f031509 64
    0xa03050b4030070070985040500d801800740340385490144007240d130303881e0341c90003400b45801003420300c2c00002c0c02c1842141e0002c00086420031445a11114126408500c8440013808a0000d1984460300820300c90f00d80550780d200c0010510800040c4014003964011070350061003078058500c800340e5843c41105940012220b04003030031001c5001d0041840c440b244660000c8034980801c9014a00080141b5801400e18050306100c3c200c08014400d2055000110550801500034800980e4807503540c080004140300a607012800d044103803202c01e00350b038116120990000c020004500309030080103041015030313000300c0d03081d961900043c07521072840c5010006003014440315401042031252540410700c000740300c01007544003003006000240c85010a01e40040d003d1529901415041c0f4100088400e030380c01001ea1442002030b51410198032007040c0381070301d108040807030340142e4040c440c0c1400001950440d602d80c0081c007406100e0041c0d800599442140c2540f5418a0440d00010928041341a103100d90 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 967467293 1250 967466043 967466057
    0x12081312030e0c031c08011a12070e031501050f2706030709140709090c0c11040f0212250c08031b0c07090501141c030512070503010e01060806061812030a 68
    0x581641041481f8010a109000c1403101501003402c040d507840f58142c00c1c2e00c06290344010489251192803400051800135046070034048000e00c0100402c8030910801c1d00c604180f0722081e2807414404107180e01c010101a005e0b0007131175a510042505140181240d030036100740540050b9510031409004e048080c81168810b40c0c1c141028000c01c0c00545030404615241171044041440d07502000015402c0e400c0355101c2c0791481d007100017401034a41d1001e450341007800030900c50080d90000c58550300400c0b540b141407004820070411000c80c0208d0403028400f1500441555004c122408011603000290030b040802042e000080480c1a0300f10521140d1240d11050050062641c10f1080c103014001d80c2031000c40c456141c200140c81c40e9801d203c80c0310961421a07010040602a03402d841d140c0c01406a102c01629000d600101185c0091281c904c14002e04000041c8150080035103900614010b0090707460701502032503a80c070b201d6000d50340542011941d030703110300000750500160081c012256a42c003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 967468543 1250 967467293 967467343
    0x5010608010909050606040e010209060d0f050a05060a1e0e1305010624030f2309060714090d020a050316030605060609031e01110712081312030e0c03 66
    0x14012003058101284040c0b60004a40100d200040d403d03620260480d00401d084111072035050190103040c00c203a811000100c0e200c0400c40b415000001c010a805108000c280d0301e0648802c2038850a403a05500120401014031100e45080b14100ea046881c4041e080301a03a50707210054501c0301100c420324000c0740386c86d0500c100035084c0901c000621a0070074602851704400b490744154a40038220f1000c0c1942c55024800c4e0001c1904001040d810003003040088040582c0c2010424204450908041c0036007000034407001c0c043c1c041c0c200c0025010b034549003091001070030300854400040007070340d024105000c0050b05030b0741004110b801c83c4881c4016540c0d10b01e1850400152000079201c42d100c0c1d41c00340101e4225032800200c01042540201c406030100070207407c0796004004c214000002c6000000e074001c1070004a40140e244142c0e240e55070115552000c601d18010300c01c07141e0007045a2010b01e000440079119800124654081c80241d9420501030780c00a883c005c000d070b10038400b561440081c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 967469793 1250 967468543 967468547
    0x2103131a1009181106070204110c010518030a35010801020d150803030c03071e0e090a0b010c26070f0209010501080c04030305130503031303110a030f061a030a06050106 74
    0x2c580c803c1d210307620b143e00105540ca804980301e14600c51400b540001c1149000d55441c1c0e00854400050166080d60301d0032000415406003204542002e0300401582600d011207100004440102c407040d960072890300760f400909a00075141c2e8100041014007802e4105100446040392402040c00500040c0d50b0301c4140365003015180412014030728206840d40400022202004a0b0380c0401c114001540d00c0d540e618054070904031040c000d8031610f58048a0580707064101503c610311003021104c400c815602e010103c001d443d441c0a00c11b00148000301c4100005181858000c400190040e100d1281e42c4e140701c02c0703d401e8020f4041035805c1c40000b0044400c1d4200400d5090141000b031800380082e2509110b005401e1086110003000c0100c0004c0d0310002810140303008002d0030009083e40e65901d124100d1182803641c50000b950000014180741c00c2038a0042c05030000c480e40002444170960242e11500004d0410f029451f50b0356049004d00b5040ea5000d010603241684100d000280070f5040c4680 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 967471043 1250 967469793 967469801
    0x9040b0907020109200a0e04022403010503071a0703030c0219030e130507080c0c07030f05010c02160f060806030a06090f140a022803020a172103131a1009 68
    0x120702d81c0349501d203100c5c40da1600c1d040341e0a410745211030403e0400e6152880880d40c003c40000c09520198204d800e4252843d010100440c101c48080f000c03500f00070340300c04a42c40da10044900103101c1c030303004010032000240a60010524402c5a0050310b17005060441a43c4111840e0b01c8110005140400075600d035180100e119010070995041c200200d241800e00980b035500084c0009104070f03c04140d540d00b400b01009081d002c2c2d984002e5846071101c4c3c03442c00301d02070003803882041e0141c00307a00300d00800d2112440d07a0000325140c034410003141a1405c40142e4180e24040c1203290940203801940d0085851400b906141301d01c6540f080f4200303182800c012a042c001e0300603800079600700d107400b0300250340c03006440c1041d5408401e81000c001e04048103200301d4400c540c4001d40060400341c0c0022146070038030590a8151162064a00d1554004070b100201050b904642214040520200d104020008a035111140c4034100f03035000c5540115600f18400d01c2282c031800c9219019600b80100007903801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 967472293 1250 967471043 967471073
    0x70603060806060d1509151a040e100c120509031207052b0e0f0f011d07090e2503110f0d02040b0f040213060e0303040e06040209040b0907020109 64
    0x805010715052240c00580d02d10a118009017501000740701405851034594400640e00382d1103020050108400c020200191000494554850706c1415403070101342010b01650706605081805440c19045240640009103090304c0400704001e18800741d03410640c1103200340b5009801c0d400017513840b440c14400c04442c2d09001000d001c100041444411029078a0a0030184c60001c6000c6120030100481001001486015a524440e10038a81302c81281d8201140884061603504001d0007041380010820581c41d10403084141a60b020020801c003402a0b6480500d03002d4545050f0b40052006802c40001c0c80c008180803000c10100510801c2000398840310307800d1454059589500c2988003100203401c00c444100c002c1d00451b11000905080da031260b01013045420018000c5484d41030340c5110b40c96103c20b500900002c0368814822541900d000003d035000c44403840228042c0365101002d00001e500f040e805560040d807501c207039800aa50380d0f1000c910850f00d960001400b04007600f01a04c107541c4d405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 967473543 1250 967472293 967472309
    0x15030607050a0804080703030b04140a050c0406080c0a111c020d0e0d06110904060f031e0b0a1104030624050406050d03080c0c0111030103031103190f14040807060306 73
    0x7500b401d80e801250140d4403d41152540b0385400c21400c05602500040b441390b81d003d0316001c90030300c8913195020030600603100c05104119542e581906282c541c0302e18007601c00400d10a60010b641300076030340d00900c0503402c2c91410782002113081d0489458920303503a0360350f1500c0000607000c1c1d012035030401011103440078500c1c1c850840500f400121350851b41d050310203040070340c0311404001100e043e0400c40301c03e84000340081004a5031158034101c0c001241c001150699503c81000c410001c0221400240ca500829a9603203512851f903120000c0c100b00281d81034000c070600000010130000d1141c3c81501c0c50754421151070015161554000e104143c0210384070324a890400e20103500c52446040700039a250804692503210760545500a01a01100c11501d6092122080c0712043d0480958102d92080d1150120a0040f6840d15128040d50290016011500d500c1e0701009101d48012483e21b0784508149901c0c048002c1110402d600c5a00160810380c00000104a00c41d41482260004d003406 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 967474793 1250 967473543 967473547
    0x9051b010804020109031416140a0509100b03041e08090111070312030e0c131e20090d02040603050f0f010e061602100516110c03120a030902091503060705 68
    0x590f001a00b900303028040a440448480d803400c014100800c203094043e2004002ca9079041d50b5000e05014028405841d02d0252039801c00014440c1401181c1034050340301c00b070000c01c50a0400c5806216500020401e8601e41c8000c2c1e81010222042048110420700a00400b913a9080890001d80090112100507819078040c00081010500b00d4000a546600d94034000c03074254031200c005490700070b00706100c584c42030580361400c0c1e840301030798842c5a81c03680e0081c0741400c6050070140c1c402282d001c600102c4158405001340e80118014034024022800018107990000c182c0f900801c0032191142c008039800e503c01c0c402c8aa020004008410302018924000d100d0500044c10032a11050050903907025103001101d6200c42c14024041c0641002c40800200b000c3e1408030680c0e010906004013103c04121040403907101d090700861040d0b080400034000f4041011300c1100c2d1303403d41d4414012401055076503415080140c3d43c41110a000e4280b140400ca100150303601018180003018020300c052001c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 967476043 1250 967474793 967474801
    0xd060e150102190303020a02010b062a030301031e1a0a050402121209090705070209040302010c1404060f0c0201050919031109061f02100f0c0215010b0d090507080109051b0108 77
    0x52010f01800b258107280c00b40e20307000400b10a80c05400c107000c0340d540c40304e00407902c1e005500701c10100380d900400e07408aa031076580340d142020751680700078080074200d0145801c2d85a4824194408000082e129004c030340c442600c5d80089000034182074a00007003041d00c42c4180025442d1640540b10010000c8000d410303c940c1d8400340f05070500c241c2c0a031a02400e401c7d40081c040318020390560380c5060b00034155900c240f503d4900240241741e40013440d8041141500200c101d1043e480c1514161203c40d21501110559a90f056545042c00d6108904000c400c1005610545a001c4880c050401a040305c8100b2030540c50000b18810b8800002d50003408014104255992a110041c00943e0b10300700b803d4604a900004900b0083c1205038400e909041c00c1c075203203010701d007035200000c00c1c2c0c0268240d4105003000f542c014a266020701c500a401c080500c00101c10881b070784e20608000b2b1090048904640c0d55441803401c3d81c2c03480b00c054800d03401206588002c0b0811282000d02c070842444c01303910343c1c54 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 967477293 1250 967476043 967476073
    0x4081f060605041719080c01111306050d0b040c0e0102060f10060c3f1403011401030b09101701020c06070c08090d0c1e140d0203030d060e150102 64
    0x12071203a180f060f13107900500500752a0034040e039003c0c180140d1030010300d5203260070200b83d1035000000241040d8608030002072034580319030070303200200d0b00d09400c41c0c0d0844c50044203d5441e000f0f0340804071b802e640c401d10044550790f544100d10500c450b035100c0c982229000c4001a09140000340b85030108035141e030410100380c2403802410146d41c5a17091007103070041b4500f00100c0c1000c261840d80325414000076419615581c603000507640d0004410003601d41407203940210f0700c402000c000d9180081044c0300501010710718001c4031000050601d00010042d0749540011369604040e0303207000300c2210001040c4180000c2ca090349000b8400080298074000c41a60081c4e500e1100800e0b810400101070105010401848104c41412078010101c4440c80c1303890500034240c082610543d80101c041c4171030740d4204075068901c030f411110031200107211401007105000c1000c010f503a0480c0c4c940010014032000801c0c9116000c0034040910340d54103686441d204c00000341c9440c40215056611400708000c5940e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 967478543 1250 967477293 967477297
    0x50408040b0f0409020c070510180e13020307030c051203071e0c03050114070e0a060207052e11010b060f0d090c0f090e07120203060c1c0204081f060605 67
    0x140c10680c00c503641d01c045101c0791810b0f00468011000e007500004141400910000300c50b0140c40701265100b200301c198006c02d442c1c81c002154410714100364510704002c4106c003040d0740b40d4440042c08040103160700383e80c0001c2c14001d0f90740084410f810064018007e50510b42e256040b0072640600451414071f082c1c64070811104000c440701c0c2c1003200510036504002c007010230703540215400b10007409100d44041000a4962040351200001480640783d110360f490401d0312042107599540103828a28108020320180c05e400304103034810044144442d103c40b101e070203018000c1455640d10074500c000410304560075034991609444c0718a0080c044030040c003400a0845030f8602c0122000940070005140442c00506550310900113010350010000720f804594112080c118950010388030320b80c0d1140074451103843d400030042d4165101200160300c00049000501621442d5454480d903480140f00d00001e9a0290300140c000f42c200e007a1001c411407520120620300100c90005100103030900400801038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 967479793 1250 967478543 967478549
    0x160210021215030f0a120201150e0619050a03030509030109020a0e0414010c090504050907030b07031a0904050303060108090a0f030f120c05160c080d0804120503060d060207020315040c0f0905040804 87
    0x2105550103c2c6c0064000d50009802d03d100c4020f0302c804580d17a610490500100322082c0d80070391003180100c6003000c0b4884042e0b040d18802480c03130780700a0454038102e41c1a000303a44450b81540d6a1a240d0000d41c0d1090340702d800811404c0c0d000c0030185040d02e000300c48407403100349501e2146e0500d654500640d8012090f60705443c803d40f000a16585c1e0007501d24505007803980094006a00c40741444002541900541607440100e07880c005090040403d002000100311405010340d0024408101c0c10741c1700d00e511581040788402210b4000460340c481e011001700a050807404105559803040c9125000b00740c0d02d080d80040340301005005140303000a4443d2003010503207070044030300c59030180411030f103814000007600c201c1d004c540701c2c0103031400060950041600c0540b140950f03450080c640710301c1801103074818100601405804101503a0f444069040ba0b4000c80c0c0c0360007030094002d140e002e00c0014901c194000c45802e054603242201d5030390401101d401c02c0103a542000104030210b001c160441c2c0403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 967481043 1250 967479793 967479803
    0x2404030c030f020a270b2805011b05190804080105070e100e011d040e060108030a0306081605012604030f08062b11030d0e1305040b160210021215030f0a 67
    0x1512203880000c0c150074000361210800e61199018016058500d403801c070607101c080e22020352440c00400c03101c0700ac1c024500001c04c513070300003010000d40c0315180c09400420b40c0f180c034040e0b040a0300c8040d01c60a44800300d69480015140d0002602c0901e41020004a00455410004410b00c94603000070640c80314400d000903a40142a0100000d03200c80c0e12640c0120302d140f040d81c4075541c40b2000c054495201c5d01d61140028140080484c0700d04e004501002d9034400a00b240d04041d290500646e41c0014000d001c4496104030410452005020252244203038401d81c0e81044110120002600c80c0a01409080c0220880d04212a92040401744081d0324840a101001c10010615200b052a6100510b117509401a400503980e51a00540754600041003140e000030903d4081180030704840c0c048401401040010010aa0242c84507001c404915418030540c0c0c0d07610029030340442680e02410315000c00a1462003000b40c0c80e01508060050600e0880c09041032410042889a984590000c0501 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 967482293 1250 967481043 967481051
    0xf040b040f031e200f15090c06070501050f01380c011e110a08040303020a1806180b030c270a03080a08070c022404030c030f020a27 58
    0xc140350040b2010101c059038891002040030361080300030040001d04c074403a14220846031180c410383d400414000700ca14580d5006040302103031460034a121050203008116207010380f40900760541c4840000340100740c01000046098141014103040b0081c0507400349402080c00d1000209560b8007548216005a1000000c1c18000c40d40c1018040780c42520742d503000c03035032800c150550681000c00c020840d0500e81081040141e60070940c0684602c14017100c4800103e80d4000500000d0180d03001c1c10460702e807407070401000082d074540e024040c0c05941003500031841241020a441a5014441000d814501481815400c001c00100e5180c0200000080c0100c011901060f580078507482c03044560200404a56069540f41003104c210b501441c1124000341e00031000908a600481c8000141da42c00341401101d08200b05040e6001e00401c0a218449001004004081224189640c0295020710b2007030610003407910400c241d2441c03682c41855000354200f00c015003020344080e903070607000324080041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 967483543 1250 967482293 967482323
    0x6050a05120106020705010f0e01022d2a0303190e0d06020f0d0f0c020a060c0207180e07120c0504020904090f11190e0109020a0309020d030f02060f040b04 68
    0x1480a006044040e41c60010010001640356800602c0034125042a2208c140d458a030380812603c04005440282c00750b80451020842a10301d00541805205124010f1034840905940035003070900c02105041c13111190782109030309507101c20790203400d500110300079407405000c0e052225101c4810341c41c0c00244600e0810001d1583c540344020080c507980711104646c1c809644009814a400440c28010f05c24601100101c02c0501c1d1300c42c6042d80d01c9107400811446074142c0e00c0c070300600398070f807540b0003140105c5100241c500c0f42da425020324140340200101d07526000146031480c2c034080740c1c4192080520500c072080481d8011450209856050f2405a621110000418050100301c10010035401c1d21821070001d010f1548403c0310015003c0765007c01d1a4036070307010070013502420700034413004040c410010003c01c50b03d54000c0c5203071152810003042d4411b0310340004440c5c1c003d180007030300801c40310600040200d0781031110300d50006e918492a007440c20191039199111100400042001003801603031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 967484793 1250 967483543 967483547
    0x60d02030a020d050703031b020108162309090a14011205030405060d050f2a130302100216060903080708030910020412050106171903180b190c0c06050a 67
    0x7040344140c000d84103100044651034000c1d5170f0415844143d0003d080703085810303242e10b4100024240c0315016507449074181c03181c4500b102a20320b0207120340c0c00d000707079000701d8905522100e5282c1c098540603280e0903201d4031402d0a004440c40d001b08402c1d01e00f440d10b01c1c116291075488500380c1c1942e800c070352104080c0c038092030818907501c5641c05c507a41c003180114108011050503041240f140090300070041c2d03075488503801d1129984d8000010608609511044800768486502402441c240310710300890107030f540c1d008a80707203007126a290170043e0800480000c0540c1494210801001d00b49441880039286440d8044903015058000b000300e2000004943d18020400900f00001c221501c110360f03035980e4464030154110150030031100b550038984006a030304150752a9224502c00100a0410034006480e40726440d41c0804c01102840200114501c43c03806c444031480c00350005011f401d40d918219140e6600c0002140c520504002e200c1e12180006158404003408655407070030711300d449403881001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 967486043 1250 967484793 967484803
    0xa0f0804030b0a09030e040b0f0f06041a0309060708060f01120e06161103030415021605030d020901030501050f15090103020717220b03010608041e03020a02190e060d0203 75
    0xb9211501030001d010110407207500c00301195100e81c032402c400441e00c1c02030105545107014401e900c20f80e9082c1105050030b1070019650b03040002401903190685903220001501c0b42c1801100d000030700030041007810310301000502e40144403410401540d2610704000f0b84d041c404116100e0420005001c00030850b0400e8000101c518a404141c5250385000200007015208404078400051406500c000b444140882102e00482c0c124500f841e00101300421702c4083e40c403503000024003284045500f0042082403014158030a0030003409a984e8148000040035918107810003031181d0780c450000d060a549950541404866000002e611004c104005800a0250640207840d01074294410340b000c08001004180e842406091a981c01e03025942d50031a42045001f1416009000c20051010500890340c299216100c0c5030443c842c000d414a1040ca04141d40314201c1c00740e07101114100440c40e20801042c607a01c5103034510080107152661f210130801015104600034400c902d1140250b4606203d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 967487293 1250 967486043 967486049
    0x7020109080f0f0d050913090804051504231c17300103050a03030b0604031e0b01060201050606041e17030c0706020304030b01050f040f0c0f031a030a0f0804 69
    0x4140c400e42c6180d10318403074076142070440d40d00290103868a0040c009000340152280c804014052440c041038448a800003040c41d82400d641402c1c080c00000b9030355851009410640500d901181d8465145c400d40c402003111031800f65680f0143c9103c111005d40301d24680209401061107111070023000703428094041c00440005e40900c4000088001600f04000c08003269681124001000c1c070524551420310401c0c00e000042c2150400c800d1180420320a030072840d07212038014043c1c0d18180d601d0303480d28240701c13900c2c00140c96000c0ea20404d0b4248031030038501e02c7c0141000e00080c8024502140045c4170b86c070643c000c032400038411412403103031400c0305007044014007803e048028580c013501c5600e0b55260400a0a642940300e0307000045070051002c0180c904903035101001c025240d080c0001c0003405010008510b800c075940b020032a00f0b40050b130142c4290070545441e2520b0f800d140680050565088041161640c02d02602c46503964030300081c2075014070b4200c40c03039002a041520708002d4901c641c2d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 967488543 1250 967487293 967487309
    0xc080a0b040b1e07020a0308130c0513111b06100e1801201308150a020337110717070201110a0506010f06110706050c0c0402040905070305060303120c07020109 70
    0x5410000055000514400098000d466051007527980d1b8511404880700814003e0150f01a20800c00903401c100d02601000a551400850007402c410350040d40b0f500070f00105400b400104c1d1031290f03501c409004050b00000400400a01a420064020340c1703194040c102003805c154200008904110079032000c80004241c421509010704040c940b2116a00074a0725440c020503103a1001074100000220b01d0800e41340c0004260082c0d41c1c1c4404140250801404100f42440d024615041c810310413518030782e41c1c1d402c50b034424000f2010007260001c80350348140e00b03040c41000f01b0001001c0303020140100125010503411580c0c0d80b580d440100c84071690300216003814859a1000c008202010403d181a203001c06080c0c0e40701c40d40c520048030b403a602c1d081c403680300307030800c141c14403486110b00b00628940b00203600300e4040b0b16804000c03408aa000780d101000150b9504140071001d030f8103004403034002c0d800f20021810b115040e00784814003100502550150340c4001141c00459003d0020000102008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 967489793 1250 967488543 967488601
    0x110c0606120f160f150f0503061206070f0f030b01020c092809110f0f010818070905060a0b09090c090415081e010c2106030611070c080a0b040b 63
    0x2440d2502000e0205000344e1101052a1801241d46402901c0da503440f110030b60364100d82074455507001e6540e0381c4041c001c00d2300084407000c840c80c40c0608010751030040401e99583d8145441003680104000c0750741c0b0340e0104040c00d021142c40c450ba4002034054401804461310204d40d1128529011800d03580381000e4801641150800061070711a4000e041980c000c500b940d00d48020f603420011400c0300c00c42500c0e802240c14541c0b4003d5441400219031040001d070b6618070300036848481514180242d4016000e9580795410094a420080c042400400c400000c0a041414140c000707080354000924008440340041054907595980c0c0e081069800b4003420b922040540b540362060311030070251003a116801070024040c44080e4148500d040112503551040b1a030891002001802078140315407040c0561190404004110b91b88202840c0000603400685e48105900c0c00c00c8017115940e000800c9600400303040c501090140720340e5503006a01a058040b90342e103402a1143c18640802d10758180810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 967491043 1250 967489793 967489813
    0x10c020d0e0102030a090320060d090201180602030a081b0703050919050303090d03180f0f06020105090d0309051606051e030405030a0e0607140c04110c0606120f 71
    0x2050420524059079549240e07207092000581c1d0701e01c1000c041000050048108002181d81c022942c01e825002c01d0403120300c01d88c4a0000303038040e007156140b540940e548440724002c640c1c00c031409004064103404040190b524002d0040d461303018401c0880305001000700011000c0300c2d446000c010111703200f03002989410107424010160303000f24030102c3c02120540c0141046801000311841281c000a000303500e00100a01031002a02d0b0b50442281802014140140350075000206180540007411140256034075085900d642d112541d88040c0c2564941000d00444890105242c03558031441c2c00c010030b401e04079141c401c1c60240400c095aa400103109008105564050014510f4141080d061000d005c130b820f0b1441c2c0c0030b1209039030090040d03004100f001521030040d2280103424030000c00007418070040340c80e83c501c82d80c1c0100464a054103c540501d0442c13070a40b2600069401d00c80c0054246582248a503660301e01c05494140720f50040d400d040781071042044601c120350101d4066540d4148 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 967492293 1250 967491043 967491047
    0x151f2007122a03020f0a090509010c030c26060a05090709061814090c0f07050303091009050a141213230306040303050604200c151501120608010c 64
    0x1d400c00301100d20300b070b0048071044091180d01d9800400254020510492880e5034208150900d680b15441e8000c0c0900307000150004a91045501c10100400003181411044500038200c824041550041c0038003840d030514250200302c11551040e041070141c40198442c49c00007030220025910880e4004050707002c10207103507445a8284112075068a81c281c4410310400d0404041c14203004400b079800711042c104030f5519040d80400e4111400108086c641941c11440c181c40381e101d075400703503800d80c000801d0040340c0300e0820a003003610082107000c1006090307a40d01c0d55140c00e1130000150020190810407000b50700148180085007940f080016968101109103400c0e0040b9032103600310414680c040c0010300c0c80d02c000c54400581e80180941441c1c1d4490b0f50590050501800154005035034034113107000044118624000c1c0c07403100707000d2621540946029450140329031043c401d48800c84c1d0070b010880c152520f408035040f5003400d040b80c025441c1d4031302e0401040c8a500c000c0b125800d205600d20030755 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 967493543 1250 967492293 967492319
    0x8102715051806010b0313080d020403050111040e06150f0c1c020d110604110108070c120804230d030f020909070521010f1211030a0803151f2007 64
    0x40c206609807010f03aaa03d094440890208840d01c440c1c858072010301e81c0000c2c031b04030020049a41131905c01400c058598441c01d084030178842000f40d0000000a007404042e0f1b2a0f05c00940c81082210b58010007401c07991404224096403041032413048010030000510f00c418442c41c5041100e500c1501020710710164000d649400000c1000040f40740600705007c45c40380410300d14411030f0404882196054400011584480b00810580030040343d518030000141c9080386e450802c0a5035507413015503052904094425410404103843e050600d00858464260b0204945e9009061810300195080720400c500380644210300c06a83e00c4000c0c1404c001c80e4540210107080203001e080e03440d26080d10340b80c21041030340b4002c0c003d0061200d02a40104440c19411540e02c1c0e81c2c82c41010000a00c444180110f854503060301c0080f14031075000b00030000a074031000d001445120b411591140b5200124020313007107514607001031104018074160346009540c10311611050f00e0b807000048400407075482005001035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 967494793 1250 967493543 967493581
    0x3110120071802070209010e040201170915010902090108040209070c150e12070b16050c060f0405120723031606050403080105040c0503280e01060810271505 69
    0x550034034030600e6a40e0000f071080d00d000030342c0503005000e40d0342401805041c10320001c000720f04100004080c4188145255950ba014402d007000500440443c9902d100070508141c1080c03401324414005655580e034003141a80d08160150b4403001e56848a0104480b02c00e0203042c06060180442c0e50b071019a480766010a03400d0043c4400d84880d28691820850704d441041c1002c2e003c5500100030600d40d00b090240d050154445e8240180342088c0b00c10141e080c81da04030b0781e088001e200380040006000c02449220400c101440d000c41ca050381d2550340c2c10010403a5200c403082d024116440780c115160820403140d481e4444048c4041501c01842c024025081c1143c0844c0024a10300002880303060078003540f80068100c3d1662801c60b6115844200c1041c00481c0d00505212054030101d0703452514455642c01c80f421a001055403402c0140103445c2032480c0d1000d98101f490104c00c403112810242803881007000d01d40300d2921080c0f0900385415101c410040c21010303289010107020203020902110401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 967496043 1250 967494793 967494809
    0x111070209010909120806040b101106070311040e1e0423030a05070b060f04180201182706150314060f060d0207030201060e0901050907090b010203040311012007 71
    0xc81da80f0780300c083c0700355141410014040b421030500502d400e4000e010890348000040c000285880120300060030600da840f04450108112400c141001078080c40f0059010300241010b0101000d06a00815035100718814152011951404100c0d1580c0c1034180c2c42030b014030103843ca0b241d414035040c90300200041000b0010b08225004005444210100030b0791070116068803584e023040296111a51100d000600c0b42c0d50051540d100e4907003569481c880c010300090403c828142c040002c2c4000741000440d40c80c60800e50304003000402184110314540d09030004007035442418201c240300c7d050007600d03c0350824030351488402c481441c0c10b54107502080007400c1901203c81c680e11081d0500000c1c48200082076040780080010340080c0c80b03540c0050140c131740b01e44000144c05a0381c080b5403030b40e1441070780c03040003a94440c0d0500603c00402c000d000c0103000e01c0c0000700021814200081d6591107030b444020901c40d50080240042c0e8058455007140154030021035a60804078619580c545c5107501403d51 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 967497293 1250 967496043 967496059
    0x11b020a0b131e030b06090c07020409212a0201050c12070201090b1e090303040e04060c030506010206070e01120f0f0f0c032003180a15050c030402090406051801110702 74
    0x3800c040f460107504a0b90411880001519040140140380c2c400814011035800104801001a1118421100a00e005011011464202c1003003c00107a8260031200104062850214080c0b24080400b003e0408000c01c61081003d280c40146e0b028080e201610500e07010b41404101d89801e0500100243e5100741d070b03050b1038103445255000541c000d031440c8420398a41c01605c0306000d18030304010220000d005085a041954602c514000e02d54101d400326255a11075804041803070301802aa90440700900240a41d40340c022401094000c481c81450b04114544160022541c8240e00003041701030f1040d0b0900140c014100c60300c002d40300c984c9d1312104e6549000044004280701c2d00c1124110440041306c2001014405100c1006030005048295103010f4500520300707420741040b065884500c1031aa0340480d40b032070b1050000305c1d0b9000300304140070102003080100681d1040300d0654002d9000300005156110b18250f40d1601d0182c610304102c0d50b180004060f40302c0007200c00b50100c1385c42116404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 967498543 1250 967497293 967497329
    0x5060f04110d0b061201061e0f090e190c0509070503060901080705150f040e04140c150a03020a030605090106020a060f02070f02011409040213061d011b020a0b13 71
    0x40b26a102e100606605150b001085807854107422104c4035480010010451544400e404100d440a00c402c24a2300b003c240300402c8132000d41c0d039418008140c0f25100700659050703001c03990344030f100c030310b5074400084508541481088455010080580702c040c02c5003c1384c0c03400aa000d40786900995802d40710b240c800340000f48611000030700301c042c3c0700041c01091041a005009071842e0f086001c0b8200078803818000440c0e000c2280440d688200d0040c1c4100ea40c00201c56209414900c070004054000c810a0fa40080040c0300c00382165821203c9180050f03950030010b004500400d010742190754071807005400007885035070025050107580d0145008000c0d070b510420100080f4812540024010b070f039a13980c407c02560040200d000300c800b500b00081d00d40340140340010b040740d0003081c6540000c1c41201040c0402580030610759122080c40c42c00c401603448200018104003450b020600034104403007940030442d01e035415000d00409201d9141f545500d516036482015004034064040c070b0541020b114 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 967499793 1250 967498543 967498549
    0x80105090603210708073f171f06020d030b0103150611070905090d0305070f23120405010f0c1403040b2203080103020a09060315020c0a05060f0411 65
    0xb9201500c030030b07100c2051802150b840e00f070301c1d8120420030b0710f40e0f4105004242c04143c03800b070f004254140c0c901c4501641d984209001031120b514458040554012084a000d0340d42c100541c2c0c0c1215414040094a0395100142c440c01b080c1d20131407100902421020006a07150001100d140c1c44005031000e11144400c14011422562400e0170450b200203024030812035207008403245000c0c0c125110566100c1c40d00d44440308182c810698a196603a406070701507501c1103606201d0746801c2291490078410007407003da001007100c000b8146040e0a400c1e101c00c504032030710b85801200e0304140c610703900488600e441e06040340200200c851400c0b00a06000130354400500c112140200c00c4000340005085441e40d07101c03080510401805500c11103038811100e032428050f2504078034024032035550009590b040d481841928217a40d8084080c25003010b0080c000a40a003041c0c00d0f002040c620010f17182d41214600a1a002c160000a8254003c41042c08103c84040c202c0d540b01d00d0041c108900020421014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 967501043 1250 967499793 967499803
    0xf11010306290a0905191a160201030b031c11010506040b030d08040302010b090406020d060602030405060d020c012a020c0306040b060907020708100222050f0607030302120403080105090603 83
    0x8001000b800c0100c0c1041c648068006004507080b00d01d4100307080ca45400200d50102d424a041e141c01c03040301042040003180520900c1000a101d160711420000307404842040c1044110009045c5519207170349401e1500c0c00c01c1840d1004c88181d03010101c2c0740d0b8920001c0e22081d440410310744554202000555a0f0909003d00307801c0c040050010b1003c1c0c0c0840c0300455640d040584120215500c40304805019a0713550000c600030b5004105c0181e450b03400541403411650b0342c0c0d00040940d00244010071840d5580c01c2034805100c07020401594851040c00340030300604544800d0410351032103006441c2e00c002d41c03c0100c03201c505960203c540742000703101090f035940002c881c01004415054000f444c542030500d051500407280c6e00484003400e4071121340c0c03410b00c0102d0b1040e010b441d0b40131501d014590142400011014241e1803076003d16414500410340c40862486020b0007581c00180c9803082522950450b158030492484985880c10a0f240040c5503034028868503114407080c0c40414218a00464 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 967502293 1250 967501043 967501079
    0xf09010537052d1c020a0330081b0f040803090a081923010507020309010905060304021e011b03021f1b030f15031412190311070f11010306 61
    0x20f600300c0e00700c18110400401c440c1845000307010202d041a800010307210b03000210051441504007280c910000b808101c048105182d05000030a0096444010182c01c240e40c281c2040b008400602c0702c4410f4000000d00e441141b040c1c0c401c1c0f010018000401d84404400342c40301c0002203486c453308654900e041c039924100005039014128510010300e0000300482c0d00344140c0c80503030b000807100310390000341142102c0045a0400140e040064030b00465a4001c00440c00b038030b42220400d04505007600411206600240340d2580040240190703007441e8054640070841c50982c00c0080c50b0000d4500c4c00a4460fa8005c035134850103d5140390412803e4454020403040c0c0e0b4594020054511643d03004401420b545d20002c8000781c4d551021200040d007110004000d14015100030342d11901c0014054600545141c0d0790308180c1090192048505061a980170034103501d00c3c001c501807088080c450014814480d00811361441801c1d411b042181d01c480b00d0ac5258405d80f01004810355540c00300c1e0200143c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 967503543 1250 967502293 967502359
    0x40e150109202d03040303050627042307080109050c0d110d02040618090512121518040302010b040f0c09061407060c0c050c0f0901053705 61
    0xc4408043c01060310310800041d40701c0c5403107224000b18081468080d5005407015800251031710104860f6050070b10141e6030140c03180880e02d404c80300d141543c0d100c8080140c0010521104000c070100300622412150000e8484001580c040d2903032011980d000700340900084609006486c0f4019262926030140041a504500494004814482002a0503442c60b204980c030a65a10300800d0b074010305203c4000d500c1640c1c500040241c0b26041451804202c0c190a1501000c204800d0701d40010f01301d5032a8204041c0309266401290f860000f40244982004203807030402080c08000604d035054100c02d25401c02600d0812840b0710a1107103a080d01c010000b05000304030118410003140d442072445400000c0c100c4030543c1080565602c900994481c0403401c00001c41c988600028400c09020b0800b60540449020f0020030103c000308082c0c007814425030384107202400320840042c5e400503e121000016000303040c0108061200030540e2182409a1405130400d44425121088040c52030443c200440d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 967504793 1250 967503543 967503547
    0x70b160b07080f060103020c10050a0f0f0507200c060f1b06062805030a05061009091106180405101d011d0717040f0b090d08060906040e15010920 64
    0x4d400158081e604c0000000402e01c12085184207041d500d1050500822403400301250020039002c0600949002011504000d4504028080d0043e0880303c07000c06105204140c04044054070915800c1c40b480c5401c0c5a00884001218010009500c0040c20100340d011585004c86031001001940c0d050200c130309070b401a08410fa008512140083c403000308000f110301400d401910750300481d0415140c9101103a03640d0000b000d10801c410031081d014050b1600c26804c01660410f6254500002020008580503410001d00502c0052941240384c410400140060000b800c040140900766240351040501c007405902441501b008481c03502e50490300800c0404604450088400320b082c5000ba00311001c0c05081070340841c445255003840351245004110301118050541046000044000c018007280c0d000710414405031a00f01440d19040300081e15501500e40d80d03400410001d0022800c004c10600c40c041042070f000c0c00030000341d07040e108202018808a14120a036a19403601d481581c20401d0701 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 967506043 1250 967504793 967504801
    0x30a0305090a1703030906061c030f05040518010e070f05030a11041206050601080709061d0a090f020304060b040c02071809060f020a02010c0e100c05070b160b07080f 73
    0x1181001d058600801001c00660590300d0070b080c0501210581074800c0e5030004010030080b02da040c004282d00400030740c0c00d40b12084550407203150382c00400c0303002420f020b80d548c00900b029100341e096601401001c0c1a0003104000742540e023428813424401c202103280b01c000000c000920074914002460a1915200d04640381c0c952071001805041d6001858618140400540b00c9500c1092680c114010100001c0600b03080e00010301030748004000030306200101d0401c1280c20750141d40008442000b1900010301804400050840f81c4d95174008070043d401c1131502000159030f0b030300540c02284595810440d001d0303a0000e00c0242d800d505842005a007100d0003c008a014115941f1940c0c00c15010000d29003038280e4911b01100e049080c0b05080550100c0c2c803003203040c0c0900c1250b010860034203002c100c01d00d0543c0020221403401d190b4408001c8644c941c40704100d820071540014007540c03c480d54450074482c1303c02014911001c1e00b601d586803e0300200e0100b03409207091138094802c0b04210300761951 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 967507293 1250 967506043 967506047
    0x909090c030f030a1706240414010e100f020705060a11073003020f031602240406050702010c080703050a1202030c0f0c030903011b021b0d0201031e091b09020702030a03 74
    0x21004106c141c0002c0100c0e03440d5400481150740c11404c0b06c01440c0c072078030781c1e082c075255503200c8a4006c9041d05010303c40d00e940b1000e68850004880d615102d2825282c40f00c00e880c422814003006500c0306400850200f2030704808d6030090700040c2c1c80c15412044410365a505c2c0c60b401a450f214004403400400100f00d0110b0700341c0c407510b25041050290044802540c4000d03002e85c40c5502c0300c180c80c441e0b1102d008200085241200070b075841521103030051101c420031980c4100d547c0c0710b94401ca505000c40042e11000316401000d0f516007158205103640d407070b0052810003400355402480e403000002d071031094484240d41648290703800340c81107015441c2056180b081490065101d2024030620303200071301503480640e509004e85140c030b09240581500c0e120b90020003914050703490200822031094508050495101c0c000f2401c0c85035024030700032842401c0500c00c0b100c3d02040a04000101e4100000030003800745101491442a0b080c00880d81015950307444c42d01203010350003000b903150f0088030101010038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 967508543 1250 967507293 967507337
    0xd031a120a0f05060109061202010206061014030405030909090313090903120f0c0e01030b1c03050f0a0e18010b070209040606180b040f060f0e0a020909090c030f030a 73
    0x2204902107030414203140d121882118a9140d04458661010006000400007030040700700408a00c41840079800031540040d4640700020609401207480240602c0440e1013181060a0510203004450356424079080c1151603600c01100e0781d002d040007901082202c0800000c0b00c440c41c04088481c0402ca0070000743c2c84c003810b041c1034246c04001186007240c10741c00c500c3c4680c980c40c200c8900001142e00040e00e024100a15141059050510b005603000c0b981d00c42100014207046030b0703c40030584420721701d019180f80c0204913041401180c0400c550400b9a045490f4010800c2d040784d80c60004604100c8d0703c1e854003001d01820b50802400e200c0d6000504000001c15041403203180080f600c203484202c40e41c02040814400d801280c9c0b42c80030302600b42018482c4080c0d84c5c1c4014014001107040c42c800032940c1c501032040c829010b00003000940d04043c2681a221614001001a0b4080c10000c21459403051940b0800e0f00c00d000d01500d40066035000812a40300c07010a880d4180000c1412401544503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 967509793 1250 967508543 967508569
    0x50d1202040513020c0601140303070206030a091b0609080604031d03010905100b1c021005130306110306040c0924030b060406050c07060e4606020d031a 67
    0x140d4080c40085950743c1e50002c120010b0305040e030016112158454400e15000040c3d10222400d0f8410701c42941a40307010040b600740030780648100d542c036122035002c04010064500e000c4e0200404c0c9201c1070042c40400a01c0003100c6543e80d0380e4000c1c035154012141c80740e005507401030109842030308014600c450010001c503000e00c014000a140e81c81d5441704d6080005141200d2aa0b564034411656035260001c038000004650780160401960154040b1381208140d9141030148140860400c1c81810303003207443c001440c2d1051003031110240711200b8034542c0c1c200360b81c01132007642007074802d00311544196010800c0300c41b0420601c441c06c5281c80318190b16000303050301d0001c25441d4417220016480d450000e10007001e556031255610301480d40344a0900300260030042c200407000c0c01c20f040591b41d404084d0b10200d90100242c100244001b01d01c0e181d4148882d40703682c46882c600100b10140710300304003c4112041da03003c0c0d44541c07400792001c0b004c5031014a081d101c2c00e1400320b00f45d40d2600700b018510000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 967511043 1250 967509793 967509827
    0x10090501060f082a180a050106140910030504240605090a050709060f1112090a060c4e0305101a07080c120903010f18110621150d050d 59
    0x180c1405002e1441208006c81e0030381400341d22540100710042c3e12982a06144450908403030a041407a4009044582c0c00710740c40c0101521080440c06000c01010f01150841c9100840041014052907400c0500304038850300b44075007640c03030000381c94404034010540f203182c1a9640084650608a095a0340d006506103102041200a0f85c0f0002c503008000745a00c0709101c0c503a541c0c46800765010441503a00310f4015a080009080c0028001a4484d80a8496001c95080c20030815101d8154460b08080301c034010901c04200244003030340001d036003d581c40601180d5000d100c039988100c01101d5807030040c403415400c0f00804458100c400c441c0c00c040d00341c15118242642c0f0340301e071901d400da00d4450507603020000744a0000c0c012105181c244140781100c05ca69205101c01038903040344c0d0242600c45200074240b5a01d00202c04500c0c4e0310b810880d0300765145040021040d50031030b6102e002190080f52513416025180e0390020462502070400458a644000188860700020000f1140d84815042c0701403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 967512293 1250 967511043 967511059
    0xb0303120a0e0d02011a010c080f030c09040204120201030e1f0905100603150c0f050f0702010c0c0f1409280e1e100618020c10090501060f082a 63
    0xd40e002c1c24043d00c56030000960000c140d4424444045ea05041c04600c01414840c1c48104040050314074420b8888071100030714002c0d1039688214510405214001840794000c0c07000074045501c41038845400580d07030003030340c04110744030322116607a41e503114881100a144201c1c0340c807003503030f40352a80200f02ea0707a00c9101030380c1c91103022045900c141c1d43c031034004440403000002d50300080700b0b481c40b502c0030403c45458401010707400d0180c0540644507058a01008441c0000c0309025640540d0311300c0311499124020010441c0e84610103891202c0390f00589000c0082411080860325101c1c0c13490380a21200c000001190104060301a6019042144c0101ca41c1d101c0a0140641c0c40c28014440001b100941910b10a55110035003410116907640e41d60100e031a0170b40521201c0740c1038000051015401c400185d0f079440e0401c00318501040018603030000c81c04c0c103450a007005810b4000c0700482d20721400340c880d0741d9180d800b003c0c1c03182040e0380240304600128100704058084521807448061010340a41 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 967513543 1250 967512293 967512311
    0x314060609190602010603051c201e03030106020d0201090210031d0d08040c120b060108181e0c0d240b040c091a0c15090c181501030b0303120a 63
    0x102590b00d59901c41030150350f54007130030001d0200901c114808134030145544481910002c401426030800e070b00848a44040702009418100b02c10030404d103400c42c854203042c11020a141045507643d0090040c40014000d9040001e10b2600500841408a9000f040c5034492501800110010040c0e8407280180c40295481e400d0558130a100904d4000c200b980d40e80d8040c40c2c103003004c2c540fa29182e401009c809200e94080700205004511003a04a0001d03e070025440d00c60b03251081190303030390307000f200b2407809036400c040702c6503102c40b0b2000c4100c0c00e5842540e90045401c0200115150300b0140078081440320b80d1100740c074411005181041d80c0602c0c1b400224101d400e0b020070105c07404400b449011454462041c003481400150000ea0ba030084a1f030b0301d00d42482221241e40701c10302000180280c1c030001021880c005810700210900308805810304800e0038010138a001d02d120300f524580d41408400460a8070f9520a01600003003442c044d0055150189040e0b00d4003980b50003e07c003e10b46d40e5207080c5a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 967514793 1250 967513543 967513579
    0x41b270b10050406081503031b0715090806011e12020604092906250204060b03160314040c0b07030c08030a0b030f0102090d120e10090602010c0314060609 68
    0x888070001e60303102c0ba00d0724240f00d0003804130180a02050400e1a407216000d2266900104445014120300600b02040d452087d0710361900712541c00c01e501e46200c1003110002d09034030034080c00440c0c425104940d4940d0b030318a1a81c0c2030005061034201007003c050002d0141c8002d4104003084a40301800c100c1c07619a03549921000c85140d200c0801e58032100444020181036130324450411300004403031071464480200c4004808041000c901c86401004102c40310956855a00040040110140c0d10f81c0d286080f81d15480c148401440c1400468608002884a55030340c44c1c130b881c4030300d90140c1892009810414402440e4000381000c0307041104000c07860340003911410103940a10300703070700010a00700300c04410507052006a13400207409a105210490080d41c443d0209101c00303400022840c000c04120f54100d58150611220b5500460804403991403268409200000c844c90f0354002c1040680d18401281a1040010301c0b0780c2180b07075100499050f03c0c04800502860400030200d52401c0c05404e00c07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 967516043 1250 967514793 967514809
    0x170709060608041b0e061903080c03130602061506030406020d06061d060f1206060d020712080601020a170d02070203010e0303160c080a030b06090301090b041b270b 72
    0x6a0020750300d202400200300c1c4034045001304040c80134108103a01d0030a40b450403101c40c010049841100c0e07107482c03d40d107052600c58a0001d1034020004940d00c81d8207a02c02036880c0d00c19101c4034a40203000b44005019480412107502a0300d0705241ca010f201c40010800c92a90800307001030f00c6542d0f0800c841d6014900512661004100a4407194650504c00381c15594407901100c11a024550800002d60790065800458140300348141c0c207000c52762580400700e1054041c8602e4030004510004903013042c00081c91031143e01040a58a01d401d0344d4800004a0f1510402c039030060140d00080b91004691780c0c1140a00003540904200505081c6c40c1c0e00000e080d80c0440c91004841d4100200340302844a00394190821012541001c00c040c000aa4405026202e22000902090b94425280b4081e9071100c0441f46102c40040080c40350640c5805e0800c29004c003a40d00b1524003028800340d00c5658103074100b031411580c0b0504000300b1003106030020341462180900000304c6035070314001d80301030b40c1d14011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 967517293 1250 967516043 967516049
    0x40629160308062b0302010c020f0606060a0c0203060a140a29031c0c0b130804060809100203150f191a0906071a010906050a0510181706150a17070906 66
    0xe241c0e6a404d00324200a42111544c1400e0300864101c03101c8204110070019465410072400d881d1036540306a40d01007240ca10800c240020f40c140128070074001804001c0d0010801071510200c030b806203880d0b00c02110221030b0451413030f1001e10880c0814003844551001c03003d400a4010b810381d101d01038a40703108010f0001c1c001c001d20108000f52400c40c24400c410a4560b440489176040e65100303401522198072501503441588100f01e4004001051500203110300c3e40180441c0d80155200e090802c4042c4c1c10000a0000d14003440510031010010710f0450409802e541308000c0d940e010a083c80280107a048c40d820a1028180c8100000700c92916214024a917050050018200c804071807580e185030194180e00510b826410401c050105558021000c8122041103500e2981651100419901640405031000f01c114a404e030014031032480c14078404070266280d00b40c031082d03900e41303a60220f0600a66145600030126450601000e40004050030440b8114003c85001d1652a0a04401d80c1c007103030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 967518543 1250 967517293 967517359
    0x9121e05062d011208070305040803070809190e160302040506120414151612110301090b060c1902130501090b0901080607120b060904062916030806 65
    0x4010601032060314041d0240c1102c81c032011800b551400020315000c00380c803840a0000d036400079180c810140100100c82c010003c0400343d079191056800c003540070341c21090540d801031842c02c8528042c0c2075122014030580b40b020000a0082c1c4803003101041024140407410b06240d03007040f01240030307518080500400e10203415203080900d000d241c0b950710a103204843e101c507640140111402c010343e442050358445100e080580d072119a20800300c511000d8503003003030000c030b20b02000609000321850007103040e5210302000f484420801c1050141a01c00c4200d006a607070400450842c0c0300b01d869254200c16400284000c615900814200d803c07160283c0c403450000341c1da61000110b40c10724400c0715004107609405000300f8640010042d014a08800d0321454007a0b4414032801540e64003000e8034031845001d002008010749401c1c40b810004c52056104680f40441c0c100e06e40c1e0100128101c030442400c4900c0348064190706e580c1030340c0709040a049942e000889085c042c080d02084c1070181072400c842c4c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 967519793 1250 967518543 967518571
    0xd02090a171203091b0f1002100617030d0b04090b1006030c0806030618030c01090503030108070503030705190f0f050a0219051507061103190c09121e0506 68
    0x886a20b403400101c031901e140c8005200b0040c648201213040008101c0d20084004001c64080c0007805014000003040c2d407191140710f410000d40c0d030004010f0009500000300b04142a00e40c0c3c945601c40c2000068588243c2c000c01041c010321184d03402c2402d020602608c00305501c1d18540e1545000340041740c846164030310080007000260b40c14003c00d480c0c0d023001d0606000d641801030110740c6800000707003802c92105a0802146100c00200b084480a01400c00200304088451500d15181c1e030083c401d554640c03180200c04100380c9400f0040301c40c0309c0d511070005c1040d081441d8a0300490004550240d4103180c40014003070101e9684040000201d1041020b4400c900780c40c0b04010301420224441e4100010f01c1d1014040303a1241082941048124035909e40c48000900d024006040040702e410105040407062000300d403c200615414040d5100c028031454134100343c00c0f02c00d09000e11802c003502c2039521546000c00d2003001c1c0c481c101c4801398441d6610078840d89490b890f0000036105510117200f1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 967521043 1250 967519793 967519829
    0x309050114070c0512030c07020d0201020709020c0706020c1503040b280c180503060a110d0212040c08150f130b09030918010e0402040b01022806051e040303020d02090a 74
    0x303001c245170b100c128220321400c50424460b4141c160060b4030009000d08021900320055a00800200008100d2008190350321407050312503640702c00c0d840c8160070142c420811043c1c00e51400f4000a014140d40002090840da100e0300c031038901e440064074070100191134070103035205e0104580b03a040002c050b9040224080b140040014402083d4905600d920440100d041c403850f60085042500f144580c00f001c20304906011010145105e4020500b034030f0307440007444001c40f9000c0048640710701d00401710205074507038075101e85445421800402d2040081e00001540c00941494101c1c3c01014072a031651040003181d844464014041d22030b030050b6400410030f2202e46c988140f000c54242c0c0e030b115050900c0d5140101c034a12585016000074407840e100e4041c0c101d103910070454010340000040803552202034841c06a420020301d50026900c0b40d04110024448a90f0302440036242c01c0c5c0e40c0050703012030381d0b5a20304a00079084800c526410035000c00050003650340d41080b010182001100068152070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 967522293 1250 967521043 967521053
    0x4080a0c12020303010e010b0901090e0c040b070f030207050303070f03181205010b1905060d36020102060a02070308070f1107090605030d03052a1b010212250309050114070c 76
    0x16800f040300703230204000c8400980d80c094004411202c1403030400c42d441d00c50100c103401c2d5004a0300a2a4400300104203002480342a800703000010b0701a0b02942d42245e11070302819142c0c803502d5409401c0f05000404080000d10481003906911b1082c403214500700e80b503682980d5200745140c01510569100c5e0451041813815102101a0301d020f00f003042001840c12020404900502e158010f1550742c0380300b04240398087c850501e440500e0314440507802201442d03c58003201941e0340c280c2c018400c2c88009081200103100711007616030140c681c00311640d1100b0040303070a03446c00080f600800c41c80c3d18000e028a013040107013401408503c8008030310300c1d0030407050528014a201c4c140d000c0509107414041d445403032060340e81c0800e880011094403c1c1650240341c0440c451351600c41c1d4852081e0b4810301440750194060b1100f0307503086801300c00e16202d15034254045420342d60400b9207003661309aa000a54002e07884021500d10030000032482904107401181c0700b200855524001c919091a13090800c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 967523543 1250 967522293 967522319
    0x507020306150a0b090303040906151b08040509130c091a06040b031f1203120e070602030409090303060306050403020c031e0a06020c01022b0c0e030604080a0c1202030301 75
    0x15003480c03074490ba40d5084000080c0c4140740d91207103904501e0001a101c0c081c0e202072080303402525040c1c40c140f0003103030fa40c07280c07800c42c0300c40c0e00003040010f0201d61071f50b880d8005034013400019604252141d00300b40c108004c104840070003400b541200016849500001a0000b1400005250080700003541000a929070b03440440702142ca41c2c800c0c00200002d002052022050725000040c1103880c0080c0e44100f10039242d04215030300500c084c0700c13458909400305948201800095100007000340146050b00d10810380d244001d004070009031f04144001d104640107030340702103026400f0b40b0307001c1003041e580e40700c54080724000c4e50143c0c010f030080d41d043c480505041000d40643d0702e4a0b514698112150303603805403154241c0200500654001031030015501e005d40564070710095100c01c040c0d002d5840c00080c0c4d400b08145c48108070023401d1081004502c0d01035100f24001c100094040c011550b030319070b1505090b074840d059500900c000b6907400c601155806180c0b000000c2030b42c00071a0745c0d50608211b00c02310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 967524793 1250 967523543 967523551
    0x901020316051e0604020307030623010305030d110a08070e13110909071d300d12060806040b131703041b0b071b120303060f050108220302010b100507020306 69
    0x50780302e1001e05c00180c800140700811030740c04c6000021440038008030103000d13008019180790600c10341400441845408002010444000c3c1c0e01000109040d11514519006809041010804100000f01440d02451080c41a140010700c2c0c0030304004015240800c0707034102241100080300100310b05817036041240d4001d0b080307042828070403540110034910500400d89000e1441c010724080312103d018031001d5103070304568050801046950004001e1040e030390342c1444107070000603207500352101005015200d00410353b2421005070206540d9521034151800e03010b4400741240408860a03404642c0b50502d0790308080c0f41040c5c0175601d007001d0a1100c40c030300890301213070380b4001142d604000740d850740341c12a01101d1380550400440403071614000c00d13415141d40300c0315602444070704c003600b010390503482081550b068903299400e549d264801180e2088044444040e803c03242c052040d80c001c4004844140c0d14030038800071032054200310224140005c08040e074004a14080380b01d204525041c0441940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 967526043 1250 967524793 967524853
    0x204090b0a0f06030b0310063c05011805030a050601030c050306160c060906050c0d1b020303010b07110310050402240f1303330b0a050105090102031605 67
    0xd158144070036240b00980601c680014144d0390281e401903501d0500c40c05170100d2903d1010030003070b680c0d942742c1030000d60350b4140b5580300f1101e84001410022801640140c21107003030704100156007001c005650428803c016021507080040c400a05079400300203490759140b0440c05030010754914900825203401c40e40150740b0035080304040291070300c20518484110401490102d0041c0110f0500340001d107000a0084c04003400e14040240c40d43c0c03140000e04942c50005030801104410b80015000910342c0500100107030010001080041f05800191240d03c0c0550010303500f01200c040040d00d00412104400c041d141c481042005500c2c100042440c103a6003103020004040080300345001512803180380c5090b0b010086441281104541c00d100040c40d0320441d100c0e244082e10185014020751117001e42402c1140560b80c13500242240200c24a40d10044c085040103401c280054a01c1e0304400022030441c4002c0c031844030545244841d00c0100360040020382115200c08204d403030440c90803c28140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 967527293 1250 967526043 967526059
    0x120111090f03070945020402030601030b03010908030114090103020d020622151e08040209090a020d0812100e0622090c080d050a140705011b0503060306010e01060206180c130204090b 80
    0x2140180e5603117281d05059049900503680d03656a00113070001c10010402a4043d03190464540030480168015410b0320842c21912900a030613a04010007880b0034000250054500080f440050402d40c4c0074140d0089900010304840e1040e101e2042140410352000c41c0c2403540038040f12525400c10503540c4201115265001c1b0280f07041c2c40503140c0e02014100074010b00c81400001c0d14004c007070050b00c84696000748803210031b05a500b4088041d803c85000a00e509003401d0210b911501e00342403100c101e80406101c120b01356581d00400201da008204901e8030051011840c0521507190320600d0a000d10800100711014107000d1520310703194060711560700344079081245181d0329070003407122000002d07600c0300181d4500192411501400c080385207440c640c208055600c100c80e421101440c401c060035011140c0d1070703a0300d08811a0081c001c0c8210405a0000008140116042580d1900310009042160003400c14080130400941070f1075140096660b0118051001c90058012603140d010203e550300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 967528543 1250 967527293 967527401
    0x2d08181302071101110309040204140a0509090a060e01140403080405010f11071506150507060f0c0e0915100203040608090307050312040f060614120111090f030709 72
    0x103000703440403185410f0251100c81858143c3c5c0800807145800b401510035901c450b65400c0e83c03040480140000d9110349030703c42c3d0100303060402c8808140700340d0420000b424410701e1a124107000705150105600c02e552140326108200c21450f001c03502984c8683e9520141d0320709420090b003114006c54400ca0031a040001038400c1070016000c0c3c445a5411120307031085036030030700c4a200c001d21031944401c0d41341c100031019840e00c2e6003140c06400309c0340c00b41005001e140344802004045070151243c0d400407405803118841e207401d10340c0c0042d078008551041400151500d030300040107200500429001039100040c14464107a00c080401d800c000c9041c011810095a81e540545a015201a024056451100040500410580e201c500e42c0d04072004120040d00c03100c8208a240718000c0090241200d02859099001c0502c01d1a540d40c0611020030b050441607000c009884212044580c0d05100740c07000070030700783c0e01c5124400d24200080280340c006409036006d503540f0038116101d0f52011000d6201c40c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 967529793 1250 967528543 967528553
    0x201020c0306160e0a172d0304121103010e030a030609090203150403090b0706330b16021c0c1a0315010915030902090606072d0818130207 61
    0xa1008a86681132002c213001c0c0352008540102e01c039501c0202c2d500c1c0b0b650080e107101d0b83c0204a14000c0c1e03042c0c01041c5240c86411120845501d400075001c0e47d01d030f108001c2002000315a9a9400703c40e0701c6001446881150b4200003425164490709182c02500009441d03c06245c05103d654020484810280101185900000d4582c6001c17182d10f00310844500000c4c08051103910b10801034880031a12036205c00081c1089402040820300d420718241c210701028412a0400150305144441e205110207643d0400e4200e0708103030451355402051070350350304a440044c0d85503803045503004410448082c40d034659080c41401800c241d0f000542e101c0030440702e810b001d546501142d07800322100d0030002209900500481306c841da281d0050111820882c910042d00c0c1d0325811160b000750089403214074640f00c59080099074802e60400820f04054000e4107006484401011040550011340c03007900100c0a4962200682c0a03440c1482c0801d00c8400241075883d00a800d072105204e42c484c2103062000d00d0b41c030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 967531043 1250 967529793 967529821
    0x327080906030703060e010e010510033b0a0317010b031b0304020a0312050310061b0f052e061e1e1a0d0e210703170709030201020c0306 60
    0xc240c02035400200041c04140a0740111004007a642e501c4c050942e0340341040106d1030001c2c0150b51241440c055112041c40c42405800300080c00071100d8000d440070310721400c0032009034601180d48103061510f09801098180f003501902e502039107551800c03c404c800748030b103070810580005c020b80d6428014002401d06d40341801c074100035403018840d03594840e400028a000f0182c0d02c020400d1101400e80003410382c0c080003940c0280f842e103000914480d20f4550642d220604100c580d4440710380005054040b03820507504281c01405042680c906941c00c21414040703002a00401e04414610302c0d490080080c0c2d80b05040050404000049480007180c2c6640030104203403041007842d15108104601e8448602c10041c0188400342c0416064064000b03080d60903003000841d5254103103044804448800041014400030810030b00000c0702150300082c101254000c010140c00304000030300c40322070540b2070410071409180b10303481d000803142c030310f1000905d4003101020a6020b40c014078140714540d850869 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 967532293 1250 967531043 967531057
    0x4030c051b04201209030c0a060e0c0306090c060d0e0105070e031b3f010e070b03010b07231212130c05040509030c1e15010803160213020307032708 65
    0x844c11858440c0c1c1203c03071035801812406c2034a8060440020b042001d0b41d444905148028404d540c5a03000384400c26841b48402c03285103140d034002c681c090420345440c40080c01009289800011a10300c07a4841a0071075070100d8000010401c5201148c07141d140400a03801950f01c420f203000d1074032006402040540c120728003010740004969001c69840b8005003001c10f4404518441d0102d030160001d500780c064a24038003010018000c030309001c2523108408048a059943d4103513414a0415103654806a18914400c8888050341001148221850a11091804542140ba110340b10001e04040c40700c120310161004514442c080c0d4100001440d4203211003c80e03a044400098644e1881c0c0e42034114440c81d01c07500f03458002c107030104040c5074181a2a500101205045400380650079000150700b0342c003805128000d0340140300b03644c0400d00c00c60361044900d2018112800d40c0d05e00c01c500d4801e03a0030a980700404a0b4a403a0319000008030300c94804038402d0010b102e0484401e194039a514035101d010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 967533543 1250 967532293 967532317
    0x60e010e01061710051005070b130c0b0c0a02090414030c0d0306060509220f0e2b09090b01020a0b0a0c0e01090510031505030f103204030c051b0420 65
    0x900d004035403502620584811a8021310281c0031460140c00ae15404036105900702c071100364001c4045008003a05003565a03841d851001403440c042c01c0d40820410080040080304c000d00e5414164076040814400340c9903044000780200a0480480d0b006000e45255401c1a001c0110034858400380759103400010f220b14100250354141140310f040a00003030300a01a20502490074403214007010880003402ca142c1483c03140c0c1100400d030000281d954001c0c10712031881c00044008209102d040a01e034095602980e050042f9840f81d180c954039440c4550044504000b66075862614414140d08500a00c0c0c84520910308035544604041c00a004032100c0000b03641056500d0042d103101240000929000d070100404580c0011140700c0300d1a5140341c100b091020150030240b806007881c11224001c604100c02c2480c41002c0103141104844206004000ba02004014511000425018800c4540d0400c034800d0030240025900280010307200c003502c07001d00f0114048607042d0301044a42c10345403075005035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 967534793 1250 967533543 967533559
    0x4030204230c04050102060a090c0324050c04060f09061d0d0f060501180504050703060c1206090e0d080c19090305030a0201022503020601090f060e010e0106171005 72
    0x114010700480c0c1550700101500850801c0c440400d4041d0301800c1110070907400c4a900c3d6170380001050644645410003894084010418400240045800d0440401020355005445082c255803829140d0913030b10524442000038092040d164850110710400742a0700348011a9071400d00d0090001002d041924610000c0e81c0b0550926560031507040c00b07080c1c101182c6880c02c441c5007480781c0144428464035480d07118440c1c64a410f0360050094030700c160740000161860030326540320f030300103080c5511002c010800c0c3d07010b0740f240c0303150b071841040701401c20550f00141c401c1c02c540001d440c2c203a03002c0c40c81040c04a400104220b1207520720032617103814020a40c0520700c0d0300200c01a0392100312604010030354000810408207440d8158058015400058600421454450368019008111640150058101d9401031205042940101003491a405000101103a50300c0d003c0340298000e811a504452841c401007142c9548400d08a1010f401c1c6105c0440f141002207500a00950f03900c41d040c090481 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 967536043 1250 967534793 967534811
    0xb06012d0c14100c1407020402211602010e030705071e0b030403180f032001050c0307112b0b0604111b01060806090304050f03030d18030e01030b0604030204 69
    0x21401c03500e0311641d845640814002201c60000383c40300748100c0f0b980100c61600c41c1c55a1260f104500c2d6204c42e800303104034117242003295002d1001075409030074a1920600145583c440c64464541d6481c41110341282c61000c00d0890a0000c2c00e4500d0900c8191443d84284035100200b500466414101c0c0c003c0c1e403060005000c801101002d89455a100720f12410b408400c01c000d058001200d11190b0780d16500050903140c459117580c100002600002c1d2408561584a003c1c088060294040d41441410181c1c05c000e0f50800c40d07842e5030f124043c105c41d488410b860030001d50900b401c0c9400c14003001da0484049000031019000900000100a003c194414011824a071200d40c00600740416185180703503141a911911140c2c0200c0c460541429840e002000903c0a80824054020480140510724192a05040028460019103402c4d8076000801028042c1a10f61044170700030f02c560b0108403d0701904e0709005d400c030031104c44002c0c180341c00c041c481c2c0341907922401181c050766412600041c500308 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 967537293 1250 967536043 967536047
    0x82406161208100504051918032d120f0e030a02060c0403020f100c0203030301090c1106040b060402070c0b0307031d0c06040302010c030e1206011e0b03010501050f160f0b06012d 78
    0x80c41000c081104d903d006c05c018080c0c1680c141d49004980292038030305c40417003070512001c08aa680701c200302102d40d402b0120048a032145a00f9401c594070800041490704c0d0780710042c011604d0081204e04240c0c400210840e2094040c03040703a6010302d1078001c4608042c65034010551500e03580c400749104112000702c48c403006008035056580160040c1c201d9450390307187c0c0c01c3c420050003084800300c0031409141005007214800203a0501c02d070746c805282035090b01c891080c000030f500900400c030740c00d0361403400100342c210f111006944181a0b51303601043c40ca56000282c11070b9843ca40c0681c100b40c115285840158581c5400c86041740d5081c60030300041e51003170030f048900c90824001c20340d00100d500b41014110000240f024103942c8843c1c1032252482495001c0c22202410340304103d81080203100400066000740c01078061102155101450312032601050480350711104412a42c0081008180c400e01000e502c159902060030300705100003094110340ca110448025644400503403a03030079403e020714 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 967538543 1250 967537293 967537321
    0x91011160f06061508090d0228020402130504150f030809010909050f010303110c0d0b0601050705100f06050406050306130c090c08090f06040308240616120810050405 73
    0x16802c4401000b5064491402484015000062000040c016008a44d1301d64000c1000500381105800421815448200b01c40002882c0c0800840c0030f440c1354030090260300c5500041810442c0c504030707100046e00b000c040208a9403218140c01a544100034203102c901d905a55250684c3e81241c00300f6210315640004883c00744850700000305032030802c000d200c0d010543c40d80d81c0303050b0381c82030f1070340c181e6031070042903055840e000300403001d0307112441c6e04200012888041c0d0883e04002c3c185003203440c0480300d845151a20024401c41d82c5a20707610011050f05425500c5a9000b400003220180007040c034240c0000c0c0e85d6080a4021200c0d100405c9000c0c0801c003680d65054014000904140174400e007501014000c0c020031600c8030b40d9400769000c45110345a000c181c0034483c1d030781511503603180d4982c0c1c1007440c201292079101d43e262041d8200c10408665890014158003240b04510310940049890300b404c3c400d510044603800d101c1c0354014428200700d00c034101010380324203441c00980c664454002440c15 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 967539793 1250 967538543 967538573
    0xc030a0f090c06020a050d08100e090c030304120b0901020f0909060f04060f0501030e010221090705030a0c080d080906010513140705093a0201020a02150309101116 72
    0x411120380003e034190f004110a070b5400e000c0c00a58031807203891401500c3e0715804039050101c8028100052004000c190501130700040c189040318108040704011a2940d4802c0e000741c250700360b0807090300d000c000447c105c0541c0400340c58002e50500000d41d00d60300150140d903172014440c9070b103c00001c600e91a010025001640010700c10300607550b8400c2080da154800f4003d03540083c0c241503081d50f049030b050088450369000e8401c01c804a410340d001d4003581c0c441c00740101c08603000d02000043c1f581c3d010045124094080c4030b540da031452410b60424544240c01401809110700c160421514100c04079070941120000d81d9000300c0810200a41c400400782c20b0074140301c803200e480600c1206a48400034160030002030300e44410401c003207480e0589010085040109801052001c048290328454100e006984180111400500c03558005220340c1c1014802105195020003000b144150421104035500c1c00c0c00002c1100c44124115905184903412503003080c1810104401e00b0000519069882d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 967541043 1250 967539793 967539803
    0x1b120909130b0103080c0d050702090606071a010807150206092509050124050c0c130e0a05010f150305030712052b140f1605091809150c030a0f09 64
    0x10968580c60000d0003a04074031005083d507c100210305003690301440403038018540040c030340b40c1e20380c0d41c0b40304000c0b00f6032040c001255041c204100b918408000d03004614040c0c000003000d041c045040c2425030600c4414400c0c54400c5600060510541403c0410302c0b0304030441c0450841000c0c04204080c0e03100048981c400c155a52a14000042000600c64442c800420b80070940d40c8000889500b00e0b80d5029407e4010500e42203070b1a04001403800180302d5204542e0b00030081950f103900307801c2c3d41c14003500c41c100707503450307510b030f41110b41e100946101d40b107514544105070107a480e0942d1a80d980c1d901900000820410508891000507070040c02030320340550892480c086a128040d009101c85142d00912104250a000100703840708800c014a80c0304d2500404410390301e680f01e81580c7d140d0600003100c3d9082c400100020b00b890b40ba0301100300d030021903c4000c151b8904000420b2450490350f07080c0c4c1d001c00d030791700014405044182c42c00c59400c160842800300303a0f070400080a0004002c4080c00800c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 967542293 1250 967541043 967541063
    0x1e0206090a061e02030304150903020a0b0a0f052a090604090c050705011515051323031c0c150b0a2705040201200111040b1b12090913 59
    0x1809560005500080005200240c0b0214803400400c0e85d0300e000a4900801084010150310f900b175030750340e02103030265001344121514045682c07182c00f42110256100c0f1045c07600c1d0080320203c0c0040f40102c5810030441c0c440b108a15601294200d407644010204580300700300010740341015541c580035900500303200c0104001d9102c0c171460190480d0301c141e100715095428000c0b240b000b103810301c500c6012601c401c21240d00c5106214402c482d02c1d80701305020341400150990103d19105580c0c9140001d01c0911b20036171810443c40105842c1840c0ca12895080d8540e0301440c400c00c0e03038000102007103243e20640500b10f01d020400480c4c082d28600c5000d82d0000000400001c4046031030001d5840c440e85406064034030b488514010090710700455000c0d0115004183c90800010004001d036801d250100001802220721000640b00341d2140d8051010f42d10003241c01403d01c0c03d521050240091980011301c619070840002c044603000310b44400c0d10a01c1e02c080011060f844501240324000e1f40508205 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 967543543 1250 967542293 967542299
    0x1090504151806050a0303050307021f20040b0f0702151204030f0e0d0219080307060e01110a12151206050403020105010f03021f110d0206010302040b060301031e0206090a 75
    0x481c40c41091058980500700200040c0624645114070707010340360041c2c10140b0890079910269103603400074040c20b045108440d2441403110920f2441d00c100c0c00054404103440321580804501c800c44061201c0342d998040004012805002003220b070140084a103003a190780840c000161240d1401840107520b840009004a42008802c001032280f80300740c0340c074215100240000c42c0c1d40d000030000903400c1013980245001501d000e60201120481c4050007080b115103502c051425900072031030803515107803514400e01a1003428015921070800b180b55642c102804c549004262480840d4401100c0e95118034404c400740b100400e010180191200841811005150042c0100012103068005518103400402c4034804a1202c504a0350000c040303914082c010400c005da0141178015680c1802880c8a460f103403581d040c00803551358030712a00540215031550050105461281c03a8540c030414041005200083c400c400c41012401948001901c554051021a54511a174000540d110440c81400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 967544793 1250 967543543 967543571
    0xc180f1f060806240703211109030d03110d0902010c0b0114040b01030b0f0105130f0609171212040f0b010902040f090c020a1b0306020a0f111204060c0201090504 71
    0x10350298006894503420002c5110001107058402105854491010081c060100b44903d041425000f41f0006c26158840400781c0101102c440c110408558000802c0201071883c080c0300c080b02291850400348900001d6001000c007501c1050449003180d0340da10303400000c0da40700f909040304113540035000c8000c558590b109602c07a10302441c503141c4070318242130410513594401e0161903602e55000d003102d5000c0012000545060708140005464207020107400034000036072803400401048e03207403240401d0b2424111883c00c50b081e401035050f103030b80c072105000c04109019000c6a00074407070b0941d5904580c03503500d045409039a4400c07010781000000400810301d043c1d164000c2040b5514030380e0000405940e20f03103030070940d844090000056008040da6601041d00040425400c0c8000c01c2c145541a80740d40e203a0040380c0048142c280041d20a0018015282e084903418407501c0d0910024810505801d0843c0036038491030280d6010400d40d52244000c59016130251000303040b00410602004d08101c2c40c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 967546043 1250 967544793 967544807
    0xf030409060320010f35060310140106031d070335040b071e0c0303081509070e030106120f02011b0506061c0209090606030c180f1f06 59
    0x541d203100b0121440d5001040c3d40450840c25181a1034400d2400d40c2e840041d10f42d405000520b80d4894500e0302c0306106040300700c10607409011207410080c85410480d040c10319008644e003060342024500001040385c0c0382c0c021001e41c11503031103140104070051110300d1405003140aa42c41c140038810510044200a03910000c00812a2090036040f9824600f03400b01001360003074195104e60304070811040c028408640002d01e00b9034061208001801c000b0030b00310070120079004054030001d0b01da00007030081643c071607080c8e038100c050b03840c10015000b0b00c0c80008440c400b0140c51001800340c51000c40c003490720300f0341022000b400700030000034926601e803d00f1000210002012400160f49410075181021300240350b9070510303044001071400d40e84d14814045000d09140074000c0c1e4a114002da000103949408682e4818240d84000d0209030a190052600d0400384a17440b502c02c5840710b5903840e45803d0171805a0b4030103400c000380d1101e40c641e0b00e1114040c0b5002d0700030004407040c7e1000406c0f00b07504000c0e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 967547293 1250 967546043 967546049
    0x30614152e020a031107260307050d0801090507110318030c10030204140604240212030411010f0e03030d051911040e01080a02060f1b0708010e1c0804030f020f03040906 74
    0x7103016015494005c0c85449000c0d81c094006031081401a80303544060303400001160050203002c492070410f007a1680c6141644600c40d000000f01628018070041c01280200c641002041c10090304100903c41c00130386901402031600400c0081000c225a0f47e0b40411a400d1603800180c04090f280001220050181d8464040d601484c1610344e9001c0302070800c1401c603011140b0008181021000050400e416041603110260461040d022513030000d40b45000110300817803089108000d0a0700300f00000d4014200c00c50048240005040020340f2500c003c402c44900c2c002c1040001703501e0380d400720000c0c81502510084044186008100e4030382c200500e0003001076a00096200c0c0c00b070707a81c03403540998172001e0010013904904107102c00d140310074038507010301038102c1c0c4040b103001d02081404400c2d290515540c0079050b00d0703469401c00154a0030910086406112018003000c44c4064204060910078001d070000b002c0003520118005168424000024882d85070001c3c4c1b40d030346d541c81d8240000b802442c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 967548543 1250 967547293 967547297
    0x60d02130e010605150901080705120a0b1c0b010b07031e08040b010e091c052205010f080405030a0516061404022d06030618040507030614152e020a03 66
    0x5400030071303149403001003a8a4810300c0b10740d207840d0014420044030500d8000d0101001d022003800800d000d501d15016031803180000e01d0000030144106410046020b40203510602c0d070700d0552050b00007094244c40c1250541d80000c0345203550359194942210081c12040d0380c007101e842c4c51840c168a042d0300c11110790240740107401c1c49030540d0321a51105070950f01911810100c3c7d002c643c041d50304543d00701c0c0100c403a80c0513041c8141003a001c0c0b08805240c922846980300d83c251040401c2c401503802c001d840040c0d00300d07440c2440103031525658040d681d210300705250080c03007408900300540440310f600d0710702440d5005109000a00030b420304c10900c85801e490803880350b000240c2c1240301d00c9580c12460381c25001c401400010484141c1400074030381c4040c206540201d5a4000314021209680301c1d180100e11810042039110720b18141801100d000c0d60124141c000b104090041c010140403144400c00403c81c3c0d2003032804204480c010700c0131000c005014181e0320003d4210003141d004200452214065 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 967549793 1250 967548543 967548551
    0x6120105030c0307060210090212030c010c120903360305010b090703110702151b0f010b060403020306010b0d060906030803060405060f0d031b060509340b03060d02130e01 75
    0x380b820036896808078001c41e40107030b016030750396042c41d1103070741000480c0c034005004c5d20321544139662100d045138400200c0201c035030744030603c03841c14a6002d8101c00d170261094100f0000c8009a6030000c00300b100a81d40c41d81401d54129008007501c42e401e800408030403005207c07603001c90380c0b440c22501034040e00295612818203400099100c034024000d149d62040000156807a06e0616820042004c99107660a20190b00501100558498017001150031080d0740c00100380201011103101d00b51001451218021507081c002000141c8000840c0c50656681c2c04605803101c1e11100c2c0d440c0180100d41c8070380d038145c0c2060000814042d94400641c00780c201620140002c0d0b44e44030602141800070010650044c8500c048113001c43d1145005500d10069103017542e5a594141d21341105940701a200d000d041c0d0450f140300c018000d20008845019841700714280c441c0012008000032034607161150381c050000020010703806983d41800d54242c06d500900c9045140a0341c41410b0040002c200c50740c03400c1d807030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 967551043 1250 967549793 967549813
    0x30f0a03110a030e190b130f33023a031a0d0204021207020d021c0206181906050a0f1b030902010c0f030509090f190e0c0612010503 58
    0x8607480030b503181c050301d4400d65101882e00703000069002000710002051912000708540ca5154010201600080d0203003e849003004c0c81e802d900781c7d4550101911040c2c0701103c5141081102c1c44016405404043e441555040034041c0d0400c107504142a0b0072a061540340040c00502440750803038100d00102e482046150740c142541110b800001d8801c10003100201ca600e10b103045108925654800f80015041140c0828601c4246a09072901c10260b0070a00d001c030099a8100b100c0d1042503a210074244006800c1c03600a5220000903000304003088800f40380201c250010440701c150440700001c042c122420a0901c000100000e554065000d0300b4141501070718a0b2502804205d06160500084800186003080e0000c0007034800032814800d50b07510440202e041074022000d0345c0e019454099a80c02c9400030080620002040c99008132948028030445031b00900030008d510169400004070780b0f15502e01985080d00707600209500c01030015401d00c1030490340c040207048410940031600103640c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 967552293 1250 967551043 967551077
    0x204060f020a0201020c2b0b042603040b0417121f06051602040603020901080a0605370e0f0c04110406140d020904141e07050f07060605030f0a03 64
    0x41c1201010380140d0007010203100350710340580b04040c1d0345540d0050035804601c02030807207c0300c0000c14040e9003a0680001308400d2021009582c688407216840c480e5071724140300703403030903950101801c040d10701040071001604100198010b0640004a07200c074a880340000300d440e400c0c0104c12a4070f4940000c68042d501c184407840040101075803042d40b01d0707034242240940038190000c0d0004050340e10503100d90002026803280b1522a004e0401d130406405540c00b9030902106442010300343c1c625010510994448050f64410072540140c1c200d106241115000f483c007001804951402c1c00680c000c3d80207404c828007001454802001042d10248012440031340002486d010b5803140c0b10118415480801f8554a0000180303600100080c00509240c5088081800c07210b10520003102c0341d11100074400007a40070f4115140c0c440407060382004c03918240b14024014020340003200004400400d036141000314540101c0b01600020b02165503841c02942c00d40d070340f821b02c64070580200b02c040c40c1d41043c0300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 967553543 1250 967552293 967552303
    0x4030e060306130506040615051908010e01060c061d0d090518011e0f0b1c090c09090f0506091f020c06040f0f021518030c030a1e050f010204060f02 65
    0x60801400a402d144a140f800300c09440000c0510398419a030b154041910f5050704558281c0300700c0e07a9121501d0306030f541c1000b2400c180c2d00454800f8040c018004002482229080c54103603609843c00185c4a440d52030007101400800200141d030035803480840d0041d85000074440264141c40c0c0d64080c456a40d0400d0065404906201100740d1400c00014480200115036210927204800c10507295a982c440810102c0c0109410650b450f007000210000b00b021103e820000301c0e010781d0010441504140c0d44c0c01d000c620f140c818809081c0c0c403089031006022210201d0303d03005400205940f01ca1034008207494480e5940c1070702c080311002d64400b20307100200700c0c030a03141035100c0303000201002d44803034490440e100740380c6a0803100c1c0c00c104580840140c6421801c001c0c00004d90505503229596070450300942010001407602a46c449030140f9640d0350002190440d0682001d600345488660580300000c48501c488040c1440c441c292046c0303c0e03101d0550040c4110341484d40d5884110780d02c030381304036110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 967554793 1250 967553543 967553551
    0x5072f1e01030527030406030c0e0a060f110106120501050f010305070e0604020c0d20030c07050613080304140102010c14070b07020f0d1d03010b0901030f0c0b030f04030e0603 77
    0x4008540c005916502951080da0408003040c8100c803202c0e03203251244680d820340b0300001090382000c54100002501030098400e101c4440c100309442402d141c0104500c40a903124000402c032021400c2c1c00f48502500c070110040303040c10300912110b81c646460b0070101507a000119841c2d0b180c00c0000e5440d01e00301c1c140d2816030f075100016001c485e107029000b05d0210310142c1101d50040c0c0c02c108441d003000080180a62001e140c2e02e403510920111102980c4034501417140350300541080102d1030414002141d42c0c8141d6008a901941300e18000c0029185103600d40c1110081348000540807480302221249561104002d03030090040728a020022a880c0154501c283c08655050049100003100082c038a5481882441240d40403045120a18a490601c01c0308401241c2c03007100d00c8030303540c10540e200800c20806400900100010a002c54410303141440003810b0341000c5845c0341d0810003920040401001f248061548a050980741c1d8001400705076000c41c08074000c08150541c50510b14207481c4030f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 967556043 1250 967554793 967554829
    0x902040e0a020d0213080105060f0406180906060b070305180a0b03160e100908100209060415020c060a0e03061e0a0c030902090405010608190c05060a05072f 69
    0xe1501c0d010400c4029410915454240c50303024000502e4405104c100322000f801e90708000b007210700b020f00034048104403100300f803030042e400c000d014091202d412200805100302d240f00050700c000941442001016a0740061940d9640040d041c0c003811381c001c014110340140074450780c2149545500b08080d02e144d03172180f148155000c0c400241060a84a05240c0c112402c0c103120081710300718400941410307918042c0801081c4e6000702400320190820050340f003021001c6c403c5103003d440b08000341c0c01e4083d52080303006680f190348003554098801d0105000810020708034586640c0302c00000380401c40100c2d0064040c0c49841e00040c04201d459440440c0070201a084c2643c0e0b46072010b0020240050381d8889040c180c80d10144e05c0140c440a094502c2203000300300016201c1c0c201209582040c60f907000032414584045103070000701c2d030300c550000112082200c0d400d9491012140c1540c050040d224043c00303102e2100080c68503415403501800c5005103c2690115000001041100b40c450800390700603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 967557293 1250 967556043 967556069
    0x10828030309110405010b0a020d0228080d0501090b100807090302010e18010803030f010806041104200a0309021306030308131e030504050906010c021018120804050a090204 76
    0x80864001c0d800394248a025103000340e02d40700e040f8080307001d460003030b13010140d650310007c0e0281d85103605000032a07495410b03202520b91422140b4800205030380c45a140d03181007501a03c89400c001038078003110781008400205015640c0d440c8072817001004d22f802a00d0144400e003005040451107a240640700348401d88410039060f003980c0045035034203492090f031034014014241e102c5508483e07c1696000b8034141004565a01e85501e980000102c183d10100c2607501c00300521001841c480c2030f41049150a030f9001075900e01c0c1c440380400c06855454904505500044c4151340c01e03070f05402c51502c081c000d41d02300719410080d5408504840c0c6078400600002e941c2c074082a5840102c0c0038024046011f841034024618810440603180a4000c4003100411b030002002c001c03d050410145070b000c030742401d0024221200c0e8011030000141842000c0070803003900b8001c4d0420071281400380240044408030591090f81c0d1030040180d41c424001c0e14840c1c2c03040c40c0c00040c0e0303907400d000711006e4a50f0908161 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 967558543 1250 967557293 967557373
    0x90b04030908240a05191505150a050d0908070c0b12090c10180504141006020607050703030b010c082113080418140a0c0809010c051905040503030a080108 68
    0x1402c0c058080380c4060031b0005000c0b2609414060091400c0d02242102d00c0a8940402c000c00c5c0d140300800c0c401c0245003440b2a034245c0350001d040d501c15156a02010510040314030b0400340070700c5521802803000f080e80c1e0003c200d8030184d03006481900329082950701a51034402540d96142405800f081d404540c207031001c140240301c0c0c00d444501a005054102c02d25440390005811350f0701e200701a40f01e0b07141c05010001c416400306222402051702d4000b4087c542002440107185100c1d03880c001c0c05058540e01000d0301a44200601240160020a07082d100c03102c60019010040c000802c07030505800701c83c0465403011603162003041072075203c10910704c1c02e0315144c101c40d9501c0c000b0310044c01041d03461407684030b543e842c3c103181071045c510713190001814200c170703103000c1c4c895030025200d84402d80c98401c01054980d001000c41d10103012111806403100701e000c004a903103214a81219030180404079103c405550003440302d6058802c42d00955008004084400f84285040a08415003521410300d49c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 967559793 1250 967558543 967558561
    0x90f0d0c0503070c09021c0615141c0b03100506060d050c0c10090b160e131e061505130e060a0302061c0c0e22090b0403090824 56
    0x10100c1803141c0207483c1070800e580c403021007009040d40610b50140e000186800f90907508041c440907000c00f4481044110300300f01c2440e000c00e1001d030307000c014041a04c0c10540d24020210a0740c810f61050001c0302d84c10080e1011000150441140c0c050113072084641d100031411840c0513261040c00050400d604103200d105000003e85409423407400b840c4000c01186a01c4c141c20300111034100620f001c04035034102589405014084000c00e0b0000303101217040c9d9814400d40c090b810a038051022201103000309040c0140c40014440d403644503160512850400d501080d49802c07550031a1850003000b82e1156510005a03100d01c41d80b0411221040c10a8091001b50341c8022000c1c2c0001c070191070110b506850f0f03800b1a100f540b01c200311910600c0c1e0f00b0b150004010260284000e07052291401c2c0044000d00004135500003e05c0f00d01035015041d0301c0100000c0b0300315034084076455400c40307020403081c101400c015001d9880ba0007000b200b0b0041c0d00300380200007000402c828507450071307000341c183c142e0b070340310381 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 967561043 1250 967559793 967559807
    0x6070c0611070b031f15020d021b0607022103040e01030b070302030415200319051f03020d06090c1d06040b130504030207181a031908070f1704030b090f0d 68
    0x40c10b401400361724804180700102c801d801051100344e80050060100303600020b1300c2d241e4a1000202e641c58080509402074543c40d09459100e641599600f0280c1100d88030b2455090320007018480380c0c4004200003829010266441d0b04890040b002c00c0180d844100b81203040c2c1c0b000701c6000e41887c503140800e600d00040343d030180d190b4800e9400403202071704880c0e40c10211580155001518801d03a2041d40810000038031569400405c040440214851203114590b902c0c2441e10000c2d229450111840040c010725400024102d54045241d000c026168588078440d854a440d80c0d4551102c1c5100044590825124000c0516402090b10364004001c1001c44042c12000308100d00318010014002100341c2914195441031040400100c0d10480043d40c803d10000c0c9421142d1107a4070100030034403c00b000e200c00f100c0703039600614601d58481d01e1342810059050503600c0103005c41001022060320304445809802500d1044c1c09504245d220780c810390f542e030711054615202507042448418070550068134 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 967562293 1250 967561043 967561081
    0x3181207030b0c0403050a120e040e1c02030d020703050a0801060504120b04050307050109110f0d0f030315080f010f050606030402100806011209230a0b0f040c0506070c0611070b03 79
    0x50f659140c152203545450030810b0f908021901e54910340d1801401030741022550846c8030702681c0800c589203600d0403495983c2c030715601815139034240034000181113109004440110502e408255622101c80c40e0080207903002031601000074051100100b016489007044608540403000c10b00f82c581030710380310000800e5001d071013114030703100030001440003440038001d02213128000c900201004203500b040c0302042c54040303c0c1c03620600d03062980320b002a000f00300c1614a80c0e01440c00060701200349000d030544080759084020948248056035004040c15000b074000c20302e03400390511a41d21500e0520000b80000d5800941c000d0311844000100ea09c5031282e1a07009105140034401600240103503001c591403080140d501c10006050016108000001c00d070655a042005003003400300b944070b00129500107441180c0c8200c5040104007481400740e859005054014070b80d1365954070a213802c00b250f03122482010003060f0100d250002001003c0b82500883c2c0104400ca403035659910b2203001200c003080c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 967563543 1250 967562293 967562311
    0x92f0c1b060d092105091302130506040e071b0819030f1107050c0108040b07080613020f0c070510020304120f0b2e0302100e0a090c0203181207030b 65
    0x48600902010700f0b00911068500070100c1080c01c60300c0250780020341d80f845003c281405030401106c000b0340c80b1805110803030b02d001c020040c1c481000c0c2c4201016540c00e0382c020390303201e5004100412010801980ba0780500c403030391250200b41c00b6001c00d5824500111802800e10b120612043e54000d42c4100d4000c00d001d000d181c00140b4000250b40c003001c07212800d551b44c0c002c10001c41c444041000030009510f0113102400c02d00304514203035441000034035006100c401005191000f0903026280c07031a00c2403107107070703422001c0d500e507584e031220f030310442d00041007001180c4620b03400040c145c244011600b14500043d0702551401c4c1c01c20352260240c501e44102120f640e500c00f8003000114a017242811b0164417400c0491800310304c0300000c04084861404500a20021040204016918000404809481420201e90080c1345200040c6960300702d42c0841900c40c100301e80006020f07404401851807400040d001058a495103041c003601080f4040305107159403011200380040382e684503403035901202d00c1d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 967564793 1250 967563543 967563547
    0x20105070c1e111302070506010e01050a0b0c0307081c0b0d210c0c060302090907050c0a1403160b1b030f0a020714070b040609080c090406020c07092f0c1b06 69
    0xf42002c9068041c0e00c04c0c2100701ca690109040c1d080200c140841801052100200305403941000006071800b1910b10800030b003010001950000b410003402651400b5801c4214070791071340302043d05403d103e40810309145580e86452251005480d10306029800286c20000e1000e204c080c0f5a1100c0240c0a00714106c800e21103d141410001050400c0c504042c010715030f405600c50700c659040c07116101010f403211040c000203001c20748056000141c54032286030003c6000d45c0c1441039010403821481103501d50b400070700c81003811005004024403003030300804a0390000c0e0b8000b00000c41c5101140025641c18034810405008182c40742441c0d0090480345010344202580d1501c0202c840f494402c3d81e070b1004400e0f04000c10100a10750b0854100b000420820018201454070500080c145160052004008507030103e01480b2901d020003410010740540d24081000c040ca202007071901200104010603024602ea000c405014402000c3d9a41c42d2040e500820800c160300705003816038410301b10303074603008401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 967566043 1250 967564793 967564823
    0x50a360c030807060605092505040e0406051b09280b120a0f020708090103051801020706140703270305071a070212090a0e0604021e0a020105070c1e 65
    0x408034000045100b00b01450755181036141c06425562964000d51244142008214480189510842600702c6a00703940d040c8400b03c0a060360140100d800600700380c20083d04100030006036622240c0039800c4102c0d5503000c10b450315001c400303907c40c0d079903103a402c298100f1110460300314880c0412041e45c00310343c221100584600328154181c01c008513065000301d034003007445660002c910401c945000c9030881580b0b420015107406582d0320070b07044000e0400d5610300004404502001d1a2841c186081000755a10441820100068074186d02d03c11803000440c8041186280240f00300c0c8546000c50307170380c03001a6548042c1c182400e04081c106a0500c101004104000b60030204e143c040000d42d150402d09074149400000d03c2d00c4510509004600700030444042259100410b40040b64901400000c065a0706000300b4043e010320350035800c0310030a052907108101c040d180900301e00380c00b6038000c015540d5205d000711400038004402901c0c0c1d1005403800340c144420481120481400f030302d460600e00f4a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 967567293 1250 967566043 967566053
    0x40f12140c0c0f09151c02100f0e060406080403050a2010150e190f050a06180e0318030f06151c031403092a03010c09080606060901090803120a050a36 66
    0x92a00c0800c0c000b03001107607c0c0d01260b800102ca0410642b0542c1c1c0c60b414079040c0391000e81000005000a0103100c0d02086050546200b08103210316500344020112003121070310f2100340d1381e040c000c03103005110381081007083e070141442a90b801140d40042440600d078440303582111402c0c10745822000310903100d0800710714110150150600900d00620001a02d0f0300d004003401a8800c0e800700d017a1101c2c24042d158066080c0042501c85410080d464410000301241c00a86045044061030f030060013000e0400c4180703540341cbc00101230a001541c001c131110f0901400c04460162500f001800f0900c040100ca031480a01c230065940088050100e035940702e4201c0d507042195240a40b03582498001c50599845800d007805422a40300d0f00d808c1121a0300e0400071001d031112401080540034580c08940c000b06a0700c5841c40b0801030101d8000c3c1c4e561515280c3e94500c840f1021140340896a0501001c200300f40305a104002c107041d10b10f460400002e0514200c041c440311a4100d85520800300215072021030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 967568543 1250 967567293 967567309
    0x1e0e0a021215090a140a0b06010f0c020406141f09090f1103100501020c0105130b09010507231b03030d0b0a05120604120206040f12140c0c0f09151c02 66
    0x208044010070313113131041d4030b000d40809155041c090140d80101600e6000284040d101a070003c100f424628510420302c58120707460101410065845418450000f8980000c44007481034180c0648000600142c00c414001307441c501016440001008035074108000346207980303d1b440e4407540e07030300200d50300c4d85003076544500c2e8005441309200e030602240e0800580d0b03010041c0105910342800c1c640c2c00d0809004010a4180041c403550701007400c0001e01c0b50031684618112603407031768071849103911250000300030030090700d400044804500c149610b40c0b41c2819004100d400d0604002d0046160007001c958010113000d070304003056006070b44502e0218150391114468045950303950000e20345441c141c10840765030369190081e0380c01e6421020900002c14440c101c813070702642d0003240210194030008011201c401c8213589100240e40003007070500b90110081b424052641040b1079200420030a44208048110199800c98111814048581542c1440d2a11a01001c40306451405140c1d694001c12600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 967569793 1250 967568543 967568551
    0x20a020709060311010210151217071a010803070b01090c0c05030a0302090a140108010b07051005040812090f0c01030c090e13120f0e04090f02131e0e0a021215 70
    0x100d1104840e0310513a503410403500c00c032420131900501801c442110141109030803409012003508000310300c0c8042c40308090503030000517107203031035203550307103504e040c86214007002c1c103500490652088000200c0000000584520b5508503444020907440e00d6540c03002000142440d000b84100031801d01701140003400504110201d07900d01603901d800c95001c00117250131942180106a0070341c010030a4699000b940241510b01c410151596003a15042880c0f80400340d0101c00403081c01e1401308820070854101802c0410b001c900410010346800102545409010b0b0301c0c7c40083d4440303941d103d99503103e070f0480b0304034060300e00300b00d01c0050301ca0300c0d4941c600100303c840340340001e0349040382410000f030a100e10f00034076000d01c0c050b0904000428014480300d5401e072365900c00c2d902c448a440c113016801c0c1c2c68050266004203000c2083c4000e014030f00141c09070140c115030b569000c04080381d007056035018910301060304401038201b11074180e003081108030140420428904c1864844104a0000e040e0780d401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 967571043 1250 967569793 967569803
    0x9071701120201180312091a0a050319060909030f031803181d1e0c09091009020a0e120d02071503110a02010b030c01030b2103211e0106020a06020a0207090603 70
    0x1818100354000d0325080440d0300c20841070305281e9100d40c8910408c0c080d10902902c92a055603240c4540c040004013006005107110114902880000c0c602c10690260554500c03944411007c80290340064088489000d00099006840e400b000c000a20481c0ea0241d1101d050b404801520b8840b01c0e90380d1a02c0c081080d6020800c2d0000601c086030014011400c0e1a58031051000b00c1407820f41050300c0b0600804400d43c1c06101100003181c071600b071681248014100d1001c00319117400b06918001c00c065858010030707002e010400700d0003840c10703400304020482c00001d40003003004518083c01302c500407024200d1101015980c036145034450840c2c5c401000f03200700940c008580800f01402f0141807a4152040e1410300d03280c10707400101a04e541d990442c4a406a00003480c5003a00303080c070325040d80704030850b84d51b00d8000c0401903d082d00400610f00d004907284481408804003260142c00070441c28007620000d60b00c800c0c0c1c120005880b0f90000c1c05010030900c1a1100700c1e40d148941815200240c1040312 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 967572293 1250 967571043 967571063
    0x9140105120a0f170c150f10120f02090721150506030a0207020a0803120a1e0e120a1206050d1e03180f030b07080601050405040b01020c130b090717011202011803 71
    0x131b140c402d110405500a5411105950740341403004e2000d0400e130f050311507545e054034403052160034440343d91403040038150054020760b40c44ca4407032002020b0401c42c104000304c480a03010424001115486200790140303400c1c2100c801d0720709040c1080266000100806089074080000e08010f1722004030f800000c00fa030000450712041744004582c01c1c454010036401ca001d19041600c00c20f81005a007122581622445c00141c6c2e44840c840f071401d104208005a4850400290031030441754001650000ea40c00703560300f040038584890400682c00d5000300060b2182e8009510304c180c440041041e43c2907540b007400c003101d1410001c075030034044c0c112030340c004440741c101031380c040040c0903038a800d1542c040d0aa10700361400d45041000079081e4002d50003403500443c1e6071581d0a0040e4002c03c400100d00c10014184003035104007603010700242445c03000050140c0d0488006c2803015005140866110100b907400025580c20710076100203184403c40241e041042d103216041041044c0b203a0640a50301030f00401c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 967573543 1250 967572293 967572313
    0x2b06020702030d030905070b070f050607051e040e0408030603100f0b01080a200a030209131a01080c031f0b03040308090f37080409140105120a0f170c 66
    0x1500f8012440c0b883c4050500b003041410002d800407640c0000d80e00100200b946580c054240800400c2c000b4000a249129000a0002c030b150088060f2084c8411600c207005944003403a10140a8010b521030348034515000408680000c0100c4040d603403001c000750880d0206482c14201000b9038090b82e883c00d400a964540311806943d11040f10f0394841240581030048103000004249124640754010400d0000800c1c0d08a205200703804403010742e10024108a6040845840c0070018582c4a03980060040c129050a0480d401000320030f00c2000118141c60640c0c0d1480d40c1d04004204018501081c40703866000880c459000d0400b55001d207000c2c1d82c2e046043c3c90900d050f64071702560705603142c41d03503407240040c170f5990080f10000f81580500200c2c3d02c10744a01607200303031803040d902600040007031202140c04100340c4901d605c41e20035a408030386025440e0b40e80b80c00380450410002d40c405420b401111640d03003c2100e00040c0c80350716210b00c454018004085070840b0164110825030640e50b04517071810 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 967574793 1250 967573543 967573549
    0x1b040b13060518070e0405190c090503160b0304030311040902040e0a0b04050910090c050a0308030a0f02070312090c0b0f070201022b080c070602040f1e030201020601052b06020702 79
    0x1003882c4425507114051300340f0b40360281880d07100028440c440c6854100249545131440c501031100d0032100010f12800728400d0024101c00001c0c040c6a001348541c001710382d14080d98003050000c032028110316920310785840c3c41c11400380410030315071803140700708020000d190346541c030050000f803086e40c0304002942482c0c04103105075004040c840c4d109505050a0003110000030521004111512a002502c010a031800c19082802d0764011503015102110010600c210100190b01c0390523181130410030040644c4032034080340503c0c440030340090825880e00204240c0f942c002880c9a0243d07141a840594995a202c103503402440c0b240c042e00f80c046804011960100907411624140460a00f000c1904850300f0031241c0c00e9400300000c100e407090100701401c00c82c1c801c80d1040c03900584255512500c5182c00da10387c80c06880391903140380c1c5d0a5040d500621807d1042c9003a654164060404da0346020308105240c1c45401c810155901500741101d81c4122000030007005620491026031901494010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 967576043 1250 967574793 967574809
    0x30c0b10031214160c05030f010e0d02010c05031b09040e0f07060801230a090f09020f09070c03110102090d1401050c0331020603100e16021b040b130605 67
    0x221100703003d18071180340c00c00280341054941a00380da200c0722071000c0300781c1040390003d2903640c80a601406041c3c981c4030fa070001900709902102410b4126090314080f40403c0342206d4461800380d000803000d00201d080581d0385030041150403401d900e51420072034030200040c1241c001420300e8001c0d07804580d00310324203d01481403400030036050030401700c1980351405441c0b00d11009541c0c605a00d103030460126181d611090200d001c0e00c0001d0082058000b842c250304000d0020b1842640302e50841003402c4840d1409000303040c401c080320742d01d8482d201c040c2d41c1e090301c1480240361030142654090014918079150806c0004040d4020521403c58604400300142181d401400031300007002e0400c100041c80c40440d22601d6104007243d203500c00742c800481051681007440400950000000042c42080306201043c10b056520a00101c1d50307a4031040c04c0c5080c1d6028100030140540c002104889040311042c41c00c04040d10041c102042081e811800034100541303c0345c440440559450081c4030a00304044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 967577293 1250 967576043 967576073
    0x4171218251401050705150a0b1e0415080a150609150b03070306030c08010b011403130204180203060403020709201c1508070612050105010e010c030c0b1003 69
    0xd10a0441040380000740390500c068002c0040420480c1d420344a0341e4401c8044800d41900306d01641d284c503040302140342c808038080e01c030b4055250411465540300e141418006091113800c0740340f076881e890602d06110283c5440d001509004e80f44c640c0001d0035a0040c0858000039120300000c80c00c0d41074010260048500780d4005c035420503c1c014031158a001824088001c1d9840901c60310748075592220104d000d03003400e03000240b4070810355000003000d802c1500510200202600c80ca002c1850000c0c0303030003031400102e0341112880140c04180006d414180d02ca0032034085031030640700341e0005680120745000c10a48045005a01c20741c0c040061344054440c034004145200709488500110b0540c40d0340d0303800744e41500940f403030030350741d107403010041d640c0c000010000f0511400c1d08859036886903d403078103543e00c60100416860786500d51640494481d40741691816103440d1604144100115040c202c1e0300012000d106280c42c03800003041407000414414002c07410f8960301103096140152403580520 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 967578543 1250 967577293 967577323
    0xd050109060b0901050304052b02010b0d031b080712050a021506100f0e181005010504080618030c0109050105010612090506070e1305151203070b04171218 68
    0x102400314603041c4040383c1c4240403d02c0c085840352903030306081c0c0c14480d0440003903181c500d10801d02c000b206445a20120200c9007074000b04080d0080109008030200711101c0180014882203820b40c070440200c0c54111390600582031b460414800341d882083c01d8500f0018940410070205810101c0c50b4104858911949040c103481d101e401c05e80c010482d03282c000901407080c0442c0c94841d00000388a014541015000144090a0505042c4041b1500181a9000b00348040d52400109541d4041d604039003c03600d03020f004012035035032402c040d030101140c03001c040d44a00040124030341800090046200403405540001010f502d070020182040b00000300141919080ca41610080386010804681c40995418450310000755080002c88103800701080180107490320091114920440c01c8114041f1420f80d104189000507155190340c038007414000900061658000400244c2e000e038001540215094045007412442d141006d4260350440390014181d11000c07900c440a9402c0180d060801494 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 967579793 1250 967578543 967578551
    0x1302120f0a18120e010c0f0b100f0311100216080303090c0103090203030d0507053006120d0f0504090e030c0c0f0102070303110a050313091103060d111201050c0d050109 74
    0x381e86001d00301c10080081000d120380d01303203100070307990240305641c160650000081072401801d00d000c9030070b14401d0b205004110461000800c07407800312821203090f29040740b0540c000625500400440d004641c034117504500131807074400d58019011f030404000e051040c0c00385441c0c1c60f000038030034a04480c1e0500310741094101003030300c400750b100401101d40c664041180402c0c6542c85902c1550f16118040128850801c04001d44c025104100c200f006c54005280340208035803940000c028a260080821000c55000240070000b01d40c001c030741d81c07120769040b400e109040a41d07030f20740c05044030302d055854046604001580f4801941c103000041c00c215003100c48068400140d03000070358821160000505120b03000010034948072007045003801d81c5034040d04581d59404081e1702e600d600850361207413821032401e040d5641d011003c0641900d100d030101500441c00112030b5200e8544002507510f00c2c1e078210240350303007490380240c0038090644641c0c916105203580e15100e00f200c80c21900d050707114610003454 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 967581043 1250 967579793 967579841
    0x4060b0d0c05040b030a020a1709010e1908220f1d06011107091e02190215010303052a0f0102090f09040203100507200706120e0601051302120f0a 64
    0x5001c0c00e4035085010780e1b01c01600c0e42c940c00015160a40410303000000307034089000300082808150400d99034482540c1c00c1c0d91001e521000384510062141d1001010b480c0103010540080f0103845070404201c441119180d40d150b40d80901d000140f1558100001e2040c51028242c00e00d0040407425030420341c2864500c07200b1946107032580d00c500007805801d0020740c443c0c10545800040c002451340d20303031000004658401035840b035803440c100004179601c0507002d45c248003400e4820303080c0c0c0e040c1200c1c1c060711030078609191442c028815001d015028101781141411611400800b08148064860302d140010b170f441c0180000c010050802c08511840341013618108401601e02244000702c40c080607030086034544803000241d4080e0312050103000c4142000d40d0b2030000a40004026084803034544940740303035000b0580e0304000ea88a80c130740764285504c42001040700d8100106d1500c102503000038014100b0a581c3d038092030f0700100351602485039140c1414041c41c41000d01c111000f036030f150310ba1f01c7ca114070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 967582293 1250 967581043 967581059
    0x8280804150e07051f080c03090c0d0c15110106121a1503030a0203030109050c040303080402010e0a080304060206090d080934080a060c081302060c0c04060b0d0c0504 73
    0x5150078951011911003403200c184500c10890680034010003011005c524080801940741e80203184003210009000501080725a035202003102d0040030484c1c041d100d00e8145000388542042203410883d0b80c2e014484001502e01c1d42e01c0d00307000414a140e6540c40c140c1101c3c0c1c000c10b003590b40c26002001e41064079116100000e152620780c0701280c581d200360100940d204080ca080c0444103281094060100040c034203003042c0c0c044029070503500c900388104800d0726250190601070091b4000103021410440c00b00b07000d90f01490700044603101c0100915007451301d5a05542c1142c2199101380c01584c05901400060315041c003907a14010b41500d040c00b001d1400740b1001d50340c0da07031900c04180214258185000d0300d9140d005a000c0d01c1c0e80a0054050b800d5a501c00c8591b610306480c0141e885614084810041d18403c14881f4040c2285404007035050398207400308a02a8801c0d0002c01d103a2040b191100816280c074000c01000381000a280e0303803205800d462020559a144400c082000000c010501c0246 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 967583543 1250 967582293 967582313
    0xc0e01020d051e040b0a02152401030e0a0c270207120c030203090307120308060f0f011206050d1b09020906180d0b04060b0a0f051804050a08280804 65
    0x120301d00030f011501280b5141c40740540d10a9030800900f40000140603520503400103401d41e050700e4003250328507441d6281c05034411201d038120380f10200380703100110030b0b100c0e9072280d00085202d96491042d20904403075907a500c1c900407281d1f8007442c5108254005001000c01c2caa6890080301981d035019840c00314140d80d02040c0003440c494880c1441001c0550b00e045c903200f00240c805052002d422603d04944413102e0300c170700b1904c03901c00f280090f4044000072560308280d504004840c00c081d00c1c0c40348107404400103440044003070301d01d902c24036038032107000070155030b51000580024014980c200ba0f00c0c46241d00e0702c50214294000b101c40500402c22024561a07020403030784114562825085a0500c41001485480c0c042e000600b5060b07140042c082800307115801043d080f0700890715119510303a5900c040070003031100d00c1000d44c4080c0d03c1c0d00440707140341c90751703d02d0f0381c0144104c0540c0c41c0030301c41d542c0341c1c40d4030340090303441c9840f8a0a5644640f042446082d050100714510b0030401303428641035a072034100c5c2e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 967584793 1250 967583543 967583557
    0x3010b0316090e030f0c06180309240c03030a0605120d021506041e060504061502060a18020310020307080f0606090d050c130b0406050405012409030602030a0c0e01020d05 75
    0x22956911100e10a08400c4c0140c900030840c214401d035a4000c031080003691200c0584402a41c074050a990205100c8000222480c0c444090405c0707074078a080c55000e11320b5400c400707091810820200300750840c0d841c09100440c40340041440018050f400c2000b40000c11504001c5d1111580c00040c140900640004111400030120000c000d400e42d500340200300506242d40111688500308840b420800780142c000c14243c0b1016102081035641c0d4000a1007903100c11451500544c0100e40030920b8084240c1008503a0400003001c48100b03401035004c03e10305590308500060311035010043c400d11503400b48070241c0055100c40d069805040180c0010704610514294a03c0390584014070410040c0a02080240a4008001e141c0b9289450203000240000c0d04c2c241d80704900e0940007080514040c232a141c16500703404002c440d48250700302c00760390348045000b03d2000d00581010000000d0700c00d00013580308080044020851071800f100281c440e0000b00c00c07081c199000a19030f81c180707640c01000c2e0703108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 967586043 1250 967584793 967584809
    0xd060c03061e09150e0103060905011118030d050a0906051e04260c1f0e19092708180a03031106090703030f0e0a050a1706070311040504090516030b0603010b0316 71
    0x703900b0600e00b4500400080c0ca00d42121300cc041000c15015605020300203100e00140c05491550300c2d000ca0031102889580300e0740012800003002403184c1c0e8032600c0945201075100d051000c010464405c40107031600641d1066222205a0b5204c008a00340e09601900307510f483c1000303102d20070315072000404403116800520700012b14a421051660300c2902d03491210740002c0c250010b520001000b8600f03190b8140104c081c0e66092803016010f21800c3d4100c3c4c0d19402c07049101407100511550b031691f80e0790007090f04013080758071101c11001903512030032a40011131081d103c2581c0404406121342c14254018070400031900034000801c0403d40140c260300320307144145409400b1645600000b540b1000c40e0300490340195004c20081081840d00c003050b0a1640104200d880694a055044090f1100ca107480f0a000c0030500c0f0030011400c140d0845c1140c1c905c9402500e0f0360760f02c0ca001c25400304001e40d100f554105144000c0c0900343c1000e110307a040c0300350284c000c0e0118014400351740411358110711680e91 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 967587293 1250 967586043 967586051
    0x6180506040219200a020a120813180c05090f04020306131107030306080d020d030c091809150c20031210051504050d060c03061e09150e010306 63
    0x105a501caa048600c402e0200030344070200754800c0360060402c131134072010103034080c140c01c210045041c0018031840040d90051040880c82d0400e60541c41000d00080b0403100c00c18140b01002d500d40c04a5100009000c01da000800c5c0441c50b148a042944c0c407100390501440f10801544005031a00d500c0c4c024501e1060301c0c0503035039498803804203070700c1740c1222098100103140201c1c14800703006110040c5002c500917903042c410140c450f80d1007611818040583c40c0503a00855040e80f00900a4001c00d4001c50036060002141d940c442046034250354800640084958400304102009102051120481002e1200704406109600d010381a40f0b02800e003015003015203614518002010011100c0d808011a5410701c2401e08503c0807603140b801d805010701c02d01a942400b2145000c00c02550111200184003110110440d110031004110080020f01050340b14074021440c29803443c0740e03140400c28280300e09081e40c58551103004441d940303210040c8000c42440204803079001281500c1c19603801c41c800107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 967588543 1250 967587293 967587301
    0xc0606101d19210b0606030c0304030c080d0e0a030807030605060403140106080706080415050c0d05090109170d052413090209040b0a2004060e121002090310061805 72
    0x85407005900c124110072002e181007681d4402c0c40c443e0070b9075034411004034410362504402c00c62035002c100e80344080c0345001c2c0002000319214800a00e1001d0040c01c2840ca03085080380080c050350340801d05400507501c407500f00f03402c03d41c1c0700c3e42080c1c0c0801c031031504005c02801c0500003a9140300e503110203480e50a07500002d0702c008100f075001c00010400d41045400b010794840700a80145c108a6094801c00d0350040820310f416458080c0503c03420040d00d0306490001621100402440040c0c4214a10b41d80e820f214800594000288a200004c904410b500c0b40c10303010011040c0e44008180103030350501750000810100c4003009a2040399022650b1114000c400190791004001e01c80b406544001004140070510504400c0c1c107007d03000510051000d804071840c101c8400d600852107408841d070801007088298416020281680002840740e0b5001c041307200c4561a094440c0301034401ca40e0f0010340201517180810803034040000e9500f0034045940b50103400c0c1c8035180d584c4509c402458a4200103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 967589793 1250 967588543 967588579
    0x80708030a23092e0203130c080622141f2a08190204060f0318020a0902090105040e0a0c0f09030b0a0518190b0c2802030f0c0606101d 59
    0x4006000501c40854032480c1203200c00e20584100203048c0d4102162040100708490042100c038425040c2e02e200300400440084200001c1668041c02c1e16000031102c40340c0419030050010f00b10402000c0142d9a060b050341c41203004072035a8501d82480c0b005040d1499880035101862044581071604141042d50b0300c08000c000c56900c2c0503920405244000f0b00424426000020001c4242031075070100280d140d404040d000b00584460040c3d0b100d006460704000004842e00217001c00c400615105080541d070721003010150005407403040714180c0320122009100d42c010804c1408110526041d0303408c61031a1200e902c0280054001460603854400051070245034107d418140b0141508407940f910b103880c2610300607520060101c447c00d40e10008505072003400c0e0241c5285003499641e0b40003402c609406441c40c2c80c1d05811000a5010078840074090303d02c0318000d03154410800010300348901c0d2200402641d41c00060141c4c0a202008400b4180a0b01ca9070b18444203d0003a103060294804c0b41c556 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 967591043 1250 967589793 967589863
    0x3081914061c1205030717060105090415120305030a15180507031112090607140d0b19081c2a050a080c0106090506030309100c080708030a2309 63
    0x1003e011454100c0d2400302060740240158801d16095070345070fa40c5c1460402202c280981075a8990018100344603104140c649a480940507545001c0c224040c00c0e0382e80c4600c5028150a0000e9003c50000b00411412243c18000c03605000c2000310030745040e42c108800c840f411201c403244902103d0351140090001c90099000da02c00a40b1070361102d40710600046911444081264860782c94003ea00100c0d0480d4020540522120035090b6851308103030070600c0c0c0703074014a01c41c0f42d4075a100f01d1018241602a15001410010b421004050514400035003d20305050400312120b408200b400b0002282081e1148444868400c00510302212440725046c82441c0401485010705110400210303401da0420542c0f01000301c8500480501050765000101510380c0507031154145c11651412030b46040324442d45078071761900d100d000120708212450310f691303456802c11242d141f80590380b80d01300601584441038644108485402c40e0050380342c4030132429103603002650000c03444a58001150420621030314 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 967592293 1250 967591043 967591099
    0xe01170a051002181002030a05071112010603050d0801030b060f04141005121507080c0f07060902011229030c04051e133c0308191406 59
    0x108403003a407031007000800020b520652402c0d0804d44c0e01c5807801001c1c18250107a0b0300040f00364024500b801083c54090781c51760700c100700407a0800081901c0ca442e40e501e082c03c601200d0862800080c5043c2907140c51450095140703d01c2041c0b01201c00100006100c829440e07138012000c1d220008150002c00215000d01803900d010321a1030741c074004001d5070341c80e000e00c06d400b1590101c2d102d0130010441031005885001e0b602c800401d0380d20342400074007618000c91025400c60030480c01d03e490411007030740c2c1c100310f45c02004044079050788480c40001513607400b07804840f00d402e02c41d504100c1c40d00f02040000c0c0200c190000c051080344080d512102d6a5000e00007030b40000c602074028407a510709031581440f00e1802c0c8420108070500da00200c2d001e0304040251400080d8000c616215400300e5682c10b907001041e0050000703100c2600d0071f501409500301440358441e98406d807101e19150606000041c12500d00345403454500d841c000e101900700541c5007040c2d8101c2e00507246215406c1c0c59401c0f520f4551043c403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 967593543 1250 967592293 967592303
    0x180103020f03040b102108031b032a0306060a0e1507060e07120201050409113001080118080f040f03050a030806031507080a1b030b0f09010e01170a 65
    0x3100304020300402c2d8404d58444e0344801c42e1321a2040e00c1d0116152040c4040345a120300b0440d400d00303d000504090700454109081e15000c5001d00d60103203140c071055004a0b0340f80d5000c6482500244c26400b0050a010b5414007105c001d030a62400e5030104610b4000c1d40d040200704824903d010410707448821028046103c0601030542d965840d0900e9405841c40c4011750700103104a4000140d10071000a69088803071b4140c0d136561502d46002014400b5040f80c0161841083c010032510091b640c044032306001042c603582c00000500d16201c0c000d100404142d1008420340d0501c4000c01900800000c0000d074568004810f80d02c80100c5107203030310349000d00e070040101c03000806008400d020002a0b1400c03403d100b65a0b032030071503507103509060b212543c0d90b2910079070f050590085044a401490419440100f1450018001079402a14941c818520700d10b200820f039110031403500ca00309003c02003162441502d0009803545801c100810480b014030516940c00443c840401c1c10315000d00003400c85136040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 967594793 1250 967593543 967593547
    0x3010606050c1002090901030b1b0304061a19210c14031e0c06031f240203030412080603160306020d05010509060307090b01180f030501060e0c180103020f 68
    0x903031014065510075560060a40b103a83c103035411580d01402140c8a154000e403400c00c25910356079500c11640380103064684e50307041d2900720444502c0900090f5214902524000c21450080400488069054610385010b09100074041110146c00590403040724000e02940c22070641802400207400304411004120001d044d100190f00d8170080d071241c82800080741a110401649002c0301d00550140c0c1c6900d81c035030400e0a4403040ca28080000c1d550020060603c400880b401c0806c6580681c8a070300507440904803100740c0103007203d120700c42070070000d100e0004514504207a15004452b0490258540c1001028400035402da1024440c0181d044035805c80c0c0c3c000d40e512031412a019400814404240c2840c5c90000034803443c10780380240c05103c010f800b0703045050502e07040101921030200c001d03043c4a002d0f0b640080102e02140314400400e50296442411030a41c500242514460b82c05890645a00c4081c03000307c00200d01180d80c4c090820310184c002c01209001a8041c3c00340c140c0c125549040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 967596043 1250 967594793 967594799
    0x20a020108180a081b06091606030504030917010504050c040e1c0e12060906060105040621110403050a02090a09051f110d0914010507050a050c030c01060314070f03080306010815030106 81
    0x1003c2e21021710b5504001c0d10b0003541c420021135558514992440e50308505202d0421a0600170360146410034001e10f0010540d9484084601b480fa281481c0d80c90241e5585040205019041c00f00300c0724407c00f201c081c0259201d80e104550748000740e00c02d80802002e02e800404080c0e000780e4400781003081c00351030000103028982200da00c4400403280758020303005100c00141070790720540c2200c00740e5a860310b4851200400c8190001546001c502c1c40b036601d035030f54041c403072440c2807c405000114452002007115807580c0c41885130303030140a481e243c4c2c00d500b015040c2c00020800310303054442440d41c11009055211352a82d03030014000450004400721030000b00340b007091645400c030105450203800c0300b1010103028115142212001c40b0300400003141400560419440703240200303064041e620440b4180b5200d00d8070b8500b194911341c4121100400d003000100340f1001408000000c040710180a040e09155464101580c8402030005040091006c0000c8409102c04890b00312aa80640200032845e1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 967597293 1250 967596043 967596067
    0xd0b0705030103050d05040b04061d040f0905010b0f031203131e0506060907051909030203101e020f040e06061201180e06010b04050f03150a09060c020a020108180a08 73
    0x4400c3c041924540200080c41d40301a000c0e004440442d03421007111407500740b500c02d003103a14424a0b48191204405441c6486113940d45008420540c02843c20000d034140191030420308446480900b24085c585d107058070040c540d0003141c0c416090b10441c84459a070343d9811a4001105034212004000581d450701e142011701c4a207116005d014415412555141c9031942084860601103130700d040011010003103000885011808042c40c0a001d052848089449600203030511041c0e90150b02e403e581c1d400040d07011141007110900c1504007600071885c0c540c0c00c1c104000740344594041d110352900c40502080068940d8400c41c3c0d0602c1d007802180d0000e50311056050b49000024802181032400c22800c0c3d0130f510700105545048075070a840325032400380b41c031050044505890034010b40c1401910100d0368044580c03125544203030b590120010b0207004616021040301c000740c401c102198464114400181d80000015030403400500904660280200d1400e1a01d0740340345000f040c5444c0403a44001e062 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 967598543 1250 967597293 967597297
    0xf0f1b0e011d0402100c0f1b0f03030903110f0315060f010509010e0d0c150302070302011d03030a052a13091404031d0a031110020316110d0b0705 64
    0x4001101240207640e03500d041c078445601d500115032030122140d02003030040c507010301465030f50209403d1921400846403255065008120001c0d564a0354055020444c0443c41c209000540044020000400c1c11901c00612110036400000c00070000d045a0b03035440e90fa80f45100d2000c007001011514644009107000c131b4940300c00e035503840c01070710706908605075503024109848044070103954031140041840200170046000d44001e440300301c2c0400d4089100d10b042c0d0305284140030207441c050790b16034080c0b07802130854841c1c002460300b18101c620407044480010045a4211420400104103500e5580c01400da444000c01451000500e040300300300b03d031282201034254005200e41000c091b569403c288402d1341e110051a80c5044103020005002034040c203c00103000e04c60b00c9024a41001c403502003846094150802d68020200c10100501850720150769003889000d84040d41c107042c80501d0f51880100c0c0308030018541c03140091610195150300410b200c0300e98100c0c0440d01c1506020901a000b5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 967599793 1250 967598543 967598549
    0xa0e010801050f030d2a1406100303080c070c05060d0603020909030a05042c01061e230c03250b091b090703201c05060d0f0f1b 56
    0xc210200c000080d00d142c50350301c0790781d00382d4068040c0800006140c2c04462080040c201e5202c007000c840d000400c80035440c42c42089040c41205101a502d10ba48401494414010468494075440712400c1c00025446507010741c2112912459540302c004600d0b1046039000140c2210b50004c00100d104207400e5101c0c0c01c15000c41b40203450900490f20340c0d4044940360701c01c541e10800440c10410040010200740b0928000308044002c800c003890100461844e412031081e0f01444c00100800302d420b41c40743e48041c01c40314091b8075003000701189039821b40320380c0241c0d50364196940d075000105017014100c1c1c00380122103542d00c800c03808039002003040084548040b2040c805032084101c1c0700000e10a40320009840682c504104400f0002d0f44400042103440c03000140f1042c00c0680358891422800c05a0541214510240d101103894141c6200c82302101035440e109030090030704100134800c1d140c82d8032456102064001c1500c0d45040c140381031240325600000c00007804007c1c4d0b029044202c0c0c9408000b9000e03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 967601043 1250 967599793 967599797
    0x702041103160306150e0a0f06020d08160e010819020d02190c0b01030602070c030618020909010c090909140601030c0e073e10060e0c03090d050a12020a0e01 69
    0x9010311002044080f50b01c1c0340a50000040340074002c0c450365000301203660391b003880140100e00150302e850b03058520117040c0d0701c5940564801c0411040454200102580c0320403600810b0446a1b810380c4c00400006214044a06000c420004174090003404421024800d886080644d551031061509400075403106089040300c503c9000d0342c00b1a036102e2152202201c2c0c01c459002d0041e4250749894000350300610040382d02205003038002000407094015081a81c00d070741c2000e09454840c1c0144580c60000901500c03490345021035140660360040c80b02c0041c0c07140c00d540040d070003001d4601110a000c04404c1c0101c3c51103410000010807041c10b06d10020b60b030344034140880b1030700c4812042d6154162005901460303c4c00c1e000400340014207e4084000030740542c42d034030072080400c21071400d0040701c2102c01041600c62000784014841d090300b03550000010701d10540b4515040260581b102451010881000740001d07140354030922500c1c0940007034a0300740c0b003103684145003903000d08180c03000106240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 967602293 1250 967601043 967601071
    0x10e1c062c0601051207032a050a06050306180613050a060e10060201110306060f0702030a1712010b0c0a081b0312011d04030e010c17070506040c0b0a230702041103 72
    0x80e0103100486c0c0074084a41c816110455001d0114405100d0842100c000400da50340c1000011a5031760300700c0d410700400060321217581d00e0070300c50203002d1044200a04040624203a6050002e10785481c1290041000500000035080e241d24241501524180d840a02644540300034030068610314150001102c0b5a078000300003030480a410029203000c111107007a0302c5081400038a0400c0c00c18401403103d40e10080a80f0754040d08c65541050f841040c8a00001e0880082101c0c0c0e07000e4207905c1014090480455444d007041d400050081d541ca1001e00002e18140307012441400e100c8031501000504801c080035261644115110349025540900c940d0b007440f011800d501400005a80301940a160540e4920140c02d6038800107603101e402010089403070120051500540d0300c007000242a14030703c10006400300d801d240c00d00003807c030390f17580000641500030800c030040c0310703046000c0d40101803480b2000550460040b140d8200c0340204003019403c5820907100e0b001c00294440154800d4566038071a107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 967603543 1250 967602293 967602319
    0x601080907080c060c031e090406050303070203120906070f03080f0f07140f16060e0d0f091a0d0c080a0c1b080904090f05010506010e1c062c060105 65
    0x3554901d81889686001d400c41c1c0d16028450400707000134110030982000301c1c0e00c3c000d001c000106d01c041c50101001d64800700030070304c0003030782c079003030040e54010001200214101402900000d4840c0383c40c039002302d00250005210a480c0d2104810383d4940394000d54654a00e2110341000b0345041801c490342240014081c00181d02d50400c20134080c0944502c0d698110550302e030311500503103648402408200844140300107998452402c1901c1c030420b120300303c0419508034605c0107900d481d4000c0d00e200c060202d9140c051019070b40c443e904a04841d42c1540304d1015039140000c20881d44512201112094282450803032429006004a4011207002c101007203810040081258554071215407501e011116403896800703c1c01000c00b510100a0041c000111840aa45c60104051100104465994440082001541c4c0004285442e49019a480d9501042500802c030b400d2013180300c0100850359400040c000803c0804120f0404e02c4030504202241c0003940c034150361038200f403041c02e100350811982ca03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 967604793 1250 967603543 967603561
    0xa0c0e0d0305032d07030f0e010e0312070e2b0204020d1505060a051c110c1c0c080405060c01060e150f030f1c0509031501060201390309060212060108 66
    0x4000d001c4c840b6500001901c0b072007400c030060661702015002c03d5455900c0e807041c418007882401824801c44c001035643d401d40c01e40403803403043d00130882410300012828183c525140c450340704600c0c045000c803542d44203010060080080c810072002a400a101107105490b203d00e9912405886429030040a43c0ba951541000624811259030100150040c4800002d0480040d018114001c4d2800007103412650780200021031741003150700540d01da03c0850300410300340c1c12042d0510b15071000d181450640a05454201503841a482003031300030b11000620002c0c500d0290b100e103004e402030944140550a204000181e039001410700c05120351040c61640c241c07440e0026402e1119018403010304045c44080c00e07068a10f0110251020030701208200700c01701c659003800045498442091501c40c40d5050110007400c480340420304e0818100c05101c9a1810401494102e05001c000d552884c150580040104c0c090302500d07100130201800440c1041c0c204040003c00e46c4a50001c0e82d50360419034869140c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 967606043 1250 967604793 967604851
    0x220b0901021608070b1c020a0314010602070e04170d0e070f0b1303060c093b0403081909020301060329010b040b0a0507020904050105010f08150a0c0e0d030503 70
    0xd1041c81354080c0000708039003000303c806040071070005240940419202d4881900380c1c0c0c003041241c40001d41d981d4509620004d2903041c039014025a10041c40001d0034503049020f4110042d2010340303040500c0007100300015022017101c485041014042c00080021920a50b96071954000c10107003400001000c00c042c0343d16030654108942070840728000610303580302d14009054031820b5904010082001065045844005c100c422582c0b943c56100036010300508000007080c100700c034240e80448014040070030751085225403c2001d071140403c3c070589994249008103260f00e0300a41650134210000300b485003204c129959800206440000c11600c102d800240b008240078412a42c24180030a004040a080c00b8000780c0c9554285245080381ca030b000074114030800c4074129a260f4480d03006000c80300385091544000c2000030300400d98006003848184102a00a040025003550fa06a4009591003109103a40c0104042c1407802501e20701d0038000c040b0307070007120801c402104d54150210b041c01e061071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 967607293 1250 967606043 967606049
    0xc08010f0c051e07020607030905040b0108090a02012007090509070e01080703120c020405040f0215030606040e1902070812220303020702012d1404120206220b09010216 74
    0x42c0360342c6000c054078110300c1102424080c0c1d0320500b02c140700840051300c03508006c00080e4003e882d54001d0030703e01002c100950b02c40d001c40e24104800301040c0140c038540050900c82d25542424100c02c500c2581c207923540740c031410607038070f6691b8403c407000001d0400c1a9807000c0d01645840e0706a601007900d030420445030350802c0c451004240e000e05400c10125442810810f401000d5184c5040f1401e015000142902d0701624259515003110004c142145800c0511181d0340b642030680509600e460740c0043d0300c07805203109580780987d00d20005190403100803c45903528284850031512000d450402030b0082e000446220300b11124500460190401103e8030011451601c110140b80103450340c1c00c501075045001c040741800342d482800c4407600c407000120b08880461948902aa20981038000c0249500b480800c030105e40802052081d0403071070b03d044401940544655681e10084005404440703056015042d071aa40508040340c40022000104a449403d030300b21054820070b4515107120400902c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 967608543 1250 967607293 967607297
    0x1a010219020f01051e180f0a060503130203010b0d06060510020c220e070611010c140a0e1206070c021008090d110a060207050c04051e01060e0d050a0c08010f0c 70
    0xe800c10750b2a40c030a0000b80b50034071000d09262040c580e800d41c1ea011036005905000c2c000b541d40d040065083c2461031284074100310071101421140e1808901404911004d0407080c0700e004240500c50554600350444881010050019480b04c041c42c00d0240c000d20850241c18802e6405001901c02ea0b40b0024043c2036440d80144108107407501c0e240c510418800390316080300907644404222482032010300400c802840d0940b030310007503001e0390400382d421a10050302a10510104441c5001040012020386a200506080c203101345102c800004003861105d44070750301c0f03034482d540401071880d80c028012040300b442038856001c1000000300540d0b02e03110440c0e50141e691b00505150290b18401c1c00b0895600841300c0540f088146a51250022b9a02c90141a502e541c0442900c0000382032620803590312803101300c0301405111902486407540b85040c81200b007040000009200380b9031b6100c8400c6c0405030300200315407880e8160b2038408101102413255240c59480e00c1e07440c4809940c68010021500301316 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 967609793 1250 967608543 967608559
    0x50903030f0a05060f21060604090f02062a01090c09050c1602060405030a03080118060303120203040614040b0a0c020d02070509040c0f062c0d080304060902041a01021902 75
    0xd10007600207203c01001c0300e910001d615001c4081c2e8450711039000301d60014079240000031a00c0001e103450194007400c0a8001e52501000c0c40200d540050391100456049800d940c2d10b080c48000d00c0e5064030500709034100c00644c03004008400348154002c03e0014420060a0030403507403881101f0460b40102c80540000301c0070000611545244001c1e0000503100501031401d02da250301c007017454440310120031400300d15044018800305051a020600040c400c071410b001d95030a5030b0f801082c01605103801c980284c0c022000c06c0410956800c414407010102040c07241515082c10041d0800c3d0741a60100c0e0300300d01d04400c0e000094808640000241d00c29001052810b151009000040c18002c7c070658403d03040000102c0c1c21400c00080d200101000d681700841d42040a4200038401800078214000060544810000d502c030040c0b46880e968100302825100c0c2e80c4c504016014202c41c5c200254000d2070300884c11003100e0510041c0a0320502a42114a00b2041c0708038a51403441707050001c6c0d4000f8503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 967611043 1250 967609793 967609801
    0xf0d020c0d0605060a0312110c03160b03070201180606140103061a0c010e03030f0103120f09090c0507050f0d170f13050304091b1719020a091e050301050903030f 71
    0x5030f4018035000341024100441aa80d070703880b01e50103101440c2e10540003410440200440e00400c026104040c0d00031001740c072006900c031b01c0d8408003056074840d5462801c401302c0003d00050003984044812401413028204c00740941c40c000d001400d8500480d18003500d01c01e42003000b0351092241400761641d0f4901d21209040396400c0d0301b12030300407003001c01841d92034402d0320007006c85c140003860144200e01146030f215411403030300c1010314802110070030070496070040c2190290f5102040c9002c503111100002148200a10212098411181c01030318070300c40c0003650f003555034000130f265454152a542c2d041c40c0080c508007900c10503030b0640306000d01c071400c05e0100300710094084283e001c241c41030044901d01551080a00300f600c2ca1020309414481d6079500c0c1c00c4030550041b80c54245801d1a0b44510294604441450f1180004402400e03010b94081802c4d10004d025040000190810011820941041984106500700c040c00342074043d50030a804544400c900005485c004c94114003440410b0b56 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 967612293 1250 967611043 967611053
    0x30315091f030b010f0b0a17070e030f07090507110a080313050f03030105041d1c0504180f11040602060708091f09050615030a020424080f0d020c0d 65
    0x1030162540c0000508075106500d4610a20a8400103520903008024290f16040305207141c030b00e40fa0b01080304008100403520f0040c3d801441c155681c50408004410b13501c440b0000c1b90926400c0102d941c1512941c2a00e01a068000440400301c8030300324414020f036950f02104130340a01c1032212000315a0311002c0c40070000382c4000065540300c001c003040003240820b66282d0a2615001041901080c0c00c0040140250306090081452004441a010b4031030300c02c8940050b41c0380b00361641117211103601c9110b000260f1040d8215402000100c508010382c50039050190000d05000380e50a00c01882c11150b50708014100e02950116111500580b050341e4804a09440f107850003041c8200b540251140c1c0b040008445c620a2005100030700009130605c03952400e149004400f0f4078240300c006800300700410036070300040c26402142e41514007003001000c60562941000740c40b420551448030718240030980f204001040175440c5800030403a0b08440940c02c1c00da848a1002c01402d404c0801e002210012031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 967613543 1250 967612293 967612309
    0x61509090b2701031218030308060d0b15120f0d0807020f01020301230409020a140301021303051516050409180b040819140909060a0b03190e030315 65
    0x5030103406048140441c008018442035112180c40d1002d98460042c0180b11030b808080e8521074807401c02d0301e1110808030a501840c101440010100800880060400d440701810904078650001800e103150400c280070035107103400c04068a00405010321001c08505001940b10810503900f40940486d00d01404115292000100171380250310510005031b8041101344019802030502a0f61441000c801500c1400e40c0b9481e909202c0c071480c149100080560b0b0342100003400c5031415901c21114241000c04240a8002c104c2e5000009006e01e4000052003400b00d85884505035610200026603900c808400548140b1902600043c20a200a0042c01c0044d031103202403100c11181d110784507003d41e0b10420078100441e0125801800400d00d00c001c1810554a07138040005400d282801c9400482450a03900542110300d2083c25101d002c00c4068450f184044058412600f10f01c1d541d1500c7d8185103030000c2c070f294505030110324040d00c4801940c00070040d41e001303800c2c0c06a1004170802c1c141c00c20400e1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 967614793 1250 967613543 967613561
    0xf0a0303030c091205030d060504150b18060c0604170a0c0312060e070903020f010507021c140a0305120f0412110c220614011403090304050409051006150909 69
    0x200145900c0410b140c3c1d040141c40004612900045031f440005003940d1058502650003d07010314100078003060503a1003003c250041c1c6215601c11507c0d0b002071441c4440c91164500701c40d070000d500003080228030b100070400d80d118901560070301c2040d4000c030095901901c16010420009085000c50500013840f0f11845500c00342000000700344e094440f0200200482c080d01c40e1004030f0759401c0304104500f04040041c0540c0801d0903e10704090301ca0700440d1002c251210302d5800407044c0f140d02e00030840481d2424a625205204590360800c961070041d0950340180348440c42c034090b03a00000d081800c10b03807a00c0d101d29884280100d03842c10148042da10070110000044c0a401203144004083e104c000d68541e85038034a0000f803400c05007482c0724400311103290b085171691a02c0340700b0301c00d016608421100e00e4030850321a4540c1d0b1350350301c055640c01d500403500025406406c03c44a6014000005040d001e401c00c604010466196996000a030300c1c40d44c1e09100000c180800c8042000ca0080d80c8190302d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 967616043 1250 967614793 967614797
    0xa18061d22080c0a020909160e06040e011803030f060506091e09090a03080108060114060f070b0c04090b030106061e17011214030f040314190602030106030b0f0a0303030c 75
    0x581c41c50741e50004541c20440704405264440700300c410662a014102030b030454000d2014100320b91000700380c0b2200108900452420860701c8010400c3d5803507036842143c040c10f544000300710103089510002610641440c0c00d43c006800c24147c5000303981c80344540403c8440050a051501d016941401010309120380101d2800c070703272041c10140548409107007070300c2a400e070070107000750700500e18003e0070001042e080040c4036030203000184105281d80808074040682191120707202c81000103058024480c0d00b00080c1201c010809100040c440b010140096886c41c6009120308001c0c40e05140c06c0b0340ae0b030710440b400a485428140c1c5004400380c0140852401071821000c1d01565903c001880741e800c0e40640d4503d140900c489060140c6110784619281841010794a05001c80300e50034a02d000f640000340000381801409884050304019030f807040e04010514142d90301190174010025002445100702090400d2600226841d0108812440031b60041c0904005030454404400800480d013440b81 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 967617293 1250 967616043 967616101
    0xe15010b181e040e011d03160231090201110319110c0406080f060907030b360d0f03090803010308030907030209090708010606050403030f0e030c0a18061d 68
    0x60342c6030360052113003518a00d400840c1c03151340d501c2e0780b800045040c00302031082d410620039000b110408106841d252901225a070251905890320f10040c3c094251442e054050000d01c0b9186038422500660401c1d0b0013600d4138a0358035074081082d510380c0701e6105420703100d0810b481d102c0d404500801c102c00b400b000c0101120214180c0b20081801c8030b0305038100380401c0e80111844044140304000203540a00a080500036051a56032549002d0f83c02400704c1503d010b07905080c2c209000c02d400e50b0540c503c15100c1401d14022000d2007039842d000c02c042c60f2000200703000081c0101c1d9004c1d004444005c3c4d0b00c2904240303181c4c60742e26200c07081d41002c0c0c10b090b0140200f10002002d40d85580744070f8007441c1c01102a008891074146900d085455580c800000d12000f40010404030781c210703841c01d04003409801d10f0b0a04c503c2520000342442281003005510501c1944045080b40f8156802c0c200300c0300d128010000b02e0780f03c41243c107900768002040e640d20058040007800410612034129540b40c0c10000d814 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 967618543 1250 967617293 967617349
    0x1701080c1e0d030305010e0a02070b0a020c012a02060703060f0b0d0e07030c080106050f210a150e010b030307050a140309060f09010e102c040e15010b18 67
    0x4100d8a009a819030000b0749405c014013100e01e22118240c1c20a502c07030300461800e01c141d650380f407844100415840c0100d82c00f08030b940b6007081c2034200f411101003a10707a200d03501d074100c01c42c110307102d030500b240b00e005109180004101502a200f403c003503510185550300ba0030f00d06250b24149a0162511100b0192200b840e1024001c08000d8000510b100e1040f140c5071a05250a0700d0850303445078400b51040c00c8140c09540c01d0345510149400661072120710b1021900d40d150710510b03051400d00001c05007011950030214185255024104440c2081d000b07112100c08541010b43c0da003e400d601800540240c0764003000205440b0b0303030710036650641081ea170411340c501c03001800641020500090700800012940352660384220800f00d03400c000c462104143c4030f0310f103004104c03141c2040100b02d00f04084d24982d460411240b400608040b00800902c180b48909205036124240e000441c060414640e0003c6146d2640c1c9095400311100200f025034004500740c20824103400d5480f8440c3c01845001c100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 967619793 1250 967618543 967618549
    0x3020d38061902030309100507050714191506090905151b030a02180607031215080f0a03300f020409022701050906072306161701080c1e 60
    0x41e072a9181c2c80c0c000c2e41c4c0302d103041e204446c100b031103c00c00c55070501d01e04820050141c1e000420390300c2031a0428080d00c500c1e581b81c01c0980c60300c911003141103201f01c0002199802c1001c0e41c2100103804444090901400765203100e0130f01a2411000c0c02000c030340000e49113002b0701c03081c00480d07035001c0c000c0c0d1914584074041105030900d035402030710b242c5600c03600003071402d10764000c9001903d440303c2c3c03d40e42d42d8034125854800402403100c001c00810780eaa100c07690b0061070b418807010303280900700c00d100342c1e0000042d20b000542d0381c0501140403030120310b6868501139021040b84510b4020010007250f00c0c902603611083c2d000509091185841d120f40c28040400c50324400d202800114051403c0405940025254100d510080f00c2516040000401451500f5220841641c503141e81c0015001c802c0c40d84d24000b4182140186055262841781d00304200294407514001100040705444400e00482da6120350404807400b4041c01c2c0150b44019041165030404c82c00701c0250400e100ea945640100302400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 967621043 1250 967619793 967619827
    0x20102090904081e0f0d09050c13090203010b0406030b0f131208070809010c0906080a06090504051e0c060306010e22060608011203080601270603020d3806 68
    0x401c0e20756480218101081d000740034100706214029600704c42c00c0501c04415090a84191829559641d880718080010001d04108100c1168401002a2500314207902c05030001c28a05100384d21940c01e00c039581c0b400d400c2500c0f4503401d490704200c1902d05695490300307648116001a00d410b05500c19000324801103a48110003000401a5903928455401c081c100180444800782000c08143d2500d40381c40d000a801802c000215406800c090710907075280c180d880d00400d0340b940321610f421700303007000c0208001c804209111843c40c0088032024030a130b840320f8903603600f690348503180c0c01031000c0001c5031496004880c00015058000c2007450400300200428071076060400c2d0003001607850350414080f05400460807409484d40501d210000401c03618000c24035400a000302e0705000c5446086c080b0005094481c0341d40c4400100c11880a9564030030040003907004240b144402c0d49405068031500f55006400310002986c0900500702031000c20074600c0b8a40c220900030361000e010440c0c40350b244101c00e6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 967622293 1250 967621043 967621051
    0x20603070c1b06050a1d030309040c0201020405040c1e02011406040209060c0d030b010306240302090a0f0f050108060402090f060a02100f0b01020c120304092715060b0c0606040504030201020909 85
    0x504c407a00c451400c10003801081e00a4407141d00c21121440c0301c00961400802e40300300140440e4049a0072403086400d9009208503001241c02500341800000f100b030b040b0100d071051040b086048800c5413580241203003200c103071404540354084444d01080513442d1607006480e4a090081256180015440c14907143c0f000801e01140402d85424550509680620841000b4000002200e01e036000007048110314400e0301d980181415404951400320340c450094410140c90750b8507000300722988440010710451050f100700c500096001c80050710a050a0007920b051710405081d001a590013801007058a8201c952120214480d51060303440c2074410f401458041c500e00800041c0c410a100002410020154403050054130840c45888802100008481c210b0301390381e00c00907400e01002030300c500c20074001c081e83c05810300d06801c080c14001b41d1880f084080d07018100406c05550303035040120083c0240042040685c003c40000b9206040030f4000e141d200e80319200041c07500c500c0300005940c11074195 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 967623543 1250 967622293 967622297
    0x703030216030e101115040c0305062a041202010f120906050411040b0916050403080d0c09050109150311040b0a050309010f05130809011202190e0409020603070c1b06 73
    0x1101041d51404c101a005101e0100b92500b00e000c2214200840e940c0c0f20155810341940b10380d480050180000206101c0c007030740d4800191146402d0144c01c0f80c00d03982d80e01c5100c19404100501010b0780f044c400301181c08541c40540e000300400c505400558030b9404100898082c0000107454158a07801446030300c07207a92080d80c0004507802d01c1d040120300c900c002c0c00000c0c00742c1c1c80c25028600c0f0369605040541e0200a00c0741d200c5140b941010115214000c40d4070050a40401080c80070b40c1e060b184d081001a2540e0707941e105185075841004603100304051181d0903403140b402502062140c820380080b01da2031702041b04136140554034801d2203c194070824150f03001038000700c280182070f1801e01900490091602042c00f007802e05082d002ca0b240c0540c80d009049050020b610341c09a4002c1d0360304500261458021529400900070b083d40310202003001000041e444000e00030719103014407680500c1500600700e1419952800d034269944c800545c429a200620f070700901c1d44012610520101030f05c1d8a03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 967624793 1250 967623543 967623557
    0x60801050c0c010e030a0e06030a0e010923060c041e0f0b0c101a0d031106070305150d0503032e06020304030c120b0a05130c1d1008060408070303021603 67
    0x303111060f0841c1d0b900c450304031079900200281c2d00302d590711461a11b81d48000b107810560300c0c2c0714036003124010003050038a0282c65007061102c805101849009040031401c2103d4150400702e102041c90301c0b04230844003841002028841032025109410b450201c20101c000c12040680d240d0302040344c080b03241e500000301c404000410b40ea94640a200c0c08202009000092051801507541e59011280ea42120b90107008080082c1c030a240c4076011031b000d6082402c082e1101070a04003c02005804100da040c0141c403000018860a810314980c0e000c170700c1e0b4100024604580725404c01600c0b0000e4400d01a011040000305203200d94140f00c080750090080d0703001141d0710381c95490907e040170307450303444048582203203460391000c62800d400385a07104081c500001001d80c0c0c0c1004121004290301703c00303800b189120a001c101035041020310745500c1c1110f02000a01d54680d40c0103102c04415005188050304242c000c5400101103a0181070450b110781400341c1012442d810400b08120f0300c0c441900000e01c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 967625899 1106 967624793 967624807
    0x60f020702091905161d030a05060a0203100b040803180109080106030f02130b01020d05090d0803090d032a0c11030319081f090c03060801050c 63
    0x40100191a01e041201d04101c10807092543c0b240309900c1c2901041046a0200d00088a04003558407180a9080c3c414014000621558029090303c180013503180011000e0010904c200e20403480140c591414451004800c80d441d80400080078041009000b415004012201074001e6640441020881500102c403804184d03401a40709501c0d0280110030070002442c083c502600072145422070304805401d800454034841d20389405030317000086140110780620701800102c04018010a00c001c0320b070700d40c40c68a074011114010b46402c0302e41203402d07050705441203000c1d5242d801038a98000c01c0c0020500721300000d914050081c0f1020196403010400c1e040002c42e50201c0c0541501c0d21800e4008558a05e11410390003c404110b107040001d8046091a5050103008003030101814030a01c0c0c07400304001454256404c900309515040003040d00c440034002d10340036440310b803191075031040 = true := by decide +kernel

theorem cover : BRFrame.Cov 967446043 967625899 := by
  have h0 := BRFrame.cov_init 967446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 967446043 ≤ n) (h2 : n < 967625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
