-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5398
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:44:04.79998+00:00
-- url     : https://prove2.me/submissions/fd76148a-a7ff-44a4-9557-7ab6bbd01239

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 970683453 ≤ n < 970863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 970684703 1250 970683453 970683503
    0x304030804060309060c080f01053105070e12030d0f0e161a0403021804050102090a4e020f1005090405060d3c140c01030606050d0216 59
    0x1d00c64101048109006d403410381d4450019903082d494500100e0050007281000780503418181c5042032002000c0810082190701c003d620003140c0201615503061203020741c1c010a02191314942125480d072181c1d4124941c941da8001c9504111070292540f02c001044902580a10b4140da25102900c0d840601107110400c1500c0790321581201900149244029520071010f40307041d290300a03c403080340140707401d09204400e00900305540c59542003020741c00640c2e80900c203500420303002e4201c04095074109076040c042126851407000c02424144003501d00c1c10140d0310005030649241c2c1c01c0d90040b00320300100d07051101c1c04090f10f400142090040020907004405040030304801c075810b00081c0c1e501c409100140c41d00380c100a0410282116004075070452450100d440e03040c01e0a032056901c440c000004040e1a11b89055400c2d011104c125004040207002d00310a909081c20280310b018509007008009101c0d5840586201d90701144040141c01c8a86043c046070b0340252a111b01c0780007138480b1201071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 970685953 1250 970684703 970684721
    0x5090f07090b01020c010c14030a110d030c2109060608070323070b0c0111030a050405011508210d0e030909131a0903163801140303040308040603 64
    0x20310a030100020810340c40d00400036902d0040e4050103040a6a02c01520040c5c080001120307a4505181d4181c098002000904290300c5540c2c0c50f02180c641400005040c05150390296080608085004556680190f400030307a40c501e501d00443c980c8060440354000385840d60000741120308081c400210310000107040c40079203020b100c03480840c001d940c0d0300701840842d0f03041c4211a9000313036100f0850a96180080c100e952170348000420101001e00051400e517104440c03400036035a031101800706110b02440348282e851958102c40e0070340c504002500750f503801341498549143c0c1c0032100014201000c0002d481641e050b9a00034450390035002c40c113a860790064040d082c040c3c0300788000120014040400300f480701cad8000d0048a1444411819480600741c01026203216200070090021030180725290360100c203005100f28a10010f040703100d500c0381c445212540d4141d050880b031212042101002c03550441d242648042d6482041101203821400340e64405041d501000c1800203c4c0d6406420426030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 970687203 1250 970685953 970685983
    0x926100c08090d0908070501210e0d0306230f0409051606022a062113050d0c080d0513050a05010204060201110c0a030c020a09020403060209030f0609060f06130509 72
    0x402c82641c1203a01a62512845c1c802d58006c81c0104550b500030300303850110b90141500382269000412100d016540382098004959000440c6001c105a15100d000054001d491fa06250010f201e1190104d070740d1790f40d802920401261011003000e5859a00540070558044181c1d100090050100221103240b4860030015004249280c007021903440081a050b0000c078040180740e281c3c11003440aa03400407290001d0a80c0010b51f4000c0f485180b45a0078070445803030164000301c0c0d006280640c04d201644e0790b4101403050006000300024188400d480d5210100440014241da500400c4203086404001c09040f81c003030f00c0b4815051003c10740080094480e51b40003840300301200c8100382414440e80d580c80c0f04a800510b0401c000070b204040c580300150008200c041d0340354854600c4000c0742c0c0302c1c0c0d10441e034055000420754403500301800611041c56580010700f00b0303440c00301c5995480300b400a0039080001c1c0b03042c0c0041c40c259100d941030b90144201007001c0103146007070160070303070b44010122604c55 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 970688453 1250 970687203 970687213
    0x10903051e0a080403080901020f030f07020c091005151e120f150628020a020108090607080c0a120929070504090e0a0f0605070f0926100c0809 63
    0xc40e051a0750495880c2c003003a50300c0344056682d07518229001c1002034440300c00c0d55003c202c00d081d840c00440245000d04030040c13045129041c092006031501302000d810502500c06502000b60380b914030281001212000d850041c1055012a5954943d20603010051107040c42070030003603914503000c1d0142c48456403005002c80c842e103901c41c2c403100441c4200e9031045040740180700394266084c02c4000d41f45480b510100507240d006400182c05009280c41d01010050f440340c0051410356a0292582d0740003005c0a015000500f40307084010071490009203903041c00040000c10810451140c0040d60a03249916420808400c0300e00c1d041000d0080e509401c59900c2c91038290001003c0f9003d000360041c00561102d91402e841d1802c0303c130180508188055840c01010361101c08203451807900d0541e10302c40c1500086914207441c0207480711400201c902e04000340c0740c0041c85804004401155000030b400c00000f0459052691341e8a8866804608250142400e0201d181c140d048148240113403404415a1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 970689703 1250 970688453 970688497
    0x902090912030114010e12030a0906080603060a020f04082424040506030a050f06220c060e0d0812090c0303090a052407030f02010f0b0603161101090305 67
    0x141d0784841d591842001c00504100411424428501c41c80304001e0604010101150281c0010322940d00c41703c2c2c0301f0715a000041c20100469020840501815090034030941901700300c4046179580e13070000c1241007a180c0c00118a40e02d11000c80980d001040d014044528007145840982e2194010040f007008030391a440104104108458204a0207040c035041209070100c14030406c4003402000c0e04258060048518070320100d00305000203c1c0c80041c80c0010b10b643d040c460461149104204060f14140c04264945800103003804a405c00b160006d1420003078441326a000074040c519645001482e410300040c0e110400302070f07850361621900c40341041e078404041820a058070380c4100c107800c1d503011118001c10311051078620040b040004200107402d007500e80500f0a0700207a03000b044250042000c208008403440d509000368400f400d4060803d1140160305004660716000c0078000300e070759049139001e011882d071007840b4024030700309014003e205050769400c0260440d800102008406007160b00f240b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 970690953 1250 970689703 970689721
    0x302151903060501121b081810020c0c09191515020a02040606050a0c150912051b071505030601140a03061d0c0307080414071517010e2710090209 64
    0x18500c402101b820f1291080008a0803030f00002c00803d100c40040b160030465503190300400403070118141e80324005a0b0381108000992800608411291191800c032007000344410078004032203194407440a0100310045484070f01d01e44005150001066100c1074188107028603070001d050781c40e02b402510100b16090700c4000455181c8180c900c000b0106552082d030400155181030301c201003280c4104d000814203441d545100d68103451501500c00514041400d03044140f0020b0440000c18040e0010302000345441c400c003440005c50403900d014044044001203041e400307200c0c5510602c0c030800c070313566640c038070244c002d40104030718080d030031400d001002d2011503c1c14100c1c449005240d9000030314110b030340b001011038200000400458031002c445401180c07085040268501501801c10010643c50803400010103000c000e1030180d040c8507032500100039041c011203d80ba0040c541010410340025003000001c5500d104d1603592200b407045140354110800140c1c030070340301940f007180e03d48000d448030007403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 970692203 1250 970690953 970690961
    0xe010f02060c180102030c10020c070906080618010914070906060302070507051909020315040f1506080c040509010f05030d2613081204060b06070c030215190306050112 74
    0x7a129442c0007000507103c0181c092070110160707181441141e21b000324401c2d05e2400c2c51007541c9100d6041c1c4e0003040c600c1031000705015101c00307000c0d800020040586492174690b030790800a4510f9a50310040d064081d1a0308084d00114403ca80011114004000c11b205039039854203180b241c9014903213481804210b00307110340219400716411000a1884506004c20061070044000044401501c0075600203844a403d001a5100d0300031070030000480181d102c248421380780c400c44c4010780e45180c070841140c0c0d00e12201e2404107a03220381c43c001c95113a03140c0c2c0c50341203144100e81109501214420001641b8280c10b580081610001d0342640c0c914040b4400540308076a00c481d411034003000042009210321011904130781c3c480c0078010000c2913560643c80302011640800f00894000050504000138840709008141c560342c0151900c5140400715240c4071000d02c9a400002c0c403408008111000404aa50a81d0307080000088050484080640090000c00161180d41d0100b010382d0545520448a885 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 970693453 1250 970692203 970692211
    0xf05040b060306070f090b030916030f15020a050315060c100b0406061809020a03090204020c16050603160302030603250e061912020111060907210309030308070c02100e010f0206 78
    0x4920300d1352410f003211f401140c1c0005145500c588101100402c1062102c0c4840000354051240d0f609a0f07100e500313004800800028429885a0040141a062641c440110787c1c2c0886046a4040c1c0701d0307401c400140c00751080d100040120700c181c1c94004070000040d40b00300240c24044a003007001c150380e1402964520200d1105c03d0110302090b0082160000c41c0d00100607140d210700d400958803410343d0005080380c1000c2c050150b1070f88110b0103403a818511242c41c80240c001103424034114942415021102da150405160402d50040b003c6521501d0801480c41051204480142d8100c01e2444820480d00e0303038030404004007000004654142022829100c900a10f070b10114101c505141c0d800b0b40041941e00c007241040030f8001c108120b0b076810302015000303002e240003401070b2501e0444400c58003800300c1c4013403d0000000c1110000a0340100002040300e81c5404c250381d01da500c030442a109644c6101029400500040c480030410f60310907110503960380262144040c407507620000700c1c0c0d41c001c01c035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 970694703 1250 970693453 970693457
    0xf0e013e0c0a0501051207020f0a08030f060301151205070f15020d0c020d141f05090d021504060b0a0909050303180c090601050d02041a030a0605010503070503011202040f05040b060306070f 83
    0x4034130300060f06c52925a0780420680101c85100c0c580200041c903094048109079924035000c42032120120054142d642c00c09411030080c05020030301402c0d21a8400d96201d03034549000d509241000b0484c3c1400081d00804c0007445059100c0e90310754018241c940c040e1451401406100c00080701c0c80c0c090382d6040741c070315005030551152580302d5540305444441041003174060f1090307040505481c4911525100114031000300410503042c81203a061809034100903480564100c0300644106100740758080c0e45c40b0344c000c100400c0c80d403910404103c9422040c1c02c403003041030030306040d0b5061190010046010f48014824001001c1700e01e05d0341c64031114007010344c41d805800140403950661061000c0c1501481100006241035a40e01d00401184000007070141c11103008020012803142e02e05c610001054282862403551901e11030013041807005009400864451600400c155110f5900c46900c01d040d0070740800c158101420000342d00c4000300c075040e01c00d00c00c1e000003070320061003060b4a80400e4569 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 970695953 1250 970694703 970694707
    0xd08160804020d0f061d39040209060a0201020c0c04021c1a0a030b06150703080a0203420a1d04052e0c0f0e013e0c0a050105 55
    0x19401c1000300c1a84030360640309030720400100f0010030080d01c01c2410031110030701b1010000703522110090a0501d101e03949101c0401c066118803504c0c2007582c40450b88000c080325074200030103410000c0d0090007940041c5801031408a00000000d0301540245904956042103a84512280302000141d104141c1d010070b1401e44028400340d424113a811840010a8070b900c0402040e540c940405c2890800354025186420800700b03110ba40e0600600800502203d44459450b108998030007520800d0040c0c10107044c164000700244242c80c800000240d156000c0b02601000a426510396603e491840382c00c1c0920005440a030400e440c10036054411280c3c401070030342c15413205040000540a0081c81604c660251b00c01090920350000c0ca03a2604150303000000303040c1100c003240c103c2203804203080301c8203000602100401880e0001051001d01c4001d103030607002103488200d81d01700c1035450249400b02c0f0659520309002d441e80941d0410350813a1071806c0f12050010300080104407100c0384512401310700d003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 970697203 1250 970695953 970695961
    0x6050105040e0a092004050f040b0105010c050708030f12072a14030408011b020c1c030c0506090615030309060a050c0a080d02090901080a051c09050306090d081608 72
    0x2d001015072282000d080041c4108041c0c4880305000800d04640209a100c410480310074641841200d0300002c890185120614280e0f40700803080d601805200d040c404100e076500708205c030800020015081040641ea2039080ca009000720700d030000e08a010005003140000303005580720380c403000c8001c00d880c00300c0d080c0f203250001d0b0081c058403800815555981c44041201d461a0100004d1004040a0000082412a01c0034041080404081000464000c0842500319980346000300c07211506c00498103210b514989400d0b9003a4103452001401405403108000c0c45c480042021403007140010100c507403607404601059202d100f4031200c164440c400f07001301c096151140c0040d024200c62802102c80008440d151900160042d0045850300c49e0001950071042c01c0603441c0500400c2180014142e001e00b658415817503196548080040000d41c040a00d41c030b84c4507002000040c54090140d81490a00005098858440e07160a5001c106a500403500041180a89003070307822082d0f50b1402d90b919 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 970698453 1250 970697203 970697219
    0x121f050c0705011406092202040c031b081815130c0f030f0201180b031f050406030305030405281b090c031b0807020a0201080406140c030f06040605010504 68
    0xa000d84080c020160074007481c00010024400d400b80b950403e48040e001e45050010043c0c0e480b4001e0040310b401c4400c8845d1410380019a0841181c281c2c110f402007441d00050808500511500c1c0703d41d06200d159201030701002c2e8000010714024448510001150802c0700d1840345d44608080c00c03010b40c1da80719000201c0340302003551f010034424400c1c001e078084c00303640d418030900d2211140c2050300c0420080b1280411983c2001c040c0c5000d402903440010190702c0d0001d1802c10740002000f5010300401e40f041c0ca06a01c0c000d0300b10b41c02805004000700107082d12418010310030307001120101c83c144118010050040c500040c1a9a880108500040320305610b40d68031132440c2c2040748003c403034110038001003000d8202d8082d00311040100c3da00041c05407100304140c98407242c40c9403017405101e0501c00344000300d61b0114588a01d95020b090100107900e0f1464010014820010800002c003001030034000b00903540c0e00207500034502881d120b00306403034910400040303403151301c40c09012801c200001c004135a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 970699703 1250 970698453 970698461
    0x908030f04050d0512130807060c02130b0d02030628060305121309060b18090c031b16050c18060607020108090118030f12051302040b130c0e121f 64
    0xf501c1002542c0d0302c510045120f086541004002a0a400b0415400d00900e2000c00546006111503c0c00c602070f52800c0c0c000c00c064000d001808142c081e1500d580070000d407240381300d80c00700c40da028048a1851070b1a000001d814200c0e0940102c2101c24500320f40c0902a85000786416030750404d02403c40f941c900c405600705039010300126441645400d100088108003032013044020914243c080c1c0c0d5806101114142c4146c031500e581d445050160b0a01c61007003007060a880d0720001250040c011b00140c10840c100d140640407002150100002c0c0e00010010045480266440c081c0c9910401005088045490a404440c0385e60001c0c41440f0030000756100b030707008942140d040f0b00002401a400130050340362942130349040c4c1c041105c1284010012740e0042c0b2003e242e4042c050100650b05116142501d000054540030348100d0311021f2240c503c0d503e1840f0b0080074590102c04200d240d4900e800500718401d0300c02940d103d40401e11024040100c0841d034160035801f25454210b0040380c0808820080c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 970700953 1250 970699703 970699729
    0x61906082a040e1f1d0703020711040b040b03060a02040501090f0320210a0b0106030b0604031502120a050105042009090405070b0f0d202704090b070908030f0405 71
    0x804681480c0d405100114040041c04103c1781c401c02c0b13520140215060b25801804082c1018410081c01022a50524050000302e004990104007030100b400010060302120783c025078180aa403050004c425080c0c1d0091085580a0302c2c1e2403105030380c510a01200100c07a00c40a8107040c2c0c4040d00c1500d03060b07102c880108a06004001881c00b9404010450100305280c00221040e840140e100051002d524101c500410603032400b801100131040224146024511004103984800750050240c0501901a40e4104482030100142403419003c0c00c0e000d40401c1c42030741e000d82d1410140c02d03001c00b5481d0301100c0080100c49114500140d0340300340405010000c100f0f40d0940034100c00402d2540104000740a0060f480c0003194455401c2038092080320001807021990361041c842001030742d0342080c16909260b00d517400c01c00d010032076a0b0300b90280140c0c490460758841c1c50443e008007001810101c0501901c591754980001c240c1755441d640c0d0703c1c800c1082030072980c1c07402c2c0420001c2c0d261101202d811 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 970702203 1250 970700953 970700971
    0x3090911040b0a050a11030903120705101806060503060105090c07050c0402040b090f1e3d020d020723150c0f0d05040609060503061906082a040e 64
    0x74240d55100440e0240d040302c0035400c0015000034075200300d2076001440d403490a07a0b9001461411a201d40026a50a0741c0703026022a01004071752941400028000c580d030f681600c074014094a0f8983d821441c1e041040b0a080b5213441c5400070116003810b000514a050715005024007656885413078410751b49030080c02c012a0300b4130451130355210603107442c0082c0000385004141c032500d41b06d103101006013050020541e0340c01a840e010102914400c01c2c0c03220300c1010300682d03500304d03074040f400090303100003020b45c00344400b42031020403803469584910352604080d14a542a1145882214412078880100d071280391302600540c2481601c2d410400c80c2040c4485000381a080c144030381c40d50316078203500602c45000d12500724842e2401c4041c0184800b210300c0401d490000c0c074040c01c0c12400f4121090031701400040140c02b000090890f10340d001003000c508204881504110750b10100185066004c450300707100c00c034450b006041d05116001c00c0c3d90300a00703441d00850400d4145150070480d2a0010701d1202 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 970703453 1250 970702203 970702207
    0x71517060d0c031101030b0d050c0607020d050601180507020616030b030f100e010c092d120f0c050105040815060103022104030e0607050c10020705130212090a03090911 74
    0x800503010b00c0302c000c021403140c42000044010710780090300310749400c06001c1c061340d2841d00319000520f000c54402541c01080300e03c00e0301d035035050011a008148000d0001d00c20700c103410020030908801c000d200d8280f500e00c03c0600c16a031314040200d031200e20696003100c0300c04c0d03410380040310305001c3d402001440d40c000d41119010080d442c1454600b0608096001c0d40300c0d51585404d400080a0003098a205070070304160010b01d1411100c0e0401c882d50402c1552030031441507626016115480d003e0707004011526118840131000c1c20329071945051603604442000c1c00d42c0c03000821f9405441694210b88841d1b01403c2d100800c2c24940c000399000900c00ca0406600304120103c41103101c00900040101c40320030015454186809854090004005803003002c00b0b00c01c1d8400100001005402c12905a69501d4070480712081a460021241c001d940c2c05000401c0840a0049503406803508140742c507200741c915218210f556480c1e0680b0354000d8000341a1210502101c01c981c0c200c0d07412100c840800c07038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 970704703 1250 970703453 970703479
    0xf05011e02041d06060f04121103150109050415091a01090507090302060c011805030a020d0206010f03150605030102031905010509064b10030e0d1103070f0c0807151706 74
    0x800154401e41105a8040301c40d5295018004030307200e840750020003540186001c80b402c032f0302d01012580c14421180701031349503c00107081050303003010a0825560002c00380107014a41c42c25200c1130608410022511246900020b100a2030f4001d41d805403205488004107030741180c007070160710b0f400071030038041c559255072640e020b0b8081d040352100c0140c086c802035612043c0c601002030908144042d000210362000c001032069001003500d24086070741c0040750069105242c081c00c0040c2100754009a85544040100048000b00c1e070301181c1c1d01010100b04220580e00c0f078041200404007950300c0c5030442aa40000504061035140f01521f40488101c0b2110380030140f4044566a203c004a9000500a0780c080344204e0800b10b11550020301d942c01c2c280106003031240e22950725421050b0000c1040703810b20100b0f64209041c01160240c54108100a0b04404241080401000507200e54044d80c8030301800010b10710540c0c460601ea0403156920400520881d41112840d50b101901d0142e00807800c441c44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 970705953 1250 970704703 970704727
    0x12a020a0b04062d0c050f100b120303090c0f0d080301060207180c0c02130b04020d0b240a030c1209200f150f070f05011e02041d0606 59
    0x1540061644404440e0b440d41889802000c1c00c1900c1504540c101000280034452610480d40345009502850914925002c500344145800352140082c05a40101c2c00045139447d0240c000154a03141a00d801081c2c0180c4030070b0507503902c001c44080340c0b10f40120314028150300d00302c0f004504064008240610b45641620f8005603940280d04c04409a0301440041003024800120903072a0195290204a814210b08c0054941800a20b00a1041ca004581c0c4e035688461035001c64000d00f0003520440d218208205d00d00002c10003c000980b00d41007103e0104505508072154003c010050744595013000c06021059024000c0201082d040c496200c880b4602c00b6214420030407540c1c000c894031065076407000050080c2407a003050460245a290300c0002031034491f114400f0300071040f83c80302c0340d0361300d259607080e091401900c000a02c0c081c032145218060202c150096020340380b0382280c910702c0c04030040c2408220312071803040880d0340499052041354400d48080b036640c09200507150625210080500c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 970707203 1250 970705953 970705969
    0x3060108030a0e100507021201020d092f1c05010b090703240f0e10150c03080f101205011d0d0801080f1203040c0b0301030c1d06012a02 60
    0x28000340d800400d10480701548001006440d2030b064600c0424080b0114004040344203582c400303400340c420b8a158914203482503048942c500e21000c03040103001c02514001c0f80c1140000400c0d005524024011482410551007500d0010f100030250041034010804a995900ca05901681d02e03550711000003c040c2c690f40e0846100e90102c2e039001814811441a50041104103a98042c0e801c0c0c171507600703014100760713004994241c1c2d00c142040383c0c0c5503484984d960030700780e8160040c40750648045c0030340034800c0d0000001d1490512a4403806015620f0012004c101d039011915402070083c1903004001e11041d03d0003608845009400100da1580307040c2500c0804283c41444c403620303a229030302019650703500c00314040c00f501016001d0202e290700720102d1550750582185c04911064000f02013400c110680c541300000b450449201c0d5100c3d03960781440f043d1030b03c07548101d0302c0c01d200c404014483e98803800b140a20800741615010708110600129044400800c4001c0d0210800c04031a40056910140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 970708453 1250 970707203 970707209
    0x2040603020909090a020f012304030308040308010e10121a010e01090605010305241c031e1715210f150103170a03060b0a0c17090306060618030601 65
    0x5000d03030b0341d89807030050011844000b4000042a013168141400603039945001c400e1614003460a0320007000320722103102400a04441d45510710301c0000d400000c05802c4054144a5030080e214132a09aaa8564405080204856520312040d4048042c40001326407074007500a54040c03800100903113010f2180c100c02c02000c4c1c20a02803800d210b001002090824040c9901400e000e20302401070342403006010250400060f11340c00d003810900503803007031034460680b40c0c0188940080075102c103400b1418007400301007601c090072128441045914800368000c50000141018855480c0440c3e42c03000803000e00441c0c0c2030072550344642004060031031824610301102003415218050611501440702803858564460b43d8105240108401080415072000d041c3e0311412018034034680d92071140c40c0c1140101030607084a44014004210030007200d6018844010451080c4529540264202e42e135802c14082c40881b2039061b805580003621b241840405800c0001d1202d5000e860842254000707814840260 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 970709703 1250 970708453 970708457
    0x303060806130c1a04141c030507050d0908100e0c03070e01050f2d01021006120209010e011a07050f010204030506040b0a021603030b030f01060f030201031506021e030d020406 77
    0x50010002d000c545101d1900030090b00c40446130000700c103284260b0b0380c05248035852402c41d84491641d5551180d12400039000350107001c0701d0540711103140241c042c3c1c10800003603034a4410013507034000e03480c040d12142094400f010020144104081c07802e5020b080f03854544c4d5201d020b003074104411510100101d4015060105e00040300358109014400294190f0580910401d000c4c41d1890743d24500340d030b291b4400c50390b4400e282800c14004006070706c1d124510025400407454408000b80b02c0c3ca11026000506200301d8a0100c1640e0701c40040f601d0b00e02c03c7c014098101d0b000310321200091112030081c80e00c28420340580d00c0c0607901440141c00ca0b0030651040d12a60080d40400c0100700d15800d2043d80210550021810404285030030004640c501800409040d80c0b118240703e90f5a04107e0f1890081501d0003d00400340c0fa603040c0c00c1c0b07220303440c80104d011908001032100000100610f1900707075078159004103030061002c00c05141c85441c442661203140000c01200205024900007400a00515 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 970710953 1250 970709703 970709731
    0x907020106080c0603070504050d06290301050f06130e0a0506042103060303050706020703050d1e0e0304120f08040308280305091506060d0204141207080a08070303060806 75
    0xb002865092030342515482d407184104000b00840030f41c1000585040d548180c0d181c4550000c00d01d003a500030034900c1c00103009180003e01403541800708000014a1503801e8001303200303a4564160705100c00405813900c507805428114900c0558507154400c0940280d01c00446840b0310094070351505192041d20b080da008910340880c41100540d88060b0002c902c01460304100303203031860f24001c02a0040d144001c2002c1e400103011814544204103446c101c00101500b080f100e00c4501c1003070600300c40b1800589816042503400d1503606008000d0318200e030000c40b100400c681c0e0a95480b140b9008004c1c0031a01144280808404110201e014014001480d015900d0508003d401503c9100840007000c080605107010031185c810046085c80f441c41c0b08202404040d15044009410380c0140c16004139070034404030f800070b0803004240c030007401d00300d058032002c8400c4414044592913400c4d81c01600354541c0284440300016400c1d034020074080d030003447c00191945c0c0341c103d01410128261031000410940c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 970712203 1250 970710953 970710959
    0x1f0b011b0b010317271002060408180d060218090709050d0b1e0112051e030909060402091206040204150f03030f0c062f0a0e0d060e0304180510030209041e020907020106 74
    0x4100c50f4214071b5552800100084d20700750340e60f44200e210f151503840c00b0446024211501c0d80714010b500594550002d4155218041100d44a0034180c261031181e1103006498040b0301040e0003260780344103850700a045259108041e4958162860019103140c072101000c08200c10700c100f102e0070b00c5d070280244d400c00301120703900b81c01c00e6854842d40c4541400b5694450130201c002d003100001302e64a60078103694404155580e18000f80c020b0103032810380341d084041c1e046800b41e0040d01240c3d25110f981700700c6081003a9051503032088045211402500000c20b641c5105002003809009082540013283c51700c070000300301303d0740d501d17043c3c44081e21182c1c403104e012840304507106101c0074464103010913030140c2410040220001400000e5000c81203019100c0c2c1c1ca0000c09105082e0444100d15040b00308480d6100e0b900c0d0307020700c1011009a140101d1511300404036600c0b09168a041040302e070010710a014580341c5440d00c4100c904402140d403ca1211075a459005803981601188500195000080d050346 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 970713453 1250 970712203 970712209
    0x518190206040e19110a2c0910061101020f031b040801230a05063706050307090f03020d03030b060d050702010b0f0f06030a05091f0b011b0b01031727 66
    0x2081540030001c00f1803e00c90442c0450344544034500c0004120000000801f0709009190409110038015402c001544100304942403a44c032054100c8445a075040201c0f42e02101c1c441c03c030b0051100a205000d02040814103084043d040369910340c4203440090300d041d5403203004c10b0031601032803200003070800c103180e041a8112070000d1855200f03140403814846840e00d0000105e511894043c0c68025440503118000e0304107042c11a01720501c5682d28105d42151240d201400d40d41044451000294003600c0200c1c2ca503507040294402c50f80d02400344074000100b550180c024110b000d07200740d0018818002c0340001c42007400351500664564000050b440b40c084107021100300c03074030252805981c0c0102102c1554560724212544100101d80005840c1c854140ca10704000e84103001d00211032074001040410306080d808240001001d0722407152081c8408440c26001c2c903882000783c030403001e034401040801c1d800090340300c1c0e01d040c0714a0301e0700c1c1c8100d101c88400301290005040d00040c0701c060155001d81 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 970714703 1250 970713453 970713461
    0x21506012d0302070f050732041805031206040b04060e1f03053c0618280c0506120703090201020705090702030d0518190206040e19 58
    0x20a1030721180c1240c00940100014500440c2090703105008000142814425810f0b038000c107600ca04034000c000e00c207040591b5181300c54001d082840061003420b0861044000c00126004080c89a0210240c026000c000040905412820b20105414000400107406200400001c5021181a1070504202c014001156a1700c8a1a4001ca182140500c0070904a0305401c3d402600102d5000344003424000341309080e1040d60004150f0b20401e01d5a2444080c15040c064544038030419981101468494040c16100e0f158440c42c0a034000740045103400404154907e88480301d00220780d41091070405880c81e41d2801c080001c48844124005000c200812603144000c1004860050828a1a201d04003000704042e10341c005040c0d0380c0e00702c4411640203101f0756004084c024203030a880d1400d0000607440358400c1d9120101d440c9030400150b808440c0c54492084089044024140b1800881019850011009060340d1101c8213001c0065052200300006101c0d44640c3e0f14529403441800c6900255 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 970715953 1250 970714703 970714711
    0x9060406030e1e034003030806030706080106050c0106170109050f07152601170d03050903040504090804090606090e1308190c0f03110f0303010f0b0307110d0215 71
    0x40400d10030280c520407000040c0c0300e5104000000310035a4000740303010109203242005285c0c401484038181d10600c001600c401045034040c1c0c443c6100356030f0302c0042644419a40c0501000304a400c0c00501001c0d20481c081c08050a50800005030140c4400080010f00302d48210a4048d0391100c2c03d0f81e040001c1409003c1d040411240200302e01402c084031a11a074600c04168070400901001299944030790b1310200b10b032021590149090755856221020b05401001c00c401c0803031041903030544070310740303e8810306100e0f5000001441c1403030b040c5020013014042000003510001d906101c00b227100d031a103110700c90080019840d94125070785402d09402c60310700300502800307401429441101c04601110704850f00031211074510030700d11610032010364141742c06000140c0810740b404050010140c01c030240c1800c0750a440c08552401200e410441e41d02d1009009660618110b5401001180424405590081118204814a0051001da0500d0400c02c0400b180043c1e10030350340009905404d114003500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 970717203 1250 970715953 970715983
    0x16030203160c1404090804060e03030d06060201021201150c0b130b1303170f0403052b0618020c1f1d0a030306051c030c0501111b0c0409021c02030309060406030e 71
    0xb642500b1b4440000e180101d11411007400640b00c2c0e040640e64040c41200d24000b640103040010315140d0700028000d403c495282c0c1c45118400e0300118000a841c4810040d444850756000420061503580089021000d0401a86550750810070000140208240c40c41074202c038031312030300100316800c00400081034103807611258284c00052200b0380e0450b01e00c159105805050096880503016100800010100e04030031010045215004841b070103500424201d6560006c1c11900980400000c800ca1142d03441c0c000882d030050341014621014a460310701c110320f0840f0001440d09000d03201070910743e1020294401608000d008030109a0544030f0b590150500350380742c250f000800c845c3c100340018104000f03401d0010034121101000400d4008010a0b0355a50b4130542310360f11800d999290303141041c80e00405005050440c405418148900012543c00605405214014402822030080c034031a050360180410003e01c071aa803990f5009000601a9540014800348005281403d000600c442095 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 970718453 1250 970717203 970717211
    0x4030b061504060206041b0f08010c0e03010b0117040809040204150318021005032509030204180809060a1106131101020a082505010c080106080c0403020616030203160c1404 76
    0x1010344e0740010b080c0d600640c401000782000c2004503022011410640c881041c03907070031040101e40250306400c80d4025407400d4540a020700e40c14800c0500340e0f10b40d000c5160008616500d00d1108940f04441d0b96001030003035285600d8491617a010500741e03881380d0032201070042c10b4100d01310001d515105804150080c2c641040031044554005a484207005003020b003004400310104011803030300341000101c030700b140300094104800ca08d4082c2c21b40b001440141d20480c41c1c1030502e00d1200f10404091101940a80141d03c1c2031400130030070030a41c00640f00c50041294000e108a01e00b1002c01c0214002d40700c4e213080e807030b80051754901095172500c84030100c0d0440d080004802c2c0002c0c903e40550b0f044050707a00501c20b48031460b48508642c1040500050000c0d82404501842c4079080180b1905072901641c483c143c69031058040c0245100d80d01c0000d4205000708442050b407880d40342c4440e24588240306682c5009038003d009103e00c044d0703000c01e9800041d1010b0030001e40412240880789254255000e00c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 970719703 1250 970718453 970718459
    0x120f060909020a0b12270a211803020136030b0703020a020a0201031a1c0302010e030f120705040e1602070602011515090b12060906011409040b130204030b061504 71
    0x226494002030b10301d0140001c1108461b1200d1a180010544010703800308036018421181400c0b2541e100e142d90407080c840d80c80e181d0000e06c034410b408517a50110041c02c050345192440e030046400c20502c4504616007191850903a610060901c1403032009a0a0060b414289041d800e0400c46444060f10a0302818810400343c24030940200d090a2803c0d02428002815441e09414116501c1106d04a550002c03540002a805442034424440654029402001091040004107689100c1d04000d0000210700340070141c1c0b4280d03901c2140d40c0c011031a250043c01d20b80c0e40c10405a40442c140c501c041403109030b0042007202a410030081c0c006003510300c0240184590750024200850690090408036211003807805506130003880700d00004d02004447c0f598540c02d10035030311400d110035681d00340f2440c0e680020544941c860b040356261f8a80048200c0d01c0c0012200c20400201031003015160000b089640001c6440b01034405000294000d150041c42c0c0d00d45041001719002c0500301400c1600000c0c4400c2c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 970720953 1250 970719703 970719727
    0xa0f080112170d0e0a0506070809030f07050106050409060b03010e0705181308070506040b091f020c0f07060905132a0509130e0c010c03020c01120f060909020a0b 71
    0x444862500300040c42500e61441c084480e41c1e1080c0b202040f10141407040401035014002480b014060144081e101c0a46406108582c0346405403a0f8091981c4180a000c87c18100c52005010544c40ba030000900344c0d944002050070786400001c01c0d40c18558860504c1d555040c280104542d0366009405040c1c2d00342407400181c3c58030800001450700540031800034a14180404140010301d4125862940710203582c9803e954800381110121107540782403020034000b0000284030780d0202254450000100d201e001e16500a402050318218036200d405060800d01f0b00501c5140d000e4003080da0b8030050380741401c080c055801d500507284020301e8686076104940c1c2c0120070020400b550700800e4071209901d10401256076002d200c0400768001c03409008041c41c0320582d409160103891820176620700c12511401034070354480e0b000020303015170418207121006612821010f10f1410401c1c40000350701130102c5524007140d00e0354010b6a801940c030414030095180c10a0340720020700c1c0381036206181400781890 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 970722203 1250 970720953 970720979
    0xc060801081506010912111801180b10260106021b090103020a0506071a0f07120e250e1005192108070602070b07110c01080606070206130603020a0f0801 67
    0x501c01146d0f6111301d842c02001030489000c41c00c10f00c024101c84800c003000d20200c020010070311906112100b020003800381003006000396950100c000f400e80705d001080f01019a01c0c44c50304142c401d45c0d0044450f41030545000d500003903003e441f00d6401070001c1001842036aa8000702d01d00a580300d5024400100f0060f51138880f41e500fa240140e0701d0680354102c41c0761503014002165200b150001070181013040c41a506030f2001d2081c00a550355030311a01d4207903220412164103601148250700480d003880d02d500fa1080700b00140301c144e0064201d0450303460381514840380c01503d502540000f0004104040c0c07801400006040c1c2c60404049142c62070301140e020b80302c030781402c048040e6202e40b030a141440f018104ce6003006800c02ca003907680344440d2a040242c42001c85a000c04103200d10141c540c20b080004801c003280c441a15100310301d0f1110001c01801360062001241c0c40702e41000110701c800081d214901c0201803d4a0141c0c6900341a013000e0302400742862000c1c10090781c3d500400090b008580 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 970723453 1250 970722203 970722209
    0x51e0306090f071a0f0304050d120b1f05041d01030c0b0309071e030c06050a1218060e0a3c03050d020903070e0c0406090e1b0d090c0608010815060109 66
    0x40c0c43c00300c181c4d4801c558451030143c50a010039009000c8100824000085034401c0301c0c0c01c0941d40c001c81c40580c900a141210000c60b0541d801c480101d0341682142c03002200801c44c2c100c9805d216042c950380340c00304200707540f0841a028010210700010001c0003101030317030400075040f8056090306600c3c1440e4003c1c0c0e9450644280641d0740f000101e01d501c0380d02407285480c01b6542160310718211503152540038010b5489030b10000001600c07080c804d03072807201d18820f01c1d421480c142c008185a40c0306449150241001420012040c02002602d00014140d112000140c4d02c0a4428000d0120608881c9602000c1c8801c94030400b00d0311604080044c0d84941121300440d103c040041e01c890558002c08d18000701c80c4c000c07450307034146601030000310b84100c030280041b035100c2c1e59440411030310382c2d40300140303400260b5007540c81061514442010380c1c155406406016242d020018000c00389844840d00b9904540c05500440e00040042c445458140004000f01566164001d5103041400008241d00b03801d00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 970724703 1250 970723453 970723469
    0x2040314030a050a051b060a091b080d030b0f0d0f02090c090603240d110f06270d1e02011e020a0206030c22090b09010308040b030a0204051e0306090f07 67
    0x5641c9042c150805005000081c000b011101107240182814002702910321043c0d82d516006a268003c11101d1034640050320416000b034040e00c0241d184c194050300031803101981c007560340303503500040d62075600c07140080138056216a5080c218500501c220303404054056001c4403001c10031440c050702c40390300f200e801c15036103401c200d45010803001c1c2d0306105000f0300302d03143e00488034180e09060246441094030700760b0080322100000c041900400000344101041c01c1d100181010004000c002170002c2c02c101c40d0b01c007418440e001d000c0d5550b444500c5818008140c0c18403c001c494030190350b8000c40b007517440d81510301a91002d481080c4007940d83c242502c8002d10543c070000c0020f403124a400c058540c031001380014645071116181e1300b00a10f2100e0300a0300b104074500144009503152020003e41201c0d00a590b0303500d01428403080505a500c02820300107026020400001e4603112441d9a0244070201c2031001c0004188030300b0541007000181c68481c4a602040c400724000e40e003c56001300b111814 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 970725953 1250 970724703 970724707
    0xf0d0f0207120f0813031707020a020306060a06091505041a0409140906040b0403030f020445050624130506041401050d0e12070c0b040e0601030b03100f02040314030a050a05 76
    0x52504994211f40d001410b041041f0210503c02400e4000401c405428822000c1d81c10036615039081c484c124555100310800142000da042003055a0729400140e03112151408034036090700c0314005440800381d51b40802100302c00080c204000d80e0f451050b50700351403181500c95103038105048000c0c1d454402a1002e040680804d02050816000c0d500c60b043e8446d0418041d074840d40e6a454944110ad0000080521146d00078004140451085d0b41299001c0661030105400355548881100070701000300701d20380126240105841c0c2c040c4440c40e060400c600121840d541b080c04101c1072a60300c01e10340c0714601a01c0c00f480280020341e2900080780044034286081d945a20295a401001d030400f074460054501819840c804410103000040801e0742c01031001c00032036a030340c4001207400c0c4502d1044e0812100448042195036101ea084204440e100601321032400092003c4042224507030212048113079400142082001517000794507040c0701c1100b0203176042681d8448060454490607550400304440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 970727203 1250 970725953 970725991
    0x601050d2d1a10020d0807050706060e010501021c0e0d150e0a02090f0411060c1507020601090b010813170d0207050d08012304020f0d0f0207120f08 65
    0x21041d4003580401c010301e03000050991014140003030905482008144002081e09160360a04001048004056038010040b107600072804480c01200500000c080000c10072007c0d0205203203025000250041004000a0794507285c00649000c85810b08001e12813002402c0700c1405800c04802406003c05850612151030b01e4035200c0c50700355051061900040c0b51400000040000007003200c6518807e0350001213684a8050810104500b110003c04903049111404081e04210700546405801134040366000c40c02401045803001c1c003200d0440041e84401c1c0100310620032801100e040080030b003026205414131041146451899000180c02c03003150350f0070842610301038004c65010751138080342152607400324641961141c1e480400100004c0000001007042c1c11441142e04003003d1410b207a00708202d60340103004c00313908040311070000038038103201c20842103220b4002d0100c80d035440b18005968113407514082400300e580003d00400c12501c140844200350b040100207400903442a0f1071900706031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 970728453 1250 970727203 970727231
    0x80a0b03030f041e0611060103030f0509090a0917040e0109050912030703051906120209040206090a060e040608010c0c1704120b0417090303070821131205030601050d 73
    0x2207080c6010b03481d2000041c000841c484c000098240c401ea6491240c1091656142c00b100d003150346590903480e0b5003110004100203801044407120031410b90400703134200703105400050401c8400f00e8581301e4003919820f241080007481e088500300d4150700c00b682d5080905100340c14560040c14040d0450309940c1d98042100c4510803c1500010b03001c04080580c1ca181902d0010050070301603840f051b01b181003009001034501c5900600c030039a00c00c001d032803010003803a80802c2091b20340588183e0700050104480a11500c4006281000c0c0c0500c0d1101001410303034809000449031031350700042203039142a4a040c80c465205005154242e0011481519410036520380e0b0507074407517644000c2c000d8000c01d50f82c00400801000d150b01c22030154011000050500c1d294501601c90007090980c150000c0042d80c0000b220303c009003003504003070500003141c80c500b0214800001401c1c0d40052a0400281160b410040320380105089480c840c43c185080d07007403280002c0d015004121050707007520384400c107000e0920 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 970729703 1250 970728453 970728457
    0x5010b2a03220e011202090402010c1a0a060e0c0429130e0603101512111002060f01140607060903030b0405010b0414010e060301091d0115090c0f080a0b0303 69
    0x7812120b42010a8260030075600540002d4410300d160381d4041000010340b1038444001410f41074014050002c06e688560045034400340030502290100155018140b000c180c5400b03c5110398500c030400207203070f800c1c81c0c40410a80e900401d0244107420401007400202d22403400703030241541b00c0c1503000e00d0410740203081c6c02c140034204000b0b030a05220039000030302030680796003103002e2003055007503a8108401e00c825500303641c1c051120721920318528000f00504031191101c00d81e024040c0205401458030840010390b0300d0301000b4001d005074000014804442c0031460300f240144890342c04007406903076480c045101d500444101070030190791074029400b41030090300140d00d0140010000c0001d5a125403180c1c80503003203402480e2907642c02e03400c0a8095402120402541480180f5043c1168030305001170018000000c0d194034801154081d01c45060300034050485c56410410301d814800f820300441204982c0e281d50881c5c100038511032843c82444e0802e0354aa0014400000429041d404030b02103440c41c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 970730953 1250 970729703 970729717
    0x50a11090a0623121e07140a1202370804030804140604050d030608010c0914120307030815040501030b06010309031b060e010506030c01021504050a020d05030c0105010b2a03 76
    0x3071540020b450130034051035900707a4850840380d0b03645800c0c000000d1005040d43c1040b01c80002007206941c001051880034800b030706019045203000c4006c131a00c107100c5030a98001c0c0e40190884800b07441a00360154038040c0214180c1d02840c901005850064802002a040070f0000350a204002c0081024002c40d01c18000b202000c0d401118070a04061074071540c1c4030303a171007400740c0000d10f003450205840d44103000350302e81541d0035039405658500b051520307480ca0b01d103200c04c286d110703001641c0d12004400602c06800024001d440b403004520780201c5290f40c180d005c0461f188944c2c5040e006200140c0c80c08215a0046000e1900040c0040b0500d41a505402e2100144131060010030f00442007110b2a00442141c69006009011781d4503a4002d041e80c1c1c9001c40b0340305000da0032500d900c10004c10f0703150220b92301c00d004004858120160740c01203031300380b50094070540d0203400002e0203580030403007409014014450300c00d6403450108504c0095000c0c901d940501c0006052144000100f4070b000c00c203840314 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 970732203 1250 970730953 970731017
    0x40c02060f2203020c040b1c080c070905090a03090905010303140702130518070504091101080a020409050c120709050a05120106050603070903031706010c030f0201021c050a11090a06 80
    0x40b008450030041d5a030040303180400d216908201c04011103007840360a003c882e220140c2e10707102e204110b5031451a55002103050b10110b1181010001c1c0e401780758066a070040584202810380600d45050083c6045640d070040300b0114100001000000d5100e12102c1a035000444c2c4a91900b4603803000980c0c40a1040d150b41c8003d042c2000c0c082c040c42c2101c0c82d0000703600c000c000c0719180b541c0c0380180001d0707510074400a0500400826a500304d0b5014000d4190f004214010052130b040d10390454508a40c81a20b61400b40c480c04504080c4034000c4501c50380d084102400c2000c1281e18000001e4102415070003150300401e00c5118800443c00309400035009040700030b005a45901e00840c0052158085200a4000502c1c03401c14a066801c44c02c0e080b8002c0106940303103542c4541a0f2420b07203085d41c0c500f80300b200310340d8200005c2416146c1c0d064015110b825440c800300d0381c4d00305050a8800d50b48045541c10a811040207400e5169640904a5045031805e041001810020011034000b000080101481c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 970733453 1250 970732203 970732261
    0x120503060d02100504170f0703021c0b011409010602010b0901060e04061a0c01050606030103150213050d050718060f0527010311130507052b09081305040c02060f 71
    0x1030f9a0010058029500f200041c00d01101d1800d0741c031035031140c0c0f00d03120401c2c58001039002c2c4094100081d0161a000030f001a0a41d00205591a40c03050b807000d0f402240b1143d51b1001d80c8907240b030400d9007203005124034030003400210b1500001030560700041c0315000502051010b000b0154442c1d80204000303000304411000c0e68000310b0500c0c00c4a030701680803003805529200c0095a07914240c03023030342d041e00d8001d034940314030084021401000f944201008590140d0410000603203680701000d20901f14030440207005840d203030456030311407481d42e2101403841380c1c00c1c00360a01240d84c02074004012078400700c41010303136541c0c446915689079124031071080c031001905001005122504606a22444098404641d100d403610701510403201300342c442e80c00103901003041e0021000c650030081003209504e42c05400c429070700041c0108941d815041141d000102044441414004500340001000d040d09c0500c031008010000035118007004220010507018000861958684030824458980c54048541 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 970734703 1250 970733453 970733479
    0xc141603150e1203100b180102070602060c0f07080d0905070f0e0105090105060307021510080708060f0423010903030207061d0607050c19032a120503060d02 69
    0x2000104490105549610881c107a003001c8040c903100c0c0382807010b4224042c0075502604809104603038006080c140d07000b03609900c003041041398040103114142c6418000356401c0c00314000641010300030740c030140070364002204129040182c50201c81d42a101d68044680d42c01240c40d044029005a03030741107400c189460544400c1000020b040340a07101200040c8041c0c036614110900851001d00400c0e4120300944010000d0f070814001035900400e15006072040c000d41605841042d4408580002002074900407c100da8101805428040d03c991006040c841c500700c103881015000241000b01443c9c512143e007803d407680d14400c040e021017000024441d000403410b000300a90007846040e107074145050580c06d000c4840b140400e07454041c100162501da82ca8020a58483e000220000b40900403210350071001102a12080c000314882d88442605107000e401d040700440030191824402e140c0810b40c0004100704c00f8404003120031503c2e00301c0d6281c0c0e45c200403449001c1c1400c0025005517506a0b11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 970735953 1250 970734703 970734733
    0x61c050f091006060e01051804050c03011d01230111071e060201020c0a06020a03020403021c0302060c0307050316090e09100b0607080d0b01030209031b0f100f0c14 72
    0x85070050710014111100c65420b511280221100c0f80b080320046090610800c1c280c0d40200058500c0d00c901e908503d016480c5440406d0646908441074203101c54004018030441c2900c400598000300c04d4840800c0f01e40c1084000281c0010071007414071400350400075442246e2003207002c0b0b0070ba41c900344d064840141c0d40c0c1641c01c0c144800c000f51000901c0707030303110040b175054414400e0340e0030300180d20014606c0818030f8541e44000d51140700c00c00101902000044003580b1900c038210218a0820b101e100f802c2d0032414000c0c14041c01a09403000208100213011445034840c09583e0010075142c1c1c551941c22241500740c4030448594007081000703240c4010028001f00c0450300f040315800136401400804030110410800c0c0c860064010103000c02807003000d1060745968010032205a06040042c1f40c140e074030001a181801e0300a007075006000c50100000300e0b04004007520b1904c0d000399564030402c0300700c01c0050040422644100104210716844405000b0300c0c1d045c0691004070b00043d2628a00c0e90022 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 970737203 1250 970735953 970735981
    0x90a05030709050f07030b09060933030708030f07060507030906090803070f020706050703050d020915040f0906050f090a0f150609080d02060c0a11030406080a0e06010e06061c05 78
    0x8201ca0f481c04c044006800c203406406041c141d588010113070316165560100f009a8900301505034003802030350b041c2001c088840c206035110080d04080ba220360305148502010b203048441e40181c0c04e990010701144d000c2070515829215600e50011000c40c003683c942c58114010308103010301400312400d00381018103116001004501034a010f03641d944000503000d9007660341b04500d1003402d00041c000c100e6034020038810400b80441c0700c880c0308050700d401c03c18400119001d40d01c0c4a050780002000404100200c0d01d002c2400080008a2003407120500c1e00000480e6044585c218034052086103001944551081c0e0202121100820042214000c102c1075642c00d03800a0041c440494a14500402d600030001008114456242d00401d2240d40d403021120442e002036134420203000c1e079001040301c0d844092004d40050021030303a07681114a4045094030540e80e4000000305075802c00c00c010322210f5100720300d50758840016100e20ba560b07110300310714010040e00d400c804c00d03401c0d146c5001d00c9580c2d408500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 970738453 1250 970737203 970737211
    0x5011103010b070b0a290109031a010e091c0f0522050a240c03090f0b0d05240105091912050606103f0c0201180b0606090a0503070905 59
    0x30713240759103903524000001114a801c01b5184590181110780398185d4403003e81100c4a4410b261148149603039590721024000003840f0380f4114905031006001200c0207002181e440741169006124045040c000e060001030104c0308541080300300740001c403000b40180120fa41260b07548040c0b00c072445500f10013195040b00d41c0a0b052060070217810010b5001080613a01c03071001c0c0690805a01402c08a40a4554441d0890110207108040070300003a04000e44041d90000e00d16161f0b40d030f603110b60075800034040780c1c0010130341409010b19100c013030311659401c059400d4034402803d1030b543e074410ba14001119070b42c0c00b00c003203495201c2c00d0101160480032201420001c5114004681081c0c0b22041007152070400c0d94584800103070010a03841c01180b40140f4000080407040903c04103048842c03003201503031002d144d000d03105a228076035900c4180c0e09104415004a0245100c034038044550749a1544000c00303050030b88281070204442a00d903903070180c41d000030301c802003c56510343c2d81c03000050047e00c402c603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 970739703 1250 970738453 970738463
    0x30c020108010501050f04290a0804110a032102030d090c031208011512020714060f06060423060405060a2007050d02010c0317152e0c05011103010b07 66
    0x800028294017a030140c40c22840500500c5092905014440310140c3c2c055026048803404c125154100d0b14800b002000408400c0d513980d0203170b10b02420303c80b1a4482c9944254003e00322940104085684001040c0702d00914255062605030ba01c04100d181d03002e000503480d040d41c5020380c243d0402407000d03544003c482c8074081c003240e14190307034000365031120702485510790300c0d1441d071190301b42030348218000752111190300d0005041601640b40c4d0321010756102e10b02c40c07850340800148269000d42640059014000302c4142c0d2905051483c041505041607588107995001c000c60b4241a640300010348010344000762115850b44140341008104801d02450880700ea5420151050240004624042030380c0d005001c1c070250105c1030340115054102404241c1c100001e03113810b80d00198010761181d00a2002892050180440c40204101301d250301910070b01c07078140c440111b1280ba1627a250084000030302d0401804607a0b0900700107015141042d036031254818008000300740007103031201420005001e5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 970740953 1250 970739703 970739717
    0x304050a050f0d090e01120b070918060611060601050d0e03070803072307030237031d0103050907060c05150f0a2304020418020a0830030402010c0c050d030c0201 71
    0xb54201c0750410f2000c1c010928600800f01d443c1c00423901455105401003690314201e5032003a6180c9210b154079040342d580441440e20b40e4010001d181e80141c1c02c0c0c40b0038901c034020b03224508120740045c0c2548240a404100540c660152041c0d29509100f5a03415641250356550f6a150101000f00024001c0c001410208a4016045851030403881904c28a0340d05070010038100000e214042c01558a94904610070100c2da60007020b00c4406074508aa0740b4800c1c0c50740c48406030000c80c00350080c0c1913101d1480c109480d050400002100004950048031200d0829200341c05880c140b403810b0101164103a400d8030021414000706460070f4402a102c3c0c045101c0800400500c0e803174800c14010a4080e44401c0001900460017601d410340c0b2480541c141d03802d8184007200640d005c2212a20280d005444c03580201404940700314600039890307120745242c0c2c081c14810b0600c0300e5480140c007000e84040d040025902c0034504110f8804036a001a0400902c110308060407882d008003580d190401c128001088 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 970742203 1250 970740953 970740959
    0x7050f070b030108060a020d020d020a030e0705011106010905060d05030a09050126060f0609040f090c0b090612060118030b06010f02060105030d030b0d02090c130b19050304050a050f0d09 82
    0x300c4142d038103841444025088940311030500d000a50000d4040500c0d1075402c10010301507031442c2c401090100715070784000c42e451000010860428626078032680c140702e096110410030303000125180741902e050541c00101d44d00c83c400132807070812080000400303920002588000f40c903002444901119002d0f43c030250301c100d4840707003c62080403100c140c01c030880e100408650140380c80304119200601c080d00550038404000001800c0d40c0c2035124448407160380d081401c05001900e014000034200c610b02d581d00e00214803021071598400d1007052403003c80c040001c1211684914030380110866030081e241c0b2180d4890404090b40f480c25281607020a19800109094900118a05041b503d0080240001061040041d000b030191b0b01d0f0b80a034080b141e901038000607a128240f0b9030003903140645e07168945c604804804090303100c60300901016001400000090a1081c0401e0400e00f03451901c50380301c1d00c482c03501501d08036110354020100e000d900b01c40d00c440f4030001a5141303074002c81d40d50000059a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 970743453 1250 970742203 970742219
    0x70906060203160b07020a0c14011404140907050405040504080316081015031118031e0a060b041d0303070e04050f13051623100905041802030307050f07 67
    0x803501605641c00440000300f2404264540889640801d030750044d03c002c0502d50b030b6445030b1b240710b50704980600c0c00001c58805007943d020f041480d01607a1014441e15140c108a400c0c1c440610054080e88101003420005003883c0c884c500351002000058824030090600e8a00107006410032686040c00004011421800e140f1440301e10f401501004038402455003042c260303106c0d486118150000741074845410114603c00310700100303045801210608400c0c400e9100705828a0910030405007500341c1808a014108004078680e212540d2140f0001a501c040c540401e01400c18102c0d0098110540001d00c10728440120042d4440d0040d5a212041400c2d44820041100d006581301508060a9800070b603d40c84820556000031b4020710440345844036840204c0c80c0d844003a0418007962011200b0181560f202105008100204a4042061080e11a80100320310001d1003003501c07076038560030313075101000c0b00031400c0c1005030700607054a03612031b001e0800d90b40d104030301c2c00182c81a1180c0400018062 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 970744703 1250 970743453 970743457
    0x5030417090901180e030c070e090303011809020f040c02010501170a050307140a1407030201020d030612030e0a0801060618090605090411180f040c050a0609171e070906060203 77
    0x418018105410b030f0742050560458030401411202c8050303907621a8041100040000d03101c541c107a140108007a90408080c40d803054005030850b0155401400180038080034941003680d000030802001454510383d00015000300d0784d05285a40191902101781d10b10340d03040d0006416a608840c1030703482014003004e5941d48020034100502242c0080c07100400040090f00700d808001502011101031621580310a005a41c0000490a05504c00f80c410802c658051007407986604072420204409850681c44d03007403c14640000508016280702c8400b005c0c1d1303d40310010050981e035802004401d88800c006001e0000c80000900b85481c001000546207149019a800b510800b1b048040701c3c1d1102e507108200590120121a8400205080501d60414440d00c0c2d81c8100c281500e16110f90400b0f08140c045034205400407801403500b41001c0c08003039041170b0780380100c943d400b900f9280418a00800350901141c0790540c030841c0c0543c1504514010001225003d5950707a0008000442d910201030343c3d24 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 970745953 1250 970744703 970744717
    0xf0e01050a030b0a05310203040c0302010509130f02040317030903040b070f081207200316052107031b03090e0402040209030607021c08100e0601051905030417 70
    0x149041180769041032107074200f41002c81d000b50920454680b2903001801c200d010380c0e50508400b045054001543e10049101c01c1c0c003031544402149581002d48840c1c03440c1459000180c1804000600300c0740c240c40c1c003d520480400b01c0c1c1010003e44415140d010040d40c41440140c4640b10441c0c5c40c040344408050882c0d00800107080211300c2c00303142c07400d11042c581000c181601c3d060f800c00d00040c00b187c00c80004110034003c404803e00e191400c2403014010300125048003042c01404541c041300b04000104503404090081c00103000400c213032600c54904a40c0115410300d40c10b843c0b0317889140c0040d00b0050143c0510986032021125400c100c1841416030313002003d000100c05010800296807114185030700075001403c09031414014801180c0b4000d81034400341e006030300c900c580e0405185640d01d461032081162800710800d0074001c0284c4900c040e18095803101d45041404994168000c2044401c00b20450000816070400c80c200034040703800854040d1001401d10342e4680c14020380c13004031350301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 970747203 1250 970745953 970745957
    0x30605060f04270302030f03040308010f0b070201140c0f1203060a061404090c030e0a240207170d320a02040315051914100603090201020a030e0307240f0e01 69
    0x100c101142d05889400143c48002c2d03083d0302080041051603032410300218441d41c001d480301c200c0c030b501d040c40c40341041300e442d40042103035402440b6040040c6e0b400f01002c0368880c4641010f544560071513002038100140b103286001c1620600840314a00312402c2e01851040307008940000c4043d9030f81c2002e682d031103202d00385196000010441408180c90a8cc1701118400d003c0c038001800e02ea116810900c0c114409100752884010110301d28841d00e8111008181460314031815070a003116030341d0302c100e469854000c9a10400000c00c4010034000298072501c0c0d41981034456101ca1000d000341d12444034041e04248401d50280400580b80e40500c1c001c68080301c0c5c2c40b509109010226000207401010003900701c00040045890710b490800c0c403401060100031a0b12568030f40d90410340341d44503030208a0390045003803606100400004d42e0700400c0003c43e4075010b0074036105005507800064200011a00052400e5902100c84801541020345542031b09040d5100c1d0341841e50001815078084114a0040740 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 970748453 1250 970747203 970747241
    0x1b0a030c0315090c06081f0b0a140910050706060504110307260a020d050f0c1c021c09020108060d230a1208101211010522030605060f04 60
    0x41e550280c03601051840b850b0006050145540301c031000304841d4401400140d020080c0105c1d0301c071030b130f00e64201c50ba518880349500900e407481c088128020800c601d800c2c02154018070919580304030480b4000319006121080c2c00380e81e460043e282d901310b103070155807140c40c2c07a0700400e00e42400d01c10501c130310a016840c00e040d0341e5061021503010300300000252415040300c0340c4040813600780c3c009a0007000c132805c0150f12101c909202808a4030020080e92401b003803402070080d10004042103038000d4400081c1040a03030010406900a4407445400601600c20505407520f101810b41c020380c3c109100b40d0340c44809840f40710411000c10060079029240c121038000460340f44c8054107001500c40030301401d5902414440e00c580e400340c85059103100c04285a54200804000c0e0391072003001400c1001035051030b0710325a4a0b50181c40d003d4452a9050002c001540502c00c0a8181d0388d0542011410b803202100d5143d2400501500301501c0480c0162129001000a40381a000718880c121484443c12 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 970749703 1250 970748453 970748459
    0x10b0108010b09190602060a1a09060d0c1e05130b300604050d020d210504111e030706030207030c06051008030a0f08060103330803040303021b0a030c 66
    0x70306a52000003d5a8044030440811840a03100b900c20401007202c3d4001c0c000c10b2130f10008070000e0310483e4094800710300000a51159a07034440300442c0e0040310a40708c04070b140001c0d141c143d44c1078400e60411017103000600d08125510344220681c1c016a101035a95800c0401e650041070103849001040507403100e49010076481d003282c41000040c0d4800e822592503c10340001007502e042c10360130345055805812030080c1400203070301001190141e12861800b058082ca00c49201150b225150140ca4030150320703040031074144007032040e000b00b407680018082c1e1500854000020b0325000007800150190003224000500707140248283d80d0403d4150300e0f2850311072210743c0c07035034010500200403002c2d0842190001c60801c1003040a081c0e80880d90b2284492550f290340d01138418500181814101410006080c00a481d903041c0200301d454240320000700101d03034807042d0b180b121380c0d0740007541d8a00c004034002050550000e2104030021460b815503c40600e5078080c030034800060f0001404421000c0420 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 970750953 1250 970749703 970749719
    0x2e03050705010e100315050d0602210106120905150a0c09060305060a0e130503120703060e04210309120e040f05100e070311070f020f0a0305060a1104030203012c010b010801 76
    0x5401000ca040545410241d22440051400d223041c2d0025202141e0200f26100806c01894081051696080d5060520340c5840001001c2a0301505542c1a090311400e13200c041140811444800b078942c188040707168603001800d500240705881000000802554000a03105e010b803041d07900274034001d030a104000d0700300780000b801c0b80b90107003032005080a00419280840d00a0025000b110221101c1410310300340b200009007643c02941042401a411805000c001902030304110340d148261000310030280e83c8128240e00504a0301d401410b02e41d844904038050310740c00401148040c0c070456007009038a03050403100301194811600b042040c00111807d201943e5044a042d51112140c6004109621804840e0300c46030003110307003201c003100390f601c3d03000451408180c0700c4d00c1201c1c290f8103044c4991440e210a0340e034070400352074130781c0146e40d4048112411406a04580c05190090002d1111a152200340d99076000c0b0031603001440c2c2c10300c4806254a05060084e65081c4005035140d1070540d003400b0007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 970752203 1250 970750953 970750961
    0x21021150803040b191b020906030a1208180a0807022223130c1703040f03080306121603020121090507300b2e03050705010e1003 57
    0x990069011000400203420000308010030140007404085901d45132442680e60440d41d124a00c1000d1041d150101140c081b80c003403031242c40580440304810329031a074802280c1808091140604440c126600c8022443c0e0408031a1340510014a10710810342d202c4280280c03030f80d078150030050070340c14100f00080252401844207100c0340d00e040b00308050030812011b036400315900740c021002d600c2001841609120381065040c1d600c100034594903683c000c240d5a60006184041c01192000f01c0a0480800720a1080003075801400c91000080ca0060712810301e9070300340d00112001c2d88101601c2c0307280c41710460301190b04c00141c0120100c00762514116401942d510084003003000c290354041078644008017440c01036210281c05400609043c9081c540c0880204a42d0100e2030711030b1000c25040121007080d04015403405070002c201c0440354540c01348010070341a143c0020b0036a601410300781c02006203250b00c284212032248085070b14030340c5d0310001542d400c1d000c548640d41c041407060f10b040c141c50003600 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 970753453 1250 970752203 970752221
    0xc0b0705040506031018050705030a15050429030d081602010902130504110f1302180a06110606010201060605031f0308030709170307080a0f050904050c07021021 71
    0x10001d0078030b6100e50200b43d5a070021a610500b024154108009141c407600541c10aa0b20344030f400d0146290051002c1d040c0d2001900e002c90007581c64105491101000040b100030b888010700902c4450854500411426194221000007951481c0f04103000e29000a0030b018410868440401c07a58404048c03403850b4040c0c400007030543d500c0b10300110050760f8400c40329400014001d270001e03003402d21b0306000729550100d2604501408030074500ca81e480d030b52483c903940e811a003294091b0741e03244054403200c0103000d40c40c40b80f41c00c04203e003004142c4607000b80d0081c140c01744220031580749139100c0004a081c1c0705240b0072003011a81c200042402000e812141c0b00c0d0320701d058080c0109081c0e495943e00c5640c6d204881480000e004280180907000c62408036050000140e002903051680703d8460303030201c2c0702c1c410000042c0680c19485400c0315016405964244000802c20081d1303160068040125a10400023280b140d0600603040040c50b0151846103066810703804200040c01e0045088002002210 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 970754703 1250 970753453 970753457
    0x1214010b07020a05180402310203251b02041d0a021c08032214010209030f030408060c070f061802010311030f010b090120011505031b0112020c011a100e010c0b07 71
    0x203000c6c5400c09075224488015042908c6006940e40b8220171000d1700840fa5804040c4030f0802440d0742c17845181d110585440031a603220a1082e0842c1074800180200002c10452558041100ea84905500041900d01d5403600940e0402060100d4003030a6850007401c00b8014201d04050020507a913820740c0c02d0b1810301800c0c0c1050340000303d0441d1207100189101c0400c413415070707400040c0106241410b0000070000c16440340214145814a46255102c0000a00c03035144d80700041880001d00c04280c0c42c9040071500800c00300048003082d03000d407104c1032854506034082030400b200d1000300c00034130341142c0c03044030304032a14001079003418450051903000080381c90403c44c0c1007900d02d14525000c100001c1c50030121000144072041003a0f0308241c00c0550307000d548680c001c103410788140400100e079000c00e030380309191000d02034810003880300003030040b0304003400207600c3c0c41007104105400144002a016080b42c482c2c8100c42044002c84901c9400802140000e561541c0800014601014203030480e2040c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 970755953 1250 970754703 970754749
    0xc08030f0c0c01020d0c020c010e03120d1e0509061003051c032301080705040c0906030f0204090e0a0213020a050a05180405040c030b09071202011214010b07020a05180402 75
    0x400752050130380c1c01a00140c038946a6601120111031b8040000480e1600c081c2400c54580032444002a03c2d8000a4000d150141c000103984c22a54015800342d03004602812511001401d0072914900500c4225042d822601c640808104030b040c1c1c02c0708c501c048945c001d0052002004a0388140d400ac0d015072a90400d05403140748903401c4011110090817440c4140c802d0f4070856242c0f0740824070380310309540094022450070742c46124440c0c2c03060180c0117981c150b080208031000d0594080d8020302c103940c04820800d186c07480250404001103a20101c0e80d0003143c100c62210030500d40b10080348203114100c0080b4200300600c4207054000c030081c014040c005103180d1055040724001c941600d4003102d044034042d034512424070030885a084010b0704001c500d802002c81c98101083d41d41004815840070707044c0002c110001c0c03c04402600314000e00c1901c1c208801c038651351450f030003065411180d8101e12071040c2840c04940d1741400013041610b004184015100303904d03039800380109440480b402854440c03034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 970757203 1250 970755953 970755967
    0x32d0f150810180203031902150f070f09140d060f110703110c03071403031918080309030c0d0f0f0305070b090d0807120e061e0105010c08030f0c 64
    0x19003030514006081c8103010300403080c255000d050840d1040620b030445203582c06040c001584000007907402c240c81d0b41c40200031240f01a0000e03450880114609440d01218800700a00b0420454045000e41c445844110151290034015192070640380208041400142d00085071440d101d8040d0100502a500c00a024802d05080b50191a40024000c1880d10001600b05c101507110240342c510007c40006019102409400682c84900910455164481d00c1c4618500b9640a20031115000300020175140342a01c404009448000c0c50a10404841d005450000340690f0100480382144070081c0a03104601d840341c2000002c1450360000d482c0d09841c900705100152201281110b40fa010b0b8075180d854880b141380510104800034134a032384035000315601507603030b603003000c1d0309a0400f501e828081d0b00c1c5d44266003604001d01040282c41003030321030034091140c0d486e01c0891010744c00c0d103000d910f51401d03a00c0e03100541e00918070500003451607008200084034001038191070360700070314000c1500d494002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 970758453 1250 970757203 970757231
    0x12020708040803130b0408150703020f1b071d0a0510030b10030b0a090201020a122f01050109020405010206310b090705040c0e040b1816032d0f 63
    0x81030300220030b560700018211949220b00c0d054680100f400121325440e1a0a26010907114128149002001011000031414680c081e17015206500f110460b00b94540c1c03005800702c0000030144030550654010141e0200d64031640d80210705012540301070511054860710020700040800801120103040c5042010000940d007480c002e000703501d40c89528083c0e0f421428032040c0f4501c060401c3e40014a8086480d0050b600401e0103071038244c001c9002d0b03c540442c0c1806884014600582d441c09044d075001605c0300100c0700b520041a047c1c0400200000c0e030300c0d0f0450f101203200d24002c95015a02c2840002c202d509410700c18051641031041d000c8200f60300200d40348846a038100125009000b00d070030400b40ca0030411001006000c115014051407010742806002490700300746150056841c1e0039036000741d07100c40ca64140011018019242a4a07240c02d082a02140301c80111000a003440c1ea862110048003000741d5008050840240b00181c0d4208400014140d850f0340058040c0c03102c0c03915180c40 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 970759703 1250 970758453 970758457
    0x8070215040221060a18120c03031b090e0a0603030c150f0c08060102160609050402070215030c0c0f0c010906050d0b0a081c020115050d1a2a071212020708 68
    0x4206840101013a04217004420182c0d090701050306541c10400080a010825400c4665000111030400190164003424104c2c06410748207007175110700118030b050034074480e40446a4000c60b000e01d04800c10710344400e50000c09451840c44003400140c0e903100c2210100c0c4031040445442004040005170301140c01111009640606074124003045030802009280e580500118074030303c3c42000c43c2003107942002c10251000c8024041d084c011607011a1600c21901d8808042203401000d49c401504e80ca0310441070300c003940c0030002210003801540c00c00081200d0010b60b41d41008016140c1200c400d041030001c0b9025040084c5446215031620541380325610fa0344294400303406020061f104074881041d042c0e032442030940d055400c681c501218440b010842454280a5450440d4100030715000741c100760080c00c004929103d040a080f070180002d4405408616200c04100030803003500c2c01101c8580403150041d180c003c1c285c48400680303210418801c1501710300c080b003501d40041c14046a900e82410799 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 970760953 1250 970759703 970759759
    0x1603081819080105060a0b070b0a020309030f040803210108060406180b0412030e160920032401110d08040c080d0c150203041203020a120203160f080702150402 70
    0x180d54130010301001d401e01c40400005031021188003403428420759214800d4450007000f18202076804004118401c805008075500124140a0f054407a51606481038895200000005882c000c1c0f818050169131680c02e0305040360342c444042c15450341d481c1c6540014100035031904083c0100030031880c0004020115041c080c0d402034200c00b202c158400006400c4810022150b0415441700380c0c10b014510b03801c1940c800342e50b402400850b02004c00c00301c1b00450460548204011003010041008410038a40b203a21900b80c04008110906005030055882a5658620f4001a00120950002c090252680e030750480e10480e0707400c07200e6540e5481746c0e0070005000b41c0440080c58002d03801041c0306101c40100009540780d0342c02c600e075003090b64580010541e0500e10600340750b00800c000c440b9500400c10036443c40344004d81550349203400208030302100c180140c1d89000c41d0f40e803222203405c41d02c10b40c41542304a4081d0001c007480b4059802084504400a000b2648011409030760303801035011003184814 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 970762203 1250 970760953 970760969
    0x50a0e07350c03010507050c0c0f0303040b041206061505030109051009020c010c090806010509070c110301020d060e150a0918050a0b07080c0702010f0503151503091603081819 77
    0x3000080b44105425243c0140069041010511100e225402e002c038507d012060102e90914044c4035030300c00719081d07000c2c59106000444010400144845203152450b081a100700002c02420352203148001c1031164a6202400040003800140480c6c5600d41c0102d810201440030150440d42d42d81014090740c2c006600300c0c40c181d45a00a0184468020392001c0c06000c7e800e000e001d2542c10500410320051009043d00304000301440c0800500003030b19945800500082c009543ea0084061810043c08041c0b04e0045241c4208001070306450390070300c048904581c000c190084e00b80c070303180b01a4040d0100a0002401149404807079001074401c00003134442a104214418192812113009021014010083c00503810b042100d0b00c0140e034850301101c1c5401c1c0714105681c40c0e0720340d4084060390340d107881c0540707400079068400e610030f640c502005544030300008000c5500052490203001c40c5900c480c440104105828000004000a828002e45041002814040400da103800c0c0e45151480c00d1303880501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 970763453 1250 970762203 970762213
    0x100509010f0f0b0d1220060103030f020c0a03030e04022506060605070f230a03030f110a021c030b2106010b03133e04050a0e0735 57
    0x85803a819018403054500c1d031290070800c5a2516000c40c2010304041d100a001d03104071040110621b02a05c03c0c245404102040c00c04c01500b414011035407004280801d5001c155014002461a840091007110050f8050800c641381407540e038041c0c40c0c1d2444400300e0740d406502844200441c00d8104020f80300c0c507000700048003024900741000421102543c2255041100400c02c03200400c103203000c00300040764404502040a24a880c5200c800c0d14990442070b00350181811307207000c1c980d064010343c9485844960401c043c50b40d255070700c2d800780305241c4100007603007040d001d00b0b031141c00c076040055044605050102c2c55011550000381a000048144120000000c0584c0c1800b001008200c0c050a031107401103241d400d002c20940c10400004c0c800400301c0001050082e28000550020f2180d590407040c41001d02156a6000384008210311616001d88e14041c005140541c1c41d00840c82d0b81c02490004d0041182085d050008110900d0740040d922500c00346588441080405050314503600b00000d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 970764703 1250 970763453 970763471
    0x513033c020c0f01080c22090903030b010f08070e0409060e01060602030d1104030b0f07030608060c04030b060603041220070b040311043e070f02030f060c0306060a0210050901 77
    0x11190310f0b50900c83c1040504c1007001403a1400300e0480e0034030540c02251854061a4409403d440c48142e080780e482d003828010108105500758211a030404001d0700c0d80a000b03c3c891000702c8201e0300c2120f01e4800100704240800306070800b51b1199601a000d84000704580420038211070941d103080d440f2000691000440d41c110b800c183c400c10207244090300480e80b40500e19100d01c0000d000c0604040b43d0464074502085505010342c0c0100001d00c1c00c2e070142c074010300d080c00714109140c01c184001d644528205000400e10701e0702c4011240300e144e020f0f0302550380f00c488200488107800071003007804440d0b481c1803e01402400410018004210000e0119034407400c5180c41c85580100800c0c56000d0360074140011580f40c2e01c840c0f200001c509407001300498254402d8a581030390740981d41914902c2c80051804140a20214642034080c0280d0480e900990088039042c4e6583c07040310031808a25080c00401d01515241c7d0051101000c140304464000120603001c400b01e580a94040d46140e54502280c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 970765953 1250 970764703 970764709
    0x615250209010806090a030e0111060f1803070503030c09180405030703030e0109050d0311130803090a080d0c0209040206120f0108070b120f0a06030506010312030513033c020c 77
    0x72a014081d00030242101d8244504020780e070301c00d2088002e0034001d281e030b8820708592091040607070840d1040200c46a074207000b45c3e0900e00311005e4030168000410780c1c4c0c951205da43d000089444440d40035008500d15034502c3e2610700903400101c040c65201e04c41080c42a04400e034809014040c9020710040c0d50385580d940b0740607045440420b0b01c00030356410b020b90100820390200e900d000702802e6060200b02062080c408448a108004807804061b64044000c140d110340040a0148001c06945407124251200005a951540c4142400018400b5446200107040c412551038015102a000f1418a600700030807620381a800c40e600c40000381804010402e0b034004100c03180c0102000703040546018010340e61003904140040c0050820310030200850070600305940000020354201c0e060310004c0d6164603040c501d08080c0c1026000081c1000c0110300311101d00c104006031950306450f04903400c504806043c40c003210300402d40c0c0340301c2104001141000300c1c204120303c4100555000c0c0102c071041c1010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 970767203 1250 970765953 970765969
    0x31803100e030304030807020f0708030c0c01020313030f020a030218040c0e1e060d170307020c0f060702041e061d010b040e0f040f020301111213020906152502 70
    0x1681031040e051010550400c1408800c60740c005806292000c455030303485009916000525900510030700c500e400005444002101505e0244c0b4050706488103403092800491b41c0b802003141310440e19151035002c00001b44d0003170010b1000b0384050302e42c144175540c03a000550f000c4520104d031107082503048104001c12294920041c0a420b82c0100c525150070f003102c01d848000e44004546500d4580c21020804540d6079078440740c40c0991002d2498014440c20803094000e0304141d5440300588030780c001000c601d25040769015131522018208606103001c68081001411081c40700c0606c21b0b1680c3d86d191809415801103c01400c0044040c020002c4201c1444641540503841000022000d00c01801240207007100140c110340c2100030006c03e40c68034101036903102210f648c003c2d4158070304500241348810410191240f0060703054200b546030b40301015030f0105054804029808000c0c1000103003d403826601d02985208080c01c1136041c209840d03d0741000c034002203010001b801d0180e840d1411480d005c20 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 970768453 1250 970767203 970767223
    0xf0503011820040e0a12080c0301061211130e01080c04090c0e19051608180a12030b0a030c0323211c09050f01180b09010e031803 57
    0x80d8141c9401500c40072848540b0000c888030411031000001c225994640110102d103401c8815601da143e0180b41035010b00b224805001c0105024000081e03c0c02c0056080c3c0b4100c07452500d60741c0c4542c0141c4003400003001e154040c88000d61090000040d01b040307200c1020301400100354207100035410048c005151015000c500e500c5281842092300c0040d035241240001c4410038000100f10b525241c1800205825040000c98201c0c0351008000300016a8100c3c085420969103540009480b402411080c82c001600001c06660050a5540c0010b141802007900c42c5401d10700060710003c9100080d0303600d8040d60043d0750314103403610140300b1701c0070b0081c0c55910141300d070300700a914940f10f000f40d503128000c0c00d2100c410b0082800e8441891614001100c21003011b044401c000c00311071054040003000950003c2e10f082c030503800b11500c0207034140b003010f68604601c81940310714091640c64660721840242044010754a418260304540b40400280811f11001e482255004001c103082c9407510102030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 970769703 1250 970768453 970768481
    0xb030309010c02060a02071203020a060b01111510050d05030903100501050a0605030405010207020a0e100609080705040e01020d05040b071b1505040201020109020a17070905060913050109020a0f050301 88
    0xd000342036a00b120b03040e10070b560305851041d1a50740080050f0300b0000c1940c000401307a051403542804141d80480c1d07664000d4858141001a06500801100c03000701004c4001c5a503480b2010b0480b103041c00c030088551102d40c56a4070aa81901c0b00085801c0744005a000c030740f42e51010031011014a014001c9503016a81c40c0000c1010350325010000c1d0010b00d0701c1c4141030030f11a0010215040c04000e40403180d000d17801902c40380c0c102e6569029500c50403000c440b030307480c45071280c40c0208049210310042012540c0c24070041503d5400e10381000b00401e101000b000043d0f40c00c0203a0310907000b140c007406104d640104403242e8949081400900707802d094104c07003403176104000c07141c03030000d030710001100c4c4103040707203000040c00e0b40e61840140d004105215001e0f500044055000038490f1245c1d80b000303030b00c00c42d41007a1418036558500361801c1c5e40c01610b8603507002410600082c0520641c0c00c1a4034018002d00021581c140c071138011a020603601d41080300c065541540c00e002c103050074003800001c0315400d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 970770953 1250 970769703 970769707
    0x603090519051e150f010302040b090c2b0e0d0906090501082d160e03010b0a15140d0c140702031b0a08190b090d081303050c030c01060302040b0303 65
    0x1d03640c1680340c407607001e4840c1c0d6051510f0b9040300c0b003220804c00011801c14034841e81801d41400600403010420900c002c92045081c018070401c2400c0c0a800c582c011074008200030b0424a080041400c100c0c024000c00c2031900e01c1c148502002c00c4035000300d010b013030344880241051400005005090b5022604000140205e4040802c200d036403014481e64400d0308900c0c21041d03000307141007000050f00c20708940401c2410680070f00c0385050410318000c0c0c10600030349038141c03141d0050f005d05003a1020000850f81c030551001e0200150a2900f0700108101707035030b00d0704c000c80c500c82c06017100803500900d03041d11003959245031841234540c000c10564154030b94808290309050b000c1d4000307640c3d039410040c6003000300d02e49080080c640e210b0704c0049015005800c281d88601002001c50104c141e1002002d59a800800022481039140400c070000a80815a145101584c912544550000e003003001142085020409050500014000340551180000000c5480c6245004000a44203100d480c0352180d081 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 970772203 1250 970770953 970771003
    0x3060a0b070b0415110703030b01021009050714011707110c01030e19020402040b040b0d060506030f0106080411040c020f16050d020118030618060f09020d1b0f06030905 74
    0x668840241c0c4950b1081c01d226040c925001d01c44040c1c2108031010b0443c0305c001c50000304260305034001c4462a9403e90071600c042d64154820340c2034503803405000d00a500405401e02035103840311200081a1010705081181c0c180d492150101c1e0305040342c444d0001403100356600c020708014404a00c04083c2481e050252400fa00d112544445144880c0b0b0840310a107002c5c10115105c0782c06440c010031841c4501a200d6a440d1090042a8400d02803901418500200400c81d0301d804800d590044607052440b20303a603820401c041d034054902030800e5840c0c1c901c4802c2803c280d9982d00554107500c0496010348628081004030b1841d11000c1a0000d030800501401400603464000c42907904d542c09103445000d0800c2410440d414080340d400180c0101d060a010803001d103903805001c01d800b842031400304580608054050200c0d484000002d40c010317811030410003c42d0b00c0c100c440342241345120119915580d54107203110490420351121000c00d864000c81d0043c841c0920051a801000301d268545080c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 970773453 1250 970772203 970772213
    0xc060f0507020108060108070e12010e160303081f08011d011515050a1206060503061206060a030f1b0e060f1203030103020103110d051f080a11040b0f1503060a0b07 72
    0x4c4024003042c100480f410010b146980309040ca104400390190003170320441e6030210050701910520f0710390003007803040840c90721010640b0071200081740d4050395100c00079210307400b02e0a0740316903003a0091818100400c002c0341c5020213200b186899950012400203101403074a029007529203040d4005510204000304110f10014558140c100150b986071481c0d644a00040c11385020350206030410303402d4500303c0040791040c0c104000b0341c000c200c2182c0c0035040e440d200b0110399075140c0440d483d44e00400403600802c00114144000865944280846859405041801d8920004a52140daa036114020a020190804119440d90400140c0d8900341c49001e1906850b40c0348418840281010398034681e4200c0142000305645e10101d540c0001d100324102110b0700c8003400400d1a0300c0108070200d540029020200003000b1020a6000655001a10344142004002e100701000150801d0512310310511382e581b003e80b04c01c0c0312100a842e1603101d0070600140b04441d2696002500c4843d004c0001c81c01040d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 970774703 1250 970773453 970773467
    0x5090907050a0c08190207054002130f1a070f020102010e0f070f060801081e0708100914010c0516030c0c180b04050c18060909040c060f05070201 64
    0x5107800c11075035400098200310740d0802e0030040580311450100d680100810b4014080d2145405682124078840e1540c0c10455000c043d0f0b524045d00e100701500c41c800c40b041c10441c1c80394600145020b0b01031003080709081c0069074050101500d260700041d1040c48400c00c081d0301c1b00d000c0c2c0000321840c0c7d600c200d141c80d0415039218506010b010020016521411603200750801c0c1c1a070030100301903a41200d1100324080c0d544486016042103101c2104001c42c25504c1403040504a42e4594002d0461848200084020f140448034036291800303151404284203601300180c9080101c00000058040041d06013000d401541301d901d904141d04100c1d04000302540134003503c182004242d10500b112240d443d068031030084c0100d00601d285915800010040480c0899143c1d480c060038040c00000303c40380c20042129011074400d1a0364a080c0840454030381c40110410954201a110b5840c04203110000f0b03d240700112011206c070031062006014180d0301c9860840342104a04245080680b15400030f4081 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 970775953 1250 970774703 970774711
    0x51f0f050402030421021005060117070804053d0615080a0902042c0604081c062102012709110d050f180c06122806050f01050909 57
    0x81c1c2d802102240500030055040e100c0c1d1501a203620482c51070444000e03485108140940c214a45040c00040b030550050440c00b0108028941080c811782c2c038150203480001000d0015a494456021500c0c01101005021030300c031603e0741003840c0c603514001020011102d03585580d1012a0a002007000411300c0603000d49048290390500200799942e0300141c4004008104000c0e41c001c0c1404066260308090880210541142504464030740b0039402d0607545c1d803401582c006060f094108402c820445004100100501c140c0c840800e00c5a87c0d8144143c5032041c0207603004403a40c285040b44115078002e00350b42404a1800084140301102068141c0d8008407031007415021a12038000350ba44880c18021641129401c0300d0070007440c00c0500d4a04004041110780611000344110504110400040e07505d00a05000b13000c0c9242c041003003050a800c0700081c14a001d01c24112403a900c00c03400c40e103440c003611054400000340c454601402c0111000c0f410900ca814003c0800c1303400d9140e200c4032141980 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 970777203 1250 970775953 970775959
    0x31502090127052107050f01030b0a14030f070b09060703030b0d06061818080c0a0f0f0b0c07030e040504080f0705010b0a1703030a050717010306051f0f05 68
    0x100d400e004016601c001502810b1070490b00c2c44028900c00d8461240800203541040d1410110b0156a010180311211441d15505295018003000c04c800d00e44415118034000040c5004103170650286d01280080901350060041032000c01070840a5007000c2115030702c9100743c1d100400c25946005100d10144c8181c11050b806400c001502c241894000e8100c80b10f507542c00740003101d450f400c0f410140020002400384407807110720b61064002401c1e0600070b044031b1500f28114018985403a54600751a0342c0b105003111201d00847e982117010450a920000070790303010344201c2101d00310b01d00d0042c50245005110310603611081c0031a001003607010744031011340c5005441c00180303a110750528a04c0d5004551170381b0041c2c10b0003d48401000010b4002c0c03031030a0000e441441c20240c5403145150381d0f40f41d4107051000c0d68800e200003008184290410360300440b860800e8001090f0701d03803000341c204100741c0040c0c950036154030a103d81c07461482582c9040070303004000c44c0bd040b03040000c40c0d5030001a45c803690748 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 970778453 1250 970777203 970777207
    0x36060f0c06060108011229090d0f030e100e1606020f060106091d0915150405100b03040b040f0203061014030c0102030a14310b1801030507050d0c08011509031502 71
    0x1801c0c10721211f1110b8030040c0c4055641442c50480103480e90b070b40d054041500014010030012891074020f0160544455480300501807403110109100014984900104014172034a000e040200014400403006040e03a6800381940741c001c804654500300c4107901c0700080041041040218403100d840c00b000d10308191034130803955103035042128508010700c1d51b0000404501d60034082d9917440c14600708009801610f05000030b50b00c1084000040c034241c801c40303201060820008000840714a0b015030f205200d1640c441c0101950307000700c1e261520072681561707108480329051103c407014000d024070b000402c50051030340d06100d1000035240e010700000d1105011a0500d091280c0c0300c05420340300440e40d955140c3c1904030810303110b458030080e0203113000c502d00b0310b0746000309175805500201c5482d130740b40840303600c0130741e05090044000700750042269003003007018804400c00c04514098603242c6680741c0d881d0041c0e54100200c2101520140014100380500f68104200295040e0318091a0390241c900040e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 970779703 1250 970778453 970778483
    0x43605100b04140f100914060d05071e0f0b0309120307021207150e0a0503040e0601090302040906050f0105010c0201080a0b0117070305010602070b36060f0c060601080112 75
    0x5400b03422903c10340440020741e141048420ba101c018501c1c4122414001848110360303442941084030a52030802c440c8502820016410b8109601e64003c01840f8408540d2030a40d202d0303010740f5200c0d944c9020303180e14002d59410401d00300c00709c180001401d2040d654515508181020503552800c800345044105d5000c000030792464001d001d40e80908180c800300c15581c84881c640090001d2a50000e100514500814a0207580b40000c10550844d03020000b1031400c0e081921404448600030005810800c1040001c8010380361801214102c42c800d82000c156400e01804c44940080d05070000e40c10021215110b0300540e07403212225801114604001035504000c41c0100d50741c0803603117210f440c2101000c0520166560681c4014100c54880e070135205416124001ca1090303109946400064003034500b80b000040c0d020103441c59a0320700c4114048150b00084000c228a0781003030004070443c100c0032070305008480080c81031aa1051092805804940c1481d140d02e5410485940250091503020800c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 970780953 1250 970779703 970779709
    0xf031a010804060204092301060c240f0c030207050d020d1d0612160306050604030201090e06030f0f28050307140a02030715020c15030a020f0702043605100b 69
    0x40c0c02030b003c00b400a107d54041104c048103034090205201c0503030720300c0d0b00c000100076104c2c0c0e040280f0303154080c100242400c01c9800b030301c41444400d031001503010307541d0032354030f030034040c0c51040350b890b105c0c540c03009a255141810b0482c1007030440400c1c0307801d541280081841441d84800490041075208001031450121200811200c0c069002d1942c2c1401c010740510910394212182810816440e560902413140c460080c0b02081c09644802404501c05610602036000c803800c0d0f80390320800180440d100e0000046055103040d0003903540c2c80083e080500b119921803034951581c1d16004460505200b1038400740d46240e071300c2c40f4482015000314044111014000c02c00c0c00350f02c9c6040c7e001411203040d162665100e1448c04c1048081201510a02a41910f11304005140310307104054034400c1d60130b507a603490403200603500200796003d0002d0f00300017920050f900c9210302100710b09564000a4000f040e0420b0409802c01e50942c0c0c06c429549501000010350300165141c140454090003040c1002e1322804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 970782203 1250 970780953 970780957
    0x509061c06020a091806080a0204180f06020a03060806010b0711190803041403011a01031104080f030a1b0b01030204021e0307020c092d0402060403140105070f031a0108040602 77
    0xc010100d5000242c00511142d02c08a820705440011500089030112501c02c202201c01c2da21591055400800c00103000d03290542c03080d804000c044409407001c4275540c1d20751442d10303043c00d02212150750218080711070591510812020307107680303001807040c1c3d410800c81084e64010300b64003c240080303891000700b29031501da450025021188201042040c1c0319a0420740360340003801504c060f85136141e00c81c020381c5814064524403455010300c41d410702119000441c06003407a121020981c11041000083c607103030070000401d03011942c03400385407103a100c00c0c0020088100c0c1c69400d945075505101620124904070300d410f044990444006941c0c1a064410000800b00402412a005804420004c4068002c50707005a281d004840e40203455458032820408080464500c88a901c0d41108044d4014162071030340d074000380020111818141d50b507071502a5441104002c40c00c80c0d4440082c4000e50b80c01203509182c00201d418103201141e41c8038140c9058000d00d51469041040300c202041c144000c07681 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 970783453 1250 970782203 970782259
    0x9010e1c2129030106060504050d052e0b060a1706011b030815010c05060c0a0201060b1b011d030f070807080406091508160e010309081926010515250302011401050906 73
    0x44400103000096001d075480cc41c1d1282212015420f08130703000d08a144c10001c503a84540141ca880502e03921802c03081e04045e00003130425040c40740d501100314a80072400440c1c4560b030f02c665607444186c42e10751445010714020568050500c070040900314001403000c41e65540c00812554210f0300d802c0030803000c07801740605a0200c50030030390014038441106070302c000d80c1c429212414001e02044e111800c003500c825903400d42e50a000d4009001d036105d41c149210041034400d0140c0e800301d0030803006807a40c5402d030703000c0d9000001040700c05408100c1a0714845c004180c0310046e041030719141c50288290b220300903041c880301c01003008000f4450402da01070380c004802140c0103400c00f03498020a0084030399000041d0819008103803443c03810640b1812130054a03040d5440180c02d401c99903e0401804801d1b08520300d49213003c10280080002c81030130f01c00c0b20b5580104044140c00b0018942406400c40d2008080d0482c01c0103c0001804907407100c241e101d4110320305aa41341c8504d10700e044000c1c00c07005a06 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 970784703 1250 970783453 970783483
    0x11010902060703030603053c0109060609060617040305092101060801020a0e060c10051e07051c05040c0302060327010509010e1c2129030106060504050d05 68
    0x800c0030b02c01e06502d41c0c00300060740d11032404c860104007a500d0110300c085098055040860040800e4480524a01d2009511007030320f000104030340480b991640700f680c1c501c7c3c124081d8141d407076504021542d800348584003034040c40c034210800e504140e18018607500c00d8019003070091040210001d4550040c41c10410001805002040001d0316199854081d6100342c0400f4006038140c1c0741040301c1e1410301c0c220f541d031402100003400050742c452141409000010281501400482582001d0302080b122051182003142d460a0391001e440c410080c3d503030800b617171100c0001c1c90002000000340704411182d041d25012991542c4980d078020306440b80310220b050b4a070315440700411002c0c9041c41508482c3c0078401140c020720102c00700c0c1010b1030366040001034010300042c00c0102600a240148025001006c4240181c00101d4143c003000083da10004109103070142c0001804580c50306801007d20001c0040340240b0006152500041450085018040c400c3c04032880312010800c00304800389650803c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 970785953 1250 970784703 970784707
    0x20a0504050910060917101503050a030807090b0306100e040f1a1008041e02131e05090c01051c06050d050601060210021207050a0e03100b1206070804031101090206 72
    0x3c4240207034080a10408020a0000300007040894409400c40007903182400100720107411828100c01800e1003510b003c1820348000c0c008070120350140083c0c1c881078025200c0700640e090001c802440c00da00b691140742e11a0017401407158582d1401c00c420700c104c6c038601e4950603140100e40010010841039842041e9a440c00c80c042074421540d1441c26800c5c04103d4909840080605056800700d20031140100b0425a0011420003900201d8003440b42034000703032045060030302203001081107461510107034640000300034043c2529200381c000e1503072250240b00505403c01800d000600240240180c40050140250710948801c04c85d44c4110f00900008000480440d0241030858644d60b0a0050000500804800d003247d01c010303000720340b456000f0300b4010000ea651523004441d150441c0716824200079803e60f01000998040000300100703201d4403800a0a9141c0c1e40410a0300c401003217507541541c01c03000401403415046030300321364000d8040c1011010011410303951030040c02040e40c000c1d888500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 970787203 1250 970785953 970785961
    0x312020310180b01080606030702030306190509010b12060111060c2206030506100906020706052805090a090911040b030304080303071707081b0a030e070311151804020a05040509 78
    0xe40160f200b060080c0c072415820344802c020f000c101d1204031406400b5034810000304d81c6a04001e410a6803441e2240d80b007140c00f94036680002c030240c0c004c0e40000c405581c0441d161120a0b41c9150280d0445002d0a1002440b0300c9804401d45851004081e5102040c011800720b40f9011004244141045465100c401b003036116040940108402c0e50150300503414842c4e0040c07058096044030742600c2040d002001c0461a0100488040d0321100042e142c03560391616600504085201d0410641055121107458201420038010b04a000d58000c1015500b0040100301150364601540b543c02816036010407501e8280010928500c00e40d4400102c1b444000308210301c5690054802c11243c4038014966900d4484001c100d44075181500d84910b94200214551400f005400050060020504010a00d000d008400d41d040901d15802a103404d17082011805462030102c810480046407400f0242c203090354080c62103601403039402c07500c1c0140e5000624041d4180524147e030000c0c43d0043c8014441d10f8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 970788453 1250 970787203 970787249
    0x81303080f1e041805040f0b070903020f1e131103130309170c0d1b0b1908071e0c0b0a1406091524071a01120312020310 53
    0x121a07041941c140c000c0b590448a141c03041c200b142c003201c612481640310394034102031002c010f203c09003084410b4501402e280e000152500381e030612607202d0ba22120191481c60061006007203149103540c0c030032225011100d040c0c0d20030704450704181400703442c80c95500400d1039401b402082c0e1031401e01d044c01d601004216140000040440c100ca200780d641094141d80d50003d041e01d41c3c045208141c0355000400c036410701d4241402000c0e01d0500135041d038083d4050340c40280000c000c254103c0c901e00c132000076a99000b00b80c013022801025030240307010701c400d1034140300091454a8118005400d4010f42080429140c400c00c020b104031900300a40510500380f104401c4010503007500381c0342920100c070001a5844c40c0c40e17076059100360144103684284c04480340411540b50925030000340c41c440e024502840004c1201d024003069032040d0510501030043c0380303d000b920b040503440809a040c0c02d10301400002e5001406ea60318814082c4096102d0301c404440710780409240c0c016440c0480034600410740343c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 970789703 1250 970788453 970788457
    0xc0607140f012f0f04090b040b04050a0209120a0302060613021908190912110304030c080c0109170c040c0e032a01050301030b1503030409050915010b09030a081303080f 74
    0x2c10704482c00d001492040c3c0880381d030b40076145080c44100c030240020030036040550060004000020000980383e5076190000c0c00311030060703c820391003070340c003242d100c2903401d203c030780000c1c84503110004005421560350002d40c0c03030070028081c60142240d081c407003500c5000e60b01030720b842c1c820701440740c50304c80c8169500500c0079000300d0f22850301c601541c0842044d103450b4400c041c056034002e10705001c1d401e0890029030384181d110700441d009110802000001c2081c00c00f00b50f024100c0e020203080c400070040001403125901380c0000d485407805105a444000002503501100e0300241e41c0450020103011055424000e0080d01e0764142c054090384900891002031100c02502c0b204440c68100705041c001142c285c00240802403042c0340b8803000c50052007a18a00c142c0b00c10300281124a00381d140c4154506580c0e0a40f90389031164060403c0e0b000f1501509452405441101001c2e401c014480002981c0e81e88082c20140c0040000a030014103142d42c060000b010703641141c0d0040c1d0304e402800000703500d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 970790953 1250 970789703 970789751
    0xf020f150714071109060109050405090a14060907030b04060f0507120507030b09010b0904020708041e0909110d2108010e0a06060f14090d060209030f0c0607140f01 72
    0x20300e40380c40c1125002104000da5900540105506803200f84c0c0000340320740c070320003e00f0550503c0024030001945030b6a5000c0c0500c151000005803201a00394500070b131400e9517280300c44045410900070409689000240b090443c2d80162661110340c8450410ac0028000030740034505c2c2c68103007401c000c142e5405c02d00340034040c000c0d42401c00060707840100c02c80c00ca40c11005040e501160a400410180d9905406000e0714800204014500a069a5000d070305521640c000e0351140d0111181d01d07660a12550b100c1d009180320300d401e02c00c61030f507940e801c403542c00c0f0050324511600c00001c680c828001d80040942059214125541c44140101800b405001092155080045c440000203002c0440c6008810840d580d07920b801c45c88000003031050341c100301464009691504184201c0c1c40c40c5d92072480303144105000c1d00f4011382d0390001780141030030082c9906240c501f82d8030940282000351507280846088a0700403d4140060305c003880c01a00700746603404415019802d09006a08100c616400c100d2030f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 970792203 1250 970790953 970790957
    0x14030405010915061203110313121a1006110a0c060c14010b0d02060c030d0f0b09090d051602010203160803060306070216060509030f010606020d140702100f020f1507 73
    0x200c02180c0e5103070041d12100e0103180b031740381c2c410f0400c0d60000b800b83d212220101d86240c140c030f041c40b040c03020103a6203507090351244818090440c3d0f80d005001014084469091f455200140f036841c18552412600001e882000c0c10009100a080c003800424400001035650101c07071300718601da40f00d07001001d20b00d0481b800d60b1041029140f00500314414856003d0640b0b02402410340c1c040b1b29020003110350007100b1145a80d00042005000c00e00c614829400d441e400042e0010360741c07550034180018080001d00740340d00781e4401d69884143c550054203030391030640d400841201481075480100c0c00c5015070000c0c00304500203810302d081001003550207180710b0201901290304d941e68002e8200d03501e42c0e6294420b0710220100c0c8041c0907151107103006242200c8050b0854014018510400b0b007120840d5004100581040c681c04907105c0d4400894105c100e141010b46003483c0b0035400154114908140d901c0900c40c4441300c03004203900178055110b103200680180d0f0031000740007a020450800459074600 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 970793453 1250 970792203 970792223
    0x506070306080a0b0606090d21030c17010b0a0311120405010b0114031f120b070306141c0620040f0605070b1f08010c051c11071101140304050109 64
    0x25101c200184080c9119000320044003130307458101c01d000665005600703040e048070b2003102141c08200152078035109103c0c1c2410316241400d01781c00c000d045800302084401000680f07140d82c003061401c8407451341940d6400b0f4071150b4605402200b900203001d00f601100380341e0408961038040c4142500c20754071440c000e00c000e1091920940044681301d181102143c0302402c00e01c042801b401620407411458086111400c02417501e4007007061420071031080c04c80c0c0c070542d03d01c01c10100f19418001c03d001088010b18115441c0720040016642c43c014601d24288241c20507151f5051008540100700552048103010456140036111030b140c6034080e0040307225281d025880000d40c140714030200d5a52680090614140b501c0303400038400b0f04013600000c0b0400e210b00003000b0941010a2040884580c02ca890b00d030750324164070b414240140b680c04a07078a001c40c0780071805005602c81e541260b180070f034440d2448000703030200f00040e50265001c00300d01d518900080700f0031080080541c020a0100d0142000c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 970794703 1250 970793453 970793459
    0x30e1519060609030b0a06030f1103010b01181a0d0c0c0b0912040b0d09060c090806091c05160503040e0702061f1202060903010504030207032a06050d0b030a0506070306 74
    0x80180d070054401c40e030002c0c40d0650200040707000c03100d1003900a0361419011807490341c0c80e111050212032200c0282c0719424585408655441d00b48521402d4090a003004496112040c070304408111481c81042e0007180700303810b44000c1710b032440202e0f880c055040c0e004104811049200601c100c80000c0c041b10b14401d1140441c1d0703408030000f520402081c3e00104580f078282441c03440901604102703604401e164440403010300080c4103003c0c58031822141e80d540b144480c9401e80c4a480c00340050304585460b00020a08496070101a03c10307000714145040140c0e880403210104030511460110151484c0070100e800300d10341490300c0c401802595194201c9032282c41e2120707601543d041d41c030302d8a2031f00000030354100b00d5031510426540d42c00340014003003800e0180420200e82924004c80301107006810010f001d004100d43d031a048840321040e123080c8603948440d14034200b40711800380190002d210000c030f41451111031a41000406410140c01d07110b0a010b90324041e9559001aa601c1c0b021a040142c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 970795953 1250 970794703 970794751
    0x80d08010f080304260d03050a1802030303070c210309061407020d110703020d0c08060702031801082511010e0109080d0515030708032503080610030e15 67
    0x9000e440d04503020b0f514145c505138540106100c100e440700140303a031125a4558070b003002d20540440d14070b907442c0410341d4a0540b5102c002c548544016000c44503003881c00402680b800010390f9401704060070710140000b0389040088071001304182201c840e0404018a0941c0e0317505404c080b08542c0704030414044103080c0c64040c030b1504000c4032140c005a100d5003919221522513040ca41c00e0820b0301c0141e40702591030381c012030806021800280c032045014a020840507000704200c0d50301078903510141d800c02d0500084040031000080c481030400500c030001c1086031940594420092001d48140103001031030103000703030400103070112070402946032408060340c41c401030040403c110342c0081c04074038013000b000c0d040c402080302901220842c2d194100c0b40246403420801c0c070b005049244001c50700e5280380c0d40c1030510080c5051405019180603642c3c3c0740025001400c490704107400300e580070509102048110010300b65941042400d104040c1c03006034803180c6001440c0180b08201150750501e50f81500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 970797203 1250 970795953 970795979
    0x30d0c0501050f0c0d1e0608010e16031709011713060c020610031b03020a171204030804180b0306011e0b03071709032b05063f0601080d0801 62
    0x30400380e10401c02170090800c00326804860710b824112801841d440000d41c1c601c1c03c403503640d044988540c0d560044c1d907458410800c0701d03860503501c201003c0790007800c50b500e0740c800c1d03400c44881112004020641d010035a0007800c407003c5001d0300c40518081c40c504402200c03c00031000109a81541c41c20a1807036103d0701c0401c0507440b403000c6441340c0b001d06245645c1c1444004035080000c1a07403a409034003100695402004800410501039103000110b1405034040c20f02da80050340b20170b006000c1104000140c854015181154165181c120000d62402e820101801d00700041540c1800740400210380021208907454a00c1c50040c400c00c1d00e5071f2581c0b580340c1180300582e100300200340c62000c80c1140780060940f02d58001d000d101a281008002c1e54005417040200382c840420301f038031440940c080b4071a4460140e0182d4112024401a440030766008a801303c4100b030806520342000080c804c0310b0941c11074079a101850411200ea03583c0d50801d403500c9071078540d08440010b41c120000989000050302e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 970798453 1250 970797203 970797211
    0x90305040e1e072601030804031e02010c02040c2102040f05040515040e030c0109060b090a02070308010902090d0b10081c02070521010203180c030f030f1305030d0c0501050f 76
    0x10345030625403180c241c240c4088222010300542c180b00c048131000d5142088644900852040711815115030035480d20b800806408400b007410010901c1801d40581e0380001c0c4031280b44d030141c900148200399150100c50744d6000f41603010141c1c8070381115401c1103819070300400440324442841c480141d2584200000d0303904c159280c095a0f42c812080c85001c1c502079010142c14100081100d10b000d08001040d400e64061100544203159a01c0100255003090721109510419501c8110729000301950b021307046001c1801200c0d6043d5012806007000c0e2580806180b0254202092080919040c2c0e100e00303102d5011f02404189002c0c072003c0f9840385002c3d41d010300e1144d8494010f07141d02400c0c0000d0000f02c00d041a42c002210200710390703140e00414280300440c020401d1010b40203440b107111206603e007403003001040f40a6803003455403d1400e00081700b034030000d00d0866102952000300c01c2d04030316500301c141c00c040da044c000d26204030031b410b0f000074a0402c1e143c440c0f0001d210640ea22060325080c40800c032 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 970799703 1250 970798453 970798501
    0x109020d1101021e071a210c0c0f0a12080108070b09010201110d090515190207060e0d02160b0a1d041b0e01090e01082e090305040e 58
    0x4100d000569241c4040c03010700410310407640d140340c07000e080d44038007414200102e5841c0c101c100c0031b00080c0751100100f40031a514561903860401840d10250910119080c2d0b54140b145032404254902c401d2002c8a00445030041212064860018116120112250211030b03031042940f82003520781c02000814106c4403220058003045150030120310060f44191076540c119541e41d1182c110360b50700c000140a040074002e400051761981d40c0f07081494250550158403c20780402c1c00c000071208888401003c4200b42c0d41302603240d02d114074121014200e804003955581c001c5440b0030000d01d600240e440d44a400d2011000d02195a60501d001c1600c1840c0500b03001400350610f032080131303084800724003034800d0203480010002c03030341041c0c2041302c0d05800070900001c006c41100301c019039101c0000c1024203081100031a603949000c1c1c1e1a07a540c100811021004000d010005000b040f02c91480300040340800d509000c17404151500a0082e486800b5501001c43c070440030802081412840c800080c40d03c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 970800953 1250 970799703 970799719
    0xc020c10140703020c09010308180118060f020a0602040801050906100f0b0919090b1207050a030b0c070b09030918090705060d0605060f031e13030f050408010e1509010902 75
    0x6103910381c107076602241d030a0b4203503c00c40d500985e43c0d03181d40b20b181e8000c42c05019070f15241d0801a058100c000040614a41000300c40400060f00c00800c64440c0d044401d1801d101c50b0f032003802d04086c2d080c15441c0b40058012840401c002a1207441034100c03910943d0b00c0004d540340d5a845255032900541140504850480490814407040c0703440030040c1048100189869403a034402003c802005000f9006042c64503210040c816550400040700ca02040c0c800c8082d2295a060a000c900008100e106c068002443c500118582020200880f84015001820003040385082d409407a503c5d4401e02c00c09003d21602a0750100c401c20342814a8003070103c40008d085074920304410001e8a41169100c0c8071040c2d960a40012650f45540040c0895554007003070580741c0c5000d400a0f80c03091210301d95000300031300d00c500304103490030009112004070745d1605000c210348104507003ca8150007140c0141c0f038507610f00f0022031818040000c40707031000110301400030055560185000d00f0303600a010000d40081785 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 970802203 1250 970800953 970800977
    0x40905070f05120a020c1f1d15150307140114040617060f0429101e02031b0a06050901150303120908030c0403050708071d1017010c020c10 61
    0x1c00d0303d4240c011207105805030070880c209081e9402d0964040546048890800020084003a14007504100e8002e1588007080c0c1d900000c41e942d2250305000c0381e540c000000b18001105114094001c007080035001d41114050341c0c031110042c055818000c5014082403801701c00c481984e504804440c06d68501d580c94a01005400145803c445d0003d0840b0358054046655002d80c2c0e00e6502c42c0001444860354218901c7c0f110304461066820b03d80d000c01e015070101007003c00c805402c524941030b05580302d2004a420085c00c0030407421402224840e140c0712010700b542c08011900000e6031404c0d03038040d800400035925141083d42c02c07180c10681104200703080c4202000845d01410341007840c40000000442c20040340e030340301055640b00300d03112000f00101180520900070208001d1002c3c0001000074012242041a04106850040c40e000c102d0aa6040050071841c40d518a05008100d038032408000c0040030f0313007087d01824603042214010321420f4040d60803490500c03007410407602c2e6610b400030301c492 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 970803453 1250 970802203 970802227
    0xf070c0210090b13090b0312040308181c03170103050c0d0302030d0c0203040f0e09100e0a170a030b03070e07030e190507051e010e090604090b0c040905070f05 70
    0x800c0030401c01070114403603002400351900c00c0100108610707240150b580e14241526601105c56122416010380d0141000304207201e18002101c050ba40c1020380e05456209070f5000410103101901d02540041040800307120142c090400718a045209840d040d10f8000c260a002d18041000d00c00038200750b200349010079181c202280000c0320903000788180c03490002c1070072094054495041248c00160b0000400300f2079202070200510180c075070300c0300c2c14415041c80b4203006e5035201c94440704206e240c0d07140c80d8110032560400c42d5140351070b40a1240750003072420b4400c045e01c1da00402c02e4140401d0810b491019079148c041081d00958078800d0444d010303602c403000300310020421014000e000b449004048055100c40c50318280d4498822030003041d001d070800c0184072010311041410941d10740c80d02c04008140c0e07004a40300040b40029511407603540c3d110340004002d405c0d4801c002c1c01307461440c8180014068581d000344181d908100c800e210079128007008035480190024032000154041c4907101c0035403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 970804703 1250 970803453 970803469
    0x60f0d03030b010c0501050f15030d050a030510080604030c02090604090302061302061b03031608090613030216060e030606090c070b27010c0207090507052b1806050f070c02 76
    0xb0603d0401c034040f0701a030b9980c0c2100e40c10b550f81c1d251001e50740c041040017241840d0b5084c8001c403e901606050b100030201a00380d0181072541130505454000081d5041c450000d00002004103104845141c01c29040281c0b1582c5d440c00305074056800c0000142ca41e0802d8000c0c0d56060750306900901266a03003410030320b1035119401c42240d02100820101420410090110030030011890280da5281050300032001e103500d00c40f1010b000c1c03000003005c0007004100498900d602140054140703c0102242c5812400c190b50a0000d00000020900c013250440e070240c910400e01105804880c5103440346c03410456800c2040300d00c040c808104000300000200180c851640042000c215000d64515508560003801c5603040d00c078046039541e0350100300d0503904000010003000b00c65000c210034200540d0040c0070344602025440350101511408200e0380c250804241138180c0d0050802000c6080c0c800c051541c01c41200c00da074518281004100024502202680141d26039210b01d0800415642030101c60 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 970805953 1250 970804703 970804721
    0x16020d0f0e130c050309010c0f0c030c170a0e0109050303070b0711030906120702060f060604050105220f0e01080114013506061002030c340b030f060f0d0303 69
    0x10820030010102c001c0b500d405160715000d041d460b038a440c1d260141c1c015084074406500c82041005542c1000c200e650010110302c100c1c0c1d018506060105040d00b0303d07000303204440480b00340d0070400254824625a0140c40400d8041c0241e035004a400d039078000f05a40c90140d1640034111801000c0481da04074090b810007403510006070260381c200300c1d45070001410f6400c880035504004007000d08001000da418004036502c249401c2102c403050801c880824a58040c178003555040c4a0001240d031440c01c810b503440b10729610740300100a50f880d2900c840710800c80305849525a0340c1c01d03000010583c540103008266010056080d401d000f61700c3d0410702c00800d0a242c0901156140b082540030301c0c0c050342041414060708200c01056030742043c505220043c802c081da07100c1150400d002e030901c50b260116004500030351203100604824006580725000030002020710b082c01d078919000040d01880d40014600c0303021034248003204d9070b0303540003070040344041c0102d0250300040070b04c040e2000030b0081d2700040034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 970807203 1250 970805953 970805959
    0x1030e0703050607090306141b160f080a140c060a0218030d031b1403131a07080910050405030912030f0f040305060a0b031005040f020d060516020d0f0e 67
    0xc0140c0c0ca4807014185101590700400045400205006004090141000d08900e030421078000d807901c44507440c4090114600c8a0354190001031136034000074814992451503410015100344009240340805581d1700240000c00070a1202003050805d03060802521848444800504203d5880b915840000d41c0000b010080c00b0741c2c0402582f2a80d141044100b002134160b0f20f000803151400400503180307001c1200708404100c00c0222078420301500000340c0e44c100c500c280b41015540300300e150940002c188008c421402d0070101c000c11180540c4161114014600c11059034040c21001100c441038903011240944250320030040d808940c101080312130703001e400b000c05032030030401400701c6441541e106071003070508403201080034400d000c4280324168002040800c00c2041d40c10b098003180c2c6920b404940390804554a1000070305018854581482490740100030b0280d840d42445c0240c0144015a040b141030403607a00c543c00110b00019000a40000740e03291405292681c0c0022141e2282404503550 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 970808453 1250 970807203 970807213
    0x2040f06020102091e0a0303081803070503030712092307050303132c0414070b2808060108180109080a0305061504030f0f030c1b05150408030901030e 66
    0x20220616200100541803941c000360781d07080ca510810406220b000d00240020500340c02ca240c1c2d60340d0300d0001d40700b201d90608043e2240e41d02c807565a2404a4408903144075404001000d800b0070101000541c49000705490300c000c002009050b0804031142400000c0c0500494059062010300704c0008000b20014102101c850603103c1c1c0109056402c4038819410701c00c1c01e41024080c000d800108040c14090b003182c403249121081c02e080c40703105005440035040d6081c07a580c0c101341d1442888502c0c0900b00350301d03c640e03882031004c0c0c0748160034104a00d21020301c411000d1044000c0d10800b07450f03000390f10581d141c40f540e884440800e440b03001d020780c4a032400d41d030381c0aa240010310144050304001e0503a480000d040d1502c80140010400c40b56001685400100820b01c0001d5050300390740380e01768200c804c02003162124a03043c2e6205c00c0d0440c0180041c4ae0042c1a544101821482c00054031740654036010781614190b031222050003207014480043d0000c0c4416509075200381d00c40003d203a40441155 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 970809703 1250 970808453 970808459
    0x30412021207032405160e1306030803040b0a020c0c0603270d082503020315131d030a080f25030510051507023c030d02011407120204 59
    0x42d01e00003980d40210b032084460f424003000074900149507481912144014801c0d03152403a40058003424000c03108092020071000c0c0d9240c0d4a40c00e607408006588500100103403034881c103080c1c00e00c0e001194200c0b0425024000948402c00600a88008059a000910344241c0711001c114213074200400c584807440318040180c2c0c425080c0b44d150504031440d0070241442c140b41140c01050403c0c0100490300000185e90202c0b812440c040150007140c24925005840303459512030043c04260368400198040c075802c00114070030030b0960281c01608a9500c8885c080d5155140d0241c40c1c0c003c030400c00c400304071341a00190f01c0b12000d0200b940d000300f19004851a12529850faa90b03044208621040066034600401030755051201941e4040d040456420240c1140b0174503800d0070303100e042c000038069403030b15205084148a044800004181100b0a5103045600c0c07030941c40c1010780408094481e10030030480080c500c0c01071040c03c40000e01026000319540e15110141c81581100d281c0c5188190300300000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 970810953 1250 970809703 970809739
    0x1b12010603081801090f0605030a02091002030c1b060f180405040f0c0f0b0307120906110c060f0906060d0503070206130501121a0f0d0c0f1806060203041202 69
    0x44000c1c61040d14841d440c1c018121220605041c3c00c0c1c0c9407418000c0a01043c010b1010258070305044420610709141e0704e544d908900b0010b07024402040340c01901044036000125004005441c02d8410041260b190400345130f15042c000009044254005c50100721042a480021b402041005500150a2040141a004242214422070b002d030703405502000500d040010a015003001001c60001c621135032800c2c0303a0343c2405840003810f01e6003402855105550100c0c80c83d007200c01f10a07040310341049000344554900d0f0f529403220811481c01e01075500069008024486003500941c9001c0042c0019540c1d0400d001c2d0402c03030400c0036102c40c030051048030016a108001000c0d6000c91840110006203000000740003020b14100d00140c550801d11144891075008168002d90304c4203c9094400c4000000071441030403070864083d102c1c00755410081000e80c803002200d0102c800303c00303044d01600407d004410441e500c0b4060b140c010780041000f0403541d940b00c002107000ea40000c1200701042040741079 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 970812203 1250 970810953 970810961
    0xf0909020d0209131509020f060705190c150201060b0702040b060f04080a110f030a0215070c0b090307060507030f0f03060509070206090d050a21061d15010c02031b1201 74
    0x13209040c410b10b038800d410031154415003240c00001c1d000134440c0c082e4650000d052905405c0006000c1e42010506006210080010036148008090344e42c98040e26402c0c0b4480c000c656004014070b046c4400150311886105206070003c8403039844020313081c04440c0c0d0802014100d68500b030741c0c1c00354080c401902094203020003800288800f800510380c100302460220340003221030300704921420040428050b0740d01d0125544034a117a0483d0f10b18101803251424030118010a00301a10050080f0302c0490300454810080030080c204a003180d030425981c21045030240b04004c00140003807405050041600d0142a01d80700b800c03030604004c5a1a80c880011a0482c0720032240d101c0107034808400d012035941c003800200c0c0c118400f460910b1404100c0000580303001c0c01e190840d98a01d00d961401f21038103009500c65000381000c2804a41150984016075001c9101600d61342022401090643c180c1e40c090755602000641c0a0047c2c40d0030842400d280d40114504020150004004407603200301c8042031107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 970813453 1250 970812203 970812211
    0x5011a030a052a1509030106050f060d1116060902150913020c01060320040c031104121103010606020616170a0513020301050a06060e06030c1b21220f0909020d0209 72
    0x199925807400401b00350a503503155200c00d0058141082d45449500e4010444642030450b80c400304004c10101c10008041c03060039500c4a02640b03910f0450304001080c3c01c1856401c0c021250724440a001c14006511445420b01d03213a41300d100c40303803284d20081c410b40142c00c2900c20700c00005903c1e6034075107407001c00d001400328240000344249c0c0d943c552480d040c460203104041e540f0f810032014804080082d094030a50248050b0751f005038040038204042d01c1c90510801c2e202500a2101565070034003c0c0d0307147e1058802c40c0e10301c0c1095020040c8540710f580e03403004074009881d100540c0e482c0c2030024001054054104020350b2104044540507072400d0241c0c2d802032074011000151540780080007400c5e690f40c00c00d0288210020024004c0c080e010106542c1b84108400390311303619600700c85c00c0c24906810140718420070202500c250718560400c2000c4c142d100348103030140281c1c501065480e030442e46a80951318a181014005215000490740700d00e40c081c0c40030308840031204190300090303a00c0d4001c41d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 970814703 1250 970813453 970813489
    0xe2803170a0e0f06010501122d05071409030d0f0c0c06020705031905060f06011808060106030f0903320316020706021501092705011a030a052a 63
    0x2c81c0740d4910041088032a40d50b14244002d04829414040020100035070403840844098980303036182140c401920304036045807030b00c44030700c015445122203100207001c00701d03200310101e6008060709010b91840c0d412030306c01e0b9000502030141c000352440140d641c100703002c1c1000c00b007095888101d0001035100c100b03840607107569001000894907007010145031803181070716110040b00f45020a40001c4000030111303000035010304a04156610400101c5003141121001c0720540c20012000524020124105040c2ea22503901849840121014881601c0b1203010080009090461060004885508a500303c0c0102c00d80d9120068607500c0c00c03d02a0400d0702c580b01c031101e020746081c0100d0340410403c4010042800506985c094182962000c258144203010040d42c90705c4032204654042020b40031130a0384262410546181824001e00a216030681003040c0504445a01003501d00054541c01c00c503440001040c40c10010703c0e28040401c1070b2000c210111003041c03160718003591001203658040c0c07040307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 970815953 1250 970814703 970814711
    0x71b1a0421020324010f0f0e0606190504080c0d0b1513060305010b36090703151410143f0d030c080606091f09090e2803170a 55
    0x40004d48480740d40690020b254043c60ba44100000e00300011280c0c12582e0244481e01c0326600c807008202070307108055420510b80355001441c40b22942001c00350095901107411100c04503840c0d000c3c80580403d070a000f400741074102000890f25103c108031114048406065841a20061100c82c0c0a03a0400c0d0000c48850b511101049414205222001e1150a0100b030040c2042c11404001485c83c200070f115014030820840000d0400804000c05002147e20040014004840030303058401007010300901081d448070840490783c00b0070740281031001c0c0d41945805080c000289010841c440c40715070701c41d80700000d0842010b104030354103501080c0000c10068030b20064007a0743d0410341c04c0c40300c0c142d07801080c0340c41c10070480c0380264001e04084c2d2007038055034416a211600800a010b40000746603645001d00c81441414045038090700110031155110028051811822211a210050360300000004140403610701c003589804003902e0030300d60090810002881c0700b10345030845107000f01c460b00b401a480f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 970817203 1250 970815953 970816003
    0x140a03060f0f050f04211815020c01030c05041511060711060703150b09220c0905040e0c0607081b0114090a1101140f071b1a04210203 59
    0x9074000c684d03106140d010400003174900341c0d80d03180108113051500030748000b40c103006048150141030a00500e44c006800881c46503aa11405071004580c658828014010340003030780803c0d4020300072001030382c4c02c07900d80304e0810b030412080d400b8010b44094100e041003128450712503194410f10443c2d018083d95078540b108400e0102183d80f40542c064008410145050011015541e0190340c000980d01e003e01c0e5599281da41e81d001903c8004546640310303100c1d4140d1840c0c1d14440042c0e101e0701c8003032080e440741400c0c10b030380d42d00b000129040450400c41035044298022080e15160b001441820312900300c690070050704c110240600400142030342d200340e40d11590720f032001c01d00c80c05181c3e205841e000202103a820681c0c81070f003c00010389100c0d044c4413200901a24965910003925503019500d0006a15149541040f0783d1a55560800da404500c20b06404285021400c03071254440164010f4141307010301e40781200c914010100c081c402e2401d40315040c0c0340142e809110070b11451078a008035000359a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 970818453 1250 970817203 970817231
    0x61206020c011d03090906151803100908180d0c060315050406060f0c060b1c06060b091c08120a05061e1e0f0a15020105010608040c140a03060f 63
    0x2021251100341c0f00c8401a03011000c3e4400022140140350543e10510552210b4002c500380d03000c0d9102d000c1c030107840407441003160f45205602d4103600c0e808030100c0300c82241d0902d040044521340500a401404d0400030900001c0404011100c41c0c00054480000c440f0188c8518607032503030507041180042e40b0703a40c1c104108040609402c001d000215010088a86015400b809581034031030b4281c240f0103c0400c94041c000d0302c0d408400c00030005092121a03d03036882c40c00002d40101d4400b115011300d480b50104d1040c13400d5090710540c0c40003030485200c02c2e01702c80c40071010b0f02d04000100d5403550b0400ca018000765607006071500450400c1e8010810741080306c03c014440b016400ca03040700c407907403400f07580041c2e40d00c0c0c400c04180d600c0c80d40720007510300c4041c010a100107415560704d9088400da000008803059180e42c0741c030360038240d40d00811150741c03170310301c22200d4400079540036008030390001082c0a0058054080e40128070000c161100c866a6a80c6007400c3e90400300e02960b4042da524080702400f1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 970819703 1250 970818453 970818461
    0x2a080a05061f08060415060509190e1f260d03050601050f18040207140610060903020918060a06080c010804080d090c0306021305100e0d060c03061206020c01 69
    0x420121000c01c1c1c2c4002c01c2030700407998020031840408001000300400c2c1075880f41d82c0461051281d91142c140c80a49404020700103521411200d4018185003074840703580c4d1640114042952031b80300b5045110f2303c9a0703011010003250340380e2031003e9050001e0000360006501c0312101c5650f60072040c1c4200c821300e11a0040c10708101151110505091004101050780d0050440d08a2054000c403030391604218245000103000d4110300a030130900c005080c6090000c0c04d000741c203078100da95040325101e03a03032507c2d0078420100c0751240c0404200d41e640140014901101c2d4140d020300f240d1014413000c504148090300e0300505480f00095150380c1c4c41c00340103000c0c040c8043d80003c1e4017800d009010703003020b6450000302d124421405030701c1da9075010494100b0181c0a00c00000719000182503455000304225100445413038451184140f18034401070190741d01a015440011100403d00c065080140c0c0307484002d003403082080c4040607900c030b50200701301041040c291070311800345000507195402d203038041c1d00311 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 970820953 1250 970819703 970819711
    0xf120a090b0117070510020c031015080a0f060b12010c0c05240406091713050414040819030b060403230a05030406031512060c020d0e10032a080a05 65
    0x46900b0811122545400284907130440e0825159004800002e43c8100e0070942c203542d14a51501070f84140034440c01c05a0011f00c1a2416060111203241d0b680c1c10b182c0d40c48061460080c000d0241071010808200035a0010040381c4010302207086a113500c42d40142101e0780c0b03c81d060046148400810203210041003031401c055130001160b044000c03400d070342141c0d09800600c010300c0390381c031380b8003903420012904503070f0000002c00111561a8010303121055440310260250034002c51900c007030540c40d00021001c0900680d00198090700e0901010b110030315805054500b01e06141c0c4070100141c098036124014030045000d1104100d01c18104411b915281e0404224041d50307621144d08280861001b0040b0780445030941000214016610303814074568070140c1c070201002003814140c809012090300300603455504c030703400d0b18010f1564803015100d000588034070325005410000749002c0a4042d40c054180400c060000d00702e01202404144010902041780e8000544181c1c140140c0300f501e070140301c0d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 970822203 1250 970820953 970820969
    0x102918010e150609012307060204151202070b01031b080d05070b0a0603032f031305040e060403050904020a120c050403020907020a0201020a061a040f0203060a1d0a020f120a090b01 79
    0x240c501500c0000f001e902041c1c013003480300340a00080544140c6c0da84100c0d1078540d4002d00654445e5507504400d00c2c40b8411030302c00030105000711000c07507042070b262003100c0c503442e4000000c060baa421a110f08081502e54040d1283c0f0110307003040800c1c4180104111704020310700382d0700c083d6a12100d1504002d0700c00b010b44280002800c1c20300a1000940041040b40041c0001140741110070400b41030940807030060b50100a81e010004911100500b80c142175410303900d0941d018091180c0d01f821190b07541401f00d0b00680000e009000803600c52416800900c02280c0034500500303401c0c0c100607032108584e8006500360108500250070411801c0170b00d4959441800341c00544403244050b00081e4488916800081019580703400c141e060303642c0000380070054a4050000c20840d080700c0c2800009501c03d6940350712403503500301c00140707262000c410040400f0040c0319020b25500c4101004019400c124080119480e040c842c0320381101130044602e00c0391115030004a0309504030700300b1104d0070034103800c0b181c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 970823453 1250 970822203 970822207
    0xe07140c070b0a050d06083403060e010905071415030103080306091012060e011109010207090513020616031e0e010e1203070311102918010e1506 64
    0x10034000401c807101160b000158065503041e00003000c64080c425100111549403402e00c0106000200092a030fa8008481c00c40b0000d0010f0407201d001c40010100103007188100403513041c030000b00290007500d0030041080c0045007410482d40d0301400e05095401003d51842e400740d0740c640c1484e180da05c0d03900a00703861440d9491541941c86154440c8002043c2030f01850b400c1c2c0c0815504031681c10600d0060400e840b88940390511458084040c01c5030415642c080c1d0300b0598503c0070b000004040f00d00310003050300102007992900410300050139004042c1c0c6003000b45490703030034050303283e01e4014071106001c4e269000002030689005460300355040c421032050441d907440c050407260004110440d540003400e159016031003400c00038844140481c1c00306210700000c0754050406030400c01d60389520014130150703108400c61207450700c100d5698034071401101c01171081294010b4030702c0000100380140a004c03841e03880655400f440e0742c0e61007a4400b0703420b140d0403070420000c0c203007541c02c4500300c1f80304881c018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 970824703 1250 970823453 970823467
    0x111f0b040603230a12020a0507090b030a0201030f0f0507050a020105091603023a02011d0603190b060a0e040c0c0b0a020c010b10030501061803031407030215010e0714 73
    0x140100140b41c001c3c2d642200d44032008446814100001581e150380720440902601c011311009480e030380f40c054101d5042c800c1c041c0c0410b401e44180141044c2140c0a0011f11000712903800440182040c0c00300d21f40701c5581c400d841c0c003400b210f5014040c896421074807059501c044480009003143d100800c107000e940c004c501c1c04802c030a11107030401c0031280c040300c0c4410100821040c003003030507003809075240301211004c4085024424884c0d03c0004039000f601d44001c8200345808d401c85007824a118554040310400020708881a420b160070300b106c2c540701c2e00043d0352032080c0c00705003250320101c0c0e0310300425a089100d50701c0d807529000e14101040c035850000c04e6484580c1d500801d400d4094081c4840c070f0b1300803070386e915408c000754480c003101080101141000000040042c0c01020203000d44000034074094000d40c42d0900c15180320b01280c0d40355864040c2d002034003095940c5500440740c11030460160442c0b04110541c01820280030748403d2900041a06218402400000300a015514007c0d4280411 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 970825953 1250 970824703 970824713
    0x60a0b010504241d010905060f0d0501091a040204080a08031e04030302120a1b0f020c040f0b01020606270c0904020c1608010606141b03130501020c0a05031b01111f0b040603 76
    0x9074100c03002036a0342380c0c96900c0820000151f000b482852208c5528080001a0110040d0891440600c0d04040010301801100070302043e48524040d140c0301c2e40c040d04640c0c0003e40908001c5600c0885004c0f5050150075580c3c00c030048410a5a00b030300083c2e000310f0380650014070940c4258016100403010088041f500d41c0c100b918001c030034195001d0001390000c3d0480c84d4028000419100c0c0018001c0120b6038212186000804160881c54010302c01c41002941609040d070009264903600d10f83d51183e507200355031010249400510307540d80e95405008048180d01c0798000380600d00d2011020b0101c00924404010105000d54818403080c2c0c105901002a50b80204440c0e045001c001c8215503a4003201280484400c7c900300f00846511001070507401d10703414a0301810075240242c0c01d4a0440401004110880845000700d603856000103a90228003209440c3d14642e035403060410000360100040943c0c10040581d8410341c00c442000d141c3d030000d403c140705020201008907010005641140c9070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 970827203 1250 970825953 970825967
    0x5010f0c12030e010f1b090509010b0906090d05100b150f03060d0c0303050703020d030218040504020d0236040503030c030406020d1b0e1002060a0b010504241d01 71
    0x1024120070701039003203814010311035000240d0511610009010142002c241341c4c0040c003488246e4007092030b01c1c506041c0c42038414030f0020219003000f09182c546908000802d20a40d00504a0725445a130070004410329445642801003080c0c0034801a040e61115141c0c0d840546000c3c541c1180f14010b000403021500766480d05444800c800920800d031240d441002050242c15901000f1f080342c1d200c68000410542d02200402600b0304c02c0e82600c0840d2843c800c25416400380002e081d0301c407058014034020714200f03a84015407050004055111225054000c92581110b102c41c01038107000450001c1118000030501d0f03003d151211210b00700da480c2586505440b40006060484681e030004007190621402390140c50381e408001e20704121030030342c014610407a084520b1041e07012601220b4240414070b4002030503042100c081d0040c1505940d102400e1000b015881c0070766040c000203000229481882c039003c04007414401c2c60140781a4400300c00508400845014803481d21640c3c400c40d1510307648a41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 970828453 1250 970827203 970827227
    0x306100602060a0b0f0d1214090616051e010501090c0c05070314030f0f0a080c09030619021c0c0206090d140d0908130504110a020a0b06060f040303080a0605010f 71
    0x40c00182d0720300780c2d07000a6190343c0311074017140e801200b54001c40c3c00d0140e111455020440c45844a40c01e120030340406041d075000d103c0740e40d6409082030003051314210fa04406003440c58440c0342501c1c660201c400000d20310845010807080709a54640043c0000c101c1482078200300c0c0c9007810195081c04807581c43c941c1d105903d000042c0600c40c0c0b907401002100f81001a51060b400c14242d1949581c40c2407030404580d042607000000040c200c0300810a00035010003151311036107019018002950303589041000c41034181003564005a801c02518010341280c040701f80514142010115020107403440007440c000c0040c1131580650003c00401001e960409402d08018403001c0d541600d6988803c211001010011030103000b4010003d8004008103604001e042509c1044508005000c221903084400b070044440020141e403007090302401182c0e24040e020360100c4018012483c04201d50f1058907150415403044020401c103509212194080e0f00446000e00001c0c030b4159441c1079040030003090a910313a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 970829703 1250 970828453 970828471
    0xc06030c02010b1e0111370807060b130c02010204030209150a03060b0d1a0906010e09070e04050c0a0b0a110a0305042102150c07080606011e02010b04050403090302030610060206 78
    0xc0240421a4021038240b54071440c503205131120008070464400c501400c0040f01c4e2909100c4547c10a03200c8100c100480d00140c20400c0b5070700f41070083d92200020800c028500c0d50207000a09040101c02e0300740210892040140d001684582c554810300110344805131409004030085512188a6164004614222500828003040c80650350010401401c03800b54090602041c4208d080d1441c0342c5124114003d00300e040490720303180c2e0784002804003000103840c0e000441e00f00c02802c11282c42a0000b058000f070113602035601c48101d84000400e00c031115031007400010070101e203070100349070022011110300f003222016000e01c0383c0a0340c0c001c0852059000d0780070207405425545013050a801139084420b80c1c050124440b484107181880c1e030351380200148000500c210100400d4100c0c0119449000c0e80c0c040e16280224200e520350100d1030640c042c410411517507030b415580082e0b500d5001d1140224000c0e15042d8546095006060401c0c0c0002d29803055420310740c1e0704011640d8002903640e44074200c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 970830953 1250 970829703 970829749
    0x40203090a2409060c0e09040305090415080312250c0303050711060405212502030a0c0b0405010905010c050a110a120501050601031407020c060706060e040c06030c02010b 75
    0x1080d0480c000348140c50100640c500d4040010308101482c2e110003102030051b103a030140301c021041044003002c0200d0f0300600213501401800303d00d05003600a054000c1840400014141d200c0107150f10f9604100440f07031010088000f072068042c13200c02d645400058001103911054007080001e4144000710000404166554001071207517486003001d00c2c9a01c02c2081610003605241c00c041d40d4900c2d1354501d41d2156030070100070048400b5032000303ea040f1003e04400c0210018880c000e4204000d604109a03054080c042100000901c04d4107070310040c0a112252688681c01c000c00104009220b80145040c0582c04800714040b55001540c28482c03a03011101400304892940412090070b007542c480b118100700011000201f02043d00094814002130b0713401c001503070300f841301c50340895410f990798800740c1c001460803070503410148010180140201d901254060303a4800d24440000b040f601a80c0e1818000805d2042682c14000e110040440b071001380028800800010581880d08220754811401 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 970832203 1250 970830953 970830983
    0x3060518071d03030a0905010f030b09040609030c0507121217241002011d19060510120503030703050109022b060902160b09071a09030109080c1b040203090a 69
    0x1070b0b0212802c10040c064142c0e5280c0001100250105421b40a0180030414100324031044a11900c03a40c0c02e004801031030208e658807291185401041495815810022428041d10101d2020450b09000b410f0802203820070100c103042080c0750482031032500d0f0420070400b401d504212003d42d81660040149580d951000145040d8500c071a0080441036403c600d15440094440d5010f40c068003010b90401c14200d4a8140580c8680e11044400368411005030090025404500344d0b9228036801681d01180d2000c05841d01e00414280610010840302a8000010010b41c83d40c117018181c01803082840a5003800c40c2c1c0d000d61210101d4040320072100da281b052114070001d010f50003181c004c1595030000c640e100c00c210300c002c1c1d89200001040c2c5000c0040c001086d1810070000354070044541d04016899908104c980b40007803580400c3c0030540c07540d251384a042c041042d00000709a010340f10401020300000c1d24000c040d0001001c500b41e48558414420054181c1c0041400d580042c0e1065135500030300a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 970833453 1250 970832203 970832237
    0x2a060e100914031510090f0207051f0e0105130312060f0501050913050a200a093b09010609050f1611101413030c0803060d0219060306051807 62
    0x42130422001c85403054003800903607030700f00000800f074400f43c21090100301c15175000b8805034440d4100090441d8400c000324035000f00b941e81ca18521801f4030320041500c168034901c0340d0075110140c170752807007400480000c90f04040d04108005c0c6d001642940510003185807601920302000c1c14400c1505000002070701d2949551004488070b80121150801c00c010b091505a00c0c00130454000c80c0c4034050100c0c03150b080c0346601c50007035a140a003150743c1c01080758104401baa00d030000c0d84000342240001c0e20698905c070400441800031820030003e80005074030b480d401840c01c2d2455548080d12051a050a114604680700c1a0641c008601c000c40020701c1d952420850b010b1440d90a01e034540e005485180d820803840341c0110024404429110030241c494441c0e07581c0c1c2c0490207a0041c046207140ba10080000d076001d000e96031062004000303106440c69a004680c003015201103102135082c0e140d200f40445a0503104036005000309440b0140a41120225030718540360151662051145030550f03442441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 970834703 1250 970833453 970833463
    0x5010e15030603030913150b0309060106031e020a0e0112024003080a020106140f10121e0501151205060a05150a17222a060e10091403 59
    0x41750290600b0602c60100e0340741ea00400d8140032520f0984032016000806a090f001903078080c600401c00b034021646800c006400400000c2899150f9003081700300706107100150f20107010740d209507480d00c810314064800014102c1060300712850f40e06105200e80440081c842c1d440d219241080c40c20488550521a900003500400060780c9010009410b00030040003e820050304494002d40c0003400540c0d200d8440780c500508140d6410742240f42c140c0c081c900c5281c0340750024410165401c1c9011207601d04100c000907203c51240700c030b42281c00166406c00c44134040c41002d0040203a200e111200c0c404490004203141031500b152000c458171400814080d0345c41c0141d00000f060000c12005410422444050040d0021a07400f000704403994988080000c044195600c00c01c0201203641036070035440c0101d590401a50000c1d0342405800794034a110841d049150440c0b540da050340000c3c0301d498111700034485054a5191401940f6000c0201d082c20f8104110400f52030a1000304840402543c0c040307498a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 970835953 1250 970834703 970834717
    0x409060608120c0d081b071a0c180409110d11060301030b0a150f060507030522080610180e030d050708070215250c2a05010e1503060303 60
    0x20b40200c0c8140050324114400400d110b59698081c2c40d251807208000f5194544220703580850f54070740c2c0303a122038410088002010150b02c640c0d400b5865000207100d9a00d0520704aa64400c01c100004200440c01c07690541050b07004c00407a024050108556500c48034404110040d0b405001079124810403c00d440300d00710042800508065140d6942c1c3c00e212030369410070b4444c0204907162450348400e8100c0c2c44101c3e02590002d2042c42e58240c54036804030748030381c41040c069081000c1808200c003201c4e1880d0929210203c0d40078180e0200b400c04a0b51414040050181c0c1060b0660203c10400440f030b00104541a02e4070160010b0001020400581548110241802e95038682010080b903641c0001e41a801801c081d802c4403490707049070781c49c0102418265011202020325000d00e020213602582040c6401450346482d4a002e1030795500e0001406207182030b20000809084c662468414028101008100c24681040d82500301c01c0840d01501a90301c40d01500d540000000744192010012201c0d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 970837203 1250 970835953 970835969
    0x1021e0a0c140303040605130209060108090735030a020c040209060706050a0e0d030605061b120c060108060708150f040b060f0405090108010b010912021f03051b0a09030204090606 79
    0xa00c1036145403c1e20b83c0c0c802ca804450282c0340901061018500c115030a00307403903001e072481c1459214040151140c0100808118191045142c0850b880750100110103000d40c0c20034090406036403940a0107480404002114000d80c03042c81900c14590303002804e0859a0001c2e42c00507620031425020420134070504201030a220301707040c240300034211b846d44545c02e0f100016090b161592603201c4101d0656185c0e102c2c180e44100d0502a41c0d0305a29503114400303840a000741110917101c0300e40324015050700b2560b0240b15607002100108591241407010680c02025864458124a4004020b1241110000000d400b07050f411299600030348842d0321003e008a40180341d65124855001f02d4107041e401400380381c0c0200440c0d0000281a00140500504000705031180100e81c0d0410184140000c0d04540c1039a000d80c1c10300811081c201c41203541100000903650100e00d600c0c00100c0644e0703003245081004103000041140d00000356004101805890b4100c4000ca00c2035010b0405401802444d000140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 970838453 1250 970837203 970837223
    0x5030c061e07210f0f0e0a1404020403050d1d0427050708100b040e06062d09040804063c020c1008010810020702090408280201150801021e0a0c 63
    0xc40f290040c2c03513403003c0139040d0344901c450312030000c08a0705000e006003050780040482c40c1c24820075801d01501190608050001800c140d0b032925403601d231501c0c61007000041a0781e225000fa0050103c2240507000c07400351000d018288000703d960a515a111a01403820304125100f902000010b004000080503090200d485250a2500c00401071125418141c80b07185041120080a06d01040c414881c00c0000c0000b50700c00150fa00107002147d880300da540c104240c01001c1c04da203035104401640568020000a9191802c00101900ca40400c0462003182c10005010070580b0a041c0d04100c8007000c0c2c00f00c074140d44422854180c0c60300c000300030000c0d0f204511000c0291141d42c0083e0250403103904d041120813408030b918000c0124443c004002e9042502400054045100c1c02c0042c402e5103c10744844802d84080620721418055400321400140d440302d550039142803d100510f8080c2074010001c52401100d21641c2101c2c1704411514902501c01040b0100c8850090403941000c68100603a08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 970839703 1250 970838453 970838513
    0x5010b0301060e1006230a09090f051b031b132606010609081209060702090405010c0807020312130812010602010c14070209070c02060d020c01020405030c061e07 71
    0x9100311400c551101807180002c00c0000c0551064030348101c444006580058508486e0206103041e0340555028002d120b0b044200241007070780380c4104400512032030b00c0060b07070341440c00598030134540694191300106c100340184020901c45000e1240385400c048401e540c0d45074004454002c464403944000080b40480b1080c15110800c5a1055129440384050300d569030307250041590019070340d002d03003003c950180317484207503d0301250020080200005c040c2c506010f41c2da40099412001141c080315580d45070b07a021440b4a8010404940100244c0041c0d0b040540d8046880c5020030000d0074511130f6202c941190084c000600d0869000d03c944803c42016580c46000c081e01070030010700b8500010b06501c1010401d52010416503159680c000c1160605032150041102d1044185c3c1c403d9a11890401a600141500d84000e10f0001140350000d62118500f404041c182040800c142d80500401c00c0300d000710204800040c0c1e12100d45103040d03500d801c51820818030000308030080442401455401e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 970840953 1250 970839703 970839719
    0x40c0f0b09130e07090f3605030d0507020c01080c040b070b04080d11030912070f0b180712020117040f030f0302120a06140d0b01290d0519090203071205010b030106 72
    0x34515001510800307201d142e03542c0340e819641911350201400440c1400000d000034040080440c1c0c100c5016402700c2c2e041904000520084610035106030002d41c4c4404040901c958100356501c1d8030400da007140904062030240c45030b00502c24960020b050302c2108000074100204030003034401c100c10541040241c0000030700800b0f100e500640d000a4144100d040440c42d0404a030100c2e9481540110010090003a41d51005c06060005c1c1c40550342d55064074120b101088200320440003001c1e04211440d200080d03000143c10801072800b12010400d0007001c00010680c13240c02084116410304d044407000c04900d100310000d004a1030b1204504208030244038020015400c0ba00a5484803822402d8495000017081003a4821036801883d582e94040100005002d95020100441040c148910100d41c0580e01e07012a41c043c1200710160b82d9039005021803d001d0400081000302c1c0694200401c0f0540d800103a03a900c2c0c14030407440480c183d01a90b80401400703402c80703c46040050000e020007503c079111 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 970842203 1250 970840953 970840961
    0x20f070b01031401051e040204380402030105152b05100801140106030e070807030804080601080a0507120206040b0c07050108130c0506071712040c0f0b09130e0709 72
    0x7003070b01c60f00c03410301c08918010410f10506019a113101d251241c01803d5840381d0600c0302c8002c0059030700c56621000020401000c040c00c10b0aa90001130000b10341100f0f1080c01031102807406103902480c03046c00140001d8035103020802c0030860700d084054540080c101946a14032404568640d4420302c803030001501e042d41d42000b0301594003641020903194642c011942210051804141240c6843c00104178950103681b0040441c000307201561285516002064604900c0341d00032240810005810009003905100150244c4566070240150381600d1301c880d5941d1f142d074018400c0604001404800710b42c5d80340101c50042c102072440b15200c0c000010402d8452001e0305c00d2070b01050500e00051a5820540c851180340c0e03900c045200b146d0707401c08081c8007140c0c000364012554084a07050251100c420300c40901020241c4030548629441c26107040340461420760301415008031329402c01d00c041e00d900c03429030721040d400b540c05a040010054288000c1d00019400e00f12074090f40d0808200c010706600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 970843453 1250 970842203 970842209
    0x80c01060b07052b08041b09020a1d010809071505040909030804050c060906040b160b16140f0306090604090b0a02041406130b0a03091a1e0f0106030f020f070b01 71
    0xa090540c0e031480002c0100119110014000503822134001030001f251202603403555030b15000c0c1342c01d60360384981c640b01c200c1c1d01440c101f00108189015041d07100d003089800c01d030118828a000a16410048142590340d1070900512018001c1e0000e201c1c1c12034864002c2d90010056050140704404290601a10064041c1d5040c4e03114041c0c00841041810308508840c800c0c0e001a1129140030b140c07888050203038010101036050340010302c191001149522510700d019101450240e4a4bc41036028080e14a4029400c3c41d044400280200c021540f504c0c41a02d50000d02a904400595500b2000074002c0c5409040100111001002e000c10454958060000d1320347c110040307450716400201300011030040c0035409022002c428424048520520003901c03000d40d29080c0400e940c0980d90b01c0078081b0401003500b202d000169000c104002d11013902420b10300c01c07645010105030800720240d100c02a814001c6d5002d01d41c0b00c15154407084816070440d540b10010415050310380075103103000381c2e048500f0b00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 970844703 1250 970843453 970843483
    0x904060f0f05250e120105090709050f01030308040f140c0103200d09021309030c0b070e2b081308070e0108030301120f02040519050a1107080c01060b0705 68
    0xa28441000190b40300785802030140307990182001c0d11209210070381581c1c621554042110030501c044054455000c0354030407404010010550303191409807030707241c824107a0284e49c0c014281010701c0103442c860f40710181903e400d03281c00000c45e07072030781069000046120b800808407000e1920329a42a03001044042481c4426601807141e800341c001042d00311805c00854051a0307804014019042c3c074154020440c0b83d1014250305076400c2462040e1084031204403003034005c9000c03990380e00108502186403e0344411942060700b07451030f00704007240b0540201000c140c5101d4130002c480d180c6404101d07031201d0f040c1e0300924481d80c80109180b00c2d14010464400e400083c840c00401061a20200e5230150590701a0b000543c1143e01e482c0042c010703900c1414091b2095014a1404009a11030780035241c0b040101071000c880e00092010041e0454800801006100d854400d2004240c1444070480700701e01d8000f25040d840e0454a0300b600d006081507440070800510001d90002080404038917208910001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 970845953 1250 970844703 970844711
    0xb01030207121e2105060103180b010e06090103050613140a0f0b0903040e1f171615210b031c0801080102030705090424140301060807060e09150904060f 67
    0x105001e0303504c5005014840c815aa40c0b00c2d076410b408107a40e01003130b0302c01414900410024082545809101c2450009407446405800140800c80c201d00026800042c107582c085030961440e110342e42c503034070050300d0b41a03030144125044061000d17903500c028113910003009032101d01d949480c101e00c42c495506001c8400710b51a100060010b98003000340c4040301e08800b0603401507500c25120080d01c1032085041342026166030300101c1c4a078520340c0e115801408040040c02c0c40314500e00781c0b954142c40399208824166a06841c4146580e0258030105004c0d0042c4401d2106230f81c2e0040040645072024880350140301c0c0c00005248468842204884070040ea100d51a150f44c032050b0150903072004407843c0b80461810058030140382450740c420500800a142184c01a5038080f0f03607a203482d440c40c0e101000e428042c51013144246801c1c0f20f02030041c18184001d0042c289040740c090310b40002c9401c0c2c00e100e000900001165102d010590043d42003005003a143c803031078141740c050000c002038018002d81601d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 970847203 1250 970845953 970846007
    0x9010e1507020c09071107030c1e0501020d18080303040303091b0608150d0c0b0c0c03031306050c0a0503070b0708131106030703060806040f060b01020703080306040b0103020712 78
    0x1034000346004a4140d40600142a00e00f400d0107099803020b0451410002094040c0030041c400f03000e44c40c0035502c2003004000b21864221159401c400c483e000032054220312604124a030f80025003074241a0b032a04040c03505250314a040f01c264000e543c0107980c94000042008101a850b5100070304a80c41440070060f102e003d522401d0024000d40076000c0881c005030049110a44200101c149a400c000c01068a05000fa55280c0000e205a84050142a4041440d01440304c0c18015088200303030030790040d410308051101801c03000d021032162406101c00028240e0400405101406449030088201ca5540c0384525100310702c00b41c111038060000d14440007080080b014401d0340d104582d080808600300c000004d0400040d03a00281030312013491f9985400240d407082c10f01c03519201e5402822590100c5080782044400e07a0f0802d58120304640001c00184002801c00003900d0700a1825100040c003c86d460780182d000f40700b44030b809007001d070360505610035407603007d02c0f0089090ba0f601c800c1405682 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 970848453 1250 970847203 970847233
    0x6170102041e03050a0f020f061305010908010c090512160f061206080c090c04080a080306100e030703030309060204051c110a050d031821050d1409091306020309010e 73
    0x20407800f000304550002000c141c08620502118050b4600041c002c40410310040d001441c1c070340c4440250406503555220406c0290381001c0440000c01d240070003800410381400c07004003c603140c0c2c06483d201e90000c94a10040c180c0400907403565410404d0314010311a1502c0300003c240e1403501c0f9080c0050750204c2c803112161103c2c010402100c00c500300411040301c2c0c0300c0400401803001803c0010f42e43c018800010a00c4080102061044c000c0840d240e680c1440c80611640b02007000c6441d05020319404603040c25240007401204aa0305071400150101051401c5000381c4100d0707226603071069400252000d552580c9c10390500f0f144c81842d0b0000181e44030b40a0081c1120640309642e0b1007840703040041c0c0803c1c050032a070642c2d00d04840818252589550400b08518205042c4821451585034510100a4108001c44034810181004130707403d081010b100e025480b94401680c060509900420708000700d800f03402c0a4260702a10940d184e14140c11810700030880c0c5104020184100d1a100050305 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 970849703 1250 970848453 970848509
    0xa0804030c090c1713110306070c150207030c020d080f0a050a021e070909142508060105030604122c15120604180b04200105090a17010617010204 64
    0x1004d02d003c02e40d0560ba0710456958140030b40101940d02940d0421800140d9400b03021091052038a40c50b20030a2065074200000c0c0084803610402585104005080110303030412041c4ca50340340d044940d207090a0403450004d03464080c10010003c548008610040196000780c05480b46801c940e0880d102130204801074000d02c11103801d1800c86400c0180240030070801c0340c104540e15800780c400f142c0c1c80a41541c4441c41c0c0700011005549541c45420f400840c40740c000b181200401c048401070900d5410f043c0007948542001c2c2c001000000c0c0324500c00300243c01070b03689220b50400090903042605003640c00400c555801c0c078140e80300c4c0c0e8107001103907800c10a0106031406002c0c1c04c800840e40e03660720802d02009005032000c44510360711045421001a0a221001c0d110354820903400c1c9010030702454082050850f45000b90602c4002d00031007015844465040c1c04079001e5001c1c5006181102c540301d40144040c0e08614204944668411a0060305400510494610391346c1d042c5203e030320180510180c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 970850953 1250 970849703 970849727
    0x103030206040b061009060f05121003110a0608010605070c0e040302211e090a15030905010f05010302030c21030a0216080708031209030f18040b12100e0a0804030c090c 74
    0x40b61119506000048c45520000c0810980c1e0401901e010081c402c5402580c100711030584550706040d50920411081c55040f1b03600708400d6507640d80d02c5043c008042c0119005000e080100840403c1c03450070b1181c1c03840d03c28001c1104038034001043c140782c20020340303d803803000b8000550084c9010210245096a044520031050406201d01140c2e9140d01001c1c0d65129000c0242e204c5020720006c01d081591070a11030345902c041cac4000440380312500c1c0c12804e640e090302a8000551a010040000d61408035200e1003144089172400c480c141700890011480d40c2c4090b4400181c800400c080c0345080c1c0001c0c41c200481641440085565501d0399002e41c0e5501d18000c4105a8106101d40b10109100d10541500101480241d03030400340048099030791600604601200c5003e165010b20150625209100003064140d0301c200040c5254500305681c0d001d544066000c484e5224200c4851540c107002d000046540840103c2d40c0b1070350b90400b044c484206004a0030000e1801200d2200540120104482 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 970852203 1250 970850953 970850957
    0x90506070806210f151f03020a06050c120a0c060506030a21030e0102132c0610020a0b070504080d081014210313060918050705120103030206040b0610 66
    0x920703c01541c088000c0c1c1d0100303d48110341c0c444d0f462039000075241071100d1000f800e0f05a01c04011803920344010b4041b41c1008144607041004540c042c405030711810010401c0e15618140340342c0d00c2c09141a040e18010f540b01951680103000310f00078442e26486180082c07030324041c003814002515104101602c421239084001c004003402c241d040c20102d107100301a010350351141800216403d20a45060990340054641c1b40d00402d850020701401c220102c00c001c10301000511900d80e0001c07503151560154000d4002803280e01030344600c10403a40f017042068030841e44107854151170301300000d000c2d01d00d4000740100031550003a0b1500c49003451148a85070f01c41c200303141110400701d14184000c4e1501e00000f45594100355010b492056074114503c105c000c010b0520011580e581503051214081000c5802080800810364420002c0c1e90002069405854101c00c001850740c0b51070b074040e1740e01c4c0304500d074465030301d0340b8103000100b0305801044552269010320300050103540d40c03008009080110b07801030300c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 970853453 1250 970852203 970852219
    0xf180a0915060c14150a060f12290c040314030313110a050402040f080d1103180d0b04050706080106031a100203070b0103080a0e15480708030c030706090222090506070806 75
    0x2011810ad4880e4041d803101d10040c11014103c00c00138807d003548100c690709400c0380001010003c00c603182c000246207500d10f90145041d401c00c45c0300c02d20441039002c070103080b0718000c0851285541d600c443c1d16004280c018411580c690382c440240718468164426400315014060b01418440c2c0200f0381c1d4040061008040c42c944002c914078041e5200c129561660050035031003d190001e409810141e0149018200400d0114942400149800c0d0140c00440800d410501c039138176000e01d00706c03094034038960840390740101414440040780742d4003458030043d0002410500000500c0310a02c0205240b96040e43d80c9200d80c0407100505c1401c0d4003204912068440c20450915030048c482c0e0f07490b07013218402c0003001e85c1d0015035903403500c0d440c040d005074421a180c1c1e03d01510070110407c1001c00801c80704000d50704080c450103410352a030081c40001750920b51039220a00071562290003012a200540c601d84041c5003111017030a0013003019110841d01403060070045150503028411452041000400e446 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 970854703 1250 970853453 970853489
    0x90d0507020105120a150801091511040308030a113001060504050603060d080c0f070f0501080c1605240708040c1202060f180a0915060c14150a060f 65
    0x20490600522100200b50341d030401c6e01d07440711802c28490081c080c1400204455040e0b0400c801c540660984103040c00b490311048034141c42400c000c0c0c0302220340100c4015100e584100801010708602204030a40200000304004582000e01c1000c0c1d14505401000c40396205028041415080078001c000200340e051104020078503180c0000c56000d0406003100c20600da4554610340d03140c004a4141409410440d01021a4501044440700914101c000480c0301031400300040d0030000d02130700117000c800c4005074000e0b9882004100c1e02d0701692010458419800107484001c600c6001e1031a501540d07101c1000c9030b6071500c80c0880d01d005540240030040c0d518640b4440c040740c200f00080882c6c0199040c4200a400010500605818441c04220200f07080502007008050605a040004018034003034144020786c2c0c403840c400042c0d42c2c0d6401c0400c4c1607205820000018004400c10254610070302c8865107070700c81d19650160040400030710602445484002c0100340c00107a0141c0866609541494 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 970855953 1250 970854703 970854727
    0x1d070206061f1809021809061e0a081212181b0114030406060801060e04110f1201021c0f020c03070605070504030b0702070311091611010f0f05090d0507020105 70
    0x82d50885040c00d1886010b034220601442808260f4045440d05a000c110544584c940c1c2c00400515801110b02d00ea440c80d010780041c83c80d403002c401d41c3e110980c040c0a0034585845828481c00580320010807250687c03c0224680c081d580305201d400c0d0700d000d02c0c6c008150303840c0010314100030b40c505000141c00003084519040048081080d8028108041d401c4200d400a00a50085025a02a1708089050307414401c9043c00d6482c2c0e0750090340d080c00c9a00c10000842d41c4030080107983c1c0c00c100c1d807940c580d101702c000050401208a5030240c00b948001099014031660190324003c2c0480e414040c055070081c00c03501412400740013608841d03a00708210420014030654401ca41c08501400c06508185e103980340d50046e000f08682e400c0c00359002003024024041c3c0720440c0304000c2ea08407460241c40c5002d418001000d914001e00c0340900181340c59812540c0000c2d08414504440504204030706240114810701501c025a84054240a284650803203144120300f22941c0d160180c440d50f11788080e40c41c0b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 970857203 1250 970855953 970855999
    0x121e050d050a020d0c09050a060f14070309030b0a1505100f121b120b09010b04030f030e03010516090506070804120f0605041a1e01061101151d07020606 67
    0xb41d180826820009000340d180c0c00d20480c3c68401d0581c2d116076080c0d040c8010712480c0c4082c2c1e005041400304400000c2c549030350107a003800f038103602035203103603124042c0389001c2e40e01c07036650340009095004803010030104a050340e024031000b02c804042110111350302e07401d00100354901291b0200051201f40354501e00360142070302520040050500060701c803400070810601e483d031842280001401040225481c90b6680180c2801741c008640c006544c4d40b5108903810726119600c8000e02031440640f2040600d40902c034001292040a0024030562a05140d2010240031290416000c207042c844d000c0380c0f90600c00291404254030400c030610341420720005100700021040c0171540d007108180c07034a001944500540b80900c0c41904140c00088022031048000030004007800108804e80100300100b903059081d01d81152810304200b0710400842e4251405406000000b0750030b00102d0200043c004815070b00c4e980c01703070244001500d01d80c80300c1904985840064a0080c0d10920348119003100403030400c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 970858453 1250 970857203 970857211
    0x3100c0e01180e130b1609030303050702191b1208090405101a091f0e01140c070b0d0c0804200a090e0a030905030f030d091106030103121e050d05 64
    0x12a1410155203280148540900f03c0b2440540030b2918104401c01c082c03121100d8000c01c88000514081b104c01c407004281c885070340300c0502010b07111004220410300902ca42c0d00074a0900e0031071711040006003489000c01c580c2a0030190340c41864540025031a28034a020100d041c0c1c0320628600d03103034001080002900d8042c04450740c0c027406038000035201d1800c120703005000041a101c0d41c1c07103082036000c00580703030241c0121820b0714440d1042481443e5101501104444003420320200101c40c80c1c0360300b4000e00441d070300580c0d24810b2030808529920010b004d000c040021034024850f014028400721140c140070f41e001024480c00c80c1c8550403211812a001540d24005000b41040d10760741c21000d026250380c2c00c42d0041c65000600c500c0281a84000c420015040c00e8000f406010b452103030580c1ea0b48034030180c1c14034040d07a130100241003115660781c000b4909001410b00703880c3d58503810918a03000c2135440101c04180d0103008511a03910b006590818031019888140c06d1107418003441d0044d01d4024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 970859703 1250 970858453 970858487
    0x30803040804051207150e01080f10150801140d1208091606170105030624030c030706121a011b141c081e01050d03020f06041103100c0e01 61
    0x8040890f2a4865a01e1244202e08540040c40c3c0a40b030320300140c030000080d601000401c880c5162400c21a42c2140120f6040700d510200000c040d81c45c61001c41e05510380b60448003c16410b00405284989d00044443c180d0303107000b5103080312070100d00800c240c008800d03100070001009440d002c2402406058510b070701c2844241030312494910030541030303004400c40d042480402e54040540c0841c080141c41075014050550040c001d90912140201202c0c100a00012a803452014003402e203480034031001283c0345028040f2202152144006481c0740450600740d00400d24010801d801c03c42501c195038510365040e110f801d080c894441c02c03115002c86442080d603986180d000d1915500c0001c1100da81c0085400c4081d410080c080c55000f41000005000c208405078940b0a0a0300300301d82020b114111482110310500040c4d0038501641020a803000e078203400d0140b40200b0090003809142080001c00c11415100d01a036041003401c1150040340301080014403480e610606940070f2264500180400e07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 970860953 1250 970859703 970859707
    0xb0a021c03140c07060b0409050316030c120f020d020106060e010c030318061d1515030f060106090906091a040e030f0313020f01021b062521020102090a0308030408 72
    0x101c0b00d550080c03142590407000c6068000741e2a018004103102d44411200100c8080c440184a40c84095503802400340c80c4012000b850099010035010f50242c200c60750b40080d00400c01020218007615840e200442c00000d4001d1440144e0014418414901035a216413a142c03808120307400112084690400110203060b40c3d200c2140d9403040c0541d41080c040e01c56080410050564041d899060122005034002580b010801035000b1002c503000c2070b030000d20b80c11900940c19a00f00082c2c07412962920304500c6010722800400c2d6030360300c42c4019003980c440c0300c2c0c10700c80256902c90420480d1881411011045402800d142d9145019000006030036041c0c03088078105044410080d601c0d500a640d5030110741c084180c5041142002c1426040301d8030f0900103060201d40440c4814103030040c03201042d21607480001d9090850040c444000b500d43e54074013080000d5202c6142c00703400000d0110246c414115408081d02c1d5840c414002c950700120094240b031070740d910b95656070b107041e0400b6008440e9100c003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 970862203 1250 970860953 970860971
    0x3160513120b0601030b01031103190213030507320405071e05090a050a060207030609020a09050f060312250212010c0519020c0117060a030c080102130b0a021c03 71
    0x140580d020554003860442042e414950005811035004078580c90505003000801c0003800e9112081d40d50108581c8180c014408048100078024401c40034440165014581d02200b40600041e00c541500ca142c1c082a4500b003e01d80040c002e0032000880b058080544541440c840c1010341015802c1705480c14003804400407168540000d40c910950784c00081c20100d46000b0600d40f40c50000e000f80000c0d80e125900e9401c0610080d07c2e007046000c0039010070344407400001151281d0404400500181108004a0a01d404401c1d10b12006480d03062191141074a250342c0c003600303441225000000300c0c280c03584030318a803030400032040d422250a0340d000011001e11508002c081c0290311110005942d0207a0303d0a102001020303030540109a6405c540c452070040007641d801c0030b800c2c10b103c24540a460f140b0b03a05c2c0310000c2d403201050b4000510680418100080114054028041e2007000c0e1495001840d100c0344134041c3c078010181070500580c004105088426540444050000e4140c0b4021905000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 970863309 1106 970862203 970862219
    0x60f0e10090b0a0c0213050115081015090801060e01080f01020a02030f0d0209030a03120b01110d0c1e0c05040b040c0905130905160f060503160513 65
    0x4000101240c0d058014030f10600d402e903000308070840403803510f006c0201038a4280b0030540b0f800e052620304c80c015405004610f1144600c0200410001d140145c804c0340c94a509101100740901010b011035000303001e024a4001e04800c010000d0310b5407404c03e81c03510b0806a441810656403040c0000500683d01004490b51400e016400c0c1c0d854400ca4081e040c020700c40e10030030a40c18825200140201500304803600101403c00078100040c08a4000554800e03130035016101940d0811ba24019145000b01c4410074980d01030100c0000e2544001b00007000341829500590b030f1011042804c22852900f4018412520416141803095142c0c0d0701d00a0842c0700300d03018540c800c4600b884018008025940701c0411145c000b4126040c04458008041400b10240107170950248001c40100341070b8050740c1140c1c01229010601c0c0448036000344100d80c02c0c1c01c0070400450313982100400141b461 = true := by decide +kernel

theorem cover : BRFrame.Cov 970683453 970863309 := by
  have h0 := BRFrame.cov_init 970683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 970683453 ≤ n) (h2 : n < 970863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
