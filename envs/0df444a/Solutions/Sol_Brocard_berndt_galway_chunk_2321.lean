-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2321
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:21:06.430896+00:00
-- url     : https://prove2.me/submissions/f7e853f5-7e0e-4a17-bf94-1d36eaa4ab23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 417266187 ≤ n < 417446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 417267437 1250 417266187 417266203
    0x9140904080703030f240e130807080c032a0f010507020619140406060533070206090d0b0109060f1503020a0203041d0604110c0607030c1b050105090609 67
    0x84860301c1045442e0010b8003e510600c2a0440a040000c2803240d14680880110440c03000c440c40044110041105140070307204140e00c0100b82d009041c54524503550500c050048850003400c103000402c04010300882041610019220761007980300c00d000140c903003c0070f405103207105291400f442aa0240c0c5078014000e035406503495500518155541c840240500c6601c4145846555102c41d00c00342031072145412640240e0060100084403807500741042140c0d00c0109241014030034a07100c0403101d8021000541c028411354500341c0d0b03075440502c001221842601c0c100c903031040340b481c8020107114001700300c18140da804600422126403500c208001300da10074030030510303900d08202150740e206200350042d0082c0640703801241d0416450f00e9400e510303001d0446625031110505010001540340034003a0904081c800c000451400c1041c5104d10784440004003040e0915480702c01c1d0100c0b07544102c81c941e0200c0c00c120304222074482c0b5842c20601a010a40da5103441c0c0c4604004680c01420200d9004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 417268687 1250 417267437 417267443
    0x40e0105120606090c430c2102030604150f020414270a0c0f0e300f0309030606090708070c060f02030915070203030126010902060a09140904 62
    0x400c0c19600e2070304005418100400d1903400080c2030150040c0310f841c031420b80307860b1082500140160320b840d0042c06c9151885400c031100b0582d00a03034800200e00707484050403e46820f0b0110380594066803115007501075000c4c800030b4261050200300310600c04031990354141c682441c0f030184081074070910f06005034000ea020341800e20000c0c0400c0320741c924050584040c505204402c94050180000840000810448000001c1ea8407211043c0703049d94401d4940030f00c45040e04000c2e102010700808550441c2c0b401d04103a40d0310f0983c0c041c817103210a0020850701215030100888840b8040720300402e80302e0b04240c1d101402031007038201140061030a07014191050b81c407a91141456501c6400031030740e441001d2030a4400704d9440b6694040500306000551081c0100801028100300b0644140c0e18120001d11040c119042440180085041841420302414140c002655040c00d0841600d0044c40344a9000703600c810f00190105500390403008017801c4408159416860082150501148800407a001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 417269937 1250 417268687 417268693
    0x3012304020a0609180b18040b01240f03051f1d0a02031b030c0d110301180b010807050c07120c080d0207030f12180303021e0a020a0302100203160602040e010512 71
    0xa0174402166170300c11030707040c100105a148116031480d20030184800544c1d00b6074003404880014000d0300743e0501300e185455a1a15841160342096500800b600f40e052400c0d420103407904045a00845085161000b1202c07040441c002d4696605480951603444001c1802480c4120300040c1000d4081c420780f07105003070841c3c4803c0400c3c2c480c0c0c4011210782c0000d1000030b00e0781d014000480320207554030416220481d403940b01960b80d410604d004801a40f0220102d1205007000320704409039a00000c510b41044450608540f100700d04071446007403c615801802002960000c1c0400740b04203403904204503030448007641c1003500804012078407a4407900018000540e034256590018000c00102001c802c014501001c00d00c0d84c00c01c000640940940c0180c0040c1c0c4070303d030381c0041c031003100c039092603076031000c000170b00e1513040c264085060302e4514400030f48141012031809080d0340c02030044948085040c29883c115100703078580700380290040d00a603a002d440b40700021a02e42003200d07580e4944041d42d802 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 417271187 1250 417269937 417269969
    0x906060905130b0112020c010f05090a1110090b0c0a14070f0302090a0207080307030b042d0203070e03061614031e06130c050c01050c0a05041403012304020a0609 71
    0x109101070300f0203049890400910303d11200805205101401111481800104101d0700452010742503500280010070715811841d450000a480359106070f603402801e851104200c240e1200907944500e040d8040c45202e200000c01c1e40f0000c6010440e1403a8a00c82d54003001310382200303041d207581c42540d03005181c02c821100340c0c21b0015203060f44000d40d1180c05000b01600e071a10075920100240c00c01e90b1074502003034176685601030601e414012283e400b40c1c10034403003002a9241802c0d003100420204107400381a070000109491350712500c001140d07004041c0c00c0714000c1c1041c10541c4030f00340400080400003102d602c400352080d4002802c490141d01da811100001405070181c3d00440103000e414107034001c006040d2541143c203d8000d0340041c02c01d6403240e68680042a1440d400d40c2d2000380101c1005a040020703801d84c5401030280c505032003484513490b1502e0f8407031010900400d0000c402505181041c0500d402d00a00540d07003e12892080c1c80c0754855950b101c40540782c05e90940102030303406581c502 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 417272437 1250 417271187 417271219
    0x1203300412030b030712060504060b12030901030209030f1c02010c050a0c020f04090b010b09090c03092d0313081006141c0f0f020108070c02090f070e0307090203010906060905 77
    0xf02c0b0540240040035035110964034003d8081104160004844154565080206101d124401c1c00644401591206030080d1007844898607403260000d021706056000c5a1803032503480402040c1d92450060003107442071200014184c94030200100560019806c08489513041d0b4450401e403072216010f6203032011890110343c204106410521503950f04240c0c1e9066500100355030302d1510b4000c004404040e9035270710400d018484204001058004202e8041041c0304107400001541400074201c0d864100740184581d0211042d46008200760b00d451001080340c00e02074000030640001c99103604102e6241003503164807801a10900c3c420000c500e40352101004441c00d0000d500075641c429024030180d80211a0346940d240c111000080da0004980407040085580000009401541c54102070043d4803103a80090180d40c0010162000180620b0110704118000e05200e110a58028260341806403640341300300081d0000d1003000803103818818000345141c0221030142c20303a2009082c2c5100292405 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 417273687 1250 417272437 417272441
    0x6030c050607051c0f0e010801180b03120a02030a030e01050411090a0b04020711030601061713020f040903020a21081b0f0d09030e0f0f0906120330041203 68
    0x41c162402d00030418089880081101001500c80f06034840714650741841000508001d60368046d1418410224010b002e8400441161081000003050100f008524900801d003480407091051418000105c0c3c9140040d0700071000d0400c2101942e001c0040d4501c103142c0b07a099032000c0d20301401c50f80c0b8244010007a4102030001c1540086000c40101f0000040c0010a040340d1000c2801d844850212000c0c64552a051250301d0052140d89080000d0080342051b060b10040d0140201d0b8035822503040381811034489031541011118020010010000319003000ba44407040901e003110a1b0107102c0000b20041c040d010a0302481d40382c0c0d23581c8115503640401c0e00c44030f1b03030740321214440700901801074440391f500d20802008104007551b0080b902d0780042c600039103240480500c251007401e841b0584d09071074580141524101c103084480e52030688441d0003283da034549809181126000000b40e8803100d000e040d06038480944130100700036030711300180c01c03c42c45071200f61002052003072010001c540481c444e0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 417274937 1250 417273687 417273697
    0x31104050901021308030403060608010e060c090409080301060503090706110a02040b030106051908010b010503010510030213212319080c1e1b06030a090c0302060706020903060a06030c0506 83
    0x1c80005151800010b40000424a2a441280c065200003403e004100c0d4038094240106001c4000f031080095800d07000340c03501d0004000b1801b00c180411028000d560300d400c00500d003504107601658a58542000400681c401c0300c5c01036407031044d008001a90b9110f0348007031074400110400b500c10518a6130801015008045141c1d9240d9240c140203e62647c0324094a800c29030344040c1040c02c240340ca000700c1d09441015501c00e050040034801088241c540450005160641340f50040c0da4642c1050f0990b840f0319175800c490b842c90a414007407400010443c4a200748a409030100034148000080306440e50403082e542c0700c1181c0c01c96030a5032030581c8806000d21211344500511818000703904d50440c03510784200b4003481046105010008815414440700e43c540070310440000480d00e00300081005480050014210f1982d10740c1145d00f8400f05407004400703940d008004560b40d0400c5e0812101a401078010588a070140501080c241c494a01c903c8084a5001200007030485c84c204c100031881d001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 417276187 1250 417274937 417274951
    0x20f0304090213090f020712080c0304080a050c06070207080c0603011206020304260d060b0306010207150e130f15030b060907050903100c0f171305010908030115080a0603110405 78
    0x2108001203031300c0c00d081c0240c0070f9088010303800580740e81440c1080b202002e44074001805002c55401804080303c01c0303504580e449034208040c00e94030b40b00c450f41100c1c3c500c11881d101d5070354000c46007407280c21a800310702d5000316800c40003218400e01d2888100300e4184400e02c83d031901c0e00c10250000c000602240c0240d80e0140c02100c2054100c00c0c0c2282141100205010350405004002441c06c0141050720030308018090b24000b50b4114504030002030350380da509014042c1e84109c07a40b10310454a03c1170401c02903256024052071074011b000d44024000c3c0c8030b510720041005042040b40c0b620220032801400489402001010443d01d0740780a00c11800d0b00504100d003002010000c1070700646041090402c03142c2003101c000340641c21804010801902c289040081240403821142c103000005091a0408a030380315284084036646041c2e401018041c4000304540404030000843c0134691108007101042a200d82d66140c1d0384031584c00448086000082254010810559160515500c082d500c400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 417277437 1250 417276187 417276217
    0x609030306050a1e0f06020a03080405011503060f240303050a0c0804030f020102010e030307051e1e030a1b1704030908120d110c0c09040f060510080d020f03040902 72
    0x10700ca4001c64011040c5410102051080281411401418a404d0301c000d2000c00e00c07100599080c608003e440e9a4590b2000e0308104089011505100086d8401812001c0c5245190202a66031505101034606500f40d0710006117040e1071031442c00300040c1c40c1400301c1440700d8000e51003815980c00303665a0300985054402c00003002000000515140014000385000c2c5d44000351500c1184002400c1d25403c00f020b80003504188140458941c00500b0343d100312140d03c4031150b8495034072801a025019070a055540d2070141c0d200488000c0310b10f07004501440340e410381030110184840d1080f0904031003902d0b400029040e81e0070450030005c2000c50681061082c50400f000781c1c2d584154500e001c1c01c0540500380781c180090b503204c661100d4422411a2407070030100e5030803e072480c500540c80d8048008868003030117410300042c0c20806d40a01108030954005001c20803400c1ca22140243d40d01640254100f82c0f00e16100340e903126000091044404c4d511038011480e087c01c1c082d42002a401450608030003607 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 417278687 1250 417277437 417277439
    0xd0806100210020403030905131109060d020f03100e070e010504182004091409033703061401020f07140102070305060901021225050304030c1a0108010e0d020601030609030306 77
    0x1070b240c002800194001d907909085141000100075441f1940d0b04281403c1e8a86a0b201e4490f9850351b090354080351084a17030585804440c0210700107440740c6a14447c441400001300442214078032032b0f5805440740040003100350756a00c5010740f01100c0042c0d40e207000c180144402c100c55204083e10080385140da220201e11003a40d2032102229401105401c6d507481004101801400b440d4803556422200098412080e0b050002c407194407072040460940c1200807800440da0701884095010706402045680f407510351204c41c0005004081c0340c010300114560440c10b0f281d8541c800600f030f030f024007161005000d405181a4100c0d40e01c20146c0350041c1980a0b522000000c1a0148040c51155600707100140e50f61400b0144281102ca00500d50356101c945805403202c0202640220041c10b00035042842da00d40b9241401e0329081104500241400304900f000215808442c140904030b034840d500030700000210000064417224159242030069020343c0042010440b950011a60180030b07040c0010303c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 417279937 1250 417278687 417278713
    0xb03060621090618030901120b0604030f0c0510030c1e020f0a06020405131e0f0207081b06070e1804140609030304150b330a020a0c05030d08061002 65
    0x180444060b007480c1c00050030080015400141c00315480c0c500b00c0510b140c0b4401c0c90028000c00026900c3d29455940c0740c038032524649600b0120b41c05141c0200d09150a506039140c03411025040b40605401040005807045845000380180141c0001c5500c4000c220501d0a2040c013602022800782c00c2184a6420304001e140d80c14000d40c89503500428001d41e0301d509250900101e504a1503818001600d0320300d400001140c645a08294045203502c041003204003240d41e06c0113030203a110050480350700012982801c04201054000800c1044140c5a695035044015250700800f0401c0a410440b0760005101c00c0503003510040d401441550041e054080103a640da180c89011640c0c280103030701c00410f000500c405a0805c0802c0b0391480010300c224800440450701d2014025680344802502c03682003140401c1d880d401505c0a103038159042d03102c24044074020743d100c032500010341d4031107200300012490703003004206034800700650b441d01c00e40740d182c050030301100001d0806101c0850003900315030296 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 417281187 1250 417279937 417279997
    0x3070905091602120c060c0a0905150301050102160503030f0c010f14040320070e0c0910020106090f1104030305070c120c03020103380a0810051501090b030606 70
    0x2661002c4403040c0100d0701550042c0ca00708503419011410b40c418081c030481072500003440c0d50302401250029440d20307081513080c0d0750512107400c0164040c441c0503680315071090b90b0000d507040715000d07802c6415104082c0c0c20083c0346202402650b404d07401c10092420700f070420400a0414914050001a0524460480e9021101c031280241900b5000c18140402e055000d4046078588400c42d0400240341006050280e4440c503c0c401c203042d4548070b400207a5150161030650f5408140546010113603035004200034028003260041000c00c910381140547d1110b910300c54402d0120f00c01801c1403034103095031025589504000c0d02181c042508000214402e00d104012201c29440303005d40000141c00d42c03002505480c0a030b0a50352031107080c140041803d10a6104180c00594103d04284181c070081c0b01240c1220701d140c00c1501c2512a04400c0b07a950030b0182d1250b449080861605e042c240d258034011290141c142c440c00783e0310701c4140b0104196240c50b100a10401c403003080c6110f140b0a0710b80030407507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 417282437 1250 417281187 417281191
    0x5090c09131b11070504150e041a01080a020f0d02040207020d060519270203250f050109050a060e0a0905040b16080613110409091b060509150307090509 67
    0x560903151151001044200580020b070414070b401c1c40035041582c1880c80355a200a845042e11071910303454003000340c05031525000f000c3c1005120b6031200740b40c942080c401d21620480c060101c12030220002401c4507000c5104525980e0090000822811840030000716044904041c0e0f800b9600b0401e0300010790340e508a1a10403442040007080702c2c5009640d212481c115a0008400386003801840700c52000b034003a495001501d4146107104a03440c41c00030a1a0a81090302d80c0c1c0d40d40c405040c0040d00b44040e0280c0400c85911100c0320a0042c0ca8400450b04070f28544900d0350004c25102090103540d0059521851074076000c0c085400c11580c542c05e4900b580c40503503003038505840c0d50701404034a0303440745141c4402010a0130501100c0c2043c1c804901a58004183c01c409241d9483c444207103003103004c0c00c680003815a13a40c184040b44080c00d00850b0286991005a40014119000034400e8001c400391015401c1c0208211079600c12088101c140c0d50009110208000002c80b0108566494810f094 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 417283687 1250 417282437 417282469
    0xf07060b0f120d0219081c0f020a0c0b06060408070612020712030914010e060606070204090c0803221406090402070204090b06040621300c0b06040203070905090c09 72
    0x1000a0a0b680400707420000540c0717180c4220740240c00308801280034074003224003e03094603001d62042d90281d05001d00400080850062403800000c40d2081c0c1984240c0d0381d4012070284051070000e0703c4413020015540308510031b040c210307007111502300103050042c5800101e1101d00e05015107010115a035036606184103404043c04a80c0d10054907041c0702c04101e241140045101c0208440e4000091071a0b0fa001d00500c001d01c101400284542103407240d4125120050744403004036811030729421040d8480d0052050f4107c10b140107a2010600d0303807113807401800c64044507281100c1858010521803950700c8000000d4025400708a02801a141c51040892450141d100840c407130501070100015252580e100002c000781001440da51020303075101c69810564028100b620383e2003080852050a04110760605e034104091a03200c11440d006803500710700510509907541955901d0782000124041039840400040010f201800b00d4200b810300707950030030b03e5031400a00780f0152400080a074180032203c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 417284937 1250 417283687 417283693
    0x3030d060f0f0506120412050c0601080a0b0601050304030c12050705061021020303090f030106120501050402010e0109080607080a0e010603031205060402070b220f120e060f07060b0f12 81
    0xc01c07015004003002c90103400d0896090b8135101c115440c843c0840c0c0090005040c070018004140a614000d10455800320284403c1e28220341e0b40b60f545a071607005100d0280c03100013190000922940c4100110b034803450303040c0c4580c46542c940781c80d5189081c0002020b4414040100001800300b401002000c0c03040076085407884c0401d080202041d2105441800c60b09050900c418a8005075804010b40c0d0010300180c41807045403c0c00c00000703014140da0b40c4074000491841c030a800911906400c80c80c842c5000fa240c0740e900d601c0c42c0f0f004403203068051003400e0b0541c00000201c0d40c0c6a00c0740d9401604040e003840d0105469000d60318413400c44006038804c601007000005d801900039070714051640c1c03264040b18210305040ca50b40300c0c500800e00003800709041c1031114007250340380d44101c08411140c5030400f01300000015a403402200041580342c425010480101400c6101e00e043c00442c0d40402c40c081c1114140b40080d80d0b01d0000e4011032044503806030307038180da05c1c2c1c4075201d41141c4517184c0c0d500801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 417286187 1250 417284937 417284939
    0x304050d020c010f02070e1e0709170c210703140a0b01090506030604030f020a051605130506010e040f06050612011e030507121104050f070e030604120c0203030d060f 73
    0x10192030424180c1915040c4138800c154030110f980c011039110112000c01440c050b817552008000565001c04125107182000c5600c140170351181c2c07103e402015600e4081010615815803204541d8482031442c100d6403001015440d000c0d1090b185c85039400c041d10110841d90030940340d80c0c40c0d03d544400210409415800703810a9014442400c0c4058010940346404020904119020a4540a0007800607050101d080c000c0c0701458820410480d14541050a49000c501280c031424042142481204d01c240c0c02082800d8480c2114403825000700c034141c4075051001e010f0b0b018000549001d101030300030b447d620100014540c81d000014080c0f843c82d2256080c4c95810500304c583c104507140b04003114062000002d20020301c000503100c0036140b000d03d60780d403100070910b4000301c16803d1080817a0881e05003001e00403e41c0303400d0f0310701e0f0181c40d494075001c01c20b0391400d0074550348440448025080340e10203400400110f028280c408045800501503a02c0c1c20802c561080503589183c3c0301302a643d85101b4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 417287437 1250 417286187 417286213
    0x703030815061602060723010b011115010513020d110309190f03121d010c0809011a06090102030f0f04140a05010f030c1209140d0306030206190c08030405 68
    0x410600c2509086804500f0160a80044100d80448100090085500007041005d2002401072034503184200c882d2130594003101c201c031034080e0036039069042c0401d0744032000302080f5002181810200350030014000041e882c0c0400c11454460b4040880c0b90107900700214031686c440c501131100d01002142d1040e03664104500d186250100c00d000000d40e0126409458000031360304410004666014980a1500c540c00c00700c22001702070746100b00e80010102c001d105452041900094040e000030b45030a1081c4c1d5a0210032800d07644182110105c1111044020196107000c40c0541400030062045a0070035407002844210781d800956600f500760400b040c101f242a80c20801c0c101380100a032808004240b810001038601001404004245a22101103200e5184034082491101036030180903c0113180900302200040382003000c9080600400181310011070080c0544801c4903409001c99280441210100c41300c040c010f45840c0402c2111740440000c994284081e5020740c2c02480500f41d0001d5040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 417288687 1250 417287437 417287461
    0x5090105030f03030f04081216020d030204051302131d010e1311010804020f2d0a05010915030212101419050103090f050d0906020708120d0b010c0507030308 69
    0x19012a11030750202c010360008401c0802500d030000c0f011201802203485914040503140210084840307130480c584104082c8003242400d041c1500026001e952150100c00c004034168410b0b4000d50780c0104c02c800310180c900740d4650081141d00482500c0105568a905401e8100d035022031300714400031624001404031241009407140c0041d1014858070f00c49225613a110200504500e00f18140111300740000c0540d200d000305182d0304540103007818000805250b12801c030b106003420240e0001064010040181841c459003004da800c1611007c102c603103010a0b164050242c001d10208062302030103400000400740d0b00e05401004009082c4002d00d017001302c5404920340c954800b0b4451200480c54240800e059170b10503042d59401e180202c0c909180e41485030101c08102c60080080c401d01e40c6480b03c11358011a00d509454060303007926549a070707071001240d6440d5402d600c1e1540d1141009011000511588605042030041c10726a20494164031054140034143d0701c2617010880c600200011440f03c6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 417289937 1250 417288687 417288689
    0xb0909070515120702070501260609150904060f140105060904020a0908030c0a060b0d0201090b0c0316110109121a0a0e010f050402091305060a020703180906180603080d0f0f020d06050901 82
    0x3d030102200e509c141c040f42c962080d070141c60030b406141007070301140550304082c8101c01000310240c01c01c209400c02e03180000080c88045c0d03e8004240c500354041c4c0110a024034030a040b07410003007609080c41100000c000003940400440c3d0107008031400b001681d50414805030407488403400251000d0b0125003401401d44809005491040780701e1901400141c0c1c1207104c0d0000d8910342036486495a1412110919611078596007905044445030b10000f041203112113000a50400e980d500c0d0600c0e0744418a441071228400c00038422071f80b581e1607803008418003005950004c00000d0108210300c20300c1d151421103615a4505060315100c00800055040034008141c06c13041505102240f2503598459681b12000600700c200040d4001540380c05040c42001d01003003655203041103c0e103943c0e41e910345e80c009040a03c201100f0f404001d600c80a211024420841105d801c18101407800020f1080803009103c48107601d005256280c0500c1c0c50500684060f22214203040c50000d04603060008102c100d20f81 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 417291187 1250 417289937 417289967
    0x117270a0515160f020313090603120305090a0803130b04081806040b04030b040501090803010b040819030c030e0a0e0106110f0f030a080705040305060f0a0b0909070515120702070501 80
    0xd08424030650a03401c82c1d101c0b5032041c80d841c0110581303840050807429441740c5910344520441222001c68100c00341e62200302140c2c42a411443d00501d40d20b8140d00b6543e044a1640c11078000e41c01c0320021400200046030b004002b603250103480381c0302d584c4110070404103842c25903618901003814a40092041d002c03642140c0c02b122090308252404240e83d234030b88560300009020314180408242080025001003c100d82d00030441758482da12200e50b0a0f59400900c03c1c0403052091256481541c001d618540268580541c1c0d003401c2680b25440030350340074a4848140d500024040c10000e032045006034807501806040d0340d110441700c0180c2c000751038003400030941c2c1202c0d000343c2a50f0344508000000c548110b031107801c080d869582c5550050b0b030240900c1c3c0c400350407130141c0c50400c1504a12401038500c1030f0f0400760200884c00d100024008690011103130903416074080d440600c5249131401e120b01e42071803607441c0c4a2508400481c800311a01051b9032101c00359220040500042d1f8001d0850481414 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 417292437 1250 417291187 417291223
    0x8040b0a0c0501050a0b061e0d09050c09010902131710050403020123010f150c120c020901090b03120903010e0a200102030f0406030b15190305150117270a05 69
    0x207030b5100003210b600c0344200b20f030654401023640aa1484840e801e50b41c0c14003000d181005081d82c0f50410f0342c0c0b912088503ca0b840789035864004070b107031075a6100b5103a80342c190561410046081c040910b0004000a0380b0301c0341e900c942004002c4403200f5000e0703035103c3e6110f6400401c0326030304440404800600c020307404070500103080052103078080105c00401200c1508c41501b80c00c1600c0c500549004030545c20140018190700000e800241d04504a03481c0365100740c3c2c007242141ea80d0500c2c002140c00c50606680e1541150344148080070401c80681070544000f000000c5505c2940c1140d854120b20060454021421030350840c0101c140e010303520321400c400c1c0055450400390a5901615109601400c4145a40c404041110b074441c1c60000001107035180c403940c0d440c038180000103560391203d512600005d061038001014070082c090401d0003404182c549008180d610741c07115402d0b6134010702056403104055030441092140d204c6142c3c40d940b641e400350021303048505005003130031409451a103500c3c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 417293687 1250 417292437 417292451
    0xc010f03092a06170a0504030c0503031806221b053613061107020603011806140328050a0b190614121e011509180f08040b0a0c0501050a 60
    0x35031095610742c001c0045000107072987d1186000d888002d82c014014002e8400841040b140c40811001403000689401c200d0f00e136a900c0c0410344031500d600e80c01511052403c1048140054038054400721910629013109000726103410214000c0c0300c0101ea200060100224210030500301d680c00c0124030764226030f00d80e1b090310303003400340c40500692032400401c0703296646a08007524481c00140c44405a00400490740e9595a5410700c41c03401d41109600415807810100184201007811541120400500640f004c5102c486440412180c21b00203040c1035800c4800250000b5420f0060313032072151060301c10a0141c00e01c11082c0f064000754000c1c4102192030400b0074803105a19103c0c0f01f540c0b08049036000710341e41050131005e04003030002103208000d60520744a03415554040d00042c03881c0400c01100d40000f5070346e02c09030003566080c14030320395250605009100420039210f044802d41d4020b00c0114506961160900500d60003001603000085180d8007000810001b8001c0c2d68201c80c0f9140c0502c004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 417294937 1250 417293687 417293717
    0x406080d140a02010902060f040302031606090b0a0201020c030a0302070b1315020f09040504030f0e01050f0306090628030309050d0b07030f0e0a0507051f020c010f03092a06 76
    0x441c081600c44484010040751031030182c0d10075000014030729805401c554913800040f6413200b40340c1241c04128840d004610385441509003c20680c1c0441c0c03015030360100c0144c90000b003042c6d039030301416070001195020414202d01d03403010001454158074075500140d642d2800e0038800e602410150081d003403a1603145d401d40c04902a81c01c24170514000c0a070060769610800c290128510400003c240c000b81400104414507420582c03c00d042d45990310741e0b20803250458011261480343c4001e41404a10500101d0010b040c101505070b4029405024000310f00582040f00c400d841707112410346801d91640d42c05000f016800b0b00c0f00b034000e240a0b110814030003030580d14844044c1c001441201055951503074000c2c886ca050b0000384d0801c5002e02034504404041c10080d03100e1a907800740034024030488086100d00e204191800d0a090b5455020b0030b8071009610044400091944011080680b60b4050b800407030001b004804a980c08c621201070120307801e849501c40d58100e81d0280d0140b005c0f2064074004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 417296187 1250 417294937 417294947
    0x307031b0e040f061d04031101020901083625030f0f02060d020412050c0307051e030102210601090b030601050d0509280b060307030f061a06030a02090406080d 70
    0x40002200d01003003c081d8901420b00a2805030f00001e1010640c4079100945040550214092400399962030462100e5541d094280d1080c00e0015000880303030b20010340d41000ca0103481c00c070b0310041c84010100c084211512052815030311907509030740c0c011002010120300720342851141d10766420b0140d1034461840e101c0c40701aa00550380078110740e0b0460540021907480600310f40d450506680d0440d160342d02ca200203056203031b801200300c07118030030013492004034030340052840200c541c0148905030004180b4250782031345100c1d40304190550740070310946217000088200300100055014481c1420b2030302a00040c0a2a426803200c01072400c1003052100e141d0b4014215240b41074110004200c40e1148150b440c5040d25100301a521414035042c2d407603c0b05058640c0c1c00c0d005014468a030100c0c0c6403a010503458016520004001c85815408032001800540003003d46000052080c10804035801c0880d00c20f1f07100320350501c4039035800204500b10345842d2140002500441e401080341c41c1c1083e0010342 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 417297437 1250 417296187 417296207
    0x20f0a021e060618070e040c020708060a020c0d1b050709050f1303081f0e0108031c050108061501110609070914191e14010e010605090d030503070201060e09030307031b 74
    0x244648134000280a07502640180e05c03882e4005d0300810040881c004003d4441000b4068060b160042102241401040313000b940c0c10700840d13101904050310703950f5055a240340c0004c44a81c04494070301c0681301154051141100034840031101107480d00e04402d80410840e030080c410400c0301607016015000caa841039425034004007100d05440c6004032100000800002a80510494007003600007050071240880036180e421140601d0700c0f0a07e00080028054502c00d0003000b0f000c0c0c3c081c07000601200e850b680802d0040310117040a81c0c0d4400c0582e01a410040103d80032500d5a0000c0d0003040000702a225046414464070b00508290800400305080d52020300381c0c5840d01e40d00d400a5004000b952010409504140d44040140c0701c5928078080740c5100920483c1b02d5921020300004107140030b44210382c3d0540c4010403c026840140d41c0c1614a84c00182c0150115941c0d050041024822102c00b03c0c0504000130003503499103440e40c00101511580503248116000e0000a403a11a8100302c0b500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 417298687 1250 417297437 417297469
    0x902030a0516032a090801090c1e0305210d0207030801080f07120209090304170a030e0a0b07022b0f060b0a08060103150b0d150606030c090b0d020f0a021e0606 70
    0x24407002c00a100440b99417000c1d40140300b26504c7c04010700c08005603214148100c1c0d5a80c184c240601049032028200c2e020148000380c400d8001c5080000c8001007440d4500051600000207410044001d0020080707802c40c000803408185150018040214100084504050b4030001000458182020740950598021000780102c12607000f1030141c5609000760b40107000440e00715200441c0304011150389004500c1c080d0049440401400d407a403c001d078440c000d80701c0c04080e0a242200070750034412041d02c8406112501d0308010a14111614001c0300108498020415a03081c801c41e0f090000884400c8000a40f14a11810041083d000082181c5044a400000c400c02c0500c56580a90141104802d030a51100050300c41208110031000c044c10196008601080760360f8844009804039a0450398403000314000361000c006d107550020081000b400041409810020007401050381d64202181e5440503030030110741440709400048648000c19100c030002c1a160909201080d407030b201c401e40c09 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 417299937 1250 417298687 417298751
    0x18040204180e0a06150f06050a080106110a022709010b0a05010c0501091b0306140f0612010207080708070b07020705210a143f0309070902030a051603 66
    0x450b101c100600c00407074800d8000c1d0b0240007010031500c0031000d203055801594a00c881c88000812140d11031020703603a00c0322468a401c00b043e402d0020595003c001c0c0070650301544078030310780d40700140c031801010184010101000180c4a113001c01413905114000d2800c00d09a25040030310800d6501d1481d40c60481c0d10a00304000c14440314100140980700c1c110010b0444511082d184620040488124080380d0103498200b210804a4040d4081480c0c283c0d0741c010301200d07902c0800c800b807404041001190a07032400040c6810003e9982c0080d6410070001903e0282000c2000000d0154030211141d00c04054405440c4203410500003480380703903001038103010390400b606104107084420031406110b0358100f007800e8010291074a40b1035461004c005e50f400201d08842d100610a03100c03050b8008800c0a003983c3c0000801d20003903903001500300500307601103031007804800528002c481c801075004141a4201045515040e810400c21402840e004010181340100c8416160301820380d481421034070f0000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 417301187 1250 417299937 417299951
    0x1030210090f14120a03080705090d05070b0c0114010305070b0706020f2802210304030306050d030c020301230a0504021201020d2403441804020418 65
    0x40760030710902d8102801103641c060020800c15034440c2044408041155109400790859410316141d20560320024081492500812410b1b8010405000d2040001d49500d4031a030507a21558038012869004a01c00350000440c814210820300524003043d140a060300d001d0351540e540e00c2d968500510880311001004610300c0c040002c43c0d011900300754906120240c540005040d5100e460b007a00b049a454107030a0a1611885070000c2200e101c401c504000e8010002300c550700600e0150300007813048040641c0d030301001c503581e6200f4205440b1a406542c85003034068042c4107141c00c403801030004e8220001c03505a0803900310110704074107600100c00c26000c070701c0c1e03101c92000c1110307000c4040c14000b8035400410740c40c5542e8419440b242004500c0320f140c880c5070403c0004207034110181e01000d400d9029a4500503200d00303084440148803a0440c080e4045d5120b2841e4110000c1c0558403040c4003800001204540c007400001144400241141d00714a001c0c0303404c0482c0e0807510b024140b1600a500c40b20 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 417302437 1250 417301187 417301219
    0x1b202a06090d1104050a1503021207050406080604120e0901170c06031807140f01200a0b0f0601080c090d1b0806010608070201020901021b1c030e0406080c09010302 72
    0xa0340d84000d00546041100b07425460b00500302c010503008203020390302d0b2000040c0c5082c00c5000e0307001d0200d6a0000b07440294107540030302126010481542410f0322906c13100145c0742e16244211001006150003030402c0b4101031800e5020440c0c044108420030494450481e00b69681c00c07032050444200c640a0781e4400e040d0507166060480041e80c40d82e000307a010040003211452807098205500c102002e0b038940a89030b51503000d819402040b881d401102904240380594018512000c007010646110001040c400307451034500916440c0460340b40d003070b0b50180003403140c4250710302d034109009003821030003440c1241c04030003103019441803d84910f45081c16907060018500c645000c104400849403101900e890902d580c440b000c0c0701d02030000d01304d2000501590b06c18070076141e000310148e01411150108488511528500e4100a98000d2019540300b104800d41090302031158403035110402c4082211081004440103079211458507001181c140c1640d603580707955070b410b5a60489240600c104001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 417303687 1250 417302437 417302449
    0x507060e06010f0801060609030b060103050c070605040f0b010e06032d07080304031106040f09050a020d020316031508060c0d150305070306060603021218011b202a 72
    0x4028030516015410000c140310100f008404103540e2803800a0101075943c1c10121400d03289440f02034600f862507000b0400340d41c8070f600401d400007020b0001e1070402e0001d0b03c40e041258400c0e50102c680020780d42d00c0c103003003281501d566801071014015044030340c5498008a92210f011550394412041030071128102c00c0c1c074071404405640400022222a1030700c41070440e940394042c0c041034600f440d0b10800180685088812101901d00d80c054003441a4175044c0d00300081c08000d4161440701d40c09108411102a5034070240d403044e1406442e840d0040015030019044a117051480c0720913006003a410b00103080300007080c58108254103841a50380c1c140509000c014680d1000411a451940b0800018407000180c1d078800da078051001041034940d2507006504a11404d280d0762601481000020300d80c0500c00101e100310502d43c0f0003c103109a400e9003084c4054001450180070498101e007a2400403041c00ba2628101c01110080103e401c80f0000c4409c54416034003074800700d0300040e80500d59502c0315 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 417304937 1250 417303687 417303701
    0xc0a03030b0a090908040806010f080d180b0a03151a090d060617060f013002030109020402030c12090a0819020a02040f1d0a0201051602010306031703180c01020d050706 74
    0x240800c116031341c00c524205060703920510900382c1510403000081800d0a0740c440b1103040b036071114020f0900352040030b01079900751760300c0c02c0c0d2000d40b01d4143c01c0000e80c03020400c001e280080c00c03a0790004081550035a980450030a0f60020300403044130398a00450900301c0c10840709001e50466061503852241c0c500030b4080c02007900201c400944a0440201000340010003c0c040c01c511510b4006581c4c88412605a80b4206451041c070030503d0034550060800001128a4041c000340000c151407442e50042001e030b82c800da80c501d5040d40001988600c001740c1c2400311750090142405003a004545459a4250340950054150128440c00c548500c03e4000c112030b02c491035000c0c0c41440390301e03003180c041e00080c40c0401110079418007403041115410004101800300907416150142805000b000450f0501513642081b8141075403100040045520a1451808903c0c80c07050b2541c0c1c1c4c5801241c0524050700025185000d9000b004044001e0b030f000f00ba0010140c0c0540740070b80c1c1390304080c10208058070741 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 417306187 1250 417304937 417304949
    0x503030d05180f0a02040f020d050c19081b0307020f0d0807080601260702100e0d090506041202090a180308010512071802030411030d050913020c0a03030b0a 69
    0x19840403801400e40046109005820b1060b116494405507691103070301a044841182c0c01820112005240660103000c05c506110401800c06a02c11102c40403107105681800040c500880c0801004c03542c00040c2014104174070702041c960070030030201c410b0040ca18580340c11200c808400a100300f4420403d400042d0100012920340300c0f80034501426803901603c3c500e00007811000018904d50140d1984000312141f0030070034800301401d0a20208605010300003c04600581524000418150186000024986014108000341d10ba0003601c0c5040300c5d4002ea0050300144010081444601c8405101e00d4059036a0fa20551702c840c1c9250080100c4c980c1c0300c1c079035081e50800c5c00c14141c0c002e000d941643c6050354204844e0b207071410140ea84585030300ca50707030440d02405a0702403406081e0300a143c01c1403040c0d070b4141c5000074460000b070030547c4c50000800051408121b5000c4d903d040454125161409141180b500c0c104001c9152120310b0b00318054103040d20340d482c0d24640e8a0705030b00c0e0401032103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 417307437 1250 417306187 417306193
    0xd0c09020d0635010e030403080c0c010903050a0803070504030c08100e06330907020d030506010311030f18060a0902120303130b0c0403050712020102011506051803070503 75
    0x921808014000e410180c200040c05107407280c04105605098a14961603401404403003ca81000502140f0074050120300103155485407981c40751510104003600140d4401c036290b94990941d0306a4919215005481e141085162a400c201003800460001d030004d4200780c100f59690f0387c89000b580c0a00c501d504c0140801011207001603040340200d1244401d1144036418044611b400300700c0d941c3d408040c1c81501300c00007440c105c02c035a6440030704031119aa101d818800d400300903d500062040c4130032070390000503801040d61146116071510519520075000d09041080902c482802c0c4c96600004000d2140300d84580d022840008103502d52013020b0800700c3c11140989040306040d0701418950034228001c44000d0002262a8400b1055078032840c0940820b0075181507a807283e44400310040c00600030814100030100210348240304000242c600480f001d41d540c015403000a00311407443c0850b010300314660300140800e5030300ca4104d0b52140304114013990500c5100c00002e051112aa00080d8148 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 417308687 1250 417307437 417307439
    0x50f07050c070f1202010305091216020406090f0c08010b0a02060412211e140a090812090114070c0b0714040f030507061b0822170a0204050123040b0d0c 67
    0x80c494241013140c0a20030fa8080c000b50721582d198558901d01c507101c1d0b1400300000c0c091144000b00502200c0020741c001800850050b681b00503c40131541c008030b5040c1c80075180c02003608100e800c035070031500400c030b031026030f5240440d86103009440c0c000280000700f0181c401b20352001e80c24441d4000030141d080c00c0c01004980c00f07500320324000400807500b00e030380724040c8106468110340040c41018030303050085803900295a9001030000040c8040601120400743c00d1241041c46020108600d00c60320980b00001510b08201108958041c1c00801040c10000c001010341d0008070502c6a0325004025402d045407100c25105e061803090227550403441152603080c00000600400103034410845000f511044a2010100e9035030f4400d608100d4094405c000801c480b222a154168581d425242d001c59200806500c2c0c8900c40340d03c505501c1140005c1d1b115039181c005506d4544034060041c44245814201207d0100000034000117558101d8403a0ba615139480102d034441c03d0301055095801101c0300811 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 417309937 1250 417308687 417308699
    0x5130b160306050105040b072d050d090b0906090d08160c1502341502010b09070908210c030a0906120b1309020a0810090312050f07050c070f 62
    0x3000042040c0000303060400c00076007035010304211400c2d9122800700c545443d010740c0b5041c040240348041c000b0703890b082c2e0042440e24007016400c00c170610b104070007914184032402d0000700030b00c000340c1000641c5071040041011641d2044126650503405444040612105080001441c003641c440c4404111415034800104001d00e403140d4152a1f0084003015080c030041401c036903c0c000d60101220040c3c00c180990b100213029140c40d040701c0c02c401460104c0705c1c6c403218802080b0030034400071b40150b911550080640e01c2c007030840c1a0f20110503d4580d0001d0319044080c0d568141450210b02601c8070303510303006c02c01400c860459a80d000c0b88003c0b40c2c0e4800000a00800c049001e109200c00101c504104240c1003001d030107184980c042c02081e8400700380c840c1108100a01400d48200d9019024020008110b90305100c610045048003400181c442c03c03908001c1d1600700c0c1e80c49071544992800040121049a03140d116802100d1894960740350340210440b6844c195082e0051321102c1c481c1c3d5000503803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 417311187 1250 417309937 417309961
    0x10503180c06161b0f1e08120304050c0114190e04060e01030201091208030f130c080c0f03010509101121010317030601120b03390d0f030305130b 64
    0x721610a110b092010384481000e03844c0c100c503038050000000c0a5510070072180c0214051744115020006250400542d5203034501d20b440311034184110b94003000300030002803000502610000680a00300881d00120041544056210312581d00c0042040000c07881c0206105006110b59218041c204110094841400d100380c00824441240001e00c056070205200c8407940e40e251116038424040c5081d51140450300d202c41a0041070717100780320406441d110104809503881001414946c0240c0300c9401c0c00014081c2001c800141c0c14041d80c10481445501e000019110003100340c2039000240040880007800c0192190210100400b00702010340d020449000003054102c1e0311070301c60a07100e03075401400e1101d20f000440d0411b01003403507882e0009003001e10360410034032488002d0595080005045502801c445552021040700c040480101844c2c41e10003e03c5118040440e2501c3c04d025190380e80440700f44050304010101070700c410200302d0140203000b41101081d071052110300d9518120700c603540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 417312437 1250 417311187 417311227
    0xb04060e041e0b07031a031501050310060501090e0604200a1e08041704260f1603080705070b040b0c25030f05100e100507080105010503180c06 63
    0x15070200103507140002d050300c81c01c1c0c03400c6042d80228035003000d5035603841c00c0d4004e0030450624448071407201c81c400207940e070070b018031900381e0103c440190041d4105003e15150404804512401c035103045014405a80c214842d070301104e0b0a00824600f41d515080842c000d07003208110704804007070804040e01004420800340c03a048090b0b5407070746450300318510700c800d10b282031102c200086101c44011070040303500d00381c48801e071445100b5070030314059035882c6450b20340d28070a098010452282121a8103800180112400030010400801c1c10458240281641702c0c61440000c02ca01400940c0a0400400744a03440080640e5142103407501d031b460032881c24941c000000884103015480101300c44980542c1c0c0c0411070100ca40b500c201c2c0070304545c0d27000986000410260b4041c442d65104101c04811401aa0141401030000c2c3c05032450351716640c020f42d20040e01d445c050010369401408036036400003c4e01e0b401540c581842d21500e0846800c04e040906404040b904002c00140700c0269855040c8065 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 417313687 1250 417312437 417312443
    0x30a0e1917073c0312030203040f1407030515011a130b0d0506040f050709120201020a2001020d0201050601020d03021b0d09081207020906010c020111060907090e0c0d0206030a0b04060e04 82
    0x158030a030020307404203011810340002000c60145c1901c1c04080341c801d50185520510a80d800800d005c4652a042440000100e00822a500c09003043c010400d0601080c1d0301100d0784841c4800c1075040000940b43e030b44540d1b000f0800140c01107903880003070301e100d110f040007068110381c03140d40c0304600480c0300041d100c01c55540b401a81030000361400d402582c8207942c40340780d16030764540e0a2420804030842d000340b890005e90461050b1039000c804285898502c0906600000d0407142d4044114006810807503050f9520041d039150208015660340c000ca001d40c03154071a8540140d541860300c03034155100d034030b031001d602d13507171081803c50080c66801104e40c00a554215045035200104826219900d12810b0002500051f0407004a042c9500400c3d030f0420f0b642c4141042c696442005d0030013468141c007103c001c5060782c0450010084490684603076100480c0b84409070420040c00c001141700d210700d0040090140764004005000b02c9510f80c000c0c003021500810600210750344502c04040c40d101030781e081d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 417314937 1250 417313687 417313769
    0xf0b01090212090c09190603020901080d08090303241216081204030224090303030f06010e01030c0c0f0311030403060219050909191b02030a0e191707 66
    0x101c3c116100004002c001014028440340c020380e0f40010303c5481c8440c141c0010803c5465400c00300069841004aa018189440c010541c0c3d46065000500e80240030f40040d869070010001d2042e80311039001c1c400d89103280002d800e030040c1080b0b40443c10540ca08501007404d4014033613401480e654403403099007200c0710700e4202e400d0f0031b024012048891142e4840203500c0441c3c04a0040340302d110081144541003581000303428010000042410340d032044a101c94500c00420822820b5a0400c110340c803080c0c002c0c03804100c0c8145081c40542201034851014024216445a4600305441054024034031070441c8196503d81d540e9141c40c1e0080e41103800d81541c0f01c40b51001c1511a24451340588540810052080401d40c4a00a41c00c2461103070402e06420380c0c0d203441c00d04214000070030b000c80201070701d98011a900c20300880c1c028240c0e07013a0264075201c0c2d5007000241c810740740403c180201361481020340c0e500103003580d503c1d00c1c50002d01c1e03800307040d0725000322001c58000380381502d500106542400d41 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 417316187 1250 417314937 417314941
    0x80d050f0601180b09010e0607020307030302100e030f030103060203060a08010615080a0c27030609150f0c08150117040f120f090b0d0216112e03090f0b01090212 71
    0x502004500d0350041404400041c00044103a47c0324100c010910000600310b1450b1119070b80103e070601e052904160050b034401241125001114401c9520092803580178500300700c01410a2484c82c40184805024150080049026a600c1d9008080180003410081002d544d50701e00510040d4461000100070800c18070004480d14141e010740d00300c1c84500d542c0e620700411211107900100041d044003040c911070190003c00010294400c00320090b0040b41001c01d68440d280e84402581d82440000c500c0c00d04201621000c5900300c0005074028031300010b05035910050030b004862072140107104c401480400018441231214540f0f907111740074010310001c1103813100b441c4140c80c501d001d048210300180f16100108202c3d0441009441ca42d14010300c09481c0c005100d46454009407a680d0a9817020001d42c0024002e00c1d150b805056544141d0340e4410b00031071042480c0781c19101121902c03007859101c0c0700040801000c556140741d01c80d802920000302e961101c080100030b401002c20882c0034500940 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 417317437 1250 417316187 417316217
    0x7140715170103021f12020c100e0c030709020306030109050604080a020114160507080c03030a0c09080d0504090b0105041802040305060615071203020d060305060a0c091809080d050f0601 82
    0x9800790599402424600303620000490310300f000d421505a400c1040580d45003007410340c8160001f0010035929030010302103005414070104c00c4503401c2415079035542c0b10740b55200c4151004030340c440440d21149401601ca541d04d00100340902941c0400420358010f21742000200700c00300d409080350b5007696000b005003108126010f00303d14029103429444400880291040d0303071196008001e40c5100b541034604100b5003c51441c03a541041c0d0b40079420944a912001c0429400341c4218000c0010b00d000f0128045020f002814510450145a41103038507003a442c0050b9001d035044034020304029003001c480f8064580b4102c002c0d045070000310341b90b000359000309170a0718190a140021505410310b40340ba100140d918860f4050103c1c8044050540a00c5502c10a600c50701c0392600940c019070180090b86000c00b9444100c80e41d14101c00f090007580d080501404032156030301102c03000300e00740004034190282802c035147d002d143c00d007a004074188410044008001d02c0300070700500003a21002d14040c0030755 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 417318687 1250 417317437 417317477
    0x1060f091509020c070b2d0913060501050a1211040e090c0405071e0905210111030106020d050c0102042102040e010b010503070f170a0b0a0902070f0201030207140715 73
    0x4407202d02a070008400740404031000d03004007103086084045030b03406d4a808485801d107c180000700312941401144110003070a00d0006070090350690401013080505010002c0c00714002e06601030100400050107540c9a540d90344070003d80c040c80c4401726122556040c1c9000010400c94250000d80915400c85440d41040d00880d40180c1c2151520b541c0c1c0b031110365207006005c41c0c040980b002c0012000340051540c403880348000641c642d10194100240c0c0f10540d007429940400000b0003003210403c01081440c2d40468080f400180700c0c6081070340c507201c142c1082c0c0a802280c020408240c1810701042203401d10740b400813002ca1003641e09001460712410304608a50758164520302141c4100009800544118040c1c2c9403189242007601507a1254040801c02c000100c50000081c0d81c0c9071400c5d42249052102c11009002c4514103620780013050351114019400c2410090505070046030407020411881030a4050391800300c01c803000c4a641e00f5002c501000004004004a04485405c1503001108 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 417319937 1250 417318687 417318697
    0x329010f0e01091205031306030e0c1c0605091006080307020f010503100311030321010e060d1502031302060a020109110a080a020f0d0b090c0f0109060215040501060f09150902 77
    0x142c6500b81814500003c1c000c11130a00c1208660034001006600e00c5219641501c0e0041e00752564005020582e0305001032030120920803c034442c100000581e03138090803103944903004640c0507801088585505055074a04482c914000300000d0620700d003c280204004003500d10f00d03000308d0b00384407582c103a14015520362005031030150b641c1500e0700080c4013007034075025148092240982203900d400070801c070000c4140c0704025242c9400281000400c91402025502604000100e5003c4982400c41e03855010300c01070300c0c0040c07400315004030004100340d906141894400740c01508442d507404003800001c0c002c00800200f01c1d03d042146241c0c0e000f41c1132900098095820b408010811103220b9001c001b682e60350701922582c0f140074a410000051418043c07640500d0b0444c00400684c41400d0400032451003541e03140381003102e141010002a940080d11001804003d4042e4402c0e40319410030b00e0141440e0f40141714000c12030600040c0503c555070002059410001c0d41181c025111001407040e4130176 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 417321187 1250 417319937 417319939
    0x50a0501060807030e1c0c150605011e02072105010e01020f07060905031e130503120409330608011202060702013207021009051e010329010f0e 63
    0xa00800103240c0d50117a4041e041c05507014085030100c240300e04003d00b1841d9241e00c0c07070780010f0700d9110b68410445001000e0030384c040d03800b5003071201d02d0404d00000c14040b460180c121030100c040c01d45080b801d000b4000340b0094402480321104400b40c0106410044201d071000f00c580d03600e0201c864200080c10300c25540703030f032503181f90350340ca8610075444a42c043c2110350030540e035a01040246100c0c601c92910380a0140d590307403901e030b52506e280f1010845610301540c08240079801c08800d45030064507800071101640c500c00000240c591404101c083d1700307503200001c04100c0003c0a140551032240d05065070803100c0e02e55a5655036a00ca40e40590210240c0c88020341141082c02144010341c09196030246c02544983e54660100f2291420201c0002620380500000750000b00c10b4203504064141e0401c01505042215090785048040769100b44007920900703a21001c5600d0040d075a1080d002016042003200d4080c00c20030104108000303008075000441d020a000074002581240074044242d10000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 417322437 1250 417321187 417321197
    0x2030c010f02030d020403030201140708060117040305160501051b0405101b0804060c1112280819020c010f050d020d020f19030f0e120c011d03030a050a050106 70
    0x12000055079064801c031107000a40c001404401200f01a51000c1c100840c060343c000701300344054105411104602400d440d0070403451000300310590740c01035481450200740720742e0319007682d0300d078181110a40603215a91908240b440950b8052140540000d805003d82c035181d4800f00041303068104040c0300c0c41c4207250300080d00c0121280d5007400784619000c0307208040c51509002c0c0d6183e40d520340ca41c0c043d810280101d103820302240103100300a21030129a10040e901034000c00344554200703130b5030146480361504c01c1d100b480e844c04100501074001d1121540c0300c7c1b180c1d511105005000c2c0000340015400c1001441802060080c07507108004802055815441e0760707180507084103110020303610007118907440ca6000c010201c219034100000f01300d050060b8a85022680c100740c401401d41d05182e0000d1030b45800e10900560f20a0007040c200b0b818440301c0e185c81e9840301e00d89403460162841094100603c0e03030324100c4001c1f800b00800214402c00c25050104520350b100720000302103e030280102000030b5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 417323687 1250 417322437 417322453
    0x1b0d0206070c0e010303020d0206010b28020115120b0603030f070b0403180b0d050718140f031e0f1504021314070909060f08030703140f03240103090203 67
    0x2080a80080400c1c5002c0d00c40071803226240c400c881c42d6500c00b80c0c81280180d0002644440d00c6505110941c003400c00700201030f1421325408122110340707920f400b995442c200707100ca2181356103000358007600b0074203400d101d00b000d1103640340c411541c01c03000308405130380340c01900e0006150b9150100c2110410955000454141649520703510030380d5a0042c0120103120030031508803a00d80b10a00800014200000342079907890604ea90b82054640c05003880c010301842d0810303101c03011141000c400999010011020500c0b0144000501c00300481c40e9040d018000d040184022221034034445c13140f404113500705c41c3d8601c0c1d1100713001d644804400c408140d04e0116800314006103464002d41d80b950741e0307410f03010070044031a85c070706602c09405072a44800304551180c20040e20280e0300580c00284045d410800801d868030400c03544903c56101c0c000c042080d5041c11107071110100060321514484800e40589074a0f24940d001c0042c0c0740080038603c0c3d01c0d2516140c202541c4a8041c103200f40b039002d8080c280c00707 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 417324937 1250 417323687 417323689
    0x1b01120603022b0209040c03110a0602030a211b140f03010312050d0f0c2304051504090219120e0d05030a0e0a1a0c1204030509011b060e1b0d02 63
    0x52400b42a403c801042c2e030700c01e080150b030700e6810890040e80910388500d0f40d180f4500d000074828042d031107650700441088600300040d80d00070094603c500c9240c00c061151100301d204e0b19001035220907220740704e10326040c0f400c0508501d5034504207110f1107948815a4040701c0995030241d40c0030344007904114401c10001440056800b14011165031200d040046c14015214540419078840d0366200983e2070340c901d03000203e594400c0041c1d10602040541c0c41c4030f40602014110244180e020311130045a07210520300d02140e041e4221001003001c003901710344075404c0c040d4001d10741c00340c0e84074000016140b01202c0c1c0c4507c0244903503158000840000d1148a8100e0b00549880d0802003c112500360380321460446041c0521903660a0f42c4905503000d403c21481024034100580580805585c003070611411161003180505c0b42e42041e01401d01c07944400c2010012141c0c003e501c580c07402880705d00d41646081106580091b1076540d0749400740d031170070120001801803500045141c01c5c0d206080035641005 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 417326187 1250 417324937 417324979
    0xc02120f0a260403020c0f1e0607150f0c0f0503150a05030f030301091508120c0a0c0806061219020d1401020c0609010b030607080106050c0f1b0112060302 68
    0x402407103040c0701d21000365010449480907491800c1141c4001c60380200710030141d05000e082c0314150121060781075800400045025001359114440b0070101d90003c442803980c0b140207480a0550040141d11000500e0700140c0c05070200405030b080444c200b406810015004000d0744c403203042e6541e18107065036a00c0083e040304a0303807a070480d50840000140803443c0e440034032020a034003056074011030390381d4501400032041700c4940f0309039803407101c0c0702d0410f00c16054085448888200001c08840e2103030701c140ca94608200d913080300101040200780740018040004500c1c01c2c456507080b1388034500c188100702001e8903448009182c02c2c1c0001c0c201010310052030100c800034003460041c00004050f030790001c515422603025864418a0b03622100c00c100e5035270f109000341101d41c00260003070700c55800c050302c0c05419100180202018460081600321240104000301c0381809c001c81c045846d80f83c42c44161202d2001100710300ca0005500c940d0040000146001d043c080300c0c0d019008040c1c84000c080301c504 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 417327437 1250 417326187 417326197
    0x31106130b0f06131b120b0307060f0e0a06030911031f020f0d0c08180106030f02060a0e0a0609080d022a011106040b060f010c020f0111070b030108010507030c02120f 73
    0x64410a14a040600c0e22913600c200301910000303001c480140502c40c0d00c0603088401001d1160001800c12501d8641c40e2000306e5400110342caa401c100301900710340a000d90b80000c1c940100c84d0004000500019510341c1908214038081c0030b101000340a0280b1410715841d020045003e1404074800c0741c14051140080e401001e034a500da01d0000d040082c16190b00b0240c50405c091040091220800c0c00740003502c140b80420701d04541c0b0000c101045c078640d55840100c4030060044c2c403846c804110322002900a0100b40c02c0004028124003406480740380c050308100c0140130341e498a12800600c440e02030700000d6211080025000c0d01080580085c0300c4120030030002001d40c0c10071020801a20085804002d030303034020b5110300c0500400c0d00c0d210b810b000a200707658041c03504003d4070005910160b25180002281c00000707180c44800d6081c059070340e40c50400d040d480031782c110b0400000020010419072003640070300c50030b13070b014810345ca00d0544c100d03621a61024004940c910410611a0410101004003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 417328687 1250 417327437 417327439
    0x20a0818030918011403030a17040201111f0c0f0206060d030903051006140a0302010e04050c0903101406010e1507060f020c0c0109050103050c0f070804080604031106130b0f06 77
    0x929014100d00401c4003406021030081c0d10440c3c0300014007a030445009400e0101c0f0081d00114180f07441410024030800e66540e0040f0011402d102103000d59118030001c1844010400403250901440c02065011400c2564655900d51034400004280c900c00c0c0c07805014800c455005000984400082202d0740304c1a440803020300c54070070400070008005010b4120401c41420740041d02c03034503208d4030100d03012480c403c1500c201d007683c0c42807005030f8000d01e4503c0c0d00c0c102528000b07003d0b03850501d40e82546c0b04902000303903d0b11941000018900d0281c0140c40c0c0080114402103203621041c00646103040200d035865030084105000100801400b0b003c1c08803d402000080380c145c00c00c0d4001c13401c992041007003034419002320381d8000340781d43c20000c0e40008000a180801c03883ca48215203001c01d0150740700708500004002118401d010310078068401401042c0c042d1500c5050a1030060195540c0400381c02d560300071080000c144200c80c07005401e84982003c2500b0382035a0b400c0d107825140c03030001d21403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 417329937 1250 417328687 417328693
    0xc01050918060315011502071a12091e010605400204030606033009090906020702060f040e010b0313020d14100518030306030714130905100609020a0818 67
    0xc4c0505110080840c0e0080c200e83e9085d01c420740240000070704180940c1c028071340c004c61443d8601c041c00030b00e00403103d1540c0144800c0d102621030000c0ca83c2480d110526103d0040d0581303000c201411010350201003240e4044401126850840208002c0842070a100e03441c580a6102100340d2a00005107802240107a440700500c4c181d1a540c0314000c0f80c4040d0004e45020154040c500c400d00060842003480b030780200000c0c1d0319403486042c024180300c207500132191081e4894004204010b6a501900c440940c020710072a16410407900b80c01c2285c01a20624001642140000035601440800c0720700600074031308804034101140d02400402d4002040850744d04007951007001c04c6d580e01740101c0000c114808400f003914180701030200e9007014114070103040c5820070014010309035070001d00c1c0350461b000b2005c1c2c510f04404a0000076440c00b41e030030400da141c5041540c002c0800c031011030310020480700b1000c01c006082c1c840c24008124010300d1807020200d52f000c004503591600002619200072000421 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 417331187 1250 417329937 417329953
    0x50f01090b07122d030e060f010303110a05060a0b0316060c0303110909040b040b0117060f04080c070b0c01060909021e1c061a010203070c060e0616030c050c010509180603 75
    0x10880401c60113403041c1004640082c441000981c140120100c5000304070045c80b00c2d05100075a0700c0b449106120050a10038030240c1142c0c0c406c020b0014040d51f40e040403e5940500e0490030b200064022518034034800c1c0140321592001003910a00303502982e60700d5845107080c10303035660250010104501c0e00281610b09020b4000f1035512480794a220750321804941040c0d0a003032402d121139490603049015411000500085841d0001614a0744001600203a8029032218189500720348a11840d000240c0240ca001003a01c0d0243c0006241891242c0300801c105644c0303090b404122081d03500000e5100743e44403ca201d0120f40825181110f00c001094101a03045101d0004507170402c1400890301c003912030350144041c50007804e50504c403140c203001451820543d6664100000858060501032200c10180b00134142ca613801560700c103407002200c6100c10000303410040c00c1c22400345000c844034840c161f0090380710b520442c00d88003603000203040340c4014681224041c4412000030300070341c2c05104140c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 417332437 1250 417331187 417331217
    0xf07050f190306080105070e01081e0903030106080106022a03070503190c0e011a0706110f030f09070b160609060f060f0b030c1e0d0e010204050f01090b0712 69
    0xc148030850310704035611100041c08040c054848580c45030003203924010800c491146c124410301c49946d02441e2280460b51003000c1000c04010340001d00001d44004010440c00e407000000460580305907860b800d51aa90f1203030100d0761280000350703120141000011840f46103224422540c0b5115004045e140c4150710f4030007203840c2c042c0e0201100b10004850000609024446414002a218258142d0700d00d41c1000842105942c101c0c0c504400c0845c00030303c0340f080c0100c80e03100c0040c903a500301c8042d96941902e140da01c600d1b001a1504041d04005074082010708100050700300c105c0e200300030150b0510788446110303c1c2941201d4000e8505549070b843c2540040c0c403c0c80381401e640c1001c2c0740018400d00b08a800b0100030303ca6009840602e4042080c420300c40510003e40700c040b1101c0840400d4030303103820248045401007110303d01c2d003113080a101d0b0107905d0064020f001521010b4a0b02c01400320305c503004448000c85403140415400040103414089010540d40026520031410640301507041d00c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 417333687 1250 417332437 417332467
    0x106110313262b0e0901050910030f0305030a0c031509020d0204181401050913020f010504080a0606080111040308030f130215130909120e150c011401050d08030f0705 73
    0x1d9600b0b100c030700c51220100307110f00b001c00100944209860b2046110ba0302c40c02240ca00070301070003240d1040d041c0000043d4580c1e12a43e401c0060b5600000c06c2e20070708280e00d005407140d0815290700e2109400c00340301c218400d120344140700301d091110315400c00b0303d494140c0707140c020b512001c1c000345c80d42c1c1c08000100d020440341c40360305040401c005d40000c110036202c44074800000f040c0c100c00e10030782d4968148680108001c1004110a8041315040004242000161014130a5602c584a5400391050040500160754000301c100c0709040000d201490f0040c120000c28451400002c000d0541440410810103080d4115030780f020350029a401258040c0d00043c08200b540f409000c14884006005460301c69103034000c2c4018a070f4003000740490003c540d510f001d074080d0303130f500c00007007004006181c2c0b030301d41e520090b15225a16220a01c0d54840d81041c1150281805580c045803407400000000340f40c0c100f0007a402e0650b40c01480e0310b820361321400240390b02d40c40040d00c0d10781007082c24001050300d01428 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 417334937 1250 417333687 417333703
    0x306080d0207030506010905060907050c0106031505090c0411121f030b01080c012f010b122d0c0126010605042111010e0406150305010611031326 64
    0x307900140b82ca00e295252203841d20505030400d00d65141008280142610784241980e0442c10500341180c0b0b50901032401801030a566201510514075841503c50003003040e031001e40030340105810b40b0302c0d40d03180702c0900094918052000d0305503103040111415040c0500a6150801c507412120030021258040c0c81c0c46a10f41c681080c0c2c2e498152030010016008108072030900d005083c00d00c15000c900403031440104003505600551f203002041d490b003460b40000e602003010700f4001406880c1000744011141c0d56221015a500300e0748000504811514028203003001c404900e01c402005480c1c0c40748011102c810b400750700381750020707500c180c824069100442d94501910b466610a51120301d40001f2032100300400c424200c0c030800c00c018100100b421071280c1d43c0d1008081c28071400c5541c003040403070014070050f4040040110080d1070800405d903da0440d504841c010760f10800c0013450600800d440e40708614141c200c10079516400c00403130304040105e100c14005169103000c907034241c0040504003211 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 417336187 1250 417334937 417334963
    0x510060e04060b030f1f081c0e0a0b090f030604080316050403060203090307030801050d02011202091210140612031c0b03010212070810030c050d11130f05150303030402040903030608 80
    0x8400802c80003802102000f19000000007261009910f803030301f01b5071144000341c2c84101945012210560050284c05021440c110180409842540c0d0322207000e05170b00181e054030321036810f081c5190218680015803500540c0c005580b2071840c4c5680d40c10b51344030b002084c049818004140300010220308203101451041d000391025580e03600781403030003c00e04078058004034400c3d6038408000025076030100c0301c018018500d94005a41e0a404e034001511100e100d21a50441d11580301840e200540300d0700030400c2d4001e003100700c500c0d9440304030070404008000e5640100319441801081c04240c04860500501090003030f00055260484001c282a640040310080b05100d501e014002d24a0b840004240d0001c105000600203e066540384601120315104203442055000350030340c11302c84111032410705444020030721000703c1c89201c0e80c0030140441c07246000201c2d2814000032815240c0c054000754588001f0040c3d403650b6116802c110040902c003509504069035902d0103d95004100225501c03900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 417337437 1250 417336187 417336211
    0x201060308160209010608010311040e1906140603010204030f03050f0d09120f11030a080c0c0f06191b0c060605060c03120a0b0d0308130503120610030510060e04060b03 74
    0x4454011301c113083d00180d0040c0100f10400e0010008285046002419400200c80108504c00c1da800c0c2c05240c00d1040103400381c280741e098a40820040c003940300041d0840c2c0010001c0541c0da9600405080340210321001e449456220600d5000031312400c01400e8140301d1051240c1031060413002d0100300c0310141c1d400c031070801140c010108069009080d100c1d41101900d000482d94849084e003580741d0041c0074884051041c0350b00454410040041510100c144120855017020846000300755189400c1c0c8000c010305c0400c0503000540962406656245000da40c0341034600388400500f2219100701c04003d95039a992010301266584d40e43c001040041d1007003008503106d03526080a54070342240500070300d400d289014600070440d00c0d81c4503d0074266030141000302442e5034508104e0b82001d80c81200508901000440444140c0c0c8480d41030f006280581d40c55004510116094041b90320075030741e0b0702140b510114108403161103407002c0380d45444080c101050007699000c1c0604035400031f5440c120505 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 417338687 1250 417337437 417337477
    0x51608220c1d040804050609010302070206070c0f080606061c1d010b130b031c020f0106091a03030a1e120501032307181802120705150a09050607030201060308 70
    0x14000042e8201040345640031446503041c2a0b0f1070b031040384114800c031800341c074001c40d0320039450f8080c0e41a02d1545401521a60744e4840d10300d481c0c42000c1440c0111465002090b00225414074002041e62045202a180a150080e41c4400510ba107069445408410b17884c0d170014404c0040c0c5d00125411b45485100218204c4501420000e600c0c004081d01303078141e03180003041805035900207505602a600d100410135003400e8510105d00b09044005030310403940c02d20b040042c81d440554481000d07103801c00b1b44c40e0020254181019264841c42c640ca100240406954410110340d01404100b04001d500740395140c0316501305450700b698403d910030340b000c03400722841132003007054a14401e002ca1041790103003800600f00f014900100408665100106644050a11000818401d80a40c05400800301d4a15400c0805659074803e09801050300549118542d604981d68800c16200d12140039101c1c04000390802050090030381101105030f0440d1348519000000c40c81000040c03a200c00ca00d66210820 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 417339937 1250 417338687 417338699
    0x120308190e0f0115120206040510020c060708090306010e04020117060604050a0311030c01090810091e050a1401020306010e01122a090501020c150d0905060703020715051608220c 78
    0x841c2150700540d03c40046061796801030780c1d800b0850341035078030440d051203115142550072490704209044043d04500300045060a1103586d0000d00083c40b030407422600a60b0300d98032070070700c03503002924000e010407800314111101d0004c10b10095848100075241c9420030fa0349078002000e044031644281c5814480c003400c03103000c2c1824010200b0911081c200881e13480e241030144c69941d0400c11039050481c3e5141002e10400580c16081340c0f02000d6040e1090100c90a030030041d4035040b81c1601142c41d02c002d1900b1501e0f205041c0243c3e40b04038016100c41d041c001c0c69400545048144072085040c282c0c1c3d604030003116022010040d003043c42d009001082c1002c03103103000381c2044983d0b00803070705551120300f07040031954070020114207030f0803400d0105d61603030000020480a494101c4004080d400798401700612140d0582c060078415005052080b000001d04a025084a6080e10b8010b001d4418110030543c89025a0307420707800014074511000c4074408500585498100d41004a8031658000410000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 417341187 1250 417339937 417339971
    0xf0310020d1a09010b0d0603081c14090d0c030c0c030b040510020403110607050c0d03030b0109050d020d08090d0c03050a02101106150a1a030603010501120308190e0f01 74
    0xb18100224481840a2890000690f030200512800340c1d143e000190a08030400315402503030085511080c42901d070b040e0302d844003100900000703c0c00c01c800e1030034222040003203a40c00318a004107518805019005101241101c0c0b04844842c00e41c180502c0e501c5150001e241e5151000003580614606249420540b0784035007040008000a44010300500090010031000005000d4010f012240540e903070b00c052510509007200084801d5116003260748060034550540c10800301d444090b61120441501c03403040012040113890065003005408110b940060701100041800403001000005107561f503030b40c0c80803042d4254100726000d4108031009001c5041041c071200642c075550401114840e10386694030382da04c00040011086078a06202c12003140c80d00d504a00190074a41c2100d846048040c4d415400c40c0d0090302d05a000e0f41c80c040001620908100309122169403607540e84004e605e83c0041240c442c4d22070041488655566214944020010400d51120389c0c892400411002c00b84052004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 417342437 1250 417341187 417341201
    0x6040c06180518091531020301020c070602010f15030210050f040305070e180a031206080316020a06260406140f160306050f091b070c0807080304030f0b060f0310020d 73
    0x2106045c003206111a84444400c43c01c26210700b40000c2ca0391006800210a00590400000e90503502c0040c0da0ba10401001c140c1c4410703101160000e10402100b01c403180c00b11201420380700c42c21241d6003424401480c006284003044606460240c2c1444035600311000d560b4401d0348211116848401c08000056495008076840003800c036030004506810319281d91a0490020b00400304103098000c5191007010380d001e10060050340701100d840364480361340706003580703800e8406a1144403c2d910014000d48248000c08240c0311039098400b08001044070240a19405002200c103182c50ba190082a0000300504501c41c40c0c66100c1400319052464402c05518242070075042058141035003400035131122081c2040c2c810b001c0d6141c510780d03560540740c14104094030303031408000140082c100050000440703580080d9900c0741c06803004e107961111a02e6885c07140f0b01c002040c401080070743c0c101149040a00b164020000b4103083c6004031b00d140001c1c106031403150140600359000c2440c400d40c08280c42008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 417343687 1250 417342437 417342463
    0x609061003080a0c0f0507080708060a0e030406081504050c0a0e04050105010206060d1e0c05030f0102120a1107060c08190e1e072c0906040c0618051809 67
    0x103406a05503240c0d040d061080c0c40c2142e05009502e1242020002e001550180044e002420346c1d14040e22603900301d486104901c124a07a03485458041102d010a42c4542035403081002d004500e040c0c584101a5480c030801046503600d10725540a419483c1c481c1d001b1b0a00c03c0d0100300e001580d8480e40c0101824440c2c41042c6140203611303020050065980002d100c1c0e0300028200e030f43d016030f00c1043c07403d401e00c1c41c1e200e41800c1c000c4031043c508804018031002180c0540b407080b400d50701100c0d0346584140c202d0040040c980f00c045800008100ca04070564002d12185003008020b5142220f16210349043e100c3c58035454002442035000c2000503082802d02000c0c09040480600072400481d203459a241401800801c101040d0b5900000950041290000600400786100350100031408164100100d00a04400511041c400a00c0b0706a0105da2036101d607a00004a045c05401d1407c1211903c80d1001050400c1251407004200c036070b1030043e0813080303098180c4e1030f8032940340101c546030034906101c0c508 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 417344937 1250 417343687 417343711
    0x1602030901020a061a040906020304032c010e01091e0305010e0307050601031106120403020a0b07080106050d050405010b120304090b01050f0417010f0c02030705070608190b0f12060906 81
    0x4036560760b9010540e184616007000020521803c280c0315a4004200071080c564440e140690314030070880b054002d507208034065203490454844d06140c00503450052483e0f03103903605420481314001d41c0070746903031038074501c042c58001a80e503111500c0411501781121441148110644100200300b0b00b4000d45880c1d91a02d0059801c1005a03500c09035038030b10600009000c40d031524103111054644405450329018405c0c003061040c20942000703901c6084e2024240c4011034000005070289003d8440c16040f54040c1e83c07612710748100c86043c1401001e0252080302c2c00e540302e100b220810750710380c40403e0080f15034402556030303246003142c82000c4811504c4443d060240034003007200b186074060140d0302121520b00d00f03844494900e2680f103004001d01c00d07030000720300d18142c110301c48030360300101038034103903104100700d88009455031800d03141c0d1a0103c3d5000007444440e408a62105980d40115070030781d1010380054080d0340180700041d14003074404945801d55001c8410496a8281000031036003042a100c0c0c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 417346187 1250 417344937 417344947
    0x180a09092f0105070501090215210c0301090e011b11010e071208180405070c022103032a040e09070603050402180705160c050a060813030e030321160203 67
    0x80081111008030746141400408142e030410301c0800e40003146e0040d4002c110041c0076600d2a10304069400041004d140003d4480e080000481741c540790501401031502c4540c156840c000c1d5460140c040340c1020800d039526100d003010154803010000c242e1043d0780d22815041c1540c0d0222a08403544442c2100081d841810100a540001c920072221903402c241c800c3d541c0c2c1e09aa41c0311184030709000b40c00340c2003840d0100304000c581d408490380185078821168400520203100c40340c074100460010307441d420b40040001c00d10010740c0a4030882d14001c0e00050711022426241c00300960f4201c0d501c141e0703000070110104646420244030b0074015001d1410200302900b880c0d0085207581c0c04440c084050380c181c20f000309500500810680b03001d4000b201442140886074034103c95590000d00c1458002c41c0406004208103005540107882120008604150720100340c0702114800c003403070602034050104000039143d4154801c801280c0e01803581e0b00303040347c1c24152900c094081041c0040e0086400c2448 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 417347437 1250 417346187 417346253
    0x9170601120f14060109091502070c210503040306141e01030323030702010b030c03070311040510150206040c050a0303050a0825021005070e0312180a0909 68
    0x9503240700190040300040500c0740928046052008107055050584100b00c0006030100142d005544420702c19882d0038459245031030ba00741a0300130008014003420019100303000b9203521402568440b40745c0701030301c0d800e40780b20344506046620980060741c2d0340b40c0320386580541500e2466170301e42190000445041c00049450088030482c0103000c018108034040002d270320000c40d00f003808076403060f942041a03a80d0804482c06070003000000e1200f4002d00036080402c580d0301c1c01013001c40880e50420503003040541c9990401c0300808006001105000741c6100200d042804000e040c2c007420702680090000c1d0405040c0a02c0301d002c20360256110303607414042440025485001e0395503900700da04046015490745009041420050001e903d030034458480d82e0500c10352f0004030010024501d28080100d5251880115a0380c0301a48582e509a400030b822000020315110003046002840026960b441604100066800600b5070010014980ba0003856090000d500040c40e1924000f01a0040c52801d0071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 417348687 1250 417347437 417347459
    0xf0303040b0a03090218070c0201110610060509041b1106010f061d040618140108010204151407020d11030f06041203091104020a080f070201062702070501060609170601 74
    0x340080415458400c10011503c1b011a007000b2051840c80d4039140303241c80c3c0030080c10104469410f90010740150940c8914a102090040c0600c800c030401e4840181030400c20745032980b180c8546908a40d4581001280c29000c1600d1100d06129543c1d03200f1030209003041c145042d0060b0442c140d0403500e01c0080054030340020300342d920050080f0000707082e01541c4000030010641d035409107082145e00c0324030011081d116401084100e0919a104420b80d0325221298200d0241e80910b01080c28616500000a4044c0005030b4008031350050f207030300d0400702d40d0224030101d0400d4811144020107441c52100c5284c10721400c0c20740205840200711302c1c034007501c03581104170365071140409250740c40281400b8040c1c507500b5840a0580504150360b600740050000308032004c200c0b8146103070b5080c0d00208040c0e41c810300411048a0946140041d81d0f24102050307100c03105640d08116106500f0019903000500070f02480000301856114010141d117081d106803290340c0e02d4000d01d07080f81c1042c40144a03000c1c402d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 417349937 1250 417348687 417348697
    0x120402010c0206090a03061e1a220c03020a0f030c17072003040501090e090601090b060403050109031e030608060c16051e100e1b0613090501050f0303040b 68
    0x2441d140025a0190003c19014450070701c10980203810040088140b1909400881c40d080301d0142d01030407032010000e0001209c0c68198680c1d0440108600c141c00d81c13500f1458280d0041e000f040d104c107030710000c1d142c03003003220044014100440d40202d1001c100c590400f00d041c0042004d424248103080300c0701740090407121401000540c041070140807c0ea024451481c1a0350a050155070200b00b6100c00301b074540d6904913224a50014124442c0488d2984021003c1402590400c004103410790070302c0000c1000d0004400714030340044050000001240090054500141c080d444104600e43c0d0218192400d00c54105040e0516007400e0b0100309401c000550258440c003402d01003a00d40c0a09818440d0070140f11703134050558811200306508000c2101e226a560f01c4c0c42c3c1c0c0403100c0d900c100144500030340341000690002508423800c40340c0500d0142001b1421810018009803800000c030321107204207d15501320560341d0355100014019030520a8900c054208110000c5061906e4a54800580d12179 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 417351187 1250 417349937 417349939
    0xa06090506091003150905190b060d090303091a190507050a080415060305060702010f111801090503031c060f0b0403081b0703060b0117010807060507050a08040e01030c0b120402 78
    0x1220003c150500d101c2d5001008400c12051401300c0b140e0f80344d40090140c10152a401c01a900342111012909494800d81c900081c014001500b0007141c2010000140301102080d000c5c140c0f2100c148001600c001c41001101d116503040f800b0a0411b01e4000c00fa181a01843c90300142c07400e002c1c408c0ca00d80110035030b0080f40d4a85001980ea55584c0b8201e03000c0903400c2a20340e940c0d8180140401002000704c1c60340d00c141615402000315800800031075007170b558074402e650121401080012000505403003007010540040c188800170958a10220b85954840e10f03039803806d034926541c1d007a2a00c80d5809050300810000000a80c4241003003014407451186110080210400107040d2840c5403c000003085146281400c0d0f91656a070b904040c406400c020314030500040a80080c5000804181d42d0103060358a064000c0c551103046c190190703031035030062100341c405104d108081000200004000c10241c0783c1e10413581030760f52452030112145403041e00200304200003403240101590840b01400d40c880e030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 417352437 1250 417351187 417351199
    0x201050c0d0f0b031c17071407062d0e0c0a09020c1e010b0108060d0b0c03070c061503020a060f05091c021c14010903122301060e0a0609050609 63
    0xa07124401c9001801441901034150180500c020820040c200c07171040045240c0c0c0350301100c454420b01c8080d01d150121030200110300d5281200081c420250050481b50b44a0390f40007a4071702d03601662002450b151300c5241c51280742400700c5050b010880c044e0381c50248840000701201c240c0e000c006010740485010fa1b60302c132035000c20490306600c0200100302c80350010707007402c00141c2c58000c5810b02038843c62001038003242c0d858000c110709041041d24030b0b01d15500100300c41d40741d8070303080c0010441c3d9102910384000c00101c06030710001300c1e5480c8508080104e40001c040d20480c514814484002000e60040040c0304854581c000b14036006021614040d82c221410f00101c030080b801002400e032100c00c00780d0001080c001148031459240558881940101e00c02558003103103520701401e0b5014000005c000403080c0341202c01540c40394015030090348080c16040312400d10303c0081900d91800768081c1000601048440c012420b16200c0800640503a10b010180242010045041d0788039a00c03800340660 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 417353687 1250 417352437 417352451
    0x2030a0b06070b01080d050901020c0108100923090a15090c2c0c09030705090a06091107150204050a151206060f090f05240405031515010201050c0d 65
    0x40100e900c8100c90080080c50a03407a1031407818002c9081c4424025103820b481400070440159000350140d8844041c145d000b80140f47c58640110398246015001136512240c03810042460300c803034019243d03a91158044412072103e00e200c8100d00703070005410001280c1081c2868004605810008086084032a1012403003030b00c24a80080020200c0d0b0009514002e1007411544c4240350040c0f0a00a480440c0340750001d803180c0d42c480a2620498024950503800703448100b1503818811899540811410030018031150313900c8051040e83c1e9041e0700420a0400080c91004104840f82030206003e0030700c07800c43c18030707051401241d541505401040d800045441d61031182c144100c01b91f44000b4005070007800200e503030b014040d007452052107400000c6800107402088003002110400106e8100400001140307003440442e0320f840750750b000090344000d81000007054544040008085840c10405c0c104843c2c0b818504420010b0502855541164100b0f4240310a12901100f940c10032058508002105 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 417354937 1250 417353687 417353701
    0x2150f060a0e0c0f031905090c1320070602210405030901120b180603150c0a0509011206030b0105040e030c0705090a1814120307020a120309080d0b0a050102030f030a0203 75
    0x5000d0411074880c00e40b000020031021458240400013003413031b81d00017803100e80c541034509501d03619801ca03040c0c0c0099030308611076035010350754000c10403880b02d00300d14024030400b840c10202581d00075481942e62a0700003440160103207841446da042038840709011589800c2032b0b664961a441000000c904000340e201100010381c0c0304c1c1e40b00340c078905c074014040604100c1000c00007200c400202c5541d40309000b041680e510038480000240e10034103580302044e20f41803d0000940e8244c0010071040c2c1013141406c1d220580381154400c00016600540c0d10703641540c940000c210680e1840f42d1102c44680040c040045800b000107140004d84400f1035000e4625520244060000c01d0405110306030300300c400d180f6009000c06210400000340a14040c1c8501d0305a1040840030b03480180e603a6001a407118410302d020a06d0403c019044102d94500487c0750069605c40004903002800080d4129070394603454007551405a04030001010b00780040d50500c0308594802c9111700006140b01a1290004002101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 417356187 1250 417354937 417354961
    0x6150c01140f2401210b1c1a0c161b0909150507051911061005030703031b140d030f0b0f040908090d03020307062406050a1e02150f060a0e 61
    0x10741c40040003145c01107040c12900304090000c0e40b0080340501150ba0032400a40460b0055264907908841c040c00a800d0113240120b03060b030009c0c00401404000d21a0603004070300c480074104114000c132000e0112854200d84019840c0e180d510510b05640b404185200042c40310000030405030401c0070014196950708003d9540e0b2003850030580c490000f080100d140c8030f4100f18000042c1100d2070445d005c5568002000305002c0c0e41d4020182d0580c403140c0100000391040c900200e449005000c504038148080da1401c032100310403918003003290030400c2070030001d0384d00d8441c45c0c41c1554422014064200000c0102c0d0071694800382050282d6151098101807200010032510a0032010f8519070140980e41002900d0f03801089080300d6440c1065404118595206c2c02d10003030b29240c0307640f801881d14107241601c0c03591040c134141060200c0f1111800e442c0070b400c040e502d60620715401808401107451034841c803000d801850750440c1502c400510a407501c800e09400c0a803400300c032a00300641c442d4032280355 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 417357437 1250 417356187 417356207
    0x601120204060504060e0a030206030c07030e0d030e1306061b0201030209060706020702120c0a170c0301060b21091b03030c01020f120112021806150c01140f2401 71
    0x2045038000940020401c1e48034000300100c44540d41c0b0030040d6900380c03040000c0d0704103521001c0e50000041c4085802d0740b044800a1845c3c85c86070078039413025034416000c0b6002c550b000301300350040b0302c0c9103441c001c450400c1103603503022550b0040200304940c100700f405016221502424425006111305e14400c590181d030494400070002401c45403075081c0707490242c010394801c0400301d01500e0081e013200004540000d0316400c40000910303e001082c1450007244141d0010404503040d4464041840140c0c0c0382885058041c00c1705000071982c91000c240d08001010510710341401c0d8032403078000c00c001c6640210b0010480102800c5141b00c0c040e8440019246005070425401075500c00141c455a00b020301d801042c2a03003000140021f80da0781c0b101e9000b0307001038501d0301942000c012a403603045038070907201042e8071820080003007940d524040c00c0c00c10180c020381d0441070300e82e5440c0f02035001a030001100c250301c0340d032000502c52507213000300102500b2005180b90b0f100d081a17251b014401a07001e05a02e903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 417358687 1250 417357437 417357467
    0x3020a0311160e15030a03050304080310120302060103052a0909030408070602010902030c090f070e04020c07120615030203120f0d020a21060f03020d02040b040c05030a0b090f040b0601 81
    0x1030b4550701c42c200c000c4144420340b140c100040d2051072643c1a4100464100301494258a0303850a41d540d0340c5458116520090031b8070302e8490103040114800c0c2461035105001d0b8000d9000340a12341c154680a4600104d41c0e000e0106592040c17260416450039010691207080c041c0e03403081080d1640250f00749580102c0d005081c042c01821f20225025505510440f060b034000c4044808199000d403e01c0015041a2103252000081a00140415000f40140036440384060001071401010395106070801125030020b4014a01d0440d100c0700340141402010304000840e00d401c07001501e145c0c0001c3d96850000d4607042042c00114030344801421980035212090f4490809551712800b601c001081070b94050040c1d9403001f031300c51005103e101036200b94803e0300c441001c641c1401d41580c08108800310b2142c07007280e00a0304e403140a80c00d61280d000b1f9001c3d80d241500c86603200d0504000381025035141c03070300040c010300002d020010002110808a41c0182d009000322481d5142d98004031f6140181c038030b040e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 417359937 1250 417358687 417358723
    0x9020c15070c03080a14070806010e10020703140105060603180309040c05120709081e10060f030209070509030a02060c0c0a0308030a0e19060b0d150f0b0301050403020a0311 76
    0x4184030b9006007003403075014483ea441003c5540ca0802d82c10480312890460a46240180c0010b11690700a000a40e082401414405510801400029a905480c0d88403030f0040e040b01c401001004502d0040c14038003141000280203c1c9030030720203d030003800010030809141002c40b8900c0d07407100052088411110016005005507155420003170011b41c400c2041003a0021042c0000d100c0074811070322081075440c12805007083c0b1186074040144204009100e041a000e1110740179010082c038450705004141d0700008684051441c01003240c044001850301060043c108200401980c1c0403909c10400740d0304075222510fa9200851417447c00079204850b94110b00c0b9080040280240c0d0805140f0820608a09118060400c9829170b150603030240211240000840c0d010002000340c0c1213044c020710050071911412449440e11505c0d21003070744014090558828041c0020056400303101002c403020b074003e01144c101aa002541c449035075101808001c0820307c0f100b0000820303c16083c2d010b00320421 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 417361187 1250 417359937 417359941
    0x21f090f1d060405100b0d060e0a0b01030c0206010b0a051612122304120212030103150c0f3e0102030f07020a050a0b0c0702120609120c0709020c15 65
    0x108650381e03070810072000744003815500014014030b03040c003840c1d01c2215480100d0090078500500810583c1216003416070700c41d202d60000ca00c81148102183c8104003d403004902100e0303d50014045844405d0410115002030300140408442902103034002000c074035110b0b907140282100f071110b826110b100100542a00b0100d81c22280e8000343c4400d20f01d002110800c04c598940c401410700710440c08855220f1961413000901007004c000c0c803158401c40e14015103403d58081504207806078000d07042100d481484a650412103400c5100d900030784521403d00716503054101c0700c00780800d990409640c41e24540300c030103000504014925030b590f840e03143e1070388280c80c0e12021545020b5001202c8150303070082d00c8030000c0c0341070340300182d201c0c40c464001d0007401d034141d884d4a4118640300010442c4c4600107081240d00010380b200d400d4103210516031400340c140e604000707428605112450216090000046c04a88104a030124130b02040310065400165190b29500380309003001001d0300c0040c501042001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 417362437 1250 417361187 417361199
    0x4030519021002070f1a01061413030b070801150807080402041e05010611012a18030506011211010e0102070927050304030b0f04080405040e0f0a05100e0109021f090f 73
    0x400003c6208401e443d01c045440700300301b20b0180007480341a000500c03112010201c00c141400034040c071401480071010807074407522840001d1800762483c00020364000d00420144651030752005040d44203140441a41c10030141c01408030714003500191140f50b4a0b842c019824001458244524010800500542d03075148805042c41715105e482c40a6542849100c0406090355140112601701d019110401d0120720a000c0703464407000311291108074000240400481c8003008520f008040c00301c83c01e813100340c0c03e04c1d120101e0011070582034140001c0300700300c80d202e0381c020540000741c442c1503070300045140c900300801200700740c840c041c415113000464517801807140110041069038056035101040e510342042e405202c64007110060541e900a0000b4403040c600743d044082040040b100310350b1020010222541070254804042b1529400490300e64505200d50140e1114070205030000c00804140d9008207845136650200340e5070052056900d611014040d002d8903010b0041880c03080482c42c1c54403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 417363687 1250 417362437 417362453
    0x1021060602070803160318031e12080601120509010b060408071409131529010929130b040905060315040f020904020105091207030b0c030403051902100207 68
    0x20140e0030041c0a940000f06015100000303d58034540c612151590510709501c007190380312a24900b60001c248100800004900039120601c510380701d001c0f500600003120725080150340e07020744640f0144807103c1d00b0002203a804c0000308a0306585c1410119950392101030241c014800c0c0025030b0341c0700341c0105020500542c00501d46054840d180012880c080c091020004500360440385406402e042541d40030000304003081288184404c90030108841401098078a41405d4402910230301c01c2500c01340030240d60744568110000c0040c02420015140a00003070b0300d0a40180100c1408403000060003d888200955a031004010458585490700c3d1540c1350301d00644070a6034100c2c0304c0d12804600c800032841d0b11000d20300903903020701c041c2c00889440c0e0a0026a51009005274103025081c0807003211341d02c0303202c00d4022207016100030f8200d1900350b24082240003000740003042074140500c1004000303a00720085944160f03100b11a0344a80810060480c54140000e082c50641800420b007802000310172 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 417364937 1250 417363687 417363689
    0xd030c1401181425290a08040b1b090d14120a0207051f080a0f0e030903011103310203030d05150d0c0b0702060702040c0507051605010e102106 63
    0x24000341e400c011140602c1c01c10600101e107098400f0380c00041300b00301e03a48490b01c100804076504044d145d1807054030380001e40503422052080e4049040701d01000f0030004c0001c00e1070703030160516400d1104580d07200484111801008401806000148200b40510003c00031700012403c0e9003085811202c02844500c401e5003040d001d0001500c01c403034000c141403070602c01d842c1400c0c0c2c034903410300607220840c0011a402c0f0409000e021003aa66165101610403042c010880d901c803000008650302c0050809140c2100e05001d58505440c41c10320038085610310f541100d042d20000c0d800c107030a052009018603400040314000080d0305d803200188506a048442d000305210304075580359941c4116040043c00b1085400540c001d2851071501d00034400e6443e071102400c0c030b40f80090311032420154560b0204086400541202c00807030008a0817100700902000052000d43e110f2100d07456072403500d800a809ca0350740e2604a4411307d400c510400e0b1061082002c420300a05000a4405241c24014140010012 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 417366187 1250 417364937 417364973
    0x20702120114090105070f0503070509151b03120a0c0207080a06060518060a03060509071d06030607090b19050705150709090c021207030509061c05060d030c140118 72
    0x78a8000911500c81172041c94428003007a11609091480b6860440700c0394402006031702448014005240036031680c0c6006451044d552003030550740e4441441301641c00448000ca00c145074820401c440c01400111306881d00003034106c00100b414030b07981e10b05a050640c0307a00701c00700341d1107041c00c420244101c5402c0340301210700a5800070b50490004140881c0380710102c0d4450341000002c0000c1000800d40e503c01c551242440041d40c0030315841c0c03440303060f00b401c0d14102c16000303814150034400c15103000d100868200d1140d00b42440c6041c5444001e04180c0100c0c03d80c141440d1036080e1070b6002c207006404807101541e0003415143c41070786150711083c00c0300e0180e03503a0002920290012808031110310400c651f5a41c160020304070384a051080340059030002104808001c0c00b0711401250b901c4150250101c203d89845c05000e1002502e500000c80c1c600505051182284841010102e50820341441c949504001c070000c550b80340b22520740c00750a02441e11416600303c48c03196024850130703041030140101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 417367437 1250 417366187 417366221
    0x110702030d0c0c0e04050d0804031b05030706150315020703090b030c0a090905101a040503031207020d02011406010e0a030c0603060501030b0901030c0512010f020406030203060f010c050d03020d0207021201 90
    0x13480f12601c44011108035401415a40007401204890b0b014610700b5034082e10900d084000403138030840303581c1100d40440003103130aa840416040200700c2540200440c503000400b804154900c0c1da113070101d641007074100d011040c40e40000d02006151041003500050030441c124240d0f641012015590f513540141d90150000d005894041008800703409050300480001a506000034102008504450348070048070340b800108000025107518144040d041c1103080307004881180ca4a1a0080d0030a070782c0a1500046900d0304003041d1a00044c03068407a0031103000e103420350703084009e040442d826200726000a84900d150440002c0e0866054200030244c903020398007031040b107190f04c051202e03c00003800001d0040c2c800c201c050286003040d00c050402040350100204444207600341c4035040ba0700941102c000a5000804c0058904200042d8080c6680a10340010035107203940701c8645401c2d23030492107400c01d13800217510034925034030740c050340c0645400030418030141c006225228001d02c102084000021 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 417368687 1250 417367437 417367439
    0x133091d0c0f0a030e0a261201030308070e0414060406120c03060209190320060a0e01120204050a15091d0c0706240501080a020903030904110702030d0c0c 68
    0x12809000c89030041900304441c60034030a80309001c0b2019040075941608260740d600c0c07001c00c0800e042000c96030346406600c544150800e210440076280304888202c107800601004030200183c144410641140d070980b1348005151901a4210740300c242c12100c8a41c01030520b407108103441584a8014000d0008a5040104580d2200003d2844150f540d01070607960101c1c00c1040800c550340c00a00360808002c00c50341c1011140300140d11040720a40090b180210110b4480034030b02d901d6194541c10400444072241020760300e40009001d203956140140c1004000e4440c0c80043d48030b40c055070090302e8001c21006083e81c0721801c2220003401008142d000401042c00080c0c1ca42d40c0080c10161030008070310071b1011780c0d18901c0b550440c0d800404110340d080d07650f0140c80e2820070b0b10a1070814101c1c084440380d40c1c407858100018070070726024040960070361041200b0744040d070380041100d13448502a1404101100c04d0b82c021f544500803214040d4040c0190b14a584c1d5280d0302c181c020b00e05911405041c0901 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 417369937 1250 417368687 417368729
    0xa031805010903150e030f0403050607090b030c0a2003180301110a140a090f0602100e060915040f0804081606020102090907271509120308013309 64
    0xd031600f88000381c05228850b0341680c2841c00ca41084818403c84800c59290500600c00351003103502c1984103440c0d5420220501403c1503101c6440401407042415190941c10000391500d00ea104910040d4207005015000a104440c002c80e40b42202c0b4014043d0703902c07101101c0d00340312025030803618240f00303528114514906a4290f019100051344680c1c490a0031038032100441001d901c00b501130414000001000500301038092050005005242e025004031658605000c090300c40d10212090b903504503204121100c100000c4807140c800a40d160121b85031960f04003008c0504008001030b101520024010481e2000062904e403040340c602410280e4035641c1608030300300d000f0211110350101244010070703d218881d00721000d4005400c01030f106174480d004050306c0e2104007a4001d10032400080e070409a4681c00801e0f110080038000300001c51400c0d547c0d4020007682d814002e600f403040401243e01d40c8401241d89160030307101d2590400038090f0302084041d003450f180d446007a60100394103a10040c1d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 417371187 1250 417369937 417369947
    0x512070312230a03020403030f08010305101a0603090606010807030e03031902130320040203161404030f0c0f061110020a1404031505220303090309080a03180501 71
    0xc990308400d00d01c01d02010311904841215038807544001d56280b4844100000e1066030060803445266200107907503030301d10b00d07003c8c1c80c024a42e0171342428011000010008914045442c2d442e010801000084410018040d000500b000001107a00100040101b10bc0801c00069080c0100c0b007d03201d03400d49565524040782030b1005803030308180031340050011032000344025961034055480c0d000058201902940c4407000d4001645c0b040e5246004c00340c8100103180780d0403980700300d0841658154510324001c0c09805030f000c00581d00d082000300718002c2c01c2c00127592505442c05154844000c000c528164204111029991b0141e8401188a24400107416001ea40400440000317000030308042a18103401100070b40201d108107040c0418091012022100400100046c611544120403c8400204904100e52000700b5503007070881070038540040001c2869180c00400e0f410b1501140315a40c1d4641152039160303030360241640c2e101c2c1c40d11035400c00d504224100c88109000100014407551030b401111 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 417372437 1250 417371187 417371189
    0x80102121803090d0c0b1809011a040302090a0b0a090e16080613051606120b03010b0a090b130c0c050f061009020309010615020a0c0602010209060d1e15051207 70
    0x40716501c104001c01041c00c2225404580d980103200d821320382c0ea83c480749440316601901046040b143c4115104540785020505907026141c0c0140c507042c2c1c00400707103403026a40701c1e501010741701d038448034009000c01840d6000b1544402010300743c09005641d07214840c0c090010340300c08806a0007018802c8210207080310010007100d91800042000d41c0714454400710002c0300d804151360600410004503030352418581c41100030401640e03071010705004100402c0841c0e1104103128401e1f41080000013081c0c0d11454250103844a0003800114295000c00003601b081407802ca0714041c030304003281c0442840d040351400b5410b03400344003a00c4000d00d01c20482c940b40c0c02c01f11440c0001c11114101840044020f44c003459115503924000a00301d9207504190072079144800b000001642f000300e81008000300e5290b41d000800d4140002d60901483c1c00010780c4902542400115440c2d54051200d00c141c3d00743d0310200c00a4980744c1c10800483c0216610380310003554003030140100d0b05047c22204040d00045c05030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 417373687 1250 417372437 417372481
    0xa2405060d060e0f061501081806010e07050c160603140609180f070b030610050a020a06021804050f22020d080304020a0308031306390306090608010212 67
    0x107962180c0707a0380c001c020401d249000e582842144444603090108000d118000e2826004800755040343c5800148a010000d080322000d5601c1c80c2ca01c046208005003140c11b4408401307104d0388507039900604403101e014a104624584c42076035005d1103140d5000c4007201c10ba0320076690a0008001d13250707000402c010b00b03582245d00055000c0001e40100700402c502c428401c004400e960003039911100080c6002582d401c0b40c58240e80010610405151440c4420401760440c10700b14140542014040d4491001400151000ea00020003180d845135134034001c941d900300140104007909054041e5201054100d03011091078204001d000c1c1c220a82040c40001b59a0080020203688803d076508541a000030300126008125101e0120014a00d08044c40c400c80d00440c00440481260411005a401c000305081c03074200c100388090641c81c61006240e0f101c10030464900c51050003402c00b00c2c010500d603480745000b40d140803004994201c064000745084581100c8540c0c094481d51400d858a00c803905130704e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 417374937 1250 417373687 417373699
    0x20705060610030e03030901060501110a110d0312020c010504121103091329090106080903091212160209060411030a0903051216031a01120e0a050a240506 68
    0x30a5440c110000600c02e07141da2501155040c00c2810052464005844000d156511050188001d59004400072903244005005249211441d00c0d15040e841250810380d00a00580b24400d081c180141c0f0f00b00b13104850500b0441d030b6031542c01c003418001c0500762000c0318000c03460301341054880e00c03600c1ca0004103445d500140d850705807042c1c00c101d00da07950080c484600a07120720391a900000340c2420b04056240403802c401d8919465070400100d89c1c016000032050004000501003190000000c1d9101e41000341c1e60014101800c68045241c890742c01034483d0302c28800199500c810703182ca40d014000c54800d580030007654039104c1c204025101d1541842180c04400d000080301c040950308400c2c00c0318040c1c00c205103010743e409076800003404100c960080d05040b02c0c2810400b65418811205800892a050103d840300400001c10301c85207040000c0080740c5403922803034400030074010140303804e51003021280c0a00c058501140300c10340308a0495030381ca03035160328031003240c11038001c0d184502e00040c05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 417376187 1250 417374937 417374941
    0x30902130213090e0a0515100f0308030609060d0c0602150f130305130308030c0c061509130507180e1005150d1b0e061201020712030914030f0306010305010902070506 73
    0xc43c010109202c1d84400c0b8400d03100c2c01004580240100102c4625008403da05443c125001030103603015548018005560b02008202040c079031001d50340c20450440b01108940c0740d85000031311103018680080d08811041d0300010700036400150f000740c3c000f180a0900d003036a03151020a24190001c4801c2800d049241c0a10ba00003413141c4010700d9080901c4034042d20f0070780c03a6151100c1c07541086800140864001450340e240340c070b00f044103580c4005240032000b5400c0102e0040b032004000586225500101e90300c0d03840410409000980190010f00c070350048500380c00c50f041024181041c0c41100c90301984608071201942401202c0c482c0020b1100b0340f42011543c410306c10345c00c1c0801e40a550458031000050464002d850641c0700925011582c51001d0800c60200403c407a400d100114a9a10400c41d100020b520800008040c45540c01e00094000703850400e126200b020301c4a05a450200194050303403084000b0195000c1c61003030380d0410407a07880d03c070448220302c030303600001d441c070707800580 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 417377437 1250 417376187 417376199
    0x20c21150910020f0301031401022d09060c0d030e150f1b0307090608010b0a080f06120a03020106080105060603010e0a0c0e0d03053106051e030106030902130213 71
    0x111a5412050701c0741112944025032481404903040b14100101e00d8100100420611030348030361007020a00c0b007100031850108210004111401c80204203000d101e501182c8810380000c06081c1c4203554806042c1603503601e030800c2c2203500c540084d070500c1c0219250403101031000d400011307403205401080b04018855121048000386a450043c107116500300c4580b46509424010310145001c1c90746920b071115000d0804070091b0071441e0580001012402c20b22010048540c00401c640d041074008d22a455240c68810108803a81050540c00405120f040c2583c810903905500440807209000c2c001c120944030403003041610721080c4075061106032500b0201350f2515441d4440b004040050400c00c600c0b01c00c040200701e5180820390140d02280010401c00720f01400c1020740b014a02900380c031110504101c94a181d4901224090740c4204a808a040a1000080041500e00e00781d01e4000326242d60f07644a0080181020280480c010007200c944420f09070030364000d4070314038880030842e0222941006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 417378687 1250 417377437 417377473
    0xe0103081b011503080a0801081b130e0a0f1103070308220503100f0506040605030304030f0821090118020603060d020307090f02190906021209011e020c21 68
    0x401e0316a45540e00c20840d220340c1040121a4002d51140c44c0f0345484080502000d03004540585c44016107070000b40c00744400c030360030084030318800c001110402d4403107400c40b4910004040c00c8696402d103102e00e960f000140516501c030381110611841c019000200410103040d00d61065100082c8201400c1c44150708264000003d030700d10008409002c1d00c402c0d6220000707450400300210342c1c0300c80d0b41d42c2c1303000c50000d104038003c507580700d0001da405100f0549407201003581c92045200c068801070310307103c1d11010824008110fa070340050942e880007200c000000d000e000c5200a81c0d822901d50b103411014140961056491580640c00074413041c11a80c5000600c0001035501404030703814000c3c5407001c81e07065134034801c0401c018200d0200507100d000140302a0520440489401c0900603c4a0104586603000038204080407505814644900c26080141c5100c6a00e08903400c0f07100d10550030305130382c80d070004150b18040c0d0101c4084103603812010361901c8480900b18101400d030001d4403c010729000d50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 417379937 1250 417378687 417378727
    0x10240b0a11010f0906020d0c020714010809070e09160801050f0109021e0705010204030203070b13140f030a050c040f0204030519052404050706080108060604050c22050a0e010308 78
    0x4200100c2c91403c8038030b410f0201d50031004200c6115070702280d1041511518400d0641c5c10340c01e1b0005102c000d06000b42625461250803029040120700800651040010300501d4000c2c200390740c1c801d209060203000703583c903404000c04d100188a481d04001600180500a00b801112482c00c2000d0503420132000e080a5400045412034188810360400400f404032002061914020f000060700c2d50305610400d170a108242d40a0340c03101c0001d000440402c10068500021112054441220300c0b5200d07010469400c06103902580c140918020a028010003084207505010110b408200f0030f0381400249040b0301440c00007070700c40e82c04118942194841540030a100900840840748450001d8503440d411111280c51165100e80f0182440200601088120058040d41c200009958140071065a54080c005c008500c07403903c40c00490080000074040314000080c21915500030000c903032560720416101e101d21030040d41c62445c005001d44800624906032603100c6011840c003001842e1910f203400701 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 417381187 1250 417379937 417379967
    0x6021605060715110409050105040f050915092112010803030c120c041215111204061e05150312070309030b1906061106070c05070b070c0810240b0a 65
    0xb441c4d0699000e146402c003c3d100a208002001c6035560411003804140d030340c001090504a400e0406000d00300101241d944c0d0004e00b1160200d038a85da07040846403502050360710220707941c04030f00c03180200d0803140300003495102030280c6401c801d80d0382d0302a0261749101c215044e00542d04207000c090011041f030900580c1049840c5540e40c00d050700c903078261117045480841151000c1e00120f20a0344d0110f1802030400f4644050a8541485034a90503c8060100100018480381c0c0c2c882e081c0300203030380c201018952101c444000b0040c030710b40b601981c1c1407030110f074001600c02c5c0300d240b21003051084000103c1d01c8190707040e59804030130340c5169214200c920029101c00004200d000c0c5140d880200b610442c4010b283d80c1c5d862482d4581c91078902410210041c00c05820014001015004501c00040c607904032426620714568a030b0342da04065801641e03e0700400510700403d1044045000c4681102e9488440180402e0701d0401150491113681c034140b060024400c02800b03162001e60003040f40b03503d40301d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 417382437 1250 417381187 417381191
    0x12170411060f0408060702030702031606090510020a06090c050f0d051b0310110415050304050c060a03140f01031a0106020c0f01031b0801030b010b161101170106020706021605060715 80
    0x14813a0501800c119040f203442c0c005030b00c041298401c0d0718080007070600842d4505941d080090030004000e1a084550003030034024800380c099140081e1081100d0381800707422a00c100148003135868000c00401c07403440740e18407030b80c901e031003004040c907004029000f0f659004005103031398880000e02e02c000350780a21f000b40c0d041c05030241d200c000500760700884c41c103075403080101c560f614102091040a901102d00c1482004414401c2000052001450382d50b00c1d1030803034140380c031a4842002100034141c4010030100c0c441427201031000c000703014040306040c1c03481062403001c4074010203003106100da402d00c07440005034050300c588880c81c1092035204c139400c501031501003004690068040700c3d542e5041c030040c002882c02d000401c244031403804601e014200b8599000e19014000c9a40c050984030740d08080c140350056104289240c4c012007200c96107009284689086603541e0001945641a030f02c642b20150091f002104003030170085401206030750004102906284107500c841d000301c0120050007020035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 417383687 1250 417382437 417382439
    0xf07060e0708101e02160209040203030d0e031b010216141005010602151f05010516120207140405060d0308180609030a1107140d0f060912170411060f04 67
    0x500103210ba0780c21900f090f82d011660321140c0140c008a41031070150300340083c1c814014421007403401d0f07054403001038040b2000e40b003030340312400028118880d5500084d8158a4580c12000d14840840548024640d13124040c01c00211002c0c4107081c1d21030ba40034552041c9a9444500000d000304c200884da03c12150101d41004540c40c070602d0442d4130a80050003d0b038801078503d04500040342281d94045031440840c2114032000d15904981640c40c020710f414400040f84800003070400080340704280d0303000020f503810000074141c06074407000b982c040c41c01f100e10281d030407025a00b01406014046c40001d440c280d4090310075282165403034005001e20442c41003120781703802d1b03050b000c000302e40c012014000510f5480460482c040c1c040a11a10010070700d070044003040100034100007000b10701c00d50a44401e03d080440e8540f100191082c5800200440c2c40c3c882c02d0b000788000c4c9a15459048013a41303039900c58104125010300d0000d000c442c014020490340c0020415810300101505c00d05102001d158101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 417384937 1250 417383687 417383699
    0x90412050405100c050c03210f091305070801090b0907050a111e0f1b060703170a0b04050112020901140301230702120a1209032f070603020f07060e07 66
    0x181c4040f040e440c000900f040203100074054184014542214110000c080180300c00174040c00035404401768031100f09010030442035004020088400c2c09000428a900300021006018002e100541d0f4010001b40d0340703070020603440d5052103044031920f40142003002ca942c80d00b404a8a55200c040c82d0820061900e00c4070351541d2003004807604182903020032a1040c02c0c8104107900e041c40c0182082031692048060942d055280d80c29182c101e102a1015591440b55050070346006403500400154104c03504100624141c0d030740c1c0199502c50086078180242e076a640041003004d1401c0101039480003c0200420503584000301c1520001c0024002040034003420060a000d4412884503150301d4000200300250540e05010340c036035201486070214100864140b00030031901e510000a601d0954030034600040c580910751582d061140c41c980728003850b05504c0c940d90084100c1441d103070b561107044000f0480900a000744c41c009001400c82c5414001d86071585406460180c40c09512402000004162 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 417386187 1250 417384937 417384949
    0xc0f0604030545010f03020a090909020609060c03040906051206070c030315080609010c030c0f0c020406090e010c0e0a0524041a25081209010e011a0406050f090412050405 75
    0xc01c882e02983e00800328810700014203040505140201003500c10084c880c441c941044481d81943c00a1600003000b203080d2000c17030200e120b00aa400d50004d000b103000010f040c1c0000060050351110302040c8215a03a40060001c4290040d1030903185420601c009581c075441070501c400b20500914011074022000030800407030b800c2c1da030809001034012804101c0150380c24001c0e42010b4240e49410840352011100c020302411503402a1303401c00ca2100b48080555455400013406002c2e00035041044020004040d03001b1310078401000045120010f01c4081840c03c40c01ca2030032900060325000440000c2100d1300501c28240d0030418a0000c18400031440c0c3c400c03440c00c0501c60910500e0760356a001c000c005000c3c100c800d40d5900004068114400c0001402441540d07601540042484ca594641c000e065001d030041000d10010356180542d00707c1c0b0451900941e800c1542d083c4c4007002415201c4081c001906580703141190000d00600114000900200011218141c54501581815141c40010382 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 417387437 1250 417386187 417386287
    0x31d030705041826071709040f0b191a1e0408060103031101090c0308030702240118060b07020f0307031208010e06060a0206070f0908060c0c0f06040305 67
    0x3d20040443c041d80c080142900c00d05201c40050300708848010851108603a1500c54a04001c0c060106540452011035651041c0c45000320004c0c021b003d902140b0200400510b4400c2c1a10b00c030724241e100c0582140300504140080e1050b00d170b9840c41c0c00c910b018124410ba84000d50f040034205c0341c04c0303c060f00c908140002c1d2020388903803806040a940345003170007060003410510240302a4501481c25000030080030840702100c0e4000304c11a2241c0e0740079816810000d11081420708200340030100c5150692040001d41a190340461030207c0c1c15011202d40304854441c0a0214800010000303440540f410b0015508180303001412034003815100c0e40c40070700120b840301004c004501e08070010b1040e0301d842150542d000c00b05070381c110b04240f441c16009644100c0a0842414000c4002c40211100c1c800e60795031024116107412644c0d542091040301100e540058941c0b00c40d40129440034400c0580800c1a038091383d0540e071014100030001c0c510300b11625a04c0b50244034a41c00c1c503803005c0718a0212410311 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 417388687 1250 417387437 417387461
    0x5220507020312090d09051c020f0103020903061303030c050903120f041d04230303150a05030304120c08010603031224060e0414010518090c03150702070e0103031d03070504 76
    0x9010106100601146d01d15081030384904548012400b10301404140c5a00140d0122042603da074800c600580084c8500c0c41110340501448007080301d030b04405441140141e00c01d079800c000710001a40112800c2c01940a11503260b00700c404180fa00c50120300291000982700403001c0d28169450200382c4a4501600c2540f0f21849a20100010f000f00000c20f94070710f4440440010340b860450380541c0d100c3c40000d184501c1d8404510001003151a410140005420091304503665075880c0d8640c02e0807171101b100220fa81c2c09030980003080b14a0180500412654143c80c2d59240c40104000d40d0b01030000f001e0f04200b0071243d820003c41c1e070040911010010041ca03115040160382e05400e10040e51800c0c200b1800a00c030303c20040220f615914030551880100f0245550252900c100b941e042c9821048030640c10b114805449016008005010f13000704200c0e0200e0300c00325942c0201459041d0244805000309980078800c40541e240505030354070b01140201501da032180c4840025046490b002580 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 417389937 1250 417388687 417388693
    0xa06080906070906050415021c020a020f18012705070c020102011b0e0409030221091c0503030c09040b0a030506011e03120507080409021c05010522050702031209 71
    0x100c44500d606020940d040305152810040700740c148000608903110b0342c841c0801e241002e40b1f12001a0b0f20a01030781001c000c012280c40000300a01c00d000b90f51322b584e1801a4803550715801d0790041490030410081c580c80d52030502a0551303203488606042015801c20260300417022180001c80006d03d40b04442c40792105858100fa0f0b944140002401c407201460204c0c0c0401c1c3c01c502d082201500314862151450040b034011481005d5480c04030b00b020703000c68a0710319404c0c40d42515041d1003010005800200d000382c40301c0c05100e440b014481c6c078080d15414080c000750800c0000c6104d1500310001040c0000c03002c1c10104854010b00046007946250750300640b0103403c8200140410481e80d00c08030700001880840b8100141181c840003103050000d004403050210001c3c42200300080074003590010401581c045440d40d45030b1100130f005440e040e4002004501d04000030600f8681a180c03014034620861100c505505048132000080c0000382101d81903100038080501041c115802041c8160080006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 417391187 1250 417389937 417389941
    0x1020309010f0b09060a181104090603020111071406160210080604050601110c040e0118110114121f080a11030c0f0d0b0c07080d240506040302040207020f0a0608 71
    0xb071000326800c244000b40308550030000c1c405182c5e6424440020341c1d80004803000d08100c207911400040500810000d00c00c20301050000302950198021001c80b8002e8031352081f00a254100340d40c80320614000c80d4600c40024250228078180ba0740500a003450480d2a0554111140c0000f80300c001900c40b030700c00007039200003086800d007803a0045d19040320003801c02c60f2850304051840d5803500e000c0c0045601a41c0d60303401d4854601c00035001a0032a0821480c03c3c6010449420304440c400d400007040740c0440e03542c1015683c131917140300c22142c852288844100d0f0320b850703040c17102160710071000001001c0400e4210103d4565028424000703d00d210385400e581c002500c00500d420b1103400b000051141d08289040b0415458030084401d2440d44040f0782c3c10140c2d41c14000d18010b00801c01c0103400313110042840300c98100711784e0002d42129200640c0c5034038040c101244011021030360045903003004081c4403c10041c102500a4640c40e44000c0503180c0d00707801070000c201c0f8010240c1c07000c4002590301c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 417392437 1250 417391187 417391211
    0xf05090a080615100914130e0a0506010803040e070c050a0813030b101d090a0f14250504090f1a0103030809030c0d082203050a020c120705040c0c050102030901 70
    0x40ea01e400a4a050b0328a07005104007034176034800c51240c42c01d0041a19510200d07903031490751030000680c40000170401a680606d071141e641c0b9085104640b1071180c8000070583d8200041a501115004500c101d45551610b408440c2c002401504503403600c00c03e5903400000381d01c00c014046d15054003000306420f61550400d60402c220240100301e014000840500200200e401d41c480c440940300c0c9214000d44400c403290345031036a1003d0291003030f200c0300248010010f0b103a08044800440380d04861050f1008820b03042c10016800c0e1011801214001c00c0001d0f040c690040a4090700640d00c08030000c440343c60340d8111480d500c0d40d201070508150010300c20142c000d10b031035402516000007582010040c2d420705035151380000f140350a11081c5000140b00c0c030900c12080350080e030440e150b12808426441c0c080c04580281c0c09000c05801640b8007400b040c02c0117131022155a003480001d2074058030305020310008103490b003102e10801000e03c9480d80070407800d00055004064640001505e001101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 417393687 1250 417392437 417392461
    0x902030a0b01080f0708130b07020115140d02131d0c030d0c03120b1c060f0c0c0203100c030908040b040602060105010c0203030307080702190609022e0f05090a0806 72
    0x40c034101d0503c0300120070300c618130004005503680720781c6a083c516455210b41c50840102508504010a403554a5080040c00703603041d0404000780040d055441c000a032607414100303040c42440c1c090764100002d0384100015143c0b40c601505070982a5200048800b501260141c0101207040c90a0040d4402c289140322030508108005079051a4a05000b104106540003008a1800140c00410644420030800b0316541c4c21403062011056214415020b0703094541074018204082c81794410520b445041c119003400364803203aa486900801070b20000350b2420191004102c41d002071001c06664020003000206070800500241508607002ca4899103001e00c0240307007090580203d03042108256600c00181c50010603690442203c0c241121556200c080483c80c029078600281843c2072181d030403805102880c0c1c0141315aa00a44451101a82035003420590181e0907943d406039a0719601d01c0c00160340f00d490040c1413000d42e80340c26440c040d0f0801c0001c20b1070010344c000362010b070011410300034075924034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 417394937 1250 417393687 417393701
    0xb010911340f17042105030f18090f06100c060b0607050604050712030905010e031510081203040203070e1306051602060601020106030312110706050f0403080919021003090c0902030a 80
    0x82070050380b07000d0400001c20040817030b514a04caa400b0b050801541042010700c00e64100c1c1d01c40d01c040c01e031030b1240070300103900a9027504482801030545401088c03034451000c1825100301e001400d411a0800c3c0c03610200c446501d0000161041c640c1c5035101e41140d41d9520052400c0703401000107000c5806d10b41020740c00c084855004500001e00000c0c1800020b40141c20302080301c5003420258002c401090100c1c1c14007a02041150b0305212a030104100b849500c10307480252248042101e540002d440310b0340c0043d21080d2230103176142c4d11242040100c429010b1390340741d028661302054100d020b519940c4105460b8165803c0400780041c1c020003107070550420a1300d40c82402480207010036803541d180640180750390400803444980320001c0141d9410360504443c0703400d500c140100901e250140c84080d03070a000340c0d41200001e0000012070410400042d08000c40c1c0000ea664800302d11856082000b5064140940390030300d52210484000300d6690031010000740340300500984d40c0e1911394000c0c0129114 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 417396187 1250 417394937 417394973
    0x20909070903110121051015170a050c041505070201082508060a0f030c05280e060424050307050103141501021510030b010911340f 58
    0x8490701040454942c0c20004400316007030800d080801070703120300040c071000118070034800c1c2403d050903ca0b414800780c1404007120141400002c46501c8c05a0485203213052203000001084150007003104145035030300403900301440d242c54524107640c40a8600c44881180d04603070101d0008100d000c20f40d6080070541c0d038004171446441002c1c00c84540d20b447c078101d01964032820800e007080010b2468403056911005840d4030266154920341d02d02c0c2800d045d000c42e008007401039101c0d0703101d260030700b00d107003400100d800c1c9117a42070b0415428001d002c1c0c054040148880c0e403250302d440405003926a80c4089513109080f1807103c49070a4106400d040c54400c807035009504041c50700f182d6450300b000702440d0a405c00100350f1510000809100100c0c81c0c4104103141c041184855401d104c0340c40c1e030150b404021030f8400c04045d00c01c1d030fa0701c0d0442c40848104d008115151a41000074000130210382e2144100d034008181b0040c400f1041225100d141c5410002c211807071140d9040210078000340d586035448401d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 417397437 1250 417396187 417396197
    0xb01091d1f0b160302122b060302030a0f0201020102040b0403060c020114070e0f0a030204020307050c100b0603010b0313060509070303031508071e15200c06180a090f02090907 77
    0x1180c400114460300c65407040030300b8540c90f83d0000080520900203240000d1580e800726481341210300e000c841400190321b070303900d1052509800030f03000c90860007440c00701e80d0003c3c040c0640003680e13100e03041d100101c003204904555081001103541049035000e040518000c040c0091104000362000e03003151a00c2c1480103900d01641c04025146c1da0014510340c0c1000c0a503801c000d8491160007040701004140c0000b94080e002108104005070f02038060103a050010080350425400d900c0d54004a4411300d150b141c20040400c01841581e100130002c68200305070546171030002d490f64441c5021030306c00303680c0f41810740c1240c0b0007001456894051401002c0388c542c0490031841c9042d564681c0d9a0492044a40c501ea11000462403002c0321000803000388645000d0145d085180c8a00030a03420303a6aa042007698000498040305400002d078003440d02c00040d00340b51802103411050011800c0d43c071180380d4030141ca85400701c2c50380f456018428162070b1280c4017585a145040c1048213000b401000101000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 417398687 1250 417397437 417397439
    0x90906011404020c0c1005030f070c170306060702040f02040503070b090f01030b010522030b0c07030e01050c0304030609080d200706090c051906120e100b01091d1f 72
    0x701484421581001084500580e940320356012a070800c0d00c40e01000e035001100c43c41e10b6024035041001180711304003548498002e982c510703205403014151403201502700700303805414000402401000315041078008101c54100480c0d40e001806550940c18544101500810200441d0604024540141005620701400e10061a0100e414840320030016810503480b014103165a9014a0440710514019180945440c1f40640c5841e445d01003840102d4035040010001080c004501c000c1c4d0348055072581e80c5002d0384040d0380c0111080c1e00720300c800000c0c600042200000085403441f503400c1c1d092140c902903031034800c03c88071582110b214142c42c40c442c1040c107070303000383c080f43d82401c84150340c5d44103c00050704202802d0079915800d407504881d4200710704201c640080031461111104580b43c40da1582070241c1880488000e9400414000c0e050b6481405040360a8816070400280004185840b0100030b0307482044a10303582d61400c6149032101c0c46d50900c001c83c00700700925040d4032400020003241c6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 417399937 1250 417398687 417398699
    0x3060b0f0f0d0c170303060108060103180f0201090801060e091002090a06030f020d020d0f05181e010e191101081306021608041d0105030c0a060c0311010c09030209090601 75
    0x10a20404600d4841c482c0b0305402010000c16240c1030018118070f180e030320440c4480300b0303005542e82c2c01580c2c10b501140c0c103030b8001390480d8840e005601400d4014109070340072009640e11407000daa1026000c9040c084058008280c22109100c2d070030081407903010206a90410440d61410424a5a40c500a4074010441c40e4229100c608110307040303a211380b034001154042001208001e001e01d110340603042d800091001d03115690f68100c02c0311301d460340508100c1c58903100d8032405000d1601021004e20b070010070031035200710305080b036840b030266102c0b0020413502800500181815818901c40d500a07c010b0164800d0183c5800328101140083c200f030100e5051034051a80301c0c145d0520010045600000c40946031003014018000c0240c0c0400c1203502c481d15120403514608010321452044044000002880d1038000b4006000303100240c00c2c1d11456040039400c0342c00d00b108050607018041c0301402c0c04d882c80801d205951100e092640c54500780d40c11441088802200a82040c1890340b0000c018424 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 417401187 1250 417399937 417399949
    0x1b0309010c300806100e1309020609090103030c0b0c0717090303120f01060329062203080a17090c04021605012f04030302030f13030b1003060b0f 64
    0x341c60381011452519000320908140240600c01d04400d801008003982c8000b10f4011003010b00401d0201c92541c08803e0021086400d0302c101d440c250360041a0041d0304a0340c1c851644000c00150024040902c0e2040800110306208020390044000030207200c200c0c0d0921202c001d40940021520244c03501d055003075150145d241d1035244c090390b094900010700e545140c0c1d0420480307820f50383e801c4001c10b942c90007852410304075000b4481c00c4c0106c0d04000c803407200c0b400c1c2c1c0696903c11542e02c0b107003030306144106d40a0101a801250700c1c5c28541540744007000a1145003540d03000154441d0700b00590394510032000400042a041e40c00113150715220520658840215910a40d0340061fa4010b84441c1aa61003d10940c0c0108000c0c0c059480e01c0d0141c050401e040041d03d101d03c6200b0301800880b22107590078200b91183c0d01c00540140c00034400075407101e4031000244101c60503101d80b2441c1588948445521000a59240c003a015210400304108065402030080c1c4080440e4440c650124440c00310b15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 417402437 1250 417401187 417401207
    0x21b06070806030d1d010908060a15050303211e0115140705060f0703150b030114090f01091e021c0e0f030403080c070915031104051302060d09080f1b030901 69
    0x4040703400b001d182181d203e03015000c000c0c8840e80c00c607185402c01e00d402c4000bc040050302181c0031140c2c80804517150034000121445031404c0c1c1c4d28800c81011440203880400c0014007240300c0201d400002c0c24540c2d9205c1d00080c040d01c0ea8801d071920100f28500e0141004100c141c9400f2101070a0003c800440e10106600390302010071615004690b41340c0ea001c0b001481c5000100c41c1d1000442c1002c11130580100145050303882541443d50109040420072110300300c122800c0440e1581140180071071031150704017043e94111401c208400800a15800050341c11450700000b2848503003403c00d41912490084600c94071425001e0022076105c2d80c0d40907101d1085000140a42e4400969040190001c00180300200810700c01000003a80b104a1000440780c5840243c2e4040010003950307490340350904c1005d00520708440480300c6208982d080c02400e0f0801c075903070343e90b00b030b070301c5051001080c00b400c01400b01c0503010b0308a5960304030403441200d603402c0c0780758104c043c0d42c000c1c002d004240c0d8221400407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 417403687 1250 417402437 417402467
    0x17010b041428020307020717070308090d050304050618040f050f2403060f07080c12060d08070b040c1d060904020402220f0306050a2d021b06070806030d 67
    0xa6200d0b0703001a030050044031418011604a4400410059031319400f0590360241c2d03003201d4410103044042c0000030b030380700058040503003c81010429186c1514140c50301e401075911400a80742000d60342d01c0001c0b042d8100301e070ba03480201c0c000000b12021749003901c02e030300c01700740c81590800090410030455000d00c0c0740101a400d5201003010384042c11001400c0310380d40d01c48014201e038043d01d0000c002c104071102c195010030201e50307624040f500ca000b80309d081c0c4030710030150345800090780d40d40010400509420074090780c60a50400a207004507003002d075610702c50350040c0c5159100c1c92422260550584030200c548030000d40e41010b0008a03520401901d0300641c0480340940c9603803070141d02da15142e10585851081100c100000541003803000c082608690080d902040a0b41d2100b18450588800d8030030b030203a44029445100804000001e00c042104204000508041100624403008501c08a4541c80380d40254200600701c1d5000411507800202980980044280301101903c0002152118 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 417404937 1250 417403687 417403711
    0xa18050114060c0a06180615090b060a020d20010528060b0403140f030406030e01050609090309010c1112100c05040308070809010201091502070c050f180c0903010617010b0414 77
    0xd100541940c000c0c41b2102500420200001004c11010700c803c40d82a104480c919800c10703043d0030207071a104081ea4042c2020f500901424a00e6410849001c01042043c0f00c194903c58800011480d0900c85c5a01c150700c81820403009000488400000010558622002c94107114007030040c10200010756080701c4c1c1c0501c14040d85901458036900308a0224000c12640c4808a030002d00c01e985600000003200020000300000e0701c0c0c0b0400e11000520031074950a9640c4208448c20495101b141000d801c80d009190000300450f0140014401c00d90b0603d005815502c010000d05c83c0c01c05520898041d400f05080c0189018956580d03100f541c002d0140c0a4056180401ca2541c0c0d42d0017034105207502c542c0300344901d0001f003500008400a41020134183c86c1d01003ea80b0115042c03c20b928004c2c0030b07100042c442000c1c0900c000140745180e0300104004e1114009104141c0305407400d0007642d010b000280007211840000c962001d08680c0005a1280300d5800d0204600700b5841c001a0180c0101a0080f0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 417406187 1250 417404937 417404951
    0x1903020f0f120d0e0a0203060405070e09060c030711010b04051306240303230403080301031a061c02030a0203031207081003020618190e090706080c16020a18050114060c0a06 76
    0x800341400c0085d40060b4050091104000400801180c04002d03179101821036001c9480d5070b02a907548540855107008030101c02c1012451070350003184034000501000d03002003807011107140482d058400c1500d43c2d6161009560f0620208080b0b4010113100240858407803034080c43d100da611404406d544000340500002201c440d14a6500343c03000840e84102c20101641c1c1c1e80d5a1130320404542c400d210a40340040402c0700318590b0006160182c0c081d0302e0041c41280300300c025880303205810b0b5011004136414800c4040a80050300d046c005171403980111843c40c1d2413450044030160106100601110020305800f1042c00140d60b54000d4481304040b804440c0800c01900340420b0520a00901202e8558464240001e206c100c0107007040c443d034095801d40b41ca142d6568801e540c00365044d258442d40001c1442140442c44120302c810b44040e000502d2841e6141c0e4418002512640c01060511003644070001480007000c501e561281d0204182c030400e10300349241980907200e058280c00141f0311034990030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 417407437 1250 417406187 417406211
    0x6132a0c0f0f1a010b040f0605030601020705010305090c28080a15050c090607152003160c02060a02070603050f0601120c0201060b27061603080402031903020f0f120d 73
    0x604071040c3c0a8501c6050515611a842e0343c1c2c0b240c00903c600121017007448404200c552040040c0e03070003134806800901d540b80c2020019006040003d180d03500910500350092025511964800340212103035003444003407000b1049a110100b2a6000000994403200c80d4030009080c0c2d200100e0420105d50001600b070701c4401000c280741c810703004455404036010900b1410b0042d40c0040d280307003500b14641040b22800700c11952803d03996103100c40c8c280110510026001540c40c0d51110070305c240340e00e4060318111031580042c1054210452007030040c1e001c000c0c00c2c800c141d0580324040c0c111240661812581c0f0f0f0800001b016105c0d4240c1000342c05894a40c0150028000d42282004d42203040d12951500514100c00101c071800380c040003613808140c2d0002341182000412280359040303420310152500e0300c07a2401d1740d10b403101a004030b030140700b02a001c08203840f0030009520886c0c0710794046e2031340340410402a031a0071004001d00300c1d5a08070740341c014001400030045500507151074a001c109014090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 417408687 1250 417407437 417407453
    0x9030512060a030b090d081b07020609030106150908010c03021804020901140a05070507090509030f0310090501030b0a05071d010f11102f0f0306132a0c0f0f 69
    0x3500013051006240140718407080b01040d4031410341d05c1955010899034922561001402c0e12000e05403ca40d000c00900d00541041d100420714420054008a09a03954040c0702c8075056440c0e8424000640001d414400008280207900d900781c224902541402e004240d5a45405004a0081e1080760b00041000c040e034058805401149075084d0401d0300c030031142801514540c000c010456250003002c10102d0350b00400c0c0328040c020703008140210305003110f440309104158406407020100c80d018500c0005e0800d040c0c0501806913101c0d1101c80c6450400320b12080588101a00d88c00600024260742d40c4420002c074801c0200004c01d2a090f900c1e180400400d5078900301e00800c04425000c0c1d01e101d901012a1604601c0310121105c0e2104030320500f60800c01c01c8000280082806003400b0406c40d0b842044040c00b946d000440105460088603041c605181294040d0140d00400041021700d0a014540380b203203d00440720718185190030400580e507804d8894142c00c1d008104080002800042c04029 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 417409937 1250 417408687 417408689
    0x60a0318060c020d020f07080a0b22031211120a02090a030f110f0105040b0406080703180f29010b070503160b190603110904050c10200109030512060a 66
    0x2000041040c2020380b08000e484009007060007001d0310075003071001c111110019075281200e07909400344c07102040e141e03030344550828094075103403a1340900b80f00360029070031201d88140407500ca0780f03070b0001c01c440303641d4003074203031108403200780781c600400c2c8403ca0501c02d4100d80355910004861005070b9416011000070810800e90700007420f81c0152800c05000c0191700c1104071021001128168400411000110707041e101d14000c1d504405814001000b0550042130500d40000300c3d400d02140c01c00c1025203075a50340e0044c1c5030984000e442403000105000d041001041c281d40308100c01409484161248070001e1010b1003407540c41c04001901740c007848418820354078100420400107150030110b0510b0401e03038400b5254001c00c164a001c44d0891082188104012658810703021401040d100d81008000301000340251018000c0d126690115030301d208680c2001441610740c0100b29030310010076800c0d440d074821860306580c174102d14500860f403c00300b9991115040c50f00a10f083c1e981902048200c041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 417411187 1250 417409937 417409943
    0x19092a0e0427060e0105090a15090b0405030a0f11030405011107050a12060c020d17090a060e0d090503010606140a0c020303030106110c0a0f150c050f010e0d050405060a0318 76
    0x91000314140a40c444110070705441c050b10084c441c04405996003403c807042940c51500319031200801d00d0003d8151064209140301e510000510315103140c131070002d009003c460883d202c0c0c1000814403680c41d0000401106410b042c506078000d18410000644e880c452400780c1e5050001003100020318907810001c12026040c0a0800d2319100d030341c0d1925039101504074604403403a0b82001c0750300d12080c1c80000c45185001e410703512240c508603072501010752140068034400d100e0103092510340105210303015070000a246840101605000100010301d00c1105401c150301c00e904015007000300a501c4400c2e80148510070702002d0352007410384000c2d103081082d403100035050b02000c000040c56580180e4a150000001c900b07544400442c10300300011040c540c003d800f03444061100c140032140c0902e101400c0002e1905081141507565100e00f4604000c403ea0502030b80c4d1200307c045180c107014000319070519800d0916904090500e00040d00502480b1022030400d035403800013000e4610580e9405c81c00c550 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 417412437 1250 417411187 417411221
    0x3020c07180c0210090f06180209150102010c050910141e090103180c06030b060c0a120e03210901030b1c1b0e0f0402060919092a0e04 59
    0x2000303101d02030152006000d10000741c0a166840e00c00c002182c041c0e03804182d03120940e4107840409541c0d10008081c00401071500c1c1031101a40e03070040e11641082400f80c92150001124250464002130945c3d18040308a000c00506010000568a92a02c07402400034103040125400c040681c0c3e8203268080c5860085048444419040741c0110880060220450a076010302420118030035900b034100041400820030071000f401041403511aa1012007900350040501d40341000c50711056203010801c4c01d0548076180038102c080380721504413456020500c026030141ca00055001c0e05c1c403181904910900381b041c6000980f121030b50303100f64009031941e10000c5c501c8185082d025010000248446002c0382d10102d40d0103100d480495010101c0c0840d09010790484466803903001026a50002400c01c1360440300500002040b81e03502003001c50750755428440c1c1643d05c1e1a10031200300307403003c40010818903501010382e0000c505620f0070041401d011400c1214a122445001c680101140c50903940851 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 417413687 1250 417412437 417412469
    0x1050921031303030201060504061212090519051e0a1e0b03041a0702010e030421020406150e06070f0206070203120f0409110406080f0414031804050a1b03020c07 71
    0xc03800b00041d00d020b580201702c01d0b81c9640501c001c8070807500490300f02ca07416400000000305035a0800c00056024500401c08558580101d01c80e91442c00e9000721150b540c10b014092424281183c100c2120202080004141c2c0380000c908406298010a602c1c14002001c104003107146d40c0030000146024524240e0704d2405040c0300b03000c80c040d0350b81610a6917140c03010403401c502c14003811200c000044040e41c909132400c3c41100324041d104801d0340d4013951010000340036a60b10b2190000401c401110004020540100141384294003010140329420510201740890380c503e40803030000b41c0c1075030081d50324051800028901912003030405100d01c00003030505003030b0030020050011290400f0041c8203404041d40e50000d01d005034050070000420000000da40c0f008901d82c004c1d0064020364081414451040003542181e002540c01808182e8014a0040307030f003864450182e10001948082004403400ca9203460014644c01481080540128400701c4916007800050000c2141c49607003d080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 417414937 1250 417413687 417413707
    0x501060302090a0c1107050a060e040902030f0d09060c11040903031b09060e04140c0f0d11070c090218090a150f17030c0307030f03020c10060905070c020105092103 72
    0x282c07800c0420440000c1480d01c2c9a4171038940001c4800076100010079951600e410020110307140b5010300c81e41588552140f0306080561010710001c4d861801c4034020700040380f004034010308032402070350044041000e41d4019002190203c69008041402250701141e1000e803070170120050800d1840142c0c4d0064241010303401075030421000d00c111002c6440e5201c0e0400c94074208812221042c410041c0d84090030300040002d4441802848401c50951442c2c0c1050507400305031003128140c000001242000154403400c1c04101c20009009182e030f03410541c80c00140c11840b01c11840b00303015940c0200401e1001c03844607051508000100307130914514400c003aa0b00c1c95500a00c400c5482034010b4401c40c10210710710f6a0000c411201030710140d00c011840c080050344c040300e42c1d42010000904050342070100a0f901d0205110480c0001407019021a42c141000c0c104021194041c02e20300500c11a8094840141d0304030702500c0040408445404880e400c04948460301c2080510221160000084030103003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 417416187 1250 417414937 417414941
    0x1050702091e1509010504090f0807080a090512100b12010c03051b09090c0f070b0c0c070807050102100203091e0a030e15310914100f030803040501060302090a 70
    0x444a903000e810b16260b11500000c420555000021039007180d5090011722007400c0030f400c0050218440c0701c00c2500c50101d0f84956100f5008001e0880301c01000051a8000aa100c8141800b1b8001112242c0000c21a8802d4641e0343e28010003200b4010303142d00d061022607880300c80d00c64440c43c080000740020114818000c005100440759000131040c2c000b000c544000411080e41e24015018000d0415034455045804180d04060308000c9000420804c10b800242041c240a010381100d90419480d200d49021490910500b074000200c2039001003000c010780daa0000300c1c01411014817900598a41702c5c0f068040c1080040c0c40080c09003414419050040383d40007d81d031480c5030081d5982040744400c0d01c104208000c0d1210f1900080d4400e01031614059241d2036250300b4081c030101d4043d40c1c010640140e061702c01c55580540c059994400b03026041000c11003010354492210811000e000f4102040400c0f4400580001740c8020400b10000e41048400d5212002071a002060b0075468900450aa00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 417417437 1250 417416187 417416221
    0x18050a26030f1e0c0c0904060f1a03100e120901090801060b091503070c03200a150e01050f0c0f070501050f0411040e0a030e01181701060e150904020105070209 70
    0x19a8110b03540f5071a802e208004243c2d03407000250009802d0160031942086501a0f0103007050b5501c0da41e82240c1c881c800c1880c0b003400110200d15181c110120500d004050410303c15804424644d0300b410b9070120400790200705a20105014260123488065450040300d6115140d00240415031800b1000301e5106064005003600c0c03a821a2210a42988580d940b480d901043c4c80c808041ba1542250400003405a03070940d240206442042c19100c80c03581e10146064040c02040e100e10381002004c00c44441c0034001c80b2407014041c8003d100505102c42032a100c204001c065071038405020502400b00c0b00500308584000b07400030024006820f00a00c2e1110303028096500700d54248154506800c00c1c203150180d09a0602d1300c00140102d4031540c1c80c1544e45850707445d171041c104117107900c409101c11100b04404002d0301301856034170184800a801c4a01311140d03038200c8503461341440300b005110074040d0005c0e0070402c416200da150a495600c010303525809880b100a42c04010002040000329510034501 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 417418687 1250 417417437 417417457
    0x10b0408011512080306010e0d03110105130b04120309170910110c130209060d051906051c110d030c05060705090d2411070318050a26030f 61
    0x304076102e2220092090a05100d54101c054094038003a001c61400f80244d03074804811306208403503405480009a42c480200c03812004111080000014410300344600f590258080300304120380e9086071128031181c10000d000400019042d41c81c0364999100360800342641d60301a038265100c2e403124500481513003000e4442c03030003583d0528812294a120b06828000c040d2100c0c05841c0c042008014000000c66040c04110761036000c10484606864030320003840c1c1e0701445c0d035000a0300e00f003c4c90030140940039100d0003211103040c04070a00103507441c2040303007403020310309201c400c2a041940750884841e401407241c9070b030080082d800d09041c941c120103504400e170311840650b00d15955280d010388440c010003081d150000000d410410006a40e1001c0a400f919100c0201d06088100b992020580351503440300d035411302001c51241d082681259518940b010650203d000c940d05050104010006912505130280c5011141642ca40740303030360051600c17155010589949607500301e402c88403648083c00e11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 417419937 1250 417418687 417418691
    0x212041a090d0e041d07080114090c0901120f0519030807020f1b0604050301060b190507050303060d1a0c0a090602010915111210061b050a02011b0506010b040801 71
    0x900308100c04200c50311418026169040900b080034103100007062000406009080b5009105d0190340c420482d80300113102a01c0042955a000e000c90540e90780301403c488500d0780040042031041e502e81c018641035415845058406004608101c4184400f44102514074000c1200284c0ea0304482800441003038041e89a00c0c003039480710101261703240212302414505800020308031040319100284030941c0355004060b00d06040d2204002402c5643e258804600c0c0440050340c284421401c4000c0b102d641c05900700181071000503141c0b15102c0c4070080955220f411004c61000070040080e242d0305140888640701c04081ca40342c034015400e50b10448028020402c0d5240c001101d61050203005e152640c03040303903041100c4e0b01d48006006005589a07400c011407003030100d260a442411070343e500c100049900c0140b0b1903d4142d000c5e2a680c06803034817001c1102d58403540b0340450350014400b0185503081c03030840d000e41781c6d4040701101c0f500d040000a01c00d008410000a031740580c0400340007911003007070003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 417421187 1250 417419937 417419941
    0x3070201080c03060f060d09050106080f0d080f04020d14010f0b120708030d1505060f04061202030c070f020a080d09080606060a0c0605060d08120907091509020c010212041a 76
    0x1880294042184d00c1a8005a90301001c90542495005040c400c003540c0d20103d10311200da500c00d0300b035a0b0103810001103a88110b41c2040c80e142c00300f0401c040d400440c2030060b13160820320305104070303200b0041020340035005140540302040300303280a120f101c0f02ca401c02007103400b07030050302038001d452240038151103540300800340103544e01c011805004451241c0021031a042540070aa030117042d20000050040044a80000d11902e0341001848080300e40806d260740e681c1000c030040c2c80c03090035100541219205108201108140340125410203420109405e4880354502c00210050340740d4100e00c0c1d150103481c03201c2e0704c2e01c3d42141c00c10341070351540401e86205546100503c80140201049600040d6402c10325101041f03041d0300c4103400500c050300c41e00414046483e00031007036001c845d00324481641c1c502002440d900500440014003071401080c0818102d2a104040d1503003503001d10486258001814280080258100c40c640901142c400f82a0310301814480303000702585150760348a04061700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 417422437 1250 417421187 417421201
    0x10e0306090309130e06010602060f15130213090f060503100b090f1005060406050c0616051c090209040b0103020a1707170c0d0c0602070f240504090e0307020108 71
    0x24005101d00081801542820000f204124254000c1e0310301403144d656034012903203150f40502405018140c1e5030001c0165060108442d806410014a0181c1340d001c3c8211402c0d6507960360060044003400c1d0200940c485050304041e1030b00c0e003015844120f1051500c00030318240745454216400700e460403401e543c100074400100c0f4003035600144d07405a01181040000d640c03419404469a0000b0403103070001c49454039a4041000c6521035000000800e40104410f0103080003000840e52080c803031040035500f0b00d0f1001000c2d2150180c600070031031001210003034a40d1305a140d804041e16903001454010181050300382000346413030a01040c4c0c01583ca000c0e01203150f1120800b11662140c4101c010701e200c1d407a2a46440010704c400103020b46500a2801004166882c603034128a4076020365010500d0516002c6c010b840c0081c0c030b90182c01c0000f0403000400101303c0e495080d40c102d480c22060b0301606649840d0031540c80c0320b6038114030b48041c0341c400050f580d07040000142001510030788607050f958803504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 417423687 1250 417422437 417422443
    0x20d05191a0a060c05120309010218180106080c090616050129040f180302070f060f02031b1f020306030607080123040b060a020c0f0a0b1803120406030902010e03 71
    0x150031241c018580002c1001518440d078144200ca90041c4d042c0c0e42481d00d07501591200d03610903a956070031a90007060125082c092071003d40360b050380c1121041c1c2401c90401300761040d210140310b950240042a000030b48038074a0b031000c079103542c0c2c00100032a55580442c0c4c6070969400000405072540d40c41d01a5507130100c8030101c0c064604406c80a079840310900c00204000113420501221b054494a031071100c440c60b0070050408661610940143c80ca0ba030600d500b50203a4000e51340040d0402840c0c90102100a40101c1110603400f0021017080458485481c0a031611082c8000075419240030002442000000d5014502510084081d21002c0c6c0b9241c4003190500828041d00c0c080b11054183d08510401591800002a80141c008503024180c00c0008026800c580074030f80140e0031100705100c062502140402980c8070868004c030080d420310303110600714000d501c2a522400c1c1045202c01080d0b82c20810200948050f0011a940742d4a0b000001d01074034442e1000c0f804034400142004581c5004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 417424937 1250 417423687 417423731
    0x6110607020705010c060b04020f03010e06040b090601200a05120a030f06050a060f030b040f060503010b030a081611040903091509050102061b0909010909120f0e0112020d0519 77
    0x141c0d02c405d0f0b00e40d80d64440c1001070141071030b1035602c554204102c0c4060842000a140203000c09100861140360910034081600c0c40b03512010320074100602002840d0380c0000e40070329840d041682003081450340001540c0b501c00c081c40b000d48144254039480200040030802406402ca19907010700c000410841c0900c20346009026241d4098540081031162074401c1005220b840303070301e207001706042ca4020046012a41030a04140c152a1942d070140300300d04003405400607151081c0c00a100300c20300340e10f0b07054541c05800704003c81540c0d8032041605019050784045211800140204880822403a028026001e42d04c600c1a28400b030503044401c0074055661342c42140c4060b0060a41aa40c0764072400441881000751881c2c81424410501d41d42c50f03028040d03000c1d00815000150b40c1c441d60918801d003d01c4000d0042c20000099020b0100075400345650b004c600302800c04641009407519540007034054050460121403400c01088135410351082842c00d45000c5070300c10000c001c4082050011907804c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 417426187 1250 417424937 417424939
    0x306050105090402030702100501090605191202060a0207031a04061a01020d0311130308030a061a04051c14010c180f0506070c1508070e0907020c1504080706110607020705 75
    0x1d0082c01c0da80c1c1801c0c0c0041d91300c698144103072040c4001c007501403821950283c1081d0540c44d1780329801d000a0030482265920600310140151640f40b078190741c0080b0500e0244028001c0700c0204004d44031074000c020882c081c641c0200703010300f2075000841c0e40003811803c0f50280c45031030811085003202d05c1e0fa48500d200c40300043c0d0281050300c1120720141c02500664450201100303081100200071510445c440c006148550309543c0d403070502200f054103946450300300c1b0070401010062103c01500000c1203604031601559001341981d4196915009090340788005410b401c9859400060690198000f4500e90b400c1d403290079004950141c0810100101d004400c1482d008507000e120500c0c0050140003403911423514006001d44920007c0006071213030940c4404504d81c1410302610503000906910100d03405e4450b8181441e200714020360320000030b00f100f80504120f413142d000e40510310040710090940320044903c00c0355181802003c840c0394a0310b40020340200c00c0410000c906c00310340401200c0b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 417427437 1250 417426187 417426197
    0x30606070201080615070804030b06010509060a1d0a030b0a0e0606030703061d0a0302030c10180201030c0c060606091d0405060601080903120f041a0c2203060908031603060501 77
    0x1015074015a40c40d60043c0541354440b811090079210304c00c41074010082107100d1451103441d070f881d61a00c203000010260215050041c140444c1201752620801c0d10a1aa16481c024803003040c200c6145070700c8814841e0445c0c21150a41010041c4290101b070b050196032601002c0090079880442a038031800d060341c496a26411a40e000c0020808603000341e040f103402c02c10204600301d803180c007240c580151454200c01603000458031410200d424450001520780c41755040c40840150102c40903580101c00009041c11740d034003403040036240304ac0700a0f11125030007070040101e291100e4002c3d0000d9800d114000100340c0c512050402518103100403400340c1e81c080000c000c180c80d002e0041d10000c00003060460148424403940d404481a5000700d4041c2c801165203944608040c1071000700c0032924481120003000020522152084031011110399004001038401542c840350b12100807400c01d03a00240503941480e0210090002e80401180203d4031800c0140800100c20400c0d0240c807494400c45000c00c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 417428687 1250 417427437 417427447
    0x14100c11010b060f1b0d02070f0806010321121e0b061903241e09050f0f130602070b060103061d0112080d0507020a05121c090302030403050604140c0402030606 70
    0x1c0166400b80c54121710301d2411000844801000d50310308408600340f900180d1040034100840c0c980703008240050254480503140030760564498003d078135100700196040010180086c820320b40b080404003110102010305115544c50b0700c02419004000c0a0f003540d24074500240306d036052808004903009582043d00d172100401c90724a040c0c009080000c1e060002002054042c8040d000380c3c604c2b00083c00c500c0b0a0541000c8034418821404007258010510b042c0c549400d2100c034140c20740c405a44000d40c9000c806c2290b80300d581905441c2d0b000340d00200f030203001003114030400200f201d42902c81e0310280e03410031078650b80c0c1d4140700c0030701100540301c005955a003005000c17040c03626a00c120b402d0301a103003d0340f4000c0ca41d2624004c5410803100240140c0003203440c001004000d1000503000402000c00505003680c1c0c1d0022a0f000e001010088042c4d540e400b41002090700034010f8800450300102030303403ca031416041c0340d03004000442000d4080e0290305071121451915201340c1e402420b01030700050403c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 417429937 1250 417428687 417428707
    0x6060c0605040215130303091d04121b03050c0c040c08040f0c03021503040209061009050f04060f0b04080111071707050c041a03060f01030b0402090414100c11010b06 73
    0x2400054000da0b08229920200d002c28001e0070001c5c117100518400e400441c0d441c42c00c004009220907000781c0c0f0400e26031042e8413982004618620f030000d40001d40b0302d6240712403030b800b03680e101030725001d800384415400e200d1000d140d001005001d1044200080c0d0340307416111010002102e84008460000c5036110b4041008103403070328494003a05100d030300000250790f245d4000400c61805420b50394008d0000008110450500c00705d555001a030503542a01d40d21282c01002d801c02000b070080034000d08020007100380039901c5400520081a1155011084032384505031600d071766119000e00d90040d0308102d0b84d111000d090401307c1c1d0886c0e42010126640144600380a94150f105220079109441410b1607100c081d52288111080f1803000030790b0408180b1203006050404200504003e2064201401000805d0201240e80e0f44240e0440700b907540c0d5070b55803400c0d14604001041d144598800c400f00d02e0f0081d141d0b0350010309250307803a45440201c0501547c805003a101d8040031160400001e1144030780e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 417431187 1250 417429937 417429941
    0xb04140a060303080105100f110102360d0b06011214010f03120c1a040201030f050108030406031a0f01080903070c0308090901090227151204060509030f070b06010c0b1303110106060c06 81
    0x1e6000f60005464007061441d0500d61400398040d2020891088030049500300080034180380d0040140c1d9504c1d0001c8080d11003504ec0d90000703011074140208030403120b40214543c4d101c1c84a024540503107208558491040e6000c003a40307800125401c41c0408000300070903010351141403505501c11810f50040d007809160700700b0f605020b08109e05054540c1d100d540b00e181c03507009050190460314011908c031131400c3e03802815030380340400c495043e1240964110094580c003003d982c0042c001e082291850302d5294503107145210380c40c8007800c86440490044108031080c070050030b1582c0129848019643c80382c000008034802c11404c1101c84240300c84420000b04031542421500c4002451103001c080484500502a03201e001d52040a00b61001000b0810055125690300200d041c0010360508290503244e064601c901003020340180d2035240091041e030b1007005c440d95241c1e80705100030440c2c202910641302401505c08102c01145540c3d170041ca03542d50510408003110301a079102503a58800d500c2e0640 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 417432437 1250 417431187 417431207
    0x6090a0807061e020a0210110906030a0203070c020a060210050c0a0c0201180b04090501150906080c0904020415081009051302090406020d02220602070b0405040b04140a060303080105100f 82
    0xc4030440c0e80302c52240d50140341c400740c08440600e0300030340007480e0030007c00b808694024020399000e0300c1c02d10071080d86441d0142600e0f4404000c400040e030b82d84a5500664485020160081d03111206200100f00a9800700301d4143e41c02052000b40420707215003d4041941c05015251000124858100b030050741c0700d4424081c06075002a0400e031743d662100b4841740c082d880340e0000e021440d00d4000400c00314454141082c0f048030b40f803a00b554054145403004002c0c24004e002e8251108020528808070f944e2030341110010300c82d8404180911180c0724000d00340030360883e80d41030346503041100091654510f000d403030b00c200403110440c0c21041065003086440280600b0a0b01c05a500b030254006070310721803004101000340920070400d03065031340010300001d1070160047d00454220303d0007005441e02c508d040d10705031041124007140700d46000340464010f007174151100034414009410b01101000d6680640b083d02c0c003a0f521190316a80707070b206200001219801032400038001101d400115442191611 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 417433687 1250 417432437 417432461
    0x10b0109140405072d0e0301050f0f04060f05070903060f0605031c031d0c0a06020f03030402040f09170d1107050a0204020a14041d01170d0518060403060e06090a080706 74
    0xd2840c81c45c207140040c441c0c00c8014081381c2c482103400340d40d03d05401c01c604942104e012402440340c0d203011403011400940242c01d0300300d00100e8001050402c49035400c50002c0d4540c51000f000540343c68480141110050300c000e07034140b840c140764014484100c2c0200001e50350041c0003008061244070050f0101e404404803542056901da0888018013a1460b0040308840340c03a004100b1244a0410081c60380d0981e0f003d6002d540c0580d003000c48000c001b00540303a0040d0100d80010300e80122502c22000f421104500401c03401c4000c0c481404a03a6100182c101003030040c00c10425072001040041b003030302c90f00102600300d1744015444c40052519400502101c41c440c40c09000c1081142d000300510780054204e111040040c815048450040c0c0401d2401000b100c00ba100d109181000070780e8480c0e283c40c541ca01003240008003201e00c121040420480c044e00039048656840d0359003403104c0101401c0b00a002c5900a9801240c2c140800098050310b10307070004015071601c5200c0c0e450b0401000c002d4120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 417434937 1250 417433687 417433697
    0x61602011802060f040b031302040b0303161104110d0912030b010503040212010212070509030105130339080408010b091b0c0c040227030d0f120e0f0f010b010914040507 74
    0x210741b00c031281010b10300504210110a040c3d034036500c10032040c0c404004806029501c240030b05100e800c20041a04c9550350000d9a041c3c2880c2d00c070b00860041c21180d06007505031200024040b40c00100303030f800040101e004400800d51400000000c40a8440500000340010000d101160245c0303008200707411204180c1000602c0c000462550006c0c0150840d10a000700710045000c0646060a004155100e14940d100030190900c50f5009801a49070150310489000c004004040b841c0b07800092034035005032a080655045c0107454100455400707400788241a50810341c0d651031a081c25a0305601072100408034802480d10808074116a4100503075039192845281420031a0362a40c0c40101046250000300c010361070a84004400703d4025001c1490190788241040c2d044981d0200400702080018600869100d2446013003d0140040b64010320040c020244107003000d140019820290501c040001c2c481c40640c5030041d90166441d100f02c3c14116008030300d6980310300e0030b9407100d507102520303041c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 417436187 1250 417434937 417434939
    0x905091012081c0207030512040f060e032206020309061c05070c05061018020702010309080424020106050a0501030209030a170a111207060c020a05030a02061602011802060f04 77
    0x15014002441d80568418400169500420303810711070009410007032030015072412110f55001040ca100d10f0580c0d2007905210000708081000d0544001c80c85508400180039204c07154003110346952104500c2d000440d00042c040001c1d5503101807100444860342c01070f40c00c004001c0309000442e40311240c250108143c840803002a44414814540100b01e40e80d10040c40031075500d03241d49440c90150100c06100000481040b400920303c8071000054400000540c5030344003880180d000d0001c06400504040000c00c4c00305000328004ad0710b8544480e642080358a40c004070100340e08844e6a4080c09800810700c04092015500940061000c5580503045030f8610300151207504400c8401c09000c5007440002881001456019130300700510010000909002d0842c1040c0300c40e28801c0600c010202616a108201124000d04c0040012034105060f240e440804003002910361504941c10304030f0509c1ca40764015007900c1482400010044082001200c0a040d000c1000c16044200241b100740b004201c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 417437437 1250 417436187 417436199
    0x90c0901140d05011d040f140307050f0c1807080103062705100c03060e0105130204080607091e0501020a032109050709050f0f24040507020c010f080709050910 70
    0xa01c28030b01c04400004165041032100c00e00301403d101d10205901c40d20b410311000c5441c000d2907204055100c1161100c00c0407960b2441c0c198054490040c0090141103031511501d64003141d01d155580d81255982e90f0b0041c1904962001c4206480e01d01c00540c0140041c030018180e58880c10f0110a0700780002c2c20010f004140c2c40340040401400c585c4c0b9040480c5526035460a0b00400203140c1b51414140106800c220071800c000f18144651441032120454208c14500280d0441d0042c250210a80340f4a19103200c01922848007446941500541c50700c0701d0407040f072802007a82c29140160701070445c2c100252022a11301000008105180c2007803d0782d1703003020f41c59110b030310710a52051001d030074010b1034140003a04030f40000b41082c4131000000108400301e20700b903900d0765205030f03c2c12048016640c8219582800c3d031041180c0c40e0020301d00700a101c0c82ca9000038400ca80ca06c000da03200d50f0600d091500071901c00d80c042e03541c1800300d80901e07800e128514013080415840341c44c100304007280d0707983c0749 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 417438687 1250 417437437 417437477
    0xf0f0e0f04080a1107230102010c1b0f08040902031e010501090e070e03120a110111071119030c14030f011a010c02030c030a080301060f021b0d02060d0504050303011403010506090c0901 81
    0x4040031b012408021080d03055580a003d44007044040b424404841c515031802c56409080c4404d00914543c1d00ea401a03040016402c00e440140080032411910785c42c2021154a07031001078000012080901c03c0000380a61181194a050780c0c000100204140c6940340280c071400c028607207850f4180030712501d0b001d00e041a0320140c1509001c80d41c90004210b1900a00c0c1d085854040401074000805c2102401080900348241c0040f5001e451500030345c0f50117041c0c1050001c1c00c0d04000c29414594000003038580344415081141c2c1812000d4440703440161403640d0172644445114101405400c4501d04190300414484101c24006019684040d18135400a8144401841d089482200200050046c01c0e4000300e191701c400d10724002401d0000e07903005006108002016018861102c0070302c02c00031521141c0a0350a0601c9090040c0170302e08040c034042e43c49401c2401141c94205100c240d4546506c2d05016041c0150f40160104c8201e850320f50072000709030321085885040c0400380c02e100260380305203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 417439937 1250 417438687 417438719
    0x40807060e010b1011030a0f021c0e1e0d020f060405061303030927050c091c060c03090b0a0b010509060415180803160501060f0f0e0f04080a1107 64
    0x480700004850024804114040d48015615410000d880c51403646800b0004115140144075007007000502100341c00c202e02d005030000214200003e4040c41003090b6800480f0300780c101c4000c440c5415038005c41c900c20050341c10241003c40c0d11400180c01d0f070000d81440303212030612240150003a45802d44810110f521903000040000302964646402c205160780319044501402483c42d400c0203860104000700318107140340c03030a002d50325a1603010407440c00c4090704840b00d10102800004070862030b080b442c3d11010324280d0070344440d030034000b4441e41544070303229240c0340a500180611054039034050420045c05a06201418801d00700030405240e03844002a20003401780045204100300f03c41c0b4000c2c004041149495008044a102800441404010364044610340300391040300c4025810b1603030142000350f000480305034901b4000700708007182410325010350f201c46060300700c9521180389030080d6100494002d080d18074103005d540c2c10288900104202e20301d98030116503040e03880701501c140c50040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 417441187 1250 417439937 417439961
    0xb060d021303170331021206090d03020c12090d020a030c080c0301020703080703090c0e0129040522020c070b030411030c0108010b0904061d010f090e0a0b04080706 72
    0x807000c0c04104004060701e181c01c1c0d4003950500c02d420f60510a450540c4103603003000d0b032401100768842c550b42c1800a070084001d00c0360014003040c42c100c0e0390700c8095100e14055035886140c0c0200207680440d24041d00880300c0b039650400003403e4414075251701c25540e40000185941c00130681000c000582d403003044180141d400f40394002d988a00d040d04141c54901004403180c001d9005000750701c04280c00c4210300c2c3c0d0002860030041542d403414034082144403499000780020464207000891501481c4107000000c2884c00d03c480034200b85005014203c0c040c1e8820903a000c088800b001e500700382552820500000c89000150803c1e09507045207040240b5904004000034000c8200418041040514000c554041c0c001d0820300d0940400205400014001c1032035004c2d0001d103036102512190f100d41d0051206d220070114203641281140b1441c1028801c90021a681060105214441d40b140d2180c00a28800600742040c1725900d10b40c01d003400a1040d516000c09100d18800f00d001c50240c6105012 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 417442437 1250 417441187 417441217
    0x1080628020a05040e2202120109120206011706040c0303050a0c0618021005030610030c0212030a05040b010e1006030902040f1410080304080a0b2706010f0b1c0b060d02 74
    0x820304c042484100c100500d400070050940c0344e40300c035010007400000d083c1b0740c055510208000d00c040c0311034003614021500030040c00c035020302044115408151b10341a01d41181e4141d24100381c0c0b44a140da50701041e203020b0120300076820704100003030290004010354101030078400c02a09580d21030344100d59011464804403081c0701c805400718688424584100701c0300341001c44c19814a0000704240340e00c3c5503010004d040d81c07001c030312290b140200b11904001503030b0324010340c2d01c0c68004050005000250f604445100c4d4010000c074502c5c500c0c0e003500c2e216114010b018004c1e1898040224054100e00c1030691704242c1c0c1d42420382c0c0703c0ca00b03070060010044005e43e50900c07604201000003c10313a42e56012500b29041800284944c10001c552001e40c1070b0800c4401d01c1c142c559030402c141c0800050300000d0401c2d080b481400380024042000784c12211407000d0011030658030a0103000c94402d0400341b42207440099020300039242c51ba4804081c004025155904000d030b082c15450032640310905005c0150 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 417443687 1250 417442437 417442439
    0x6050d05100b0402070305090f03010f0e030903060115050304110a09061e0807051e04020d050702060403030b010c0c0519030c23040b031509030c10050403110601080628020a0504 78
    0x41c886006060181000382c404500c0d21509841c010894010f80c0481e51007200c600701400015942500f000c80510204c1c00100020788040c4060342e9a5401009600d01038042d00000103502d224148150000c050706840d003928507501d1ba42c2d0f0344082031001400c0c0754081820500814025068032855024085040d4210b012400300c4100110048495001116560206c1005e0041d525059076507050310036000fa03548000c245800000e406400b50303940a0142510700740400400300e50000d031181c041ca000392400c00a02440300b0044a00140f840c902415001e08210108483e00b0010002041847d2401e050000542c4a41e507543e04091a03510407441c60401054040e07882005512a4001c144c08030780c03c0000081035004251181400118509406411400100121000d004803000959a4030980b520707503100c282480000c0600360750a41c0082e050360307411240543c0006186041e142c0010003020b0301e03602ea0641d14019a005c1c0c090600407007004003c4401d600350703400603000c044c1c0a03440d119125 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 417444937 1250 417443687 417443713
    0x501080c0306040c06030e21040303090b090d080c0f0703060501080c04150501050c0f060106031d0d0909020d0207020405040f121d04020a050f03040b0609060102071a030a06050d05 79
    0x8056150354841c40390704414140800986981501c104441040c14040344a110b140031050605500c91030302c80e030719400c400c00399100994240003081500d00c01e458800c0c4507515960215003038055800c0e4590810410160134010584481c080c20183c2034010888060f40c0c0ca22092074180b1005078000c48049490350018840305205000301c9135100e03070a48040201e01c0140812001500c2940304041c180040041e40c1c0503901c4050000388034644d41c1204491003540e45800090003003104252880f040c54012030b0b001800040420b800d0090b0f4415039076246440d04281c8502c0095001c40d00300e0050070b900708119401a16036000b4070344603a002e1f44c9800240d05e60350800d007100700508a01d400400111010b0480d4507591014500c1400c1c034255001601c034044420155021301c1091840c126001d004000c110800c0313000385c4698400e41d0141e0b081c0d00c0c20b403584401a41d9038007840c0141d044040c051801c0c0c1b02140c41d80380196900107405170700825002d543d40041420540b0200007581c46801a00c2a0140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 417446043 1106 417444937 417444943
    0x100b0a02030d0b01110d091e0302032512030c06110304120c0201020a0b0109091b0815091c02100b010f08070302030a0e0615040b0406050a121410050108 67
    0x80c01300c4030752010740500747c46e12074054504404107801c0818654682d145044a0303002d0f00511014900441605003d07034000c07684100403440813030000310709100025110b0624048e48861512030030b41c0c200381040d104122449224100100103100001d19039101240700080c0500d0402420000e500c0100d080c5140100003030510f0703143d4400450051b40a0348280380e224030565000d11504024501e07220501c031244644c1901c0c0d0820000896460b8910075480d5201c0c981c0020b41e030094036600713482d50244003841083c0700160b00200c8114001022489050b0b0500024284402540d041d030400506070381004012004040c0c0220200d000f03c0d8550300304000010b10390043e80d07410314000400542480d100b41c00b0601c0340e03003001c90b40c0700d041c00d02f44525802d03a13034046c0c48400c00504100390080100360801e01207c0d5041c0b007050114a4071170500c003554400b1074011000c10341d94905103100345 = true := by decide +kernel

theorem cover : BRFrame.Cov 417266187 417446043 := by
  have h0 := BRFrame.cov_init 417266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 417266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 417266187 ≤ n) (h2 : n < 417446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
