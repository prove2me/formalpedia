-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4082
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:30:52.528872+00:00
-- url     : https://prove2.me/submissions/174dd938-152a-4640-a958-bf09c8575db5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 733992805 ≤ n < 734172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 733994055 1250 733992805 733992823
    0x18020a1205010f0306020708090603040c0f0b160b0a090818040515030303011514070326040c051207090e011410081203070c0c080601060201060815060d02030f0102040323 75
    0x80f044030021071440c3c8030500039501c00503045900c030f10200400e0b03883c1d80d66a0042c40c040c600a0780013044103410320f4544800464140c000320760700c3c0b1040c030107440c80040c20b40b500d0340c02507070220b003600ea01d440b04180b28000e002088d0000b0814103020072072100007100304043c00180101100d042c0900c0d1502020b80006d0300141350b85076010b400070801408000181c1000c0c03811204140b801c040200840d4925800d10782110070100e0001b13100c0398058914180101d000b6135490400029280319082680e24070034441082d2040300e000d16011040e500c103c010500c81403000340441241404441000d000250007000e0b01d03103060301320040e1035002c42c60381c2d65000c60391015202d81c880100200d295a21b100490b9410080040d420030140c64901d400280090310110014403002c001411554105500039013503400c190400485a403040e0001881413442d1445160099819214042114180d001103030030011040d55201403580001400000c001125a030391080841100143d003a84100308000c1e62145028 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 733995305 1250 733994055 733994069
    0x31209170a0f0201170420040506300319020118030807030203181b12030a021c0c0c12150b0906130209040608160905060904060e010618020a120501 65
    0x90075140000502002d00b904500b070050400c00b40380b04004510b450460411507040710310342e1a103000030307688110850200070b00d160304540900c60f81c5000001314000c1096008800106800000703003441c0003070b003a22400d641409600560340c0d1501c00c640260001c506085003c001986010645c01140115501028046606555120060711007501c128040c1d000030b8032141d4002010030038017111210400c203458100172030700150500700a08508204800c611205840c01e160410441040b400d130340030440f00040718202e0080840400548001c844c81c05070707803000a018003164500444c034000c600c0c0c24884414481c0700c884c0074501080c5584401d03105082481500141c1800110f18146020004240020780e150001801c01000d0b4001600f515443d51100506400c4500d203032403020107101078a030151442e8903086c41036040501c04501075140041006d030160b0b50b40c1c55240d0707080c03000307411160052158002218546451040c80c10095012b0b09148000c202815030b900076030201801058101c44030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 733996555 1250 733995305 733995313
    0x7030e0307032312070e03190501090605100f05150c2e200d0b06130f0515091513060807021e07090b030102040b04032402030415020703031503120917 66
    0x5c0d80c5029600042201206a8180070704096903600d0180c05041026031406940049800041c80c03c00c41c0440340007600968058020031024000c04504460140403a5000d8508800f0241134046421303080c00f9030000310185d0b00a900d1801900e54407600c1364568140d180501d11701a000d80200c19084501589100304480352180c21a418810003001828213480c121f000410030000980024240717a00c440b52921100082c203c060103d0030b81c010010b40940404d0315100600c50080c000700c21340e030042c001014415152030482c5502e41c5032000a840100d002c151129100640712240030788010401c98510005124100b9146d42c2250720303605c410261044a0081d1001e5420310700c4c000041c2515465054156400704400140d808140300244001c40c005c001e00460b0b0303080344440c80b5294406808440b003e9005209010115030400c00c586d1000040040c016034405a9140a9028082c4040d003201074052202001090240e40c00102500c08401d6076908070b01d94a50349041d0301e0601440c1c0082035584 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 733997805 1250 733996555 733996561
    0x290909040f030203070f03050a120e030405040510080601030809331e03010e060a06110606010c020d02091302040606032c03120a0905121c0507030e0307032312 70
    0x404000700108050103803043da450a505074aa000115446030300032000180c4c00100048a543e0100080700c803458104000d000c0d0009010000d9a64061402070a00c103d50f500081500d00f0400c1c482400108440c82c2610312a603505c2c14041143d0b0860a0b95500600120840c410b4200122040c0510031341001405001d0320086180402c030307508005004200f140b83c03810101522803805000d10b008080c042100841c52034214148141018a030740008140b00322440000615034000c140168000c0082c607200c0c080081500004420454105001c5d4004990006000c0c2604080000302e007098020794041c00010368680c012412103110306113007152810180c000041080c0403a07045180100c0c0b0074212800d05104000040c0c20b5007058602c5c081c11640c0d501080104101808008858000d43c03400500340150b14044034450b171288103280c4400790b661800030b010b00e4025801440f0225010040760b0300d80002e49000740c00e45502034192202c0481d910740c1402c480d150542243c00c6501000c42803002d581b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 733999055 1250 733997805 733997813
    0xf0724063813091506030c0519090306060b03040c0f05010507020418050708060103060609021213052d0c0406032a0b2a0d0516080405040629090904 65
    0x1209952840c1c1d15040401020aa4000c035040c1040074102d001d0300001d07401c409003054480141a5404031040c1414000800503860708031059802c10607a002940b090828020000c86a550382900020a818500680403a04110980240d031049100d00c2e00446000c0e04c07404841c1c0d070368000e40701b518009441008032400600745600052003031060368104202c41d003c0d50340c5203802c0c11119002000c255200c0c100410038403c46010365401401000740451904549404010391154010152046092018101030800c202084000044580490500c04103d1519100d8650341c00c41b40d0442018450340c048648a03192501c150001c41c0e622070b00088454103075442d941c0e5943e00b01601005180480703000003c065284000138107146006840c0d5480342c12041c07001c6800c184607004490b28540c016500411559009022261040c10340c442440d04060b031482c0001d80751180e0341000707800a0518000150040700e00e8200c072040160080000c142c5140c80c07603500e8040c0180090141d2114094012030003003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 734000305 1250 733999055 733999139
    0x7030f03182d050906061e04030602030714041a030601230a090f080d0c021201061d07031509020c010b040608010b0102010c021605060f0f030f091603170f072406 71
    0x7d8042e000c440c010701090003100201a04140d0080d07922540000411a4890703000720403001344450003d995040c1400d020a1101c103450000d01140501e6000006c966035030302540c80c144406040300d60201c45042c101c07940440a400c81c950b09000724000110101d8041c8800700790b03000b230b10a0340008288040d10356008403506040450180e03040350350355001d898562400c1c0600c0d000741500c0561034031403100c0d680400d40b9040c402410300c2c042616103180e0072600c0784a40507003400c03501072800140c0c441d80d13070344440d500400280c141c1e0f6900078540030340000c03410410b4010002d01c4409030000c000740c1904810580c0c07070307100349540e110b03180e451900188860710700103010309004511480080c1c20560400800d02540d4400d41e081c0d0380e001c00440c00c00241c2c140402030948070000c0102e100301194610341d60340304400031052910b1070020700854070300503040c0120140c1c0d0b15290000c08280c1e414a1041c03524803202c404801e480c0c9998242400400c00800600ca4510b21b15000040240c4188060824000c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 734001555 1250 734000305 734000317
    0x601050703022112071706040501030b040605070e120a060f051909050102090901090f050703021905160b0709090f05060d02010806010210021305040e0c010207030f03182d05090606 79
    0x20f445092081d00215499200c0d0036104514070b40301e80a1800d034201c08100d001c20014480c600c17460034000140005055039003c0783c0c0183d48800c0c04201900d03801c8007600c03958882400d0399005100c404001481d818001440c0104074000c0e5000c0202d2100c001404040d5036007141c001760300007151101011464244d510031503138140076200050a00d040d44000840250082e88140d240903194081c04e41d080300745101303103608001b2508045140020007040845916080b14804d01480004900100a80400f00040c01300c02c1c0d00c00a201d03c50b2a046034058180350f02802103025140c0382916100c811081c034400c0a000361802810489109101d0f40110b1306054010013150440c01400c43c1c02042c2c41d158000b8044100004107034840d00c40c20300c800d0000325210100300c0d84003680140d1204102d41d80100780c1d4420760b41c0064440030411079504060b5207034084141c2508802805c50344c0002c62034501c200e000007600b0000880380090314119031280d102c03009802040d601a40300ca01007101d604e000401891 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 734002805 1250 734001555 734001613
    0x230306010b0d090b0a02031e010e010b0702040e2e090c15030b03010e0d1b0803041704031203051b0705070b1605031b010605010816030b012d08060105070302 69
    0x1a1880f20307135603248410352041d00c02520540d00031007445541c00c04c480c03421130340b032203003900a004940c03414602110720041803007000005440018050300b551103981010784103401c401c0440e40d10b159074005580c03003001e40d00e100000500c5800d4511581c00724901a1881d45074010103c114101c1c105404400c94102a20101b0107243e0390b2518201a0340342070040c1c100701062800a4412000d4020001d401052561000d100d4007421543c420005105030051300c0d0055048002a00f100c4802510b0074424426504050103401e0b0b200c021003849a455017285100c0c03640030350390014069160041c0546401645002070850300554003c4c090f00f207928000d00311180c18032060840003a1581c803400e041d58000c144a00d00514269000300b0050310034002c03000146020319005025203400300400d040c2e4807041041c0010180c40d05400045d0303a1081d000066046c84803080b840c103068545180ca80441411810b000c00304800e24001002507000343c1c281c1e8001501a00a04480f8100300040c1c0c0301c5280c0440042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 734004055 1250 734002805 734002811
    0xc030c0f180527060f1609140102150f04020f0a0b19090b070305030907080a0c09091a0c07060b03010c021506061e03011a390d0306230306010b0d 64
    0x34003000c030f400c2a00140705032003406041c1034100400ca40703000000041c1801803202500343d02404555100520400b12088040c3e40c0c15009400d01c0100d06200b2441580314a4010711000d2000e08801d0b01d10345d90042c3e1084401c03d0000c603901050001c01503a901c149642c00d001484101c1c0a03080c0c26071003c0d004022480c0c89400903465202d5185580c010640030740000313401204101020303104000c00c4002c2c040703510017000703c6621a40c440c03500081b58060b204415440b0003485080000b2145c11200c0070011003001e007001d01c0d0150725001c684d0003142090702c1a40c200400d05107182810310800d0703003210803940a810180d104034002d4000840c040e15260b006241089006e58000c214900441c2c4d20304415074056403549841484501c40c22006911029060100310a0f236005290f1100c50020901400144c0c5031042c050f440d0490904604110f00307128000d9540700380312180d0550190050368040c0194850701c01c880c40c015080300700744022003901a44510014890454843c01400c8001120107001c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 734005305 1250 734004055 734004091
    0x111090607050c0a081b0301050105060f0705280605100f12080706050c030105030f1207061107021f120e060403140f07030921030206161b0c030c0f1805 67
    0x8502d513040160b0081c45260890010100c2143e8640b0410a64a0003103000b0700441d41071070006411442a94007000c0c001000144003c20841c09100d0302003108140e0700303444003071031a400035000300202c041000c680141c03510700040e511111400c03929064403000f0204100803400c0081e10820f40079000025a8000000d100100028850303028840c130404024456036180d524050900d0710b03109900101d1442500305842c80301c2c03050545410b03554030941091001c90010407c1c0400c40642c0300344ca1019400800d1500c003a6003590004058040c5d00c1a1682c4600c1c21000001ea0a401c6a0603030811012036000300c40030402003407240e68400b02c000e81e807001e010714100c480030100c6a41c0c0c1c41000e00b02d02181203403408104050001c10703e8a001c65196007807084203005a90001d4440340c00900c400981d5210000c10416144648010400b54890021502d101c244901340700c821424103200c00c0303624900382240400c650302d8203000401214000c0441180c03c1c1e403150900c5026210041c00c0c0101d107000600302c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 734006555 1250 734005305 734005309
    0x20a0314250507050d110d020109030218090616120b0103060b0403050f070605070b06011818020d0c031103041e0b070816020c0a06120617030301170111090607050c 72
    0x20840741060401ca031000c903803a241c64814108005503100070b120398000d50001021544034050305c4103899080381d55400600c410710045c1c4200740c068101941004080121641403a03c180d10203008081c1d080858200342d03540d242c80104000d00c0001c000c00560242e41c00100e8480e1500100d91406050501241c450380b5040c02074841e0f04164001d450942c06107801d22601c84080c007504024007154a8040e02c2d000160b1500003301c072024140504100c002041121082c041442d054082c060003049208451415100348020750000d45c1482569480d10540055080c0a03100d092141c91078151413078107641c0c9076110510100f04455040c4501e002116048000a200f03040e09481641180c4882c4542d050110030a199502c4a142d0310b030555000030219000c0303545540c0d0f40800c030b0b8014031344680c800c501c0380c184001400e940d074002c1700313241c0c0f4040021801140102c05103068802852440c015000316401943c00d9a02d02c026078070501d1030421442e06903044c40001001254011800c8072900c1c400100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 734007805 1250 734006555 734006587
    0x40b1e030705040f06021908131802040519120305180612070206131707080d0c03050f0a060e060f0609190617061021050103050724020a0314 62
    0x441e10000b4000150a00c141402800f2000107419180300a14203480121b140129000400102400100703000c01c188081e5807140703c20308042c090021428032102a4030314008041c1d005401074070301c03441c0c45241011b1031505040c0c0a2040b41d002e007507202444800c54034156501e501525551840d4159862940c250340c030342d0002841d0522465200d45410300e001d100013070030300c90003403c51000e0103480000680070854900140407090b1000505a550b611a454801c1c46403003180c4e401c42d101c50512134249443c6406500580c4101c4036031911620580c0c6112114040f1600740c05501800400d04021881500389441c5000c03640d400a40340c10701d41070000c0c0001c0d1940036450310412003040d4100051006030f9103d209804003010714010741c2d425081201c000750054200c4036a2204014400f400301d4400f14600101d0390b100c1c4411a002c000700e50f1139003001074417040d50b8003440969000050440000c014110410046880d4940c06442444003564040b50030b60002144074003140f1081c45a0000ea83c5151 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 734009055 1250 734007805 734007811
    0x1d0c04181b03060605031b0609030304030606080105100618140d051006090c050405061608041508040b15030d0e01020f07061d06090d0803091c020610090c05040b1e03 73
    0x5040c0c16a020301c0c500c3c200c81524042d4011a0103a0042c1801c41040030001081d00740b0b8080c1282c0c001d40b511403c0740030a06d140256030014240d81d00b04440002ca0741819813003039016003440c09071610140d480d84800e442c411004102d03041c3c40a00030b031040044240c0304418400c02c2d070004120a20010050319030616142d400d141c44281203945507020444541c0f14898841c030b4080509229041030b16203030004105010303070400d44895001c034046c1c0000b000031820440e000f52100942d1501c440480240c0240202d00807101203d1841e00a400305961000e10340403c90400b100800400c500d81c03035000216040745001d00c0a82c154801e801e40e800c1200340a004d160003030100e5a1342c44007650211180010707400c05042d061030054a0400000d907154898440c4002c8164101500603581d44642111a1800030003002072800c10032101d14540006601040b490302035040080d502c1040341c1c6030651f4400702c50308a030783d10003c40c03000c000420615203000007500c46003183c5100d00c0e1045503100d40750242c940c021 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 734010305 1250 734009055 734009093
    0xb0f0417010c09080c01050706020c0a0f0f0c060804080f0c0c0907031e0501030515090c031b0127180b0307080a05101811130f0506041d0c0418 63
    0x3071002c0664159200d0308150041007003d00625508504400107055803040d81005081d89400280740c1d1a0300070100103040702c49034052100700100b02c050500d1560744007442c10803142007002c40d10001c0d42d64440c6040034012078010001c00d16124070507405070103d034850010101c4901a100965025546204015200d171074103441c04034030360000c0b0078001c142c4500c1c82142d200003460320b40188040744002540050721019641500708075114850741030b03c1c3c8118003070501d0b45482540000c40305214801a58443c6403000c0e01c1d0800310141c4000984140d140e010341621001040c080e040140c0c240e015500c001d00310403070000081c14040c01d00880e061803040e0b04421540c0d800701c4210010803104001111905d180c003e01041460003102919480c0030350107034050002c26041510540aa44043c8030f039040381b5004e10100050640740310100003800044503410b2140703150038100300f4003010703c0c4038102d800c506040180150f030030340104210052900444e00c46d0548069040c941c0061a110b20140c0600d0f58 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 734011555 1250 734010305 734010311
    0xf060f271f1e0e0a06090305040b040f0e0c071502091207030f020906031506010509062502030c06181905063f131b0f080f0304050a0b0f041701 63
    0x400c14410080144001008010910340f42c81c0d0b031114040070940e40c101c00d0344402c01062280c0c45080807030b0310b40259000314840b1000042e0001d01c815460646104444184041c00c80d240d581c0250001e4070b0040003070250450016000d401d03904102c5034001e09403060002c0c110a0a440b070f0740c4030140383c0714841e002107540503203500044041d8940103480d5607010908500078454141c44680a544244028150b00c2c1840b0003c550744041e603441c60b041c0c5010810a10f442c0c0100a03403002800595800c2c14400d81c060700480a41c843c650a204045480b400501410120070714004000c2c0162101c444450840740e031020180428641d680d0002440c60341011055014101d0681e0f0801100d440120361124202286210300c0000c0c40f116040f069109000c500102d0700c0c0c4001b402c182142c803c1c084411440c4e602c00e40b0f00442c20161000c01407017620080c07400c40c1c0a01c903030710080700d0b524403c502429034402c1c0c40481c2082040700c0100241140304a1440c0e240c00c196440b154010b6880c0704008000d03050351 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 734012805 1250 734011555 734011571
    0xe19060f0b030406060b0c150a0b04050f06011427030a020402040f0e0108211305090c0d0e0303060109051c051504021905060a03090c030f050f060f271f 67
    0x1840e40940400740014814280c0b404840d4090280e0301c3e0760b403502c040c09200230040042c41d00562903010340c0d148817020b4010300080c54400c1c0c1ca4030310a0812112a03002c111704810140f054850102036808414409901d030200080502036030170f4500c084210203a252085540076030058030307640080e00042c003031180700340a82414200e5810076424160040301d0300780d205105441d075850150b0605600e40302c00003a410307928038880d007903039014081030f4204c5604401484240038078155144004c1a9800000c2420880301d216403c40ca502c0b44410b458880c002510007106000351714001c1c16000138040441e20401a0f455607a854904040d0505148080c06280c0b208000660800401c018100707242d040c2c10700c1410782002d0010713030a40601c070341800030560b03a40454010440c1c1040c1104c040d64104c10401c03641202803500550b6100c000c0d1201109020b05004141010030000320540505010840303000c682c462072020412003078a4410000c2d180c8180b40c0c010542040302aa03102d0040c19030350000c26848 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 734014055 1250 734012805 734012813
    0xe0a1e1103010c230a0509010e06161103100b0904020120010c05090f120d03050c040b030c13050a03120f30060f0303140901022a0907090e19060f0b0304 67
    0x191030401e007030031950000c00c645c204065002080320741d402001d00b070042c4001010340104030380e4028040a1103007900002c420000303000c102c140001d018070702201250680a020061803090795900100c00390000b60160100300150300039524ac410040d00c1001c40700c40b00d09462512802d460907003031b03200040713400026124040c0c103041d51211007421041c1c030700320201100031032041c5d0794801030005003040564500c041000303041303a0000c40b00245142c021003526800d14620302280d541c00100741c0d0201e8500300034006980c1c200b8100c403400700c0f41c01291413528012015819500310f80d242d0042c270104403204002450b400d001c00c00003824103000c18840900320380c0400c1214120b4056030800c08850210460410000394400c03510304000c58400406a1200816401030345011441e04c0349138581c14400e0700d04010041c08501280300704804a41403000c03929a20301c02c1d05c4050140c0503042c0c2c44001c190000350480710010305840d103d03c00d00e00015506561760800c080c52070703050f00000c000750800814003041c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 734015305 1250 734014055 734014097
    0x50c0303041119081c050c07060315050d020d08070804120b0403091a1e0c0303130618030c02060a02150a0204030302010608161502012703030e0a1e1103010c 69
    0x1803d011600d0401404d1030016075441064404400f01046200e5100c000148107009851a80042174201c50600b610380202a010b0018204031081400381325400003241c1c609219100211500902240721880c11921100241d030b0102c0010703685050304001c0040e90814124000040720f0060000081d0350402e45001402400f451b44029000c06500346901c0603a04010129125001c4100e04462101d00c9800c1160303903409142e5010b04540800f00420020b8078085040350540b51082804114100101c005100c109032400c4021b00040d40d82541d40005091000c010304860980d030048480c045c003410882c44c0c0c0d0140c211007030382c05aa0007007000c100305034090107040090b001c40700c081c122003002c00c4050a058074640c4200135044020150026250b03000b0b500c048a1114031502d03900d42100300700151005950240011030001e85000c05101d04004081000d00d00d069218091003140c0c4807000f4030300c03041e4034071410665000500200400159400344140ca0112409456122004030412000c1e481 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 734016555 1250 734015305 734015329
    0x4030e03160f05060a0c0803090609160b0d2301080f010b0405010e3d0509070c02150a02070b030907150207061707030e100e300901050c03030411 64
    0x30030003850718240800c0d010494004103841c000c0d07500d2a00c81ca0b0791082204d114403480f1015200070000418000806804121030b0321605a4038100c840c40c4001c06a9000220203032f12402c0501c100c1400b000d600591241c1081c907803900706481120b00500000740007040c00d07400382e11880040d4401042c03210a03003002c0c0079200038048211003c003c02d600d80020040e801000078401c4008040308203031b001c4485029080451200000f000140300d4410510007040002124040e481c800d0003001c00045a4600c40c4400c084110750151a07951600703034018400169030040850001940900b21021404128400255204190a030b0040008514080c40c1e0000d44c034040301528115004400c050004a42040459800d0800703580200318075036a0250450080c0a00c85841d8902e000d4496103103c1c90019800600e501e4480320251f0f40703400c102a42004e8201c812012914014076020140403c28000344050940e10b10181062850010aa8061800e56000729001c03078450820b20b410705000c0c1440508011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 734017805 1250 734016555 734016583
    0xb01120c0801231e010e041407030b06041b020a02041505060a03051f050904080a02150c0c0d0e030c0d0c050a030c08060606120f040c09020406230405010f05130302030604030e03 78
    0x29411343d000240184600c140648030768140718902003020440c10849420185047c0c20990320b420340c60f0303d0700482038401501c5c00c620031418038803415850030070b2030490902410580c0007410106080c0d400c2c4000381c1800300000400c44000840024107494440c010600b8445a0780c0c00686c900c0c20580101400c024600c0d00c400c17400300c240003481766440318410f0740e030080c0e04201080d440e02c640840403031030003645413440003c0c1241d0406102c1200d08040140006030a20f60541d1000303601a98104c4107070030f00c003070641d6055100c1d9065071151f041010304503903464000c2c0c00c6000070f50340300c0d00441e042e9030a40e48201e80c5071040c10300030850040140141074000700c007100e606150407003c0070482d0700c0303802c007604c820b004030700c0ca001103010040c40e10001001400f41c0c002c250744855a580010340b0b02a00d1003220700c4200c00d00c510351114074000303000b190143d900c142c40380c82c60001d01030301c21981c43d0080f0f150100c254801071804130151b541002143d110340d10a40c2c4440c8103445080c24903040010400c0207038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 734019055 1250 734017805 734017831
    0xc0a0c0909050619180f1a10180209032409030304150e010e0a060c090b0702061b07180213210605090a02040e010b010e09040b01120c080123 62
    0xc001040803ca0a800c00d1a110740b04900101c0c3c03240c004d000b00381001c41c0066001402d40341004020000e9680e4035070754001d801c0d002d01100707040721205807a40c0840340101d405000810034440141450004c20800f80a0000181403010020102e85005145c20386403c1e80d00b03107055039240680d0005180391348010070710040c50030760500e90baa00034058410760402c00f07120740395070000c400504258051446811a401101c001040909050b0001d08502c08810001408001d012030300401c21000c6a0500b81c3c0a01428500401d104081500600c1c03081c01d1080381c0240038000402031130304103852501d200e80800040e03403055034100400a001907584104190482201c580100d40c6046c0d45a50b803d54000030042102d035126245142808840d00d00298054035040e08115406415401501280c0c02a240d41600b603655208010000f0b004031703401421003075640c0050000b070408064241042e0300c10450f9450741500c4504035429a240c0354842c0d12a151040f0341003c0c1c44513100030141d0018011440c05d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 734020305 1250 734019055 734019071
    0x1031a07050a020a300e0420090f2202031504110d11040b0408070503060c03041e021908060a0c0306050d03050f040803030709030b0601030b10080702070b0c0a0c09 72
    0x80c0d11189059809070185016044024120705c190301928181e0208442c0c02d00466441341000c0d00c1035481d80d48007030041d4a004280c00341d40c00201f114402030400100d405052540d4039040104855140c0e01141e04058010301c01209030a80b2542e50080c01007038640962285000440f81030050500d1b44502c1c400d17410080c000c6152000741040305c865000c00b076404940c0c07041825400010f449180d10401c0740050015000075901004141d15096441c11000d9480030b48a2000621041c0020b40700a0044150000f150b00100449481c43d035959101403c1c1a0941c600210007814008041e032005c91240c006200304001410a4820f0410100c281d0074100103090400d404200c40e04415a00107041c81800030380020803007401001c1e02c004043d410122944c91802e038100501d00003081c40222403600c200f41c0810035035800303030207a100b1204000e030000f1011a0300800442d010b400140202055000384940840e400c03030540020024010154028040340020f8680b00203a00e40c29403225450519084e41 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 734021555 1250 734020305 734020307
    0x406030803041b0b160303060e0c04050d0f05011109040b030f1b030115080c010807030219050d020d090b06120106030809210708060604050f0613020309030c0601031a07050a 76
    0x241c0340c0094105a02800b0407070a02c1000141c84290f030000c1d4200400402c00e0003c01c11400b128034075807403186c3d40c18000e040d6501c440414001c2c065440c1c40d40300c0024007051120782404041d404aa500401c10700c024003030a500c2e818211000503400c040160800190107485042c90700520b00c0c640016070062840c401c88001d426203841c0180e02852481180c00700c1071140d40c2c3c007500305640790f82103078100d00f41445ea510610350b0b0b200301420950b030100d10208001003c0ca8068403e6803030341030320490012100c1c00045c0080b1101e0707100f41c0003043c05650a0002989910651082100c86d601c00e0502007081e0801c3d1082140300c40b00c80d41140341c076a040101c24400100950142e880c10f05040e1035404d14580824910049120700060840c03052042241c0052074000c00280640100800e903000c04c5192560413100d24200c0307089031003d400610380c03000008469103a900859000188400352810104086401c1c1c1c1010020f902c01e071248041d41b00c0703252120005030b0000b0b40109a030b0400600d0645a404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 734022805 1250 734021555 734021557
    0x510020a030e01140c030309070f12020f04091b03021f020304170304030f1b052e090506160b060102060424140108010e010b061305090604090507030f0b0604060308 72
    0xc0003002c1180c260002c0d02180d0190705001e001c020f411541c0d50703c80c400c041c80d0780d070340f40c0003200c0c004103901c80d01d04002000904074110f10185e078507294046600c06030607001c2c4140d00102818041c4c00c40d54800c3e020340845c02009002034050b66030318124a107649103004000301c1c10041a07044035800140e81d440c0300f810303400204030b03801c40fa1702611038141044000c13100d03411070086a001516038040510b01604000e42a641e4036035a18400e183c40d1440e90700c2d58248864400c0481103034550710510f103503802040350701e11244404d14115182062496489001241d03540e0001c0303003030200300c00e1a002d00200b0400000c50040d40301d01e080c8028460f85ca85074a42000e810042c00604845010801c58407000030300b1074201e0019442e405503800c1080d40d4950301d05000704514150070300c07254a810b0b00807090346428006c5540c1030071440070715a03205040100b080100107020740036652195071030b281240094010b0101c0b10003980a00c0c50809010241d00b81118000d0300100142d115a10300302c010f20004034840 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 734024055 1250 734022805 734022823
    0x607060c1e270605160c0504050403110d080601051206030f0d050d0f0e0a080a0e04060f06110703050c04020a2a0c08011806090f0204050c1c0b0a0311060d24051002 72
    0x1542c1c0c04411650341440811b501a64125a400c24204410001415001040c08070b50000c400c084038541000300f1400c8601c000290781943c0002c0041081c142c0312204200c045d0740111006017560000884503510b00e01d0291800c020f5400308001182c000980951841b4501000800b00e1081c0015010071408035100c3c4040704004040c1d034800b02c0d900c0c0807144100c1303a00c6142500900100300300394494010111805c054072560000610700720f040e0360740c1e86012651008880c3c2c0803005080d8105041d00704406500204009000c1041c40da50020380340300302d0411903102d000c032500c40d040303044007034142030b005007640d40c001c1082c9a0500d00060101100044d90125498100c1400a91980350746400480041d0f0004040e50040c1401e003400300300130001c002001103485600342450b0381c2e442190418251540d0342c2d01e4641c0051001010404104a43c908180d2518024249468007034034090140c00ca406004c0c60b004074810241c0080e0200301003891030703000b030729040350201030074003a607036000350340d40110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 734025305 1250 734024055 734024077
    0x1d240415050912030a02040509061c140307021e030d09080a240c030b1207301406011e270f06031b0e060607060c1e270605 54
    0x55000100e00100c02d010f1502c192044650041e034909068100e240650058002d2510803216407010500701d207400e00840c0040f20806854511f081b5568590951101c0c669103144e1030ba00003040040c3c0180e0300c040c1e1000414039038035203501c0500035403400d05183c55508461502400303400d0006100c60140020748001503907001840080c0010358000710344d10080042d80300e031801818501030a21031605504400f1032540d090310001000c4034013010480d41c4503091320420742c1c07000c14050b021150009521a52000c0d4004144031070529010b5540c0f5104425942c1080352140c100e407005205101207552000c1e05c070300c0c810028003a030900f001010301d03180070103079080041c00d10607003a00707007080100f070f0800e1041407007a0504001c01680c9013040b12002154801642c9040440324000c40c004012100550003000e014080301d0134092155280c42c01829050317050014000a01203081d201000d41901d43d071648010354440142d280c0170b0341403001c0800c41e950036100c0310784c0c0d960051088507406020360303540703800c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 734026555 1250 734025305 734025311
    0x140f0414010207080c0d1d0a09051e0f040b010501050304080306061b030307030c0e060c1e03190c0b1501081b070b0408070c0e09030a050c011d240415 66
    0xd1014000d00a1062000041120718045041c0c0244040411a05031210241e00c1d00322020742002c0d0b2a203129070b0908490b9030f002034410710230b1002407420b5001c2507100d2862800380f440c401800c030322500245811a080e0444800600400041008001546005140a007011800c60400e5034400c4914000180a20301540000c151140520b5040300300c81301291036042507030f58030708101e01d0086c05040f540c407900000c14818011916581001030456001d0182e01c1c1c0500b0307072032840501d0200c42d0501981c680d500c5d448184030401410040b0004090811410b8440b4021014140390907092004002c002c083c06001e100f040c3e01459070401ca01c181d21144105500503103407150184c2c02840d00400d000030386203103600c40c1000204040c0e04001e06605006083e03040b141a641c10030b50003c210100c1c0c0e403907241d1b001481020989402000907141d111030001c008100d0740f0700281803042d80c0c910845480302d40c4d4085080044541e0307000d80c8400000000c04941c41103403074203031680c0c041b004091003001c0803169 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 734027805 1250 734026555 734026583
    0x30201030c021009082a030d0209130f06051e09010b03060d060612020a0b040614130b0a0305060103063507170a0209061c11040204080a080706140f04 66
    0x2109000003c00400f02c440d04100080641c10507240365002100c00030080102d142403402d0f40001000702e02c0d102d625050003540b074402203080b40406900050b100580200c05074041d4401c0300c0a6010b114006240c0c1080052020b00c1e000070058032200c107003801c0d4068481003605400030b444019076581518031003069980c0c0c9407140b03c0450020402e201d405450203240c03400216121613032500e68032080d80200c3d000c0300101d4a40b0b0420340300e07100d54840c0e00301049070601c41c4019466001f0240c141ea4102c1255400265074038020600c555009900040000e035581003045074030340c1c0521401c4003030003605241d441c0c07544030503070304482d007020b0004c0b69800d1104c1d6540a000640e07080108a018040d50448110900783c100c1809903600f2030250104d00c11320903400041c1160603d96507162120031881000201842180c4501c2e5004104410050700280c003044040f40c8075104010417441c56200341c00c202c3c0d485140b81480310031030b400b0500b9295085400f00920121000c440b441940003030300141b06980b000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 734029055 1250 734027805 734027807
    0x70b0402061b0a110a0e010e0601051303151103070914030307060c021c02030a05070303020a18121131091707061a0a0603020d1413031b0b01030201030c 67
    0x1010340c03800410380b441c2103148041c0c03060011685030b41031481024100c0c40c5643c807200700314540b040b6001e521014000000100207024800e070f1499004141818201d150070880d000c004114072440d0000d0300c1808a03402502c0080c82c182c400e40641d9880164214250709003600c00034184030552183c2c20302e03100e028401d10785a80d424411034007042da00003402c01c110317441c2c554007a45904100b14441c000342a030300e0b89800341c43c2c00401299100c007101d684007440e0810643e0300358029080600301030100001c420046103c501840d0f10303540601210440b03a00ba041051a00b0004014280002ca008101841442d40802d0081e204828181016000000b0342c0d110f00c5460300080141441c040d041242800580c041e0551202c000c20980e805048140000d240064402e40745010710b26143d40c00400740c18040014034420303400752840b02110700020961252840c51040f40d1482130740c01c4600c8820540c0369504154101624400c5050f8510f03000d0801107903a01c0300c031809081440b02a05064884030240402 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 734030305 1250 734029055 734029057
    0xb0d0f0b0a030609140303013c0803030108070f05100305130803041a090105330411040608060a0b250807030c0c06050903070317090a0e0402030c011103070b040206 72
    0x102006040401c40903942d0a00d0303800f030100441c00b03440641c2e582004004140001c421030307040c2ca411034034048669640c440c1e102007880b42203810402c1c4c0d030070715980e00e41e030380e5a015001001400d2100055840394101005c0c0790801026500030580c0340e1180d0410001501c030402060354040041c24000340e15a50203140880c40c1e030b03c41100401d504000404c2108001c0200400070300101c1258002c8035550302c441c1e10307034200c940648a0022040c5000036030180c594012031006540580c20400030500001000890141c540500600010038808034050054a9200360400c2d800007007160400622403400704036100e1407050002020a20741c1c2145051040c000104041e9009a81321a17103e50716603290078000c150a6094030201c440a0040300001a154400c000352030319000014007a000316032440da100482400c0812013030003c1781c010311203c01e180e42c401e08240c0c010500201940b0442c0303010720400d41001c2654031280c2c1848ae000d90140800d41d4000b080c0e03000681e200c03155010310380351f5000180807 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 734031555 1250 734030305 734030321
    0x6040203180f07060801050d030e090c0c120d0c17040602160c0b0d0f050601021b040b0a06021c02120d2d02090a090b090708040809150417070b0d0f 65
    0x951155800569000c2c50004040003215407a079103201030350f41c8038410010b011030300ca4030150024480c9040711034103203001c40c2c040741c0003d8400343c4185412952041c0505080d040150222030b4030002c1015000c440d01070142d011030a14034501405110b68003141c0302c40c811030180c40904203541c0030074040d5160b124500d280d0b0300150820255032032580e0350005a505a031001806d80702e006c0c01e040721030107100502d008150040300160090301c1500510645265040d060f0b00036564403d0b02c4180744d40e42c9841e9501100080e211a50103802582e0307000d94810607521602c00b42d82c04651141031f02d1140004104266259a50b1802000c54081e00c80c050188051844100200315032040d0800f540c0304060079402845281d5041d500700b400c559036000c105044811030441c9581100c0000000380c03806204095050380705102c0d5500b01d0402d414400400c20740c880fa169000000d907400501440000444903030340c0090416030008062850510889403028002c82d0803020102d82c854030034014814168000104c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 734032805 1250 734031555 734031601
    0x60313150609020d0204031202010c0906120b0a030b0708181905100e01020d0e0c06030c090a0b1206042a03020c240703051f050603060607060203070e01080c04060806040203 76
    0x504c4446000c07101c40203520500c000c5032588082052480c0c81e03801800f5022160b51f90341c6841015918281080d110b210f224200c10040d1076445003850090740c1c80303031310010207140138086030402850700d02c1c005050914003502c0f4910341c840e0b0210303601401c140041c2c10415003816a50071026601145002c03464990491800701322141801d40d07890701118154090140000040001e11210b03003200341e582c0d00c540c000d48803190404410000134503c40c80c03080c0100b0301134030054030181900d07036500e060391140d420a42c8051030110011003440400e00d01402015000d032920501c03c2980000040d41c0f003051a8407107901c106260f0040343d403a82220003804480701c0d200b15800072401015503000c8442569104454400102c3e2a01e40070a000456051841c0f000c03c02c6141040222414881082303025000209021f40c42a403c1040100160b2180003442c0520040d03114060b035000000d0000d0301021004040c420400010720040085036808440345400040541d00103a40f82c9642e24404d9000390f40c2c2801107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 734034055 1250 734032805 734032807
    0x114070c15172e081b03070e0109090b0703020c0c0f03010b030d0302070c0e10060309050a0221010f111204080f131707060f1d191406031315060902 65
    0x41032040c1402c050b112140c81c1d10b1080044409005403865441d05a4021103130f15602624040617010604c1307200d4480d22100500701d6981581d41c24442c0d004a400342c00400e1055111004034040004040301307690404103504042d400e01c031002c08580c2d0744203000d010880c070841040131403001c1ea444c2076015101c500303000360940d00101154103002d0b010b0752040c641182c1440070031100043d4100c41e02c0b41c15006d20b03401c58068206504d03042d800c80280007a584180c0e1075000c0c00f140200182d4490801c203600b1000c900d01c1045174110000740c0c40c00c65031592140c41281e802c0422000419a4100403106180310003003082c052030704c5a0500d070b4200c4c01405c0103140030b005c0010b40c0e000c0088401d01d42074200c4103403002d000c04000d01006029211061840344002141038100f1098006006105401c10b8040e080456190442e0794400501003164041715803403040942d00e070a100d040c2c000aa0f42101c89000d450752807550400c032018042d69480500081d02c2491080304204861003103800c031700c0052220007001c2d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 734035305 1250 734034055 734034061
    0x60904020f2b030206061807081f06030603053a11100204050a060f120c030e010f050a0c0c1a180609060f010503010e060609070507140a020114070c1517 67
    0x250800400c0c200b0254098490000040c030750340f900e5009003511540c801d000300a15203810b401030b1401c1c1805082a9103485e64440b48000070b9044030740340402452140e6011500c1c52450402509140c5052240400120f614815034100c0c050360301170f040101d500700c42c108084a24010211400b2101c0141310b040d90154100c0240c0710180da8002c1c00c02e0300d4003158202c03091541c8000548456440402c0c500100701e125945000c07940983e0b000124194050402040b60041e10f001a07085841c0d10803a100b1160f90742c01404000c8407140b01c1c002d07031582c3da42070140107a845034540d0300c000080034180c580a01e5a01000469404104140c070a0b242440c1040300c0b1030341440a402030b2118400c9490941c100c0c0d290000207102d107014003448100300c418002401d030301e0b210201446a082d00091480050240c20015540000c1000c070340303c0d991189a10103824600c942c0d100042000c111514007a10140c81400004049007002c4207040469804050040704103901c1c200548040810042c64000b480d404810 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 734036555 1250 734035305 734035369
    0x12f100504050c03030703020c0d030903120801060e0102070f05041a1201050103030e09192a03060801050a1506030902150406020c040c02061012081e0d14060904020f 73
    0x90041d0b102e482640c0080201006243d960300a500016005030b0200d5a5400e01e4144203146000c81c40c000c0c0303450300c900ca443e625419804003240d02080300140c601001040226406490658603003402d2018080092906804202201260180c0d41c8600c0d9074500420006000c0c101d26000100302030000c0000210791101140240340911060f0081500c5010408031480d0280d01c072442480110882481c040400034007400600440d200c3c401005800355848408a840340c0c00d00c410300501d540c007c24042e0401241d43e0a441c80a00140307441801d10007254251032825414005440b20b6140c0000e942c0c1090002030a40c58017903000d2440301b500000d002c5042a4041104134070303040284d400307102c7d405203541d007240c1c1c941080300c220000590400c010300100a526440e00b402c00e008074000760074400612001940c00003070f003420081c2000000303940ca00741c40c06030290300b5044d10f01190001c120301d8100c0103d101404004e0000744110180039110999035600b103c0200722212800b140a102c0c002841 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 734037805 1250 734036555 734036561
    0xa080307050106050a05090a050403021e1014010501084317061509030a050d08010e07030c020c090a0f050f070909090f0807020a1a09120c012f10 64
    0x5000c0d680d650800c0030109190414001c5034045079001f030080d40c100e03680c58801c58001d1801400850442c02000342450078008041303c00c066412000d03000d044010010030014007141e03000149080300000600040080c1c0c0e810072a040c0c1c0c4034440d0403805641c007038410740d44940320504c8001c00bc00d0326000d2868500103000e401203075160744590b0300c40f40100802d0940c00780081d0011500198480c00100000d003000d00306c103014000850010301106c1103074071241e40c0d1a04040000100e03400061a41004014800310107610a411040e241810440a41006002501c40b100a03070030342d001c0c04601c2d002c00c41c2d1950a6010102401c1c5003042040b00d03003131980b80c989004500b0f545400c0098071004e404956002c1d544205c1c44c2c900d07400b021006204015960300083c41d00309a1040e41d0065144500081d0940741c80308811740c0704000c0012507a642c1d011700801c60000904000b175801544020107003941d50341c100000b00b141541e1601c4064081908510140c8180c0030301e10508a00c2c0507200e21036804110f00c0e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 734039055 1250 734037805 734037817
    0x1401121217010b03191e0f02040f180612110103050601091d011502010606022113080106090f2c0f0d0503090708030f07030507210c0b161211090a0803 66
    0x8805210180039803044060f109540150010722400154044141100d6408640c00c0a0100701c0581070603500c104ae07034802061580008401480c0b03640c90715580680d40b0840300036001d2141e80081d2941e02e030b220082d440e020748000c10305140e500d40c0403440f42d82c02520307800001c3c400c14405448140300c0c007d09180c461401e21404a00c9011b007650241c0a41c01801640c058504960051a103601d102566a00c0100800c21140f00308104106c4c461b4031012400d52180a008401c0c0003083e2589040c030b451044980c490b60f6007400624281d0703414042054021107485002c21141b0001c1003403007004000b4241040c0407000c03a513038407900101110041d0400d0156200d02011410ba402543d07507005c0075504e903c992a61080f01e18420000800001c0c0078101400d0950b000301203010b002c03130104d4800e2045500c41840c1034089203010702001c04010199502c2c07507200b01c00c2403c0ca02d00c5421040c01615030410014445440e50311105075441c0036001c1429510300d544014441308034950740303480c001e440b0707806a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 734040305 1250 734039055 734039071
    0x30a020d1505060d11070c06080106140f0d0b01030f02031f0b210405070801060e060f030c030601120203030d0c05040609080304050f04023a1401121217010b03 70
    0x41811003554680c961048811510090440c03850049007041300c4004080d00083c107030300307000c003442680040b070000e14107003002d444a80c59001c40707075052010190610a041703512808418082000740c2e8044181c109070f9940c03410001001c03802218540069014003090000490494408410812110401c6510b00400001400c104840c0f40d20f46000e410725100c0c09103000c56000c0c00000042d03040840b01b80090f8004c0c001d07811b440c961a15811a582036070060b5110035800c3e01c4a101381300003480d00000700407105408800034461000300b0380101341c40e000c051050720125040d211a0304103540f002d2040300c10b600701100c1b080020103040080904250064043c000010748018808621441e0010403a026140c0c000c1034128402001c2007000043e41c000d500075083c1640c00c030b441c0d06080d1028402c905e085141c00c0110000d1140484102c421101950703031000303800c4c3c0c10400410560400301c0310481a10f0700000070801c010209101540d504c0711400c256598154007000003e100500c0d034018502607042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 734041555 1250 734040305 734040311
    0x4050d030e030313020d03050c0a030207051c05060601050f0706050c1b06091507031d0705040b0303070f0f02040605060307020609100905030d05430c0c1a0f030a020d 73
    0x154908050b9a400700301d80b45070781a00004d600e8009454000000b8007040c0c8a4a0a0b510740180301004a0625080c860128050792201e08180900e1070581016041407803039035010032205400307454203562040054280da052010019111400500e0b1a0860740c2d0103400000070b015508200c8a0040d056005080d040080ca04503503480341c0c4d2000c04035006000b010340c1c500404245100c1948610780c0800070b00030400f45a80c410b0101c50b0b512582210008404548025240c510b240c1400e01041c1d40024a51030701c03903041000300710b0015080851220690f50003513481ca016040034404100240749941009070700c043c01100304010281d0010b403051184014606680044826602c00d000362207101e04010450707001446100600c076504d9000c00ea102d03260781c1c1210b05400f10074113411002040c0d94640000c0c002040345c00081ca42c00f07008400f402074104e03c1c0001d036041113030b103032613039692014000c030360384a030301c08484000d14907a0300f0030b980b8151803900500d80d80e41000c640b048025404081c1075414031342 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 734042805 1250 734041555 734041571
    0x2090a0308070c06053f01081f0e0d0c0c0506070c06030608030a0906051c0501120b01081c050f07050102030a090b0a09051b030708061006080c07231504050d03 70
    0x1c070510960703040c80c505900040ca08400c00c0c11030301002e8001c1b410142000614904004505029211030b802001c0c81005000d040803103015650615281c1c100d0040041e0811641504081c00050302c0d40640e5850320300b09000c00c4483c43c2c0304803a108103a00c030a0303020601042803000c0c490b0081072503040b1202928104807080c3c1d2215059201e02034059803002144401e6410050300340500010102441030007214840c400390b00e00031508544080c0c10800020507509206800c00001c4844070740034014550052095480d40c0000d01662880b03166800d040010101d012480441a201603402d0a907101000759280c1c68507400181c01401008402d4424000050200d01c02070000d21651400c1074010010300402c102d02c0350403804d681d290117445505445102c1c00010092001c0c4a00d600403161400000e4240d45030031380040803400041c1c640000204200500c00000744152019481076580200441d48000918422803d007a070514a40388640540010002044000304001c81354400d251410000e8038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 734044055 1250 734042805 734042807
    0x905041b0f181203110d0509030c19060e0303191d0909070911070204110c01060608090a060515060a230a080a1107050a0308090c1518030102090a0308070c06 69
    0x12080c101140c002e8605450502400291401111000780242440c05102040340241c901c0c0180016281c0e0000318003140320042c601e03060002140b640012210400414144406a80408141d1007030034180841000b022006440030702c05e403403041e64000100c00d488054620003078508281450000813207100300e1006052440c0c101d40c4107001e4000f00c0c0080c40c2407400c06249100401810440b1382c036148044c04040010b80d1a4003c1098030110b25411a4440381e00c2c0c2d05d02401d540150308403d062110300010003020303050000700084056040755010820380c0307540c3d05089040b41c50b040003e0300200000350102d400c5030011102c0c0303c10b04884c0103507181c03010505100034650194018280004060030045690b0003080d8100c5082d29556005651600035140d40741840e01c0c1503030b40304401198421080240d003c0717061101c006584010341d008a0030142a110103410751003481400b041c45848a100348031242c409605070303194820080c0800c0800380e1a42429905a080501c2c100c40d11040100c0c00b090321 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 734045305 1250 734044055 734044067
    0x201060f1d070c0606050303040902071109061302091c0308090d0815060f130e0a0b09070c02042313060534030212010b0c06070c03120b010905041b0f 66
    0x5001648074509a255507500300d030307402c454070001e0f90350301e4480c1c1010031140d40070700c02040100100200166103850f245043c6103110003e4917024403074100d0004102d115140c07051120104061008010f0303032180540b0002e07139501030030343c124044104100b0301e1804040d001a000c1c0d01411102c01102c100b0054a18111405601112000130b46014504880e94504086002c1c12241003030004040c01c1c02c01454071801062240da04c07003100703410030400b8082c0c0d0341031910402c01e400c5810388001c0071038688404058000703900d4000090041c0d81da0740c40001902c1c60340c503040c2401079101d0b541241030b003004d03044241d100001240940d4000d1406001c90414800785600c0f0802d00070001d0003001050090010300407070030f0200101030500d5020411186035003e182d2801d8003070510101b0f00c0381c8800780c070500c6503d80000141041d00b400059031101e030102c1c0c1c2019000400b0200d082001c50f0721a83c090048610050300c3d4001500141085510404120404200d0410125540d691480d0500d480411102 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 734046555 1250 734045305 734045339
    0x50312060118051c031215050a060306290702030a0819090f030206032518060c022407050f0c01020c0307060c030e120a030e0f0a18090311030a0201060f 67
    0x3100c04a0701402840d000f44c0074001c1c0d08640282031050090060803402c109451040c4a204030304420b502050107686050490341000d080c0703d04e000c0091a0400c400d841103a0300c2900078002c40358801d80480c01c8110f504046a02c0b1944c082c00380d40c0103889529180c40150440d440f4000200b603800351050203144a401c4031070803140c1e80e007a4107041c01d00e1038080c40b16580c030251521130500e03a828401c0348600c0100050b4440707140c103541d580142d0b001540900500c42c1c141c0d017001d07040040d2080a4000f682d03900032000030752595801013008652941403282090300c20041c0c003d0a030f000b000c58103d001344c40071540240e01c4d1421b13025548510704204c2010780b541d081d40103440c003048a8540b4400402e02c103103140101c9400140c02c5462000c2441c003040c0c913104020204400040c3e07003d401c000e060400c00d0319040c50910540300c0f681c190382010030251203101d040030031540c1d007559007040c0010705203d800907103400d0031090252981e40790f20940c020301801660140250b161041140041e000c0015094454 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 734047805 1250 734046555 734046559
    0x10110901020604142121131104020c1f050604020307171f1203090801020f1b100212070806150a0f0e0301020c030a021905121605031206011805 63
    0x903510380c1d8921300340d0f0b030340c600e0004071901c01c0301001504d100030b040a42244140d100c50782615850003480c40300c50140d081d84030004000c0208140310090300c82003200b02c1d03003661240703030503891101c1c0c100860000e00a012a0346018400c8140340915048500110301100b28480800d00c03980e5a400103010503880242d4443d4000364400c0c200704040b010099490341c00c00c0605101880b500803030590740c85130707a01d10b400000c2005410340d0b03928101504418500010003031a03000750704004020401e44103900400e0103000ca026241044c00c1584001032000d86000c16030480115202e07504481c90840c1c44504540b10b01c003144c24000070440764589000b200030580e0039415820701d0320840f0101283c649a041c160f110502c41018a20b40c071903074080c000782006924542c02540c0f64150000d0091a114a012808074003405070603071000419070200d0102c40d81303000001507030340e607100c1040b07002d201c00610040070300980000300b82c503803800c560b0900990081c0c000742e8800c450200d0340352402c032000a44e0700c501a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 734049055 1250 734047805 734047813
    0x5160b03070507060204090219110105090c13180609020a0906031104020d1b08220c06050a02120a050415050903060708070203070206030114180c030705070f060c021011090102 77
    0x1921440c481e02c010500b4510480016040a59400c0320030280e820801030054281c440d64540351030303542e02c0342c80f810075014034030028401821b00b41003090302c4044242c08280200420303c5c110f03015481c103401070120108007801000e9070352004e0415030010004190124802c400754440002c00803264010802520340081500d55580f20400c1040001d50042d110803c2c01501c85014100d2904085001995950b240d118400c1c507141480c10a11a00c00920340303042a207118002c038402280321303028110306444060a100343d40fa01201c0c0164503054100683d101505400245031324140e6002e4083c00c200c07a070340f014100102850540586032400f9070305901790181d2080340080c140512a880042d00015540162844e010664000c101a540240c0141d90315481c01c032040b041508007070110a9203040b4800c007140003030500d021801000d110241842081100118224003880f5007403c83c0c0540d550702100c10454084080c4010313440304864601c490800780740c0f01408413660f0000c8111040325030164060 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 734050305 1250 734049055 734049061
    0x191a1e01060507110913020a12110f03010b19030c0e0108101a0d051c08090a11030312010e0601031a03030f031308030906010e060d0c12060e0607050705160b03 70
    0x480b0103070000441943d2004003104c0c90099600c139202c16502600c1a954411014405401482220841548128002c5290200d82c2e80070510204a142e000c01040b900c440341c0c81506c5000074050f00d10300310b2103a801004200d62010041d0000c0c1c0070400c81e88100d080070354890ba0740c180c0c2c07840c24001740b01d85000c07138200747d50710100315803d41c0c015019400510314500038070302ca05000c10444c8070000004c45096210440012406640082c41031000b41d40c1e14002c07007a440e14400c4581c0320403030750a000344080e06281c110074090350f050050f100d00c0c04130401d031000d056035103006200140909403441408203182203010070780a288989006c0311154041c0c000c525001c002620124035910003000c2e03190718108514500d0005500e04002c6000b07280c00f43c000d21440d410f1030844005984080d104901c80e4645405000000e031034041804101c60034928141c602240c48c0c00c1c40000f8104100420300c680c09008100080d01342c0100c054250103018100b02c1e4076461041c0d0400882a541e4012807a13240380c14400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 734051555 1250 734050305 734050307
    0x10504050409151b1202180904030903050118060b09101401090305010905031c180f110307060f0e04150e0c0418060302040f0203101403191a1e0106 65
    0x102d00201c038400e503800e01208150026000488159038200c90071100e030301c480c642c0b00d10380c880740343c181c04034400030708626114020303c4800204449104040c01f400703a1320009001d0501484401000359006030081c0005405030201d80d4112005140c110760691900704048040e0030f10a041034800c48900280c00d00560825007000c242d85011800d650400400f99000b10002c3c80a000300c01466201d000215101c0c00540081c0260041d580d14440103589440e689080e00300500325024800c40d00714848005040c032a080c822070f2550403540c4190107124a80e80011020352000c540e02074200721741e9410001005090400c4255080d1282d43d00200b03060307880c103006110141c5441a0450070b4080c4051406035a900c14101a100300d0350306558143e5074080820542c103042c011040102000301b003c42c51850b26080d4070070031046034010001043c9124800000e60b4808115a901d10f10442c5107942c0e2032400c41c9007502815106000c1c01202d112100040f42c007003c0c141c500101c81101c0b1010081982c2e00300300c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 734052805 1250 734051555 734051561
    0x260f0421021b0a030206131d15100504031a0711120403020907020a0f05100b01050406080a0c030e0f0c040f0c021c032009150a020a081605060c0703030608060103020105040504 77
    0x214a640714020540000042ea40c0c14000e20142c0b610749890410341d0314103c1c0000608c0d00c10340003d02c85e0502c20040008000315aa40b0300c0701c0030011110620300d6480c000003201c07113000720340005001446c00d60700c2d2106824004002c2c0c0c446c1c0c0136640c55440351044900d0054480601024000d4413850600c4144014075000008941c0080d0354411114880c2141e142d00c0100d400801c8180d8103600004041c0c44200c000c0d000c0d603560b0500a007811850645480340c001d06c203502c010310b52851503903a11075031104d543c429006020b140726070404440300354044419054480706c01d480000d214514002c070042500750789004010300c0401c65009403420100240350034240c1c420700e010038010107544484071904883c40c0300103c0c08100c042c00800c1e440311041814480b415140041a94020030f040c8400451268000380c4403500b01d03401120300b0384800c030000001d5038281c200c0c080103150340110420840b82c00743c0b01c030150040901035901030000710381d01c0040503201d00007800f010340082c504000c24070440c10150 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 734054055 1250 734052805 734052853
    0x13060f1406091807020c060307090905090a060f0c02060105040b0a05090a090c030b1801050c09060a093b010b04030803091c050d061a0a260f042102 65
    0x41d040700e24141a80001855818140c400b6441c800110701c18048010340c1007211020144003a101c892560404640c0901400360921030f40354015124800203103070780300034401c03001b4065100300b09000c0c030030b00741c41c546015203102a115001481500e000040c3d9145c94090741d014000d01500c481707002c0c4d05040600c0903c0030300030320851803641c580c00c1010002e1455200c2c04001d40c003c0d103c0d1082070528841a40304001c3c0c0c0c00c5a200603030706007130074410342c03825a0040b82d035840782c1180d0740d03641c80c0b5010300190f41024859011102100d0741c4050b8142c280c41c0010b01d041c604548040d100c60704800300076111242c410a014200000c1018441807002034002c100464200e090907040755010540c00c5940a034681c454801d0740c00103200031881c4c0340016428003454002c1c3c80c1d000010000e2000e0400000d41501510484104106019184d030712031000c004030b07400810782d40f61064a0b4605e80070b81d50703d030031540c1a03d0880714022590000150490074500d041c0c41c15041d5405050161540000c0400c400300c80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 734055305 1250 734054055 734054059
    0x102030f030f15093603030c031017031603031803020106050f01022b03060b0d0921080a1d030711031c0504090e0120070213060f14 58
    0x104540c1809040900241d4800c1c603020070003000b03074945041001c00d4800e112000b680204002001e21042031a5501d4101c4460611034505054401c0d0400d0002c1c410050100140d0b94000001800140300c070000007540700740c05810b4074038030705540c58144191a40200d042c2101940061042c001206036449800075401e01a20f070100d050305001941105a02402c003084015030f55580c000c0006041041d03416090714401d0010300bc40040d500f401c00302034048045802d014180c02c4074078140942c0281d100700d001c1c1580c0310001351a00c00b02c800701001009400001d5a004400c58545200500b404541d01e130042e0181e03958030201d84a90b10300e00702401d006136840d0040e40b114000d9213a002420805002e44902800c00849004039803428503042040c02e4200c03d64540352511814041a0400101e070300311000100001509800b48401030300502014482a102c942c0100c030200089050030050304406000325100007080c0c4189100d002100e070548102100a07440d04001c00c4003040c0c2808400541c400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 734056555 1250 734055305 734055307
    0x7050f061b040b030705040312020624030307110d0f05070e160e0904020112020c2a030309010f021c0c0312051513060b040f08070e061507030e030a030f0f0503041e02010203 76
    0x149c0c0c0c0e40c44a018910f04480006a0013142000710121418004504c60017040801c1120b01e00310b10042902c0740b14403031020341030900500c02242a07845a0000d10030042e0044030003400c00b9036034900346031950404c0c800e900041c2d02c030704007143c8241002000c50904088075182c02442c5015801408441080208242d0612510f071814801c491040c1c00101508506400942040024003410350039048800051511400d028807030f0440c16180001218040c035400d00304090b0404101004070f04c0c1c0002c0c07a0440300341c802003001034503040d50401e02254550784079171910880590b040d6025011100215004446600031900720040c034201100030310a400711003070f00820b0154441d401c0d480d0a922a600c6038141240310707001000440e4080c0032103005444d244080424604101d8006008c103000300082d001020000500c0a0070103000b84403021405d4809403d96020740401d08016207128441c08114010541a45c090700c0424030030001c8903c11030b8810726848641c5110548400e00281e281c034228190b100c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 734057805 1250 734056555 734056559
    0x602010b0f040e2104060201061208070b06060c0a12030c170601080a0e0304080c030c1e010806040204030218040b0106090b27130614010f3207050f061b040b03070504 73
    0x80d0001a84a405213445801c07542c880c905403009003158402c0d4007002d0408255128000043e40c5101110041a00021034400d19299000040d01030311448000914a10980c0c000804111520311465890700164030f04200b2075800010990307002c036000ca04100d0400300500090140d40c0501c901641158040da0001904051038001c00e01d154071580007460b180d0311036913181c407083c0342c20800005401030a460300350241d0300d0600c1120340040d080903042c0c10300c00c040d00054515180d0741c1c1914019034004100042d214150440214210010396098074541c180400205406008000c000c049503501114640381c42d40603131b1540380a1b1f513489c0c04110154039a81813840c15a50314640c500503003807816400507103546841844042c2412000c5814140401443c0040c0d8068009040c0d034800100304d58050250300140219003c4100c5080078204403c50100d4842d041c42400a80d1012803240d500454003a6211820240d09101b11960202107021003003209000080317084000d19001340c018241242025 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 734059055 1250 734057805 734057833
    0x90610111e1b03030403080f0a0203090d0609060605032a04020403121701090519091103120d0e01060510110a054306110307080c0f06010602010b0f040e 67
    0x40c015501c03181182d01c91494102c40d8240e9482007242960300310015441c082c9550345140c40c1f400340e02800c00c1410004118841254002d1045400325800140044101c0e0918545040104101481901c0044c5800004619400c002440a5903801d00e005820ba000301000001e04440d101c040201b500240c00b4400000041c00107014011540c0030343e1103031012000483c46011007188140d00000503142450180181c08120302c060450340a041e05000c03a0702d03140ea082c98803217490804001a0107108800058203161030750409803425003018401806074a58003400c01d400e170b89444c0a103c0d03000c3c13021010004414040c0c000c500702003e000c0c060b2002c3c6070b102e441b51801d000252080140b101413902140300021100c0c2582003003440611078409240002c01d01805042080d0302442c8103000d01c88600008101041064542556205480729600c2210251007600d9031240c4038906c0b5a4461440085003c0780103004003190800701500042d040000c460801014040040700c1407110b000380d00d4810120 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 734060305 1250 734059055 734059093
    0x1020a0809220f0207050d02030412080c2118090606040605031909060912081506030901060e090304090516050f0706060b180a080c090a1a100e040b09061011 69
    0xb00c0b8404016141c0391170b42816410864020200b404540080005002e0410b02c102614101608030f11301a4882c1d405407080c920b0200c810300107100d01c00d1003400c0c46030081100b5000701410176440c9001448608000140108403005035a000d51010703007030100b40305251141c000b542d80448070b0f910109018481821007802c4450702c0c001036559940b00c00c400c03024442c04412200042d2031914010a5a181103059003101d00c0d11001c00d43e121380000008144800070940003100501810100220b45080c890b090b555642d206100f914036043c18240043c1900c2100c04080b10707400415100c1c40c5c5403580018031180c5583c8a05400c40303581d40e031180007260030304036500940f0070035010300560714045400008000481740301e0b900c83c16081d4031032032003080c0c80d4682c0400d03917400c01c0d070251001c036143e10303240042c003103004036080010340280030380048041d0254000302061180b4401d65081001c400807109205a11004444081d08024560040c14149100d1503542c0008503406059400030b42000a080c605 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 734061555 1250 734060305 734060321
    0x6030a020909010c080c090108132108160305012403020d02041404051810051b0a020d030f150e130c14031e15071101140a0b01020a080922 61
    0xc581d950301500003c5a01724050300e80114078070861a04203c82000000c012040042580c512a9101c00059040140d400d8040c5e00c40b1000144181a61011160050581c01f08644000c0d0f80e2050051308845c0380d009204407030588410540e109100e845070741011080d17004521051081560030401000603c0c42c501c050b00c06070140785c141d03141044180c807c20080e9030020b807443c02d012100c1200d40008200002d075481c1202c0080c8004142c1c1c0c1e035140700d0302d04841040380040344045c00c000f5800000756401310300b04203c098542c8017040001680c40442c0c04442c40d8640201c00d0000f0300f0320070b115442d40711452a9014260300003061a13802c5660b51282d507403ea6a10010000303840b2408402c0b42e00e0700340000071440d40c150f40e2000b0100c6004c8196507840324001d2402c040802010082800c1d244218051424a00104000c2c400d90603007041905a8010488441c2141071031b0a8043d143c40d0310109015400b2034119446508000f040c400300a62422074054071105640706d182c9454081c8c5080c061441 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 734062805 1250 734061555 734061571
    0x801050708012402100f02040503010203040f1a070503060127080309010e010513050f12011107121e110f1c200a032102070c0303020c04061d06030a0209 67
    0x40c03651404400c040070019010440b8030b50f40c60359441001080d030000d07050440050300b18010540b50b41d50103000c0024803c6401090b0554000030810061148030b0010302540c1d03200d060054002000d4800c510002030341a20714000082c41000410002c0d8403840c481d903940360300104441242400c43c034070024443e09a901c03010302500003250010696030400703c1504007190a00b000c6140614680383c1002d2491a07006007032140390948c0c0c00082c1d40d182d81c00b41c642c81f121a24005c100b12a03c00b06e08001d5078000d48000c480000200400d0b6a0030342c8904003200140900c0328071480340c13040210301603401c50b0000b040d10101d44a82039200c0e010307040801c401103100b0b44041c9180d100110761440200360000491801c50308a82d4070191291b00f140c0020605040341e014901502031031100300460010100d1010205038840c000f1810400380720034410004103e80c403d0b0200c07491270410750306000603203500c4c0c0304000c58403003c80005c284148030341c0880391784460010103031106520181e002800d2000c3c1525071003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 734064055 1250 734062805 734062817
    0x91206040309061103040f090e1504030c020901050402090105120703110f0301080d0813080313020a03060e010506100c020f060706020a0f030f1434030c0e0603060d081308010507 78
    0xc1582c006404c0c0b50800506009149014203020100e8050046440b880718160343d01c0e091030f99250f400b0b0200c040b850318290808069404e150400910746155000705a2040301c100000080700d142c1072088402d10201a12018109201c802100d56a0000200380301d0915882c2d40c0c00c5915034041400801078503129200f00d90301c95041c101070380e140c0b84540c0c415105014801c0d00f44848201d501c46456400b9502040c9141c0d243d0701c2804103d20000720400080d041a400364001c820020280c04c00000040c1000c001c002599032841044401c50780211101d01180c507524011015061140702d401030010090911482c1001c5541e4040c22a031240c0603020008803440700760ba0000358140a15056810034100a0100315140000c9141c0c2a40140844403c1d9680c012422080400c05140007803000068524140900306c8441c003601408441c11f2241c00101e42201541082c0b070004282e034001c00c1c004d0304001a00d07040707503a1084076034001c0c802c20400c580301060000c0e08a1090080074800c2c40155149 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 734065305 1250 734064055 734064059
    0xb1602090a0e010b0a08150915070c03031b120e010b10080601020607020d09350705040b06040f05040c020f0703050106031403070b1b0405030304030812010510020c0105091206040309 80
    0x2150031140200700b245d01c00c403148501001004070010354150f210b500d0b18021b070250b80325041d40914240311141c00100c140c07a1a400c102c001078000703038000708940c025101840150311a0008441000c1c201d0400000705810b030702d030010940e0b8145d011140c01c0c0c3c007c0b400083c401d5561360001d00c0700303100103508070005485482040003a50303041c0800364104017140000c0c2040701d00c1902c040d10b084914050125004c400c200d14054061080c4034035000d440d4003007034200302c200390b040415840741c0c69030007410700550415222440908100044408440310709524011640c10502004040c0c00c036100c1d8501180b04510040031aa4824803d080080d0300c50400014528990715140c0300c0701d101200386402c550010300001000c510601caa403a070190a809802031201c21900b84103800340500e411551b0503210104002c8104203c1000070300104801c031440070901da80c0d94080143d02543e4041c45d400503041080b410019500480241c400a0401000d000300048071004007842c1c0b4404503800d40000c5c04203001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 734066555 1250 734065305 734065331
    0x1116063b040b06070b04060c0503010305120a0c1a04050f24070e1c030e040903080f0414010204030501060f09061208090a150201140a06060906080408070602030906180105040c0b1602090a 82
    0x4011040c281814003600312f616503125540c0f520421209188606000501540402c0c4a810703000c07080c65015100000d040390005001e800c0b198110f404a4251050111274259401d0000d0000f0400d0541100407844070801e607915868001e010304141c050020041d80c148003503586035540400e03881c0c20076443d520900e4070b0400802d1100ca5004d003601591404003003001007940507040c0d43e400b65410300c01e556180c40703c1c901120100456400c861055201290210800c0019040003040312910514101c502d0f450300208011240742d03100b02440e4955102000c00010018000b401c4040001403420520f10340e01d04a5200d04004641c4820040c0d5540c8060300e60361548148540c0c002800f4541004001e00300500a0206050742c011a07091041a40005040020800c22103843d5640600c06540303a0030f2000030550341d0074007518036800c400c40c1240d4280c03600505102d450311907a080301c0030500c480e2800720680c40541c00110030021828211031102d01503141d0a4415005107a01d000000700c20841241c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 734067805 1250 734066555 734066561
    0x1c02070321050f180a05010c02070501020f0f0303043e0118030c06030f0e01020d0e06010e07050315120106060e0a05040209130b011116063b040b06070b0406 69
    0x10745106052400c814018440080d100ca580d01c00600720102030000c1c8038007041c503d4010a018020015820700380d80c130801c2079000c81c1680c12110300380c00702c90307a84005002c0c031074403041d01441802513540148000340100f1b8401e0024030340c08900d080d1b2401003c2c0b120190310b074007103010320b00d20207040b904200b0520256070100070040ca800f983d02030310b10803038155914a15109040e00c2103a0806031240b15180f83c11040764080754044102500131940c6400e20345008001e80032082007008140100c200024804050700380d20303807040c1000e81d80c2501d590b0711245104480741c40104400c2d00140709103646060681d0910400002c0c0c40151102013140c45070030f003004030f40201c41d0890f07406640140b11100301034880b035510f4601d9200d45440460702101c0040101e484903200300380e002c45171260801000700e40948100b03450a81c2c0d025996440f16168a000080c8070710171a81c035009202c82000c030788002c2e02d00741c4e1032140402c1d2001000428848800b000090351504004010348001c0e41c4c1006000c03c1000c544 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 734069055 1250 734067805 734067857
    0xf03071d030a0204050606130801090512130e101203030b0f041a10030b1e150306031902011206171903120f021903050a27081c020703 59
    0x30044110012191000c41d84950340808000d001da0744a40204030285c0c1d9900c01d84221200101502101079900d101e400d0103001084020b40d1140604800d881c5842500022104d5101101c91403000381440d04041c003100b030100610819010316420004503030540840c606146032400b07581e000c502070400d402044420103e040c03203540310340e00c1c140d00000301d4400c1c9640d001f0200030440742c40c01104124001039005e04283d8040c103510a0281e610380d0351500081014000b018801d0780e884980f5070084031403440520040e6405640b55000c484102e005400d440742c01300c2c8841c8185850b411131085c030110f1900380c070b0050701300b1aa03911001c180e0261468041011b202c00002c200600d501c1414207460160804005c4803804100549412500030849101e40480d081100d61a0010301c855a9400e80200203280599140c9005030a1990350740560b0484100314070b4001d00141601c41500b02c0d80d84d00e1038181e010000c03030401c03203001414580d0200b4081c809469030601a4a548012903a0442103810300020341d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 734070305 1250 734069055 734069087
    0x702120616230309160e040c0f0b03010308280917030406051b070b03010303050414150a1d0a03051e0102030115050a05120a020c0705010206240111030f0307 69
    0x507168080c1c1c1240c28109100c0b02082c608505960351a8030620300c2c01c1c103642c040800420858a0000074800c0c0302135150034812805500c505a6a503241c0006040982052046c0d810701c42081c80184080386070100181820a00f403d10031002c0c00c10003e0f00c4605040c410500008904a603004003c40320309034190811402c05030300610303c6d05040c050041c040e4010503080342c2501e1481c01800c10805020040200900840f01e0b2040c0c4135a0740e450000d003558007034052140e0300402da07180402c5a0038003040c602803103006d00e1a0141400030f4050212092001c00000340c030654401c2005401e1900e030491104050740c015801b0301020110080340c0e81040049071803141c1207a204000411041040304840202c403804d40c03034003039507072101d038001260380703018100654400403814010b003c0b00c40215401000c10144c050151001c040d0b40d440160b0f15030f6170868050611004a41c0c90b103600c4110b41c075840300d030201c0504240115490044402c0d185400c0500d42c800481c500109000c1300350340003c01d09043d1044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 734071555 1250 734070305 734070317
    0xa0509340905091e0c1b1c0519030b060426010b10020721060e101109090411041e0e0601140609040504060612050703170a090e040501020702120616 65
    0x1200543c003046410004091342200703031001090120070318600700c442d1440c0311001d5140a80b90340c0101e03038540c0c3d001e0389003110a03060f015203444250300400946c0c034aa4034007800c0e40c01500381448154080c0901c60b0100c0e90060f4100000300f00d50306483c480310040308403051840030190010805a085030400d40f111442101c2c107801c0f41c1c100a03400180c500a5400e814a03207003040c1c84a126000d826150400300500341d50030070010035400280001c80518003100460180998011201c44d05928800e402105801c607001c1000100400c0111a100e00e00b104003600010700c13094014401c1d0302100400900b040f003281c6420080010000800a89000d04403064000c81d149141d04002200d610824040c0ba010381c3e245d0000909003d00c0e81e1009000f450075200c03003d00b01c0385074030703003d601c1c0c01030343c00210f070b00c0020340502c0000507001d402502c04091082d200d00703100505210701440c3c07004004108030f90a40d002c200308070041e10f46842c041c40c40f031310000041c60306044c4140044c41c940c030046600c03030800c91 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 734072805 1250 734071555 734071561
    0xb01050915031e0903250b04030201090b0106081603020928181401090f240602120a020604080714010f0e0c011e1101141807060e0a050934090509 64
    0xa002c0b040b00c1107062108010550300303203030b030b0208101e4441c142405407c0c3e0311030b00100401e058041d00103801d02c9100300002c040d16030700c0f4001500c25605c01e89582c1892080c41c415007001500179030003040758903402440040303100321030748901c07815842c00a042d0441c4007100e1410020300040f03800e412120f1809447c03c0c0024901c0340082480c862052090300d5005440742c040010b0100d2a5101c8141c6020096003040c07049885441e40742140344610580300123200300b0a0a0360303058022400da82b8003604607400350159131203035190741d1003036003004205407000f42c00c0003990400110309219944840d003441c2c101041003050305003018100783c000542c003030502c514240d0800c040070341c0c20850b0101c41502d0800034181051141002c6c010031140010700c089011000c2481010700050388110b00f1190a0011101003c2e103c030b030101c4680c0895411f0b03e4011004240900083c42c1594506d41d100006d81910902000d89207601d02d0b00a881d080760071100004540b084031b51681c030ad5070f19070140c0415240d002d0a42 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 734074055 1250 734072805 734072821
    0x1715010314060a0b100f030e010905030306030f28051501121703040209040618061119090f05090a110711011209151a03060a050a1505090a0b01050915031e 68
    0x111420381d0700042101900c00c6c441c1081c004d82c8800c294003c0310000304a000c8c814502a41e99500c05c0d14214401c4c81441001405808000b030044c603120411410510302c078401c03a1a001c4c80340f10800d000c48241c080c085468441c15908002503000381441843c01c3e26000712401d01c020903050040203003020280400070040580c480c00180d079000317030384001c00284851003903c600b001f404030310701d000740250304040e10382100d00c0580b0b0180080041032199107076010707800e40b800c0d41c4000c018482c1000c01085201c0811546c236001152075480300b00c80d0341c08a407080b00b40c01e6407141984070710021260044a002150215640146170701d01000103a0401c0040c64595102c4100107142032400c0c211a988540101c8480e06414084074082c0b1001ba040751005d09060400c3c4028001c225510694036260a00a0408a4801845c0c108444010b000e40e45640c941c000480090036100d920b00b41401404c01401e034041e21448021180200071300040703a142c0c148951450784c15095840000c0303802c100c440c2800090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 734075305 1250 734074055 734074069
    0xb0a050904030e0f0103180f020909011e02070807061e060b0c03090d0c0515041401031a0103021e0a0207030605181509101b020c18011715010314060a0b 67
    0x25010486100324803007011130048014042c1010b0340c411420402880c80200f011009030784070040c0c4200c03070052950741c0341040c0500701c0d16110f2000c070400c03131413180303182000e8400d40c01401518000d0400500e04155526800141c40c41744280744002c00711a8031001d2135000074070521024000d00341d0514640b88400c043d040e500d000345a0654801e030304a07054030003040054100203004202c041d000110010040c445c044007900301d4828244085004c2070034560948c0f00780f2901d000040ba81210040840785000118000e4002c1c12040132112618002030004490f101c0160882804ea9070040c4406400c61030b20105446e0080c00c0c01c910801e0f0303030780d100340d481c0300119148001c0a04101031190643d242280507144c1040041d04500d00c0c0d141c00090380f07180d82002c520000c020500d03000c88014003900e0302070000640d44240f085400600b40801444210840e00003524928aa10101c4601c2001030301c2c034405045007a44201c61a445d140c140c0e5004880508c61280d01c072034414803c0103661045008a014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 734076555 1250 734075305 734075327
    0x720040b01020a120f0504080f010c1101021908040f140607020714030303010e07170c0a090e061f0c05100c02061e0412050c0a0b01090b040204030c0302040209060f0c010b0a05090403 80
    0x180021507031403000031751181041c7c50050070603800b00ca43c401800703120703a4020440d100e0800c7c000b510036103201c0d2560905000312092130f58100c600c6120744000030070448000344040c000301e03003544048400401154803200304c1e80c0d1950503080600010300380800c2c007914103031807584940846040720042e03051650b4080140d0381111203884041c80782d41c1d02d0900440300380040715045286c544020040c00078058290018040c400c500b03032104039015840307041340c080d88403049689560041b5000700c1000a40d0002440e24030480301d5042000c0c45080c1c0303985050500401301300305070450384d48440c01c10310755a040080a800411140d04076034101d0070030720410506040144007501d450070040006480d98401e500f01c0c1c0d1010050b00540d0f030600c2044c030f0241c2c000d170b0007840348240060134584080d002c0d00d0b0034421a030031207520012300c0c0300c290329540c2484041d4000040d4158026000d000c0f585903100504000c0c2040d5400000020348000014108a400e450a4220a0161001504000000f50800c0040705 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 734077805 1250 734076555 734076557
    0x12010c0522030209010602070f0b04320a030303050f0f0103171602090a02030717091009020a1724060f0904050c0402040b1206040905120703050720040b01020a12 71
    0x3600c1d1150001c50300341d40015032000790030916039400004d01540c04076040c01540c3c9a0003000c0c68240da1601054054021801003000182000c0ca081140d9030120740407900080d100880d002c020b94406000851102541e80158003094446007001a103114241406031301c9800c1c00f4080c40c1550460702c5004140b100040300c030800507130000c0c0c1042c0c40c3c44041401c0c10385c41e81c01408a01e00f45803120703411001c1e4006440e0070020501070b000e02100180e05407001072085003900002d00070b0001d4807112a014041c110700c10785e008150604003007481d201c101041541440c0a8004210401545001e40d4004d500c101c20788100c00c0c4103505226440e50b82403240030000c60101d0b00000113498034100705061000a480090740644006400a501c9410b4005010110900c50522081d03954020900c4103880c0c0c081c1004080ea04446010000882c050001d0710f4800d000c1d180050502c00507507108100f103132103040d84114100d40b1208400342407400c0d004a05c039502c42840607084000030b940d5094071104001007610 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 734079055 1250 734077805 734077837
    0x1c0c14030c071a04150e0315040203060a1d0f01090209150f040207031110060f1a041a1309020304020f010e0907110a021c02010e0303120a0f0216050c12010c05 70
    0x803000c0c3c0a16400d4070007802c0e03110079422404800700d201416940440f002240203020705000c80300104c090003d024440d45d00600505029981c400001c4020030b410f4003020000741e41d60740d400012034000c00068102c030301c0004c000182c2c1c043c24010440a20360043c0400c0c0011b00c40c002e8581d151300c1c3c1205294040c030040da0b002da1074030341d24601510604100c0c82160000d105140e120080e010841c0c224404a6401c0c01c0003400894071031441c81d03595600c8034807514140000700030400900b03011100205100c2c40c03140b40942091030481c0c441a40c0c101e164010b2284503004001e100540c41d1488418820030424204130310016800340224288800c002d00c0041407109101080120340424414028959402000950070301c0f0000c40d40e56020074030f284181d001681e112160165810004200d61220000b0059521959200b403007440c040c0140200f02a00c05400b8020300301c51058100741c011040784160b020740105400c110a01800c08800001061281c0c10000c007603080076000300490b211940544555 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 734080305 1250 734079055 734079089
    0x1303050f0c1f05070509091f0f0e092a040e070b070b04122604020d0c17060c160602031506040e0106140a09050d03021c0c14030c07 58
    0x92030a40c0603441061016004000c15244202d040b904403044510484104000540302e141d0110361070300840c0107a0350401c5080001c50202c90181036110b070602d02180b0320f905141d86625211a040400ea8013002200b61400c05120030b00c14188012408072601010200b09841070b80520f05000c00718003003e41c02035a031500d0480c0e2444040c8040d502401d03440d140240d640065280c8076a40d00d9044806641019580c1711f0500c03c03a2103036601022a018451102d0703c1541c100341c3d860f500010142003282e122144040320f900292030304000c0001404200d00c3c01c1d102c6020381036a9420106c00505800010030304003e44428410310401c42d03100749800440041e220740d40e8096080101106400144d40719002007000503400c2d080b82c80c13035410b94103d0355440300c0700c481401e0840024058103c0000201c2c4001c0030522050800b0360b260a0100d0080c0304603880c481c203a0039090b0001910450a000198211840100740002c4103480b00541d43c2010003545855041d2480700c0e2203c660340144030907000c0c01214 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 734081555 1250 734080305 734080327
    0x4170c151b25180b0d0219180207020f18070e030f0f030301061b080f072301050601090602300417100f02071101030509030c0f0c090f130305 62
    0xca14914000406040b074000e480032910414451207225a40c82c0701104900791411052602541c800a00c02516401080144e07030f0030410704201c1c00a19101d0295a5080080c0112000c20316285201c1c6110006030f4900c140d0042c4842566400e09647c0190000844c0c3d010441c42009042d5005400d8039002103c03030f5880c40064242204440746013068840c20881c4051220044003c5040306c0c042c0d11440407010601c42e41812404487c0000b5012100c1884844035540e081e10041140d90301c5091008003241181c0408200b10402403200031541e95150701300b02182d60440001c00241085000400220700081c400c0d1502c042e101c4050a00c42c0705032400020b000300e01e5001d4502902020039010136079000000c0d401d6440100320b6100d61428108400500003400760710894000301d03048101112621032440040d80030300030180185490b8072040002c416007502c20310003180c1100303402c80070b00003410010b8100054280003401a41c404030200043c4400100341f4200b00142c15403600301113454403c800d0f0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 734082805 1250 734081555 734081563
    0x13021c150e252103020304050105030709050405130606060e090a0e0316060b030610180902060910030e060609010f030b060604180e0d02030405060901030e1204170c151b 74
    0x100e400d400002d0700030509030003028000500300341c42507100742c24408888001d814044141e0381c100500135070020001030000794810401194012010300340b1103896507a410200e4110f40c41100c03d0b1f003d090050184c6010040e941c007825004200c1031612301101d0200c0d0340095060307107000d484034040d80d640d1098403440071014029104520040f0206031582c0c6058109072014080318100755200e03018840000340300c000070b41aa83c040e5039105481240c41c0c0c0d82c501843c0c0080030040c1d400d0364001c209100c4c42c401a41c8920000ca5808080d6601250740482e0300c5600340307003050203030060f03204d04185001070058030f80424012040b00d03040441c04001d1b49a0801156851180da003203000d2510400080c0440c3e0f00b12504155810010300d801c40320701201044040342c89004034051194800c00810003001150302c030750024820082c1c048140c5014016903515402c07980d01c2980001584a540301890300403207400c3c01800c000c07503016110800309038465001c034003246c401d191900c0c501c0c0c403003000e2001015030200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 734084055 1250 734082805 734082823
    0x1709011b05040602070b030f04080313051c181a070305210f0901050408090d0c05042d020301120f050a0b0106110106170604120c0b13021c150e 63
    0x340e46a00904996000203001e0b60140c054200540714414000402101520032280304102c0110440c0325500d032a5240c030825031010780b410f5903507010600d001012500502070350781c019080111000f000301d403038203002c1e00701600509105907103060b50310104081070351860280039901030710380c04542d110500d14003a203550250f01c113145aa0400c40c1951028410100c0d041e6014001d503804041d0f1030b603a400e61603070a8403412031703008051650500c1050402d08100201d40c000e144a019407503680340c0c884020034100c525080c4c070309544000c21a5240203e40d141d600900240900d80400d51940d0b04003844da0b002e1141801000b016030200c00501810b00c00140f1030075000036808080d034501c0c1e50b542d103401445001d080032044c03401c2d480c2c80383c001842082c00f190031502c9060b41018040c10340d510307202d42d42030381c500d00c80c0071061000d0760b9102e1001564035031740305114592140355107006d6485401407101d00401c4841c4511004115071512011076504900b00c04080c6151130049100441015100d0601001e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 734085305 1250 734084055 734084081
    0x71701030f260d060e130f03030c1101150501180605030f040c0509040b150a030c12030c0b070203030109150303021b0a0801020c0c030105070e010801030807031e030e0705090601170901 81
    0x10410050340c01884c0c0102d000c44240c500c5644131501ca8001401024000440092000352078130f5000303001070b02a420505288203603013042c00074024100e071480c0c25680c4031000280408902a0184130303a43c2c100c03882c0810609030700752907101d5908086002d0f00602c0b01030058101421940006420840803c1a04004d8a0090221402814140b03003440c0c00c0e10095440b03980c0c0207803000b41d074103907070603d0001340049941100c110b41c5079134607041100000e6803040ca030070ba081149840710b0b50049100d515120b406030005034025503aa602d4031060400300e64021910303007003070b50b461a000c0001c203600195048040c0c200c4032407000801d59110008940b2185640b2500aa50011503603c0700220041070004100009800900c000d5a17108012034074514a40034240c00310380c81d40c0051020034000c10180580b131b4400d05040780c007020034840300010030282e0428200000d843e9071785911108400e22001c0024201950800342c41e052980c0007030a544245001554110b01e20000914100c0003500300d60488000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 734086555 1250 734085305 734085307
    0x1603110402090d0b0a14100302040b040e01091406090304060e010509010e10020d110304050d0b070c0204060e040213111b07090c0c12021b1011070e071701030f26 71
    0x40c03031501c402d44200440701d280304030703281601b205107062580d42d000f4420003a5000503d0711720300759800c02000b03007160090f4a0304a03944400e103070742c22402407003000d401c1401a04107880c8658400c0c05a49410307002400f0007020341042c070041048a0704441d800059400034280740f82c0b603401c9000100c038100c2039907041c02c3d0300c403114207441007049802150491540c0100d41c0c805215207015400303140d0341d124500c141b540141400d00e105011070303034103c0380c03d0300005203251042d0b5160312070300064241c41e1940c00c60a010070600e4244400c5203003200c6111100e180400d0140940c1540d007070545a40c0c00b4440c24400065101184411401800d0140f140500010281000340703921910008244444000044481130300c0c00c40324880c2c440c00000c010011813414080425000c22000c284920304110310b0889040c408181411840301070b09024050182588030f90080c60342c41c02803001401c00d0690b5521102411841d00140081180d41c0c4265000325000381f5568118458420342010400028000319103010f0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 734087805 1250 734086555 734086579
    0xb0901091d12031603020717130801060803040e15030a1127010f061110020d020705010507030c08072a05030909041401140c03060d14010c0504090608160311040209 72
    0x10210065801803801c0b80c1c29a081c5055250185c080780304a10015026541c5049080401700803400200012607213001c04041003650b03000010f0035501d1b543c104a5031f90304045800d0201c1b2960f0030460360301c0042c54008249402c0d801c40442d803602c10b40c00e4050014000b44c100d8038159191150201c0e031501e8080d0710501740c3c2c501c0300903d00310080203001e40e8002d0300d008200002c0c802c1c821001807070807075440e4010b8100e8200c01d4210600a5000e21281c6841c103800344803803c0854000e100fa284540c0b1561004680303c00d408000070b2124100809100c14816141806041c204c04020101544501c12200200da20101d003085491401491611540032407440100000c010108000c0b216401c6418000d1000c03020180034014640412604200c04800520000c1c4c01464500300034203e40c2d005886440c8030100b050b5801c9d083d50f803006d0502c004501300003070030003041550f803088030024070b03445001c2d02920340c0040d4481c07403100d0707988009411000c1c1751900e10300b2980c0316411a010321000400751070342c00c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 734089055 1250 734087805 734087833
    0xa2306061b1c0201090503031f0e040305070b0a06060f0516060501031a2401030c2c030606040203010503060c07210305160206071b06110c0102070203100b0901091d 72
    0x20340461102c801110903029076100d650f005005141685520401031800c540d54074019464548015500110340d0302d001d8800540388103449903030b81c007450180c1c0e1020f039154201d00b0000d00750b03800602840440e6103040d0301048082c1d17025220344280060f81c904030703655802e004907160450004040141c940345c940400001013014408520410201c0352a414603c0c2e83c92003054141d5241040c03283c02c400d00c5005081c202984a40e012260401c55400d00800802d81551541d00840c0c60603503039094500b01b14002c0201d46020000e8540c072800480e82545150b0400340070980f0740c84c018151000124001c01c03030360b040084030b0b42500b05030854914441040c0464410040c007500c0d043d039a41000d500240c91180000f0300c0400c180340325440d079407904110701401a41429000220410565445a55161480d4001c0154004265030a040c00c00540c4449460040600b0048461000c6081500c0c04460122036240e400301c090464540e12000906807005040891001400c0c10030001c203070240889008241c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 734090305 1250 734089055 734089063
    0x40b18010b0a020d0e090c03060d050601080c0f030c0a030204021608070b07080a0902010212030a020f0c0c0f0102060103261603030606090b0a0c0b0903071505010602060a2306061b 79
    0x381075a9802c840040d000c29134161a1081c070407901d9900805000001034030280314074010341e080382c8090080c14100c6007680f201414568280c011035400d400c4a2155805032070001c50311071540360110040c20034543c0010000301c1d0300895100013070159402260100d5121001501c42d040140c109240c030366515514501900800c002b01d6824010440000220342d0150541c03055104096040e00200380d5003071061a50030781c640004201c00c3c0c40f103408014640d2040d00c882c01400da4048071900800541b80c04d402007000c540102429181103500c18001000850150400702c0b05010641008a800c0100b2031428890b91164011250744000302d0f543d0704003007680c1544044215a03207603507076060894640c001c481081c860300b4000301c0050900740a00f004901c16654294200c880a0b0450b8500716096468410610608400c42c030b542c0c0d41e44004000700368041c40025480303200040d040014032820400e030107d201c0210a58000080c1410004007162030722402c4030316010807a10501e6002c500d5003d22652 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 734091555 1250 734090305 734090317
    0xe0403030e071811070305270406080606030d05030f0106120b060403230304180203271b0f1c02190801150b03100501081306020a08011e14040b18010b 66
    0x1106144c0510400350352482400d5619240d80355803079901d00442c48103074045003442c0321406440d500c86001003c220fa5103a101da0001401e0f12030141c1a00e1500c44201418100a503030441d0600404104104145502c2c0c000141500d03a40d08081c2e4504022044110080c21100001a0090300c005401310921881c0c11000c85141004142d41d80401189035003d51680141d02c1168007400741e111007400754518640180d903204180a5454003142d0803100710710b0520303500183c011050380040c0310603030b140440d58804d10481070b4296850740d80300000c0c501050a0382c840301c2c4e0980c01d81320020350301c404556070001010b00b0165010a01a003031605c0d0060076008200c1820b000c0007550003008006100d4105605032845190f11440c00d92846203802c0064030341c210018100741c0c0d400008600b0070006a090f1000e0002d1204695a003d400d604028100310741c000c80b12524540650060740400103079962100c031035a011804d5030003090001c801c00100702070084525100840010200c00414024100000f402d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 734092805 1250 734091555 734091599
    0x60c030b1306061b02030a0506010e19090305071502190f1b112103030405010207030e09060d060b060403020406181d0303040f0f05010e1c050406090e0403030e07 71
    0x2442490504501241c100d8450b0601192014003805a40d503413101c1d48440c2580094140e80c5101c0d5181e8902d0308114007604240813101182c0c0900034180d031070904440d100c0c000301504000800b881e0300c010340b0b0740c010204000c03c03000d00c080c0c14010481094040c0d81d0740e8a07080740310565442c03206502911031078000c01d05500040340d040b42c80410596084060322055000101c11029550003014824400d01068201306441550f03014009043d00801c011403189000e00700050300d480303007403030b0041c459142c070031000c0d00c9140c00c081031003034903510b80350302e03c0311241d20802c0000d4441d052130101e05240078641c0040d6205150500c00150b401d14281d044180c040c81c0380c0f0421004444210540e404034030b010102c02c06500600010340011481c0c075000d08498021070401c680405030b41d94090a44203008041300d46500140d1042c2c0c00c81c2c4108109030300382805800c05030304045c28010003c06800c854030807075076400424400309080c11300940c081100f0080386029200c2403500d40d20005001300b442c00c00c41e1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 734094055 1250 734092805 734092819
    0x21060414012004210f1a0601092d08030705150105030a120f143603340f0f060203040e0112170a090602060f06010e13020403060c030b 59
    0x10b41036048412164444110400740c03070030b09040203860440320a20064040039030f92100f8440300401d0310101950381c50b0303104043e882100c0040349a50208040081c0c80325041c4009010b0501c989800c0c0d04400d058591040c4083c2070880c0c1400030b4014814090744040e0040c00001210400d1190102e8a52400c2c20800070002c600c1e41d841081c1035035805030400107091240002103e0f101c3e1441403105410091640c6010842c4000383d044440f0160702401c884101c140d46640d44906520090a52002d5081c518a1a60011000d040400d880c0d2803686215001c1510030780e004000b1625a00e240c4400c45c44002c0721050050b201d1042d10b1502c0068007071402c5d4111703900c03030014080307100000301c03401e440403120301c0c5420364600748500110155060044400e5a1409038a6a400e81903201400700c43c0a256550f12040c3c0c685200a030420030040c0003180e0000194041005990700141c2e00f50a01c0340999103d103640d0400090440203018981006003d2400d00f0300c26414598160414882c03144122188 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 734095305 1250 734094055 734094071
    0x804241b090e1302060703020c0603240406052b1709120c03032b1b031a061602061c050105090115020d050a02030f030f180a0507052106041401 63
    0x80c0c90b55001c4034030907229483d4880280050800c0d00142c24000c1c07003401280c0c88016814001000e40e00201e882c0d078051405161150aa60b03203049420724003c000b070700c04009050914002c02c9c40d00780d0508200c900c3c5400d10911540f03030451140600300c420380044180c41603a40c9000c10348116481401c020748503400440040e04c12020104000c803100c440140210303c0c00c54085c034404046841080d501012000ca42d550b501c0340030082c0a8110080d40030b010301884181901c0000c0c1c01c5030054440c000b0100c88189034533030180c480750115024501c24002142e480b41303d51002801e03520400e141010212120040700500e107455070480c0c0d040c3c920450703103408a84c3e01c551400c0d040b11a181082070040e84007000344180b01c0e004030000d200ea00034920549140c25031600020016a000b502d1030007606a417881082072a11350b0003003501400c000003020741400d1180d91920340d9510042c0c0a600d104040c0c03092009124401102d500c200f001111b01a00e942e45007900f8507034043d103032140c1641855401c03c004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 734096555 1250 734095305 734095319
    0xe090606030715082809140706020a02151c050103030201050708040308070804020a05060a020708101112061804060c0f030c1d0402040e0c0c010f0c0804241b09 70
    0x102c0d105403100005034618501852a044902d4040a0100d07240918421a400701d11200703803c031031014081d00000031400014a00d406030280400754003c000c5904130030014401d0a40c0800c05010b10742e0100c5002d000d24200c50035502c0c241c881e02903294111030b0b0303440d031504494406e80c0081c0e0403640a0b40003089103a0f46c6100645021004413002000a060358002800180c015006146c006002510401c440d91703c40e0b021511917441031051001503808601c04119002081080310441d402034903040c0004012050011414050100e442518901501c002001030f2980000c2c246a08142281d1150a007000e0034001c0c010944034840b64000780703030703001c6811303a0030300a0041c492201ca0583e81e48801d030449529280c5120b03140e42d1000e42c0940c00f0840003e0050003a0700ca24028070a02a41c0303503039104a421540e084480c81012816401d041c09480030310a500024065407258100c0485040d80c81d0740c500904011602c2580f807da4603207400b030009607041c5020150b2807000115210355030b02907205c4103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 734097805 1250 734096555 734096563
    0x1150f05090c040e1803030a0e010510050a060f05090d06090b180d0c08090d03020d090e0c09010807180b030106090e04050d0f05190e09073b0a0e09060603 68
    0x1880078010340b08200801084519145482e400f04041515410100307002d44518216801aa2500c210300c0c1c0780c0c0c0c8a803036018401e2041e1604001022554a9894130309000b00d820701c000c1d03224190600c05504401c502d0980220300310341450030014031415290b85a481c2440061858500075035140241d203001030451111444440d8500310700c44003d0803c41640103007180c1381200d440080b581c0d800240304015460301c03212440d8003060f2280d0081c3c0701042403410003c1c00d1035a141d210710f21026544041c0706e04507000e07000300c0e00400020310b00000c25685100c000d46885506c0c0c070189100d904165800205103c007000954182d0340959108951565104400006288281c8019210382c110581402c0d40b2405544000001140f0342003c4c0c0c2050180801008a4448880c404011518420701a04a0302c2d0040c965036100300f903410841c4064122a90b41c198024010b46008020b49800d4101c1c0441c0c25811141d8040440041543c2403480d102c58404100003000d9441821070f102d000046460707403070042 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 734099055 1250 734097805 734097811
    0x603021f141c110a120b0102030f0706020903120a1e111c0801060c02150a0309020a06022d060f1009021b0c0a03080a0e0d020904080a09090b0d03180801150f0509 71
    0x245d03034800c554041d550b522006204100c02c4606611040040c07600d0247d41502030505140910801603e0340481001e050a0220850350000115002c124000101d5041005141c120f03030320b5168902010426001681c00340013030808114517105002d4103012542c080c18800c00b919509544200d887d076a42d800580344080c03400f20007035200d034510024031180b01c50384c000381c52a441e041c41c02041182c001d40200346001c540340c1012005030003020317402c01080f248a6184070100300405041c640c1c12082c070b00503512907a010f05201d103034800100c00b1031500c4111014810242850420455850442c620b040d00390340519000c21501d405070000343c0c0402d241000158003101c0d00175007a81c2c0b8002c48407004941003800011161b5220a41082c080050780361020350910540c45211015507132080f85c14045c042c02d06580c0000300d080e081c03040100c85a1a9007580722281d590500305000f0340040d0b40c0e4012074824aa4110090075840e18100101103002821824200c8441d00c40a074901621401401a00f034412 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 734100305 1250 734099055 734099057
    0x10b100c06050a110f0d06140d0605090f0d0e1201020a17091c08061801030c12081b0304031b08032b15180603021f141c110a 55
    0x4034845401207002504031952281540c0e60003e104e0344008207940c403940154654a00152021a0f0380d04540080c0c03080d000a080e01d1040d65058800400011729a170b41d0310031000b814151641d02003842500200704403400a480a81070311142c03a80000c00822811000e8160351040380b552800f4008000c040c42207a04170803aa50f903803920300f46000809006080b01a00314a580e12801148264442485c0c000003c0d0700420342c1c41c2c00e103d0500500304071690341d1054010b50085041c0740108009064150750b40c007124004248801104d18504001c203150050140c555a80300103a00d18244c214030200041c4181e074403460f00703848249100390030320030010240e0103a200c180e4020060100865401c90016501404104214860f440300c07030201d00a46803140c4a2120f1421165803c5c00300c43e83c1c460760441102c4c1c29410070072981d882c50300010501002c91440f942100c4590807507481b01441405c0007011f0807101040c09039035400f804c0201c607200c10b0b100c28090104e490289200c0d00011108101d55021080f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 734101555 1250 734100305 734100317
    0x3030103020d020112061e080c01020a02130b0904050102031b0328020d150503010e19060902040212090d0806120a032d0302190926030d021605010b10 66
    0xd660a2180d801c81081040c1c1c14000d08a03140d400d00c014502901c80a841034071282406a0402090343c40a400c0c00d0708040c4003038001d4005282d107039900140b038120a9804451b480d80d189801a2803400514507a1202d41e00130010500708030038010150000c5009000a441c0d80001003110071445c2654001a10611008018158480c4400c090494100d4000010010051801e041001130900321074502054800c01da0261104010510b000c0c070841c0d40300c1c05654003824641400203000b503d040a54440100200da03152038240954603140c0c19030703000c091080300002c5130b401e1041c0702030354410801e15240c00103490100050024107100740100000c4484100802980d44680d9051b243e040242d0400c3c1c1101001882c000c5500e0748414010380303040780e60740b4010381d5007844003e0401c1012040c0c405100b4400705200810283c03104690400b00c1d0765049140d840d01d0503200c8440e5007548076100380c8542e00c50011460140206001084001140c4600e00070026042c09105106c1302d000c880901c4400301d80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 734102805 1250 734101555 734101559
    0xa050906040602070611120609011502100f0b0a0305101104030b01050d111e0909010605030624030a03350703150305071509061b150f0e010f180203030301 68
    0x30b6000744c01100c0c802e500201e205180107000b6074190308001c808810790590141400502d080030001140985407584c0110383c1c0b40028603000c0c2d9a8010145074003116503684505410901255202451113080145508101d80e40c9040170755a5901c280c02440c1c04501c2c1ca111482d113806450104c504403503201080c5c004680c80d020402469110740c03034041e103520a96a0b80000c1c00d50360b0031501c000210810b90806803401e102c0c0b0600000f407000810328442a894008140003c0d81c1c0000d500d50300000801000c0c65142a03441408070741c285801030560107114a0301c158040581042a1f54071089504003240c41403c0500030100803524a0001007900019410220394018440d40080420702e28039400f0554107956588c80303502c1d00200d0f80c804000480b01c00a60702c0c0441d8020b03013000081c0481e01d40072840c49180540b00000c041801e00081401c0b110110f01c0485040d1070300681402608a8010440f0103046888640a494107070031101c201850301000860126009070f43e6010540c0140003103046138 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 734104055 1250 734102805 734102813
    0x3090307060e010e0406090c1103280c1506030204180b06041104170d030509122a1c0807051806070c120609060606110d0e0a080a030e03060a05090604 66
    0x565603a9498100442c04260748030b6170312240241001170401c1d0707000249034680c622005215504a0500031855013040190280b035422140181e181c2c014610b0002102c02401c51080d2400c4006680041c2141003024031142c00c0210399201c101240c0c001c1d0303010322030030072011018940000182d0b80100218141e1000c140c0c5420a90b01880d58190b8508006160580340c10340d00e8501460054021020380c070400e001c0c800d041d0b043c0107080e0030403442c074014075504503205401c160340d02a0110b052444444219541445902c581418000b080b084060300c00c40c6107408600c0c0600c06903d00e03100042094030000c02c004902c1007080f03541c00c2640680308003c00c0e0440382041895804408151440c511444012030341d48100c1201d01081c1d0321841002803500c3c42032400e1015522143c1c00541401121107500062032404038001d0307100003603443c0074110b800c03046000a42c6d54010750808402849043d40010405800c10001c3d245030b8070803070131102a82e8070b00c99044141c40d01111031800c5504100c011174005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 734105305 1250 734104055 734104067
    0x40f02210f0c071a071103070501090c1a04060309020303190c0507060801081905031911010b0105070b150a0e0109061e0b3406060501030b030a08221508180309030706 73
    0x205c1103e1604102880e04004868a190403028040d0b8803a5542d07250030080102a00d48880142103003842d154149011190404490149102e10024541c170350f0201001c40d9000c0c806c8817910804a00100501280103200400701c0300801c80c2101c01d4821810082072240c003c09406040710105001003200200f000301030780300c0c00031a42d000c0310700c1d2005000c0f85c0d120550718000340c0590980ca684030f00c481c06900701910700390742e0040405814048100000000706480d101c06a40c0540c0d021410b9180690400205007041281e81c04011100038540c000b044402241d00214101c40c0c0040c0d46201039000c80c50a08801825803141881050040007200f2503140411000c1500483e001d03602d1704030000300010003507043d401403c01c81c4d643d50b54800603c85580c162040409866040e8000c0416540590300c100c1c1502c513201028101c00c3d100c914080e4404c0c00000008003504143e84880c01c543d0140c00003420040056820913409168050003e41c10b010020940b002580010300408a180c5803440c140c600d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 734106555 1250 734105305 734105311
    0x6150306061009180c0f090317033706051930081e0304020d0209060f031c0207060212071104180c090b04020f0306040f02210f0c071a 59
    0x140080340100241600b0312203025040131140b03640c040303414244517034002d040e030300319800c00c1c424812561000e1003c0b1302e003860141051079038605201d642e9110319200b901848170ba01c6080080e2105d050101007810003000b180188001d4211050108030b48440400c000c5030039411055114105d640b108006003444503207488143c0e40c0c2c00920380305004c28140046400040f080c810745042d01c002455480d030b071031007d4a00c0d207003e151010060860400d540090a281081040a4401c4650001040540c1d13140743c288107a100f002001c07203549540e418289503641c1d103d411400054000d904000407418004030346500c3c0d01c501408500e10784a142c0c3c1d0f030321744003181c91203540e50055500c24081d600401c41c1100c0501d40c502850860390b10610b00501201079450000c05940107600500c80c82c482d10350580181da800a27400c46c0d010554503040c09084e0020300072070040404402e030039034500002c0034040e800c881c09410804080d06040e034542803640b103070f4420107c1c000c140380709650144200041b003c0c02e09030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 734107805 1250 734106555 734106557
    0x3010e0a021c200a0b040501020a060b03010204091a0a0b040303021c030b15310909060b041401080705041125050d030e0118080f1309091103061503060610 68
    0x31000d0441c0c80d4500c00414115981d6000c030240c0601014a01d000c0c003113840248807040d07416250509210000f91034450080c0000d2015444003103210165900390190380181041c1c40301001a0301c0b420009104000803031455500402d050600414050b0782ca83c00ca4081d03075099001482c1610444124103001100040c810080507900d9003c4902a0341307094104601c80307280746070151540e503140041a45200e460b19000170340c00a0303012000380c210101d801c0e00d080740d00310800010040a103003408000380030310ba0811a030003450403084210001701d800790b003030690b50b11700704540c41291940300344400c845440c130050b181c282040c0311000e80b10060300e02100c11031074141c20340008403207503954440c80c182c0255880070200380c80b80c91320303040ca8200f441610240810a10074151040a03902c6041d028414040445046800001e050764510008141000100b488400401041180341031507603040c159001d40d00e2081c080c03100420703620381c50348e03e080d5030246005001d40700c161a002c0801154086002c5904 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 734109055 1250 734107805 734107849
    0x40b27130519050c22020703090b040803040e070207060801170312071d090c0d0b0d1401051b39030c011d061605030604021909050f03010e0a02 63
    0x100010780c00b07108001a00300c0301d95100c41c1078549850030504100014041c2030140301d1076090000144801d4400051004118400680c0c0c1c80707040c1004ca44020039038000c3c16001c1c0340013038001440d040c000010800c0700d18210203c003003602c0b410300c00ca844030703c00e103d034500040d2810f0040c4207103e480040b10005d103000904981c5071141314940d050700040c0468020010601d0307040d420a807125441d449032569142212003000c50300e40540941d02c035005a02d440015160384ad140f0003620380710890380c402c01e503070080800d6034040221003403036000c1c00040300c04c048400100e034219980488101d0541c1d203000e1342142d039101c05112031b20081c10004000361080c10341f00505540004281d40900080c8001858940003080b00751420b2840c400030440f4203039414655100204200c0d40c2100c0741d00022005005140c21075803070b150003001401034005c1d61070074400c203814449540c3e42241c01c80e03100021503170152011003034070f40d84034109422a6848402111150042a00c6800500d05070a0510a104d48484070b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 734110305 1250 734109055 734109091
    0x9060e0f0609040914011802011205071b051b1c0303050405070906120203070b03090618101a0102010e01060605041818030203030a050606090d150608100902040b27 72
    0xc040d16131400b410b0380c1e001140070b00685641800e00400150f03040700e040c46681d0504075400204000c0e80100e05003ca00c1c3e071440405c10305d5100703038500080b0303c0021030054154291404c180d5100c0382e45042c4503178003c4030142c5100d040d0501a54011a43d60402c0d140942d103c01c42d2001d0703000d85070041c001c8545008006011804880ca44641c90192161807211b40102d105403042c10300c0c008840e04088c04543d018400c008107240000780403507005800c241038440402031200d01380e1500c041802c4400d032080c100f0b5500c040103880360910200c658001d82c002d1100710b68801d01c030f134200e6032540200400150300304018040b03039454000f03440c95609040300001d020702c59014446141e038002d540c214010703000007060012081e418010b45400403001c942e91031810700b005002844440c0210b000500f441464503180c15020003a60118005009003404e840f0b049007a0030265005040c0c95004a00c9285004961040390a10700c0c070440d9030100b0a0140c0f92198501c3d071640710200c80040000642c1201d103891 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 734111555 1250 734110305 734110309
    0x16170301120201090e06090c0c0109050d080601030b12070b0a090b07141209240c0a05060106090b031b071704080312060d050703060b0112060f03021009060e0f0609 72
    0x1140240030180d4014503100341ca20004010000c0c1c2d41c001d4030307200d604000780181503660019560f0058420740e1902c3e5110f1303403001320902410504401500500500c2c400f03074402c5800c10203051285d00e00742c0e010072980d45848100035154501210b0f850b0281c1c01910b05202c031030b02c41c60007820003c0349030030440361007036036000301e414181e0002a08480300b01a2001d107007055074040010700c0301c07001d114045030309020485000c500b2401d000403c40d94a040340d01210070714400d951044610301d4550034196100c40c4e03010306003d030b0f4400c0c081c818030700012101840041d00001c020103490168004003000b20740200500f1070303075500d6000194182d0700400d14402e403440d007411010080c0300801c00a4051a2908129154140800001029180240316411032100043d038081010020340398004000a642d400804c0121140704070340b1803070048c00380b814601180c0b44111403403c1084920031581d0f0300700b1440310503085424800e070703200d00b13030102c1c940300e000c03840b645040f810000307540c200505840c4c208811400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 734112805 1250 734111555 734111557
    0x10c08060621040f05010b01020d020319050906220501030b011d010504080f0718020a020c040f020c010c0809010507020a050a0b09030d0f0e0106080f1203060a0503060c0d201617 78
    0x3401c844101c40c14800c1403c00200707004e1094050320900142184003108000650ce038400c0c600d0824814820a81d00c890550088055404c0984064078058032801020982c84000306c407548107968012503600000b4071503200c0e00038440d020206a441c4d003007544030701181c034688598010f86541032000500000c0b8500310304101c41768000300910014983d641c9030015181d60b43d61004000100e00b40100880c4600c15000148844030302c0303054a00041085034124040000c0c0905007042c00c0300d50030a081d210039036610030100d5006801c100001c00884c1c89034113060765184d0050100070990307007001e006d84010030107144615078840d10081c00e0340d1a10282c044004115520003d903261403603900c401c0c900100500348115000303415160b00074200194a44000e595a614040441c41102000800140242c5661022100070324000d4102d030103604040d40030304902d400901c24250460718000c45c1142d40705d80304100d4104011901c1400740303054500c19200790105030702c1d582038a0101c2d403201c0500100031000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 734114055 1250 734112805 734112811
    0x9162601050c121312050d06150c0215072310060617240d05011d15150901030f2a06030f0516050705100c080a0e010c08060621 56
    0x69802c2c1d5071461490701c9880c100d9409043d1814803035180704000000748985050319480300590130720035281d01159402102030701190f0000260320030b030010300313a09298001c1da20181c01407003280c407070f11100d61307241151205004400c80600400e07030022004900c507008070b91f032008070070300c0000390ba40c51280d904e041016135000303601482c0000c1280013820321941c0b51440440d006203203050100a485000c0c0760303062000e0340c4101254403540c01b200d22070080000941c02000c002d68007401829540240325181d64490740e00301666492a4074410000d1504500e0740440141500000c0206e88583d0035600c40c000141110402203640140d601c82007544195040c500280c99214510081c260f1418010001d0940c0c0f880e400603a11503003042c00b80f00c036820010903081887c810f207103031154032902113080035071400c4442403140c0000c81c50149450810b42d80003da292142d05812020700107a004102864220381d1b5001c0360300c000601c13030030200e0040c4c500f0b00e000300400d5041c441780c3c0d22262500c0030550789250742a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 734115305 1250 734114055 734114071
    0x160201091211040501081f0b0d0209011e12170306010903081c0b03030a1b0303110c101404020934020c19150822080903060916260105 59
    0x1c40c2580a0603e000d0054a015040c894040c183e100100515003481310300d541c28150707015440700c40c51101501c4c3c0019600450f078004144c041d441d42d550300401d1a5415000300c00800c0c080f01c2c0e5002c210002800880d10400f507001403a5600c010303902d4203440030358101920b202c0c1088000d030700000211b0780071406403a0601c0501c000b44882a0029049400c44400d0005c09000360014481744222030307040410081200c04115100b01c0400d0703d442d04600601224a800c1e400a00209003e100c45a000401541d10b40150008101e600580c04040c2034525007120001c0d1300440e41d0b0300103440c070b0b2036003583c01e90307a1290f846011100c850380c0c0014050072100c0d610190b00580c0504e1713101c7c0b45460302a0300c0c8044d40c0c94a40f81207a08a0401d5100a06a0078400381c20080c4a095000700c0c071381c2805000c509500e880041c3c031076103542c00705140401c1194800c202d418401e11490000c503110020100da000000d1400000c414103182c501030501d001d089242010b00e1003403e504c990350031a0300003030080602c61454 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 734116555 1250 734115305 734115323
    0x40803010e07120c05031e0603031206040e06070804110109180f0f06061d060a0806010507141b10030510090f0b0402030a020301030507060306031505060d050a03050309010e121602010912 82
    0x303c41ca90649440b0480e01c1f07141582c00000620251b070701c0101c11900303a00c4001094440c11ba54005c041406004070010b042864401c0104111401d40e200e01030074080c40c8a01186840d480180d801114106c6030740c004c0130100c040d003460780c40c45d0411702d41c010401c001c4410303400b2a0240d80d08a0f003104031a82c03030b4090004202c44480009001000c0440c82a0300e5101f2140c582c10000e0318000100408401003135107041c0400046d410382440f00c40031070516118029411600c050620548450620001c5910715009003010100103041a01a00900d80b081081c01d803001c08445c038040403080030705040d035040a041039548154070745540356030005610640503500c01603600c0d45185030076882e0030301070360101d000c051504e002800003e0340d0301c600b458260b10030a0041160340754140090212116498028030380d00c00d880e000760825402501551150035410002c010312007c41d98920f849407142146a2176980b030401c101400305412a881b02030b418010f152000d42c0d903072120500140c0c00415007081d00c51032a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 734117805 1250 734116555 734116561
    0x100813021305150a120f021807050405010e060a300509010c140f0d2003070309050607020c0901090e0102040e07020a0605070903031e020c04020a03020c0106080303040803010e07120c0503 82
    0x800508031200071105613a00009580340044400e0700440404000340080913174803041c001c0d9920040400264844804140785606110001920a5000384a0103010650391041000c1c5450803c06650300d07441691240703a1000051850300202c90320f0900382c200e03008500078100102c420340d44140352180b800d0b4030001407414103404c0c000d8000c801c200801001d1003404c00c00c00b1f110003240f10580d561000c060802181030f40b0f20503003050551b10041d50550008030040708000300103031725400c0108400d0248050f0740d01925400b0003240c9401d111407000b0f40024042004000300d15150380152641d0840ca400103050944038020f0b0100032000b51000700041c3d0001c00d15006205941c8180d5030452040e040404010749990742c058242040000130340000314023041081c00d034074000e10000b040078070020700455840000d214068002c0d0041e1840700480d6207404008038012600001b00c900540d00700140904580c6030145507040000002d2840f0104440100158a801d40500a05030302110f980c0710141c03685 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 734119055 1250 734117805 734117821
    0x5221b170a060305030d0b010c0b090312010503010e030a0c140a03120c0216031b0f060908011407020c090928141c050d021c0507170402100813021305 66
    0x40001c0d0100420078500b03007041000030000030440c0c0300c04070256804100640d201c401610401c0d13038624060245c0c0544030403c142004040003c0010b0210f070055214203980760410300d803c07100c402d490041194410409009018081d0072400c803080c1c42070b01007200052042c411703603052040d59141140454028241c17a01c4407001e03402010711200d07182c80208620a42c2901010038541184401384c004425030360843c4500702851708a0000c2e22036074100100755943d95000920364015480303075407015447c0070340c0000300300d0300901c5940c001d4041d40c0c0103100f124500c00c20019010405001d03001c8502c50c441840ca44580d240f02c041c000011800c0b0681482a402c0c10310500080340ca80401c900d68011a0182224000d50000f0760090001450500d46452110800400900c01c030b0101c015002100022403600c0010f41d00694407946207681c4440010024944080c0e0b01380064070000d5204400c9440101c1c014410015254000b80c480c69003000ca08a40d004980c90300c210200d5201520b0311001000410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 734120305 1250 734119055 734119097
    0xa061815032a08010b0c100524060702090103110a0305010908031e072f0303091006120b040b061302070515090307051e010207050d03021207080105221b 67
    0x2500341042885076140e400b60040c20240c0c140101c403543e280100f40508000400c0240c0d50070307030b800c1030004c01050a00300030044c85480000d200300e0030441110b503d240b042c200a01900c81c02d5034080c000800603400c4d65140003190a20303511a40e000081c2440c0000421009d00901d03090600a5040302c2d40c0703050045440c913280d04900007a4407009a00741c00e00c190f46500030b00380c82d01c0d4180c0b81242c80c0582c0b41000007014549104d0b030140964032000c000d115003140003003001d01030202c40c82400c00c1040c0d0380304601c01c003c00c0c10740000381840d00e6410014020540e52555594441c000800038075083e410455803d040360007804060354a60321080c00400401c03100066950000680d000450a00400f580da030765840103000e802845840700e150014400388001d406031401c455105099030001504000000c3c0207401c00e000200014500801003103820b8000d04c40c0a068400280641d600d408004200b24409110100a1001150b90342400f0f04254002200094510880d95a0f0242c550f0002c901011b2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 734121555 1250 734120305 734120351
    0x22119050a090e13140f070f05040c021603060c020a0c061110020309030711040b180702060a290d06020c0102070201090812031f0305010903050d0c09050a06181503 72
    0x1418840f90502c9605481c1d0304107038220a9221039140484554a0861824100c8a850078501d6104401e000b00305241c45050540a6440580781080413900100f012a81c4c0c501e01034a420282100440034000700701c032078000c141140820b00485d068803020f0707a03818420a00355400000000c01c403007480c0010860a00131514610030220007541141003000a5075124403641000030400c3ca244040d2043c03e44a5070002c4072042d400070f0a50b580040c440b020f90000d01011141c0310010302506000580d0102c4500ca4107040010449240d088040b51140e0648000d00010035140d01c00304c41100d890000301c2d5030004040c0c0071071440c0050f0b2182c4c154400585041c4003500825200e03040b50440c80400e080e1038054991001403516540d5400046804000c01911142c00c060525420240030703409043e0010f00521881e101c60f9010400511114400c840802a9005107544085040010881c3d10301c40d07084206001c075142c500b03c2c071070b9a440800140100c0e038202c0000109071208410000b0700705070605024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 734122805 1250 734121555 734121569
    0x1e141204062607110c09040b060109080f0c060a0314070203190504051f140c0705090903070209070302091914030105010609140103050c120709081c022119050a09 71
    0x60080089600c0a00200000e0005003000b2400d914082185010009248101d80c0540082c005052238213003000311060840300c541c046107011200240e14400000c42c418a894210007806a04000e041044800e030301654481d001c1540741d070110700301c61005c00d81441c09020190000d5548a000706c1080e0604003c03030104800707020051004100390749030701500d8941d040403141a601d441708840c00644a1920311040074410781400b28547e0681100018240e058407411200840280c1c1c032404c00380d175a88101d20000390000d100b6004102c5660098015049402008101c480410f07070002c1c1030052100aa804002c1c142c010640d8424942401c0c41210f015000515003c0380040c02d0000500c0300c0a8000040350400d6034400c001101c01c030a41007601d020490480c003407105410100d400400c6034090740544c554034014900542c10303e0030340b1a003c0300d100015401800d8050f000c045a6610405940c1481c031228104200b8001049205070b244040c0c2d1440d51030390b80c0c488002d410001e0010a044d0032100f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 734124055 1250 734122805 734122847
    0x305150108060106140405060d02070c0b0913020f09010c050705030d0201090605010e010f0e0601170114030f010b03070515090402120109061d22061b1206031e14120406 74
    0x340c505d5030403001c07035040c1d44c0e003a02c400740e546500307011001c002e00c1106009032040784042c43c04076203410050010b121500088941180400e0340d5400b03c000ca00c160f100c2074031640020042f100c01540a80c10a038100c0740118150340541d44e640001c2820842d86400220042c0d45da89485070400c10030f441118050800350400c20907543c148800200541070300e021300350800807040d0000d0500e078446c48001e071400066403203011655a60341810040103520b8042d452190082d0f940c28005031205104413880c03034000a0007002040c0c5001c0c03c1c4401f1142040c0100f440c124104a01421511940010046080c03100c841008a602d403100d8030003121955040794465200c5030141c404c2c00d4100c040c005400030000d20003d80034640040314604e43c1858000002c040b1401c102c00c100801c50020301c820030440003a1035462440f00e04075000c0e82158000e000040200600d1104c10070215204018cc8071924454031083e0a480c40d4156003070701d02007181c1c950b040d810400103002c1c4407035640300503c070140902140c1e102c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 734125305 1250 734124055 734124077
    0xb1b07050f01080a02090a410f060702060a020d080f070210052d070e0a03050a14120c0c10050c280602161a01030c0317040305150108060106 62
    0x84541d51510030880c10802c081002c0740b004000c560407a912008028000080d042e612110004210000700d00e0060981d20500a401c4650080c0540c0320241e410301043d100040c40c40f4100700342c911800c0c5801da000841400042d0040c0c603508010041034810760014081921803507401480e07100010710801e8102c10180502030f0301134000403a5040c0301c400e004041200e9035102d0191180188031010001d40359691415600c455200c0d510300c600400f1207582e1484007601c5e02c1c060080c01c2910388001821a40b04401103400300b0680100850509a2441610840100e500c10050607030000c0c00c451440c4d802c00c80807039005140c01200b103528600a1b0403d28100480300e104180c94400320008000300e80300c1c482101c0303901e495400203240d82d541e004100715112207040d81d0404d012203000c0c1040303d07100410030344140e0080100010a0480e81e1004075084c59504650b9030700203c00b03c080c10408614821f00001c00021014020110030086514121000e580340420b003914040060b0b21074070a021042ca00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 734126555 1250 734125305 734125309
    0xa0212180604030c0f1203061703040302060711030a080706060609060c0b1f090c030e0f031314150a0201050f0a1505011425030e03190b0405010b0603010b1b0705 71
    0x901d60722540500384211012514100320203150100034008101c00c0c1c030780440c5842c140d01b40c2c0c000400c2d075207074580980c5250004182c1c0303a50b9204e18000130350b001100344000400038000c0e0301d1040f46001e02400342e554071040e41e40c0e810b055811050040703a800b5103924041c865280d100944100510880c5071080d840d01042e182c040407854054000000181e800e24681ca4451142070746030010520702604000d005070b68240200213006052710540e0600840c240c800b462000082a161480707500d204a4982c14a40385c030310015940c00d402d80c650840d8011700b680320301d0b5040030b011b013100c5002074001007014900f000302d1600d20344004100040191405030040100c010b80000311042d10001c0c01d08095903650004074404074000d07044c0c0c10301da200404160307a001250241c510b45a5510903140c844110a50404050700c6030854201a24440224a80200410101a80795130020300032000018030300b402078042170281d0b109801c01001c01c08002604198200c0b003001c0001003c62480207403d0f940c1c20040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 734127805 1250 734126555 734126563
    0x90603080a021b0627060c07050906060a090605030a0906090b01052701050d152a020d02100908070512090112060302060a05250f0b090d12020c0f060a021218 69
    0x1200121900800b94201880200c036004c0545c0d603980203203516181c0c090b8410880c0d9648141c00340601450020012450500b001d8058500d204d1581c3c8480c01d00608010046505400c0203080d444a00c2d19640058045100f80c4914010503006041080d4190305003410301c070070700746803091a0303e140f20a4600300d4104a00498a5070554100b200c1e21b11000070b2600704040210700f100ba004a600349040d03104450103510400c1da10000e10030f10300c3d030300701900071100c20784c0c0350031509a004025800c40c11610000701c40381e51000a500d8404d002c04d84c00c000054494500e81854103501a240240000e0402000e6810040b032f51000c940c201000d1040c6410741e40030601e80c4c00303807501001c140b110120700500c0c020080c100071150243d01c07054642801006003400510005440c5055643c1014100842c090210200d204c0c1503500c0f068072003241451801c0400b0000354082c0800e04001c1c000c03910b909500160074030038070340903110b401d0000da1a848059010380030900080c1202c0c4040c1d2210340b1020344000085 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 734129055 1250 734127805 734127817
    0x80a0e0d020d02010e011206080307050d210519020a080a060b041a070303060b0c0309040506010305071d01020f0709270209130f06020301080d02070f121704090603080a021b06 77
    0x1710700500d507160f206005035410210303005c41c20308060810300e0109007440c001020380701c5280503904450500c2100c46060b035010f0380a40c030f00c1c40c584490390007c3c00040d006411003034111840d8999407149481408010013283c0114900c44006248842400b1801140b1301512028020800c950342c54546000c07600b54a181c00207404005e0340402144a50502d03002e9444000200f12a000302c0d5a1003c00031034450700d81c5c5c002d1a40038410782c9000041440d55201e4407929226a48a889104402e0f480d1080b2140a4040d2504c0c20304503c1915001c208002040c080e850080101c042c01203000d00c1c103542d10b601035400c61124004003824500c17024004d80d40d030864961708080070101c0c0f034000010500301000081d070759040c041d141c00c0c000000000c040d040084c0405040a840d400e4aa0715030300d800309090801124861000924140c80c14040415052000c1612880e02c00c03184903d056591001e503c01d54020b540b040c0d481010101c1c0b10451031341c040c042c0c00120503403c0350980c100050070000a40030b0141e8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 734130305 1250 734129055 734129057
    0x5120c01080f0702100b040b0612070909060312030b031f090b0a021201060804050f0604120e04052a090307270e060a090807020a0311150315010513030f080a0e0d020d0201 75
    0x1840f0042900d89655100e01d0081d9406408038ac1e03104000d040c0c0da0403048080c0c03018800200c0317440b40050704c03840720b200e41c20030b0f42d51060081c0c0e0400d58501d001c4001e0031220078030a40c14010000340d0800d6078001402010400a02100440d104001e07003031000114600070a100010f50041140c50b1001c280d5901d10741c1903c0b11810b00c07800320388642c20003502d04001d0030b04001c02d91140c0400d0000380f2038107003c0b02d42c0a071807039540c801400820006001c180d0300b0940e20b0402819640311201c2100ca04966a80c050b03000840a80d41060b010000003803400f80241c1c800400d40e0071040b100c41c006002a803045400c0e898181043c041c03604107078011590341000800c4070b2840d079a1964201c0070403031f003502103078006500103282240058980c1007481929141c48145c502c50078060b030000203007500e2901913903c20f05401086111190440700151040e600041207002998a03100002c0001007a800c0d0440f152801081c0d46900c07650011740180c0780141004015101b15141140c01e0010795802445005143d42 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 734131555 1250 734130305 734130311
    0x11130314031b03120702011401050f01030902062113032a080d0506040f06230a08031603170402061e04080f010b040b090f0a110405120c01080f070210 66
    0x900c2080a04500440b50803120900c03810b80d51640c06800040905694844680c400c021174843e0a070580c00c841020b000d001200841d68010001468a4a800340117031106041c00718411003c0e50020311254030005486003403044011306450201c02a031042c2d64450091016400740c507003980c9014000d240d40f08003c108041250800c64500402034134038690040d40140c04907181d0000500c94800782000301c80182c010b91600858980c0d011403402003001b00c804100d5040c0c004401403550091552201010ba41c01400074034000680100400081119400c8680031041519062500902c174500c001d03c0c600e032040c000c600344005691404100c070b82011000191803c541480f401c560300a00135640903075000d00815400700b50010b01134212034105201100d0403c200c440ea002003148002c41541c0e80035600102030005041d10b040c1c0c3c2d00c0842250121900a81000d9491000480e4030414000c03040c02a01725107122203486d600702000d150480300c092403116940c9400342c0002d42d180703143c25041d000251 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 734132805 1250 734131555 734131583
    0x11b1b080a0c0b070c030e15040506030c0c0d090e01050901150503180f0c04111305060a0309061104210302031918080a1506060207180f051504111303 66
    0x10182c5a8940020b902403901425860155000340c0030300e288444c160041003403004020540d140004030880305204000245003494100700a10002d500004d200040e807510130010f00c0c1c0d044c00d08214694040a107640d80400701030130b215111001000681c88103008100303600c014070000ca19003055800240b1140b803e00d45a58070442151064401c0039040c0100b40248417115100300c0000c501c6180e614000d4405020100070040c02185074410508420200b041c040c0c002d00051910600a011490003403401203041551a1a0700b8111104949001d5004034002410000c00925280d55411500d4030003031001c1d402d045480180d140d20504401c90403020a450b408060700e030048240201080040d06101806034541007415035903100120141c80e0103400a021000050340c5010f90410340306694042d01c103c0d882c00c5001c00c0a0414415140c40c1e060300e401006c0c1d1000c04500c51244a08008101641c0024000c0d081c041100c896100e4940c030b19504010341b5100f41d01c0a039490301141d41c01811040c9a003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 734134055 1250 734132805 734132807
    0xf0f0703030e011d09010605180109050904030c05160f03020f0103050403020c060d060e0925080c0d1416140604030809060c0c1201060806010b1204110f12011b1b080a 73
    0x200911031130703911080c40e1001007070340d941c0040603088030009100036030301000d010303c01036403050194821035510900b068000340c0040c1c40345607180780c520701c61012070f1424911000c10031428040c42c0c00400310841c98102c10800d52078802d1080349924400e080400c01404d042d10700a464840c4004054000d100010b0100845802a0f00000080c05d0045107040035003010f0050710f0f02c0701d520381200303000a5a1803154600d0402071f244000c080310303424001002e1001d074110520111140050099808000307003841c0401d062020f10a890340031000050f852542410108071070f03048840107420a00541c002d101c09d00000740440e04403a101681103500607254000d40c5100e9103000130590025400801c00204014100f0054000ba4180c640c00400d03545140e0300c40441d03000d203001e210b800c1a064542c080c007080c081910355201d06070208000d0101c0c80c0005000b004078405103160320b500d00d926035603102c50751803500a04801c050701448901c0c00305c0240500e08031014030310f100140f0190150302c000510302070607 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 734135305 1250 734134055 734134097
    0x11030c0a0e060d02240310050406060c060b010504091410060801050a03111f0503040b060d2103060e07021018110130051801050601081f080f0f0f0703030e01 69
    0x41c0c1a40301170310945100d44840c05910317030401d40e488410a40f40c0840880c1a04d402d00400003030310303129a2007040200f1641c854001606941e0010b070f050010800010070401e415000300e00710b003001007a0b0410141480314044018101e0b0390310600030887d014006000b5540c0780761003481200d400034068001c1d24801c0c40099100b803001c040040e10301500075045003a0035000380c080e40c4264050840300da910354a44d418840381a4490724002c16600c3c0280c071030f107c140c8403949a40907104462600180c4d040d12070700300c1c1c04a0300c0306032014009648668100600c1d01428040c000800360801100354001020703503a0744400b80c000da0f00040c1480a200700150000c0c41c049040844041c60341b821010103c160101040204002e0320044800c5040804001c450b480c1409014020310301a50b0704e10340d5503500603459491202c03801601c20324801103040020204400c00c62031047e140410041d00b4242c400503501407400000d000000440e4101283c100013194000b010243c0c407440a080885400d0808401c190344 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 734136555 1250 734135305 734135329
    0x170403110108101217030708190b010203090108090c0301090b06130e030904091406040f0303060501020a0c140f031b0a05091b0d0605041b0201050a150323060411030c0a0e060d02 78
    0x74084000c007c01020740d40c020380050142c02211407140095141c07207200c500340c0700440000e070302580c010416000315500c11100703560f002d03400400390b41100c20000002425035603d20019100f6100c40800d00100b840e01c03180300c030003912032068108145103448440940f680224115207100e01d03500d10300b0100340280c004c1e20044e2010f001e41902d1302c501d8249000c03401820f1402050300007a15100001c01d040d4000a580e200352a04212030300050f5150601044540701c01c03140b2690022103c40c04003510b81c6080084400148005915039a000107070340030312410720301039848680b00d00080c205000503120003071120050160f000341e00e9680e4820f001e112a001c2e0269510440d0040e24180c10341c1041070b00c1c04880015881941e0003803189880300d4011400b600c038051000c00360070200c032504100290611b402d02c4d48078150030a900c16650728000e262070401c2d40c12201a100c0d0010f500f04194585402e00103016110780441c0c030f240740f1505100c02c8180603040148014050002c01c0040300070743d59400310243e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 734137805 1250 734136555 734136593
    0xc0e0f0d0b04030c1704050609040905190f110609010503040303090320010507030b010207080705010c0f02090f0906010b19111515010305011406120403030204031704031101081012 79
    0x450b41003034034000f040400d82c001c081d01d0b00004c0096030741030755202200302c4084030402044141461582d00420006024082c42116544220000c260b9034082e000700c1181014000d409010a10030107050400810750381000c800d105000070030140010307a80250580b50040c0d0186000644c82c2075610301a0703402104440441e0f401c0b210400780c0140c08205400080c41807405660a00400ca21074005a0750740e14039018031011900009000d104a51261803090940d9014010301e06000f459500815207010060f2203480b41040c0103400c016542c03c041001c0c900501005c2412850240001c0b1008800d084019404041111222440890348002c00403005061015902e04906040c10b050300100d00c4081101c003070100b401d00d0000622503100039110940c480015001518000c01c0c0c1e01800100380006000300d091507400d00001c004503002c24411010b5100b05900b4550381ca0440c10040401c414100300141000b2062081204034200380344240b0840e80c801c03100c405c102165190485000e1208083c40c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 734139055 1250 734137805 734137823
    0xc071e060209041a13090503040e01060c02150403080f0f121006200709050c04150306091a0a03020411160c0f061404050f0406051807080a0c0e0f0d 65
    0x19091100650042c014a0b000700d900300b1005007124164042090340c038103040c0c1c0c0b000404002d501c6010194004421651040c01601d2401e5210250410151002e0300410006401028a00d0460400c2d4081f00d0325403541c81e420f541401d14640d00c0c4d240c14410241c04181c01200869040d07020601034082d560352100450000005161081074042050b10b18450040010b800c0c0c0065220360210360340e01c4001c414404d000e8440107080c0050300000e0b14000e4140088603408000004020368804030350300311100269804240340b4a0419101e0582d5152000301e008018801d4104800355140d1a080d01204e60646006c00d1802c50b051401745140503590b888004041c80b48d440008100f18900007006540e0b40c2c5100b2241c0c251151401c646c48028641e0000d0f1001c8104814001c501d4010109151003400030f10105659850b18003180c4070010206101009411000a1094841d0080145c81c3d00140b0141d0800110307400d03000051803a102c1300003103805185052003484150f2104006409031a400400705 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 734140305 1250 734139055 734139113
    0xf03080a0903081615020f030a0b010e060a0201050103061103150f0613030807051e0d030b0f040c020303070e01111506040e012c0303072a0501060605091203120c07 72
    0x4500281100404640c1c24198102050106009109942c441038482c500d088c19a41c0b03504818000f04034011160f410700101200da08001c1d512a00140004c00c2c0c03580c000b003091f524500c1c01d01c0c00e5039500c9800c51440c0c0000d000f00800340e88014028180880100d980e210004078017400314a03d441090000c1e00c42c0c800c0c120300071061014800003003040b28410001c6818001a2000381444480440320880068001440c00343e0501c0c4290016441d10030024400c094010440c0002011640c4a070001d04c0541c10110411034056009031001641c22000c0c28050308031407042c64500e8072540240001507081c0e415101290740e64031075604c83c0418600a400070000f140c1c0c2d0140c503261064a00d02036000d581d42c485444030760342c100801a64060201900ca004e13880d0740745c4010b03d2071311b112480d422804001030607558006c10001d0003440c000b40301540381c141c1e50307038901c405000340c00000d1001ba4140e94010400502c50903030000701c06900c00e0401144503202e481919206483e00540180851044000c10f13074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 734141555 1250 734140305 734140327
    0x610051c0c0e090c090d0b2d01150c030f050f0c03040806040c0f0b07140a0203010f0501060906140901030e0709020d14010914060112060302090f010302030708070f03080a090308 78
    0x200e1070242c0402c8803d420780d60340d03c4138509038922840c0501034001a070190000001140110b106400103d404070140d41c0d00104604500d0a000c0004004051461030f001004201c81c91a4041c01031001403609684958007914094001a5a082d4a0040100005e04819000800c0040da01040070282c29607907519910503880b90703514401c0c0d90503100c0001081d800182000080b9030754049402c000b0160341018002d880b0400c02d001855611b1445014180c06200182d03007e00c40c0000300030300d1900c0040d0075410281e000300700a8a54220406000007007507046105200e010645003070707080c02d1a002c0f07803000892096a092441990107803141d04c0c008507542c680d0f81030740c3c0c0010301800d890300c11100b03251307907101440c0d026034000516820359005100302054165115100d04107031141c460f00d01040407a52070b404920701807030448102030315002c00c10042c4110f10b81445a0402031210780e00a0207031509014a0440515062000074007131000020038900123409010450001e5400c036905d940c8441489807 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 734142805 1250 734141555 734141567
    0x70212120708010e01210804051201050108060c070c0e0408210a0513030c030f200106031e0201300c05030405010605150a080414062d0610051c0c 64
    0x1500c98080b07441d820012541440da0342d9020b0407a5003080312050034820300600030480c2007101400755080b071000c000c045042c0d01c420041d5044d00080e000005442d6251811072401c2c03070805894082508000c00400e03011510341d0700390710140c81c650710054013551201c0c500808148150404d240c2101804000c0002d40801d0941051140c0000715041c4a0359071064030481c07121558410041c0829544164000840d11484064000030a542041044680144003800050440c01c90b9442c0a0f034544800340104840e5400b00554100780142072480740c5450f40c0040c0c40885c05409152074480e00d00c502d804030450045500155101c0000308000301110760800509980c0f00b250151500d41c284400000e090410a540d01c1401103581c20680c20480d44180c206c600240250007507441849104281800e0102840340034010b081c0701c28008402e04903030201003413110454168510b1703429900304224003511454040407458183e071800c1669241000070340e000d1b4036800d4203240c00c1c0350702e4041b11850b000d40000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 734144055 1250 734142805 734142811
    0x31903030c0509060429040b07050c0f06040b0706292103030115050f210108030903100e010222050316150e01020f030a030203010f0b0901140307021212 67
    0x1035814081c10007421401d89035407280b04a00790308120100001c01081d8a54141e00705610308098802000d00781c40b03e10304605400c40c0d040f40b00442c40014400007040741c200030383c040c086005c0d10125480d0203840c3c000b41e485d0140b486550702c042400660101000502d50180c1c85210030720b0f640002c0308940c03141c90380b100c0841c00c01460080409039071034101082c80c141d5070740c4800c204000030f526580c2000d00380210348451030741200c18031101344141c4030411001409003064140304074213880c2c00780d140c0c0087c000c4118182c0c0144001d81080110322340f20b840125101c075800c9840040030071140000d0b22181c0c0248506020302e00c02d00c901c80c0c0d0900000c005600c40a04580d8201c00322401d0003c2520a0310642c005d501c5460004070150036194078040c000c0da4850898070050040e2070481021410f0f05046600c4015810300284c0d0002c010700411110001d101e01034144c0c20412401e10740070100281051880c1e80c0c105c1c103c0e80001c030000d070046100f0400103210400301000d286d02c80884540c600000300d001d13 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 734145305 1250 734144055 734144057
    0x30702092a0418020306030d260c0903010b0a030f020904030908010c0f18080c0d0f081207120c0518060c010906023c0f091c030e150d1802031903 64
    0x2030f01c0008002481402034034042c11000700603107102c440312602030780d05207400c054040401a0940341c007800c0c00010002d40744152080282d2655848a54042508459030a2080c61080001a40c01c0c80802d50b0034003111180ca030b05440702100ca4171141000e4401c0d2042c2d80c4452410342c2864060300b2200d07407101a40c82012499118600151090950f44910301aa03004690113503204006c51021850f241840000d007074003803076002e011850b55031a000b1044e071040324680c5030041460240540c09511403000b50860100080801160f030305860300424910900ba0300000501c201113503041241c1d1108103c444010014000b00100c440b0749ca0444007940021041b0a149042c000d0700718251049102180384c40280441e882c079003081c086559148540062140c000c0c0308030240302c4414143c0b9001080d41801061182c504c014107401d04d03004000902c1205240c5c0910540400c070300c1500354100903580c00003403400c0045220428101d080051218800780a5414828030342a004003400600521620b0703402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 734146555 1250 734145305 734145329
    0x9030705040506060d0504021513030507060804120804050705032a060a02060c03040507031712070f0f030b1903080909011d0403030207050f0a0303020d0f050108030702092a04 77
    0xd1001000115101140c040703030003000c100100d20514030140c2c0b00c0b0380e10620007022002852284081e45005800c18003000800c441034050070f109215040080c0340040625240c03c1a07103150940d00c07000130326402d00507803003440b4400021404025081c062500a0003004d0100e510300c02d0328035941c201110980031807031420f00344440c600451381000c1e0200ca0902419400910791a202c042420b000d6504c0180113490302e009030100440091801d03880c0703100c10010080c4441d16040b50405c881c80420303018280505003c0502c8104440030b40060318030b4454940340c1000280d1100b1080400c0d902403041c41101100707840c2e4900407042004050152444240a031602e000e50380c3c0b940340c008800c00701101201700800d09070b00000c0c0000d110350010f042c0c491056007561044207801915a191070922300007140800e4003c80c0700789103e000c0703204140400c699800e081c072255240c0503840e51039109500300130707015082500010b240041100940100c2c0031105a86006060b01441d082005400900558840c008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 734147805 1250 734146555 734146559
    0xc12011506030e03030411010c0b130611090919091b08010b01090f0b030a110c520b0d0e0607211d0f0102070204050907061e05090411090307 62
    0x40b1034400c42421060842c011440c40e140e64848640c61150f8903a02c40c104014800c0c800001650306d01e20500170752810109c040003001a207881c5040d6410341c0c400041c028010701040c032565481d6141d058002e880341d09107904c07004a5100400180581060281c08828030246010095040046100440d65000000c10091000100440c2d4121aa01c55a46143c1e000d0100b0302004206500840e08000d42e11000140c0380303240400c1446c103800150800c103031900001c00740d011425000d481820007170b4030603c105400724001001000c01c01c0356810705241d044001c581c1c0005207160416400040c006080d5a6130701c5215025000c0c6c0503040403501d20f6414062640401d5100b4010b10700c04008a80f8140b482a0304d4051035080c2009107a440ca120481010321030100104010502c0f41d0303801c0305101000036a8078001030060005450002c0c01e003040903442a8000c2005070707440f8621140c0030980032408422941e001ba0201c880d4024a160540e0245c600b4007940d280c000000b00031312030b980c030075011381c0c001c59 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 734149055 1250 734147805 734147807
    0x2e06080906070320030a090c06050d0501080601060f05160606030803090f03270109090f1d0c010519031401060816020604120509031f05100b090f040e0c12011506 71
    0x3400481080c40e07400784c422803210560300c482015641c0f040c10346030300007902e400303507261500c6c20340c1541d01160125a0001d5070044203806805824050903101004002651509a00500d1014100d5520b0100840811083c0c400141181103525503a008207040c00a540c40b828041a1548180c4034000c9600c2640b1340340c802020084282c400f03c00c4000d4004161070080b03140d68040700494680541040541e90000ca0204050320032007080844030303140060034120b0303024400700f2040400d0540300241c2c080d2020f00003980e0310400f198980c051000887c0c60400e062841035000d002d422417840e2003501c0030b400116040340d0215000c0d104484150504401d0040da41051741c2340e220558020382075a200000c0540110b00507002880b129a01078121041040d0030302c080f11810308850420003043e51a0010305c0400d01d6100c407007801905040800a00c0c0440020000341e03e0240c02d00164043c0e602c82e03480304a00351051200e55207070b0f02701403c9181c059001494681c000c240040042d0150318107031138081082 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 734150305 1250 734149055 734149061
    0x618020306030d18030f050a1a061c0228030606031b1e05010327140606060406080a09021305090d020105071b1713080705011211032e060809060703 65
    0x580c0600499100e5505607218034404068140c1c2c1034803e42303c0c1000c0c00c40040d00090750610f0001001d015800503060440802c10484000e01c295800840c0d005000005070795040c00000c501580481405045c800c0c1408621203107560303600141c4202e02d44400042805680010b4501c2414949440c66400da140d5541c00320000031b420441240c2c4421600502055002c0d9000203030a148805160003158903c400c881240c10b40301d001159003240e1000c107545110010021150400000c540301410181030480040050000800c0b00720880d0300c0d05400015500d0741500d2200d4984120030500040c500070f174106076110b01c2448440015840c041c00180c48520540d00300880011071045c04401c203101e0344400400c00c150b0000601e6071842001101c108880b031140c15801050080007030a43c0c20b24240015000340381c04034082c40320034182a40e0074a4201c4100860380c2c00048480c4002c06800c0c0084103000380380c694000b2980c131a0100e50080307800d9402010952003220410111100e075900c944003101a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 734151555 1250 734150305 734150327
    0xf0306040b0612061207170a050d09080a0f06110d020909010807080c010503091513030306060503010612050403170108011a03152703040303030e0c0d020604120201030618020306030d 80
    0x3401d0b0b03401d001c95105d191614602e2280c14004080711605a240c040c06001c400589140a6940d48048003500c00c100741800210200d40d001d081900503e454154000d4850082100040c0705510488140003002082c0d40507681d514101ca100c580c40350400d092480c02988142c0c0e109118000c03440000424400000340c1034142c484a5003d81200d452142c0156415003011300300c1001401000c0c2c0030210402c290700c2c5a44240041e007409801d440840c2009002c880340c60b0003160030041e04000502c01e4a8024807480e140030071001001680d40e070307507040403100c01110424015002d6400c100004c0c502c02705402144650143c20981d00e81d2102e01010507a23108001114118180004c10003c0e0b40c800c0c4407000c0354003001200c5404501c201e0f0700c640d01804c59100c2e4204902003555a01328400b1508104009025210161103207500e981c0c3ea600018018000c900c00c3c9195070710644900d00840e4800d03048140204108902c141400c502c0e10361210103904125801e9009214031107903030380010f03c21100080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 734152805 1250 734151555 734151577
    0x2010e0a1809080702040c02010b1009030c050d051005011707080102071109060102101b0e180c0f09031002030714070b010501361e06080a02090a0b0f0306040b06 71
    0x1444415020710700140a481c2d5081d102c0307400c00e02c07560340580c403a03010782c03039000145a00002e5090f01d203400300600000110b9008041015014040c0000b1f05041020401d85404032450981c45e02e06160462030081c110144040281c10213000040009621800010440300001960360090316a44c2d900e00b01d004008028020040c1440740c09010b050903141b480d00540b040c07066a030034900d43c40c6220142c58070505135071801a10383c0c0405244c41e40c003c0d101c0034503540480f44240e110500164280721100064059502c0c83c600055000392441d2080407120120303006030560700030407170031b00201009410843c0c07544040b9002c45114541080944100e8070b10f15445080480c040c1d00300001120251a06031904008410030140d00c0e0507240e01100500d040390209040e04a02c5090100b0040350203c0e60045809040103e075080c4140d40d00f0804c100da20950419005854001001c006180c1d20380550100040100018a140f010b9036660300071442a1300907a0140412201802404900c0c424461000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 734154055 1250 734152805 734152829
    0x5090a081b24090d0201020f151605090f0111010b1c140601060c1713150e040e030703082a030a0c0207030b011809080d140604090203150702030c01050106080402010e0a 74
    0x11241c0c44c2c00041c2c01152401071041f515112a200b0b4114603102c0c41100003a0000240d00800000d00c40d00c00c13003e094a40c05140003814800d586000c91120700340030711400e051014040d40d40d82035400c2540482d1010318020101d41001081c02048000d003120818161100c104048210040d034600140180c12900c5941e02e004144040c2e03224211881700c40c800f1008070500801c545406507803403045402c09844c940541d004105044000074100100c141c10b118000d5003050700c548405031001c403d84503200e4160a121040e603031038040d91a1f8070309400c3c540300101c403800c03286d024540001d5401785210783e0b9581010000906100001d0b41e5031030240c4802001d003c0070070018088a40d0411105080390f01e02c0710003285d503035403a540e100a070350841c0401a1000d5614445418844007034002030381c124109aa040019110316004a510b44941342480c5809894510225400e01c1c4200121425440c0e080000c0029586480c0004c000950984081c1d00241e81074940d20400d2500d0720300340007200c1d20000c0203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 734155305 1250 734154055 734154067
    0x12011b0c14150f040c08121b0703020a090c021002190216050d121e11100b0a03030507140d0c0b010603051006200f0a0b09060c04030305090a081b24 65
    0x100070003c2c0c00400880301ea04401e00c0000718107800700107018100d0343c02c044503500d41d00d05481c04000d40320320765148111940301c04410405a100da03078110007655500750f000301b2156a0060164a030141a660402c4590320010b003020b0111007410b10030440c80d0080e42a01c100c0c2408154a03020311519010340c551104081b545100064413401e8907804840d92402d00000740120b9070100d1940078020004800400c00c40c03100107640100502c4050b841e806842c2d810030082030b8050108080d200780340802414800d000464006020658140641d0940e00100300c80b840842c1100080c00303024007450840c0d0b40e400c000d0012600b01c0c028001c451080600c1204100181d207086021a5030360360710000c455514038002000c1261050500c40a01d107407504400402d02c0d0341c42403501d0040c0c803400034a1500d140c2c2000d020300003c404d40c0b000312003c03a5010b00d007440d1281c404600145180c4143e41c0311049030710030403a241c601d6001c1b102030300c5048403003180c0907000c1454103100b90f00440d010116400b05e0f501c08000e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 734156555 1250 734155305 734155321
    0x1060f180b0a03110112060305160f060906050409050c07020a09060e07030203070c030c020604120803010f0b0f040608070e060703120f0239011103090c01091412011b0c1415 76
    0x1b1030210329481300780114000c1c2e0399864080c20700030600521031160f00e60715003d00c0320002c010020002000d503440d11035101403602100034054025070040a055645800c003103002500710b48250fa440c3c0ba002001c807a4101d40d82c1c0c107404010070603846681d01d84120b80d00083c030b009000e4400d50f481119180c58a808916866a080326040820a000c0740d10090500000c1601e06c240b4009006d554800c0807002e07520350601c00b0350f038100f80d0305520103c9000000c100324508058030000b07460480c0d030305050240c12a1a0301105441c0d00d041d0764111038000d800420356104ac1540114054012211490704000014000c0441d009921500c006800310814081081c4000180c41c50703c0117580059203900454000c1d001000d60a40300207004884070000e0200034004441408c1c0300d062a809001d0034141402d07440e003000e45607020381c000f800f40d07c2003407006170360802800300b900901803182110752a2a24800c400d000a000c4d00c0c864401603480440d009a114060000007a55a0840f00b134085848034698030404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 734157805 1250 734156555 734156567
    0x10020f0d020c0607080703140d0225080f0c0c060a0c02190e180a08030108010606170403090b030726100504051e070c06110406080a0c120e01060f180b0a031101 70
    0x1c021000c0100210f2340312213001c1d000d0b000d0080510804005a0f540135440290300b00d0310b82000304410749803640d442420018640c04125402c246060316010344a0030140702040c00c211400e04602d40042c00001d00800213503102c4c0c684500316208859403060108141d4403034904002501030311140d07040800100c0e110406d80584002187c40020460f14003103825980c0781015002a84400c0d00c6a4460005000c10350f04203a42502c0c0300c03102544500985070589000705400c880e403080d85940b900c00002305804a1060081e000c40c0581003040708502201417031220340440d800c030780070005962108008034581c98030303010308d82c05552031a07203c40b08820800030340d242441024014400380031800501200042140c003411a151606162040e150340c079104028003249401004242d0031441c001c40c04401d21340040f000280314003d4040046d4851841c640140100b00c40d82128100301c1c0400c1001480c0c0c1c400803c0407004144101c1e00b0b12810461314240580340000340001030944101c03601c4036425502c208 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 734159055 1250 734157805 734157817
    0x50c120123010501020c010c030f0e150316080108030a120b0103061a1903020a171009021b10061a07062702030106060207260c10020f0d020c060708 65
    0x2900009420180500c400084410241220910381050004021560701401006103400c42820081c400c0003503981c00400b0b554a500c08407050051800c0c94003040c0d21103540c4000c6081c00c0e081d00366aa400d1006401050040c584945000119480c00200308100007005480d05200503440b44000d079001a44a4401740040000752410540e4a100000d60800c1c85002007010004074005240c0d07a0f400c2451059150365500d26220526004212403080c40c3e500c400013a8050300c1c0f080c60132806840314005142410711a9114805050010960403180f1843c00224603201064100b202e045a800f110030170306031350451141501c05101c4e00050961580d0000080401910503880010004c82e140c0c00c1500a030380a9075201e00665012042004508091241902a181e980010249580381003094040c074038005519001440c127500007904444c104104440200078001c01080240580000083d82c07003451180c1901f030b51240b20405480a4000700b030512801c000606180d20300303a15900d0b02e401c1a4045 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 734160305 1250 734159055 734159089
    0x1b04080a0314130e041e0209071b0c0602010e1e0c060703030905030a030911040b030d050a0c0209070513060e0102030306010f020f06011806080f0a0b060a1206020409060b07050c 78
    0x802c05003d107082c201e484035014140884500b040ea040c40e08085c2940404452444400c529280c01c20025030764681c4032550003c080e00d8142551703801380480b042c030001030380b0008000b425a900c01260703603074044d0040045c07811540f00f1100c000c003d2a00c0300c3d15003106100c50300c00503044400c01101d1030030110b00800c4454040d080101d1141300d6540e07100d2455000488001c00266107031f006204101e105104805101c3c0f0442e0240400311000000a032104a059401c200f4003d0015100c1000348c001c1900001c0c0319002090030690b4a881c102c05040da91060a000c10880c200c00408162030740290144124180188e00460460b03070750341c0040d80c110260701000380c154407850120014520b03080000b18040c103005c0348401110003e58068000340c59650b0021009500840040220035400150a0604a8000712611201e882e0031001c511005041d800a070b5142500001030424070244d84c00410032a50f009000f0810715903181084905405042c3d4010070503041801c044960b4a4840744030b0b0390354010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 734161555 1250 734160305 734160307
    0x250909021c1a0901020a120b190b340b04060e030309070504060824040f050303010b07030206060f0d020405041e030c0218010e040807030c0210081b04080a0314 70
    0x849110494140e6012021100b041400307910244400d5040c90981d002200e10000f9414140c1c445d1020f00210032001c01030803056942c102c0d0100582d42c801d0407403810120300e072420703641d552580c01d0742e4103580c0324640780d1a0f01042c0a802c106800a0300c0c81202c14804000e1410907481e1003999854a600381c05031003078802c981c460b520100a40d10a1004500510000004003121071420050001340d44296008000981011620144060390410038611003036424a040741980e486160402803420002006051488080004220034000c0d200905420f03001c1d0b022914140e41c0c100c10000014400c2c0c910a410a291650050060405da04400e4216204410301c21501031100384414050018034016000140c0b01030241c0e003581003c0041e200c0c540810845848103604060114a1041001c0e00c0144010030014958050601c81c01130183c100394020a01d211405084400030843e00e07040c0c600840c1c03403068102c010003445800b8120b07012030760404068040c40d007441e08d0556241c18041380c0c0400c5240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 734162805 1250 734161555 734161579
    0x30c0f070206040623040f0b0c1c09060e04020901050a050319050907170102030c041217160b07020708060a0c0c12050304030228020d03020a0605090c0325090902 71
    0xc0c0300c00103080136141c03a564203c940c101d141851050050485504d01d407001081100380002192a00a50241ea03081c4101d42d40d980e406400b2039141c2001a031030b00d158584840050344000340c0c1714100d82c04540c0140e40c0c03e0f9072003c4100c1008200d104000255002c640104105503442d4040c0d0055a4440303007d20794107405005461070b101c180c400481d04408a40c008201c01d12400002d038000c20301e030340204802103041d8680b09800816901c80c0d409a50b40464103401170b041040000000700d2071620040e02810340703c001d04090201400c03d006402c84454418100141c00d00c0d2000aa60044071a03603401000f02f6243c2400c108000e240b8043e001c020001040b1104c004140b242c58040e090b0b0700145d80b9503541e032070907040080c00d040f00100030000c2030848103e203c0a480740c418020341560380484c0c12078130610003841c003a0324000d05d00600a0449040c1410045208000308803032030070103000d6094a040030140f070751032542010840403600c2c1e55081c41000b40701e08141e6622014902c0e2024080b60f0f0004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 734164055 1250 734162805 734162809
    0x171605031512011b030e060f060d02060706110405150a080408130b22050a0303050a080c25060b01170a0213081e1902010225090207081210030206030c0f0702 69
    0x1a00a413510844445031342c0c0c210f1031140c1c2c1407055403514041c030b5020b00268204401c030000c0081e400341c4030610880440c00c0f040700355a107a100b200c02103580000c00b007211540c00e5503040303110b400071b1003450703c40d002d98844040361a00100864940898950300d00e80e550f510f5923210a4540c03c060082014142c41e004041207400f1050010800301050305070f0310540b451541c20790001c0e040c0b9604854055a25a2410000aa008802d8618596003400c16076556542c107150100b00380644100c906100d00f40d20403030b103098424010294411400340381c00340f004204070703001520705441380d101440348801e4610000e0340c1113419501030b14405071079000c140d20103603407803821515043c4400e110480c2c900d603001e1041001982000905215500101b92007000e01c41900085e40394801da200c0c03246601d2501007111020203000000c88090103520300d0454940400b0700304000c0fa50425030400320748000d04800708240200c00041750046070780c000c01403451513070341000345202c5030041d80c107100d03c1d040d00307221801c016 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 734165305 1250 734164055 734164061
    0x5190819060f0e0a0b0108072a03170114031b040603080f030f130816061103090a141b100201020d021215090402061801020307060c17160503151201 65
    0x300001040b9003481414518040703040d0501404041c0d80c80e1400422400070303604055100d41c804005e080840241e1049040f404120125444c1c420340b981140840c0c0b010150004d003080c0590f042540084040e82e2190401d5204400300080c266242d440f001c605406007a00e0b052012290348041c0c00440c01c59038a6807030b102190001012500604008020452034002154500f584140c40004003d940c11050b02c441d0181d204644288040343e624091000a200c000d4011001d0fa54a461609640b4580211029182c040010007141c9400c0450200703a6210000a00321598200040501d501e88111200304010122810320080c1503540074410b006a92640e440504000303442d107c0700c01c19030710b4032600280320211040311491107846000280000343c0c4070202a549500b03508100711440581c244d00507440c6004408000f8980f504140454014550000c400c003001d0f006141e159980d615502c00a03200702c015000c075240010001d100003000c44a01250011f103902000d0180403e0700401c860160035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 734166555 1250 734165305 734165309
    0x3021e03150a090311030a080c091f05030610020a0c091d01050c0901090b1218010e0a05011d0307150b0a0302041404030806010302090306040f1e0f0c05010519081906 73
    0x903d560b051840f0a040c0c00a40040035202d04101551a01da45444058084034002d40b40c1000c42002144189594403900e20440c0036070202d1031640c04919000c40001d0495104454541c004d1002071001d42e540742c0009445100c10754004401c03041c840c1003071070450050041c20340d222484c418051101d12007410a00c03485000d50091b03407107685d94030380712400903100143c00e0b44080000e050800c00b02c15490400203006403c40c0030080064254000742c114140909143c9140300e43d43c0c080cbc41c01c0c20082002c158414080c11204810000c2040c000317203240783c0c490148460141031100500c2d031508110503260f01c440c0e00100e00410f03a032444c0d1f8594001c00c0c2210f03004090b80c0c070000600d9003804145278003e0142a4400d40034a41586070000340030200e902c0700b0002e4001881e0300b41c400301050801c00b001490307e80540405160070003181c040d0902312080e081c02c07102038a0664890002044c03551003071301200c014a042d80d030480031600c0d060004480e1000c006021000c0c20141008900c8061094011000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 734167805 1250 734166555 734166571
    0xc1e030a02070b0c0604060e1014090c010903080a08130b0403050309071a1b070b0f0a0f1d0d0c05040203070905031606020a030f05070c090c081003021e0315 69
    0x1885030030200020380380a0440d040200300640c01d004041184a001445030b90003540080003140b10040c1d517024030314003100b03445103c041c00d041172003c1055036030030603c4511074070580301107880259403040195080a0b00340405040c0d410100440101c441c0035440054002a18540d0030044448170f440b00f02d044441950101d00117003000060008032542007090202070400c11a07800c240f240c03039901c22290751249418400200030454101e08150a0a002607802440e50341d503882d80d1284280c1020889910480c11040072440a50700c643d101d900c41e00b085c0414880051012604029000170010390501000d022a8204190b0030301050b103407218009103005100c10703201ca000040c1007104150030041840043d840c103c4243c5000c1140c140d00096080000380c250070300381c1d142c02c14260100d8003846541400f034051100c000d8000350380506a48100d941031a103a840e034195032656112086194070701d1102035805006c549040320040800c40b0b000340031503c01801c85443c1507500d0030394a01da80040f42c8241e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 734169055 1250 734167805 734167807
    0x90c1908041112100c110609011538220f0512030301150c051f11070c1406090a080a11090912160501051311100509060c1e03 55
    0x100000700201180d04401154001801560402c20769a0340e070706060f0020b002900c172141600054000c043c0e0340c505a25010503101c1c01c0c03070000c0c07203507002c2d02441105506002803c1000a4640341107551941c141800031001000c1e0703100e403020920081c1d2500403801400a08001503010102e401e003080c812403404918200a052078080310360341910306607100340d0103640000512200d400010049034196080d5501d444c0c4802980c4208880640310400c7c01081da103ea200f030b600c0c01e168419185008800c0d601002c0c4003100c01c240d50f80a4501840310014011404480300740290b00e101d8800601d103010240c201400e081e865000540850140d80c8400c1c0544c0110301070109000110706d44603280e0106440001b160b00742410010b03a100b900b00003061402c400841c042ca40000f90f850030321209604034009000031708100341c612800c98240d01048550ba0791010304161181420365201000c82400d468490511440340140b01c207981c0031a20210441c0035400444d20310350800e406002c1104400c0c4c0040d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 734170305 1250 734169055 734169061
    0x303050610050708071e1410050c040501051e090a090f0c1806030905100e0327030a1514240303030103110d0218160314040c05090c1908 60
    0x100c0000c1e0032150440e010000708000d050042001981100c801a81c03150a4007144004091490000114150001c10455104030a6400301e0000246110000040c100801c02c90b1141c100c1d1048038031451244d940440e20a10100050600d1250702110a088a0780d81d203127003044640004002c0da442d41c002c40c403a9a5a40818000a065403007038902158003828410b0991f03440c211500a02c0203940f041e03508154640014400f0000240940c618103081b60009118810004101549036040752281030b0303c81e8000040d05910120140f107074409500040e014144d201a25290f21020900c41d0051141240e190b041201c0d42c044451403007442050018444c01c081000c40070040c019462000c4901d03c00d03031041c00180049540180184114802150401c46004540c804200c4d800122428900e41e40300c101d041120b2041400000c041084803a6010402c039426002184613901081d20f000e0940340492901340b00c42e042104210f5080b607060520381d400c1c1074401d40303101c030300e41071602250000031810014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 734171555 1250 734170305 734170309
    0x9030a030f0c090510091d0f10030b0a02090105040f0303210621061b23040b040b0c0a050609010b0108090f0a0201031d060c040815070905100e040903030506 69
    0x60840101e01c601050015000042c0c00425100c128002c00c0d201c3d5034080c10580029002c0d034000f20007800d840c2010803c1c06001c0c1c0c6510b1003000119035001c407114420002407503561201c901842501d07844034807901640c0b00d00c50450001e400c4001554144042000040b498505068880c40290300ca6901d0419904015220502c00c440d03002d109103006003000c0f02031060301701c500e0b8055120320300e103a10722580d5600c6040c80c501034801030140701ea030b808102c030f845c4c28039590204103841601c03000c0d445549811350111082c049485184900864201c06110a0104c1850600280f00180c2c000049a1101300b550f16480d04001c2d058540040907990341d001c181582d60461825944100c6001c041c01c800720500021a4564215004c000d0415948580d44004002081c1a1180403d0008112125440c00089400340360f44540039a40031481040d00c50400c244120542610440c070303035950109001d01c0d110500c60036040c00c480301c6042c0614489013078042e0305c6500c40e0103c4a80643d40104a509200e01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 734172661 1106 734171555 734171561
    0x150d020d1506032306010e06030c060a051206060a170c1c09150902100c0203011b1805011107051909020304050d031a0a050607060e01020309030a03 65
    0x803042070740038294050003d80380700300d50ba2002c10210f4400740c002c00c1020560080305500c003200611061a83c1514940c00c800081d04071440d4040c0000001c0164218454440c0060350200f034035500400324444031a040642aa000740c640800c0190041c0010922280c1a450000f0315010824030640b070000ca81060061030000380031078110348403200141800b04815100c03121a481c1a5074103462a104908840c1c0d070040810f030300c0c5452510141d6544d8411041684c0c07655899906203527407810209041172a0384244c1ea03181030709d010b41c81a0303221041d0a400c0740713040244910044c481010001040002d5038803c0710211301ea841200c1140491100540003400004c4c000f205001c204000002d072072198143d5504d0a12400c59042041c4085c6480403c40d5903005043c0e601c01c0215081ca080200040c50007000042103900080b244242a03038402d035034441091740300040c0210403650600c = true := by decide +kernel

theorem cover : BRFrame.Cov 733992805 734172661 := by
  have h0 := BRFrame.cov_init 733992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 733992805 ≤ n) (h2 : n < 734172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
