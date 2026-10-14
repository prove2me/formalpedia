-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2653
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:20:52.954145+00:00
-- url     : https://prove2.me/submissions/d703bce3-114f-42f3-aaaa-0af57fc09868

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 476978417 ≤ n < 477158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 476979667 1250 476978417 476978443
    0x5062101080d0f0804021507060603170c03040b07020a17010f0b0f0f010c0c0b0a11011d0a0f03030204120f120f0c08070602040806090a03030c020a02010801091a030601180b03 77
    0xf0224000902502400074550000c1c40a0035a0003103580b507014143c0c803a006000c044a40d903880c6c804c20800d0000e143c01b0301018004103044249000c219103c0c6682c0c910552082a40c5e03a14041040380c1550358260b08000144440840b01001c0703400c140c4624020901e48078007010aa280c00e10b010141d041c85003014402c254003030030142c11002240015a410b05800008031105072039004042851501403018008990030b03922400d07006520f0405540c01d60310124055508980c100c12a1a2065800a2407800720f54210000000c06250340c20200c02074031440d045424101140380b00354042000800d1540c012030700a859007092408081000c480003c119810300c40015170030710440f03000c9000c080041000034030501b001403406070f8841844e410844100c0e455011504000041014560036005450101082d8405401342001c40e0b40080d00d01c0c001070255144641d95505c03004011070740c1005140035100c0080c1255560b603034401c2d180c0c81c00000035110303608060501048a10a0030300003055881000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 476980917 1250 476979667 476979677
    0x1031506060c0206090f0a090e0c0306130803040813030507060915080408190201020d060906081204210303200d0f0b0303122d0403032f0a050405062101080d 69
    0x84140400160200b511b42903580f00b594680d000078212031512a1a000214440103840b1408000e000c0504000000b4101c03e27880a001c0d100c000000c0d482c80c11643e11642c041c0d056030b00e88411603060004005240c1004040c1e01c039541020408036040600c03c8100c5200e03030f41003440034108540480d41070300c040c1c900030078480d0300b07000c2d80d01251141c0411100f0f10341c0c0c80c4001070404850005440540d01c4a5000e00c0e201640c85500380214034090000c07144030042d00d0142e43c502460700210b02c40040b03000003400303403c410b02d070001c40405200340c00829144280b00019081d24100c075801260650104d040b0b040d00c1d503e408220700701e454141c00790220414000f070146040c01000402440c041c04010800603e0404981c8040720125102c05405203c2401c500c0086040ca081e25000d0120342c0c0304d0480c00407110917072110000200b810b00c80c11400c0da650713400075620f4040c84032041da06030007039400c159800f02c408103194000c45400300320745d0840850702d00f0046003a42d90340011501c45003c51030040001d6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 476982167 1250 476980917 476980927
    0x110607030f1412041a0106081501140f0a03050a0606170c03040f05030c010506010e0a051c031e020303040c05090108100e190f0515070509090411060301031506060c0206 74
    0x15019851180910b4403062840c0d29202c102045001d03d84000c031001c032400c0701d0000404250080240c50709000d400c5038101500d01c0c3c1400f0190a0502c0c0d10340d04c2c02410414408002030b10b41c00d26000b90317a0b20010034194140c0368a5890700140180c10226903948106140403030000c0c0a03807290511880c84e00d4900a8843d103615580500c08542d4002041903c00240f82c0c1030f10350004c1c00030801000e00c0c500000c0001441d00b0030800050030180c40520340c0348a2300e0640740500c00c07170303494000c450703c00304110944907404600c9181c240c80c00395040c041401099281003200c1c1c242e03a000b00086204d40d2240001c40001d54503181040348a440a0240d80311303640c040306861003240d05a0340a0354002c00d281d0212416125040c141e03200c106040803084031945803c40c0d5840030000c04010b840c81c109010021a02c15151400008096000d03241c042c40c8641070001c045418400d21103211110860007401e190350ba9a164100701001300c0128040056551905000103880751103502c81004250780209039038a00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 476983417 1250 476982167 476982197
    0x708160e060a111c091707030206070302070305062802090f0306011e290a123305061801030f050411010210020c0606010f0509040614030c03031c050717010305070311060703 76
    0x401104806c0542e14462040c000c00075039118800740540a11a5000340100782c25881c00368101080030b40003040d04860501314082c080c1c2800711104000d031070b0001c016140c504150028110500360040710f505800b80600108000400031101c040b024290242d040315544d40d80e4950214032468075900a404480901004030519480c004000300c3d01e4500c1e0144d44e01c45900c09a804070b07110620f2600d214400c0340141c44201c0480e054450b5045090003058191a00d030401054883c81072500e400d2400c3e20449801d113107a0b01940c02040306001c2124100a0351415180a22404025920142c0544038480b80d0510001c0140200e441000441001e0302c800e80b105c20055840b4000c0003059001e11800388030103002e940b00c40c8a480000c102c0340030160f045604000915007800c1d01c1e1a8990301a41040082c4c0c52007031414002a000c1c5004640c0000c0c807075503401022200d0100588011510301b040100000c00c0c4a8002241002c1c0c0380100c14000901464000b00a00e44c4544180100130484844102c482 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 476984667 1250 476983417 476983439
    0xf060507020c012f0a0c0f1401020a17090a0b0301090207021801150f0c0506280603020a0e06030109140607031802221508030c0f01050708160e060a111c09 68
    0x961301610032682100495951804c1000c07841d0801e20a07142c00000c20410320b40460701c800c2c07620764280060440d40009881e80b064042403c24040000c20340094600095212215840b000740600d03501203450b56110b900820207940034540907807144041c641d89110440005075150304035000030035011003000c038508060710005050580c40c0305215807207100c030700800c100380090781c8146540c1c40d00b58884051051003031810706582900c1d50840385803100c20710042c2c5419411806403000604821682ea6440002074054019124001e007075828801d003a110422380000c445004003100d84007804040c4406440300700c80112402c010f0743c03013241c80c01c04542444401c0c88503c0401e61040000c541c200e20308101c002d030360040c0c1d404024650300c000f0b030744018080140711514540407640001d000343e041000380201030301d2000c1c01040180b100341044842080c02882c181c0301d20b6902a285076151028120040c1101021401407101c0d4010380300d40300710706102c61144130700e0716540c1e8440c03154042c1009080c400d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 476985917 1250 476984667 476984747
    0x90f03030f14191e090b0d0b03032109160605030405010f05180f0607140f07021003020301081009170702030a020d3507110d0f060507020c01 62
    0x2081c4040101c8561080912000822450708483c1154150500e18400100304212050101010000746861182256441620001210f29848a80307484403800b41c2c8a000610392452107030707030520002561b104d00900c01c80a10f4112012100c9001c2144e40f08103e107074482580c0802a040108884030600c0318501843c060341d005030064000180040304a142d40c0100c03101503840f030a110303035004004074400100b003000707433024184031010f00f85a06010101600d15a6a0038000034842c0010038100050040340c0c09551f50144c0092640c4201200e20801600940c0280905100d6010300c00104c10100040d01800400542c481d0402d100c40c007640b0b040300c15542000c0c1d4101d03071600440d80704034096a1007240110074503000b03920400030980e603a60910307543c1c1a0400780303806184244800001c0242c00c1e0f01511002034002921050005243c0c000510701002d00600616400020281c841441916406503104100070380031610110764040066a41603412110315030b091070301b80c000840009c001d410f201 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 476987167 1250 476985917 476985947
    0x1504060c05090301050c0c010b030c03061b12010b040306110702010e0108060609090c03060f01211104081906060b161104060815061008060d14030421020f01090f0303 73
    0x107400c0402d580006403d5400c1503d181050344408a4107102c0c2447c01e214848a01500f01c0003010411400e001094031884020b0031001e0588c0e00c10700d15100d42d40008100ca80b100c9001a90a51a68403224492144e0300170740010358900e4685200642a00f00c090101c070030762a0142c44064151140000440d004900106881d40082c4140000f0300640c40383c5444078010701c3d9142d000ca40f00c0c5851414407030105070a01d1040c5c10401c0c044d901e44011200800c221a010320102800b1400c01ca40c4010000750b88115480300103076202c1c000c030260b2140d502400030642c0314170501c01030260784c0d51654411003034003c00410901841841110b000060303240d030310401024601610204000d40e440070003508101600d01c02c40b2001c01200100281071a207640707407040014490504910505046002c0741401c0300c0300f14018424100410780120700c5c94100290750003000c001f0f11204a0f203101c22038800041d507250108038000e580192140300c0c06c0d030003200c81074292405171244034401c81c42c544084400108140c0d03a1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 476988417 1250 476987167 476987177
    0x100902060913060311060f040303050306041b0203091014180a0915031b0311190503100f0b0d0215031302041d0f120301061107171e1504060c 62
    0x14201c0c64540c12034941186400980014156255007400303168011401c401510a040800c100070f200d00b80002a60b0503650103182541d166500c0c00c01040040c560341340406100804180403c0b6069800001003660810950b241d4403503030b102c8141035849050102e0000740800d0180901028030003079042c0c1a403a408010003206d84c15503500100b00885111100d0f103e28406400350510030700409803145180b50b000740e407041003154910b444050386004481201403040c001310711076080c0e0108115941018000003400d5890300e14030322049a0007000c03164090401d03035041c8202440c1e40c0c038003070300b005607200d401401111180c140c400c030641c0c00c1d0b48005c0040d441346082520314000740e1500d105109660b6510380c0c1d13503910b0001906d82c03285401f01c0c03c0d0300c0964541c4088810411800d502e01682d045840c80d040c510342c4104031100290400596030020302034040d1000d405d014001c1c0000d001100688801c4c000300b11f4060804c0c00540340c240104120b00d64200b6040894000740040d881030103589072074904 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 476989667 1250 476988417 476988427
    0x50106031704080d110a030507051c0f031a0603060118121b1509140310050a060e01080303011a0a0309060c0e01020c04020702090406021b0a030c0308010e040510090206 74
    0x3450801da00a001c0601e2965000c2400e1041c25020042030110302c2e114203148503081d900c0c4265590320000751b42e006041200206040c002c1040800142030000d110003908100d0205045008000306182d0b4030f070000207800d0200d22041030498402c9072004041c050302031803030b561b1218015100b11032100148203950103080d00024a071141240b448a91030b100d400003071181d1980b0101a4009612074010305240810448841200c82d008130f44034049645008a201624003018006400d000b4082c1b42002c11508000030400800d045070b2149041d5641e03850728217000d98841002c50b070b90b03001c01d019484074000346091030740da0384030302c50702601480403030780f4000c590340381321303070356902c01d40b00c1c0e1060103c045034101480422641c2c040c0604c083c1050190b800718104190741e00003640c0321030040c1029001d00c0e8009103248424010b041800080348402e41201c02496407440d0090580c1c035041400c0e00000c652000100d1140c05030454107003d5600440100050a4034990b5100200700d144c604a80c04882042 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 476990917 1250 476989667 476989673
    0x801230918070b0c150105030c0f22020304060c0509131a0a0303020307060c020105061e0607020402030f15010f0507030e0d05070b040f0b09011707050c01090b0612010e120705010603 80
    0x70b03200103000c1031400552030344a0f01c2d601610701040c2264484031420f040c0014400707628006100c402000040f101c0c219071a1801012038803107080320b105210651000c608000b91401c0c2600218051440b84034104220102c0c424111440e0140c1250554070400c1148601141102c541081e640e541014114540e0001c08000003201041c0681c0300f1005600081040018811948200802d04440d40003d005516140c00003581c4a095018441d10035403103c8400b0501d515a002980d04003a8003030801c41d42c0b41801c402ca442c2040d42116481c4860001124540c801c2d4800ca0f072690000f07505071569420101550b40680d865540c4111030b0307401414013030300c14001c034104124040c002c0910b0101c00f9a2a41081c080c030364450055004100415010841e03d04c041e40c0c402d11040c40e03000c8034007488059880e00c1f03070129498490400b40c026150300340b081802c1444803494402c0d01075101101c0c00000c407091580743d5820b95a2000b00c03141160051036200701401040310040480b24481c000004019859903 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 476992167 1250 476990917 476990923
    0x50f061e0415020d0507080f07050a2f0703021302040303172a0d0c0e030d03051b0a050301060e0d020904030f020a020303030108010e19202106070801230918 69
    0x15003800380190701c4005100006e500500c0440d004440c0c00794607401c0e46000c10b00580a4442e0005120411100a10f1080001e1505911112204441407243e03000009211066900c02003400164840c1d00600c824682452051088800312641502d0b4420f01503680b94009901c10001003080d51410070701e0000325540c40007807503e1304030a44070712206a200c000b544030b8002158040305410091010800c80e140c0943d030b00007203020681d4030b01e2801080715620312500140c80543c0720f20000215501080d1103404d6500003025506031105955801b061581280801180281c0c500c8d010b9045040c202c00716021a210f074160480080d0b0600480b092241607078042851544264041503403a55280e00743c4c00e11843c14054602c03080101403120407160711507110150b0b114941e07200003050107a81e095802c4940c40d070085201c1c022420250112180a22081d01751f10740804480c0c200c0022089800460940c44010880768181d07510071080c20165800401d110102c80058105090b082c211140080009410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 476993417 1250 476992167 476992177
    0x307030603050d11031b011b030f0b060a050a0806040b06040906030212030304051b1528051c05040812010f0602060f01140f01120f09050f061e041502 66
    0x15900010001c0c9541451801c0c0310820220000700304034051952000680001542d00b041440c1503503415020400f07403070724010074040400c121080d0a0100c49005590154000c502c8044690014050740003503c0c02c100d654071131050005c0100d04140684580350744554480d40e404000684005040c0304000b0002c2ca80d07030441e9218150482c3c440c04148114101540144900090900254207605146d80d445480f842c2c00900642d0b01a1080341c0c0d80d003070703607148110184c0c1d4101c111040b90b40d813221442015545c0306150002031300b106825445620142c8100c007124201078400d40b80070200945074020314007410307001c0d00a03101d01c4400d210524940060f810140d00074014052440040d5241140190401d24010f01010750f002700c10004101c506802e104010ba019811039424a00c0042040140e403070400741c50300c80445030300e1310707a1a003140d9200c1d60188601a00542c00c45208242c506a11a0b451400312040310040280d07012402200841407007040d001449001c0103224295203182c110121303048 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 476994667 1250 476993417 476993431
    0x70e0108030405031908041e050d12020f0604020109090c03020705010e0327062506051005010905220e03071e061407020606190e180105010617280203 66
    0x501046a468201702c550079904420900c8001241c0c40d40714804140144e11030703044081c460814590007014101c01681c091304c00244161684412400c22081e5169010781c100e02510a003601d41d207428800040d01441503038140d6608500600b0400c480b0007400c1004a1402816020300c6104000351081c061003044c140d44000940e00d90b070701441c1030007150081e070544500b00e807103000002e0656182c0e803048070302540040c0314001c0840c0483c255010701c02d0400a01403c40c524140a0205030002c16030040111802640c03415040c039110710410013680300340300005200310000703045d000880340d05800001e02c101110b016030f82082030a8644201d14022802d49030400059888200100030b078074032480c4140a074168000c01c00745003401000e51780e000d0250200348299a00f02014000c4466401c0c01005411040c01e81600703418607100d002e04102c04c8a014140340d50800001082240c40b5006030004017500140c2041151036540f8080c04c12040c4032000c0320060300040080f41010030a000842c000c540c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 476995917 1250 476994667 476994673
    0x60d110c0d0e060f0d02090109090f050108011d0c0d0519111e03101509090305090f101d060415020a050c0301051006081f03050f01061d0414070e0108 66
    0x705800500003081401d01d980f1510051282c5826100460151608500300e00070041c0d603081280c0058903c064030303501c0302c4921400c1000d500c1b40360030b007504030078120703484107000f881803142590750380051051000c612015940050004440c0381381c01d50a0842141c020020340d480c50a502480100c0e03c0c1c883c41003038a650381c580340c140d034103414241002c003425582c0c81101c0301c42000000000342c407602c0801300311003401e80f1252103000305086040414010950100c00704000754180c03501401c990003030200300d80b0a0403040841011420314007181200b03110360380d1740c0400d05d9541c1c4041c0300d40700c10281005604840148004204039a0781340000300050701b150020084c20744185400f43c50729401c400744600990508c42400004484507000300e06588050405003200e0703a41c1c580e011484050031225404c100d80003c3e0003c240400403a103800c02201610090201c541c0742c0a402080d5010190002c1c26844540001000b04880020320398401d581e040c103079451180d594061041400f800c2c4c0106625030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 476997167 1250 476995917 476995933
    0x1c0e070303020c0904030801140a17010906050a0603110907020a05060a1a03070b03150301090503040303080403081f030611160c050111061902071502030a0204090c0509030c060d110c 80
    0x54040207503450340d02007150882400d10b86a50000c01d0014107209002d460040740400c449030303030b41d010002000341c2000311072f1060078042014914085c103070f440000d40c4e11a00d0000440c0d07854846024610a4a0700700802602e458114800d0013069000100101c08500461035014009101400781a020b405204404035003060072078140c100ba0442d500145111f903000c2c0800b0440386074a44241c03540040c1074400054081001c40101c0e015040e140c02c000d15078000002c001c41099004000a80140c1c02540c41004c1c0e640c075124100091200c1c0c50600724800d01e40c4104100103441c81d0084022243e04d5462207080602509000302c09012010007103414920110003031295582c0200313080d100b800c10500406039401d0804403a4001c1e0058200900300c02e800040c0c3c00103121800c180c11211010100e411960392800b9010301d8002c0d08503000d48100e560400380100c1090b4490070a03600c038100e00601411000c8030030020003c0651200e65440d61154649070000e49091713402000d4101d114080010308082 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 476998417 1250 476997167 476997173
    0xe1014120a1b0e0a060e0105070510020301150c1a1003080a020a02010311070f02090402040e0f0307110109060203090904170403031701050927070b04141002071a1c0e0703 75
    0xd941c007254680b041122588411020740c0d50310220000f1211a41804803028254000480745803040110140042c402c001008151200c070342d00a60403280314084459400c17903008012203030175001c10b01c01b400424500c14060000311020b1807094100c0820060480402d41da69100341c402c1c0c00540307120026800140b044c1c420740d40c01d4010240031012940545182a441e0f54441008441f1210082d00464440000408544842e0300c542020070804040305c98144c14a203446690380e02c40032007190303d4a0146050b4065501544044054400540145041c207028209201d02414001c1060711210500040540091803040091019501a40c0c8500514840300311840a440040e4419809203000c4000c0101d050341500c01e2000010088240c3c0030088160160107203420900e4000040c401e0001070300080340284811351485503441070b5442a50354640d0a0145d0720303840140300c0c022044d01841c0d100c0c001c1c0c483c042c1c0200f80c2a41d020302c107003d41e10b503159070100c02c841501004401c02e90040d0000d200b4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 476999667 1250 476998417 476998451
    0x30501021908090a060e0309040516090b03010b041202150406020a0308061c02010f020321010501020607020d0e010c150612021302090d0602091206040c14010e1014120a 74
    0x3100d2942420b8445082068410ba0796102a0502800c07459903042005c0c0e000300140308441d64804000e20a2210b41072282d11824600c260408860200e01e03541303000078120f116542901d040700ea184000a091a151012203070719500f07000c108907030016050300401142d9455501a001401040d401840300d8039143c0340141245001500040c4108003208040442c0303920814200301043e42880d01614440040b0f10983c0307503024521030341c0c807072800b40c80647c0c041440209080707040300d009a00f159801c0c0c5442909988810405c8031407800510301054182540d40110004002c1501c2a4070300e210204408031440210f407040e400081c0350508103e2948154a130404030b080070740040c610300310700d4248510b00044480200d15001003855801141d82d12a550361116101c0c03090314008140c0305a4a824600362140700702a004a41443c4000136040d803495205204005150b00054060458051150b40a0310901403c00d05d0110440c0304000b005c100140c815541c0f4014451107001146000200c940090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 477000917 1250 476999667 476999707
    0xc0b0c04090b0f03030702010f09030c060c061d0703030e0604030b090307031404080303010e0a06121b08010b0a0905220323090105090d0602160c0f0b0903031206031603050102 77
    0x201c141055100e0314404d42d004821a515140e09007404001851072400c180c81440c10b40d071010b0104150480c1c0010340b42e0f000001103850030307c51032081014180c200f003091104202c1c08030700c40c0f45910002040c0000382c015400221a4080240090700745540c0f642c4258000e4011030300070036240c00105200042640003d403071500d0f400704618550809007005200c6030f69000500c500704200fa089030128180c5800c80e40b090014144036191404000c01c1400d020311000328802160504881c1104001401d00c010310030140b40039070042081d4205c89c0340030710002c05420081c1040142040510640240d82d5a8025100000c3d21946030300a241c0c0c0803201002c10000c2490903040c803100304001542090382c1c0b0000301c9265242c11210b070049903000d41015402400b4541c2c03032a591054419a0b0014081d002413400115240004012915900ca42c0c40e0b00b0907015140c0b09c15010380c802c1c410200c1412401c00043e501c640041c04407244c04000c1c40c80300000e5401c070352044ea03203654000762030325050025188181c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 477002167 1250 477000917 477000919
    0x1303020a0e0702060730140105060307210b0d0b01060306060f0503040f05010e1e01060f0b1207140f030a15060210020c01091406100614090f010c0b0c04090b 69
    0x11807515101c03a0194840500502da0400c00220b42d25015800c403c0e03603580a89880d90000400052041d403424000401c9400c06511128101100000e102d280c5502140c1c46489aa91a50003440782101905015103040e40000c1c103044c0c44034070010044d00c50b03810481c95a8064402403405524054015044070615000a0100105000350702140c68121003200d4109a01c142c807200494a9418a14010443c141492446004070825141030840300c600442100108030300800000350b842d1070760b0706001a9446004110003041c822546a04021041c0c143e000340d4a00300118008201000c9020342d500402c26040440408414842d034203a842c072030400d41454010040b08507608109000e50355841c0c000f1184105600050f004150710f2080d04146050340c2c1c0042e03a15441807280d80b9280e12a03804a0b41c8c1c2000d0750b0004000100c00344101010214110b440c800b15180180a8080c450342c1c01c140d80c6628103102c221440400040c0100780024402c0803213007602c0c2e882d50704103076812064484c409401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 477003417 1250 477002167 477002189
    0x4141801061208071a0906090c09090604240c17090a0209010b0f0c010603050a060507021209090403052a0c030a03200c0a0902031006090e1801111303020a 68
    0xb4000106420358540c1030907009032000ea200c0c521481c01c81c4015600301c904141c256504020b00c5008140080d410b401400c2c068292410b03180c0c0f4200b0f001030304001726112520383d8042400305004c0b404044503400b410109001c5181c00d00c56407244101071368a011104000904120300c011a0059001140340d00701c5401c0000d48400354140c0c0005410f0341041c014140c2081c000605805040208021503d070840203900a110a6a50f0308106890300c0b00a90300b9103501e410074000615440c80030800c94690b00889100390706101c003c1061040018000b00202e051000c10001800c1d03a4000e20f044400207440e001000c400b05140c40314641c14480d4107480340340203034003034611000081c1d0020a1000b00024540345035840030b04909610303140140344520560400c4205038045156406030b0021480f550140c1c01a0b0352050b6100404c42d4400c285104105c10b10740c1c800c0c0030400d8200c502505542c544048000410020740b0824030506c1c0c4e9008004502c10035040f480100110b04041c17440314000c1c800c1000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 477004667 1250 477003417 477003419
    0x1603080403140301080a1b080a0b01032003030d020a0905130e1e100e0a02120d030b0109031a0604060e010b120c0309060115090305100b01020f1b010c030507020414180106 75
    0x20b00f969103240190090070b1407420201c400540e1f440c00d4400c0001c1ca0b02d001100d01410385801c0141105600380010707200689d1141c1c41a0030811a26a0b0000040002c2d0003585031040c20101400250440355401d02002856070300002c0541d100c40b10a12a502906c00026140c5000030001c0d10b40700c2241e4030708803020a0f000300e0b1004507071b01083c84859407526081c0031801d02c01e00043c0724202161140c00030352114a1540700e9109841c0020040c1c0f2600c550344003000f885216400641d1289800e2100078014a020100180161001402c05800420241001c0f507000c5c1c5510140070000c0d0242c0004424082c0132076104818116803804c10380040003284202d00e14240040c0440e190601409002c860042c072a00121000348542e0300e030001590001c0c15542108840c46e240c8000c0c2494800c40341c018810b4001440c1d00c20300c082100f03003000b0080070441c0007032002240103560301c2c4881c0205409000b428072180d80580c843d400f83d405c035031500160642507840c1c40c60400608203e0b9007900102c0b070b032400340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 477005917 1250 477004667 477004679
    0x1c0c020a03052b02120610021203060d050312010611070609050604050f060705010c0302121e071b170c060106080903030f041e0f0c06020a03020304090507051603080403140301 77
    0x880d5000454894035803143c450702584210407015000001c1030700c5100041d6a01800f002240f0315020f07050072500c0c4103d81c00a40002c0703907240e2103804060070303914081000c50a01d00d082911204081e104900350303400c2c1a40404807c6031260241d00541c045045104513450502c000d1103410301601c25400d01080e07080c10716001c030b401e41c051030040900503181c0c0c041541090781c8840c1035401ca1a0300600074030540d0418480200a500311981d000c56256000b00440c0e418620143c181c84425008400b906895986200458485844081c41010b01c00c3e42c906c8140401d0950280ca04c50015065001d07aa94100501013031134000c05a11807010403030404c0c2404a25000881140c1c1c0200c0300c8484c0c00740e0b5440d5400c0ca40000da6903900c02c50004411a000401000781341c80d803001c982c502990525984a40d00c0704280e03100c04680030000e0050300b0820052044072002c2c1e0145410820900c0d21905011500010301c0c001450007409501064039041044201070b130000c0c070709481000d0341d6456070440d49000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 477007167 1250 477005917 477005927
    0x1303021c060f02130909060b1c05060a0b0d151808030f01060f1d011b050d11010b01050a081906030b0907050102010204120201030b0d0605070509010e09070c080c10021c0c020a03 78
    0x805101911600e56207044140191a04100000391004080d07859501040030271112141080200321000e0040200050021001d48030b00c00501c1e034080c20340c0044401c40d0391520071912000f140000d03007690b03a61700c2c0d00c08151030041050315a441840659601d0400440740d000100c0140e008000f0000242c02141441303900041c0460030817420070580c0910300d40340c00161072560700c945c0381c0e141c2c1200410390344040c480000760080b400403068840c1001907840d440304da0b0a941e0108041030114408229010002d0320075000264418100154166014101d600300804d8924a510642c0c1c00307003201060001e002010700010b03000304001d0000710b103028900400c10100301810303680641415030380ca03c5402e043e01c9010040b80303074640c80f0908012a1802040140060b0445400d0500040589900b0385990408694550003604c050700c0320200382909a0310b00ba031660190102c171003d07009150170503c0344c1e080781c0081c0003900c1c3e48410701058a11080350030b908440c20f1a820f00215440329464002081d000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 477008417 1250 477007167 477007169
    0x912020a0509090c041a01181a09010e120a03090b0a0207090e0f1c09300510090b0615120c030901060519030c080f10021303021c060f0213 61
    0x560300444903540c0c80f80c07060309018414101e5034000c0d0400259404190340084091420300090b2501c95014803407182c0055003004d90700458041c41c40342455032201490490150800150500d403184100000b50085003450090f9402d80c41c56510a071080b804160300002c2041c00790804036072240c102440d5400096079070145102d0f240480c0d6940c0703c0000c48a0341030290544040166088881e03c03000c14810014107d0f0000d0444005810700e680452080050702c3d40b107030303590140055040c990405071004114550b4126007103034a032003500d540d01c0c569041c50159001950060b0301c004030b185040e005114501083e10080100d80d0010012035426110340a95036400a0390495050303143da80d40e240c0c8500500580c0c00c52030703001500325032603001170302c0200828042d64400c5c6001c40c1c940d55500c010700e9440703591442d0940701c5d80000103880122155640900041c04054003080601ea641e0b1b0045405142d098041c00d102c003800c05039100c14007a00d40144120340c02413080841c42c12800000030210001c0e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 477009667 1250 477008417 477008419
    0x4260d0906060518150303040f0e070c0c0803040302091501020a030c030e06071b0501050408030f0d0902060304050114090303090a1103120a080417030601120b0d0606060c030912020a05 81
    0x80c5044203401e00c035550740100c001e460090040320003401e482c804030660b00000c0f200451080b83c00359000e009410040142d400b01c46c00c1c1d00f80640e02a040030003240603610700415000400507501c50003400708400011007002070540e10040d45c0d80d00e0035801800240e020080c43c1041c401c4444207072006590307000840c200c06030f4251401945450240c0740450b0b00010040416500c0340d4042801c000f440403500c649154900040b41d841681a0750303200660351030251340f003040d04c02d8000303200b0031340c00810354030050121340d801c00b030000b80c000040d90003e111600159003d403010303991130311528000c00e4003260442c0c1041c800340085081d4542007003400c0c1c0c3c498550380010140c000301421482c85860800451610400c030311142a00c80700030002c010301d00300c021070f41070325503ea6081411100310714a0003100d000c0d0700c1c183d680300d100040c1000d000e4041e01d02d4002240e0440904803606011407441c1c80b5080c064089070351907103103940c541e00b0024034560315504900d4480d644e288407200165a005011021244 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 477010917 1250 477009667 477009671
    0x10b1005042115060602060108120f1303080403080301060e041b03020913090303140f07080705030c0c0d030618050f0604090f1712090f0d11031c0504260d 68
    0x210341d4015054078002c000003040780304124250002180039402941c2a100f05a08681141e0380c0c5a4880c1d980300050040c2075203100c41080807064100c00c580c014110f00410b42c0014030350076900e503240c584aa119500030b40b1400c00100040c0120303680140810640c03c400c540c02c4c000701c20310b4910300100c800008110428582c1c002a0500f6603150004404030322801000100500000381c1000b501402c1246d0240d40301308254400101c4440c50031020a005000c1682d49040715034070010252050352000e00f800c6842c1c0d80c10300514100c2c00f41004148860030003036070003141040c0703005a9240211040501100b03001c0c140382c100040444010500c035480001118041455200d60912010301079410302c010300384486020400b41c02c006944000c00f0340344004001c0340750541d2b0300c40b12251100c4158104034100d80203201d0300910144075035005810740c1c042d0307400c2d649000407480f200300383d5140602c0500d000b19210400c04c400e0000e44003101c1c0b910600840c8a1200c1d03c00c1c0d800c01c0346144213580c0420100c0e5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 477012167 1250 477010917 477010949
    0x3040308162d1b1407061d0108040f240507050c030f160c09020a08060d0308060d080c0312040c090207030504060c050304030b070206060306180c01050f12040c0602010b100504 77
    0x51140d83d40d00c5540260201c0c01c0905400d500f08140a070142e6408600c1910400b03100007101449640002c40020310320a001901c01c4504004580c001400780094034110250740030500032850300c80f4015040344401c0403041d012500701d030343c400c2a10001010207041c040c061007107140040000c800c40c0c0310307041c0a0030701e0b40e52038201104501943c400c080010b4030000da80c90010454210030360060503180c0d116121f01140d591400c040003039040d00810f00900280c90710001c80e80c14284121068401c0d4800c503101c90a116511850034a5900030f40e41d040792113011401800213006240c0c0f80b08004c0d00e158071040d407400c00e25480c050450f2049115030b01c200312042d10244140103082c4140d8014680c8600d04c100c07a030504030030003036a0340400c0d1402803090068101150759101001030118842800801901803800c519005441c1c3d90048040c480c5552000c010800c805220004003d10441c4114050280300382044e40081c21281c1c01001a801040c0b40c0006406458000c81a24129400180f4a960b49 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 477013417 1250 477012167 477012257
    0xa031107060e0a05101b030203271e0304062304080105040605012409090f0e0106030f23121c06030602030108120f03040b1008030304030816 62
    0x29128140000d04050301c0c00c42c048262840200d1044000d81c09141154041411002c08200300c4200c0821162552400740b00610301034005e40185078000b0a110149200031080c12420000c05c1402601404503000498603070750005408030506040a01d9000031801c1070b0078040b000c4c2201c15100442101c40c1c0b00403000e9000f26010b001150050701c1044000d10850500d460400d010740000c2c05042180480c01800320006800b8800085c0e02c8c500070354601c210145030902d00c034018204061040e2001d6100d07501e85400c0b400c24003035400194030884032500d1010050400c00ca07403001c4081c8085094101c8068141c000c040040c4002c0b891358070354440c1e030703542d6a4840e48074859407508001a0406091803800000e2000e80d60241d0304a507808025601c08421618a40c0f40d81d209001856204e00824004a00401c0c40c88880355441034044030694503071612070000c40e24503001150118000ba090308101320040a0032026040d400c4000d051001040710181006141300040c014000c02c00e8070324001c1c030049 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 477014667 1250 477013417 477013451
    0xf18020303030403140f07120801050102151b0c1903020d0203030f0402010e1f03061503090314090a05030703050309031c020607030903021c03020405040e12071205250b0c03010b0a03 80
    0x450b5100c002e850351f0315200c601d08103204c081010703110404281eaa07000001d05500120740e21000d01c00000e54103a80d80d45105a12a24a1104a009418081c2800504d4200004110980b014000010080c89007102842d00902c3c200e8503106010464005006010040400b4000f064019509003840030036031f600741010400c10280036040c4a0441e06140400b41e500b60540d200509488803e4508009508044400e400750740c2c4041c0010000381401e002045c00004100290500050080c030362820280e039030000a141404940003aa0903800004d40e260141c07608011461419500904041c4000000c02010391030301001011081410785800f604810580f081c040078801800720280c6c8507440514900c004e001750070a0088501480c6000e00d04600a180090380442d8504500c114528001007035039494034102240c5420350500500b4000300992007488030001020f003444095080b03508519040c40001c000002d03040d4500141c0401c014410740864800712000c604041c1030200b0305411603804120 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 477015917 1250 477014667 477014677
    0x6140901061b062408060702030d09061b0810050d1e060b09010609050103050109050606161104050c2a060c090102070b0c010204060f0302030c070f02180405010f1802030303040314 79
    0x84598584030b41d03401150380c14030740030600035042c4c119010030645030429076030703101c0f01520790b0405603209100301c1d0301003003042d0814515a48581000304001028507000d042c84048481040701080c0f81070108004841201a80300090071f00f144c891038484030700e483c0c0c0741400c44200f00c0039262500441c069024060241c2004402d80c03409404800103694a44004040d910540500c500190424000107001012801403034094480100030914144011004449490300000c0c01c43e26200c0c2c1034021881070740e0b80c1c82101d03c1688045103882d87c40f07041030a001540c03160f2450095440300508119011002c0005429078401d084140c070a030748040c0c903001070303161800a50020300c00813800101e0641814040d009407044420300e4940c445c0c12081c0301c100390b0581c00700700e81e82002d1070002e200040100702c09410307403108140086c0c05101c040001c0700a034004000c2c12034082c0e0701a910307403240e001c2030f00286c803500d812040160750034116442d883d8002a282c0c44090030280407c130910030448080b91503031080390 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 477017167 1250 477015917 477015923
    0x30503060405042402030a0f02580e031602010e0604030f05010c0206060a0b0a05130e070309031b020a0b090f19030c053001061a0c0106140901061b 65
    0x401840491513104040c0d40220741c42c3c01224104906188072142c58000c1c5c03864403103802402c01000c480704000d00c06461609207002c2040910320200029151070302c10480c856014481080c1c80a894251802c054500050440d010f0354010800418182e00c040248144141c1c2443c0007982c00c18070350f0004465005603000501b124205003494010800154000d001d1806550251503495032400c1c10450302e28014450b1613a40b08003080a000c50038800c00041111150b281100706011740c44010500c4042000c44092010075aa251010207040d0060002501ca08050070904010320041d07003c243c1d5982103105031400500003150325011507481082d5142c0c82c040180036040040012240e8486060b00e07440240c41d4242c6411003c070301c0d030034010740c1c42501c40c0d405a04421002105001d603d50480d1802c0311a0140d5038581c00400e1048110b0543c0340c40e00c13284600c0507110000041c0603801c40381203a000094541040e8610a015216440d6050440d80d6505218551810781032144ea030f8103121210003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 477018417 1250 477017167 477017213
    0xc040b0a051203091207120314130303020f060901061215141f0515070b1305031303060501080703030e0d05070506030a0f0b01020f100c020307050601270903050306040504 75
    0x2100b003007070001014000c504d5003141e10601c9000e110003820344544d600e0017044859045120f03540e001c6030241403000032213417001c2446882d00800c84417100743d03c60b658108500681102100c842c40583c204216900b1094040080041c40d15166030301c10004941c131030041482d0450854540e46500319481120bc01c0000020174006141096100404a44441580003c0e64016802140502b0012b03403003083c031507101d003010f4078201c16615019000d41d00100031402404240081000198090000d400c5d81c0032880c03105034040f8250300c1c0c10b90903120144c02034001580075a50800119038031484825a80f0400d03924a41c001506040190a101e8240c01840e082000001404101901680541c03c4210005002c01042c0810001242c54102410b1000d02030790080ea003408503003501e54400910b15500c9e00459140c46804c0d90303007600b802d000340d0083c1401d116201d0366281121000f0b51104408240f84820090451182e9001d1300034000a018180030700d0b9907900080070810300a900340c80940c034003950 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 477019667 1250 477018417 477018439
    0xf150a0803040f0510170420040c05190c02060d05041505010f0512150115030204080f07030201110631060207060f060b0f07060218060c06101203020c040b0a05 70
    0x41085043e1032040314003440041d03c441000604c2408102c4440903010820741c51512141c40702c141d520080c480c1740e480c44680c6014281d09565520070350154080700e4540d10703224440c0200340d401031600d206650b814031102070000d00c0160b0342c08080303c0500c240e4060000d2181c5490600041c40b070344c002c0003980311a191900208800d880c4014103000ca407070848958102603000d00c0e20507220400720304d4201689101d40c006000041802214100d00e000720719006080594401d03c0034170301100c1100608041d000301b6018415541d0141c80041808403660040415040200080900140c11600305284070039001e010500207c140c20090442038000c4c46c20340d00c0d010796061040040c0b03402d52042d01490325003c400035240d65600c06445104200000301740c28441c0d03540700d2102941c410040104030342c040c42c1c4564a1595040080c1040002d80c0d001803e00e4503010402e407042c01c07241c0e0000d515100079044050002940040d03481e070716010555010131035404801c003040b400251600f1440d8403101d02c42c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 477020917 1250 477019667 477019679
    0x1e110604080702031204140f15280504030b070f02150c0307080f0106020a150f06171b0916090306020c030a081303090b031008010c05210f150a080304 66
    0x3810800d07008070305440a00f07038503034030304955840303a0310941603218030041ca9105146402c0c8c0c0d100e240c860000e44a041e0640ca4242c52502c04d80c025000383c040300c401d00007814032000300049052400030040c1040c503d01415522001a0704c0d0008100d54108807140401040e140d1003441103a007844c46000040c1c1240c1020441d054803900219201c1000030216030016450081c41d0701414121041d9030080d00c2c44442d03a8441008604048804070005911995800c1d240c40003480b0700d0008055054400001c9000490034900f89048000c3c0c0780300d104000c540034403442d03642288441e00545045c420005c1840541d00070b0700c0d203802030351014100c10b2001c03d1314000300c100803000785181c040a584011303c0b0355419840104920225002800040484001f400000c034001d000b144c01883c04503801c081103035038000d0942991002600c60340054408070302400f01348882c40c0d511804103841e0141528030b01c4c00c4c0c8500041c0000c028210000100c030b444020415850b800c0c4554050901c001c00d8030741c2c039601ca403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 477022167 1250 477020917 477020933
    0xa032c061b01050a05180703082d07084909020306191508211306020c010f0804020d110103090602030a05040c050d030e130f020304030c0c05060a1e110604 68
    0x44801000c110809441b6428120100d541401e0b80c1c0d021100904048035915a0446003d03001c2c0c4130a000c43c26842c20402041c0c0c041c0103081005d1007a034102d5030304d511158540c24a01c1d100c40c0410040c031b100811102d00800c580e102414004020317010810518155581c00b0080c00021b840a505805000203101c1c40324524104c00b000d100d00d40c0001c0c8050b5219a4042e680c4030003502c80c50859410210b192190325104008601c42c000700200010b0034454046144101064950302c1800546d210341c40c00d280658002c0e000910002050500350400c1c0341540124400d008aa08001e140d110408440c02c41607000340d0244900513005030003103459213000580f0704018070003501c003982c02414038400000c2525052002e4513030f0035415655502c100c80440113001701c030301800c66404800ca4a501d4110703e250032a2000c2d40c072031030007a901c4080c4000c01e401d0001e0591180d400541c01440204018410a600500300c011b1312045200c0c40000201c1031142250041c600c0700c40201c550040e003051200744203081d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 477023417 1250 477022167 477022171
    0x303060e0f010503010b0105070503070b060d1b0e0a06051f1209050f0c040e0316020109171c0f090b070f02090f0a15030210111e0a032c061b01050a05 66
    0x960081114000000c01508c00f400380d400000c01303540c001c100f8600003441d4004240e070001c1c1d010b0a5525030726900c0ea180c1c03180e4840f8281c00c07481030081d0310040003068038010190b60050007482003000340c54100030105008082145043d18003100d80f586800701d15104000340483c40040e94820800710195103041da446071300700505000c007485108000d684074a0107200300128403008400851030481c00c800c0309182d02d42071b0300c016410f20515440000c0d99041d54a80c41188140c1040070303003c60910410281882e05042d84000100965640031488081d003040e4a8819039488091283d03c458180c40c00700380108240d10025000220300c03061154101c8404011070242501c6c0c00300703002c0c0c0481c001941220380355500c406036000c940740302400c50940c00350703140c50b420003841070a45655100c030003540451200000f000400720703801040c0031001e03d0b074070001c0c03d02a03015910f500300d158036900344502c5d0000c1903c18858841e07500054070049481d00705845800d132105100003440149000d0340414002c2800f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 477024667 1250 477023417 477023419
    0x30b010806030318100c020d082119020903071502010c27030210020c1801061b0c06080915010308030a0b0301150915030c0e07270b070303060e0f0105 66
    0x481020079200d16000c03055403134000c42e030891030303070710000b401d00308410005012204403c1c003100c031076000003686030b40e515400400e009a84490b030325240e00c1e4102030443d1021080c41c040d660b0a009029403440352804501c4801c0e28640096190a12400000e08000e40d0758005c80e1007603506120301e0450754064010313034076081c034a448010601c507042e0341d0940014410441007817000c3d0449010b10052902412020651061b841140e20708502c02000c00c0c800c0070318400d5070f00c008010308010081d4640c0166082c5404054040754075000c100380d46ca124400140b40a90000e000712a000940365403410010300c10914009403412145507034a00304010141c1c03045e80c0c1c100d0210b080441c05149800c0501030b20420303008031204114190302e000c00c000002d102884101d800041014800004906103a42d840301515511644040ca410405806049007030700510b104000c000d0896440b0001c1212241402100d4500003299070700d4004d031400324004e001030b820108080f00c1c0182031004083c61440d0007816680 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 477025917 1250 477024667 477024677
    0xf060705070f0503030a1209080f21182a031f11040e0a0c11010e010b0f010801060c031202120f0613110702151603050c21190207090507030b01 63
    0x40c4070804e25450b880360095039404225a0750b8024141c1000b03501413580785001d00c10309400d0844902c0c06d8a80c1d644042c101c080c070b01281030301c880301407000c030f400864000c03840b141003880498499042ca91aa034a80c112038140391203895020300c40400070300c415000303480010b050750300c03240b000c030f5112003460b0b246c580e641c038020310345545a240b05402c0c8007110b080d0f46905107001555640c1190f0318000d001071250207020400380348540c0030040310074001c511000c002c000002c60900f020405002d00d20880d1124a41001000c0004100302d507000000340303001e59014071341041e6408030f0448802c00380c45080b4500c0500100c000c00c00c200c84440070b212a018010403a41068010000d81002303043c1c503142001500c180350100b04550051a18203440c1640d910710700d0119041c0700300b00303811000e55811701d40700364045180000e448101600c2402101c80807081d100c014091001c41d51003283c520300440640c1f00085902d10700710032246000700321020040c12000024062854141d90041c0908003112a030345c00700d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 477027167 1250 477025917 477025919
    0x30702070f0302090c0a0905062d0304020f0108040807080a090806090a080a0c030903060501080105040c0f0e010e0a18140f150c0714070b07150507080a0b0f060705070f 74
    0x540d00008800803660002c04204264a07170f1001d00031540c0c4901600c1c0180610f203180003076552036820282414188169840c050180e80100318600139400300403c841100c0c080040000507035405c9015848240c00b8a440c7c8040d6445162006c194420403101a0001a011401c0305142d68000c000d0020303182d5810583d60309484017140c1c00e0341d40c074070003400812100782881402c1345188145150340005001e4a445800c1c036540e42c4504088900c02c0e0006002d6944900410040c4884e54828034020076010302d1a2901c14501000804084010f0144014104000020500444894004014a0608038040204140d2034504281e440d004004c0540440c00381c030702c0308010085c02140c0c40c5400d01404100002c0c90351009403000003507105003412254100520800c00f144031007003211102030611880002c3d502c0030981807142910045242603000c0c2410f1a0801c49400e52004d0201d80050170481c010900140003030006605502c0340032003a40010000c220b10081c0000007c000d1304943d50346003003046107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 477028417 1250 477027167 477027179
    0x11060f070807111f0819050a02040f0503070e0c07030c1203061404090209040807020a0b0a0509031203010305100e0309100e0f0904030801230d030c0302060105010201150e090a080c0303070207 84
    0x200003a038800400d02c000100041300560b0165040c664804c203168000043c0714a04411075049036030036681501c84640c0414148100904541980302a180c22401040003030702c1e103103000e038080750010b04009100102040310303004c144c01030508081882c0e11502c521359040314100020014402c92203180d040208241a1020a00701031191403005500941200b48568a0b51606080342e403000c1805c0fa04988240c1c40091410103050203003110002940d00c640d5039901e041d08042c5400007841c20201174a00c200010000908001000c1c9400040b408012a1034003179810028118000c0c41c4010341c1003da64110072492503404251143e80100840e00002d140900c1030a0102c403110071900100271a00c03081c018050310200e9030010755400c201d800364039040680314021030314a00c6102c0d011070100b00e040079031408042d0144200c0d03014080a200030010340d08142c103c0101c0207aa803003281185002c00300481c80e2200c041c010207051035044105950b55500554030640c0e264000c503400c00041c040c00c080481e01e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 477029667 1250 477028417 477028429
    0x7170307080c1614191b060201060f1e0e0c0a09080109030203160c091b030f051611070807030f020910050303250f05060702011406060711060f07080711 67
    0xc10716000850f07495000c42940c901c03003003407030302401003c040c0300f580034001240c0d031405141418103200f0369180390316404010355045c001209402c51015a41051030078080700c6401d1007070340100c840d202001c2c2072a084101c0c00c1000300000740c21603120030b10000c1c00c2040c9108240300512104401d0350384d4503005940d03802528200d894416009005030030400c102c1103d03402402304001158060b402e50a501c1c0d94031003400d012141d68440d60b40c0c0b42c003220584c0010103901889191100401200180011301d000a4030048041d02c1c0c40c0682c00b40708040012810541081028070041d140f041d0403a41510b440c4d0070191140015040124400d000d060300042a41f901c0d11000000c90740050000c509148400c40c0680380c2d0300700002007118aa01e56005500800c000e8031200c0041406080074210909218100a013502c065020081c541210b00c000c0c0700c42c5859030803ca45807a07800c1004110300c402c840002400c0d03071091aa0745440c503900483d1840520520304001c1003101d1144240900400f80d04041c051 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 477030917 1250 477029667 477029677
    0x90a0312141204031404181b0f020705060a02070b120103061b05040902070206070b0a1d1b0909010b0a03120e040b060304020904080408010f091a0f1b07170307080c 72
    0x2c8419090003050000380121050307040b07100225010b9040540790805c01200090303980302d85201d87d403181d0034a00c1c410100d02c0400c07070b004c0310b528144841404c0000040e5503070046204481c02000300044160340144203201d41000b9000d031010031a514000803801c00084282030200350f40c00340c0780c071205554101c22682d03102e50783d285a88505040c03138030384a0100003d400800c0142e82050b420001e0030006042e800340140700d60f0040c00009664142e5158180807003d2260003030055600100100c40b07240041024040707000001c44031a207080e13881003101400744c240c40c1030280d0042c0e203448011041214031940302e03a00300c03a5070380c651802d09498ad08002c2078600601110342c0008040000c00c0c0941090020503610601900480d0b10f0a40c2e40c0601c1406c554681d50a02d9526544a41c0e6000300031016034070f86554040c000e580360140c01c01412508a10f40c000d003c00e13141840043e250320302c00d580a400d5828054101c00d4a00c061a00d0007060100c6602c207d030010005a004000203088a01c0d1900b510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 477032167 1250 477030917 477030937
    0x80d031b05030615030705030a1a0112020705031e041d010f090e0109020307090b090f04021f1103040f030b0604060b040603020703090f330507030311090a031214 71
    0x85051021081541e46600281c44541c020381603214813400701e0700610042d4091090340c0d4409580746000c011442c226117401c50000906819800d40b065160703801204022501d0b1020f0005a0794111850074502d11b208811401074500c0780301400b8583d000f50200036008032401002510b0006201c01440742c2d081c5424003a1107082c1c0c0b03150005100c2c940302030b804003407800c400c0000081c120520b500041d1030501c456000101107030b104c807440691400d0841c0c41c9a00802e8002c6116010300303156002820b5654010312507031170f004010144145091040c40001c2ca031142e118107884c1d560351203000040801c0607501007500d0000c0c0c4500402c03824201846850b080382c00c100e00309800c080c103100c0c00310060b6000460940400c143d102d4042154100301000310024000c401c2c0c11404141c084409000c1c5600c0c1c0d0f00441000d15604518580c0d0030b80181c00c80b51010f6041c9000500302c0e00c0d91410340314074000d01480b150403040c004c0300401000240480c0c948803214648540b2a0180150205c0d5511700c1161700179 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 477033417 1250 477032167 477032201
    0x60509010611010e0f0c12010e0a030315031e02011e0e10111006030b090619050c042303162303010b190e150d0b04020424080d03 57
    0x4000c0396100e4080409214000c200100da1601245026480c15605c6582100190000441d0600514054a401c1e00102c45003000341b028000300e007400b5441da42c0701400074040c540c03140600c0310407d15481d070740000345030f22481500610586c5802c145122500002c100e02103240f080011000c02001d01a283c0303554201c1e41ca040242c40c0e094203125250740d10503420014400e1303503d00d0f01107000091058034425400ca000008195265040107018140c0107000c000f01a000b000074400c44c0807601c4103000c41e07291b0510001c5403540316a0080e0965203c1d652140310066558400c11a00083c04400e08184800440441c0c207440071038283c00d80350700500c0c803030341d44500b100480c80024803044142035034041e0301c000d00020700450b241001c641580d04110f41ca08240040304410b0016030710214070b49030040307000c1d8214140303449680c010130766410002c04003922640c0b03400c000070215900c94001c0c8400c190101046500c0188104003007806807140c1c0507525803406544800303142c0510078441e4102c016812944 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 477034667 1250 477033417 477033419
    0x1030f090506131b0b0726030c160605010608060901090c0f0e0a03050a03051e16020607050c061c0516020c011b0f030e010f1815050c06070203031906050901 69
    0x610000d6070b070365a50032070703919000301c41c3c01350200300405800005200c0880301540c2c9010380d10b80940b4484600d03004514080881948104e2000310000340da0703010a000d070703800d0b135554640305090012204c180700c0140361a040078004140258031400450045105440d035200598031240c000d010340d001c0c0d5202d180041c1d09014000c40c107512a1800c2c440541024060315400360700d0361a014104168204150045000002c0000314046480180414030301c41000d00c90800035443c006509a810405001c0d10604001c510803003400000c0c041650008030050103503a44410480c410b200e080340816542c89018682000200c0140c20b050040070b1050040d0301401079107101d1300054030540540c40c400d40001a54035184000256001284850300707000f03440b0466480c2403d4001007490300f90642c03c03c00c01001360710091034035041031007140958510403600309010740380314812111400341c0300703141c515441000b0500c00c00f5038000c0700031400b03061a40017640001e005a41640292079140c0316064000d441800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 477035917 1250 477034667 477034681
    0x40c020d050f0403050f0c0a1a0d0507020c040c0e1009030c0b03040c09050a090204050601111506061309020a020111031603091502120f1605040b03101a03040201030f090506 76
    0x3071045015240c40b0604140d10fa480b5980303483d446048882d41c81e440341d450750807103180c1041d8100043c20b06001e290b61440c07a03142c00f08150b0141029903503d841d128804940980d00070b0040c64040c0c5406002000008140d101c018040c403d90300e80180902d2150340d081072076502c0b8408041c1a01d812801ea11079a9103881134004103030b400100180c0340e0800c614804124041d05008482c01600400d501041851507070040104542d0302400d814103020f5485803c40050f4404111400b020901000d03050f0305658000101d90180f1a160f41c91162403030b0442e01054210f0640e002c2c0c003810a5560003002040c00c880c001c9511440700f560400703c039002c0600504000741c0b003034200b040201c3c810160348450b0720f850010641aa00031600310f80004400e1401c02244680003112941d01200c00c11003282e4542002101a080c1e1080c0d000e2058550b41c0000040c06002c8800d000380e006150020860050f507250045111481c0c005860403400241040c203000705a403030703078000e03080015000350203001a0b4440c25 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 477037167 1250 477035917 477035927
    0x210090e15060906030403081009091a040c050a0e090d03021e0901020a06020c0616020c060a23190813020108060f042c010e01180201052d090102010b040c020d 70
    0x380c03520ba40144104507480c5191035a0018500442c460b40301d41c10941002c0781d8003009858141c102258072443e081c050780c0894040c68001e191410051150100b91b112401c0903400582260421508080081800203124070083c005a1207130311214142e6002c01d04584044090b840351070b04444030301c0400d028000001840781c0c0100b0750000140100e40c810185669480183c0c1c1000c2c4883c84c07a6000242088211107c000e2030842e8402903102800d00e503144100000c046004850307800040089400c5104166682243d1505141001342c50785a2105002c480c044420540e000010001a141501003440200c1c040180c80005038161101c9480303035107210510164011802e00070342c1c855128100c1307488501e6800510401501226407029103038640b0484203007520a040c1c12020180e02d8809264000142428111070311075091030160b13520700030008041d52003d000c0060202c01c0c2d56a2107070100c0f2480703c00085c9240b0400780c009000800940d000c01049610681c00341002d80c10443c29441d2040c0700f8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 477038417 1250 477037167 477037201
    0x606060a050405030106120201080a1e02180402030a15140306010b0f0d0c0521090303040209042a0e060d1109180715090f08070e040f1406040210090e 66
    0x600d0320500b096a50f20000e42034074000d0b03001000403e803600c10302044d035910a040940c4021051000c0c0b11007400070f0071000c00b00c641402e4a07801e484e401b007003d500286030000101c10802000b00b0943d183c0c00c01566020041190403505940c950f0100c000080c1c0500d55064140101030003005420300c2d80c685040c1c01d80941c0134000100010301d0400c00e06802022900c511a030303100c00303503940c10386546410b88508400c0d80d040a80d00c414640701c504007e08541c1c008101c80e40594141c135060100d44982c680a603d25044d00040400c402003006068401014020707240b003196180081d1008644807442401a034080b2100060500c5a449001c16200d0900b141e83c107030010200858809881c082d0103440e0f04014460f0000712503407050b5458030045903803203230010000d425012100300c41c091034001242c0d42e41c00584103031400c0340d22140018003841401d0b9000d080f403a41100710503100006060445490b540c00700e40c200c1c8100920a1040000e9216141d06070a03250303455010b0a8507110400070410740420 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 477039667 1250 477038417 477038437
    0x7170408010506090c0702130b03240108070503120a05040b040e04050705010c030f030b010e0402120109060803090109030f1a01080a0302060c090d1113180c120b07052d130f0602060606 81
    0x210441c01547d0348ac1004400d2100c980201c000501d0220000780081e8090706038440c000039402031009020941e0080340c00d84401e94201000c660342c40062106403446e01403075004040c91000481c00003840900208054410382c0b0034070a5400b215140c50040d81d04400704840500061a410101d0328a540250310240c6007038014105a20703000021030000b010ba9101c1c0c0165280842120010443e16110707004140291a0100c081c0d801c00d5413000000300841e2142c40058071031a8000c540b242031101c5900c4004090500b009100d03959a141d44040d076444801c1300c000c80051058100145187e055801510444600208206c44039a00c0c1c0e115003090300c4114141a80c800f0010214411081d9203100b074603101c00070001b640050142d5418045215405035000d80c00341d0142000c910001003a1010260b403010440c148591682c0a41c08521801d000d02d81c402540660710600e14200c0740c0c0080040c1014000c420042180940c650440301c100c0780c1e00307108440142e884a80401c019150000182084002c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 477040917 1250 477039667 477039671
    0x1809030c08030624280507080d2a1b02060f1e12091515042d0501230604050105070311060f0f07030b210307170408010506090c070213 59
    0x850768400840180040030b013081307190010358429840c119180ba25041c0340e410302d26843e4240035040281c058440c0150050528500258803540e0200a501c0461106c490b107101c0012004150102d1400216203000200860b05001d44145800e0110083c0b9101c942d0142c8804d00381051260142001e42110b040c0014a89040c801041c1e80c0304450301030442c00f600c0c0e41c0da005903030030404d113254100b08a805131038204400c400c0803c030040b00c10040d1410b1040095900140714403019441d82c420038015004070820009020542d000c500d4183c020780d06849000402d850cc0d890200d09011445400398074061700128140010402980200090715000340603003403400004100ca9030460901380203c1d000b0340c07519012000e10128030092000341ea4010303014101004108808000140c0032040311410480c0400c45040014920000f070050f140c0d1a81c1c0601e200000400340240381c41250001d02030948251318260006485107490801c035802038282d0300c0018030300302ca15001e1015000b0070311903c2295036 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 477042167 1250 477040917 477040939
    0x30311030904150501080f1501140408061603051303020a2018160306060804020907091503060815010522060b04060201290105160501060b0f041809030c080306 70
    0xe00e0703d00035290b10603010754004045a003840009082d00d107000c1c1c01049114194000c02030030307181181404c4800c50b02401d1055001308499021440c81c4225004074541d0702502c0c0a104041c0b0013034240e40c04001c01794405000a56500424403003900640b640500181c0c01005000042184198090b0b5504860141c0c010311001510200d08041c903890350102c108501d101c2007103c146004503007032400c070b826440c05000306072500700001d020200c0034001902c9400c0d40e0000ca010b00d4080d409032030090250f10700030b800004082c0f02c050000c0c04c032842007800340c1c010041740d43e00c1d0141f8046d80d80e05a5200070083c9566141c0645005003003d8818945000e00d0342e50400450642c8140015100501c400c0e800800c0c40d14a0072058a40d01d0380c0e9040792015404401340b6040030b680c00c82c3c15100c1e0042c0c007409405099180c2d050031400741005038400c100180c00020200441f079070000007401601e00305480b4a105070040f104000858940180c0580022010407640b000600c8400040d13412010007005090b401c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 477043417 1250 477042167 477042169
    0x90311060408010915050c070804210b010f08120c070611030903060a062102030c060d09120f02070602070f0306090303140a0527060c071b09050411030c0a0303110309 73
    0x49120440075141c4800c40407403170401e869039010340c55000c1500f0708141c2c00e003101a036428149001c2e90241c82c1030394140c2030f002d80400e03054202990b2210381042d51248a960740b1004815002031030300454403075002d41e0080c41c80c1c10900b0000c070391091b48800000d110007450800111207039841c1e00c0080340b442c003040048092a0350200400d078081c0040905c0094440e1130100000c10800b10b2940e071110b0003051480c5180035a42c08111220440c1e0187c0b044ca030366100c0c1c50010401005c51000003000740000a1300a05003560060510b200741c002602101c500503259042603940e501c0c80d2064070107024001d0410710000d001ea4104d0000c0074800e040c041100740384213a0302ea81c2c84070211818481c540c2e0760420049401c15003540076246a00c2c0700c0b40307640301c0004212450b0f180c680041840b12070010004078030003000780624070000703009200100d002c800d5803a441001c0142600391810307a000c64003403072400c545142c04908070340c03198402820510000d10b55501030350441049100000320740400d020340022 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 477044667 1250 477043417 477043421
    0x30a18081005180d17071107080607080903030103050604110111030309010b0406060504060e19030803090f010f05090303060405040501060b13051002060f011202040902130f06060f09031106040801 86
    0x150501148010480740352070340c00c0b19001c0140121049013580315056080780c0c2c581000034101407407507401c8194842c0d03607802d1098a06800d10110b402c118810b10301c00040c255030202e2064040ea2142c1d490403500d8a50300d00a6549000a0002410981207103011a0000b41c0b1848868030100c010304110002600b8680e2403802c5402c105c3c4d401d0301d141d44540b1020100d10b410b100d80e1000c0c0c8100e0510505050a000b40108100e40345510b0360300884c1c40c506c50074021140a0f8002c0000c50740140c0c81596840c2100495851f15490307100002151700305003210011307604030f010381446100203400031401c40e540c000411001d4840908290344079541d40c600890a00d258200130640010340d003c85001152805080c02061100752001c081190091020301c002d203117209840344e04540845490480710b203800e000150040c074480388000d5000072002a80c0c03d0b50002e6400502100b50114000c0107503030343d100303800c0d50200101503540c40000d4020ba41417001070405900d5415113003000d04518101907c451103282 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 477045917 1250 477044667 477044683
    0x4020301110703110c091009110d0213140405040b041e0b010f0303080a181401020906030f16020d0e1003090f080c0d02120f03090a0c0902030604110903030a1808 71
    0xf0015001c002c00b094001000c22000d003644509440400d403915064005c0e428100c0350b0700034109030a4580d04c20701e0408414a00340c40c034200464508541d566840d0144405002c002d20511a40000d074003081000c900c0e047c800c0903c0340b904126140207640c5d843d03540700e5840e550440d030900c40b610118101804581d07400d132803e01070200721000c88465420740c04d010300110801001e001c910b90426500c900c2040000c28526850341d030040144240c801c500d80c2481c0640600d10505800010110411410385103e1103460702400c0d003c481c4260f17541843c4422615030805000c070801140d0446205400d07410160740341114200e55160000321a410b0ba51426880400f07a8029903007124081000c0e280131005010880400c00a80010b01e090000d40004001b5801404030a0180a50200010342100c4082c402c030301619170300030740914031240c603108600003d400544c0c200e40100d00d054802d454a441250840b01e081070006e0085060580090088501401040c3c01c0840208405030000340c1107420840c0396 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 477047167 1250 477045917 477045923
    0x16060e030d0e06040f020d020a0b0c0c12060f07050d0e2b0f0807080411030609070e07170a050405151602011107020607170c030406020127021008040203011107 70
    0x1981e40c90308420500c2a140540145100c81d0811024000064a0340485c01201da074180c80c0358040c1211400014a080c0ca81d9000040140c0001006400000080b40d654106d100c11550103080c418102d83c19980c464048840c900c91004000201d1030b51405100600080105003001066000e803101c0400d082a11510003d0a85c0ca64040d10680c15502803400d402c1c4c9050514001e800301c103408000403c1070101800350824001c440c1c0100e010300c031145034101017000d009012920b1500700f1101c0180d440072030348110444800d8040c0422482d601c10b900c4540684004407020700581c0794101940c004150107081101d0f0b5204007003e40c120b09200c415510300c546c203600030142c0700e6903201d100a806c5d070b5101146c1b10140b0030100034100040c1d8503e001d0300e600c2a0000741c2114440c3c2c088801c02c0e4544610041221130380300c080303800079021740d054100ae01c5404251100400e00007907646141070344640f40500941c00b1866001e50402c9610603202280d1181c0001d002080c9072900b419039001795400502c0903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 477048417 1250 477047167 477047173
    0xf01031e030f230d0212060d050307030c0303090c03050d030e030f2505060403051c110f070201140301080a030e090702030909090c18060f1206060f03070803040905060a08030a090b16060e 82
    0x60072500c2101e01400c1d4400000c1d00c41e401915543d94802b80c81f8411448018103101a15076020240340c8a940441d69240d48106540362468484c10841e5584440001100000341402a003000191020040c1d130441c0c000410010300f05a155030540c0c01503402d411b0031040b00c08060000d0408203d0800001d4080e43c06512004d80d64403004c600ca000b00040c0070400c41d0003a051600701803c5101d05800c85103107400030800e590702c0d40903030310040315032100d000b1965005010200020900b14004541c40401c00d2103521154000f0380c1050500c9800c1004480c1031000d0b030020300c044207013420004100c65022050400341c5440c1041200025014401e0081842604c600c050400c030301410720079100034450030b0490b0030811003542000d5503a039400b0002c11041c000d100c804c0306032141d0b0b03c0c20070aa030041c02c1010309881d1140e440e00342c9240106404c41e0318604c28004176800085091001c001c969642c80d03543d80300942d40b030805540c80b01d140d02a4000c1c10240640c0421000800c0681c45100e40982e000707409 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 477049667 1250 477048417 477048427
    0x14011103040f030314070506060d05030c0a0b0601020c09010e061005040801060f031e0b0a0c050d1a01080c0f0a1d060a03050103060f060803040311180f01031e030f230d02 75
    0x400c0f410404002da4040e117402c02c00d11012450001e0070b141e0080c0129881c400745000342c9003060840c000d2a020b44024800d44003280704010034441c507184a0402039086071a0000480e0801015480a20842e8100803106020a01c2814008142d5001000c2c0e800c0541c50160707116034039070840b5500e81c0940301c2c0341801d200c01d004010034007000c00340c4003d1200142090b00440d0310791080766072018241c0200c9543d145146500c0764001c005843d00c0380c981130401c01203c1245650703645a0040d00289a002404000c0001c844402401c1600d251071a00c070940340c1011080d840503180024140207100042440540300c96030f659a0300002d00d2012525030717000c01d140d407451400005485000c000e0740714450420030140300001000094601b120340050a00106d403810f0030110b0940c05241d480c402c0004580801c00c0701d68241e1a4006048a04c60443c0c85000000101010b00e010030114004000407101103480c0c6080b8400c1a1800c280c003030800290b2a0380404d03400400d20b0303030b0001444181550300460 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 477050917 1250 477049667 477049673
    0x7080d020c0a1109070503090d200d050c2b0f021f020c0706050f0901051312051c020d20070506130e0112030206071b0203010f0f0f1514011103040f03 66
    0x4a070640017841070801d24118101804d03043d44030100161003c00300301a100c441c151021841607891091007039542610003440f0041c02c0100f00d03601600202c0d0346845060700030309251901600c42c0000505280b03804e00742c222802812102e07240044295421032252081042c0c03003160746040e10903100441c0c100107aa5a600c08419410505039038081400d015050000e0106410050115017074500709181c03503a41c4ea0038107141c014154400e600600010b070703c0d00c100351007044400580080610050003880120107800070b01241d40e01900c1d240301c000250807410b120040e09138180c07048800c0044405850740640c8900c0441c035542c0006a87c552000008841005540004040b0740e01514a0345c030035580225654402950700e21000d40303480200700104140c0b2060001c0c14029a00013503000b4000e01c840040806180302030812407203201c051038900400603090841030311801c041d081c0301c3c86595070302c10b1412141e02c84040030905000d042c045078100c10902184103200030305c003800c0421224907040303041d42 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 477052167 1250 477050917 477050929
    0xf0f0f0a0f210903031107080903060f100e090f061f0b03060d111903060212180a060507261503070e1f05120601050111030f07080d020c0a11 62
    0x460380100740301c00341000580b100210402400004080d000100390b0842c28a400c41c002c0241c28007016181c540440c1d040200100000103010a01084044606a40f1682e0340b820910b6000e032514001004110010019014803084240d40f128030502076a009504404101d030810100b260b81d03143d51034420005800c0c0312102c4244c48042c015030790303031107055140500203c3c101210404000d4041034085009141e075079a6440c0040200a403180d03600201c0340c0da031030040013941194000780c04400c40c0b10000b0701c0c624610402005420b41032802001007d98544800004080140c4180c0c00c115500d8061100c80c100d40c0103ca083c454910303207198052070f000c085d0150b40a0740c10749441c4a81c010140070800c890303840e80f450b60800404174190ba032800e5484085240c01e122948159002812202c00c00d824041c0803848074126042070301c40030310525008200540701d200d592074000601600f402180c1c00705030a2405003104070300f9608014580b0b801c0b140844c0c9090101181100c003050000342140407800d1035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 477053417 1250 477052167 477052187
    0x608031b010e19020405060f0a0602030d14040f03120b060403141005131205041512200403080906070b10090b030304030317040f12030920030607050f0f0f0a 69
    0x450181c803040c45024031104802c42c081c030f800b920881e181c01c0400c11315521828281c172814130090500c904256100006074480c1c100c103925001c0700c1d1400042540301c030a00140070340f269a00403c1c500d10100305507029035150f4020210701c1d0856030b03140c2e030500540c4c403004010300c00303140218500c409070007a03000403d150440003440904854182428041d49900d000e105118040d8002c1001e603000740c004008581c94007480e4012004034110340c01034000541c02a02009058004000902601c28000a11140c8455103034950042e20b41c2088104007050040c2c024200a19000380038515140d10341d15403207000c890584511500202c02041004071080c280f181141061059025508003451501c0103800100d00143c03600c40000c00c180058100700b171094801c1c04180d4800c409000c0324201c124001e00800d6490303000c41d41002d800c10120414241d0b441044e41d904d100500403c441d990f020000c035100d80290380d10300c0c50a841071004d40844058903025020001d8041841516000b040000501072129 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 477054667 1250 477053417 477053441
    0xa030b03010e1f020405010e13020d020d06030308060a0e0a1505100521010b090909010219030e1e06060d021f03020a03050a0e10180b100501110d0207090c030608031b01 74
    0x41017008200301e0740c010342e035050942d80481d4620120051040c8400107481600340c01190f40b0704c001009402c00c81c243c0e000030b050340d01030384d0362140303640c3c03901d0604c007200c0541e00503156807450110026000001235048807001040c070940b00b440d45036440c00440c50440044100034040346010421042042015000d02405d843c521303003101e034552500300c2c4210203210359002c45e4060380c0c8100c00103080311300c25011551314824001d6400c03610402068000c0042003090400003d5018058074402d01ca2119242c1e09020812071003c0c02712920345c8000c0041c2d000780380300704a81284107144213503160290480c100c050b00740252000740c1e82e605c56040050444000400710f85019142c20303078203134000701c000440c200d403403c40c660001a205120110398011000101004010807901010006801c1e00e40c24010115517003a20f81211505a00070050780300d485104200d001070348159006c200501c0d8035008140d9021003400d00140507601d40510500715806040d90740d424010986941825007403d109040703000344 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 477055917 1250 477054667 477054671
    0x1050406050708160b041112010b1c02030c0d05010213061b03030911040609060504050901090515040f2111030906070f0c150c052e020a030b03010e1f 66
    0x10034404098454020800043c14664020440e070140e00b150610b15008150442202007051a00e49010031072614207640c6140101c5a10030503c200303510500420b54034040003041000300c1d640700310204007181c0d42d04206070781c1880b41c0e69171100182c684c84840390724140524009a9210503501c0c82c1c07003001189074000410000301c41d5841d0030058840285040540d450b1501040796162800c0c114a03d40108030b5803644240750940c00203444103150f0103074044820688040c072141d56519189822146c50b03041c05000f031f80004010818403c004d2000c03c0e80030784107007100f40c0c1c4030fa11502d80c15040d84150700c1c44511100c0d0481c1c2d004134039030440c02e41c05844400c14002c5180c9040764012584074040d00000034a81980c440c18003041168908401c0c0290042010f00615100700110040c0720800d0725209903141d015015010600c01030f51217284180680c060000045900c21a0210009501c0b40c18200d080640e2000d12074a65034080c040c40340001f8ee59001009208280140742e058000700841800c0164 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 477057167 1250 477055917 477055919
    0x70807020a0305120a090213060911040807060503070201020f1305120a110103110c0f0705090a02120105060c0a020d05030c010e060f010501030b0a09290301021c150e0c0304030e010504 81
    0xd5001045444100c20b50030801c4c081d8403907a003000c014001c0300c64021340c07194882c031703441010315030540c80181103594400f4144141088104104402c0c8941c1c000e981e01d0350041d4405200d80c42c0580000e5401510500c00149045079400c0003154a0300311a10260b100131030a5020070680c03505030400d5a0400800c1c0103010350465540d24030900041c4008000c0c1030540720081c818040c440708040d00c03d501d00800507540c0304450300740c0b0642c444949004451141802d8000310b651150f00d0b10941d0781e12641545070201ca6405e00d400c01c900d03504054103082d81486001c25440050319200c0c188200e451189005588504c2e12811a85c00d65609d242070758002e0f4030100c1041800801d41040301e0448100707083c0091181070030008035006921039041508c1c0c56003080e40040210701040b1100c11010142c030400c007503100c4080101800c0c0c0c80b07403900091140080d451140700d2041c190340706100c600e01080800c105145e41d03141806048004030f40d52a402d04000c030410040c103800c050350712950350b024030b0218501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 477058417 1250 477057167 477057173
    0x12040f2001110c1f0507060926070f020405130602070506040b0a0c091404020714030a1409010f1202160303090605180303043c02100201060f14041112070807020a 71
    0x2003010700400c10403852903001240b030b407980217000b02d0714466003054007848a00041d04100400d020500d1900c6044246201c1490003d21500c00365400030303500404404010300550200800780c04042c2c400344c2001e02040c0c22400041c1140b005022091088014000764078103030402a0312071000401940c40c95040481c10f0718000d9011603441c00b9104501e6003003015040d07030400700340203003c0e075074004101041c4803150000161001029184944c25030b5526992420f00c82001790042c084e40c0c0d001030105808116281107640a142c0c1c03140140f11082c801420001e0303045040d00b60b02e4185c1c00a60200c0e54505041082c08840d001e441e6000005400046081000030461030f07503132200502c0508061420720904121841c10707000c80f8401010304595642106511680040f48208041c04030f2103021000d04040056006020b0740701101c070721901e9044000d01e0080240ea041c02c407100b40b9507015958514411046070110060a07507906280c0503503543d403820714406803400b1400b81c180320556102c52210000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 477059667 1250 477058417 477058429
    0x50d0905031e0109140609060601090f05091f0f0e1b040b0a02070f17160e060f01180902090a0b070b060d0f020904080a12050c12040f2001110c 63
    0x112015a0b0390000c45001c0504a14014550b00c480184000803d00d0404025000050054019410304c81035400035242c050054443d241240b00e400210780a5201c1000680b0b0004526030b071000100d807082c40510030319850030000051035001a100001c4541c82440502840010f0329442024003540c02c011088030216460389005a2145002d5020001210001c2d81e1081c4545d0008003c0815608007450302d0b40d40b0811814812082e04d6401c0c0f03e801c8a02c81840f008550410855003031b00038103003064a510040c400b180b0310184090303040c8400142c59a2111040500000040100480050702c1c0da042c60300700b01074004581c1c801c55000703006100c04c1d00401d10350380c3c4854000700c040315821000d64041c81c1c009c04440b0b60260107584040500104810700c44514000c21202c01c0315a11807404100a207000003c0b6401507034003a03c01581800b00c421740500c88040703280c01900601c3d00c4070301d4a0283c0da403014120322a0100b091880640818602c42e0b58100d036203208040710400c0502003021480001c520 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 477060917 1250 477059667 477059683
    0x15090c151412070c0515060f091005090c1c0603050f030c030a1805061207110a030210091112030702040f060e040b0703061203080906130f06050c04090c0c050d090503 73
    0x85202c08403008644410f000f558611500e59208094480c5403002a40c80e180030754007260194040c100703030401c0c01090b18000c0c013000e12580d03890640c0707813443c2e080206010342c1d110b0080034480c440c841005a42107246605204811898880c880072840a045103051030030b1060180301e41c0d485610038404441d2100d070101c243c5908014600c1e0040340c081d000700e41c03044124a01d910140d003003c800074002070300801803d1000d1043d4641d803603d10b003110035040c40030396840e010580070300141c200c00901407014420750461f82c54680514114540e58003c500016003401d01d20080200b1079000040c0c1b00c04506090044141c1a0300c24102004001d2800d99024611030009000404054101c80040d024900a5006e070700681207100e00822507210500d0050400d41c0245c0e1a5802807044100184002045100b0408000c8d8090b440c20031a417035995804000d0000581041410390062001041c43c255503c14109410700503616000140e03150b041103410b002040080c07100300304400d031003070000c4d40700002c3c103907 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 477062167 1250 477060917 477060937
    0x515010c031d060403060e0d140306011704050a050d050a030e030313060c021609060905010e010302010c120e100323010f063c0219020f040915090c1514 67
    0x141580b010400080061055402c01801c181c030306030780c83c1110100010001c82d00c80c580d032501640d50140d02140f080d00d000490720580001c0c1000001100d019128102d260054400c00444105401a0356102c0c01e06982c445414000341d008908500310950600407488400a2040510700c1d500f000381000c0b41d4001c81503000f411320794a5180001a06108008a82c2800071998912840e1920740400001900f414840e40051a0802c800440e0000c10524201e040b03a0b8161600c4200a10315510302e14074a0b508a5840305101460043c0021a1544030070108402c1c0140c2c0c00052040c1d4001406400381100b00c0795100200340d8030018000c01c2502801042503829505015a00c503d407001c2841c4200c80032002950720584c1c00d0396048074201010601850740d6040d0302541c00c10f500c04690030f01d4450001c48042d51110707040c00180d51505007076020010050140869002491360680244161140007030b040304d0030200070754204030700c1444004c202a040403e1402d004016200c1003041c601e40a0a840c007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 477063417 1250 477062167 477062207
    0x100c0207060e180c220f0614041d0a051305070911040b04120c0e04030e060a09080a03080f15130515031b010807110303130302010f0f0515010c03 64
    0x900a640702030000208000b5030f4103004980c5401008007409801000c040401500031032843c8101066501110f01661403088000ca0f009150003421500400203a1706400144000c210106511a8a1501460400c038080d903140c058140284c0c503200b06d907401020980054851001c90001440110f10f682c02c0b07905030071020680130340c4807a580001c1d200f50344c0860001e01000030005400f084c04900b00e03801c58040d4031140001e99440c0f1494207006801c650080000325060205821890018043d082000d0316141284820781c860411925142000b803080e00804c01440400002e45c0c2e840c0580c07076209142d44940c0d048130b004440490318403000040080402511035000581e520502c0c00000d9010200504803a1506001c22100c1440051400c405000504a030005805240501242d164920800c8010351a5640c0d601d2403101c98100040c0890071552a01c00c0c119030400e0a0007038074030b2100006070000303c505041d0012881050040b07461410720030400d40030f0300840c0e005003681c0e004003a103000c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 477064667 1250 477063417 477063437
    0x20f090601051611030d050306060d0207050a0b24011b0206090d05062d0105100e0301060504230f1e070c0803010303050c0c0d110409061d010e100c020706 68
    0x103840c0d90040c5075986210400000d40807051000701d41154002c82c42c10345c10740e10305084841003102d0780d1000300c622079040307a0100f2031240f810300154014083c4501442c00c0d40c084680c036980b0500c0c01001910b401d40c00c00d40c1c0c0d00742c3c0b0621124200120743d9070072007401c0c400b0391048046240086158144030291107100049602440707503c50903600d4030190740c00300640d0750302d14000071101c007001c0b0000402128480340104882c0428040a01035068a03402130602c1401e0600302c00c21a1225501d070202038165495001c005000d4485001d01d4102040641c041c001102d16131700f0820310241d00415100d00c48402c24107100211311010074400030300d420314002d0141550788000c2698260303000c4030014500500000008141a0700101500100c04a0800c1e554100034500c100040101e02800203017509480000b2504140340c60380c0250041c03449801c1c0400c0d40c0d040108400c00694400d8080c8070580d4440c1c0d8010500441130010520011018408000d000e01c1d165000b9034074000c6004040c184540703205 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 477065917 1250 477064667 477064669
    0x110615060c0708030a03090c080d0519050c06010f090e030306300d0207210218071206080d0e120a02150f03090a0c090627020f0c01140a0504020f0906 66
    0x90390007030300c0b180301141e41d900c5940b40010300071f02c010349040d255840c604001151540f030200d00012400703003507580c04d41010301a010f8003002c224451002824440c0400525001050034442180285480041841418507008804054804c0703143c0409882d0020000c2225541e40c0e0001c40c400c0710150b0f0a519104101d45142c071204c11903401d000d402c00d02c40c403140300d410140c1c001707901c0b8151201c0c0f007002880d90250600c0c03000140341038100254030040464840d400032465011803580130200f440c0211090700060042c108498043e00705080a03000034508030344068000000903e001d80560fa06081740344800d048030303140d4810200c024490907522008805800040c800e41301000d41000c0156602d0801c2003051350b07181401d80007201d070582c03101ca001884090b90320844046802e1030202c0d00240c400384050b401c0250050b03d4441025600340040d1458244c0c00c030181200805800c000500340204221724410440010042541a03060404210050f02d94106061000a00b43c5a510030350311400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 477067167 1250 477065917 477065923
    0x4080703050f07060605031c020a121803060f140709060c080918090d110a022101020301170715050a030506040e060721090209070f020a15020406110615060c 69
    0x2041042c40d2011507610207000f800d520078012980128119074040d8405084880401017030f02c0b10501607080866418003007840b0300c0780000c8101003490882a0710b900640480742a00083c1c1042e04e126542e444100c8a91a4512800301024000c03643c080407880c02560050402c0c101340544c004101c017400e00d10301003040a100f501c09000006205a141040c842c05c4000c4410003101d5801003403095000d07035150302d806000b440c0c40d0380d1401806404043c41580034060240b06200300540c0a9490700790882c0c80600a03c0030394041d010350b400c1c4e090081407a0802c1450804560018021071050400d484a450707049400c43d0415031843c28040b406c0d03541c0ca00000c0c0100981500c0f102a0301411041083c00d0b42e004414001218481c0b4003001c0b034200c0018168100d80894900942140007400407981213409144000b202c8041c0348115103000c0e00c07540da41c01e02a009110a0b00c03401d40c0100b010b101164109044141042244004010a103007140c070041c4e00c2404400054010000040d03c02c400032002c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 477068417 1250 477067167 477067177
    0x60c080d1805010c08270304050405090a12050f04171f0c02010f1103010308090d05010614010e01020f12090103020408010603051011031303031a09100503071d0408070305 75
    0x10640070409048020700e0301c8021840c001c0221031a5203070403900c4075040d000d215028040e4000315403584040340d240c40c00c00708011000301032003003621003400000340325500c42c001c141c070039210140074090412030343c41c080d4010b1a210044009000c0709105540480703413a501039800300c0c0d10341c4069190614217100c0380c504207411204140e1588800b210135002d4064070340c1213503608890b139900030001410540740381011202c034a110b000c00007004000410124114101a013030a410051001c000b1a0b00c0795501070131544030f42c0c40030803c450000020f840035a00003444600c04c400030f0002e8001c203180c0c80740c02d640341d40807940c181d0306400c0c010544401e6a417007907040d1800340040e00d0007041040d07128144035540b207002c3e030760303480450b402c00165110031407503001500d00503e0300031281c901403441942c00350003400502c0551030f04a1407800c01401a5a0b03841c401501820140b01c028501d1800d00382031505140c22500300c058158910b031040d40c042c3d8103140324240e10a4010a040b5120301c200c1c90201c90318456 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 477069667 1250 477068417 477068437
    0x703050a1803081b041d090c1201050910020f191101061806060e060a081504050705030406050601091a133b0c09040216060516030b03070807060c08 65
    0x1410703050404068000741218002d80075140d105106800e0490440e180d4810b034000c6a29554103c056120034060030844190481ea406003903601c8818040040b601c0c1c04542e0005524a0b9100d0b030074000082e401b40242d02e082130301401c00354174010050303c850210344980411104412080b04451550034030400060342001c17500402840107542d500180c182201c08010490903043c60840c001443d41e0180d1541c0000420280400c0d0030213800b11001e680c000002480090301a00700204140d140e0b56a1061780d1180402d501ca0f59201d0409040200c111800100100d05000000d042400200e0000070251032016a15407100d1381c1b8660000c1e4041c4640b040e51005400c405020704100c200504000101641d0030032921905410451040b42d4810b00c0c2d042d100b5500710041001035010505207500200289662014940d250b520356940c0d080840e01c0840d413076032068500d904840c04003603041c004c164001004800401d05170341090500360b15611940b0800050008600040f001c2111680c181c40031008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 477070917 1250 477069667 477069701
    0x60918011b03020406030b190605030705131203031d060112080715060312030606081506210601120b0f0922120f080f190e0709091a07080703050a 64
    0x1e03a014080d02039007060260f1800300c1d040c00c8070686c15081003c0704408422100864010705460704c5410b803130715440500100c0401008120300c2a9440d94500540024450000b2100441404d41001812500311361260a11407201c0e00c60800032041c00140603066460504041e180303076082c0e00c0c003940c09202d41c2c0305c0103182650b902d2181050300e0540c3e03c040308032030240c1071a014074007400d10100c0407030705140030f054007041007403010603000752014458103020b040c00f50030946844182e50221111420000c00950701490301c404200d419640030441d11031542074083c05010078070540c8000344003442411480d902800d415000103c80d890440090070641c0018021001070b001c00d03041424402055007144808940d050348445103452246004510a1800317406400d0300e5100d040d205411101035554403040c8a49070018020018811710140006144480d030000e4000340514210720019148100c1c0702002c0d100a0401c540c0035080b1403066809800c901d0002440d50b940c0c0956001400f0444136102c02c0c407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 477072167 1250 477070917 477070961
    0x1306030c1e0506130918050102131e0b03060409020402220504050f0105010816180e0a0e0d090b07150f0c1101051006200609030403030908030306091801 67
    0xa5005544412968903118201078415100e0040c01041d2042c01d40900320500b21200030071400440740d001c000b03088a980c106001001d803e4986900707a0300025014011188125403c03c0b0a4240f14840c01c0d8428038114580b91052030403180b00501d010080400d0700640d1102400411503035182e0440e0802012508041c0b1203012410040e6042c0c00f80d4090710303000760310b08000704240c09019004241280c00507500e103e010b940d03010301212414500c040320410720000121808501d005106120b018028000001d2168504081508251030f400405400950898444a03203040e84c4041c1da14168ad4a822500e0364a41c01403074140442c104d0054090316040c40e00078400c10540344c641094105995595a00412207060202a8201c480030391795a952402820010003040d8000d00f5414035610714402e8003022a9540d484160601d18215010002d0b13810008e41481007680101c460350150015a00540c1549006004907441c00030191074401170100341c040c034408084003500700c04284a10258101016 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 477073417 1250 477072167 477072179
    0x509270a0804080f060601030204050d03201b01180e0f1b0706050723031b0d06030f12030501080304210606140414090c0103021e0705030a030506031b1306030c 70
    0x4148003005911345001c0ca10205100e0340c030038025101940c2008020a80a40180e0350a503402e144800c10000b10780031210007542d202d0000e03c0405050080142031510004421000504940010038402080500039500380b11a000450741641d00038400c00110035661142c1810030300308003109150030b100c200001984020460f8680042c0e00031034139070310b406007142d82d04041001d1800018428407011001070002030844205071840c2100c13101001141803501c8484408901524040c3d0415100c0d000c1380d400c01d200b0001c10391003041262040349030800080d410442100c0d201d00c124400e1b4a590820703030000420703000141400c00c640640c0320504001540d61480100300c0d01c5c03000b4828910662920f685440a11140c00c1d401b0300c500161006000c02d00340b00001035000350072803540707842903809000c074006088000710028a2514017850040d5103450720307903100034280c4800400d4035000b50410001c01c840080b90103004040e010045a100d0500011a51070000900c11a8030252200000071000140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 477074667 1250 477073417 477073423
    0x180303090905070e010c031d040f023f0402042306030f0a0b0c16020306070e0f0a080606011202161407090c09090b010c0f050607090509270a080408 65
    0x1101c0916405100d155944001510080007a00d0450301007844140400b000070b100b440d4a160000585c440c0000c0c4884403c041001c03600d10841855103a0760004440351410340c00400d4031890019071592820b5a0b0001740300d00400301407141080c02d40712200001c1340455503a03410610902400f40880f043c60140a201e1005405040d07070003a01a002e5a10090100d0f00003240700341400c0c1e04440b15100d02d89070f02e400c030009640310344641c000882000c054800107903403d01000d4003c00c015680c00140410700c0041150705030440361000c0c42800c04080c01c01c0700e1100812061307408102420010314120042d0000c10217072141c4201010860808030b503503420030075014115808901c9400464003403a0b203170454881181c0b8090758501c0411100c40c410050f507041c0e6008800100c80616140e2204045940d03000b581180c032800844864002c203007008034043c0e01481501c010282250850824100b0790003802c100d1035120011140c401840d0110020800100a0301031129030016090755101e658809880d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 477075917 1250 477074667 477074669
    0x602030a0c08060a0b0a120e0303010b030a0506030307020f090a060515040e15091f0e010909050607030c080a0b0102070b0705160806060130140105041409070905040318030309 77
    0x80800e00c80b001003441400c104424a041d91405a501490302d000180f040d50000318018080080d180ca900e540c109100301400030758024540113031300302d80700d003042e6080740c041c4d850042c941c0d80641d2003480050b000d1399461040841020056500c0380341d54442d50f640301d000c3c1840d5040b20707806c210072045940504040e50001c1003154592020440c03030380c480c0384111084403030003604643d00031014808900070360201480c035014111052284500550b540500780e950340c0090b4407007020207076100404c00910000780410740c2c0c80703016490108400143c200b805025404080d012401103561340f5030b00300b10799000300a0400a003003a88170f60303500d40d059480c0c090b58502500c0e108044000b413a500014850100007441da026160585460000d180401c2c2c00d075452180350041c0030103081d0030742c0b81b00c00002000e10130324620b1902d00b0b000000c250b05100a001c1511015420f40184000040070041201c10200b408410f840710000081216200d40c01c3c102c84007400181041080c007410b1200000b09a00507170722030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 477077167 1250 477075917 477075941
    0x9050f0606131b0509130c05030a0c081605090301180b1e04080406051e0705010b09060d03080103231c030b010801030312050c1608031b09030a03030506010c0602030a 73
    0x1001d060b01940300c50107480d80003c1c240203c080c40350660030014041d0029101d05407000d015030001741d9002d00d25006036041401e01c0300c04a000002800000c500d68001c0031481081c9040880d01e0381820010107034440000010794007000320205009141d0360b400e4102c14260b990110001000f52624140807141c420256010481c81c844621700041c8442e10720350051145800220720340c109468101d080d5080c1d40800c0043d02c0403a5900100710b02c0075070500181c14418004c0d030001034004c0d0246c1c140121403001400940c071034801c07542c3c030000007030380031400c0b0b41501d03801340740d01442c03800201010707041034440324a5581c140180c01269030b41c540000410010040e15960030301103141c00c1d50054070ba460080c00042d0006080ca040202541001c2c0c0003607410501d8080801d00e03021000201c400818a00c0d10110345807100082400031080c85491005040c400140069241c03441041c00642d950001210003800d054881001032040da004090302100710b074110b002550340c0c3ca810a43e140040c85000244 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 477078417 1250 477077167 477077179
    0x9060b1b070302031b0103060e01030b0603070605040f14030a020306072105010605090d020d050f010c02010501090c090e1f0b0307030c080c1605070b0f0421050615010309050f0606 79
    0x8000e011000180007421281c018001d4103c02850b200c840341d5054100c6411414581c0b200400a201781c580341e803042c001c6006083c12206400c1a60805040840b2940010104981031000744181000c0350300100c1210409005c4090011140b0b0121381051408180694180101002c015a460308501c100c100043c00071054087c50007040e803c10102d5000307003e4940051401d200544250a100c0c18422074079000821020300c690084da101803500048240861550b5100c220340c002c00c540901409001d024044001c0c0900030003030000420048861281c1da0300d0000e104045042d55010190491ba0500c2e0070034985505030301c030328030061603501c1502d80c50700181c508501d52043c00c0c4517280303650081000d000d91524044801c3c491072002c0c18240410b841500900c00c00040c01070414005081000200040c16159480c044d8550503040030300e4628004012a1017101d00055408103850780c4c861002d00340f0100803403202c40120010160094004c04603c9480c180001c2c0e100001271a0340314010403160 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 477079667 1250 477078417 477078457
    0x606080d110f0a08070f02030c220c09030b07050f0d11071203090b040b102606100e01150e060a0e150f030a050c0f18010f0807050306120709060b 64
    0x2d1980c1c0d45200703020203845850140080d80004041228000c04907000074121140e9400000000300e00c0002d002c60680d40e48042a102542c0703040c1c40c02043c2e9110220708050450a2842d01d502e91100e0380200041c08100000880109915082055401d00b4064078000c1001842220041000c1e40c407080d01910282d62520344041c1d423074800e000e00041c441e403088403803070603481d6665081c044040c05014045040b00021010424140c403000e44001c088641070038080b10a9045121800d140c00039103810300c96038001d402445880c40441c01ea074115040c401d0f041a0517040f44404403009881c1900603a4010000510700802315403182d042e05880004840c010881d051559540e000f601c100c1c034903214509810700000708104010b0303006076408080080301d6440c040c0d20143c211603540c0682000c0404540c0703002410b4207544d200311b1040c20880c841c1042e0301c85081c0801c002d0300034000205201d1040c00c12000c0d0145206051048a0040440c6c0c0014400c00344c6920b002442c582152400001c845403141d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 477080917 1250 477079667 477079693
    0x1c0503040e160203180102190605060a080a2406171f050114060906070b010b0a0201230103020d05120309030903100606140a1704060204031101110d0c0606080d11 71
    0x2d400780244440e4004501e0100c120410f40e280c1c00c010701c90141940900c02800e42009400c0c0c00c50b00e034080c411000091a0300c5c007102080800e1123690080803d950180e40c0000c0051058100341c031004090080d100a1800c0b040e080c40701412880c0c1001803000103131000450800c800150640c0e900c14025062262411161000700440e41d00348111031441e10818000810303814040d00030010804041c04d114541102d82e200e241071810284d0005503030b8000080c5880c0416828030451192442d0284000003100f103803104140580810300010384200112100c660811004000d08884c001c2d00b01c1007076840740ba101321140c1d12074100000356400303070041001c0120302d101c141c80f0350000e6401d5a124101c05043c41c680080795500300420100c240009a8900c04289105d400540c1c03045100d10005070380c0f0781c11840c256085604810019041c0703c01040f44c0c1200340004202d040d502102e0340341845a10102e400d208019100d50b0b407105a95008070045800341c10340c004008040d209105048039454002c4030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 477082167 1250 477080917 477080941
    0x30c050d081603021305040501030c030c0b0306150d020c010c03021909050306070305071115100509060a0303030e0313121202060408030106031a10020114150105181c0503040e 77
    0x2c03020a0318400c0b00e208005024000e81c090510441072040104c41c45440d0b4000c1021140283c205640d03180180d8020020005100580e0f805444016605400e600703060000c01d440007004604540e0806000c910715003900c0050b0305507a000491300d0000e003d0100391103400750081d44141a2a8164480790400078421360052001d20100d4002030000c0c1030070707075801da4224010300000c4c001c0f908004018040e20300c1c0d218100b101000c0a0301142c00b031a402d040030b1074520b41803c0e550740054014035054040005542d60f190303400084130340601740407030060b1307100d0540d41c1907118070b482d5500744a43c40c10020a103001c039003640c2d11103580714060300110070081d06030036a0743d4201186c0061001c402040144000e504c00e07000a0080c4e0384250803010f02009180000e50b1210701510500010307903440c1c0a40080703412004c0e80c41c1c0c111000c2d98404410046000008146204050104c03040c1e100c03504040002e40c0f914410410340c081210b4003207026402d10325095440c0e44c000e10a26035034509050204204240701c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 477083417 1250 477082167 477082171
    0xe100309050c06070f080403150f05070f080c040b0c03090f030109021c0201050f0d0e0601240e120609030408060c120f040303091e0204110a05030130030c050d08 71
    0x1c10000c10091a54034100141caa01003070046881d041805126800989010081c1015600c038502010003104458042c3e01100c100c1c01c5e0f1040a182002c080c4824250030106410000e241460044810b07550032280ea2a14880c41d031000010740b100180d0390a0b04100070000d0721500b0b0040303c1603003d60391800201030903a0403104010350302c2890b055900060705812810382c80c202e48103040c0207091100d5000100c00c07a811031017503140c071140c071741c490304d10032030b0050010501401d400180c42000882005118114454500045042c0400e10101081a0391444a0503141e034041b241100e041d46014092240c69400520482c4000e1080030082242100c2d20301c1644d21084510a415040f0703603078040c000c1282c0780082c2091f02450391b5158807001158202540b0002110030b46100001410f60340305200031960081d10744c0c20101d001b880007040e11a803210440c6d044901107002c01041400981c000c03001d41c1e0344151045c16003104403900e07004042d006440c1c0c030742a030f0140d001d840c440c2410385000da03102002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 477084667 1250 477083417 477083423
    0x7031104050c25151d0a0507060516050a0303020c15060f0f01120606030b15040f0b0a090e0f0a140f07110115080f0124050f060c0d0e100309 62
    0x5104405003040b1124000810300f20440c22911894000d03214080c100700e1100400d461503032210004000328504040300314280f410720005210035034032921034a44401c0e140c00345104206001030b0310405e03c800f180f54040d90350f41240c2555290856850064000d500116800401d8015030a400401881441c800741c855103001e04020160003699007001068480030706c2450502050441c00c640c4000d4078072464014003544d0300c00050503000b84040103607070014201092680c000410092008442c415651000c4880c10340c5400d4a41d0900f840a44540030345411403003c02403400c2c10001600d049544d154090705040000b00700ca11014510300c0750b049411240c0d195055402000704008a00c01c18401c0540400c0100000f0449101d0801003003c5001e580015425400380c541d800c1c4828082c860007042000c0700803510083c000b81407001090040503c030306413069000303140741c030403980325031048610f03403100c8605603810b001c0010005080b0448161520f4042c81070030724843c001c1070080c850083c0e00c80d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 477085917 1250 477084667 477084691
    0x5040602070b0304061413060b10020a120e0d0605010e1003120f0306150207091a030a0f03020102070b0a231e0a061502242e170703110405 61
    0x10070b001440440f0b6002810885440d65076003035207201c280d00d88200c24051080251400441ca8160901030b0560781c41e04840d03803060501d20310100400790001880c00072076a105078450982980010261030300154085c6440e0004260501001007124941c00b842c16214a1200c1840039100c01c02030030a80d00c207600005110031980c0c010355600c00c0c041c51382d400d0420301900e8041103441d00d600461b01401175006882c0c000d40d115070414802c1e03c50a0040d845156091010307102c107003900f4000642d4a8100c15005005461421a00014580300303404840303c0d50780281e144605800c050340342070000d0110440d019010030349803403041e0310514440002405508401c05911044900c8001400604006401c04500c0740c0e0318107001502d040ca02400740482280754024045400103003020032003060b0302c00d00d542c1c1d250040d20108070b10303240a0380310b2414050807071031089090045100100c0130345905800020311014403a02c3c203a40c1d940000354540c02d5a2046103001240c00c00c0d0b2007884140e403c240c540300e541070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 477087167 1250 477085917 477085919
    0x3060c071b1d1302100c060f02030907060f0e040204030b0f180c060a030906110714030408100903031524020c090a0b06070611180d110103020901031e09120504060207 73
    0x1040e0648465000007400f4110604284141c1c0040c0020140c040d0342d20104000c4480041480054407a00c100f054000c002985075103045089191248064001e113024001004911a081e40c030449824180c0840a4811907131740c0e48074200300211040850350310a81c0c002d0b03200003c2120501d0324420a141e00000c0c004c040c034400b203008000e2190002050310081540e1080e4100c085a2140540800b0407540140c150350b1341325900b070007002007101084a40c00d651080004003e144c000055584c6420720880c0005407403161441d048000c0d06c0e910800100d1843c2c0c01402003001e4100c4030700c18583c03070360001c4900d5200400d0202a40c0b100c28060039540d01c1081b91002a580c28030680001e28406002041d4501c1c0818a1b925001114040307041e0003a244404542d004103004224a0505403000480780111103030150b41c1c8140241d0302c0b030445a4105500481d41c0542a40030f81c0280c0040d2100b014101500c610400c5400010f06e504c00d0180e41e40000c00c600c807000b160090041700c0c1078a2455011302070745 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 477088417 1250 477087167 477087209
    0x612060b120a020103110c15010e07020a0302060403120f050403210c0e0907140c01020a0909060302060d090203030c0a03020a02091e0109020304080912030d1a0121060503060c071b 79
    0x8200b40004411b40000c00c003c206140c0c28148076881c802020102d150345207504084406404060080440341994088066100401c0d000644070f60320a034503103000305081c0e070200401c50141c0615080c155455082006100403d500500700082800903800f054a5000c407044000c4207031012a020700010802e2a041d51515092201c03541ea48260281080e0291000d280002005580818204a0540d5000c500540e003d90b010240b4070040c800501c0c180052811500041c205200b504d4812505a5441c500b82c1c0840d03c05009580800180c04240c1da1a80d0207810069200d6280002c1244520b11040014001806804d580b54035101034566104581c0e01f0405240000d600241c4151440d503024401002c40e903071b4001c1d0b10600c0000c0c0a006d50b80360b40550300d041c03040d25503078165181c0c2111441d920b011180d9012040d4003411020036840c0702450b007058a0700d001810641c1006801d40540030800001d06201310091568911400c400ca201016080a2070065a024000c0105280c01e001da64011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 477089667 1250 477088417 477088421
    0xb0f0a090504060b0a0305071805010b0a03020307020a0203100906050903070c17010204090c0e010305070f0203160206041d04020a12050c10020c090403112b080709090612060b120a020103 82
    0x48180f082d1400924607804400040031240c480d07108940c19445208c003801340000818401094000c0ba1500780600e50403c1c1800c40c4c5802201e40820805034003000041c00702d8801c00c140d0020580103801c1e120703011019280503002e440c075508140ca15904080124030310a90010460ba99642c2082d84003649a0504001c02c000480030141c20030745640130300c0041032000c01c62060000c80c000507240c1400d05c1024078001340a44400034819028404c07401458598a9004000c4030700280e0701c00c1580340380b0000b0344006280d60049030001100039940d001c1e0b18210b510014401c6000390300072241074100d1541c9880c071448071940107600070f1468000d410084100d0404207407a4440c401c3d5401540d044c0d0f4807070004075216020803a0b0590010725011000c1c1005a802c3c8061103038100c40601c1c50100c0c400c10900c2e44098450410f80104005a240005000c9442280c40030090f090010050054907680c1c0c1842c0c0f0520312004094a00f18500804070340149007281110f1030660001000c4c0035280b042c2e40040d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 477090917 1250 477089667 477089671
    0x14060405010f120614010807020109050a080310090614040e0f07050d081b0a02130903080f1008060412030c0302040501081306020c010f05090607051c0506150703120b0f0a0905 77
    0x309014043c511182c100c480c41c003404020380320000813180d00d41280c0340010014500602008156450000c208010610105404104542119049650392645a0101c0514035260300407001d6500e00000400c071800c4008070407604107002c0714184503000240b41d80b90380b40d1112041589441e40400410030150a24000c035058881c042c04015003050380218050b0404218218180c643c0c0e0001c084020031441d15200d12095448015410040000c19540291010030042d124070700110300b0b98000b0312070b169200c854a018000607010ba50320780c10145400c0f0003111000b49800c0c0840d0401280b06030f42d074824400e480031102c059598403125203810a9900c0e240d000e04101381c444d541c0800020041000134014100001c08280d000142071510032000c500709074002d0842030811004200d07004c1b802c202090800710ba018410030008498480b140040c411a001044000015201103120000d00d07800001420203808405014400c040c074080800c214070b00c041084c961700080c0345906002c2034482e0b0748826 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 477092167 1250 477090917 477090947
    0xf160c0201020a0f03050d0e030a050702010e0d02040c052106060a1107030605070e03070807051531170607020709090611040f05100507050a0b0c13060f091406040501 73
    0x189424800313803210038858030b100006a022030b400050b10703416115140328000300040c021002d50304002c4000401440c0d032160b880080d0402c40c450b0048402c950310340c004808103c1d4020010001d924410070041c00c01d0b005800d400103410a0202c502c0036580d08507404130301c1400d005000f14902999180301ba52081301f21340000045102e020404000240c01c7c2c401c0c00c0c0174030001d80b11041d041c0713800420146410032642028142e5040b1b85410441e981f24000e50068407252a1001510f40c101c51000c54a154080c03442d880c509050b00070b80e130300380d03140c5900100c003a5444d418038410402c03020742c1ca0381e9a40400fa039101006030300c0300c94100200706059024101142c4503400203e11020b5078000d091154100d908210002403211500b00715a241150411007804030a0a00906201d030b6a110a502c44c60a0131b80980107800231400140b110040354111400050700603410300d551b0340c03901c9001b0191078110261201041c00d03481e02007075040c3d903d5440d904c14032004060320300c3c0504000044804d901510205 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 477093417 1250 477092167 477092173
    0x30c0108070302190210110f07080306060f0d0207031e0c260d0c1b030903020f0402040e04031101050907030c09020c0304150c02040513110411130801140f160c020102 73
    0x940c0b084000c000800c50714030805d078002d04161074600204401c031042c100b283c645040040120080d5070101d40700f0b07180015000b201c1a510303a0354041c0451298810303042001000640080d21100c07006650340035004090007503550320f0307400350725092003207440110000c100003044800e035044001840041d6141540303030218466103000943d10080e05007e82110300d20100403902c0384030620b0402c0c2c2c000310707404c4d803414204000d41100b403042e18050000400c0e400083d000f00d1000e040f18041e81c86030b070101c0d40242840c482c0c400240c130303003814010006100101904c516508080c04181101c00004681c404e880c0c004440c200098501806e4100942c091161820540821b10002820401c00d1882d6509100c03142c07202c1c0c000b0b00180c4100302c1103c20040c2111a980e54031040c450100780a08086008030f0070507500082c680c94402c4096100f0700860b501040300c41c0c811000465446810f41007505242101d503050140d81e12036401410801d0000c1b1003d01c0001040300c440d80c003592054185154482c018015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 477094667 1250 477093417 477093427
    0x8150f030d120c05040509041202161d070203040503100209180403020d12020319020c12041e14030a0201180b04030804050f0d0201052b020325080105030c0108070302 73
    0x8030303081c003007030007040000b090200c81421510a11801190310140092030300c0d80ca02070902000500e9441301401c050005c1c00055840c544060080020010340b44d240080d240f0546c0d590301c0c10078100c03029848840c0d4560307522808140214000000d540c265078004016148000c4601c00c01c4000f0b41241c1440fa038000310000e0b90f400445055141c00307004034020b5007e00201e6400c030318044c190005660b4004d0340d1a10420400c2240c8a0000042540042007400969240927150401d032030f1540c0e9000d0301520030350000700094200048072240385c124040400b4008240d5607448020440c201100109405070010092034005601c140000300c4191590115030807020749600514845030000d0704202d40d030050018007400b252503e0540500150002c80d000c49120354541e0000300280a030a125121201e00600c04075901080c16029418860300d0300303411912072a0101e80e48140c0641002806130b2588001e0f80c036000c2c42d01c03c0c0d284c103043c1ca001500411040e64048011900355000030705640803d5400c4c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 477095917 1250 477094667 477094669
    0x70e010506090f0631050d020d03021006080706030b01090b070b0c04080d03141602100f0609020f0403030e0604030b01150c050118050c0d0b0105270a15050603060108150f 75
    0x250020f400303e0a50b01514600710a9101d80c032088109075126200b17204401003200350340349201d001205038141ca401c00889558a010303450109801062601141841004207251034001840401c0340c505c2e50b014050301d030314000151680507440c0a50810150200304400128081032002900103058400c003c0c03030503503603214544c244982e150300280000d4890103450403001e100c10303200c0d80001d9054100603d803440c003000a99100c203c0701080003581c3d1207102950110301d07954080001844102400d6548080c0c081c2100d282c1e174054082100400d03040e802e5180303c0c0c100101920180ca130310000311881c0e80d0034a0740490740c00c020501c0541c10420a2801900000d8080c012000448011203c103030006039546440d43c180300d150040b46005406410404001c00ca05030000c904440742621941040f4450b41ca50074034505205a00c0525844210140500b0440552200300302c410f0114010801030348400c2041000c0c4800da0301c10780000c14140104528217541d581401d01d0100040c400c4e000c06031400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 477097167 1250 477095917 477095929
    0xf03021c0b100f0609080606090405011d070e070c0c0b03090709020c0a06060b0906121503030a1d0609010801050415051009140307060c080304050325030f02070e010506090f 76
    0x141c03035451081010500f00020504000500007408090800001441c10800500c0d80c0b004024641c602c5220024045800d001081d400013400391500507138070b40052010400c0c41e5031104c5920928440c0d400d40c40c00550301f54402c54800d000b640d40920b04504052400840602ca82c1000d40070711528010b0b448001240b0401d88000d1911020010140c8004210343c108901110040d501241c0c0055042000302055a43d40c01100e441d190722103c020301a071124a44060640c04038440650103100c0010141e81040d045416030500c24200c50b02e04040e01e04030000d004490040c402c81c1408265002d0050056140c141c0200000f403010031480c252081e43e0b0b07800241e884100c7c1c1c2046021514020b004d1180300e14940c04d1000e0001c05070000c02015241c820001e00007404040040c018140100100342004401d1044030046a4604940000304101c0c0328105001540e480080b008100d4940000d019240007003a008100c5507800443d1388140c2c03801083c00210350000f20307065800144000c1554481c0c0c0c5503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 477098417 1250 477097167 477097171
    0x112061113030501180b011503020706110c060106050906030f06010c06090623060d06020f07060203070207060905010804050d08090a020301050c030601300f02070b190606090f03021c0b 81
    0x11050111500e00d5403c02c80c2c02c40308005503802068050100003800302e00c800950f9030469280c1c4c10049500858020300700e0080c09100341c010040c0b802c2400080c1c05006660180c20004441800c1d5249030340c0c0c481099480f48941d42849800c1181880007402803600321a0265000c003060600000980003690346408442e501401203030010380c0ea00d002c042d2500015207070070704040807440244080c10100c000032445c400b9010000c0c0440e400160900304a2176050a071401c1e164042c0d401d6481e800c1060020751a420140240000100c171079400090542c40f40031210301983d0010041c142307003c5101400c850041e03004101110300d01c1070400741e80050b2400d21600348200d021a000b1074590030700b180018000d0240d2010403209030666503400c01102c1c1010070101400c1a10703070001a44242e2030004030064000c14134050a0740d0b41410821458101c040465030343c2d6004010304001c0c55817108410742e680700c1980615100c1510b007400506c014208003003c00640c8101c2b600300700d1741407103035650011b5403001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 477099667 1250 477098417 477098437
    0x17040e060628170f0708010f0311040c020c0a080c030c0f011b050f3004030b0708101503022208070b2d040f05060a140d110a020c031b01020601120611 66
    0x1300300401c10101d51101900307000d0300340503115510841c42c40d01c41110300f03221309522621555440440f10f05041c020008591211000f41045c05030640e281c02203501c4094500c8c90500074020951034100a1030705141400d0000e034140c5401441100c1e030061080c00c4070045004460300e20413007006a07000c40082103d1030440449140b0b8400b84074403240b00d0304c1c0d00b680c940c4072400f1040003400306200040180ea90386601c9140c914098007d60390b00e034041d400c038140a602c65619082c2c0901239042d01c0390300d03800404090700c02d681d8045141964a10061640002e44a910001d8000f50b00070b0106402d400000c3c50700c1209202e240c0151480358010203414614009201172075800084d08000040c0181001d2006240c122071b01810b160741c01c04003801031013080d01000e0b03136020001102080c1d8200c3c0da000a00d000c04c0a947c240c0c44424400c1d000c0d43e111920704100e0310900c215040b0036220310380303000c000c0342903c4181e01408043e440c00c00c0c0b0703040c20345000d6801c0383e0158658241021101c078000240c005101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 477100917 1250 477099667 477099691
    0x170c07060f0e070f05030d0c260f272103071e030206070201090c09050c070b01060306091a0d060209011106070905040c0e090115020a17040e06062817 66
    0x200d00b10045101511541c0a131b4001e80001d685074264503080800960300c5a040500c1440c0b868042d640f0f40d60f803643c200568510a000415900f079401e42078000f03440f808500d90b4980d840c6404955601c0540caa440c1040742d804074408840a0701c0b002c204000c0401000d5a00489041c54029a55944a19015544003104151051040051642c108900b070780012a50008116441b620b07106d1040c4c10410f400390704080c6840f4004283d0669201c002c6500c0241c005a210500d540c603400010003030032482c1304000d01d0500f01111302103003a4400e004411010b10003031203003910701d00390369504003e904491100ca044c0038510b40070f01030701081405454840c0d0100c0c0d49900641d818003080200300c0381c400013403c0400140b4030240e41961294042241520003c1007074201400003114203d01c0c0800888009020040b111030292900711298003074000d4a130351600940c0136170384081c107100d120f00400c030010380030754141c0300d5004000c401000c0b00001020742d40342c5042c007a09188c455592141d0250b440340c11041c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 477102167 1250 477100917 477100919
    0x1060c021f051312020a051008060904020f100e0f0402040810090c05030f100510030f030c020415062012070f061506020a0203070503010605060906031509010611010606170c07060f0e07 81
    0x715002e2600c0300900011030784120908c414620043c180d0070001c01031400b4800e2003001c1070a555030301e00f0b551070709035000f000c0150043d5000801001d00c40c0c1d402d044d41c01011041e2108110b85094002c0e00c050f031b0b44400080821054122114003e465521000d4030101040c03500803807540c0341803222489100300ca200031700d13607021031441c0c1500311a001000381e4240010000c040c800505058015460713160986441d00420341180002801403800391040403070010420b0000501e07035003050035241c41c4842c0715004014080c070f031203000c0d440b00e642040c06115000d042024000040340e4800d0340c00020b00540000817841c01c03070066205000d0164001002591002504404605d010450000509020b038002e210341c81c513010102d14180035000925200d8032000c40010203104815503c13880c030440040c0410f98a503900c0202828a152184075582103500380480820041d015040e0094440650b0807200346960700c0388070054032a044250101c5001e0f40343c989000d0b4110035802010120340921001d810b140d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 477103417 1250 477102167 477102169
    0x80f090d1a0703090f030806041103070306061403010312081b0a05090405130c1a0903070312110d0504030314090301050f061206011805040f080301180501060c021f05131202 76
    0x8100c002d0812080604103448100050100202441c240d03a2505007468103444001c0090003401c150850403202d020080b08200806516403c0f030811201c2c030b500d030f5000101c0c0114a91865100c2408043c280e0410040f450010300c1c4110111688000000b800c504902a002d1a41032240d01590003000000c5020421881d5450244100e90704a148650441d4070300e000d540d2020b032110b0b003e11490280403411031400b00301d4400300048604420008043d1b80d4080d40700d2801803104985d5464403400103031030711104c070844c0800042c4001140d889440d034030b0510f8a1940e04903190140c2900d481c4c140c5409110386c2840c0d88003409424080c44080c5032550680c9010001d0020f1a071400a9103810f80c0e0141004101c0e8820781074040b004910141000726140d9214108a8008925008018a07241002000060701c0398506545000041e1031141444240d986110484001d82c0851004e035000041c5049803001002c001c100f810b120800d4103080d13040ca02d4500001001c0801a0b1001003400c15a160b05811 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 477104667 1250 477103417 477103463
    0x5120301090c020c0f04050c070c1d0601051201050f0414091b0a030321090803040302030c0c121009171803010b060a05040b0901140307020a03020d0509010c080f090d 73
    0x41040b01e03100034222100d92000103031041d01400c040601a40e602d60216080408210841c1d10381c40d000221000c09694510206c0d6007a00000000e42c42d101e203123008076420350b10803011600f1551045808100c0d6909210400c8540000c29200a80c0a42e45482c030f8013155001c0c034400c074443c04100020b0480010740d0740d801042c0042001415200e060495170510001360440150018003010288d20740441844442074002403812410183c0640408001c20042590000040c62403400402c00d0354800b150201c00d01c140000d90116582c10764008500c2c0e403004140c6580314000460140050320180c501803d50300c4240e03400322551888040501c03510102c141002d0085840030340c0c4c1640c1961410320742c0707080104180541e000341d482590002420b101543c1c41150280ca0012001100c0c0b50750342000c1c1d0002e0b680e01498401200517018280d0100703d400e01420945585200c1a103440c251084166501140ca07400340042600602e0b042c000c40496844030186406128400d00e248152084c1482d84428 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 477105917 1250 477104667 477104681
    0x3140d03020415050c010612050304061101050105010504061110050c0403020414090601051e060417100504081911070b130e04150225150c03110a080709030512030109 73
    0x34140108410040788955600d01a03c1c10341c10b10f0540d455883c2c00380d416014214030340c084c4568031004103c9401b07102c0040002e100b01c031070315182d0171f200c041d0701c010860a0f50030900c146808a2000d020410003680240b000a82d074030140c1c01941ca401286112203c1180c0040d603206010703500110b814000c606144c4207030701d03000f00003500c842107900e00380c8401c50f03881030140203103405043c0701e10030b000d4401c460750b40075000a2401440e8603116074880720b29007640c10114a0140c154418541d41d1840100300d441028041c513040b82141d450030750412608820034103a41c0001c0304100401d44441d0a0100600c504400381042d082d41d190350703070703c118009000303800c854221040d0420b1a00a02001502c1d001103505036120410015858003100c1c4140030b070303004030400c2d02101401c0111072070003004020205415045a120800c100087d00424120201c0348070041003816010308009010420b0700840015600a040f450020f4a1070385950f11107040c8a4050940c44140c0b90100040c00803203c00d000c0d00c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 477107167 1250 477105917 477105943
    0x60f09070e121c0c050a210e1c0314040504020f0703020114070c020409140109030210050c1c180203120702010206061008181e0604150b0a0303080a150314 68
    0xe080f0903445069034540b00344039042d0510940c00a2101005410300c00d51b04199005100c0c49031603c007100101d11144e00c0ca11040c0700081c1c408a08036541d00e0180403c25904110458440910301c507075409461500000d0340c0c9281c6100148000190755842d40001c1882c9000c450150303031981da05160180c00e44410121982035200f2000400c50420b5003e0b0300003035865011207010401e091a805c110407615000e031800040365080448400c28586c000036088511356918000f040156901a480700302c82c0034a011440b0040742554401d02c110456810120244080d004403009800329540028a421004901c0c0c00d4041001b090b030130150343e0103201e520b40c04130099500029205282c50000d0202e0030042008094002d400c1c0e20174024a810011007003651b041602c06003c040307160210940c2c8d04030071203089441d0340c0c00903c0c00b02c038008035000d035802d40c181c06400003211500755502a5070040c001801569015590400c1e48070450300701184400440c0200139211000620030383c03483c20580300398003407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 477108417 1250 477107167 477107173
    0x307031d030c18100e010303021507091511010204050414150312070212010905060702012a0504030b040512030f06010e03060c090d020d05030c01241d060f09070e12 72
    0x14050580f00c11009105002d0109540300c11a640c0c01503040d4549000d410080d0a4003495001004041c1c0000e29101500711443c1c0c050659510020100c0c1c0d181c2c184d00820003441078070b5868400407400303215040c180594200000d030910361a40007241c01c4804214110780400e40c000d0070310400321000c026030f0540c0f1000346d0180051035501540310b50306100f00740c4000d015441130141801c0303174002036100041282c2e1010503608141400742e0024068400b0200b03000303100417840312003200911050000c900e585603640b81d10341010302d107441e40c0c22600d5000708151740d03030f0145000c24820b10351008011071060f812070045406a08100c1d00050500b02e06242103402a4418814404003013041c4042d155014070803699005032280d14404200c2c10005013500501da48000b07c4c4400480e030040d001000d56107039145401175011041400081c8041319882038021051100f01c2c01e0a404c00b150703203c16070040010b803202210504405c04103c1680c4110740300c10020f4400d102c800360600d8040d8440180c04240c60007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 477109667 1250 477108417 477108433
    0x206010509010611010f0f0f2703180e0106090609080c0f091e0f010311091311040b060a0210050c07051504051c0309020a0f032f030307031d03 63
    0x4203001c41c1040c0074110501044401c000e640740c0b000d40080e50080c2d00020213100e141c4440c60547e019222448960862a06003202c6005860b0002c601c0c00d801100c0310107191043e2a1603e068980a02a40b0007090f001030801d008101000e451900d04d0080c041c0d580c038a01e4040c90000003c2c004106608944c0d5160480a201034065899003104950b0a60407111060a61030300c0380c030002d80c841d00890750340c1a201e04c00304010359100303e015441e0480c4c0c0604145091540744404001d2070b2a4104ca944400c0c850420004000c181020000c0520000280c070001c2d410700e00700005080341c3c204404400040c2e1000885981102c4180503154111030180c0d440780c1001b00e540d4802c2e441c0d03d409204420580b14a500007070501c4400c0002a044101c414070141d504680004020040e11000d03000b40c0c0244c0e04110300090203040e0840070700440ea006690182c000b80040358000701c1c0c540070305000e450019280b02409056a060008003082c5100341c60304c0381c0c0c0646003070940f0805898080b00707600c69085012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 477110917 1250 477109667 477109669
    0x1623130f060c030f1e0801051c02030604030f0309020a0909060e03090f0d0602090910030c050d030e09061809160f0b1204061808030601080907060905060f071202010c0f02060105 78
    0x25140c504140d06041000f03454182030b01c100c803400c8004c07184045d002c000d6408180e002ea041301c040c9059a02c140c4803c81c0c0b11441550414001e001c0c03041c020740550000e40001d01181c41903140030b469900514002c2401d92258000034922403442c0c00560381982d131420b200d41000340b01c0c4200908651444061401c2050a00000d1720b0313840c24a8155000740001c49070700040042030350407103881000041c0b03004500e0411211501001c078060000701c48203d00c18201084074900b042500211946c195030ba03011541854003400b040280290200740c100e0b2929150921030120000d10612610a220050014003410805203002c0441ca1340204500b40703001005115002c0d080307007240c0d0015200658860f060304c0b1842d0900090001d03042d41d0011101015042c020440078000a5000744400d84e81e802090321004512507c945040c40342d170001c130300212002c201c141041d41c00340c5100d00f4104c9005003005031a1f101c0011031130a9641103801030f592100103100991b00300c100596200018070040c040e030360500c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 477112167 1250 477110917 477110927
    0x314070c020a151101051312210f0906050f24100e0a170c0a0608190e03090406090606020f030c0712140115090b0f03061623130f06 58
    0x1000f900084600708000c000681d0042042508141080300204900c0c500807081090401040c0790442e114054030401c00c140c40c0c031410004105c000c0f0344081c0c1c1000c81e2000715240082c40030b0450140d44648444426010421074444c251041482201a191602e807881d0601000c4002d1148404010701d80c200703c1c0f400d030307d4105901e510b101c480c1c240403080141810000c0c88141680c6d01a40c2e012100b40300c92030140f10301262400e1300c00301c259102c103a2181c454a066650b05421210a0020f075070050b402504c40504c0c0e00b1800044600c80e096a15101301170000c50159000f0390822400ca5032501d500300701075a810460504480400005507080146101655885203894443c5003a4004031200100070300152451480c01303d403036140200842c41e0b00300007054000040e8480c1c044500c1c546031110340b02d4240720071229041c04009018200550340d0341c480403402514000c00f1010001000003201414001021084409282c1c540981e11400b1402000103089140c1d0000060507249841c20000541c004c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 477113417 1250 477112167 477112169
    0x503060d0c0f170d0e0f010e04020409060e040210020c0d03080606040b190e150a14070c080a150213140102011526030a08190f0207030314070c020a 65
    0x44482214416035800c1c01400091560042070584051120001d100c00206841100e010226402d607403096035401c0f4190b0300c1c0e2403410240e40d0404004510600f00398880c0c03903000b4941c02c0c001c0c00103082c41e403100b15100440300641c1011003020b0301181400150303d40700d9484980c101c0e9920082c0b200d4514400484e0440440c00f10040034041c400002c00c4007643c40000740c401500e1401c6400e81c0700c0ca48004014410100d00140c0008101908030784100f81c102201d00c0084101c54141180c6071190b190001c880e1a843d1584011892201740000303400209000c151900420004004240c020f000e0308121810303910202d420040c1034410401841d500c10200071a5085510301e0300e10308210803902c03006034058500f5100c00701807a03400000c0490f02506010411160301c1d1256005500c00300b010b81000c0c0da074411500f542d0080740141001038a50704418400c2d9444840605020490710800f07682071060f40c000240c00c43c040381c2c0364240b02203888801e844141d8408034500d02082d81407019000310350001a1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 477114667 1250 477113417 477113419
    0xb0906070b04080405030d05040302010f02070b040b090d0c0e040b0703150909030302120708091203040c17070e070201091119060318050a0c0306050c1c0b0d020d0c090516050306 78
    0x100040a010310101034900502c5d0183c1540c0384024400c1005150f6845408200c1c00310b9088070390400d06502c0019900c09503140f94400030300e06030900e040b803001c0e130b0007100f400ba0303200b030341d040d01c10001544504020000705601c1003d0b81844c1000d14040490080040607201098542089040c203c80703120031078822030340d420100182c00701d102c0c00d04030080d00c41c000c1c50303030210411342c8240180d4540c889005485100203a01342c40c100742c40e01007e41e201c0e1200380c1e0040d0811048100078002407401c02c055140e0f00d50300e07074100e8000c0c0b5950300041d03400e504101c3d0440d0240c1d5445a20105102150b1102c400107001150540907646004800015000e0f403400380c2c1c82056070ba8140e113402c25104411100c0c0244c0c100741218519040c51802d44106400c90100300d0749581403002161940750707a841560124402c450b460300300a500b4405660041c640b0fa4040c65001c2e9007494800f001d0b80b2200c141c6105140070300080000903080c5150358048d50b8003c1d14a2a604140e08015811103034011300796900050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 477115917 1250 477114667 477114683
    0x3071e0203120403030906020c0d022112072d09050103020a02061f0b04080303010503011401240201571b141509010c0813031101050a0c020105010b090607 68
    0x103d50030110000c2c40c1c403842c002c0141748001240703000c1000004017024010b50a500300d49040c01c00f105034141c02444041001d00301242072240c2a69010b4040010381d0021051a00d8500f200d00514079440034a0590f16a0300c00030b003500703490a5419480b41034680030308402e0a0551416040300c1000b503440d40c0c0281110400010001426503045a1030700900007014040103242c0c54607221411a40c40b58004e1050b54803940c81c1021b061507d240c4c244505049071010030a041a0801d03290280041d40d10855150007103560707036501407020a41a030741c641384114140c00c540c1070340e88800e008944000c0702c6015124507203010002c0d440f07007840640000300424200c1d19004400d00c52072140d003003500410031302c01000c030310645181c8000c1040004070941039540e0080303001c100740ca80600f66400c841c0c107041e03035200140c04e000020b00c003002d40d01c1885500354803070700c0c0036410107030000125400c44800f03803400c105d495112008024810740c24000c11b0f016100d4030b00c0562801e40c14900041c0e203407149410040042e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 477117167 1250 477115917 477115921
    0xb06010c05010c0e030c1507030c030c1b06080609010b040b0c031e131509090c0c060903020606190b0a030b12151e190b1203040b03071e020312 63
    0x192048004654141e0300000030300c01d21002040182c0365210740d0564500910580f80c60880518040e03200d08103000c0e5a046a0346170000640341140c804050181c15014084003080d4200014203030105e9031103019248081424003420094003c0500001034038543c1b0a810090050061007080011101100d10b241c0c0079640d5800340034141da003527004a12001c00c003400944000801e0350102c41c01065114000c11074250415186c0445010034400c19001c900011a4070009200021441e0b1003240180c0c0181003015611100d5514041a90214030040f00143c00250602665040041031061a042080c0a40c030740c9c0d41c2050300802407801500c507030004050322021064820b8840c84250fa080990503802c1d10903c14001d407402404400030b44025014140440321408044011100d680c0151b8640180780d000c48820304070741c0060001c80e81003d6100490000c4030880000404c0240010000b40041c1c1c0d4484c0740c803d40103000c4000584010182030340d4034850085e0303e42d0100486046090105030000c03a0713 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 477118417 1250 477117167 477117169
    0x61b05101a06031504050709080d0c0c08010504120806030102091c1704240e0603040201110c040606030e06010504270302210d0b010e13020d0b0d0c090b0306010b070b06 74
    0x140c0d189280c1160040c0000041c0813142d1040c18500b106010191003c0c13055840b03090302111001014420300d070040d00b1403151801014410090142c0361801450003000540d1035403452421a802550110f0304900307492001070201e50406840c99010b04220021824a15100d02141d4082408441c564540074080520070801c662400c016170043c5036900e855849a4640006d0600502c1d50241c4844d152600380725589040e10071001804000e1000d000729080d82c0fa07660040d109400505107207811790213200c0e0800b0b415200c0c0d10a05008140c640d4000c21fa0b4001245521300b02a07060f04018022402c10f440307512614914200d0504000d01c04886401450031810100d0401c00701d4417296802c02c640c003620a61001350b100c064040421455000c00c900256500191540c3d07002c1c0c4040354024244603c00c0030b00c8841903028181da41a9a4804070f040c0191200150552004180c22601d20b0690703001400000100e03c1a0140d100003030300140060350401d1000c980600031400c008040078107001c00203d103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 477119667 1250 477118417 477118451
    0x310021b030a081f0f23060c01021e03071b030c020915120d12091a0705071a040b0c18090f071b080403170f0f04061b0510 54
    0x60100c0300400d4a44803405604010440c500039112880105601d03061548030b418545803071821541900140c01026262022600c03481002040344401c04100520205054896030001c091901e050380c00181d6a0350a21a0590060603100c20031a003c3e8041c1b04120949800c9071402080300c0d0032450b00030b0410114681141c0001030302200035000310740401417007620381840e1004000b0050131102041040e19010081c0d07a40c5c04500000c1d00014608400c00c843c0200c0ca40c071884816001d210340404900807110b08095040c0240c0d6010009640040e0220500c021f007001c110030748606000e15441030a168540b100010005410508002c400040075a4092482564001e2940c4003501c0e580c1c171881c1100c0b800801120849000d8040f0300620383c07000c139141041e8203003c880d9901134203060401e420340c1c4a24048a1001c50051880381e010400d40305c2420031030001c2c11005050800031303540c5074202040108500090760084496400ca01d2061001480c0456000f0084001c401e000030303060348891045030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 477120917 1250 477119667 477119707
    0xc0d0807080d060b070632130c350714060408100911040b0d080c0717010c18060e0907020712060203150a06020a080c010605100503061003020405031002 67
    0x34142d01d007103c0040c55200b034102074031485014080402000e01140c00003041d810b03001c0700044070040c01818207903c407510641c0140d0041c0c006442c1c150070100d16500c403090010681c01001032001c180c1e01a0344403424540107100300c65482c409580d103036820380030900d5031080503002c2c0652400d8452841c0c802900c4490a03100180801d00407109090300c4500ea034002002c840c0410703184100d00e4035403558281814010609910009460000c414a031611204150b4001005a040c5c44c01214070015228003a01404849505101c4c00061840350303040000e40b1070f05e811610442c12441c20b120410102e0340005490441c41c5013924150140c4d501d0040032401d180342604641c00250264422805000c3e0f268095441511480d10303204003464840d00308044928248241c2c2c0059000710715010001c0e07501c202404a05200200101d0090f40b103000040f00389140b588001c00054000c01003041038a4130000012400301c25040841c50641400c0101c1d0312042580b0340044002d0700000c2c03d803054a100c0007004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 477122167 1250 477120917 477120937
    0x110406050f0d110307140a09092705030a02070806010f03020d0f1b030212010b09070f0309080a120b041109010309031b060623031b060910030b01020f0c0d080708 71
    0x1c801c500070001d01d8005540000002c0c001ca41219032002c6c180c2d04031032041c855a1182c1d480103140c4091200600008140140062036074260195101001c040210704d05214501440c1c850601840081c80c01d22950301a90740e50388240010402e600c0a08002c03001d4a0301501c08440a0250b400c040d4440c80344c1d9140100141482034401d032a42510107503074003c1da8802c4030541120741920b01c0c46802ea441080c44145d103c05030401165401740500400e90300388425040100342e024035521008042d42014400e034001ca61440c40030791607070315144200280310a040710100103c5000c40180300403400f0f10594141415503d80681c0f090500070a2910322040380c45c103400d0100e000621700000a07003500d2080e59000c2e000050402c038040d4103140000c0c606c1c10302030004c1281140710a04480c0c043e58014013550021713010003108a160b100c41c1c107a03140c400e00d181c901040508546000a18180307501c0000c0050f90451548140c003503039100e07402007000d40c00036002c91701c44059051078426403240b80703014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 477123417 1250 477122167 477122171
    0xa2a02011409030f0d0809010c170106050313050102040311040609180b0910020d021b031c0b01031803020703020f060705070b030a0e07080604031202090609100e0307091d01110406050f0d 82
    0x207143d545512182c4d40b81f042e016040240124a003c582c00e80320079540100c01ca06850840d40107000c85407062002c0e42d44003426601d100c180381c040313444450072039115800c04d40d503403008060706541e107050a00580e070090045c2281040002ca5200c00121455008840281400205008500581d204000e1599050302d070400c02c55882405e8400b07100294030070305d60509245101c403c5481c043c80302000fa6400e5021005048044030b0041840200401c4440c04150505a403000380c20740700508e0314a80c24400b4444e070020404a4210700400284802c01c441c0d03544541d00401c04200000d9021a14008070382c0e41c0707041d0507100e032142039195001d000071200722000d5105500000031425000a0b889004034000d40342c003141803101d100b640c0164440c260700302e0b8100c00f04025180c0c150501840e1720000700c08030b2170032501c0c09074000c1c002424180c1541c0103103c0c050b1100d100d040d15425021206128010240c02001746050b10818000b460203207110350002c0c030401207140c4601d021039008a4512411140c41 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 477124667 1250 477123417 477123433
    0x21b03101404050106150c1410050103030c0209061f181509030323090603070909110c1c0e091005220507140d110408030a2a02011409030f 61
    0x1003501d032031040310b0503141c542c2841c0d000030f08070095400202c9142e110b9a01c002c203400c1d00307459240018041d440200303418811181c4008141842d0700c00c95002c1c511030740d61810550014010440c0c107000c090240c511980030082c180003c04034a10344041e43e410a030600310310a0714280d0b481103920180f51b2141e148030103452281040d01d170b030210500064034482d49450445a40441c1105030700584400c0d40c596045c1c0400c0300744040d1402c075014541c0242d0a00e07206481c15150f5180d1710940700d02c0d1040c40307107a6402060140b41e8040c24020350b1104048080300d001120440314000b4046941404064050842d03000401e440c05407404200d00901405810509400300c43e59445501e44580302610120900c0c0c80c1c041441d003031145a880341c6195907400c03407906206a91403400001e042807041c40d0034903001044000f87c42d80c0140003130107614200e6111420b0343c0d90030980410b0180c07a0522441038501071941d003400142e0304034070ba508030b0405a001704d07615200c6481c0070901d40050054440034131321805c2c074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 477125917 1250 477124667 477124691
    0x601031802031b09010f0302090a020c010f060f060e0105070206090d050a05010203090304050a060806030601090c020c0d0c0306150e0c0f0c030c060403320309030f070f0c05060307021b0310 83
    0x615105195025218130b0f1450381da45444034034112450100944c02800c000c0418030089254004d0001d10203448000555088444508022601280e000343c008ac00012030400003650444c0005070751450038207210345007600b507034005a003d200303218a0318800d64035103114400f4000b08200200449030b00000855a0b0b0070007041050b5207030841d00c10240314142c07500011502e6446050040d000c0d41002d402454941d080c40c40d19009864070444040441c030582c036411100e039880b540e06000180c06880d0800b9040e043d4106402070301c0c4104400d10460555510420150080251081e80700822441080d264140380c400e000780c91041051a50b6180b201185155415070003088850103180309449812003a4503291290708102007803003600442e00070086091075107a54100c0195031100f14602a00d01c1c1c0040d03040703401c00700c0c4c210350780660b004c12114069004010130511120f000e48411100c4a003076240400000b50b0fa40e480e42200b43c0000b2040d8881ca0705030314100f054103141c0d08240000d005c11401c4070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 477127167 1250 477125917 477125953
    0xc0c27010314060a09080d2d020c0118050703060908040e011707080105070e0f0a0b03180723040c0c0204020309030d1503050d050714120c0f070509060103180203 71
    0x600d40b002c55004401c0030554080345407040710070440e070040c0c0300ca040c107014400c860010081400e1040d82450340a26000050040000000020303526100050300d0b0094540090300b1101c0c0fa4446850006001c00e820300401c600150080441780e110001103113141da58901240c2c1c6000e076501c4030b40c0b02100c140012039040185254424a0111344048500107a5940745032800d0f1141a20b4030300104903202e600d041541411112005d4050340075200d51621683d07a070000040d0390040780c4200c04a901200190380341d210611418008001d1801190504c44c1c0041e28a024414014125441035545d40ca4007202540240740403d040c540081c0115164545403801940f80d074481c056800d81c071442c0c450012070041e03517044035a0559421500030040c58200110540707840e480000151001035000d00e140c00d020004024010001c030301c42c1c1c00340d074445103680001890000100c0364a0007640000d07070107000c151a00b1038401c0d0700180c00d00c0d000c9201c0c0254034291012001c4108080d405000d02c000010004040c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 477128417 1250 477127167 477127193
    0x16030c030806040b15070201020c030607020319170c0d090515060102101413150c021f02120c16200f0d080d2a020d0201050109020c0c270103 62
    0x380c5401849542e110104021a140804090350080600441106041d8914094403490344180116201101d4500000c1c2c40c00208682d5840180d1001650f161120942c041040c1110b00c1800c2900441040c80050340c10120300030880c143c3c081c400b007001c240d089466042100210b4120064501d19149034518982d0180c00302d44150240c1b092015950800a09203d00c0381450f0040e000d000345519402c10300ca2282a2620050f1200440340c50003068500030761103282d110314020780050040c4c142c2c80901000275145d0300c000e540418418006c405410702e814a643c0c4d408401c1c81c500c1035580c852100c0c2d8010080c1041700291011100710048860b8018480e406000c01070f0844442506024020801c400c4503041c0a000303091300b031300340000c00c2d0b034118a030000e1a8400418140d01803140e12071080c1c29221b0440d403e8480164490b064001a40380c0a20a140c05005007440c290324003502d442c0300c690b8600403110268026403002c40317001140c00124043c0301940e95101001202965a81800e85e042120 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 477129667 1250 477128417 477128423
    0xa0b01060e060904090201020c1503041a04020306072304170f0304080a0f030c140309040f1802060705031201150f0f1b060e07120515040f02060f16030c 67
    0x411000400d0041c0120844410381c0c100429540c0b03404010300500018200622040b810b6204032040701c0c480750380b0035501c00c40b01e6040c0106262203150608244c3c0b00f00400806041c0302d012440c040c400549c0b800b01308643e2114081c24661050440c0f64200054400c0f4105141c1304041d01041c08182c07010034a08090008041804036501303a0454140d003030b2a0f104034032070028550b0005144200080b040c542d00d8041ca40a410a01000c1e0541d4648100030a103650880515800004603100c0c0c5203000d1080103c10300d0b050354104002004503e00601c0420300d1180644a03030b00c0450010304210080017115130f5400c1d18110170f00c613542c1d5000740307516001988900c407000c20000011020301500c1041c030000c60320541d6803170918181c07801e5000d8070075101c0c0c0c01d03055408607210f620850f41e0010800c403600040501c41140d900f0440f150504900304442c4003132051101105505100c00b14005000302a00e5030740460b0010354840c4003141d8450f00d413150b521468001c0d034404000b0018950040322801490340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 477130917 1250 477129667 477129683
    0x3030b03030f07170f04030807030f1e0c020616060b130c02100b0d1a01050a0f14100c0b01293f04112403190615020a 52
    0x140201901c9014000340d41c2000b02c2c0c280300150205050400700100b030740f00402840e1034203142c07115160302688503800aa0ba07003840000c52000f050b901030983c0030000854502040798840141614400036075480c44801000001b0003010306542c0d92404071030611000706945403203250286401005001408100d501c1162500102d03185258030b0f01401502840d00d0b0701601c0c0c50050040008000d008886406030004000702c80500000c9200424011844400c400b142007985003008003c041e001c982c2110000d0390300d030182007014218000340c031103032503208a50b000140000d038101200c090b045990080e0400c240b400002880903081c3c1080d140c036948501b10942d42c0d07500c0074007144c6a48500c5003003541d608000c14814814038051090a0507005c0c0404984030743d00d0300e182c41c0401d80704058409441d100c4140c1c1d0400b00901d001d010424070314000c0e0000b03c0f406a2544014170f1319000c0240100f585035800801901c03001110341c070502c040d140016200310221030400340295254034100084524007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 477132167 1250 477130917 477130931
    0x110f0423030a0c060c03090302090f060a05010f020c060729010306140708130201050c070b0408070909150207020301090c0b090307061b1407050a030f060506012109020a09020d090303 80
    0x10501142804005810204210102c0c0c90001c04550950b4045e10030703000c1001c5020080016a078180700359000f820f07241d496550600380300080040909460f40100d060000301042030f280306801007071100382503208a650a0300c80704207040c420340031030008410a84c8145020703c0c0c1c5002c40615039045050302d001e084204203186801149030b500744810388055000c1444100012001d40200700c0700520688107250803801c00102d00c005502c2c00d103154210000c11440032405102e201410080302000342400c2ca400c7c0f00b00750703081c4c55402c134803003c5400c44109140c0005c0d0510554070250001601c42d64071240c0242d98903583c0d2410490780c1c00c02c02c20701d882800b03000d0300016420703c26581d4202c0402904580200f0003941c0d40e80c400081d0900c1001402401138440008039599003074142401180207030aa2007251503585000c80c100c420040c506414007603d0251984018010701c040c44a0302e103c0d070301c0098910000d00004d0f4107485290b10500185000060355804000345c0d40044600038800e0320305020305 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 477133417 1250 477132167 477132169
    0x81b04050f010e18240a1a0108070c080313150504020619120626060f04150906090303020405040b0a05060702060a0c0506090a03120c090603110f0423 66
    0x51001078900d650000100e6005218030341100245640001c21519104802041940454104003654001d50320302c056046492000003402e0280c07540c0102001e50404c86a0541d54480c0c20418002100700e040003002800074900d02d001d19001d02203a60408056134070303894000070540040d4440c4008440d4140041c0000003180010300036240110303070081c4500d040c0301c40c0c0304139051407002c0d2041040c100040307540d4030b4132031080c0340c0b240300040c0c58500020600d000e04604214050010240703105140d5200c8800c003ca600740c0903c0d030503006980300081080c4200c5450500c0d001e002d00d001c024181614100c14101059050741c010401c5520985061100100c6801004102c1040d84152174210904000140061400300700401040c00582170401807281d15031a281c1c40d01104035054185544114506820705402c9014080552a0450188101c102d000c0b4002c01284840c481d40c428592a1a00350b52031702c60301c10694070740038410102503481e2651004040a0b1032074031140c2e5a0a11202c0d4014101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 477134667 1250 477133417 477133421
    0x90601050f030309010c03030b06090604030b0f0903070b1605070516060912080405092527180906060512010b0a09020a210b040c03201303150e0106081b04 68
    0xc413505864001809100b5101a005050100003059000c84200b00f80340d016514400608044d5000c1c20750300768180703040c03c01e54032500c101030600c49440d0300503c980d0340090884150320703600403000140c1e01c008801c0618113031018018894000d04a0142c00f860088805021282e00203c440b25600c1d108074680d0b601210300711140440e0060b00b2076004100910003401c01101c10391300031b11040401c012810b000c1c512982100b40c081070000019640d01840f2890003c0180400841001e41c448804914036040104020740410400c15820544070308210080c020a41d000360010100a041ea40c07042a5111030076009003058081d080c80f903d00403201146482041c0309070382c03200082d0b40b00c4801520011555103d00152900f8143d4416240d6000781c5680d2614081c0d041d44200c69180481c0c0800e03140d05c104030482041290001c940c0e82800041000c4004a14003130071a604182030382000da00ca4000c22002e80443c0c401d2207515820804005008900041c400f5a010340b288104a0801032003010042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 477135917 1250 477134667 477134677
    0x1050307020d08060f030d0f0305010504020a0e0904020307031b030203150606040b0705030f12091e06180f1203090715120b03030931090f0f1406090601050f0303 71
    0x60b0700501001945500030450907400140062042c1d0b40d420700035000034a0174112281d1080041c41503001d03981604d030940181409000304480542c1482c0f01001e0091000002000c1948902100c1c408101552800d0203c0405907801840884ac004207000d078040c1c10002510089000e8440c0d00c60b81c0d0115040c003104113005000003881c0d545080d280c6142006950003080d001d4072240010044024003000680040107107050388840103842c0e1501050442c10300191034201d046609100c0b000000c98000484c0c5590f000c510003e503116200f8201c0c020b80e00d0101111041c020324841e818442c2e41c0d044141000d50710880c615070882e00c400c0e844100c50b1f6144046016040e0105101c0190b41c1129403c0b90042048441d0140031642081119000601100004145002415517903403608100d0320744030880048400d40781c2001d0061031042c0e6100b0100c0600204007030602d041030340b030b01c0041103c5844075481180c0d04000b16000d500342205420703110b480070321806104421480c81a05035080100c140c0b8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 477137167 1250 477135917 477135931
    0x20304050a1113020d050a0b180a38030105070903030503070c1a0a06050f060403020d140307080a08010e07170a05070302160f0605100e19110a021605010503 69
    0x401031542d64600000207030a4411650000102032280c00703401841c8060a140c00724180e0210b004c0c1880d010f02d8041310039048609010303070f00d094000c0380f400d03c0301c2114580005a0703580000300d0140f01e41800428407d01c013540ca0901014640c08102003071004000e601e80c0e41c0c2140204645d03202c8402c00d490308100c910006000c00c0d82400051411400b0300c0c2d00c005001c0c0201c02040140366074600d0254440812a007087c0141d40e03490040c0031601303010002140780d00e81524a145003030304580000e900b0710340040c0001d0500e1348146250f006d5000500c15262602d9020740d5040cac0301d015640000d0f01c5000700b40507551160180c140080c101c144a41c03e0311070001d506814503800b42e10b804d20008040c1a0040c40d0740309141d008c0200f510601c2c1c1001c280490107000e0485441d411905240c4035081c6c030030103000040440345055003030228141d020720642d00035011765040e9504100c491002c6024241040483c80314540100e01003403d2900891261102c0003042c030800740ca107071034500545403400b040d0b402c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 477138417 1250 477137167 477137173
    0x302151303140c040527210903191a0604020f0a081b03010f030c0906060504061809110702040b01031a1512010602150a0207020f06071e050f1002030405 67
    0x20000b0a403500b401000c0400154103580d510301e020004202500c00c280d50491004411400c911481e40440400d5982c90749a00013030000c540100441d104200160280c0303004c101000104000d86542c00c119080215110400e2100f18000c541004500c05041000ca44500003810000031440d00d03080c803c80303888042da015400d0504c44100400ca85480740106500711152480c1d919000c0301e20703420050350003800c0a2201b0300d9140d05514105841c010031f43c0c00200c940b81005003e020070390300304081e1410f41d0b03a980340042d82c1681c952410079480d02180d002c00211454161080325007000900146a5075000751024070000220b08011000c850f1008190007001d901c5840c1d8044901c1d04101c0707154442201d1a489050070b500503c1c010303e102080c0e103c0b802680c48422080600f80340f00f241180d00034440d0100318240290360f0080b40c40610350541d088d10881000902504020501c42101c14000340040101030001040c601503544280c01d1a000d0054881d403008281003800302d00880344115807000103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 477139667 1250 477138417 477138419
    0x6010f0302120c0c0f0f0d09080105090303010902070503040b07111507030e0f04060b0d0f14130b060114070c0504060f0f0306091a091b06030c0a0807030e100603021513 74
    0x10520a03000b14400d01d0040c010b24592541703a01041210024080071000913024441107031402511101490b4009680d590400307040010b403403404420390b41124a610000341c1d07203180a00d04103045100301c1d00301e50100d410100b00b1000b0310030300d00c81c00c4400c050180e4030302004c141241480e000500a0503002800540c0c2c01540e42002c0c05d00d0106a80d4402019002003005a1202254055030704446110704e10a507450302c0355031680e40030380112907101d80c00350304c41e103200d00b09408001c1c0b1143d54080003034117541443c2d0119901340d2140030301682801c0c01307c2520f13490701d66515140c40721410a1040c140305900303284001c10182d90760165142250b101410f90707640e6904d1907465401400f0701a40680321a40c1d84640c0030790070700385030315410b00c07030035800010b4801018842d4111030305c51000be1083e03001d0201801040364842c181350840d8040c503014102004c8640c0d540008902400c0c1d18a25040c080c01044c6044022254980280041e00e20884d8a201c040f07040c005210350601500c1c0780c51214507000700c8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 477140917 1250 477139667 477139681
    0x10050903150903091306050d1a0f04170a090b0f07050132090304091b080a090b15030705030322050f010f0c03300b0102010c08070f0c0b0f06010f030212 67
    0x16aa0b511761040c41400324400350303210002002c88003409401d0700c003512901c072862412440007052030f60120201c1080c1c582800c241e1100303401e8075044103014940950001c0c400b0200b50203104540300801101c1c10b110759030404180305203043d8100800071200d41d070130300074800304078900400e0b072084070022074840d403110751183c0010200c0400d01030007022080c0410000400c405595005604007286501c8001c1c0a80708003e034010402d0f000140100d440c0c1e031401c1000400500400c4625800c00d0452030321102031078040b80000d007003030300a034002a4513110024170f0204036022401d5180c280c0000300615070410b50b0f95420711407419076080102c0d001a001100803100c0e180030b0451840500c0c02413a04411403240c5c002d0000a400158046202085510102c010b80316601c1c022020010802c1c4001d00078100d820001030300030b00c0040d001c1000c2c40346101e21415601d1241094840d400d4000100f120a41004140444e074441c05850460001d8030b070040c1081502d009000300d800041084131003001030750b6041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 477142167 1250 477140917 477140929
    0x3230c0a0306050333040308010b071e0b010501020c0307050307090e2a10050c060a0c0203071b030b240607060914100f060e04080a0302091005090315090309 69
    0x2180c10090603900c400c0410301c0c2d2010800c14460b1100b0354424020140040540400525507800e50226107158400b00000a540044100d04480a08036000d45503003543c03904d99145010f4180f00900600783d10752000510000030001b0703048400170b0302613405101e151410b06841c2c003040e0040c9a0143e002c13034070400102c10241e001d411600700383c20a84040310455646500300002c0340b8859000d100c0c2c844012111441c100c00c0840c0800c4480c180585080d0f1050340c0c1c075480c2d0000a081c810101d41e14030702c0e025624021710884022981c01034105002c0c00c1c10250b06070b41082c0c1408103803007085c01e0303000082d0040803040e1a082c12450158100b003845800c1030030440164454001140c0c0c20340c0740c50741500042c103003042c0f0200118415000d00b0b450190040c519040310608404504158240b81003080550380090584c0c0d0070a41040c8556a03888840c03030141d01902c81d012405401ca01e81e01740803c41d1a07030140243c02281022030680b00080405110b01807100016140e100403a0420404211146040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 477143417 1250 477142167 477142177
    0x2150601030e0d05030703050606160b0405120f04030c0b0901091403030f07150e1c050d110403030c060f0218130618090c0b191202250303230c 63
    0x524020642c03401c01c14030700d81001554a480404198080b05110005030503001d2258001010f03a191401d10300c0d03d00b401504402c20b0368000d001407210201190a01005000c1525000c0c3c6441c8910f54807400401c165a090384070784015074003008414008a100098035003140d40c0000f050351500c10850414045a000d0520f400c443c0340e1504c81000038260b42895800606038690280085c500340f069000360107400c0d982080701095054000d050a081030310100440342c04400c1041c50080d0315041103164200c01071825021140502002150000405a2205a014110303100c1d05050080601d41c4201071300341e00484c01205c0803070341c00350120003503070910703140a803d84504408003190680d83c4104000b4010100280e1540e095102d010813014001200c0c4004001c00381d1a000d645000b8074080c0c0040c039403030304403621010048058050300a02070306405480c0d41d04140d540c8611000e1b114020120710b241a40003c40c04242059814000d20115514202c0e16090300340403544590750310030385030b0f01950107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 477144667 1250 477143417 477143419
    0x10080114070e090a0e060c04051903120518030304030b070219110607020d0c030308010f0b0f0912070b04080309040f2a02070306051603050f160e0105070501140a050108030a021506 79
    0x74600c014015005c01700030140c002c000b02030340310b03a58505050030302a504c0f191255200e4282d00b0f1b8442000014001410400160840d207011502c52400c921600c40005a90b800d640c1e25110100d40403040c0940341c0d040b90b0140381c2c0c540803107000d0301e070300b0350200703035801b65640d000e8001900c000c040e0307a00c4d041141c0200200c6200a02c0d01507513007050790710161201d000d0340058001905113801485144001c8401c60003514542d4007040c200f002030094444244074038122280118050310b01100c000d8000c0050390060070a41042544940d21103034100e81c2d80c0c216000052203a81081585c240f10800c902c075000e0404c0030ba54020b88145803182d202288100c040c250301d01148107182c0000080b0b081845914003800c0300510b902881c601c0800e006055410140105603194012024040001401408a50300c03104da400c0c035140c60703d50800183d4043c003c0c40005440380d402d00031a4039040959140b05407045070840030401091741c0b100981c51b941e0161030700f20000351388054900c40824070054a070b20342c0060 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 477145917 1250 477144667 477144671
    0x510121e06020c0a11040212040f050f0304150e011d040c0513030b0f060f09040b100e01090c140903070302010302130317070b060d0f02130f0510080114070e090a 71
    0xd81592034108a902482119000780c0119088000304250401407802c81c441c201c80035411b00075030f054003480404005c0d00040c5014001203184003080014003811224040d008203032615980c0d598408890303114550060b0b40000e64800d8040155030041c022011800d85100c110349000452006005c000d01c42c0c03c00120901109000e8841844903504504024521075107078418507003881550395000580144c0f0306072203848410030808140c3c0390500001d512a4208580c441d00b0f4a40401615288041e50014010005450008034001c0102d400004c0e1072205540c9041c110000800092614020702d1622503058000d4a01003015601c01d40140808501004500c5003150741e0b0707540c43c0114510801c10001c1c40c0030102d16141844609034006a019200b07031020754007450103649540c81701d088080000d1140348849250710015105038000d6804003402d4404003c142028210450b000711a44200d4074607600f0060b021808124004180d40038984649a04505401c0c01d0104020007030300802c2d05590f0381e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 477147167 1250 477145917 477145973
    0x30b0115120f0204081509030304031d13050f1003080d0c030e01061401090e0903030406020f071407081b0604060c02061e04050406231207080a0b0a051012 68
    0x1e046441960105203103500d005070b0700e6180404c1d031802c3c051401d2000c408051594204440c2000210489038819407500d040e080031802e4442c0031100c07502e205101e135007040070303102261351441107a0f05c41c07030180036070790f05110490b50b60200812280e011800014080300f0240700610a022890b005170004001505000c981c0d600742440c040d08550540d841340400e4072122500001c03658111000601900c08039040410034500408400c0c0e46c1e100140000300040d6000490101c00c080001c2a00c035070541c84038111200002e43e802c02e0741c0d54803040c000c0807194020580404022114003420041004000d800107061614000781590b08620065099070859000c000808811420301d070024001074503501595251400d20341803104560403600904c03080d854905000c5c40d00030100c4810701800c5011074241e28034010110080d41010302c207034880800e45c418150301c18200102e040d41079208490100c002c00c45581c52003001d42003601d06200b09800300b05905008004141609074400795a02c02c80b01003d050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 477148417 1250 477147167 477147197
    0x21806100e1201090501240b0906031b070b0702010c02030a0c0209040c0803121b0405010e0409060e0d050304050118020109060311041a0d0c081e1003061e0e0601030b0115 75
    0x4d02d11840702241e40384d54521440c0c40129002607d004410a40c1c13000184060030045022200d02c100c4002c648610000300c006808440f0310207440d0001080080016110342c82071610400e2404190b6001c0059420188410140f5100200f9030389195032642d50071f89901c0d0590248282414058019107062101900104064404000a0604070710070882c4030302d540341c001c1c244421300c02d0300440c01004036070400042081c0d0380d101c0282024440100d0700065580e01c0c03403408800510100038942114007505000c0001d464200d80a0741c403450080000307000c0c1c6a902e50140450080e81361009010904261040c02420302c01d61214401c6c408500c40b10f1f00d01501e418402804154201c06400e0400e0000380c0246c0c1c68040d0f015004a4001c1c500b0812401d0825102000d034400010094080e040500400181800702c007141e082d00554124408001c600e43d0b441100f0304040081ca40100c9090130903190701c4a82d20009540d60403aa08800307049640d0b403c0031a0b00d404c03903c80c00d103060100070013001000380c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 477149667 1250 477148417 477148421
    0x30c16080909070c0b06101d0103090501060b070b16091502241801050f01150207031703060907020f0309040506030a0b090d02190c0e130804080703021806100e1201 72
    0x10f0900c1c0c2c861094002071880c102c0c088401c000c007a03d000369603d00035a11415000041d02500010b9110101203142180004038014020440098201e6003864000140241083d0040a00c00d0081c243c0d46802d80d61112040d0900d000c4110700b40001e08071500c20418203014160004198406205407006179070700001210b48900056035240c092100c3704d05000e21548103422880701d10300c0250003840207180244d170200000310b0502c1458907900035a50f20f404481e200380022170186900c54003101c1440084075403101030b60400c545080c0903482c1840411105800004c0e08044940000c00846c5011800c03800c0c4000303044041c0c90503415110b0504003a00090740545001e01c60580c0b00d00401d4210103400d40246010003400c401c078440e00c01d4481d1000450b03d65006002551108103a0040783d45554612900380051400090300c80d19001c00c0109150b0400700f203134000c40303000b10b9140d00780b1a5001d043c0480c443e8290380050f44070001001a02c0c1c80d50044500424404000700b41c441243d043c01300d813a003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 477150917 1250 477149667 477149671
    0xf19020c0d030b040b010c0201210f02070302011107050a0213110309010e01051b090d08040b1303020108070e0913022116120222020405150703080c030c16080909 71
    0x5003980000105101041e41480349809100d012541800f00a0010f00080c00816400201904014024035400c1708090612010400762211000c100114804030302e20714000c2d002040110010350901ca0f11294820003407090313498507500303c0090100c107641507007001814200b9880a040c2d550b100c545140300f60403007101451052007090000305282c400d666009007181c82c010801c0140764509a003541e903038030541d03081d00d0720f140c0203658421484c02681403240e07207401154003c0d9901c1e100010074850030000e02d1915812207100b070302d400c1d2468454040669106807102d0030160071003000700014034003120440c2d003480302c10f0001d082c43d240c1d580703c580c0500ea83c643c00e084070541c55019181500141c019200c0300c00c000d1240151944204619a000540c0e0366460b500e501c644010390b0000d003424407140c1d8100c600070100105480d2009600f1103001c08180c04c802e0096003c12041400180c12503103043c11244181c5140750001c0c40c200059900f051428103001d03069601d2141800400c441ea21813410141c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 477152167 1250 477150917 477150937
    0x3050315150d0c090f0b07021207030606060908070914041b03060c0e1806030a0201080a060e040b15010c02011b1e08090307080309010f21090803010f050103140f1902 73
    0x114000d050558058803d4255600c40f0030907540c2210300f049441d21071b000703641c04168112903681d0752807103400c26607241002c6900041c09403803030100c0001e24a0b070000071580883c1e04c9601038901c102d5a42c0341d802c040702d10720041a103840e1144400500051101340058510005542103c0318003912601da0400301d80440800304040388074240310b0358a51600d01c07640484040c81411101e11454550080b0391180c1c10520024188020480822031030743c440c0c1c01400280c2102c840c402e01d60f14007400c00c91001c14003039917212540c0d40c028125031181d520510546c856030340c068464031400710000d4140313045904d02c070f401a11407440200100080845000310308800d00c0c01040034940310a0500200360810545a1003d9140d81c0308125214450741c128072000c9018109061410308039042e4185031010030540c003000c951040ca804030307071003c0080b4403028505a500a072105c852450b2102c005504985007050f0b4540145004000a0508100c91600d42e82c020b00b4411010b5403003200c54125000c1e03070003100842d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 477153417 1250 477152167 477152171
    0x1b0807210e16050a0806011503020c0f030a0e0f01110a2306090a0209131a07030b040906150b040e0c090d120e0f0a03020f0108090102090d0f050f030703050315150d 72
    0x1c004514013454400c015001c55009801070754913010020000c542818058428941c0200d403001e15400c0c18405034000c512110300781e03696215400c9004103007490004403240300d10380c0380c00855903d5214000d1820407603000c40041c5005000c07902c1d640c4154291150500308401d05207804400f190f800d000c02030040481e82c3c0100030811161040111407100102100f1769605c2400d0560042556005401001e40341c4a002602075180d00c00100e015007240312074190480c0c1400741400c20080245d000c24806150940c41300300583d1910498907051041d032003100c0310381240002044a03c85181c00614500c18000d00201004601e40e03101201c010005a043c800b181d850300d0440100d080100c0d041010700c00888103141c03000e04690003da4902c0c00caa80c001d040001c56800038440000035411281c80c10740040c84003d04080c1c41c41d01c0810320b200800100d40b40d009074024202c0d4520004140d901080c0e05480c0c07142540d46420b11400c090003070b0103140d41e0000203098150303219086140200203c0c400c1c1040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 477154667 1250 477153417 477153419
    0x918030405031e0721080a03020403020603040f02040507031e020c0f07120b01050103150e0403022b02070801051006180504020424020f0601061808101b0807210e16 72
    0x7840c2071444c82d600078801c040040300f40d4400300d02424038441d841a4083c910a0b1134028003c0100d000303000380c3c2c2009400c610000184070a010072014010342e1039100312410300181d910000120103035030315940381c5552003180342c40c80c194a19542d0058503c0424100444162250103c00c0c2403030000b0551003109201084003090040c89050119507016140a0805005c1c4268103925146034409600c40c0c816130074a0100403030b00f094800e2101c00c0c0c03000f800496400100c0300350b189840d10f20980d1203074140544200d60000031120302c18002d6521031251050041d1426183c0001036568020400c145030b11000046d1b0701090540d500d102804c050422420044030364411400700c0c11425205140070400e5500c400606850a180012250305450141c5401c02d2440c034000d00b044104209a0031403101c1d40201244c01054219560080f54000e04140f1815819018041d00b500c20303000070b1700c0c1200003a0540b0b180b0340e030300141c8c51040500034101142c000768207013084070f0301ca00f8694020500c502614071088 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 477155917 1250 477154667 477154723
    0x9030118031e0e0609040e010e0604030306060909141b120405030d060e13080a090305030706050a050c12040803060d0203100504030e030d0813020a03080304050309010909050105091803040503 84
    0x8450480b00032410084400300303044001400300c1c011102e50b10310441d19880104c8800303400303401000c590704014080ba000b900380303490082d024010a000d1040051106180010351440074041c2c810070300507c110000d01c40c0c480382821380c561504c41d08c003050b0340013040186800d80100d01404500c11782c0600046d58481c102e03800c01c00142d42d42544181705206110050100c012002031207070362403a40c403440684c1d4407a000340d81607640000b03640c4064081e000205107402071098540240d4440c001c0d0341c0003000f00d030380c45206400c8680612490744001b120350500060000318148010341e0410710050150007403064581c00286815031503a60702418039100c0c03051004054105819804001d4120050841840c400e1001030145c44020846c2d401f00c800308c51001c0c2991a0301011101440e00101c60300ea5920746802c1c11075403a80002480fa00241c00340704009071b442c0c2c051003100c1c140c64008151590341d071540382d900d01c0d03051440c2070110f031180400c0000040c150b408004c50b2074003960700558442c040d440e1007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 477157167 1250 477155917 477155957
    0x3011a0715090b07141209010e0d0908010f0516030b0a09020c0312220b190203071107050d020d020f01180602071802030108190807120504030615030c0b0903011803 72
    0x10b84010184108078481c030800403015421b8500801150110240c03075640c02c1ca004d4090700420a0342d180e00d0080120203500e180d4440030707450a81d01104028401055481d00c41070440d8422200e0000c00c0302034404015080d0310940095100d8103000b00080009600c5e00382c04800c9030700c4500b21102c4c81c0c4c03000442014540c410055294000034803030740040c001201d030b5030040c503107896064010300c901d103010002141c02d030030604503000e04030040c24119241d10b030010000d0521060009000401e2007112000121850088251200c0c6d039400b03008110302c068942d00b07216004990041140c18420456000013404500240440c020031031075004000c0e192402030141c41c8000391035000d01a4500420050011107000034031117030300c5122a10201100d00c2581403031070b203a001d400b1005220070050550402051f40c044050025680111401c02c545070410f8094442200306100c002d2420005000c100b054108800241070408800b80c00815100c85147d0003090000e40d078281180854103545219048030020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 477158273 1106 477157167 477157171
    0x90507120b04050f030f120a0b0d061a040b0d021012140103030e1806010e04060b07120305090a0b040b0c190c03180b03011a0715090b 59
    0x500e854000c8441c103450507940d5106061003800c0e5810003104030b50b100002e9009480ca03154101d200b581c440d020081070b90b4041c0d0340d2048180c1060f2a0b040314101c02600c28230001800c05581c0d01c000c0ca40342c00c1d000786c0343c0c000d610300706401c5a207855003c0605400d51301110039201e85100000215006403656511441d19414907480140c4241ca24400074180c0340b0039164460300401c2c460a01035180349070358103800d00c42c4441e0003103580c0d940901e1a0a00c0d0610151010952a45a80c7e0340c3d0381607032280504845010040b01410b4010768544a0344d43c1084015024182918868603810031f0b92101501c043d2081c4401d01c04100f0400e0700c00101c8800565280f18160820340c03411018050144080c02607011401d055044500a900c1d03900003170a80d02d032034442600b5a42418000354001001c907010b400300c0281040a04082034403034002114200b6094001703d00b0b4a490300d8810101400 = true := by decide +kernel

theorem cover : BRFrame.Cov 476978417 477158273 := by
  have h0 := BRFrame.cov_init 476978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 476978417 ≤ n) (h2 : n < 477158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
