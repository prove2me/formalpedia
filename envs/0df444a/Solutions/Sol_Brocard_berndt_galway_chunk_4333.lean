-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4333
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:16:51.870576+00:00
-- url     : https://prove2.me/submissions/7248e71a-9c0d-4c97-a708-d1bc91839253

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 779136690 ≤ n < 779316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 779137940 1250 779136690 779136697
    0x303060d02060703031415130b0609040f060504090501151a04180f090c080c01050403080d020901050c10020d14100b1305060c0d080f0f071209150c0e060f 68
    0x241124542c0c2d9560143c58140e000305030003003100c4035031b1905404001c00640075000b800300b004411039034100c0c8004010001e1058480106486411a40501c801c00c91410603412030b500480d103100020861a4130f0b840400c080b960078104c1034441340e45035504468000d08012000c006040055007801c074141c81002c0100e02c0344102e204802c180c1200481c1c1c035030f0107061603100810300284c0309030510040f1020308001c00400100d0140700701d04d02900c0f00e815190346c001c100b10742c00c90303910020180c00d160350a44400002d4010310686410b0000812610000e48000d00c00807141d45483c810060321090030340007201c11941c40b100c141901c0c12060092004140900703004108a4140284039590b4056407440041450782c95400305420540114280d40c1c3c42c6d502180300d00902d021a580d80d2004e0355003080040c1214001d448017602c1d00c1512000c00d00381d91003070009170300d00ca00517480440c825285613214454401140160000d80d5500c8c4c6c4580442e645c4089201180c1d141121118100403000e506000e1074030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 779139190 1250 779137940 779137943
    0x31303080702060c010c020604020111030c0703060902030708191b030203060a0b1504060809010509120d020a140d021b0f0c010e0310050c0309010605180403030504030c05010213090e0303060d 84
    0x100c01050080c1103680301030840e1400742e074203c000d12a0385590781019585030001e035812404902185c81440320044000141c0e03245d5042c4000801c4114510340b511700c01000c01c500c3c2070760140a040d0300444e000030304110134030401c0a00407032039641c42e0040c2410313041c2d4050f1105442003140300e12010800f42c2e0b400103845420520851001980e86001000038050191441c0c0c00c000c41540030400281103500210f08500c07a415450080c071160b910364401300c0d16903942c048080c656640c248210f10701c0d078a40d60301810a0004900f86000c0f505445c00409945400815418646079000940c60380f03460941d03450301c654400e10500070315044040c1031070a61a40d007142146c43c10491410055603850b64200b020142d4081a10420002400c294400074071035030040f1000d40302503080c548000348500305500d41e070f09a42070405803002a40c0f1256021005084090820b078204800756040f1004164284000d200c02841a00048502480c01c10740805031000c0c1100c07034645410a1003001284d071508034a101906 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 779140440 1250 779139190 779139203
    0x1609122a0609120f02040510030209070203310614041e0611070e1906120309170f1203070521091e03070303050c1204030e090903070c051302070f0602030f0108031303 73
    0x150741c0c0024416864200782d09c003079800003800040c00720050300400101003520710400c01044440307100b0048114a1019060078900c914104001c100052240c0a0030305900f8501401e54a000d50b14a5400b000900711211040340c10203580007000b04503045a5030708010040440540798841c940035044400001c0202841d444050101d17954100081d01ea01403000351039850200407021156090041c01c0604a0003a400301000a2800e000e0021002030100c0b400c1e98080024450080c92181d0a02c490300040c0c80c40d4140101805103111035072174542680940b0030449680e01051800250079031402c203100003500180b6101950403401c902002c030031150340381e17014200400e0503100e0060303120b12442241544c3d00f0740f04040b02840b0805034800420000304a0846856610f0348520710815203c1c8103030100144100c020000401c050304000e050b0101e2075102c000014203241c0d0304d4851488041e11050300726641507000040082100c0c1e1210300901400d2080015402c0520340c0f00445a01660b9000240c00c1c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 779141690 1250 779140440 779140451
    0x60f0a0c0809280602070b06090709080c060a1103030a0c0e011107050d0c0509010909020a1d06010809070503030c071a25060f09060f051609122a0609120f0204 70
    0x80c0f01e14001420180d0384513200f1551100d00f824400c01d00e003000c0e1003880c4184902d102240019215101d003000342c0c3c0c1d80ca13014100c00d1a49000708105944800d03921401d002440c41c003581076080c00e00207036100b890030040107d030b1500580e40017084000c2e0201d5290500c48400c1856030010300000350513096402c10341d014006483c2e40d04100750300c1481540041d84c0512418004201c86419402540c0c0d100c0c03096a05066160300c0d0801c020403102c2a40da201c0648110320002002980b1a03000340e0303082074040301a155600d440d80b003c642140e1115106058591001104002c6403030b410740040246140042ca450411030b0300007103017900300100b44101e4184c0c1170305c00484c0207004459004900381c69010400700192034141c5800000b40c5500240305403224a40030000300e4941001c44588503155680d40d030011030034109014041c00540c000c170300b074884405501401942c1c1d05c1d018840400003841403070311030500307240c24001010f55803540c000a41102d01c0e1124800010a800080700c4060781c104c0d00802e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 779142940 1250 779141690 779141743
    0x10b011d09042a061205130605102103020613081902031903050603010510032d0b07090f0614041703120408180d0c03080912060f0a0c0809 61
    0x44043c03c0c0502c1800d6500c40c94440311008440c120074046034450303100c000e0507402d121529401c480003102c20300c5241c1003016445000407425800319070b0040014001c0300d0140d44403808040e081a208114007010322441c03020030140741d0100b002c60740c801040c0481202003000c50307880e001c0354000d03100703400401041d40b010307038545c0e60080c01501e40f100c40501c680c40c00508200710040c041c0009a4100d4082c0d440e26000c1101e82d031940040ca404d41e600051544204100c2c00100c00c1c0a0301d4052802d012980a001c25400049815000c0c0c0c3c006c0ca040d54a6112843c240031180301c6c2d60465901c8082030000c4166000394491702d1805a40864031400c4050031103001140381c01341140706d0b01c01c40010b800a001c0410013080b061602500c60b804401c203c0e00030b81d2803c039051004500007544060711005265000b000042c3c014001000303125400f0b0b0254000c60090510f240c42e006050701c0103000d51840e4010040411410701c2427180d20b00d42864036600504010700c03425100c58140c000003540c1ca01c0c0e10b50301d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 779144190 1250 779142940 779142953
    0x1b030c0c08030a0207030807031b0e0a12120906021621021002010e0106150203070809011412160309110f0303220f0623090a0506070b09010b011d0904 66
    0x1591a9004007049075246001010031000b58001503044010848001c04101d100b07109120b90f001060191041441820700000300740c403e0201d404c8100d510051060000c04c42440a100b07003602513100c0c1e003e88030050309504010300394480035005a421903010141000c0032070185820141201c41c15000b1390402d003c282d401c101000c8050102940222059803860314440c2e055100c910a07854910080001d16128110040f04004868101005038028050030380881d0010004021404050600c0c0090102c003200c4450550064129601c0450086003000070400200d450003030300c9421443d0400c0b0a40e401e80d03c64140d41e1010605a000d260b07a6035004080d502d0410841d04401180701c00d1400c094015042c0c070021a10601890b28103000031a00064064000c01d00c207000107210061841346034042020100f036981006a042e0b82c800c0c140b4000080c140c030390310001d16049000d4030000300a80b92880d400382c2903071090001181002040220040740d0440e8401c1c0c4250a4800c5440c00484c1d10340d810b110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 779145440 1250 779144190 779144207
    0x80a0807080307091703030f28020f09221503021509031f0b010e0901030b060603040c030602190318030203030615130e040c080312040602070318180605041b030c 71
    0x15403200d50050320304480c8800c008055849020028044086961103e02041c14035641031510340300c001e0391007200c2c1072700c07003082d00a020600419602c841c10800c5000002c2d400c0d1594210f001c064120602c1c01000c50301e031138000c200c2c1098050200c0880545150b001c80c0120140c00440210b504010a840503165001e00015008268031044040007070f4081c20410000c0c1415119940403510076101c00340942060038100c4d0480b81c001101c1c901e41c0d96103005000c590380c0020005c0f1044401c2500101c0042c1c5688080c052007801e000840c144e4801d0501d0203421545e18003c44411850580d00140000342e0010441e64002c030191a101711340020207251105601500c0b07112110b041019101140000f03091200e00e00c40c5009642d004042540c8803440341e101e20801d41200e0420140c80e0018000c103043d5002000300d0751007860b064034011002c0420b0801c1c02e40d9070b00400a55103104a241110341c0040c02208003525048400304020b02d00800354000062400400c6000e140c2c80f40d180c10245405103085 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 779146690 1250 779145440 779145449
    0x4020a030f0e0d0f110a111c0308150409150b120312040b0c0301150509060c060f070e0312072d0303050a1b020a06050a1b050c07080a080708030709 65
    0x600c4494801c0c02d100e52910607240340040011010041103400303e12440c41c514114540b900981740032941900d0b04a041514030f100a41c000ca2540c4446442040800000c402c8502070340c0d55030326a0a02c15600740c140380001c05003521450134001c080f40820241503072007a48003c4000b0005282c420305000ca561155080701281c064003001c12140e40000c40c0c0404907200310300c590421886640c0d02054007085000a000f41085d0072010308903080041d029500511410030000c1040b42011131822946242283c12220742210a852209000c10340307400105c0c2810011084018203c11060000410a2402429000341c55400340d84111000800d856803104007400d50140c084001d101e46040160240000381c1d8800c00040c50460a0070351207180480400f0038511507805040c800d00144c82e80b40241002426054441e60b41d00099198003207540351010300c130940d0f0b0321030340d88500340c804415060002c594030101464011951443c0014510412184401d521045940d166154000700b1114010300e41c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 779147940 1250 779146690 779146721
    0xc0301080d0e01120f11070f0b010603020f0f090102031201091b091401140d090b041b050609010507050724090f0e04080d0204050d140123060d030c020613031205070c030204020a03 79
    0x3d014007440072810348250f0349801404127070340c3ca0366109421001c900c200d00c0b0ac1a405c1000380103034101d026210009000c4040b05204803818503841c1070321145040d10a0b804003440660380c00d44035140f880c0810850f6a9403085040c2603079035501d0940c03c3c99120a070b0441c80f0b8100700da40e8001d030000d0340780701c0c1c207440c03040600101c1000701013030703500c3c0c1001001c0c1c090b5011f0740c0d00c6280c0c07800c40d481c11032088014001d80c0c1020b88003500380f004660042d241e070f030017540b000c6400d8080e000c00030441d910020b50160300100a088003c41c03041d41048082c056403a04d4010200700e07245110248550020074000c1500720341c0c07000712aa92202e818102400a00490300304030b5200a1a0030328406000501001c09440703e800b00c0204130400742d100f414400152031184e0300390040b03001e20004030f10f440c0030341604296030f00900385103030b10f04450b03030000340594084442c00c080030408240a209100c80c0860790f16400c0900c0c10081d04d0f280715625400008151840000e05c200c0d0000b0b42a550740d4400e403c00001c0c0b070072168 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 779149190 1250 779147940 779147947
    0x40b030c09120a0201051909090f050603061b0f03040213050c1905090a05010516140c04060816031410050a0516110304151418010e0d0206091e03060c0301080d0e01120f11 75
    0xcac400c000b500098031a240f2034401c003c0800c0c5c00550880c001859610752032103c610b0002c0b0301c104003060703810041c01a07902080003081a05480c041d03009480c495200146140d9803540170302140c2251301e1a6440741010001c0078440000107480d24008041600c9003402d0254560030203050072038001030502d1004000c004410b004154941000400c04000c1c04121801d201c0385032078014180c1c0e41c0707443c10039905070008a92030410100303a180b000f42d400000c0d1102511640791007501c80c04c050300c00640d1020b480700d9a450401c00090011240048888124507260018400f60400c080c2d5070300860140f5124142000000f0710301d94010441c01c0309001004804030f403610000b0b40103640c000141c10300140410340a441c59400c514280e030001820f0340c1c0c01030500b800d000720760050190301c0b100c5410302105000700c41c0d5800c0142e6400c010440c81102101d203400e41d0b96042040440c1003101000010051000302010341e010380ea000b250340c0c00081c1da0004c1c00540300c5190350f440c40140c41044200d00300c444001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 779150440 1250 779149190 779149211
    0xb01260910090c050409050a08183f0f031602041b080103030e031c0e010201110f040303050d0608013e070318050907030e060f01050114030c040b030c09120a020105190909 75
    0x2001135422455044035480c92f6080462103040a000030328854009406446107a240d91610305914026548c0402040311082c07180c19501c03902e15808070084e17480c2c107034500e0510011468903005030222540070704a41182d80281181c094801c1e4418007009042c0081d1016200a0340c03010410140f448840304a0700603030031440c40d4040c2407080f07180c450342c1c019400e00082c07481480c6154229414010006000c030b240a15507142100c2c0c82d0004400d049819840f05000901c50f0024003c070030284602c0e0220308481c0c00390702c1c904206640400c00b4140d21030404203200d41e0082005094a50705030b0541401d4103000c400310001007240744541c000ca68001240b0b402c1c00719a1b83c2c95400920707443e1131142203400030344945940a551070000d104841c0060140c242d568070f000c5850000d1f58101090403151801e05448011104d0290800c45110f02d550ba800315601007103181590070590240c0c0810041d201c0c3c0c40113900028201d00c00c00000060121840e901d042c0c0d840d210301e55060044c41816020000500030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 779151690 1250 779150440 779150467
    0x150a0f0c0602090613140a0323070305011b0f11030406050d0f060801022106060304170c03160606090b130b0d050337120b01260910090c050409050a08 66
    0x20303029501e05a85406000d11031401c108000030223481c0c214100401c201c0070411005500488103d0103240e6000701c10300080054030901451000200d10034051840c0440c88000900c0a0007104d10003041104202c4101c1500c1030100488003a1080c40c98540d5942402e81d03100e0307002e031035042c030030303400451401c04000717048001035020f413209003078500c551142c103050820316007800203040c1c03003169001d0800c00c0032400103a00229100c0d24682090006410034a000518a0071070b08100806683c1501500501c3c0c1008000d02c21040507000b580c0041008510f0003012518581c000400302c501250746034241c1c60155900b0300c0080e603080c2c1c088101c90307494400080000d0b07607011009101c18104a407a070085414000c0480a580c5080b050740c903e04482d0703241d00303208080c0229000c0c0c2c505120028080700a40d200005040e0300f80b5001c804d80c00502e08001c455103141c100031031080c1c01002d282101002c006241c0b07034502d904581c0111008034161070340e41003403418542c920600405000300001c81e003940114 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 779152940 1250 779151690 779151727
    0x32b080a09080706050114150327160602060124271409060603040209070315030b09061b2109010b060c0d0909050609060d030e060307020c150a0f0c06020906 69
    0x5e1f803500c5080c01d43c40003414880d4040c0c0002140031580c40600008003842c9112080301c14607000c1c41c0007e41078903c00c840c0541040800c0b204080c1d11640b07460140161074041000d54018540b5104950340074007000d42c40e0540c51100520780c0200401e1060202c00b0b11080c0709241000802000e0394980140e40341b400c0da90390360086070368a00500721900088ea01d40341001c01c0d6885942c014000994036070350107a04500500310314168924580d4003980100100c0d10100115104e080848000c22090628140d81050000242e42001d0034a07410403c50620250030340c040084203448031405400e940300c3d58005401340940780c01c0542c02c4040400c07400142e00e400074101c250324649454442c6500e440e800010150b9404a4550780c000c11540007144203800c10842d9260218003030f1030100b18407051200000c2c5c2680c000d4500400582c0100344004561800c4a94290852035400c3d0861401c485410f02401885d420346480d0107001d40070310050240320058044840002c0000d004e6559490700007540745d0b0000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 779154190 1250 779152940 779152949
    0x117040c0b0318191a09030c011404060e071401050d020c0f01200310150509130605120604150b0a0f0b120601110601050f060702040608010b032b080a090807060501 72
    0x105042c203441402c40080f4042001380e8008116280c8000b56501c50310900401a01c0d0007001d220030031000704840028400c04078400000c070030340501402c081c2006000c0d11520340070a84184c001c900308000c030004040c2e441030b4203402801c042d0740b1002c002c43c2e844024001c0340d02c1010603020302c1042103200c1406500c0010500300c03040705064054040d4a004050740021a626408000d80400502000c11004107440050905290040c82c040641c80882d80740e0159008d0480a15100c2e1000d00c040e280403258440c4021422008014074a400d44a4841102c0c04100700c480f00c641d0340000304c01540315002482c0203854503500328940290750324207411859104681c0c04000c403c012002c1340ca158800c84082c070030341c1c2c10000100303556401d14040000501c1083e2040364040010409600103880368002e260041c01c80c50000500b1814881c24181004900c80c104090380c07207186100c510f030341800888180200240e16140b07903a80c3d500d14414004000058000d4107680000c5044010403095800c01410380707 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 779155440 1250 779154190 779154193
    0x8030315040c0207140d1b0510080903090d140102070c08010b120604200a03050610171f0f15090b0d050a0314040911090307080309030a08090a090905030d0b010801050117040c0b0318 80
    0xc12414200c800384c0701541c0303c0c820340d082037165203d54507000c8061200c850207400e01003400900c9803800d0b070882c1d024400032034480f00344031020007552000f0b20036440200700941b640c0303024801e42c10415441c0e0707100400040c82a01841305011082107140280000038002906408581d516400e150360340b07540441d500c10301c030500309001191a4000c1001c0f080d00d254013500510300803e4050008100601e001804404590750b000c001e03c2c10388480c0900d51301201c1c04198403005505085844c001e030b8000c02c0721f403400f9401c1e03e90520001b4800003a40c5040366014601141c05168540c00e0f42400e200f180e201714082c500740b4bc0c80c1c0e11850b0041006040c0c120088003183c49030795482540c261680611294680c4c0b58003c0940701d03010881481c0242600840100800245c0d03884000d960101ea10341c2000783d0b0250310105035800100114804c10a02c0e200c00d003442c0f4225890040024200ca03c0a02e4103110324280724045410000700240000c043c05500f642d06840346042181480816090019442c26 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 779156690 1250 779155440 779155459
    0x10507020703112812030306050d03050f160819020c010c020a060e040b0301241403100207021801031412030c0a080405100608030315040c0207140d1b05 67
    0x45600004924007142d51203c200920464407000b045010000c0501d01900030281400000c0512007042c00300300900340a0041d03880048442c10b00a08440f02d0344c000707500071541c80d4040b50100e82c02406440101b0700700710f0035542d10352081c4085e00005620044c000c04248010982001c00940344100c541008040d07400c507404000ca0170011a6000d409000107904482000d50610100b40305030552101e83e44c001c0c0010504034481da021030308403010020031468000c507176036a10704a400205100401020750f5801e615803140303100000780d152810506903100c51603000444800710344542c035481c141d030b19994000030015a503c0c02c0107030308000301d0109581e00c3c2c007030f0a0001010441c5072040d280200e2078145581e0505100304c0095500b01005802516184100070807c41c9031000c0e409013102400002018503124180581940c00c2d8408032010b851041e4202910209001e90014101c1b04036a41ca0b82d0f141e8000c5410008140301d43d0f26140060600d40c41c0e00414680a05d60500d000100d40e01600c20f401c6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 779157940 1250 779156690 779156701
    0xd06060b07060e0607080a0b0102011d0a0c06210b010c020603040b0a0c020318040b060c06010305030c120901020c09040206160b06090a05040308070f121404030e06040f0603020c0307060504080c0105 87
    0x101d6035001ca440300003058402d0f0120300c0304c11f403580c0851071600c018000082c518a1007202016440034014100180da8002404241000f40055110005244d039081c5000c0356110006c00c071000310007424160042e1980c60807500120380c41a00e214a071030b038019200c00d0b0b581c107043c2801680d1034003c48000342c040f420109403000403031000044400d036010217510050b040349440104009440c1c540700f90b9500210510441d59400c1062100314001c51150008540c2e940541c0348031420415a0a90070318984401e2010400e240d1b00070521501c0c1a6044074001955540d0f807000030158040d02514000c900b20b0300c1d40080070080720030a46802400c0484003605117558070090b4405491044400400041200c40495130140c01881144600300700c0381019107a0407400b095100c100c403011492605518459030600050503080036141d5504881622000e00c4c083c1858081c0c044070840d0b2058034205540000d440c02440820b0040e00c600591100c800e111a0400c0e041120b250b07080f9210659443d46450013107a03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 779159190 1250 779157940 779157943
    0x206010f050a0e0a06030203010c0507052b051b011b02010b0409020f010c1406130201081b040b09040f020c0d0809030a1d130c08160207050603040602090d06060b07060e 74
    0x2030444000524101c1141d09100001c0030aa402406201c0e2250b168080403005030303028041c1c00d840c17034813a680d107a444d0303a81402c0c0f061a050309450101c1001c401011780c80a103e001c294025210951801d1240c0c1d252402a100e001140c81d9444040c0c0d43d501c0c1c866042c4081c420580708840120866000b404166080b404210071250502d000941c0402c03090740e01825540140c4004030624011018251018040d44001d0b051107412108046100c0302c9040e03907811981c00c120300580000c080514417002411000701001d59204901400303036000340c0484c21012540c0ca40d004004600f204003000e644995480b90042c0c1e5561995250f200407910150001c0c00301c1c5000001d40e1030042031a030f269500040b00200d103c44510400d1101074200c0d10510b4042d541d4004c1740142c00c6100001d60b1041501d182008444841d40d00c169403180840d08100c03020011903a440c410303640c010341c00010051f511000f01c0000f54107a000250024011030405178001941c007204400340c0702e0b10f4014107081c1b104900642c1d446 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 779160440 1250 779159190 779159219
    0xc08030a03111305310c0f0806030601031b03060f05010f150807031808120402030f0703050a02150c1207020a05040c20190525030215070c09020703030c020601 70
    0x401501007980d1013080540352840350003aa440c016140400203d070394070709403060300041e00888030b00192139282000d4141c7e80020f1101e01c0703a1441c648400e680c00c1640c0041c0d1204130620019041040301c400c140008501582c03654003c1d07600030300411903000d80301040c0025001c2440b038640d00b403031086800224400f50240302030103145156602e41c1e040d40c40d2402500100505070b169081c41014400507000144000020180100e044030703a440541750500c100b5282002180f96401c45070009042000000c0002441006566040b5400c2410b450b103600e210083d401012165003162190881510611903100700611301c181c000e0301c121b403071680c950081c0f0081d2175000b0081c0b00011499541354900648101400c5018014541503c07407552030f400340c0300981da1904009407000d4001c084241413038811844a0300060342100492001c051958000403111480f5400d800c59803c0d001440350b0800c22007110700c4001e0420303500115100c0303004e410010001d00410104101511a0790b002080101d00c20150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 779161690 1250 779160440 779160457
    0x100c0804021014070212030d061406040303031a061204030e010309110f03010b04111b0a240b03070b0306011d030c1c02100e13090206070204050402010c0c08030a0311 73
    0x21412190030b07421080b030304040c0300c40756405043c0d0184203841c01643c0e040101003d8040c450011a120300d00740c1401c2044030050f41c07044401150300d600340c082c5500c5400030f44003104c1d0036080c000344201041307420000300a100304110303601000c0041d1300c03048041038074034150050b80240c2c3c56039000d1202c07000650840351740000180100002d9138401503180341ca8407010300314030005000400c401c3d03081d00c013140660b00030700104600100045000003248500c4008103a10070902401083c08088039100e8040200f0307603c43c14218100242d0091024100507006150440f40160450304055500c0c40b000a507500159480c600081200a06100c4558010444101d031200207001d040c03024503000800070074480d20150320b440e0f41c5031160391201594a0008034801c04640d619554801c86005003044039149803c00310003c414907021341c10016880c3c036019078002070741c143c800091a4130740f40016204825245402082c0921090340855008404005855940115141408003031034952000100c0d0080c18003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 779162940 1250 779161690 779161699
    0x30301030f0f0609050120070f080f13060c020111030c06180a060e03090109060206070c0213020909040f0219060804080a090b030903070c0e04030c060f0b04090302100c080402 77
    0x52000c41c10074050546024441c0c055120503501c107548400c2511100e1001781d440383d6460401107001d403041541c2140000841034007070320f04201c954030034500b00c000d0750010b00114400306e10341401b0740d17030b00c0210354074201404900c40d92595601d03c010700c2c010400c04201d00284800d90440e034501e030f000040d1040125010044c15482c1d031f600140c0c40c06100241800326991007110000d0300070409a00c90034a80c11520009903a03150380c07180001d84812100d501003021540030f41c04104040342c0c4100b240c0031f4154129848842c40d014201010701034000c041d90194020019024007082020b2400c08104842c03080c5c074130201e003101005103007011240b00c1c41408040303039800c00000c2c00501e58078010708100185003086450692103211442d1144c00032201c8242c0ca41c4002100801d0000080a020080c04614500d10340340c5415a80108411a1740c000181015203a52a90701d90100c250060804c0c80340142c020072061040e820000c0daa884e040612440c11031820010305856845244001c0c8203980140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 779164190 1250 779162940 779162947
    0x2706050603010b0a050d03032d060527070c03170106030b010e06030c0403240501080f0f0d0c02011125050f03010c020303130f081303050d081b130504020d020301240203 74
    0x85054004e07000d4000c04c0e9052028840c10109901e51607540402d0032000158000703006070501c010300460506010304e33503446081c07481e4552103014400c21025880b914520b0000240155458180c90503501c14080507180403040300046203103645903101014424090340c1d800e00c404070000c2800a40d20007a224000300c500108801d0010407000500d2181324044014007141b035403044240c0340201c6a007a001148036801c12120150012010060b83c204134210b00f004c3e241c000e0400710003038101200c81308000d05103d070700c03c004441d5190a000c54a1091241d1002c8a40300344103403100c4040842c0c07406018450042400c8048560805106080d103141642d002503103582c0307403110982180c8d02c044c002192580d00c07200410000446400c050703e622840606004041401c628060742000d6074108403004201485003089003d58104d403110f102e0184408800d5556828414150440c02d09604a650054000104411500040c0c3e00543c100ca01201d0707155680d1101440002d0816480d0040c0801a0300c2403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 779165440 1250 779164190 779164193
    0x82b090b0405151216020f032532010c030b13090f050f011d0c15030c04090908040305160b04052205041a01060c03020604062706050603010b0a050d 65
    0x702c110b841582c440e00c800741c180210311103a1000b0300b80807940c00c80d1aa000d0103807500d101c1e404104181d0031400b1040554101800d022100b0309e40079101ca190543c43c0c2e00d2004200074000351a4070118042c0c20722252505800020120060b40c0071511a90000c40d071a0040b920051880380c400d44030551401000c914420582c0d46510000d05204041981c0d221800740c10345000070340401c010143c00448400120b5083c1c40c40c4001c4e09000604d0301d20040d1600411403514240d59070080c2d11402d0306401d1407503616a11a4049002c1034012600124401440d05a401c0103100d042d501070f208682c81081100c0045541060000a4112622603500380306000e1100f4040c510b002c04480500e0710940307240140c110368400702e0070141d0b0300584094a441c2c0318110034190002001c0b04480c0500b45a041c004c600c4022aa0f00070b5454000800103414140e640d0005034410315001c5940b1955038030010015101511414410010001661810302ca503207400580000ca081c03490300542221402824180c104516 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 779166690 1250 779165440 779165449
    0x1003140601180b1b06040b0105011202160f140a1a0702010b0a0b0d02070b04080910020705010f050c120307080109050f0c0a0c170d0204030b010915051504082b090b0405 74
    0x44c0f0000303a10b501c40400c000d950400c100491140c1d00840581507103526041c005020003480400f5220180d00411034096952403001e001c55185134412108103415545080c5006034075603080d46110750740999140c900600c20200109a01c1d5464410780605c1c540381d80b50168200c510f00e0010039040003c030b18040002c0344020700a45500380d0f0031500945014819960451030f40000c560490f01d80d02c0105400da06030030b2a140240d00c0c00380c1400246485070034940081d001170000d10030300041100001e4030446901060113084080980c0d688a940c5034142140003809005007400740c0d0100c0c0380f4040c0062481c11034400f8042c00345c82100350081c54036101c20b000315150760a9a9055503c0071141e040c1119444021000b0900d29072910b50040e04c7e0350451070702c0c0711403a8041c0c2c0160710090600c840d42500e00c1c0720410680803a08126038084404900328541c01060055501003640b071700806c545940f01020456032800f1401000742e140104100c51030341030706c14110a01809004120901051049060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 779167940 1250 779166690 779166697
    0x10b030d020a0f0f0803070306090f060e1f05030a060509150403090306052205010c23180a1716050d050703060e070305010f02190908030a05181003140601180b 70
    0x35071390005410a0039120120580e00c29580e05c40041e0340c0d80410090350500d8414400103602c02c5900340103003460002080111407000e00840d5800922050a524140d401c05001c1c00502d005030540c3d14000302410400001c000c00c8032580d00901405001c032810051251a0504c629856190041ea1905580300c02006240c000d20702411804007448002204001046004c03901e4499000806c42d024120001020665400e040340501000000001100c25428050b5841036144211420307184081c140000c00d0b000b5035500c0040b4a400e20b8442c03221288021880090010008001d015012740d02d07000d0101101508130301400c0750300a40001e00010700c880d04858101801841111107140c0c0381d849003401c551040000004541c0e000070381095202800060b4070070315120b81010743c20a890842e00071b88920840400c2020403400003054450366203000d00e070524207100036150000078403601348041c00610f0070484040304210b0800c00252250b00c90183e070f070b2002200f012031460540c0b0f0519201803a40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 779169190 1250 779167940 779167943
    0x1003050613060f05090607090b090105030604090c0308271203070b0a061503140601020d05042c01080c150918040c2c01052b11030d02010905010b030d020a0f 69
    0x6032644440d6a103003030f5500455000c0d00d82c85e0064440741c107080001900b03030003440d84081d0300000c00b8080822960380081c20b0300e0b849070085d940031800c540185414141a20140c000600581d0003140c0c85070f03030008609a030303403501042400c1c00340c034020f82104000560719103040c04401a8020801c120014500002e02904a082e4034000b00c0c0d80c5840c1c28180051105a40074480000d503121404035a4580001c12540c2156003030000d04099182080010141c1c4203600079600c0b0304105170901c00c2500d000d000012a44440c01d90900495615180441d44500c10707a04e80383e100d260302a21811091030020111100d02c100144509906030380c441c0341c646000740082054902d901385c0000080d91140e4900308826000e01400c4440219001d12544c1606d810180c0026006400d280907040f180740048060303021001c404020641e084200d8a40840c0225004c3c402940600881e2014500315030150030031a982d0380f08000a2015100c901c060568030f005190254006901c1144840040f03130b8261221244603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 779170440 1250 779169190 779169203
    0x20303090c042d0e0321061e06030907180b0102100c0801260d110f0c130f020918070306090b0609010c15050708040c0602150711010902130c081003050613 68
    0xa598001c0750035074001c4411508840c281982494660321b40c0c4801c2c0d60700050480f1014001c501e200003400c144900c0c0d0840d6802605c00001160845a04105100007000440081c0c001405084000c0c005408140e40c01c902521030b070810700300c5e04401c90007882d01d03240c9136950f0b10160360320307168009110002c2c01d42801600052650345424018003881036100d00100d46d26140d0651615441031403911003640740700e0f102c0780c1081041d15855644c00036098a030111904000c1501100c14880030024810245d045a1040800720303003696074483c46150510407201c0c1e032001c004a6a541c580340003607076034034404a94400c20030007101d41258010f18119a503140541d08000d1940f21207585901101c2003901c840d400300342c84030104010001c0103807036503000e003036148041c0013080c0012820b00c60307120001d0303c0407091010340d00706080341440035407000d40e0b2150010007040481e01008602c2e0020800350708844001840e580004000805008420007142e5001004007800c1e030b1000040c01640443c0842102d84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 779171690 1250 779170440 779170451
    0x61b12200919140f090103151a1201060306052a0d0b0a030614071d0f060c161e0e010e15060703020d0f0905030c0603090a060c020303090c042d 63
    0x1944507218808003d054000100301c402c0124504120b0100440745040c1d104207101c0300140b000900000c100360f0300411180c0c010030040c094038404a184c0076503c440a4004e5103801181c1c03d02c0f1015003028040300d004010030400ba45607c6040c96041e00802c804070780341c80c1c0340740c2c41000c4061580c00803c0d840003040d4000804070b291000045100480740d00c00d82d08641c0380c9081c81007032210a900140c100d05141080c0c1c8290424009000c028080603400d1881103000c44d400c002c054031003c007124114924882074079074402c0d44901503148203140340034014410403e0b20f50406000742407129001510040340401c0c2180c1e107004421211424020302400080d00d01d010003421940b144005030203418400e80152240c0c000403a001040c88181c1138003036042083d100e1041000d9100071580e5a0012000e4039002c5e540ea943c3c0041c546080841e1200428442c070700034220860031750200146001c3e40c0a039041d02e201114603000c100548446069070591200c08200c1d43c0403484090341e81c0d2500c3c2c1d4203403401065 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 779172940 1250 779171690 779171719
    0x3100b0712080a0902010806040231090e03070302030714190f1a01140402071a01090c0f05040807140111060109050106030e0f0c0105070c03061b122009 67
    0x815004000200c420324880025801c9142d00319102075030000018a00700b0440c0d0751500003c000d100080c0000d8007071640014480d003038030021000300f29000f030840090000c9520150354a14454198894550b803d880c003046c0061811003c07046822858159008600303001d0b580e1070f01034506031900c609401c68803c4800c1e10903034190074891060168040c910448081c5481d0914840d84140f100000c010019044018003c02e03020f84250a10130400b50380042c3c403045a0b01d000f40c9903210380411441000050400012080542e400c09403109000382d403400b05c1800d101c002070740c05025034014041c031500100420b0000c603c0d0616005000b003014900782d500104410704039810420283c000c501c040e030f251801885125054020184c0300250780009000c828800f40001d034940750800001410403038002030a105008c441c264402c0615004682080395608401045030302880303030325407480032850020360242c0b08015031048410404e441616401c0c604020f000d401825402070841341c0d8271003460520700700c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 779174190 1250 779172940 779172959
    0x410c010c050c0118030b0a06180c1e050909010311041d0a03030c170a0c0908240a1506020a150207050a1106130b090307050409150e01020918041406010b07080310 71
    0x40c0201054100048d146040c03a9280e540040d1404041c0d0315282031604140100340e000139516400f0003070342c00341c940c80301c8400412101c51181c202070b107900c030100b04004000c0c01003802080a100710b08541c1086022000c40c01480c8013284d1441c20303c22074105290840100740603070400404c0820300c0c03502112480c4402d041e040c0d8a2425541c15804e5650381000140346608068664042c095041c0100110303102d11221242e41640c0b48005da0030140b180020071624225504010700500b04060304107110b0751039581c000e690f01d02006040d0b5185403011600e8000740b0303083c421161800d80000242180c44c0458072200c4412464800300d0360001c10400c00202c40071120318100028220f60044140c1c1e600011080514104403074010600c1145424000c2c400690700340307442c0415148144000c41c03140d0741e03443c645009010381072321580c02503100d200000c4402c038018200d034401e920403070745012289008118160350b407400340100200c0050030000ea0004c00d00c800050359004094102e0072030580c0e00c0d0450758 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 779175440 1250 779174190 779174213
    0x170c090d061b020c030703060f06080f101401050d0b0402010c05030a02010b0a0905072106030203010c0806180403050901111911010215060607410c010c050c011803 72
    0x68416940d91890031410b00c621080c02c2164400a100600340c070041540000e071145518840244091307543c0480c0506400d15800c24030090507000295140c0f0700010301000d40f90054040d08504082c0340440800c03442c1e40900c10203041c1c402c00352827960544030654600c0740090300908181e05018039511240c001610800013010600c00c558004a560a00a418800d21281d01d4024031401c504101c100000158440e2070001d601e056899150095101444403900400003600041c3d059402c00280107071182d040b03003029000703ea040d949600c0400310013500386070a5034113880c0140000c40030001d071641d81d8410180400b0b16900c080c2500c60786441d92501c04810042c030300c1d04440080b808040c2c02203e41e0144801d01c0c50500d4644100700ca440c1280004215200b41c480003014104034084000c5810010400e081e081210f2002030210f040380802001d03014480380c1b071a08127500c40c0e4580c1c5c41c4107500c9242d20300d0200e540040105030080296005480c000c1c800480c0c0019400c01d070030b000001c280b216800c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 779176690 1250 779175440 779175443
    0xa0f0503131b15020102070b060f120106081507030c08160521180613020d06020408010c03051801090b1302061314010306210b0a0605060d0b09060907170c090d 70
    0x210311010b880d1a1007110300f680041078002c25640705015100205400304881ea07030010703089803141d4502180350002803400104204101840d072800d10049451200000d2000c2c1e0070461140d08030703481d660030718118159880782c10008002418040030625500d000c04261a1303280c40703402c00d00e04142401160007552440d10400120a000300410301120100c03940e881011401030b0409040361b450500600f0018800b82100213000d4400d0f404604180100d03903041e0740240070f40c07400901603b032518200030b0162409440d51103000c04035407002220707a4014440c01002560004440c507103591a0152003001800c5a001660000c400300706c07410415840c041200060444285100030718403003540014119111500510100041c000440c450140d21325094a4001d42c0200401c0042c0d13a40842c0c100540403075031056400200211b94500c001050760480c90582c10700303a40860362a9603030002c0100100b0b0559400000c02c15800740316030540e884080c0158007003034450b00d031440c00c026030009c114a043e40090 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 779177940 1250 779176690 779176733
    0x6121b0a052205010f030b0411180412092301030203040f021206240609091008010e0c0102100209060901350405010b03070e06061608040324020a0f050313 68
    0x520040100d40e1007440e001d0690305482e900711700d04507551840421030141014010140351082000c050380c5040c080c2d50301c240e45404114507070403d03140c00a08013070015815004111a050003186403c1d201015030903403024600c103203c0007420b6100540c0254406081a10700303803814549040940c5490100c070303034115403007001803070700f450400800c000c0c03990410304802c1a007100e841c0080c160340d6131106851b41140e04907007481d10f540f031703603408180c000c80c440d0700c078400035400c0a604401a91011989103c5030100381c003610032030980409078008900c5142c0d00c0720340c0f0160500c0081c06552040c03e400c0b03210300155000389008102c0b601c02104540450003100841904002000300b041028002c40003210405c0e00100302c020300700610b0280d02c05000381041e00a65020801c560f03403c0041042c0c1c4400e50700619200d03642c50f124102070158104021510000341c16404c809c0150b40c03420b02c00c50b22002181d0340c94080b00c1d41446412200c9900260030029600182c400d0f03803000c100c0e15000341503051300420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 779179190 1250 779177940 779177989
    0x1170312010f17030c06010302060f0705010926091008071115040309170d0509130219020105060d0b06060f1b0714011803020418150209030606121b0a05 67
    0x420032140000703c000d0301d15820600941000c100009800b90540303904030707500d545070a10407061407014012804041e10070f6081100010a00001c850f1030042c5481c0c7c0a0b000a04484000340d40050b80f046406082c0c1200540303407180c0340d00d0700c50b141250b00a08240380c015541c400344076100c3d107008048800f420a4074498010f000070103411009040040420318840400034403000e00d515103a000000c0150284070000500b0500c80d941c0c400c42e0707010905400f0007152619480d40b0161100c0d10554018030142d803a19020400924110b4a0a03a60380c0c0d2000c50480c041c2e903070300c0a2050b00e07045071424403186d030b2044c09261f103d900020078030125682c01030000c0c0080362401c43c40341410f01030082c1d00d6041c0681d80641040c03508002c00303040103598040c0c90104010900402c003200c442d441000251800c1ca0400c9811511502ca8008040c4003408500310f98040e15190b0030440c08481d0b207810791825511000014007900204645848017840051071420880c0da42c5011880014120080000000041c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 779180440 1250 779179190 779179199
    0x103062c06061903051015170604060b0405040b0a1817030a1407050a030e2401090c09241116321302070c090903030f0e0601170312010f 60
    0x103c91401401010400d005803042c40d5484031900d0324201003462403002d40b90600106030b14003401031540145035a548001074085900c040644452007a5821030301a070402a00386040d24090103040d005503000107901c0c0c01504d03860300f280020329142c0390030855a4581e04122002c1004401c0c544500c0b10910013b6a0b00e01e021211802114100071100c428110204c0c2444907941e03000065807221030550034001445403440c0502480c2038103140030741c20036107903a0186440d0f01000c418100d04942c111003085c03142e9210346000b40d5a0001500828141048284c120f140700c2d2115600134030341070913900f0055000c0522420190412404030303001e54200038140c02c104401d100c690300610000000405500042d03546044042000c541c00c0500d43c0325440c01d44051460740c4290f412179021560019490482d40d98a40c501000382541d2601540402c0c40c04207180794440b410b014003d00c0007150b0002d4203007a820a510484948000c031003180051005216010032459424141400b90141c5603031440441d262 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 779181690 1250 779180440 779180449
    0x70e01050405070c1205161202010204050a14010c111c080c0c1816020f0d02240403120e030903030310080d020703030203042919020106090e060103062c0606 69
    0x5040f0030200700075082c041c80415142000603a911100c0d1600c1c5a80d100b04140080340f07450001e002400b116008400c034400d01e41c0540c0200100e0350243c0341090b0259594040c640d0440b248503001d40420442041800040e04a5004007a00c4000070003009000001c0301c0f81d01604044204101c0b00740c8000502038119050400246c6019001112019540c010b519042101120060020b0821400ca05643c0550310700900c0807502c01c0c800d2000310364002e40c040900960380c00c0b10034884140b44250070b50880c0c0300142501403a00c1203425032681c0100c02000300446c0018100002d0001207800180000801c41d501400110b0240c2040384641c46103a00b8040403c2c03c0a90100782c3d00c0070366200c46010800aa004000c5e64100e03209240c1da20080d064440d180580c92401020704890102c0c00100d03200340c0e0000000c1c203419038045a00030080c0030344400c6200c0440c0d11032620f0003004c0c4c1c0002c00400000b0796a8201040402c0c81b42108010301c0907144881606200662005600780c100004000c50b5007403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 779182940 1250 779181690 779181701
    0x3120207150b04020a1407030c050d020604060c05030702060411040612030503010302040c080403021905120d020309060106181703071e050f0c0109030b10031410050130030e03070e010504 82
    0x84804624117403251101502e29010044c2c05500004003007850b00516002e040000300c1c498120003070303036036034201180c3c025140d540440e02126824901070070515040d11610503284a40c20680081a194556448401022400541203540591101404102510001c1a150040f84030b61209603c075415441000182e60921f4205010041004200004260b00185400c42c620306911446450300c82402d01f642402514401d4106100000500f0b140070301b2568020762041049006543d0076903210581100c240400e1500c00781c0c2501c11401c1401070140203116042c06801400850345061a82e60300c2844a0003110380c5c006519404120010621000340600728940c104003000e466403c140c400081c102e03820ba40405810301001c00d0010b6101504c203c1501e01440d003002c1d000300d01c003106060700e5a859590341c01c400d549501345000080c04043e07940100c20208101c80c890125040d240315011210401c441d003d60800148008100e0182c42c20301c0180080c180c5150685c9841d81040705001c242c81c0e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 779184190 1250 779182940 779182961
    0x20c0402090607080f09060301060c02030d080603060c0a0516030e0a0906030308041118040506010914090d050c030403150f05061c02040b0402120906090601050d0b0f040312020715 79
    0x10300402045400795584011500143d41c410f06264550741c003641030f00214007901c94480d030800d4000002180c1e85800a03190303400c181c8210100c52140c0681001103c100d081556500c0c1c0503806040418161781c0240040d002e54055450400d00b005a804810481c1e101664400e40128001c4400c0c2c6005040c0307032201c00080d14000100b8404a8031b1580c004250300700c020400b6185021144a6251580e200b007403138071907060440c0080700c10b0b042c541007181c0c0780c1c0028407620145500d0680d0100300362a5418000c4d01c190500c20150640f522200c0056600c3c1d40188200f0103640420000800020004680180802c00010001625102440301e00c012140c01800d4113100f041442540381000c00c2c0c10403810320036541581c0c0861601003030300114001e4003d00c030f1020844010501040403121001550324800c21401c2c045071000d0742d0f140140904442a620040c1c050300160000034000e40070f0380c0110b5040740c070034608400c094110704081012600004000c80c0d10a00e80245c00301181081e014401858 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 779185440 1250 779184190 779184199
    0x406060e09030f070309030b1015020708030f0705071a0d0c140a0e0a0f141f121503021e0a32040e060c0406030e01060e0408220605070201020c 63
    0x6060401c0000e07a070340200000054512400540703d020144104504001036034071089464081c1060004400f81c80c0c0a0f02500010701c020800b0000d145200003000f40444079440040d500e0045003102c6120f40344e11241c82070755644910007000507204180d4101c9070090406480c0c81e070700e41408099040599130b40c2030401c0d0800c62118000c002081e0248215545481c5c98208094103a020801007100042541e2004607050400080003500044043c1101d0051108403030041c3c940741101c0903520385a42052801c000294171540302c0f201070710607500c80c02060703001340004140e00d6074950000f81440b20014414a07141c01e40700140006050020301400035100c0c81004001101391101d110400346115010099503072a202c080031019151356029440b07030170481c01030303405070f26251126040c40c2d8002d100e0200080d2900e101116140010311852054807580c3c24000040e07211515540d0150700305540e120a0b0481d030f8200c0c0c030101c000b83c102060042c803040d22500e840703000e00e00000e803c10400b038800c0d6024 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 779186690 1250 779185440 779185469
    0xf1205010311040228050a080906070c08070c05030a0c140928020904090809010f0e030d14120f0603070f0f0611030d0e0709051f030b0a021e03040606 66
    0x16140300b01c0914080001d660040c1c032100c80080803042c849141c0d44580042c240352010a48103035104000785412416502d9003c0305885644c3c0043e9500000c0703500500103055078814000042040009160242c001c3c1c52004036291550002828440b013144201e503401c070802e80c108100010800d01c3c9040b1031040350340500d140381144628201e4980e082040103e50b031302044070041d5500c242d05462070140003038010482d1036920b1a0120300b0750701c214403150200f40040700c843d0309103115000381e81d495507000d005000e0382e01e42e402d0181c0b0500c228911500d08a2000c0c00800720342d00885d0002e51080d000710aa162840c00d03c0814542001c41302e0b0050203603041051414044a040c105c00082181c11901d08080c1440178110001d042d4001c42c50203060040c1001200703049103d0000d0300d40151044140c4c108007035150b40003c0300000d003000c56045040d8124182c20808100d941c0300071907100034400c00162500c601e200502007ca18030948903182d6001c00300c148001d0100c64492840070b00307400941e0101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 779187940 1250 779186690 779186693
    0x6060b040f061706132012010e01060512040c0306090609060e030c07151e0f0206240f04150b071b030b0c1c06120312050601120e01110a0f12050103 65
    0x8508008007150b02480030f0124905d080701d1a0352010b0080750807140c6003a05400b84604a880c10340c84060402900380081340041448000c668001d8100d82241d20381c0c901c0c0940308801304610100c014801e460191071602c000000c2031840c092880720510a010004046826140040c101d0300c0d843c001c00782c2e03a8000d01143c0c0008100040b050140c54031001c107100044002a000c50700c2d142e0324200c074400701e203444d80600e0010750080707140a50400c840d020340d8102d6a50300d0104624140200004550344070729460507440d03007404c1045240b041e5014001041c052240900070351040300a50003000c901c42e0015401091001034482c050300c03410f0030400e150045145880d2095040d00c080c100c8015144c0c000b404c1441d030304c5041004803018000c54814040155680c0750203021020b50074042d40030880f0000b258800c01c290307219140c420041612019004000c070030484000b48003c0c40c440d000c5650324864110030188a8000d050095180d80e02d448100307460210042903015401c001000c01402e0070b00520 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 779189190 1250 779187940 779187977
    0x5010906050a0e0a022109070618030303051305121206150a051c09031706220b061308031309050603280b070933030903050706060b040f06 61
    0xca8804030352881250700c65941120091003100d680300154031106c0440c458003c06503072414450103091042e103180660701c10054030000d0000c01c004002500301d940520000f80607034041a04602800c2e1229030b683d0080d540c40786000c00a104113032411002040c030010708074402c1491580030b00242c40002440d002100507103283d001d4030540e0000e0100106030400840400007541e4030300c0242d203030240602e400904000c0c0100c2100724500019800800014440b410b2240031200c0c5030038522042100340b41e50700e1052000303000568001d980040c0401c442508501c0380c0c10010060310952000c0c554410150308031050802083d4440e200242c03c160401080360384c041907001c812030b810342500c4501054924840c3d00d11144882c010b104402c0c05003441001540055180143d540c640d0440c036282010f6400c1000b044481503034003903005a0b00100c1c4440b0fa11907003003002998403030f090050400a0550714001612225000211000170104040240d256041d101e07100601c40703400d05002c03010020182e034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 779190440 1250 779189190 779189209
    0x3031501030b13090f0f080301061b15050c040801110405010e0a12081e0d050103030806040b090c0f0f03070305091902060a200708010902041a03190618060c030501090605 75
    0x141c070040d82c5286600a1105c00c80f540c9418690050010f0700c0d2000390300e0300e00700702e810078008c171303000039284200400b001c817212006041c1c0d050f002a242d070140041c001c40391001e024005d1426507070080522002404071402d001c0c04658102d8040d040f52600d042000041140d03c11105042c41004406400c000032101181d4122031030750045a01507507125040c1d44140c0d0014064103480210b007001410f2141821994460b0341a244030340d03268001629103000b08019600440c0e81c441d8000d100b40045050001c0200080100c00403800c1094113010410f800c05a142c3c0040300d0b10703070100780c492082103002c800c1880488529500e84951110a82b00c0e90041a01c40c05050740440a100490101883c00b18210709402d1804a564044640e80c7d03132a030141501900c42420200e0249040016040c600c120130102d00401d03803c081c00a200211400a480300021580c540981d682a81d80b100c50b18800c0d4203405448485015040c0821064010b0000904650050b44070560b2135140c90070a00c02c907a954184e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 779191690 1250 779190440 779190469
    0xc03040305030c040f14041d0c01110f0604051b0103050c030a0902040f050a0f1a03030306102a14070806070e01020708010515090c090f0d1b0803031501030b 69
    0x20903100c2d0f6881c01d000c1c101d0711403a001006980703c94400040c0d00001c5422105d514501603034280012407642061628089800381401d00c135400090000d44694400c1c0301e0b5501400030714040745c4038032242d02c1c00c0900344403054405072195044140659014440c08c00700c00c0842c00c0a00e010841441d10f42c1440b05c4501000d00b035090210703110206070041d551250880c8581e40308911040001d82410700c2800700070700f080c51407920311078281805180c0201030040075040144018000c0c520755034810301000b01140100c0000018400c0141c0b10010081c921041d014460288420350920b9000c0750402040c0da5000c80400c000c20343c00032100b0b2040000214415400c00b07580e003007100303c00c400c05c00144e09000ca10781006902c0d61034003042011101903900301020f440800e881c03000d8640c440203548042c034400e2003006508404004400400d07414882e4031b2000b52806560b0b900c00a0320180030303258148540340e204d402240e00220505c130803000300d0785040340d02c10400d00b420004203400300c004c07880000d1464030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 779192940 1250 779191690 779191697
    0x5070f020318010e030f010f02040515040302090c1308011806050c0304120f051b06010611030703020a0b040c17010e16080a02150415051801081e0702030f070302010905060f0c030403 80
    0xc40e401540c17410810800104205d000911000041c00300c030300000e40080c440d952181000d4441c003156403601004450507250040c040c0d04080da16908106600da01000e015440d6600b000c0d80041c10030028816407404419403110001400741c00c0c00d200041e900c019004250710402003051000040c0f403010100780160060420809281d100c1070141c81c10302920711789800080d40003161440e00f14001c105203052f5202c035119440c40030398a0750050340e2030003101001000340e4011134002020481813010030741d01174442c1d215451070a4550181506c81c00e0729541d007c10507034403004503200d545020b01000c04142040c400e00c84405103410403072981c2d07818200e006401144401c410040b2909103904071000b0f0030140b200c0d0b90340c404070b0302001081603200c4990b50301407250b4903007280c90541c480c040250054480c40e4800c00640600710100401d52000780403001507210410910400f81401009806a14003d400000b204c0049080050806d100205802803210a480c00c0103c000a50000d03a03030440c0d007526 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 779194190 1250 779192940 779192957
    0x918220318120b01170706031a10030c031d0c1908010908210f01030836041d0a0b07090519090b030106060e04020919080105070f02031801 61
    0x20159a148203803141030210091408001c40c00d215141c1e44001d0306881883e031000715070303a10058058143d981000313160183c0c01000040140c0e900c29007002c00c13038051000075a0700c20800c600c0014074050421480c1d8001c02d403074418442040740c05108458103031042d08000050301c0d1030303e55040e80342e042d030000151103407500500c1c40b40308030000d4164901a1250b84000c0040100500303202013590055500c2c08080c3d80f00c00ca00b200210b4894600c10700415900d03180c1c0f07042d43d00b5070341c5055a64100743c40031070070341d11101d030301040d0f004001568440c54004810b41d80d802198000610045c0c03000506500c0c280d0348214540c0f011210002040040320360000720301c0d009034840041c01c5030366a0480d48400d511044c21200d0300300c03202d079050301c9d0021a54801800c02007260248141820703110540710320008980808445002414160000c22072031100034a020b2105a030100c41c50440f40b0b094201880913903486c0304010003d0740181850185514a000450034001c404280300c81500d20a5000740c1008841c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 779195440 1250 779194190 779194193
    0x14030a24020403060e0105012d12030c12050301080111030f0403080907080105090327090c03180f0304064805030703020f012d050705040305070b091822 67
    0x1d03416580590303803051050100d0040341e40018044c02c0c0a005150b80043c8420781401460b62504040c5008041c1d15440b0b5110f52500050503001440e00301d08ac0c007881003505c02140041c0000c80302e1400c082035601d400b5107d505004120b82164100c85000c03035034203820401d0007071003044c201000758007950501e0004016035035070750414149415a0f0059a941d03080409018001e1808805000004c5442090455501d58185001d414180c0c0180311904202202c01140d600c440c0d14006650001040400035070b90011591024580281a002c040c15504041424003006a0241c0307850302c821045010000505030392541d2844034030810f10402e0301c000807400d568000d401c0110054a100f5007140680e51240201e00700a0340b01ca00c0444110032952030b0802002040d40742014141c511201100c8400c2d485409a40341030003080c002e0503442c1032003028000000006e03010080b03036000d0180400d00a850344070107000e11200150b40c070240f03900404050100300e0600703421800c0c408003844842a800414806 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 779196690 1250 779195440 779195513
    0x3090904080c0d03090303150e07032a0210110a27030c060e0307230108060f1005040e070c020d1104140c0c0c1008010509190c030614030a 61
    0x30040300302a903000b540100f60525401d0313808101240c0c020b88052080c01042c034008208000280901c01841d0b00381c0c40030850311803003984545c0c004101c450304c080c0702e207000311007007034102103985294001070f401820104003042280c0134600085140301c0c0c601341032052059010b042e03844180175455944015242800000580642010096803c0394070309104a4840c080200b4500035021054000d1003910720004803a489060300640400c001100b00e883d929094004540300300001d4241c07a48401e071040460840e81d81c80b0f1074851409003d4441d207075158500030304400080b50080c505001e001d00e41c03d4650242c1c0301c20300c00c2d050066115045d509604100c0d40018010469401d107038030b8800144081180c80200200140340182c2c8010844040002d9041041480380c640e501d59000580e0b13440c0100040d0078240c0440303800c40d41448030011003a1510740220308551070380900d440043d031101c1c42002204503841c100c010300c000c1900a0b00034401c1c00d45948000b1212640a45d200410310202248400300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 779197940 1250 779196690 779196697
    0xf0613030c0b160314010305060711030f0d020a020601080f03041224021b03040f1a1b01090c14012f2a180a0507050d0504140f030c0309090408 63
    0x140500d080c00c10303007083c0608180555089401101003440c00c00880017034100403038840c0c120781e4020020802a9170301c25048840000201214800b48410720000024104d210058529104030701c00051700c5241c07005000380f0b4420180c1c42a9615041148400c52400c07001c011034043d213003c46c1c3e2603440329107545800440c8142d850a25000c440e02e8230005914070180740c000301214122440c0c0903d264130203007055502c7e03206510880d0046020090100f000f4000010506a161440200c207418108411000310042401d04054210b5941d111700001c200045000040e0250401c00452100e1080d50300010740f8411600e0344214913100442e041031008010540307500e00720f1084009031030340b00c82a410300c04207240090448426088029000201c40c1c1090003003600c4202901d43e200219454443c1010004d100203400e00040240812200212016500410b805907102c0e001000c2401060303e40b450030101c4c1000c0740d50140d002006050018030000066a111200c119080085500c440c50706c05001d22 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 779199190 1250 779197940 779197943
    0xc09390c060f01150f020304030f0203011b09050301060b03010509070309050f1002030108010f150b07150e1506030607120b0a081c030c0327030e031b03010e0f0613030c 74
    0x40380004101d41c142c030300e040745812914110292152103001075815502a08144070141c0164402d00040020950408a01d1100c90002c0c0002503d541d0300c40424201c5030701210808003241d891541004642000d220350f10050203040395442c1154108000151034810140540e07007019250741180b414880c00380140000301008904480810214920b280c1c0030f50424841ca200d40d52031f0281509120035a4044c141a00e03805000401a10742040100c503141c3c0c01c52041a10002d01403100708504e1441c0e0f200f081d400402803401840d04d90604c00e000080f49900800c0b05000e608442c05101d61541c010f642e5802020081c0c070f000c9100644000411a1040181d004103520b200b000c941c02110349402c64415800107103a0fa090007086080130341030b010389000409880791140500310f51540a502d241d00303060401e02c40d10340740c001610b0102c002071501d02114003116481d002c01400e141240b80074450200218600000360641026032594541c890700d00070000e4032140d2515200e4020540f1420045556a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 779200440 1250 779199190 779199193
    0x403030309050f07090915050105060a0f0201020c160302040510050a090b2d0a0807121403090a060801050315010b070b091905010504120c12051c0e0c09390c 69
    0x39170b8074011070029051265040c0c41302d4038044050070400c8418003806060b180d01a0a1030720b0250119000c8030b48440065070f090440d5400d100303c40d07648205000032540715200081d4071070041e086004000868a0103032200142e2000704204200c40e455040d1104212a15004c00040c41c006500100301040030900c1c680307881c1d49000c107141e039a004804009075840304003542c8a44a403900d03030659a540307000798051001d500140c0100d82000400c00c403440409030103030700d081e01d0800d000d1101180d840d00454200d4400705200750014401400d0402c5044c0707a844ca100c5000c9959407400503008220301c503500003e0503400c04140000c0c03250703004015400420056400c0301c0094400c0e824124000e140684040f1451003180400c1501c041c800c80103144200d80100c501c1b1000005003038165010340c850b83c030748107401602c01c1008050b0300c2e0a100380300c40c2c500490040c1081d00c42c0d400030080c201d5801402c40c2000d901c101c041d002e540c9560030040c00424160003220790324418048003400e42d8050501202000d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 779201690 1250 779200440 779200453
    0x1020d05010e0103140a08070f0204090203190308130c05060d06030b09150105040e0c010e120f03120108010207080304080901140711011701210c03050f0f0f01020a050403030309050f 80
    0xc2c01d128002141241d0142d9007050110000100aa86802802c43c000c1d010a20030b003c5840030503d00900d14111030b00c01030001510075403e90109042410354008241421000700c110414103400c803183c2c990115000d111420205900c0c2e45964004055000b010300401000c41c0101c0000030503400603000e190041044c640a19141420903562a818803a00c40401c102c1e2000190a0074140501951800608003a0110280071801100c0c10425440221ba200c1e034003800704104400b0610a0341c8070408510003a607502c190314443c0110040e010380c82400d060784104035620100307442034240c175041680441c3c8260f0710684040100c9181c402c0e081f9007005014000f84010400c200c28000402c1c800c0e0a032980703c903d03d81152141681c4d1740074401c5900005210141c0c9010741071002a13010381c0c0f8810f0142082243e180c4e00c80c00c1c0b422066050b000c0c0c83e83d1182807001c2d00d80c20100007640d0407903582d400a610b8003501501c0200140100c1c40014103154564421104015090240d0812682d00c0c07011101c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 779202940 1250 779201690 779201699
    0x8070e2e03031101110409051308030a09020306011a030c1c060f0905060d08040909050109080d0606020610080c0105180d060b190806012732071e0201020d0501 70
    0x140500144002c80c0840c0400034144144003040c0110801c2500461602d41050f181070515005454001c060500002e01202c410300080c03c80d501450003182480000941151144185881c00300c0c1a084100100003a1100c43c1d4a1984503040b203a008a00d40d42140d00e500e8410100070709960400e82c14214603081040218681b680c0000c0ca4003220341802d8288600d886900030f00031004260540644902e104000c14002913080c0d0700b04050340b91040000040c0c41019482c1c01e04150030440d500d10801e0b40312841080202d50422a264000514404205c04d20385440605591a081e00303003094184900071500c0d404141e100d10380b078000541c015107440260603080ca0034100070400c01040900c14a04080c0e016a15081c8818140548189400500103642420402c81c1418031103a520100300ea81541c2006410425008101000d41e004404070705603401d482c41e0102c0701c0c00b0170140c0c4001500d19010015803075030000b803240901b05500310500100217010340880c00380c4250080c40c101d0307a040200004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 779204190 1250 779202940 779203021
    0x6090c1e070f0c0902130302091e16091a07030e0a0b07380402090c0c030705010e01050a231f080f0c180711070909050d0f0908070e 58
    0x1d4016120700c2191100a0301d1300c08035030890161240c400100b80b50500140018146404100d0304544803000d030b00900481d100c00003040d440c6c2241d2010211010303045188000383c01481d000c3c040c080107840400b8a640768450307d0a0f81c081c981018081021300e040d001295192200c1c0800684540c50030076540e420340e403d103400c002e0728207000882da200164030b401220700c0f0480742c00e01012680021007000e03501d0350307000c1225424024000000c1035100b00000701d6101c1d401c01c000c002d03044c4140000b084207109001d030385084550040c4035250701c03402c02609017248032080c0300c10300c3e4240b83c003980304500b0348446901d1083c0180450480c0f001100c06c5a000c41c14076400140e22002c03030401d108896014010109100340110204503c040c1c02c02107101140406008010240341031183c1404c86200a944440c018141e41c8503c0301030b20550403810041c441c003640003c1901041da2142400798490f803804000540d254094401c41a00303459100128a0f24101070800690b01d405404104250203040100300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 779205440 1250 779204190 779204213
    0xd0b060604051216060503190e07081504050105010b0405150304050a0b0112020a080714100c060c0302030411030106080615120a03052106030304060309050a0203010618060b0306090c1e07 82
    0x141c59580c1d481c1c030001000c1b482801100d00c07a00d503070500007140702c08102c018000740501c000103007903d000300140031031840002c0001018a1180741325421203400c0038107005084800680000120820400c01800242c46064420710f10b094082e004603900e5949042141c00c01101000080444003013600001d10401c401554601d85402124054485541c889030303282d4460031881194001d20032002840480e140c11107075025010002d00304005015026a5051308403103036504c00d07401081e40407062000b44003007000003041d4144198020011642000881d50352400010314000805c105481c0090080c1c0b071381c0303034650030105500040350704d0b41c03000e4139002d4800c0c0c00a61283d8001034810f09910300710074030440c443e1b001c0c0c40060040c52900d414075600301e014100400c402e07101445050458401a1800d00c00c290080188074000e01581800d0000f60066992070350117255a003c0030710500643d90b035030b00301c5990441425110745607a400c6000c8041150003a1851810480070086040c106001c00100d64 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 779206690 1250 779205440 779205463
    0x1a03072106051518090c070b040506070e0f09010902090406030c0e070f080f0c0f25020310020a08010e060a03020a03050303071209030f1101062705060f0d0b0606040512 74
    0x2003e080340842d040b0045000ba40c0242e0740c1c0400300b109200b4030381022403255400c807096040b410b140515036182c940c5c2445d0148d400f207600b9484041003181c4240d006008070000d10040f0392200f40b80000c20009000594180503201c919640007400c0300c20355680743e12100085070700055038040b03165144c1150060040445450020519280b07038a14500e04c90401d01388031b46841c840e91951074403104200b609075040244545c0040300100000c02c400f01d003071090141006907000034901c9942e060710500d0308000760ba201c4064410f0044c40034645603030700855180c0c151604c0d00c001000541d61500042e80c02e1081c2d902c0a5000b580112010040c00000304c0114811000c42e200e401ca5400c003101450112805d4040286c00107404415695055228000b03440f801000c1b0b90021800a071070705000019280c2e0551081c2c0c1031f543d0145207a1000c680d42c01078541c006401c607804220f4118400216011845550005002c0c503c0040001d03c5039a400040d1000b801002d403c4900c1c20020003d420b50b1159522003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 779207940 1250 779206690 779206699
    0x70b040503010b0111060a020304050a0b2404110f0903071a03041103031309021309150812030708011217070b010314120a1d1206070f02010203011a0307210605 70
    0x400810f550117150110f1000404000600c01ba42d40c41010000941001c5d00888042c02403103007002c0400c0d01048814001c0c110703900b1521a4036038840f07010007480b03008085c05002c2d40c1800304101104603840c0c1aa9041540c1464081e541c4045c0c0c4006414011560010a121400e201482030600d0600c005903105030311503d10842e500c07500808059030703030158200842d150385070803000348807103803498005d03000101c1389003c60f0419648a00c201c88c1900c2040c00d0707010650360b50325401c200301354007007040680d10700c41c0d841100d00d54140800b00a1807000c0500444d030424100c10161000c010f1b9032110b2403a0241c0e2059100d4407402c8510702101c44000a2105071815030364400c07031036006000840c0e0440350068620f2903034a031100c941d80035562100d5080c07025401d005003500303480b41c9446240306020848000e07005007400340750030302001e8501c2412540403401c6a2041c001404000c10a40c0b14500c09905072184544035541c2e40780c21203020301c50032100382030001801d00d4407803d040d203034001e0000e5880486 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 779209190 1250 779207940 779207951
    0xc050405010b0a0f2307031806031a06070b0610050f0a0f0e0306090a0204051e15010f0206040305040302220c09030309140d12200d0f210f0e070b04050301 68
    0x4a040f00d0080103640e01110000b5200a101c401d0a80c81001b0714200d40309003000c540c505601c10b42c07195000c03466031100001c25240d02d0b242420b0194003052070b101460454200d402c058031501e864500c10781c003c02050048004600d10346c1128003507410b60302d40c20107560600359a0349610400905c1d05540390000c07230106e10150341301001864085034840c0b19400b03010080456203910340802000d81009040056004148417500c0101442461810b200f59807000100e21000e51490004100000c11001441150459410300c000280e104045804503901150f0341c0b241840020a01481c2d04503100e0030104891400c642840c0c4650001601000c50340a0303100d4140c0d07259240c410071540489031601d00e40c0120391201c10306c006003501c0000c1110001515201340450000e1642c0740c44045145070641d50b59112505203418a070340901c003401917040340d02e00b003000d45540c6400380011440042013006441d0301c0e0340003148143e00c190301800c2800c04c03002c1200c003c0c40e5200c400c3d4510f078ac0b1a00889001e0350078071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 779210440 1250 779209190 779209217
    0x160f060503010b190905101d030a0b04031d10200c03072c010b03040c14150c12031e010b030907180b1503070809010e07120c050405010b0a 61
    0xa1003980d0480c0d00f104030040c0340082140011005094084c060000e000300350300042042c0c2c880206118400340c454440c582e00111040045100d4a000d1302e8051181e4050912440000c40c4001300d5030b00130741d05003402400d0000142c071500450b1070f22190b103a04503a581c1d00071441c041c0d0040c24042040710f00202031f400c4807410700280b916950b842c0e08882c3c142c0d0040d01c0c200610f982c03c50114241c01c1c6d001f040302404945010040b41c41c00400e0340805004880402400140030f90424818001d00aa40d0400d00e005540c50219003444890231031403c9800380408c0d401a800c206005090b42c2e901c402d1429566890420300d28807240007111145c0a03270b2034090002258189001045034000c10f820801422024034107500c06103000d0980c0401c5002c1911034002c0c1c11140c8030804064000002c0481d540e0f1203242400005280540041400c511a8104040070b103000030081028000d5680e01c040e60040320082d03082414401c0c59680c001c0707810500d028000640c05214501400d80c00d00c40d580e44907020102c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 779211690 1250 779210440 779210447
    0x4111207080615030a08040f030c171f09050709050702011a09060907021009060606270308090402120406060302010f17160327060609022503020a05160f06 68
    0x40c00390811070b0344880080f680d02c2c20784080d000d46102c0700900b207507100c6080341c0d41c0740003a800540c00202940141482442003155451950024005609c80f000007240c0f00c1d10010380d1426a00e0f90046204410880700c80d0b0040240c014103d0560488101c800300343c5d65152a44c000d000450390310005510380407441d040c10000e17808002c806d0380010105861526a035041240040700135024a081d031240342045203500000d40201c289890084038001002854448040c1c07183c4075125a4103580880d01c0449401d0b0740040c2952003d580d080303003895403102e1449000c60004d1140b0034410718407104060420080100319005441664408e91b5041022000d12405071090208200d5000429226000141004446800355000c48205d4a004180412030700c10010746104443c5e0600b81208151a8000600180b405032100170079842034218035000350780c0040f0003c0034559440c2c00001144000000c00c0c14800c10034000929007000580381c1401e00c0f2030b1208d0304660540b06071099102407440018a2501 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 779212940 1250 779211690 779211703
    0x1120b0609060d0b03070e061306051e0f0307290301030b13050c0a08030a031104180504080405061201030b01050f060a030905070812040e0a2a0e0603041112 69
    0x103801181003142610401070280c010203401a826540c0b00c0207113078940e80402010009099014005083d4102a41070014218494000740781d0300c1e0800100b00115194006003c00800705070041e16081d06d040c500103400c40802074251a490720a841d00480c018240d1680c181c42141c1d14030f4086494060031031500c0351400309200250a500f400d0002528030f01e00b00581d4003445109205407800900f03c01e000400c04005a04280c0b00b550001c648144015010b1091050011800e041d036410f05207440c21071350703034070f25410140402c00c0d4680c80072400300402c0c0c0f03050340c0250034010101900c170102620040080202480103076019043c041c0001410b081992079012020005001a440e00c808258150054048041c04960900c0790640c001950a800c1c05012261150100001d60366450b041c00f4020100020f40f00400c05454030780071441011801c0403a03410f4030014210b0341d401c41c15017501941e240b020740c1c440c03541100c2e000080104101c065240c4e103011000841710310011101009100b03a5864 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 779214190 1250 779212940 779212961
    0x30315090b01270b0f0705100b04050709031e1509080a0210020703120e100903020309010906051611130e0610170a0308090f0703050601210b0f191a0112 67
    0x1803c140306100040950000b0030360740c9003198032546001e0703482c0e0301e4034940001c4d048515040c40d1703200b20841007881d2600905130030680074501015403508546460041103008814a40445032030b10030f0700c0400c05d01c030940c8040d02c403000200b0003281c000d41c100401181d00c100031000041c050710300211742c14850351003079500300c0c0c4d010707034804107807403141c914142c010700440b48848214030412541542c071800c41e0081040300c0784a0b42c0516203440e151000541034541c144c0000091100c00c1c00410350751035540380006681608401d1901441c025440440c5080e03050500b400c5141d402d00c800d40691f0303c40000c226010ba4402d1183c0d01906a807040003400c0d01c05100410000c582002d0440c00109200c0d0b0f444075049100003060340c2903009110001da24040d0315070b00441d440d800a00041010705820f1a50540800355011180c503101041d5840410002e401491010008011404100b80e901540c1b070346079a540542c6c1e002c20400b0180081041c0b91100b0040e2a4000780414a90360f002c801c1500403039032501c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 779215440 1250 779214190 779214257
    0x24080d0507020f060f0307030b0f060f0f0306011403010914220f02041d0615120a0323210a0b06040504020f0c010207030903061a1804030315090b01 65
    0x5210b908211214158041440d40180280241c0283c9020070000303601510040c0c40001c0d03180091402c4c00b102586019440740b10390784c1841090310144003001213420071000c1044180d504e5940200690f18030600c141040c0c680c000c04000441d401825038409240240840d001c0d8042d962540c811180360b244102510000a140e01119000030b403110042c0b00c11148000c00c0454038100d0541c07480c3c0428002c0042d811140d01c0001070107900892600c4c0380c0b144070340541d05a180100c8115545a4030380010703000408101188980045080300e030301a02c00500c490f2401280d903184000c0503036682ca480c2c202c0e0544007215450209255800e107114184100401800c0541030a1800007040000c0d00011800302d1062810403010300d400320f0a1005041542c400d8031f54072199401c1d414607908485410103a12000005020f400605a4441103a414028a02d0300b40d80001e5480d4902100540a024844c403201c5103c2040400c5901041d000000302c903c0a980e1202c0c40c0c00c0c400c1303c102501c010004c010620 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 779216690 1250 779215440 779215447
    0xf0b0a050103170310050405070509011e08040f050f0d050306040b0901030201081605160605010303021203250e09010e0108161508040804031502030609010b0a1e09050424080d05 78
    0x32a0f10036800385611500846030722200644d100c002c641602c0341101d8000c0050400121400150b0304090890b50140b40c901030800d090092150251040034060009080c07440c4807540e00d01008800c0000703050350700040c01a02ea0751242100041c0c01604180c4090340f266051a2060302d03503080040d00d80e030490703170140d549040c16150480b00ca11a20080611403003041005c01c1141c2030100100000c0007594860703200024250301d03504000b420004ea8443d502d0300c00004105011507100d03071070408070400b40d2600c2031384802d58070a28140e40101130007103040d400102d008000100c101c440079199040351024019a2081240c031841d03040040c031240114001c4280c600b00d450911032050070601c1d4094420040e4034a041d850703480d180301d40030003c1e82e0a03031841d40010410440c1c2c204460390600407d148012103040c030f44401c0c4090204460840c0c00f004000008000c200403a00c00c03c036180040c031020300200000d0b40855030300b6802800c80310f042501d544c4102d00010745820001600010140542d41e510b04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 779217940 1250 779216690 779216723
    0x2090708090c06030405151311040b0a091e180b010e0c0c060c0405010320030a0f1e0912020a122106060c030e010810060302160f0f0b0a050103 63
    0x40044000c0c0811440c1c0c03058401c5035410f40c032408021030055000d280188583d68101d1994440d02c031700181a14901982d08215500144501c60100104401250085048a40d10011404030015503111039211401c040c0480d82d00344205e9504c00e0010035055003401034a54007144089049801f13035008105140ba1401084091a031038011750308103090998507860f043c0319000051401ea0113071400c181100380001d08009646e0188900502070454168a5000454081811002d80401000998650307190710042d442c0c0421903101d02035000611035002c12869030b5412a10060504020859103501600d004c0030b402800020300d8a180ca0f4401100350b4501081c900889410221001641441d05102800c0c035901c0341030b002c1c00001c0c0c14103a8916001107003034100103010a14280905040c070a44c4402c1c0003040708131418480a407403590901603035595208100901103d800c210180151410031000410407080c0010b2401c40343c001d0385c00000b2611a0190311085800a1000a040ca0301411a003003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 779219190 1250 779217940 779217947
    0x1d070516060e03040308190e15030403110f0f0706180803041710090f02030c01080709060507020102030c061e150a1a0c07060e01140c0a0615120602040311030a020907 73
    0x101c001d001d80700f5a03040944e41c1d0b0301e0f0741c450782010400303080c0031015041141200382d000d0b9100001d1f81c41210300309208104210850784600c0007070005810003942100c0130000c010200440ea1454207000e0032203103200202603070103807942011b02815001524041201d401c0703422051500d410b540c41c14001c3c6151514000b03060810300001410b0840d103001d448103000084031280b0444a0503406101c52803c0d00b1558410141803a1a4000d12414801d140c8123103d0030587c4010001c0640d44241816640d032201343c00140e1131070041440c80c079012b202d2102000300c0540c1603507100b40e034410003040218598445400e810000c40c01c480f20703c0d42220042600b044140e1303100d07581203200c8486003402441c0031f001d540c42c0e5040024030780004000c07901c2e042000030b80c1e51b0b00600340c1910802c9420460b041440301c803c1140c0315404004060503064503000040f060380b80141150004021035207215241c58124507198000c0e402c54032060b1000141c02c1129100e505022400030b0000703a0080c80e80030b11f0b9550a406a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 779220440 1250 779219190 779219201
    0x50102220b0409050615032a120f100f0314071208190e090702010b01110a0308150105120115120203042f041a04051503030f030705090a1d07051606 65
    0x1154454009511b04400000d80001903000300241d440c888400f00c0410201480c41c21045440c0c50148000c0043d0301c403401c40b18461907040390b1542c00d030500316214035040015842c4960480602e91813001400003c10100582034018211840c0079245007a54800000b1501068008041c107000c00800c161840102d0302480303030344190894144501d03910300c10400300d100403804803852001b50703543e0200d9078045e680203151040c00c98103003c010504220b4540e00102080c502801c0503095141e44440e151060380940c2c280d81c40d101c00111074440d50342c0d4804aa1400240c0e0450300d01c0403564200664120400c03030b0085a00ca1500580840800c42c090240c0c02c2a2103503911000080d0f03c0070444420050f03569000d10a078401c0d903200c508103a03114280402086a02c040e0920b140b10b100c81950100a860100c180c0b100003148200a603166611040242c1d81413256010313590f442451054003158012249012000740712908404580c6561f80070f5041d01e40b44558145500c00141c220015000145150400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 779221690 1250 779220440 779220451
    0x30212090118080303090c221805010c080121110108060d020301060b0711030a230a2405310f0204020412021201020406051b0118050102220b040905 65
    0x802190000d800c41c0e0302c20740c1400d41061031607800000620000d0001045030380351028088070325003035481c200020b8075581721121805548268640148034100d100c034030746028919402c98020702504010b1903000b84011000d0191a44800e1801d41c8100c4603c00428903810107a0b2201c80c0200c0031101c80010754601000401643d44000103825030f10068a0070700840c001043c994507420746600c150300d4581040d280e4154081d02036441000c000022500550000b06200034182264a078065410b2009082c0405040050000080359100c2c0400340510741d41e030551005044010442510b9025a09294003400c80c81802004401c80210951280300c561800303506108200c0c11144e140540e001c14180e0300164480340940301c0748071400301541007140d1a81e06c071070305040c021460700c0e003016000f405a01640700150303c116220b100c092225a000d5012640002c00501c2c0704034540c449140660107540443c0070000b607200d8120b00c1d42c1c40b107550b901c1c0c00015035403650721450509007007907850002004014039 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 779222940 1250 779221690 779221697
    0x702190201142106010e061c0b1311041d0f06010f110609070807050a0806010b030a0f02190e0a1212090b070c08010b0904080d09050705040f090c0b03040302120901 72
    0x1459650300c1283d41c100300040e400c8104110b464880c0001d0545149680780c140140020000c207051000c80c8185284000c07a25000020b41500040c04940d0b01802c4654100949140c02c003111501070511028004403005070809203101c81070a032140c07c580a0644100d04d2401a0b5004182c0da580030b0318617406641414500641c002c00a2081107150440c02e440445190304945010f0021400c20303c03902025080a544425500745040003d503510541403180a540030300200220b0b601c1c2c44103802250030401100015511021400d40e901420500c00704002c0110b520844548214108036042c0f02c04c80d0340c2c44c51900401c010f6521100b00c1c2100644d142c8041101c0c000b0041359058045e0041c000c40c42c040c100c3c00161a08140360315003114030f9540c000e03100c0d01fa11300400002500365821541550030520780411200307550710b0020300c0d064441d000280e0140c10580c09000d001e11035840954020b0203440c02d102440d41d954a241c9451100b51405401a0444440c110b0750070481801004171034010316 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 779224190 1250 779222940 779222947
    0x403020306040212240402090106020f070905040201171906141e04060306060810051e0106110a05010f1a040612200d120e09101a090909060708070219020114 69
    0x40d05c000004a004c40c91070624007500140000c2d800c001810902400090008086048480d82c04960b1010740b44520b01080307450300000740859124240c42d50030403140d03000f0111030303003800d030250b0813180c40c40300c40d44c5010703803078088000b80c0ca01c2c420071075101c4494040e1441424007590041c91407038040c80c02d0510f41007030700c48a00000040303075440355070010308034500031300580c1900c030801405075100a4120ba000c0401d55918441c41203810f1846811540503041914121103000d840e039081210903036014200c5d51804040320340d100f0741ca400c42c440020030081d80b02d1420344090104401c0744e030b0901030491600e0304042c24000113035071440d80151311303904034810490004908000441c4078440200448103043c20044e03e445013a08150042d0b11490215102d035424503008980b1100c40005102d4203000d402c104002c150808050b01c22a1511080a011011185400b1007503590303440c0182c5000340042e0014000400c82840400c800d21504444191b040b0290510303001110240320039048520000000c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 779225440 1250 779224190 779224213
    0x309051c02012114010e070f020705010905121608030a2c151905120105040b010e01080a06050a0801020a02240a020319090c0608070203070308181921050403020306040212 75
    0x30004c034002c0100b0740c1d0090365850600401040080580718450540d44580000d000d00ea03000510340c81518400e81c0c2c241c3c00401d0b940388080c500345011f00b440010b189480400728110750f0210061078600c01c0c60719030003201020015104002d220f42e004030052006c0c0b984400502d482c0c8a04040e0752884480000750034000440300c1045044414041c2101191000031140e4031000641e2400b4010401202c0812000c102600003034100c8040c0d240a5041010b0000080c081b903a0b03650112000c0c0101500081c0d1242e01c4080c014000c0d80a074034200d003d88038001c5110000303906203ca030030194552011040f0180c42d092520f0300a5000075220303182440c10b59540c00320b44030341442010003480c01110410381c181c1c90100040c02c04a001b40858086400030400e490100341c010780c1194000d42e2188407002e0300c0d0658002141015040d440c0010b403001d4550001741400340103401071404061708011170004112041c030039a1907103d10304c4004e405821880004000d858a03801c828040d040481c103458800400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 779226690 1250 779225440 779225471
    0x20a2a3f030e1b09131a092104090509030405010903062d02031b0306281e21170a020a1b030c09050f1605160309051c020121 55
    0x5580c0103501c1d111156510742100d00e4413101c2c00d034008180e4140030040317240c16215141c1d4104244141820710408130045010340e201002000000481d05618140800b01c959220381d4561292042c00e544d2810303c00441c1148a011013118101c903030503104c08802e41d2942d42c8920103030034005000c0000e101c9034140d802c102034101003541b401c0c10000b480103a50745000045d00402081d0310b8540c8144070424420005251162460081d2410280612342c0c0ba42001da0b0031506c12600340e0b0050840c101c8040e194015400101d200101903030001440143d50911030084034071081244100548006070210000c0503114004c80201040c0406105883c5108550f481d110218a000c03484401d4039802004100180807030310021102600b00032105004900b000003000e103012001500d1072058005400e101424980941b007101e500c00300780710f0007181c0200030b81006030002d4080d01c0342c0340c01a41a41610004a0f10041c107919aaa6058564501c000c090301c00004007a40c44045d01c0b50303c66a80d04145451320017 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 779227940 1250 779226690 779226703
    0x204060e06030f010e13081c15050306071b060204080a0b01120c03020d03050c070b0c0c040213050415082d0a03270b04030b0417031504020a2a3f030e 66
    0x4264019504108d41c403240b00b08980812042100e00d01076a04140125600420b049810a419242074400403003403285101d00707052030b880018000c503c001030003c0c02c2e6501051808099000c4c1c2c10802907607a80d00f00b0000d55420907103004101a482d01001d00c01440c005541c000428080d1910500f02a48051070314600842c83c0c02160407030101140d12140008208141200004207a4055052240c4a00411038070316903409800d100300d07181c0b100030910500c02c4269000408044013200c0800d41c1c40340092600707402c81c140d070041c0d481e00e0402c1c100c003900c2c3c005004002290705a0325416510408005a04500102c4640c03001084031524002119000340000e403000e540107225001150030107107408140c1c11161036642100388030a004004001d08600c08000710001c060b9405030b40d86422102c100d030291560000c03070381e411451400018042011100341c0100d80d00c654112010f82c90703402c030381440e030207d4180c10312044070400c41512054117540111200741d9002e818007049180308071140500300764 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 779229190 1250 779227940 779227957
    0x3050f0715030e0601090906020702030a03030b13051314070b04060201060816120f0203100e010902130515011b0203010c1e05070f032708010204060e06030f010e1308 73
    0xa0240c0000c0c490500c207904403203041c5a50341000c02c04200f014828549800d8144110b01c4003c1e95551008103016040e0104e405040c1c0c0201500c0344c900803441c0160040844049003070042c0283c545c2c5502552403445a00d02605080045107218001c40d529040014000c040200741c83c0140e500001d03c18002e640a000900750035000410000d0078036419a10740414041e8240768925024000c000460b05000200241d540010940074175a40724004a8680720300c1035581200e0340d18000c0d110400301c0d810340c00042803e1089820ba0f440d40810355580c4282e40f000d07240310369540780c640d10b441840e6004180d0000400ba080d40d0151410700190002421503007103990000200d816056140c003030003004000080d140d88941006070400e07000e9243c41e100700450803401420310013a5036242c00120b00208403054860f00d000102211940c84a922a002c2d41082c0714030404150f00d03603402207461800000380c030f20400072416032081d160b19086640001d5400504524041501c65032480080b0340740400815005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 779230440 1250 779229190 779229193
    0x10302040b1f05180d0308010e1b1b010507230a03060b16230601030809030c030d120f06030f060b150c070e09011a0411090402040f03021f050304060903030603050f 72
    0x100f210f0320302c1400361000e0541d094410440b800c104000070b40c000d0b5010341909e03ea018608202c3c4d41340a1194252204e001e0350740040070020a27800e6440900700d081458110002000b4000c50301e03081419190040d11292000d80320a035510b2140c2408500000341038042454500814450382e10588600154494005c00b01c894001d041c991040c84600180c010300b00e4004400130300030703c0d480c4c0451a00e46078103005c000c0c00e040000403a00c90b284d50401120742e4000e0024241e50405600e20400b030030089040014403141d03030030309180882011b1203104020440303800201c96007240e056680c07508010031200c514150301c1920300c403075a5440b516000141c108140208002d001550a0450818070000020055080d88e03050904242080554114080b1200010303503003c6001c0d0362000321700150f40540781d01c882e00300d4070100f00003d000250110300c0040301c0c02600d8544421500482c0c2440ea0a840d030003800c0810420000304001604550000e07014a009240009441c4d8a035590070341444e0f090a5025602d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 779231690 1250 779230440 779230447
    0x630010305190314090a1d0103150204060c060c140c07051e130b03070506070510050601050a0f0819062705130f020a0b12070f0503010e010302040b1f05 67
    0x81080030440020100c00395042c00001070602e941c000c1030040003e0000c3d400f4407020410303140d180c80f00e41001c006490352142840c801802498885402c640c01d00c0305403120110743e85000641c141c20300c00c41e41551100e0703a07001c95514060310745801034003600101030f0400075103101c85060801c203400903141c203d4403000603000a0b40f07480c0c00c0058028030400010003a0a12070200300540c1d48603140d0000c0140d04c038502003100182e0000003420290076620003500803800054403c100b01011402451002d8501000c100383c0d00d0b034800456a6010701040e80c0041000d66005076000c9004804403a4060f8484c09001d59403a10010800b042e1801e0b036120400100000100f8604807030f40e4200b0003a02c8044075820003980c42c002c45402d80000d85054040c00d143d88840b050300654031181c02c0c2d10040c04142043d04d58400f020101500c4210040310380000040880080d0702e1514851802c0302d040750003c5100c030a2503403c5808010007800707a0600a80c0c8a08141c0c1c0400b01170001c1864403040c2e418039102c4a44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 779232940 1250 779231690 779231693
    0x1a0a081e01080f12030709030b070c050d030c0813050307080c010b03030d020403030e01031b030e030d020433020c0105030a1811010e1f0c02210610090507020a0206300103 75
    0x90f101e04a101c8900104c801d10070050307256840050300c41200e0700459403c02d681c9584405690202e958200035049004441c00030b0340c500c1e01a000f101001850341e6640381e00780e070b614000c0c240e902c1d01c0b600000c19540040101c4030105080802a03c034078103100b000000c00303480a500203131943c0d1000700c40c000c0c00783c0c0105081050540005082080203405e081c00c0c41803000702c0d840000c440b41d08990344d00900d42c0c0c07004880e030240c10070002c1e0707410140007007c00c664840c2c960819503400c9000c0c0c80000c0091a902ca46001103803250304507121003668540007001140035010054035031303800050040800740d9903404c004940c0503901800c441c84a0260100e20300349915140011f0078516100c4039140039003161007020381e01144516042d20500803d00e08a03141e0484c0c1d20002e8229424050005046599894091200a0301080440c000c1151903046003000760b55483d0310b8181c3d40c0490314100540c024610704400350030681c0040800044100ca00890300c03409940406140c80584100e00d4115940c000500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 779234190 1250 779232940 779232943
    0x280305070905010219060f0b091510110d0f0c02040c0e010305060406180207030512010b0d05220219090c0503040c0e0103020a090e0109060905030a03061a0a081e01080f 74
    0x4020b0402031000d403020741e61300740d02036080c000034000090280e035862005072141c0c40d031540110540c41e00184420041d06004180b022421000b085c00c41c840c110311220000f506010742d441003c010b40d82405002280d200d035000f039400030b5181c0d540805120b0740d50380c8440103036a10f01c108480d01041e0b484101e0307050030f83c0700014112034005000704e000384e180203018825000d910300321504025803850b0250b5901d0240c901121a402401c0481d280e5401d003900109400701844090000066a41800c0109540b0f0002495040818440c0308080b85128400c01c005810b2120140e0401e21062109203000c56071150b0410441e14141c0b56000003c1022090100b00400e0005410040c0f5080200240d00d505680015080c50200e2040d081d0165440340548ca40050a410020060741c004008200d56405420900d40700c0d80803e40050000f031400350085040c240d6032003040b502a021003251030030311808000032381d070107103010b845003601a1034291000d40c0f00040001c024003070641c640c00382020349a02880349 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 779235440 1250 779234190 779234207
    0x3070b0603030a02100e1c0c030e04050c09040207060b0a1d10060525050102070c260706030209030118030e2106060f0d051506030d03050609040828030507 68
    0x61194008000c3e8075002d80c0d0005204515010140000070420003209140f40b0b0900340712110070401c0c1600002000450704564115071071070081c2c036200d60403261300d020042151340841d0008080003051280122a061590243c9015841801c000609a00d1500002da80920035803280c400180120002400c500e0f0303800705250055002600c0000213400e00da40500940a18603840100d08441c4203104100c0d0740308070400b5401c1390440001c569664107820903441d1181c0134042c8c001c0c4c0e0200722910010178083e1403a1612040b8803080a01901b50620400301d0296009402c40e80c0d140d9210300b5080241403102d000c002c07180e031080c0c032141c07501842c0e441130007900880074004800d1a1040c4000342c00001011441a90101e021582462521035000009071088610b02c005051807090140c10548403145407081801810214215000140040c0085040e540102e60305038200320170b00c022800041894020703091420000c2d10032400c90110706c4c0103820616014104a00090700c420a000c425034015041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 779236690 1250 779235440 779235451
    0x50a0b0a06140405090606040e190b030c1332070806030312072607080405161d09010b1002061501080f070807121a0f040c0804112103070b 61
    0xc42e9026591800300046018601c1010300034078812000810644d41d10003250041c1450b44806191401c044080c0b4a0002c44403540d0803200d464500304c0c0032240780c00140000b84410091104194480886020026002c540040c80302d510b141e01503070700d80d44004100341d01d1401c904000e40c0701d94030f06000010103200d00548414040d800800c6420441206664056484842401c00d5004001049041420300e0382c00100203c60240a406011a1030380c481d403000d000b2802101107500040c05410708800c1c0b50310b1482010b5400c403240014001c600d00d030094482d03100d14900000505c159101010038540c011b0f280c6140010303000380c1d04000c10141c0c0780040b211100002e184c04820780c40c10b99280607034101e0207001c64051000840000c0c13419446034141c2562112074a4040c8820450304c00303030484001082c3c5c1014400d003441e22004078141021322485414420b541e84007005901c4946400803100350341c0242e150400c0c0c50301c02662904074814030700c1c00f00780c1d040402142c0d62102400c07d2402041c02420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 779237940 1250 779236690 779236697
    0x46050d300e15040f03051c020304030206090c060f09040b0a1e031709010504050402030a090501110d1d120c03070203070b04051c0201021b010c0c080d02100203070f0804020112050a0b0a06 82
    0xe22010134024202031050795454180160345003030a880c001400311908005243d0b00c1d00002c100300270540d0214119001d09400e0048480c111a4041003080b00c1c013400700003181c020010b01184105240c150400b0401c41c00203084107907000e844d685146012441071800e89080c40f000d100c10400c00034618020103c009200d4508e508203195800000d0041c880c03031090030b10458000c80850741003203066001c1e0a1095004008001c103003080c800c49141070708107182400390a8500600d11031001c01091001d05541c07a5100a0441c1d2440c0c010409800d401131400d201c00c62200384507280c0140c81c1001450b01804042c2c41c450f031114505402c210b0303110f10100f50b2000000d50b040c104401030340c00041441c10403201080007140c074400d200040301c5c0080140c3e0090a04a000000050103100c049910501c81000e9400c0d55182d600300308a10b000e0f4070080d650440017458a0f180c88407200e01c80d103507454100e031051404081d03000c4054004425240c0649034800f0301583e070049444035142030380c2014000c015030b04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 779239190 1250 779237940 779237983
    0x605040b011811040e070509121c05161e06050f150102010c02060105010813020d0b060f1e090c12090c010e0406210546050d300e 57
    0x43c2c8100440c05284500a0000c0c039000c04180e005000d1400c0c0c070f40001004c1c00415464040542003035481c6552140d5800c442c41104000c0b1440b031280040341c844032824001e494a580b070b9a580d1010900001540ba25071201c0e8942501c001080c42c0100c03801084005060011414001c001e0a01d0314242d400365415a8900f606000e81c4980110f540741c119082402c1c01c90b07440d075a0240d403642d044080d4000079030011003a881c140410804464650103003105441001d1201c0c0c00c08244080c0c00030109104d110044180c42225842c5000345009500c5510718045904141d69000175200412040d02c003400d550b009149101c80a50b403014818800c420115000d20a02c0d26080e05005544e4444032800c4880b0301104e4070806022040005102890000a2041d10740454200141660f80d1122a030300d00720301084540703240402522070006140744c02c01d010b44907c2140b100291003091103d035001d18001c0b07292038002c0a2032166a030b850420000e84401003200801400500c2c02e003004202104414010324 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 779240440 1250 779239190 779239211
    0x21010617070c0204110c06041a010308030a090501021b030702120606130f02190c0b070e0f09060a030209010b0a0e040204080c06030c0d05040807060c1d0f0d0605040b0118 75
    0x4a441540103001e609009000044074008a4050030240261092030b4030005000781000b01c0c0000c21920842c0614860b030044010307041105007001c028400504076020610210304880c0d800d901ca011001e218400040c900417001c400c2d00800389442d2200482e90304045141c500f54249200d844d20a0086036010b400386d80740c5203002401e10001034941401c0c00d40d803046c040700e0002d81641242e000c020213120f0503910490703442c1d004250b106201003c41d20004c007070000c1845140150454520400700812045081481105101c142c1070014901c55010300512800009070302c55096040c042d01c0120351603580c40d482d4413805051200001c41a5000d1441000300b00003003c0c000c01c0410300b8001c1114400c1c1c4e079840714070744101a03004992036100c00e24500744c148020401d04000505c010b610850081c49250071040c000d640d240c00d01c1c1490403c04810b01c4c080c610030b184c825070b1b24554000040041400090685421040700c0049400316202041030340180540385a00b480500b504541580038080314a00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 779241690 1250 779240440 779240477
    0x90603071404110d0615020a0803070c0f0f0501270503031f0e010801020d0608210d09050f060901180807030e01031d0109150603050a11040e03210106 66
    0xc81c4980040d04441d000021056641c0390070a00000c1100348806856008090582005240501c02c0c0c11b030030412040c3c0142c2090011403040003c070f4010680e54190394441c0710640e000c00803c042251100c8810b4482c07400902d1401007100720b50700032000000c4030000055803804410032505002541061038080c0780c005900041100e5100a03d000701460642d6a8805030559140c21b4000341003d5076440c0011030000015409084141d0001c07806001455a03254060344902203100400c0301141451000b001502c001b40040c0b100b1201d400b80020a40c480740c5800741000840304001e002e03070300000103111040400340070342c80801003911742e104005001580c07203590310300c03a041c4000c0c00c1c41b154910250315a8080c0d03102c80494540300c141ca09032902e40c04001e80c000d2a51803c100d5041c100002d1840350105c41d44100c0003501e6210004101070300c0c4946503014115002c0e0b080d580d000781c90302624000100180f028011054280e0384076030201e00007450040213444142c02c80d604002a070200c03920071444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 779242940 1250 779241690 779241703
    0xa020f2a03070b1504092102070f0b0d0902031f060f050108090a06051f080a05010e07060c02060304110406240f1d1203030709050f190e0c07060606050304020906090603 74
    0xe0810000d40c02a0303042005ca8054109040301901c0d4001950103410195140761400c000c1c0d014a5003036980f03e50701c0c1c0c14180500f84490003032140d003200900c05502d4030400c81d4031241000e030008003143c42ca10134000242031280e901d510004025919000f04109054022500801500302403c00008900d84010159500e0098a001a00858849022413806003200d1158003080c5c4030031503405d042c1c0d80c458040ea540d50b80f40d4031040f106584ac000519850800c0070038a9010b4924a42c4c86da031441d41907408100780c0b600042e00c2581c0130078810b84980090782d2144509402000804491840c03003c01c07503880842030204d885801d0a00c002194040d050b02e5020240d1401c00c402c0d00a00c0440e1031000d0081202080c85a001004600c000000d00510075080314405084a00c110b8070440700010344014005100c0c00a04408803154000c00c041c040000d51074401940304c07516407111070500d202c6031107e03070540e50160b01250206100105100c10360500c4030f110340d8019403e0f111406582010000702e0b69629 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 779244190 1250 779242940 779242951
    0x40608280c0305070b0712020105010f1a0904020307112107060c03020d0f02040f08074a010509010e1501030e010908040e070f090605120a020f2a03070b 67
    0xc461204002003103480d5880038065600542111400341d101c001901e940d40c0202c43c1500c4a400540b6070522907481401820f041c0e440014101005900e004c61100e800344440407181d028807800d1003000381c2030311144040e40c0300b40480e5460084012491108a0806101440a440b54000350081c00031158540003114410f0364032410024600600400481c003e0203506034107200d19017030181d100b04000003a00504180c072000382e165800290b07610030841c0d490400c0d00c5180ae0381d072040d202440e2001d01951324156402490420300316542c5412028940dc3d51200c01c50040c0c0482040c01441141829034149015008510b80c000d06030500c042da1004200149805904041e05c8000c80c002d03a207820341040306c400d0b52017004203480da900e0f03000305d0103030070000c80d0b440000964203152418010312407000907007151015100c040c5000060030b8a101400c03001071a00c002c0319000c0144444803042c8100030648541020707144000b008540140c00244c586070080000c40d980180800c0006c200d2940c2100c0d00032 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 779245440 1250 779244190 779244253
    0xe0115020616030905100e1c080604090204150801020a12020928050a03050321070804171c05070f0e030d030203100b04060908060709060f26090c040608 67
    0x142d884400c110068401c410b0000c04602601c2c0c1c50690041864100b1a4844d0100f0113841004040c220040141c1040c00c05000015049c0d10201300e450400c2c0d40489505400904040741d00401000410711041e15540a941140e60001d940d604c0140e11180ea0304412203e0300080d49004112000619000c842206051401015010218240301d6104822008040180c04203040c507649042464903900400c1410381c200400f1000d450700d4a1000a5252092080361141a00c584540e00e800005250030911104080c0d0108803115180349071030030070030041d510298046000d02d0136210046c542079660500c54240321181c40c0c2c0410315600801c0b4619100b01d40d18005880360303500010a070f1300c1030507079002f92540c050010b000308410b607211402d03d0540303003134008564090700c03070240131100d10001f4030840f0000f99903015880300952140101c582090401000c8c4222301d80c1114a8540e401c0d0309448605d0540d1207280d102030303a42064000c540050a00350040c01c003103d1001c5c0c02e1a1040244110070800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 779246690 1250 779245440 779245471
    0x6050a030509150703140f040b01121703040b1f180e010207060c050405032a0d021329060f040b0c0a0b09030a030e011503080a1214010e01150206 64
    0x1080d00801146081c078400e82c040f1200341c2086039000d001001a0004141000810000100940012051907004507406402c1c4440b0340c2c6481d55408017602e8542c411501030a44021503040100740201131801035008284001d16414843c0c03820105028010340c20b00c08004d244020040e02401c0c44001040c1c00604402082441c00c4403030300e074024852108018681c905d0f00760002c49240c3e000006c0c10540314160222054100d0103a000e0303107004018500c40010703092417140d10180c0d00b400403030700300a1071019202d180c000744c0d240c0d114000c0e01d000d120000309501e86000308805000311100301501d5170303800343c50180c0313020849540703002070784290b01605911010000303000080b850300300a040034154004842d00c0d04c2c0c1c10b20002c0a45c41c2d178000c62a9100003400c0c80c60101c2520011b1040418000800403c851120301d0b55540d40b40a420030420130060290b100c4012410700c0c07440c002d181e4844a00343c40d010096042400c92034040c04180c00090207210340084410700282c0010300340b600403000f01c4030000c2c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 779247940 1250 779246690 779246701
    0x90c11100b01034104050a02010509060d18030305010515030f13050607030204081b0f01080c040503010f0902190f1701060b1b120c0309130b060a0507050106080706050a0305 76
    0x24201c2e445842c0016082442001ca80d0341c130b19510540e5000002141340480c400900d2100302c00300c41650b01414981204944c80c0040d8003038001001c001c81d025001030300341418a03003080103c42c6011411001003151000c4602015450b106250142004842d40310708411f00188056240c04018412000d83e0003000c0071900c21440090035030307142d85d4071400301c604901d0032100080c0607400510620a603032281464400a600402d842003140f420080d0101400c4507580d401158400d4000e40190b0b9240000c12011810361804c1c0246626121001c2000c1410000f9205220b000950035441450152040605014003e6000408030889858840641c4105041e0b07550a00605460b40015000710f80020f407a000c41c54010845450f04500c070064900703180900d5200c0ca01c80c400c000700c00509420070481c1440615008415040008003040f000602c090b0100201306158404502a030200782d01103240c0e0f0812009000301e001412040001d003020502d0804060000d00541042070189500c0360006230 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 779249190 1250 779247940 779247947
    0x60306260a061506080115080a0b0a0305190c14180919030806012d0518040f02070b160804020904021305100614120601050705070b0310090c11100b01 66
    0xc1071540c200c0010095140d141c0c00b0505a50503038402c0b2408201c00d24000500401004900080764245d6110203403a44e8454881c0d5005051503440319a2000150102001159040050030100284224055034030605070070700800c0090b580d40402e207802448800000c03d0303180d1000024101d6210801821141c60314a00c0c0d030304000c00c000b02c0004941800c200441416888426280a40000c2c3c0b0741c0804990418800101c4440031142c4401c0240b04d010039503429403255005000c05840d550b504407000b111600001c2c1524080e1700410b2900390081640c2d828070807158240e03900000c0503054003000e59102440a8298240100040c1c07182001d10f00040540d01c0300c034206258036441140811040c98090f2402c0261540342c080c0703a0008502c4a42e50483c44004421103020307c03844650003c0079503540300111451b41c0300401c00c176050f0103807917800142d0881c090040d600071003008120340801400d2000348002c0f5040c4104000070041c1c000540d00c818140492402210288504085405041c010041c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 779250440 1250 779249190 779249203
    0x18020307170a0b042603060a051513090b01020c011d04050402060919080610030c030f031107060c2603071103090a0e1503010b060307080415050103060c020706030626 73
    0x1a240d00084410401000100e4400500c05150f00700042090b40c01d9008802281c00121001900300c88900323400d0040740f428003050f00d102c0036031026151400800070903401c100f00341d6a1112220320f8861844034071944c1c0502c150890140c00303180c12026003200038003850845036050f220900a030b5032203001c40c00b552660000c42d94119000b92005004040c240451004595a407054003024056940454200c5d024000c2c09000c50f500000c1d0342060504580310001d01c40380b007190840920003402201c411140c800e0161100500303541d00c03040c0b520b06450901210100c0d00e90304402644800c207e143c3c0d600301101d01665042801880c006803818104001e181c43c504c208004940d110541110001e40c0d0203400f50322500c1240d420f40d00c0a200c14240051500741d59440c00d65a0b4011024000500000c0c0b045405903030240c015081c1d20894840200350a044803801e801c01d40d940780d02c510800780c003260100030400003061103103410010f4503c0d005010f503010660740b10a00107041c03400c440c080c541d1000c0014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 779251690 1250 779250440 779250443
    0x230f10050a03020a02032502131a0f03032101150302030c040b0c010908131403030415081003120903030305100524271e0108041518060c0318020307170a 67
    0x12000d10100c599200e01d400300c000f94201e2180e06127621001135142a4040c2400105d58030b41c408040c01c030f0b00400c001342e80c041c14040503054401032050f0749194020f100c030903c0349030300c3c3d8200c0b01d402c0d4140302d815496010301c04100e60926004101740403030000036504580840d42070054003529640c50900450242060410140c8000d40104404001c0000b9a4943d012180c40c00603203000c0b54200000d1584900070b5100b00c03070000f0030403c0740b022294001c075000395110b0004800903100c01d440341d8544000e24500140840050303494507090042581520601c0d0300300c101007004840d02c03031a2200113603003248448001644400412002405040041c06542035040740414680b0000808131060301200840c50049100381100080705c1540c8121440d5804810300695a0381d206a942d41c90342c52001e141c03109400d18441d90b40d0460001d02103028241031300e582c442d0324080382209403034034020192010304400015105240030700c140140d81c0041d00d242101c0f15400450b08a10003003d085050916410b030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 779252940 1250 779251690 779251717
    0xe040f0b0411040b0102010b060d0506060714011a03010b0f1507060f02070c1706012603031e07020106060203040e180604030201140a27020a230f10050a03020a0203 72
    0x90100300142001c1c65102c0d400e060341d042040c42c2d00100124261481110001d82090003080744240c001d0498020580c400340140c20140750880942d0740320500000c01440c1c401c03907503580c001800d45820030040c214500300304034001d0104141d1500010040752400d075601d48612013900a810a4880f44001c3e980003e0700300c0c0c3c04022024400c080f400196211b504115902005500081103180420131003200101008006203010303070a008545425082000103521001c4000c41508004601000218400c1d15513a10000118455040403c2c1c0514081d0081080d64100306d02480540d46c008280da080b6900c444001d03429440b00c440618202c0c0d10700049001d03d0140f41d0400c014580c05400c0250740d000c800d0740d0700c0d415a940d1030320311007103a01c03c40c0403005400d580301c0300b5016400004d0700080240e00090080445070303036800f01043c0354600300003422003280e01600a80518a09501c29514509068920815510f007004d4000c02a04c103114255091603070108400b6680d900c2003081d207415401c1c064 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 779254190 1250 779252940 779252963
    0x105040506400e0a020a2a06180201170112032007030f0b010806060f040207150c110f1c05070f290a0608100e10090b091002090a0e040f 60
    0x94000c58158080d483c405004503000c2003030040280701329401017020350398401e80500d421000a64588105010b1841c604d001c0c210400420568482d00b03081d0545007000302490036280c40098550a0803c0301208110010f80040101c04030403d03448601b04c2e071500d0b00f0000c14840b5864810814100e0103604000c0c4100342d0b011080180440c0d8035a0061f0140300170700070f00d0303a0718800c440d0356000464a41d0b07044000340c02030701d0880c1015000b9081d240cbc41200400c10180300081d078241260074841e400e20000e20b04c1c901d0301e40c46200c14444240d000e16000d0290541d501d800c0d201902785c1c030310103180070100403000912106100d03041c1e401055403684096450307400f07080e1a040c20018051f030800305c00e4943c0d0320000315219001c9846004125011131001c2c081c6c1ca590310003030304003e2141c0031046965004100020458103090301c0f400410b544502d140307494504248145500c0c080d14001c0b01240648104032001c0190754019140084910003c004240f50752903140180c414140614003c01d00e86000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 779255440 1250 779254190 779254297
    0xc020f0613142e1a150c060f06010e01031803050306030721140c2805060415090e070504030b19020c2107021f110f0705040b0105040506 60
    0x200c8528035404901c02c40c00c0800807a0394403010850b030703403282440c139080110920700c0030074180403d20803600711556512034280032484500d1403c0c018111000c8000103a03140c1041503030b60300181c40814905003840e081001c03601030002d8810360700c0d072650041c06106002c070000e5500e036410416807002c2c08948080c0c2c51f0304030f4500111682200300c0c080807a40714a08040410342580001818410000c005200d030121240c40c029500b0601400030f51b00002080411000c0791544810b80200000d100d8110300302c0d8203094030070008100d05150781142c40e40c241000c041c8500c042c2d100c000d49081d2500a204008140c40d07400907203002d001e4080e888088907002281000816201083c48851640200034003403403c3c5070308000102d1881400d100a6015881000624440d181c0483c102410744042c00c1212003042c0d0790055914109040d4040040e03a07004540602c0142800d004c1c00002050070709000d420141000d0009610707000d0400100010b03400c401d00d24002440ca1208a0103841c3d00201c018800c5049 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 779256690 1250 779255440 779255473
    0x4170f09092e05210c0904020402160c030b0702030901050304030f0203070b040f020906011e030e070506030907080d05190e03070306020f120906040f0308090c06030109020c010c020f061314 83
    0x101c2c0303d0345100d14030408103590401a030011001400c071410020307203224030007901041070303075040944103030380066003404155080da4040d650711180d10301900c1c1d9100014554500300740c05000060203003003150414080801282d0700a800c4e66001645030a08003540d0401030001c0b490344c00b41d05005004141e032503003444140002e000194101c2130094448070803d03034404c401035a03a203101c0001c004400e0900755080301c0c4c0340d1203584007045004950003510152070ba2440000c2c40f58009480031f800603049000308120340002041080c55030202c60402c50f0800040e00c0d5005140240c225400c0240040d400d43ca620310354080c80502c0285510100854413081c1c104a0034103075030000e03c80301d158070001d10045102c4903030001c1ca45101d958000c000140c4401030b6941214610400303480030310541700f1825036003425607601001c0d42c0a044d801c7c0700181c07120203441e103135420348218001181c295001544d0401c0c82020200b9019440b402030507100e10818104d2030400c65092008140b50b100c0d00440380718003001c1c0c10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 779257940 1250 779256690 779256781
    0x2090f100c150c0f0305270c0310050f1e0402060703110d12060b1608070206280305130c06050901020c061804060f141c0f0302010504170f0909 63
    0x215aa03851080741110200340c0450b542550b5164180e00300c80107a4581d0340703604441c1500000058280c0702307800d03148404246040c0940c01e140300c62503118010001c040e0040034500b07500c00c0342000c00355000e00d804504040140c50240001e40111030004580040c50b001d9290401c04610640481e201e00100b40b40080000c0e01071200f41e00304900341b4100240c912014801e031072505c0c0b070010318440c106007103a4a450043d44481001c90300100103009129100c04a190b2005904000107003910014040050080c21100020562420f200304814210f020545403480141900d4050900d25614068400182e1070402c645004a52100d00040c18111605a1220040200c03600382c8041c00041c0e2192401000800d080c040c13800600070680742000c2914102c0e4212102a59100a4070210000380d00c0d0307000002c121242c2600941c0d118414042005401c6800c194050b45c002c550324244103001f403052038648580d201300d0703101d042c0090200303104103481701e65029081117004a82c41101e4810b01d1400b4000b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 779259190 1250 779257940 779257961
    0xd050606040c020c130f0e06040606082a041a191a090d080a03090602033907020103110c060106020d030e07030f0213060306021b010b0402090f100c15 66
    0xe00708242d801015000055240c0110002014801c60a815011000c003c202c8065a0031580380c45071810007400c1824841c0c6801a03005020200e0541c1c1031030b01c0d0521740141510b000004250f0328440b07a0740294014002141001c0480d0b0100e003034640341c40900241709a8901c1f8a40c08040031405080c82c106548104003203980c3ea03100621640c00c480000c03690b40c09082c0940d0380001107000711800250684000701010407031400c1c0064640416220f80781242c10407607002c4506400f001321002010200d58105464052424503002000010000030310b0754090800b00a042c103465110000c07040c00e0a400b9a8015071030340003100d01d5583d4520700290703124010800d03040400e29008264a003000041294810340340c103c0b011032034035403d0b9400e2240c00d400119030418040e07502d50011000480c01c1c001000010100101c91001c009129009800c5a14685041e44254030412640e4040e860f0340f90300d004181c00480703000e04121501c03001030b170f40c1e4003c13040f008018001c0918071041c000e072283d2000c00c502 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 779260440 1250 779259190 779259199
    0x2010213120b16020f0613060e0a0c0504200f0702270705030703150b04050102070501031b05030606070b010906030b0105011d0609010e0303040f1e0f0e150d050606 72
    0x55968240d0119003424460050720320308401000031102c2d400c3c111040140d030030902c111080d14a1000c0250304082040d1060501c10b20206205000d00805008159007040d140003c1c0142119079500c880c00c50100b8443e050003507445582865801031081540236a150030b03181c080b40c4d9810a46070300141607121140481c8550803083c40c03c1840526442c01c43c2d0455000000b05069846510054031680c0000702590304164454850881590002c0581d000810b00e8009458985003070000181c24000281c010a0415141400079110500d840f00081d0118480d424015500d45440c4041281c6100d1650f0160081c400c0800010308582c295001e03008480c014401c404440c0d881303a0044034800034060031244000d2079940c00c4506450000010b040711081410035000300c0d03400c20007080c03c41e08258400349102e0258482000340c411500500c10a8105160042e0440fa062070480d1036407074001d00030f200074aa1100005002c0350058844850b2800c40104046045075640c074040750348410884445014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 779261690 1250 779260440 779260477
    0x1104090f02030a050c190e040e0f010e0c04020c10200301030506010302011416030f0e031b19051c2301020307034b150f08030307050304020d1103030a020102 69
    0x1740082407007a1581d11740342640c00e4000886c01d88040f61040361041c0301c0c41d0300595445038102d02c600c0c104403003132140246400215030f00005141700d40c2400340c00c0800d2030080340100400401c590005c207500c0f4901318002c800080442140c0365400100d40405000b00c510300000001200313214000464504a070f100742c0e98449081d074809500710043c0582061584528885058400084e0250f00750300d0060110345071078131050540000207032900c020003520301c0f84903400c1d0952001c1c03824425041e99495202580649003980380101050300b070244d000303206d420902c684814404024400314402e8280e001724034504201e807a03152865000350301c1500c291001c00d25001d10145115043d910048500b2140d008010074202e00d100c09840810100280d16070a1081c482d610210f802d0364410104050034480301d0303c61840c1450000c14002415820019540c1c1c414030401ca1207a034170004490b8085e6050742d0006a003a100e141105500071110102e903454040030071001384207076056016111441070180329010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 779262940 1250 779261690 779261701
    0xd090906080712110f0907120e07050a0b0a09030615150e03061314060115020601060201060e4c0f150c020d0501052508191104090f02030a05 62
    0x142c841652003641041c0c151580910b010030041a942520800041d1144480b540e00c1d00000f030720300c00c1c101c2c0c4c020f01042c400f505410380c060042c421081c0e865544001800352604040010381003048520a04202000015240d60103620a4001c00c0c01543d02140a10004142c01800d86e09110b840c003d0820319a20741c4d42c0302c103605100d2501c0c41c20110307002c1c0c090921138480d034505e84004044811b09580d208610050030b5003121041185600030841000180880c1c00781580003030402c04103900c034500310380c10000184008040a290a84c02941c280d042441c07100c0c100c00305001c006520209141c1f0603041d941d00407041d07101413440d845d0f4040c072509840801600d80c51320200f00c00d485d0007009214210000c2c0e07160114042c04d4034800a0b1300003021404070034042d80e920390941d00c2c00c603074201050b0207130b200300303041c00491b40d16400308803c007410070f0031041ca804c1c5290745920212541c0b4040407916039409800c04015507048a001e811a1803080c041840c84800c1000a503105684c003030b04403407501e8002503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 779264190 1250 779262940 779262943
    0x7060c0e0628140c0a02090708090c011b120306080d14030f04170d1b050c0c0f010909020f19020606030a0b09071203110105180c0d0c080d09090608 65
    0x192120304802e2140c0c034114640b032540000d404210003180c01d0004100091214110100c0501503801c030540040c001a1414410700c81d41c441c016100405025601c030900c54411404521503034035080a2034221540e01d030a6284006040d0b28101c081c0003c0c004242c050403280c0e042d08218180d0300b15034103c2d05001c201250417580d1804c088500c094452007400850842c02c0183c50702d40d001801015032010302e44000d0000076555000e085241d02c256a22041700421009803031000c120103c1a0030510b0801c1c500c600c68075142c030900c5980d00e114942100f90355001c2d030f0044410700013505003007404640703c20100c0c030407100300c0d40900d40051041e400c80360342d860341900c00940c0030b205550103000f810321000181d5500156040c0a0304200d030b07a00820101042003030980c0d42c81d00c20341e4020758403001401c5444210701c2c01c691014154100c203901415460a0104000a04010103101542c0ba018145042d040c111030a14031908140e0581c01070410a1203090390000c104016030f101c803001085010795034801039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 779265440 1250 779264190 779264197
    0x7080903130608060406080d0909150e0604050601020f100c090b0a021e07050d12172202040f11040e09030903071206020d1d0c0105030415091707060c0e06 68
    0x100e0034592900703003400014400c5800a4000e50081e01c04906a40c8601c41c01e0f040011010480c0700040050000700704107400c900844030120040040b141009061140303a03142c0000c0140b0540c06240c444011a0199208220b070021345080c01c000c3ea80c0c01c0c16030400e841d010b4104600d000700003503d0301c4030110360101e0000c1141c003081440c0c2c000301100c0d51010744021a042c2d418403080702c00e01680d000040c0c1902c0d5409402e1200e446240541c0640035001c8d000740c400d2125502c0c940c0039401ea801000345c00069110203060340300c913141414040d20114030010700a000c44000b280f03044d40c00c01c407940030a841c000000e8019120035603840c00c1a40c0c0c8802e0b0060350b03406071241140d40f43d8410b0504002c2c0003044414640201e01405e800352600312480000c0d01560304804e0f00c07094002c0d42c050160000d4005110300a2a21401d00c0d202c1e01c0c50516854442070865490a482c03803466689900101708900980c1c24035114040042032a1690803505003000100901c0c1100d43c08034058028149a900e0a039045 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 779266690 1250 779265440 779265457
    0x6030705011128060c090f120506070e040f0e06040b060306100509040c080102181f2a0c1d010f05010210110c070f03020a0f06410307080903 62
    0x400303540300440221002d05101c041000390f4840c01265880100e184d9018800f13000d0550b8580c240d18034035040e41e40580c454a45d20000d0075143d111000000540045881900260359103080c2c1e109000c150002801410501d0300c0141c1c007464400110901140401d2052086010b00c243c91425a210700a241d00c8071801ca90a022515038148148618900201c2e16600940541c1c0610304a6840321801804c80e44070066081400c881c00600300c1c0249040902e180044c0e6100803840e54401c0d1942d0054111503444c82d070399942d60b02c40b60b00c206e00c405d03021407081016508527000c03070801903440d0294541c40c400360344c0c641c54802c100301c000300e865800352105400310b820607801400c08201c840e4030380004040c164060240d0180c2006000300c406020051030f0050800d1002c0703600d0182c51481080070180392544241465400d880f0304020007a00201040c3c00c41640007203180f603000710b10803039002c1882c000044a0360340150092890340212600c01461103400c154507131a5a9464409080d0b41c2e03401400f09 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 779267940 1250 779266690 779266693
    0x3060901030605130210030e070f060509060c010b0402070b01060905060a050405100c021005040503211b010b130905010f0603080a111f0c0207121a040206130b03060307050111 77
    0x100002032490344210703440384c80c180d0b825001900560000b4103411a150f1018000794030b54036403101940c4244400001445600802c1c0056454500c000d8981c4c0660a402c1388150004126250002c000b90490880e8010040003190380da0341628104202d83d40a0141c00c000888214001c201070600704110b541552160f10f6445c2058541020411989004440c1500f0820750031203110044c0c5810801c1104141079444103501e0364100002d00d4648a0420340c2d410080c0e00c002c001a03242c070042012110b0900355400305035100c1000c81c0d031042c050301c003403c403443e08000111307c03c800b03400f1698080b00c0c01c0c500c100000e01c00c1540c0d00303074407038240c0d20320303010151000000b0080740058502420904820300340d004c042e280e0180e071181c1181c540d81285088100c420f0780320424000b041d541400844041c1100f0002c00030044440d03224120340c4105090400040017119000c0b600f55502c01d42034a0030700c254900300556903074075100c0d030700300f10341003500c82d28064403038108045400c0d800748e0144222404080f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 779269190 1250 779267940 779267959
    0x28081f0b01050d09080909090d0e01092603040338060a0b0306120105041b0501020f0a061a12070f050d151a18150a080a150b060c060109060b0306 64
    0xf81800300a19641a0440f01c0c424100071454032500d8002200c0e200740b41078005480903038102074018220914428604d41000740d11042841060f40c500004603075400f01c41c0f40d03051a8400005820f1561040c0e410151a60f00c0564007000341e4143c402200080d105210380c030500d680b142ea0131414001100362220f607030165080720103014866841c1c0c091540000b004121744841c0c3c101d1003a80d821160103480c26200c41d961450319035107600b401c00c400d80c01043c0070302c01030103035050b0030100d1521390007040001040342e42c40c0c0c401c4810030800b0a207110b4070300340e008200e6161481c1d6504950341c1c8a40b1403041c4c145401c04000002242c0c940340201e006829002804110307041c2c41c403070341040280541c20001c045100c007004035020b80d480f00e00040c081e41c58a07940b900968101a0000e640e06c941c2ca00081c0c1c8161031000e001c0c45201004610305038841d0744200d0302d108402d01c140104005d440da410000b9004900882c000d901c66000103122412107009003070400c0f406440f010001c4840c80101c8010750440c4004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 779270440 1250 779269190 779269207
    0x1312210b0103270c120309030b040c15170906010614220b03180a1e030c080a0302070c051002030405100e0901030c08060a0903020c28081f0b0105 64
    0x54000d40880d0805140000b41c03518050240e0340503036040e8511450740003071801c0071030400c21030941e104003401040a00e1400c1e4101d60341c004100354000d01004011085003000300b400c101112000001901100307801c0f444640d02004020500030511410a045040f1000030905200011440703038107a0700b0560ba04121603800c4540c0000d40c1e4024140403071100c600389071640f2480c0b907181c0410060440306070103c2d07032401e104a070020b000e000442000c19941203280314800060400c81e54007483c0c0401c682c8014004618207066902180680d03018110142c0016080c2c40154140d004002e03403407040c0c403c4210f0301c5d180c4050183c0c82615016140159004000a010b903203000d020900340e006c0c06107000511100400302151801c1c2080e401210880024141071100760010b10200317031702074010315007086604502d4400966464180e400d6500a0444070344004081501c0034180341e031690259440d09078035540d004910303980d05800080180250b0820032407034003100140501c2c19500016502c403410203404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 779271690 1250 779270440 779270507
    0x90501050a0b280b1617040f03031b0c180608160314070b07030e041b080a1505090f091e1513021309020a0b090607080a0212031312 58
    0x1000040c445034000d580d400034903d01110004c12072200340b50345100000200385800200c40d0041d40300c50503e10407e03c400d02c44052a40e010004807034241c41d014114207642c05145c1d900e070000e80c00c082c1c80d411403000d0100700c5414400040510048800e0208105aa144103440d1112401400185e190102030360030000714810008401041c001142591038442e5076880a499640c040c00b41107000c6000380140106501e02881054151152800b40141d030380c42a10004000060080c002802250384ae548012071951650032640546000f401140007030510306e00d000b401c0c40003261050594814082007039400d44003482c0111032000000000c2c03080401e107031384240711101d00400b00211280542c003000050b0ba665082150094100b0500007a000850300600549081c15003100080e1641000040e503c0d4036030001710388050b070700320518a89517035001e8412818041104044c01c0368070004410320803c0c00c800c0801c00c0350140300300c4003007140a1b0403070810340d10070f00d81c0029492203406440c0000c0300c1ea9003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 779272940 1250 779271690 779271739
    0xc0307270f080c090f0411031506010306091404060e0715032004030f1e1211101506030f020904051611061e0403140417010501140d0312020d0609090501050a0b 70
    0x801c7c2a04007104100c1c1022914021000b0960f200c41c03400307034040c0700e51560907100716006020025400e101070310300c08008504e01080507100030903981e56201004480300c810301c81e401c09030240400c0701c03064105196004010b000c50785a501e10700b0000c2000c42840300c0b00b0908036000c81c4c4d408400c08425071110b451381007103251103800010660050b2549030b030015803d050562142001d6403218110000411501c600d481c401c03494041c021071030000101c0d4030017100941142120010310300490547e55542050700a400380c010140c0d002070034201880051404201c5038410410180e481c1c000403101503d8135640c500c4140c402d81c0c14400d141c810821011000c40000340d01a020323041108851f00d4843c60700c82154040d501000c004841d49506c651a4402802100e0041105903080c41581c42041d001038414642e61400605100e000301401c0101c0b6201c0c2c0580e00000d011000400c4110340c0c030100c0310058454968121055441d0200181100c2e925211f040000c800c040c06110310246000001840c640c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 779274190 1250 779272940 779272943
    0x60e120708012a0e01020c102a0b070504030807080304050c031203010503070f0f141203040801140703020717160507080d021e060c0307270f080c090f04 67
    0x3a0003004074400d80240585440030070008108040d04a400109a07840100c0742401000c04c04131180c0010141e0b8006102492080c003102c00d016460b12521041e9000382c905500030300c0300c84529204140d40c0c10b075801880304560091944145d1a5580c201c1214944210300004003074000600850700450f440b9806151f0242c0f2034411220343c0e4107100002031420800502d800c030840c1c000001802541001c0c003910009141e81070303000782094201504002d020301d55010326016412180c6150f42559a00740c0741d03000c04490f01c02525512a1241609030280c88a40011480c81c0c0c01000030680480c824400c64060942005010310320080d119001180c540c001c04d082d41e0140409500040854014040c0c4030082101000803c884646900d010b820000d00c11008420a00c202202e801c1d42c103030100ba0f5a82c021502c4842e29070380e98901d0019a680301c441000202c40e42c1c2e00d04804144500c89010308000d0f03030407418001b654207581e501450f54898001c040140c1141100300030403a0154048546900319 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 779275440 1250 779274190 779274193
    0x50a030e010203040c03060e0a110909071e141017091006080f01111908130804080c04111c15030f080304030e0f100e03070f141504060e12 61
    0xe0108a03455099800a840999442e4604d400c1041007001c14070035030038080e07080d101800120072103807107080d800c0e81030640444c0a1200c0c440020081c440a10940c000303803612141001184140e0300c0c02c0b10154071680100f080300310035624a40081d191180751035440d00c003d41c0d6101c0c0c480d50f07800c003d0449030002030201103a1f4482d040c030304c1102800038007450010741107410042030f0310102c036401c05080d82c444045101c10340c44e00704942c032b00b800802c411110078005142820201512003514020b2020604000070704042c1012030007054820000c0341ea820b941c201100c05010b041002011200c042c81203506480c1c1645132000411010340d0180c0250100c50729070001000c000755641c88215020103018008c51b000701001081108142d0040b007140c88144043e2603246070500d0002c003060040014032000410b10400084499855408114010141104004441c04a56542d02807020010243d00351441603808800235460303c1c90023020784045441d19980d1344031070110541030011080090700c041805 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 779276690 1250 779275440 779275451
    0x801140c0c0f06010611060c0901050909090a0602072f060a0f0c061103160c020904060e031c060602070b12011703040b2224030f15120201030c1b03050a03 68
    0x501c001d1020f1402024551076820310b5030810020f42d401d01070001e0180010447c203000c0b11140d640c0c4007080c3c600603070f07003030340c420900e9212141141c0c0b900d150750344020941800040d05800300401c0e104041c4520b040b61102c03d03c130380f0208602c04421b4043e8484160060b5007484680c015a02c502d030840d86000c0c440c00c200c440200c45841c0c0d54103980f9490030604a0260010034070845105c0e1550007081c0e50f04514201c0b2081555070300240f0030b8000035001504c00c980750b840d00841c3c5075061084440e50000814503000140d48200450017419030b0b0b10503000540540c2e80c000075510900301c201c40c0294100c5e0f083c1d05c01e6a0900340d0a00f540b00c0c00c00962081444140000b0400510500c003d0090006011260402c000d00c1b26400f030924800c0e42003c80c3c03150328000e08900e042d0880d840d5030480b818504021a42210b00c5100720002d21456460114040544500084c4002031200404045000780c1e401d00000085c0e5100790742400300e04a000c1100150740e960100031038483e00c06400d005003a0714000c1003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 779277940 1250 779276690 779276713
    0x1603110111040e37270c0807060507062c2a01270e2a0f0d050a0221091221043009050406141306031e05070801140c0c 52
    0x500400700341d1541100f00307040f4040040c446d144001d0b000074450345004114081c00e01d071000f002030040031030003021540ca600c2c03d41011030901d01c6c86540c0c0c140300050131032866580d902c5980d6480704260b02e00801c4038081d034291800d001044601d4003201046e12210070303200130b40f148118135401d200d858060300804004041000048200014043e40034415902c4c404405d07400c503001c2c00300c2c41031655040f108041092013513011109040d01c900c01d09440d00024103688035040380d00644900f501461120000d00d403d5650040032010640c0140d1652007283c140c64140320244225228100d4520700d02508071504100901c041c12010f07070700c60f00c210560804003404400400080d44c541e043d90040000e0044401c04251740f100e000c000400f4100c501340f0031a898126044010346143d82424050810708922200c14401500101c0066602c003a0f00840d907164443c510108100d026070484031402200800500c0c41c1d814080e801154a10041050464448003403c40669001980b1031805002d800c20000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 779279190 1250 779277940 779277971
    0x7170408030a09081203190c0c080f0a0306120f1202010f0f0c0e031605120c151c0c050405040b12011508010c11031603110111040e37 59
    0x6120b90142c460300340c0340f414508400d0820400900c104182c0304140104500946c05081040c4e80702d20011000891080807241140d504080300c401600d0043d000407100d2a40300308000504100100c0c0d581000441d0311060000d90800070b00c17034090f01e40890140c4e820b000c28a12000c1c10b00302030003800002281d00c0e0000c4168255081c0c00b80031181503513511001149260803030b490b034010036000c5010f0202145500a400845d001e280585030040e0a06070034000b11039800c00810803500340080c1000c4290000d904440c3c1c17154011340349a0980090103542d810700c2d0080307001e0040e248401e611003609003402d040c00c0c00001c0100c1d6041c00c1e800022400020030392140cc0c817402c1c000201180396544014140720840f425a0001c1848204202da181c800f00880207000c010b80d107511301807080c001c100d142141800ca81c0300c04280030054455203402c0d800e6220702408002842141c11403103031404a551615440200c42c2104c1d01180104004007002140101101c0c20003481c580d110704001540808450340344 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 779280440 1250 779279190 779279197
    0x9030a17041703090a0e1e1f030803071407050a0201031112040f1101090305060606090307080d020106061e0e011101180503120a090f170405120a06050108120717040803 74
    0x300c003c1d000080d0710000d03030a110b400322000c3e10082440701c0c95401d01c0d003507500da265122840256640c0038800481c0c50014800c001054031501140142002500d030300781541d10b507209648034000b0444121070584c154601c40705950b101d580240141c80d4094881d001035003c0c1211000340e105440b42000050307203603080480901d0280c1d01500308482400e006160150131140440d43c002e0500800c400d0420008400190030b40d80040c0c240c507006d84500242000c240303000607940100803240207150364241c2c00c581c15842603044a03016030791180001080c4d15905041041c0c08440c400060f015400840c00307500030b8106151000d8070710700024202c4040e581a292400035400b045480b6080040c004000341911400c2e1030300203604c038100700110700300303a50780400702251228010034048580c04050071055190064030020800907104200401110441316240c4219010440e9000e00e082d0011a24040010b10ad600d9100c0c0003022a00d0f000c050b4907030042d6814452502e01010004000105000e2800d1010303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 779281690 1250 779280440 779280479
    0x50108100b1c09080c0c09060d0303020f0909090a1110050924040b0a08090f0304061409030601030b010810060b0a0c02060409090b060922030e19032001030209030a1704 74
    0xb980d171642c04510355642010710320841988600215000d01940e6070701e4114217071590b0341c10300300107948903680030a180882c0140103115900c8220741003045103104002c02c441884a00c1122032030340011002c3d040200c84411b6400700d85c0000c2e014031989590b405c00e0403a214001001881100403246c40311003005080d44982c025861941010400c4203149800402103908460100050103501c10360442d019628015407188034208000c40c1c4002d00d061011004540d202c1101505540707041da181c1c209507a4100b000e104501c030798850103160018061040c401e100650344010f01c034a152007450b400407213243c400350314143d0f80075800308800030780700c411480703a140c680d0b11814030f0041c82d161200411204200c0107008803083c0769000c4401c081030b4250810300446590504003c0c4001c520310001c40c20f00110f840c11005002c10450002c002d0119007400c8c005031110204001d418010004011003d0740200046542c16502001da04d40024a6090f6001d0014899180490409503691003400303103050840d00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 779282940 1250 779281690 779281703
    0x1121060f0603100e0f0d020718180b010f051503060a060e270a0c0504030804030605100924082d1c090e1e0f0601030f09030509030601050108100b1c09 66
    0x38005c0b05242d0500c03032000c04140754005401c80d02d1403c1f1641030700c40c0303440e650015025901c0341341031040c1c58089001e003407040e0044819003e940c2c4401410807504058061507105100da8000b14100092100440744103500c0074003200f4003d840c00400352007030400c10850740d82c80208602c2501e46407284102408010010326825001030030520021412600001d80100400c4802c002c140045002101202e04a0f9440500010301d41c5da640e2440e44032129540000c0c07000b504107038140f129400c0da6011604200c132080e410340309003075481c044a41e07100030a0b440c6100c1c48003030700311041041200700807100d0f80c800c140055510151070328400200d40740c01c2d00c8500c00450601c141c00c1c0040d0344401c2409500005264020b54015480c169545c0049801009105401d000c0c078005942c992280c1c0140d1000c000450b03090010110524018055410170119903009100d10800001d940d031140301d090740541d50700e0300c59880720760821012042c03031360203810070300303154a50b440f188620348040c4d11a041e002405180e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 779284190 1250 779282940 779282953
    0x305010e01050618013c03020703090b0d06030b091605091b2a1609050106050d020a180b1c1b05070c0509180d0c12030c1b1121060f0603100e 62
    0x2c45031662868540d01446c1018814030050001075002100c0c58181d4403081c0d03549884088101505001e403442e500010500e0608600b03202001100145184485140b0700a129800c0e459800f4800d00c03110450300020310003440600d80c800d4225450003483c1900716003c984c07024090010792210680d06049030843c0c154081061440c0080502640c40301420040109102c0c5500d4540c00038000d00030100e0b440c0c017040c2e000130300c0d03240e503402040340c0d62070f0018074440710514564030ba020010541010744036249034049102108000203942c4124540b0159490030b200001d001c01c4000ca031503400c4603c045410440d0107001065070b07501c00002c00c0c400c01c5940c24031420300c1025031999051858114440c424010420310180c00510301c8150b40b1040c0c0d0191070000340c490800b0208842c86501e9540040b5082e244031035123400c7c004c28450118103030ba404d03510000b4a83e50707840c0303082e0100300c40e05d40a0380a0700408082240d00380f981c111144c0000c0700034210780d290242d4044040454030ba4514000390f40c1d0000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 779285440 1250 779284190 779284277
    0x91401060f180213050f061207081b1303060504020d08040308030601030c1107171608030c070e0705070602070807120c020906150d0509030f04150305010e0105061801 73
    0x240060030480140384400d508044001040e404c80070018020203201d0a26007000502548410050b036a210600001e101ca00303084c0118003400d0018291490000031441d04503e12140180a00321601444a543c0086003d4510b480d040014007000d001240c0c4078074035900c0e01e004501c400014001039801070000755502d00341a40054100c0302e803040c04600384916141c0b80800e01e4000b0516404444088910710303401d01d45003114a060458080045480040d00340d408501e4480c00409441c00c104000e08640400c1d403110442d25065104481200000d41e00f081010005101900a041028840c0d03407180d0400300325a4620480002c0d20840c1c0c2d001441180c000d60551514202d6160040d10a0700d5024540e01c5484866000d032180502c0000c0403074031400401c03c039060400440d102d0b0014071038450f40b207a0700c4d101c0307603004100342028160000382040f0010071065040090303681211001030406190648403107096060107009404103050141c4585c05002d1010b0080310214020010300c80c0d003082c031011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 779286690 1250 779285440 779285459
    0x160510030605060a050a170114010806030c030d09030204060f05030a080d090f0f05010b0402160813030f1203050f0613090201031116030206090303060109120f05030a0504080f0d050a03091401060f 86
    0x449065281c07c401c1c0c1c0040100054450000c01003180a2829010aa8074030012a10f4820070304a855014130883d540000d41584c0415902e058905c205c6041c01965911003031013070410f0b814001c440c0d1507080140080e000039800002804400d103c60b4000c03d8103800f54403164030310325441c1000c1e1005580304e1100020000280700e84201500d0855003182080411400ca80041200050083c051140014600806040400004015607102c440050840c8591802c080c0c0d0848003204100800d0401c2d010401e1a40d0301c642c668407901e40038010300b070960346000745107000d01040b807810b9051542d50301288481581180003009400540b001154910640e80340c02460110010214451504140107210346c3d82e03030140008085809204034440a01c0c0d69041c1030190480d042c80042451100152890004d50418082c20888100d0170079205508091003885440f80d8018111500003541000346485440c066404008018016960411101060031000d42151515008079000f500c0e100810042041d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 779287940 1250 779286690 779286707
    0x10c030608060c09030705030304080c1305011802031504090507060909050114060c2503020a050d031713050304080c100903050714041103100e09160510030605060a050a 74
    0x50a1404011662811608685991003d40059240c05000131400a242d50403c921005001c001341500e0ba205c2c2e9407014207607105040d14065008c1d601e5801041619416840382c0c6048070b1018010400403e00e042102c402503000900e4854101c2580d8030900c03c80d201e80c410a0036092042c0000c0c6049401c01d07401030300101165103c2000d403400c00780180300142048518000c048001d442c15909e40040f01e0302e0a003012100e0301039a0104251541103594104c56480b580201c0c0c0c02034501c0c0c1c01541d1030301c00340000e0703006207500500800c1300039488072049006100616480044213100d03007001d180310703620682140c1c0503174440400c641c00003c0030940342c50000700300082c170482828246060382c515a14141c0307522061040d18070350501c0c051580e03180e480325080040c40111611003560f40f440c0c08020b0004004041c090302c40f000c000c084c0040c884400000302003054044044040b41c1e06840c1c1810400b0941000c0908410540c90300c10001e281d48603070000d050502207948550b51a286101402000f158 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 779289190 1250 779287940 779287961
    0x506150306100f1406072f0d0503030f040c0f0605070b0903070309030605060a0f0e151c0b100b07030504060f0c0206070308150603012304051b130b0a0503070201 71
    0x361602040203444810340307038031080b0359072401090a181814400500c6070f02400c08054884101010136404032068044101c101e40d8111046100807d404424404035045c451002012940104040f800314128894429030081c82040442c03090303034849224116440c1e09901403001314001041c403004214006c240141d1084a803030041d400d04c0e00a031802000d80c1c540b031001504d40daa84102080250f22595042070142040030200b00b03100e41d0b2601d100e020b8030302c222000084000a075101001c1c40c030308021340c04010508070f10640143c68513922611380d03058016160154955010780001010360b031030000ba250030740c0651921615285000b0001d041c082c0d1003400d50003040004070014005035110800e44001d02e4062421031510b41e22812085400402c8010710342c1d102901000000d030b001461a0140c60810088078511156070030b810500041d107001ba03c082035a02140da840400e9000c0c404040c012848507450705501d80c5540e90003510290380031240c6100014800000c002c6c00c2e5409000754207548 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 779290440 1250 779289190 779289211
    0xc03130509090c120111130504150509180319051e0a1e050903160501030f0b09040314120708060a051918060504290d0b04030c020402070506150306 65
    0x2442c001d10340585841c10a07403058881c0240c074842500c000000d610120403500c0f030480642d50f4800c8500580d0b44200305104a0b803107141031902000c110100c0760280b4040312400340042000c0d440e0000f01d18964500fa0144c140684000d0001804005140650484250054980a60754500780000b80c01d0380c10061404061030303008000541c0c0d1b03594042487c8008082d004441a018000490100c509216101d4034950610814a903a040850160f131000300320389007624100801d42141070400c0c16180070b0303c00c1e90760106000e40000c001c01d00590189100c510841040307480c02060100310b00c451402920944000340e060410021181820b14051000e0402214401c1d0340c40382c005c4100d82c0e041900c0c082d07040d04600307104900611003c40d4207e540940402002800703401001d41905e80148441c00714011040284030214265060400c4504105a04103189040c2980c0b01d03101620b400011540403a006a0708000707183c086001401181e002d008c804071140b00003230a040030589425009440355086 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 779291690 1250 779290440 779290459
    0xb0c13051005070308070c080310080715020a0212120313020405010603050408091009050604060e040b01031103010b03100b0a020a050d05040617060a0f0b041703030c0301051c0501020c031305 84
    0x1d94001c402d4804040e803514004031265100002114414034607040240502404414400120500ba0000c0141c5450030112228076070b548601004001441e034407900560004280d510150400410700f12110780341404030340344600541207180066004075100741103594440350140c21884c007801b54038014101460b081c82a41055250b070a958480d2f410550300c910248030203100003901910031140180402801151200d03643c070720141c01c14240761841803086142c500c025400d580640f05041c10403000158036400c0d81e0030040a45926072019062800c51051540e000480102c4400104898803095001c0d2010110764a40b0a25203440030306840c080c80400d110a2000a5100b1040340700d00c6c0012200c0c6415480303103004a400d000c0250000750000d050540b01050744c458107070041c0300b110b00105c003a01810780c03801d007101e840b80000e55070203209071800c10040149113401044141042d141c03400384c003800081955064220307484800b00510326000440c4565441031806800d41c020705003641c0740241d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 779292940 1250 779291690 779291719
    0x70608070509150a21091106130b0c01020c03071410110d0209060c0604060e06100305100f1b030b0a0b0f0307050a0903050d020304330e06070b0c1305 66
    0x752288032200c3c100b10318400f181c0004000e02c01d2090801304440300044c20014850650b0200103011010410391f503a03d6101546600c03401e080c000c0324021702c8a005c01c0c50a4a080c410b60010a51000301014980c1d9001d1011481000c001d00050403514400caa9020241c58842011410000202c8403507811918284400039201c0d81c003012035260360040140142d46913403200001e411405001800405489408208010081c2030350110b107400c1d405008503900da03034030207070900300034052800010f1464200070342c0c1e100d2400007030b0000884411003613000304008091030002e840b141001c00c104000207440d403042c0c5c40b250422902e800050100091a10703e4035000c45252101403102900d980c0801500003a0720306d4142c031039101a0041c55000c4246c1da698901c03070303100a40d242c00601074094510f107110070b44104c801e819221400301070341001021607100101c1605542c000070726040b598218000300a90703400950b0b40030780c141c071840000d4412522038829641804001c0020340206004e028800455507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 779294190 1250 779292940 779292949
    0xf06030c03020a0c02130207170409110c0a02040b1305070815030115032d0c0602060f01080a140304150201150b090306011e0902040b090102160f05120c12070608070509 74
    0xf44c15601078480042c1641c400c1d16240091165403c00303000040a074090301e1648041000800881c0c0c1d420740280040c40c0c8140c1c1d9210103100c0c2110054440d07002540c1c0c1001810503410a070b00111004240b030301c40d2001c0ca014682a00d1088403d00d0001d540e45007040180c901c0b40958041e0078105500804c00b0784a20303820032110340c0640c00b02034002d80c8030400103207000c4201c5460307680c90f01c2180c0c1008040c0a040c034041c1c008580030b0060380c015004a0000a4407611010001812544a40010445074500381c494420007036640d104100e43e40070407c00450412860b803c0c08805200a5000144c94504040396148900d1107411590081d003080182003020381d0f0000c0d9207030565040c1d40003601c0d900c07080444081032480c0c0e640401c02c564000300e00040ea2070500c0740a05200a4280c0a03100d92840521218802c1c15003070082076244150b0b078105010a0402d83e030702c550035285100495035100c607060005185141d0000f01c0d00010707440704005000c015440000305c1e402c50110700f0300c142016912400107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 779295440 1250 779294190 779294207
    0x515031e0706140405040603150c0503100302011d09091f0905120310030209010312110c0a0b13090e0604050d020d02060105060715050403090918020d020906190f06030c03020a 77
    0x1d04100391203d4440720009035004582c002d2000800070080169a031812040c1400da040c00100c8079441d0034500400c003800342045038405d0a250300a0700d2040d08540c01511040e04040308084902e1a00885417240c1d00e4429126000e141c09100030142500700d18000700d48085d50441d202181c0f030408283d00001403001036410030fa02c0e203010519807240e0b10104084c82e22240c0d030303101940c0000900000424002146400d4014410750f9941c101c000d610319100716640c0d079030380400c10341103140a2020031890a010001d401c3c03c0c9158286601156a62120a02a9540d5000b582526003040092008000c0c0401c5070054003005400500885070000a010f92a2001403003002c0c000c6c4000900841081200c080c01b01d245140d19604202a0400342070080c28021540521454240f61601920040304100c00700501c0c0c9500401501d8100801c0d401d000b04090301900030b41d0020036000e003402d00030301c2e441c8034000509885072a440c01031345042401000d4885030307a880c0c03042c9441044140b0303030250701c80c006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 779296690 1250 779295440 779295449
    0x91b0203270303120703060e011d010302010e0d0609080d180f030804030c1a01090b010215010515160303090510060506030403030915060b1216120c0207090515031e07 73
    0x1460600d545000460f0a52140d85000491402d1060400c0000c0b500340d40402c4c1a104060070940c0280c0e02c0380303c00b810795801c0720070b414a5250401700400c015840f8801c140d070000c070040c1856445279030a645600c240e58403d50105c620383c1c1e0109480030f1444061240036183c402c80244148540e180361622600703121210310250400c0700500006040c58000e2406005480d4014410a2a01c440000030400c1d01402c1c000d042e9181d0a00d00c0b0707c10550300c00680b050a0001000710160345034602000c00c030302481c0c00c40021140b054140420340005407401c10800f801e90280c2c4002c19250071514000f4104590900d01580c090306d409000c1c44039441d01c4056a90003541070800141030044e505001c01c0c00c665a050000c45541041400310f10007120303401a14010310790a000411988034021000450f0b4803604070710340052108800c0d229180007035000351618040d940181c611680d12042c200e403c1e6442240e4170381d40c00c3c1d0440003c1040d8142040202207080c0d00c08160b20300500c50246090311001d1500c103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 779297940 1250 779296690 779296747
    0xa06120605072a0b090d200c09011d0a0c080612150711071d060d03050c030403081c27031103041d1510030509010f0501091b0203 57
    0x501d0b07841c02040e0b1610f4000c40001d9a481d9121400d00702e0001c0c505041044510b9650040440d003203e000041c00303203141805440b103031903903500c01900c644241d00e040c3c0440100d104443c411880383d207840b072425010300520981041071080c9004030102d01c0501903c880d200c01c0c0752001d000000c3d9031180009030004c1c02110b61072244c0989040c510b2038807441c1040c41d100c26214406014005030041e03101d4841c000d1348000da403540c680d50040c101900c800100703040c1e48885076600050140c03800c0c184040707034039110382030480c00c02c00c40240700d614542281c0c00440c0c0c400c07800146101ca00c40462200e0703141000d00c50b0207200688009040c2540700e142800104088114003204208041c00b0300c0d1030020651014085944580e514404005003c04000c41301d504c0140e0240071900302e0050700801e51041758003505010191700b06030740072002040300810102d040c2d5030f20680c04400003c1405058001c00010101250324403110762441c0e01c0040c2c28030340c80c05661040009038040310006840e4080e5016259 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 779299190 1250 779297940 779297951
    0x1170f180313030804170d09180e060711100b100c020109080102040b0403230c040e0a0501140a0c09060206040b040c05030d120c09030b1603020f0c030304030e060a2c0a0b0c01050a061206 82
    0x1049c036000341034080e6800705030380920010801c41c1c5a1004011101c1110b5204607010350344e00d131840c9801c5030314404000b6000500d0240d444280c5020350003400c07400b031062400d4042d031651401c0e81422a0081e800480301d0000008081051010041d034880d20003240481002c400e6401c4400c15544645905216004079140e00301a09028028444c4184880c3c01074001d0101040750180d01d00102000c0b501c3c0e60343d06240403800c4041e60303c101145402d580550300101031a03129034803800c09441005104840c04039540700c02054580b0140402684c40c0e0b81500c9a2a00e011000e200c10305590342ca80c604000c12200c0c2e5400c001242c0c5407810302c1c0e00244144944104d00d0b20505044010380309a1300c0001c00b0b9100051b44d0308800c040000210300c6627000395940b44000c200102080101d20441b100f0000050040d207103400e02c80e940c10b82c2d1281d00d40900ba0411303010203a0b14003040c8846482d40c8109803100b004115241c20000c00e0081a5103c40404001c0180b2418900300725091001c214000e0031559490 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 779300440 1250 779299190 779299229
    0x40f080403060605090f0f4c0b03060d1419050309011106070c0f05010e0a0308040b0a1a212508070b07030c0c0e0a050601170f180313030804170d09 65
    0x43c080f04400000303d081e0841078107008490400041ca03010f103808c9140d042c100001520b03594030083c2d07070261380000c0c021054030703803513465480100c011100f865041b80a1801100c4903030036038020003220648a10b01a584440400001401010703901520030348a0308070404104d01e441d4030060151202c1d50200e00070b00000c0c00c60816900520480b0411310f80e6104032103a10062640099080e4031841c8528011001c0c1d41d100c1c00400181c59540c0d0844030b08403081c03503e081c050710380003c1080400350740801d0f10044c003a003221100c0ca00410358005081c2203028a041c4925071150340c0d40300018207818002001070070314140c40c07010548241c0c500076040000700d0061208021020007044000c116904000d07059080034508100101015190710780031a107100000040ca50341000c12522800320100103400d6990383c1c045655000340340800d11401e0380410032105500d05c04180200c40514001d040190b00d4a007020800c021100c1805841d42845d03020091000d1540e40c880460300550f4607904203002c040440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 779301690 1250 779300440 779300491
    0x506120d140a0c08030f0910060b0a050d0f0915060602060f01150909020d0219030915051503030d0b0f0d120e0a08010c0c03091d0f040f080403060605090f0f 69
    0x1150b001040000d0000038040070506d60f10382c0074044c2074100306480c034200100c801c1c2d00494000d8810360264800c2441486d190a019038054045d02644c1c1501255800306580341070111000368074103d858914221010541c680303613100d101d01801081c00104001d0800c402c01d0020b80d0014030940c0710200c0c5642005850f248940315060090030460710664070f90045010f2007010b5001303075102c4518078081c4031103584101d11038020504020f03000066161541d58401283d0050305005090442e211088a4100f0729038904000804500800d41c1002480350042805c021803a100c03451000e2040311114183c8010910f0801d0b91840c002c224140400c2e1080700c0c8011030a10700b4180c0c09811070794a4003020341445034201d043c1001c070b180f0950766840f00c2c80e1660400030319074030795860a1350b9541034500014800d01c41c0f030861580080c0602e902103043c04403540c50303007415401138100312013884c1c941d00d04004074103260f6401908407a0700f80b2400100e00e4403144001b0600002000c000000e80010030141c220200e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 779302940 1250 779301690 779301707
    0x1031416030305072f010311190905240d0905150712150b0d051f03120201112104142a030304050a030f031b060506120d140a 55
    0xc00304812906941d00e0078040c0c0300b500146401c0c0c4a804e20310710981d0a0307003a40b01e00004840528801010b4022407131004500400c0e0040c40d60b40f02003403c03c4402c0300300c0d840c421240c96010283d03032114007a5041009001407000e0010394254200041e00320750324900a80429a44044842240050317941010301380740d40b6010119958044018001c4103004005a2002100c4100c11070705e030084c0811040354440c91201400c520a4640c84003040c800203203071000b01c3c2c01107a0080708049100742900e0b0310041c904040304050340103e55012191900314501902802100da031041099512810a0003460403400542a142a181c1400140c07800080400c450310540d0f0a94040b0304085403240c81c1d41ca45020069a003019001d03028900c01d40741d00849103000403c4800b611700180600e0710007451542e41404240180c03c080381840041c118500812540c600c8003100d043c0655004116400d2000c28400315108035100380d0001c0d0031446040e983d03240c101d00c5003004a0900c94040340e4400c01888221080314 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 779304190 1250 779302940 779302963
    0x1050d0f06020f070b0411120309100905091807060e0f06090111010e010209042f0319020c0105012d17030c0321010503160e25080f100608010314 64
    0x10042015420700c017000c1030652049225681020300080080304012806050040e244d49a41c010028480705042c1080513034904440f50030801c8030720b0b840390006040e50404403044130280348003040407410070404003c040300030055030400c7e08411108a000c0f494100703c201040b801010009500c05207030b40710f402c030724480000d50b1000b000201c0a18003698040d60201141074461800e1604000700c0c40c11400d12221304403454115414902091040700484d500300030070303140a81034036040000d080802800185040208180009140e43c10010b10042d500c480300d120244400076107025080c1640c620040c00d040da40c1c2e04032046040d48070152024074500c1403000c02c00b0700d0300011425007600d503808480303142010f200d4042e206d82a03885600b032555400c1070000e00c003a0b600d01d41c0c20811000d240c44034100c3e0030140da0140101c1901011032a48501c0100b18902c00004116000f0003008140031100c054002403092103c4284603d80000100503800c1800080d0440b00500345404850f18104212403001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 779305440 1250 779304190 779304217
    0x90933010306091104021804060605121303090e10150309020303072a03150b010c052e11220f0303080606120c070b0604090b010e0a1d0102040302120601050d0f0602 72
    0x180340ba01134080d18100e0042d1400e01660a00380080b90b2b00780180256119902040c2c6005100d0350f40a10260200c0260300e0190f0034001088404a041c0c0030f0300340c3c00d030301c036080a0f190308044910700080340c03080402031103c4500300352401c90351200682d000300886c1c0026030482c02d0b640301000800031b41500e4408015038410701c1d0a004000004001604083c0200289025000c00c10829a0001541e500b90701a5009140c0c2c0c001e07814031013600090700c07034610075041e01403501c0c4100890010500100ca003030740d02a0a042c1008038400381704110107560410503903410150705500d18500501c0e2202d0b03500c640401018801c2c0d41d00029500d0301d40c1c009607040c403404681c00841c0b50504900040f99580100d10070780b60100c1140000d003150a2500454048541c0b0101c4100e00740e103801c003c0300741540040c0c620707001981c03511610350a05c0b81e900b0080e0301440022000590304c503c3c600c1000204211030142a40e03c1d00300e08010006d581e9040d13500c22555400c15400903006529142c180004e2088601e1480030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 779306690 1250 779305440 779305447
    0xb04021207091b0e030607200a0b070306030516060504090c230301050108010f0f050d050a0f030206061003091a04030215040305040e0a0e07140f09093301030609110402 74
    0x50301c0c036004031101c8003041030301d500c80e04848080605d03458020032184400410079680104585850158004076980c2e403003000e80d1510142036540228641003078a03030b8000a03841d40014003e120381401701055400c0f4400a50b82c0152424102403c00c3c01a4407400144960310b401c00b1801d980244910b0303140901080c940c5038401d400c3c40000382c554100303024090000b4408030004c500103680207540c20580c0c1c1d92181054202d8548070800c444142170903011242806142c40c5d00001171811a44031801038030940180c6510314010040c00030310144000d5803000c250400401d0400304500030301c4e100e1200002ea54001c0103550b42d0405a14024599040010145840082005046d4484064002d44090501e80d8110b51114103611007035a0300d02241e145182c100403c1000b1500d5450058200000007411215020280304006800d599084030056440c6c3c000c41003108400c80b81083e03880740d107814001683c8181a14228802070b00005000042c800c07070b0340f440c81805024820040962201c0300a0040d5034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 779307940 1250 779306690 779306711
    0x108030a0201050603120d090c030b09100b01020d05160203070b120105040b2d0406150302030a0b091303081b03012c0c07080f040302040608030307090807030b0402120709 75
    0x1a00d60020308400300551800e40864418030f0301260000080c004900c1c001e042907001d100c540020003003260300300d8035001c1144000000650310122644a001c221000c0d180a00005084500345c60007901054110f411500c44d5050450b04141510300d2254444985002c650302c910104e4a40040382c1c01c1240901d0380801e4906003500c007141084e068803000d9800340300319034416080c4a107502d60700c0312640c90302d580310440341150032014081d01c0c00003200030404501c1a9071005100d40d541030152000000940000821011039218091031818680c1a02c1d00310f00ca00d4140b4000c40d50010745880101040400c0002c150801c1119091310020304000440b16a0795030b56010380c1d1102c402081c0020f00340c24030044d01511051003001d003584100c83d035402461909270145c2d01d40c1e032160301c16418010b50000510001c405a01c840c414003016094003002190b490503c0940902807011a51000215034041c3d8410310028118082503500103505a6580500000250103641401d05075003020000c90b281440024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 779309190 1250 779307940 779307943
    0x13090e030d152d1a0c07050a080309120c042c1b01120e070f050109080a151a04110a110f0303071b08130f0909170a0c05060108 56
    0x39001c003001c1c020410154a90507515200480c0c0c07250300300300e002c0c0d900d090511012900c0c08000c12828000781c81c492070b8075111690300382d580800030600d000b54007041c494030403102088030344c000d00b41c01c80d81c1c038200ea0b24000d403c07541c07031141102140c050110102400c0305402c1c10411612032440043c02801400180c5500300d180b1660303035107001501c2c42d002260000c00d840111b54000c0b10103410b0302920069058000540380d0000f4544210009a0313651040301c84101c0922810024090300450b8044a5141200040207081960002c5010350800310004c40010b1552140042c841c694400100b00c031416800d1441c40042c00ca00703841d800a090640c0f41c06003002d08401051503003e140ca46650354041022019a950740700410141c80f5481000800c44a50003004a900715818a602e0384854a11b65a02c00b0040e412500300c5120031001084180152142144d0000c040c0c0402d403c10415541240c61745d00302d40300d03e003a8046001c0d4002800b520824441c1f8181c9000a412100f180e080e035035a000c42c103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 779310440 1250 779309190 779309197
    0x10b180d0f0b071b030807030e0f0708060105190e0f0a02090d0323131703040803191e020a0320030a02030309070f06080c0c100903050904051f0b13090e03 68
    0x100005003800805071303c0805881051504a80c040e9548800d503616070005070300420b07540d5641e1031a449080080450743d9400c00011001c0e00f042c3c0c01038586549400e00b40505600b01c8000c1812460003980709102e1140141c0345c080d88040c49000400584c2c641010348402441044035250308507400072851402d06070001542003108481125120340c0c03200c03409039406240141000400d100130240b9042095514412140c400a04010240d9245c103a0764510b4520315030051403480485c4903c086040b16180d0811032001100302c0401c4500581c66400400030340f1902c0e110401400c0c40360300f0b440300181c61071001052031514441c2e0101c03903940c407011001960b82d8104880c0f49a2600c20080c0200703513904031704015000c50f440c5454000c21a02d4418801203290000500d0034904d00c2110315400c030150450044180c03860280d1142a84d880400e020300094074001000c40010105080b00c01c3c0744a500011850100c85800f13400548402050705000c0d07040010358410a100c0781420384003e00c0c0c0d075000c0000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 779311690 1250 779310440 779310451
    0x41505070b060123031e070f0f090e0f0403090509070c15090503091e0a0f031a07020c0f01020c03071d070806010c080a02210d1103010b180d0f0b 64
    0x24081e02ea4905004403207100c0d01c400c044140d0301ca48086800c200e035696010f9038001c4000130704000101d4420010080c5194101c41e031a00203080c1043e07129030140c005814009456040ca41449003a04220b1160404000502043d00410903000000c05140c40350841d0700162400404042060910140c002c2c036000c17119000b50380c1201205d10b081c00c2d5200f1446542c0c01107031303c08003641c140700043e001c01c4800d5502220300c0d03014070340020310b01c03105d9500c241140024050003036180c0c9003035086007084020b50300401043d040d202494401d02603c95000203e94054000444a810300441020f0040f414003162540083d010721502c10302281c200307003194502c01d02e100c0359900c1008540d00c65008840300d620a8a106011840c038501d02400708070054001e00c1e03025481e00488110612001d41c0800e00c00340440840c4071080c02080b0705807080417a0042d2155010405801c90030765041020348030092259888003010300e40c501040c0011602d43ca401c0014a41d003080c4162a0307004241800600c0c0c08044a9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 779312940 1250 779311690 779311703
    0xc05010e030a110304080d050306211b1806190911090f090c040b0304080c030a0e030f0c01120c021905070510031e0c0203191101050f09100507030204150507 69
    0x2240100100000541301110700400c0180b019041200b000d82301540043e003500c1d0006085d083d41e505407580a0141d13200000244000c20300b03014990340c0c0c9404000402d2a00b0700c91480081c10b12031700450110400d4002c00700b120701c0c8400a1451640c03940c84003a5510504e62141484200c01810044502074007425000f5112000c0003110001000a50b610032a41e0291559040c401480b00072040f0b0051940181303c0c0042034034042052044503d590040e01328031000a0a140c241ca0756401c0c18082e2840014020000b083d0211103a000030b4a8500314a078a02892a501d000104c40c0c0c41c800c12468039100910150308464998a051480d1284098095207000740c0c4900030440d0b62038840d105821144d0300b011141742103924080c0c1080007a1507656250030451000f400a11900654040b64400240c083e48400c10044042c1100c182035502c0201040c103415402010045107060219800010b4a45200c000800b60303030300c0c1000d80090280780c02844403a0b89503400b101e82e8540240051060500602 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 779314190 1250 779312940 779312957
    0x30f0e0f180c0c07080c19060512041e110118061d0310050c07170a0f051309180203060a020408120d06120308010303020f0604020307050d030c1e02090109050709060f0c05010e030a 79
    0x512035144850300d00c43d200c000b600401c1540390060460000036003040c8203604400b801c4103301c00044d1880c800716416a030031030520885190b00c1da0003280301050342c10f1141c40c40201d90319108005d00700400f0074060f01d030360005410003100c4998040c0200c603120034070406d00304554107100215804035089554115194400380c007544140501c0718090f0703048200a41e0f101d40c0304020008080741c540d0040340711307000700103681d210101d203460701409040c0841e04184212040c002c03517801050f1401801415034042d4a1042100303000524000c5071043e00c50b0000058540c0d00c241c0b80c401c20f00200591303400014110101210380c41010b078001d104070b0480e402542200e4060400c4900c09031a1041624000c0d4182e21401042002e82010600054154002e00f030840c4518603d8441e403050081c0c560128840e80d1841900b03030114544980c650307014044e4040308000c2c03880d0244024041c3c81041c0200414003c0d0750408480c194440d201a66505030700c040203001c03025103505015600d410883c240c1010602c0388 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 779315440 1250 779314190 779314219
    0x3110105070201090b0c071802031612140f160504030c060806030f0d020a02040c0f080a0c020309091f080610090504080d180507060e011409010219030f0e0f180c0c07080c 75
    0x2802030340e002f039410500361030080c00241025500c0588107100840c4450300d0321079814121a440380d141d8410000c40490b80e4680c9005a0341c0c0d51014082c45524003400b00901051011a01450009040e20101d046c120041e41b01c03200000d240c08221299001903104180d901e02c840c2da80400e400d17004900c2960103000040109409a03012805c900e82c2d000001e030741d080024250805c80d084408546400c0c019240360001c00c10220704210300131078a10218112686442c0c1b07003d15903072440b43c01082104080c0a0a00b4181c00e1107190b0111403240040b41e54540c1302003824410004116040003203000e82c1041049054651000606080402550340d80500000010740364080c030420000305805a48548001ea541c1c0280e0200750425800c26046200c0d4000d03440403001241182c04015009403903840b16440c211000406c01e000b60130030a03015592418078150141c842d904800d0101000754041d026030381e01c65594000e070380101d40403414607202d0030f100020000d80c0480c80343c801e2002a02c55400040c0e01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 779316546 1106 779315440 779315489
    0xa083a0f090f081c0e01051c060e0a14090105010b0d2a083c040611040b04030302070b0f03040b04031809061e03110105070201090b0c07 60
    0x641d41074141d02c404054651030702c813030f29020f1141e11800340020468050040411054142400024007075500c581009010b0500480c40314114a001301001d07019048804a4020300381414001c242c0103403040c05600e0581d00c0110700c0381e16081d41c2290090040c41c4010520401142c405000040c522904a100458480d05d82d030304881e038100148643c0c4050600c3d0840026441c1c18400400741450440503540c03064900c1055140316681c1d410000c000d0840e4215100c00110001070114000700c941e005402603a0003982152203890b1075203000500c4d271207406010302c038120080c00001c2c0051101c540107580b2500c03904e0050b441c0c15a405a85003180c80903003240072015281e000a000c050040c13014036080c0014200403c000c980b454039078007800140c00c401c1c24100100021400c2c25a4000d014210003014910411507444a2451500307840d803019004052000c44845580f40c0e40900 = true := by decide +kernel

theorem cover : BRFrame.Cov 779136690 779316546 := by
  have h0 := BRFrame.cov_init 779136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 779136690 ≤ n) (h2 : n < 779316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
