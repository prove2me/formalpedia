-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4055
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:26:22.984108+00:00
-- url     : https://prove2.me/submissions/e5f4f186-0c48-4ad2-ad12-32e1069be319

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 729136690 ≤ n < 729316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 729137940 1250 729136690 729136717
    0x30a0308042402181819021e070506040209090105100e090c041a010e180a05191404140a0c0e06010203070510050f010611102012190c05040b 62
    0x24202c40e1040e05100030b01000d0301c0744001c441d080803075805003e0520b02c108150a600304401c002c05c4000680030320b8520795400c854200507541c4044907900c0700d180c80c1c0d0760319440d0b10a1000c074204007001400140c2c0303030089008a034411940c1d501c650b0000d09851003280e5901d05041c0c1c404081182580e80400030740c000c1410000c1d40c058104201c0030400f00c2d10b82030256610491050540190341d40c01001344185440240d41414000c0046401910b8111001d0b088a185956900000e4041c085031014140925207180d030511010791849a00e0700d08000c03d44080da80200c0c50300201d0540800025490065039110805808a40c5091301501348070304018062410742c00100803075400203d0038043c06075030060b000400a9607041410301859038000c160460410f0183d10919600c03480000070b60743da00741d004049c01241c80c5c444142030600d502181c1c2041580d1807804699001c400d45400c0c0400c1c40f60322079001c0500702c040c0c034226500c1071720588048400420303c00c01050010540c84401458082c15403072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 729139190 1250 729137940 729137993
    0x910020702130507180602030c192f03010c0905030c090414120715020c150405010b090a0b01030506010516030e0f19170d050d020d0617010c0e030a030804 68
    0x50b85400b550f000319080c0b80082c0a254072500c3c04a52890410060b065900c001d50a14828030319903070707541c4196407090300c3c81444040c590081000321003104110000c2d90151220120080c042d1468602480c94043c1c825424648420512882100c0c04005c648c401002062001010000e00c00d0083e4043c20030380300c12400c00050008100b04100745900501c142100d5a59158541410340464041c02c22208880c1d004201400814500140d0b030003039071321040402d11041d01c4501e8001e005144210600c2d07040200d034070800844201030b41c002582c24030289c0341032015583ea440115868071441d404013400c11404161071003c80d11505408002c0a009800c001d0791406c107000050700b8500302e03280d4018040002000388002603241e50681d45c0303520714000130320324031030861000f0300b00d4021900f1500ca05580814504080c201d640c00c02d1307000303000540d07290003054800c044183c0a01002020741000c1418512505030300d050004051070303040e405688102990303c81d0703900c0480b001c100595201c650003800d03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 729140440 1250 729139190 729139219
    0x1312020a0b0c0705120f070e0105030a12030e0a12031808041205071d090d09050607080a1b030f020705090405060106030c0210020a0c1205120703050c12090601061103030910020702 79
    0x20306180032000b10800091000f06c0500d200b80e858504150441841c2d07030304402c01049a5100012482e0000b0f900900c03405030061482400ca004001400d01c200d241d214035000d100500164903000307018510304d42d4062180d140e22140c5001d10b04612500201400c4041208000c4501c000c1c40340400c0512440503540030950765514003029103200561800039401e032005100c03064100b04070000303002e02e86082c10f0300b05d10b1400c400200e490240b00005042141c0020794992501d204400640144019904d07010918455003002011116101546400340c41400b10109683ca48081610302c10b80d03018005003d9a0f003412012001390150380d940034150720032309400080607030490018103004001039551b034a030403a0310f060446114542517005424030000f08050031003850050790310b81d0320555a05000c241502e551740c1ca5000d5120b0340c003018124441d11014003551080c003149080c103c55203a40e230320300c00d4110381502c0d1742c8038401628284050380c428402e05c1c6500c2010340141147c00e000400c4c051070003409 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 729141690 1250 729140440 729140449
    0x102191103090a0f05040e15040b0a0e1608070f050f100203090a0905070e04020a0f0e060904060e06040e0309010215100b0a030e060a0e0c130609060602031312020a0b0c0705 76
    0x154004d080c1503c94501e0500c954101031096103d80e4030228020400c200b440d0b8039007080a203000d4000b030407007400240001d440b4070050f040b030b0321800312900403905000d1b0b0305480303400403821038084d112135405010350004210710603103210f4040d034000a1800480c04640c0c401c12524101450480c0c095001c00c1c4100c8000b5511403100b8001008518404501890f054000500002c44000c0c0c03a44078a1040c400d101700c480d880400a812081541010702d0400c94680000d1f03958000d015010b54442c2c10482d02003451801514003c2c064102510107110f2090401c4240d51240584045640140d000800040712408400c82041c0c000e078084412030341e400d4071001c00c01042d0340001807400c00b0075156500e0482c518020070213164000c0b4007510400c0146108009031741c035070141015880c81041c001e0314086402c0c14652101c001006410300810149642d640b000c0d469801101d900603450411510004040340c6952008000c2c40d4010040b5000b10f042c8405160150800049110184203040d400b1950391078 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 729142940 1250 729141690 729141709
    0x904080a1d151c150e100b2713091103030405062203123b01111e16060201050106020d03090614191109031908070b0c0d0608010219110309 61
    0x2d00441e082041360512901400d01d18000e490095201201d440c00c00c20100c1d00c40076640c840410030283c04514007040c4844c41603c00482905a102d074041a010b500c040700c46c3d00c03a4000134031030a00040903c295800b056101d006034460103411890420182134103802d441d020515680c4040081c1e445141c0340d4403150418050b96075400085000700300031380003000f04a05660f00d9562084540c02410203d200307400b80300e0341c041c4881414040001003000550f401885030011168001c03050394240c2c0e03e0304822aa481101c3d282000c040c0d0300b14500400d2552041c0641070682d84180c0052100e40c42e01e100440040c0001d110503503040307980c0c00d042c4189581040072140503007021680b032440d45000ca0ba4140864030000c640c421441c404000d01c220545001c1940d0799500c0c40301040c2440c2e000c107428040401c0c80b4248000b4500100203003041200981038018200300700810300100302c050f0301c0d11001400c03071249460311241c50640a001030403a41c42104602d10000400095074240f55280000c80d002a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 729144190 1250 729142940 729142961
    0x1c05010f053a12022817030903040e0405030415051303023d02010c030204120f061103040b0906070e032122031412030a0213050904080a1d151c 63
    0x20000e521100e104d202072014410b80950040383c2c1788216042da51205030301014496000c0300f0080c0840010020765041c41640c006042011055001e85054036040d80c0307a6000740624403101c1002c1e810360280e40d20a0040c0d58404640d03445003c081400c540802c629588070408103100c0402c0c0184c1c138440301c04003600808034064900b94801c1e051080d0500a401e49801d44007400405105000070400180a40d040c03030701c8a42c0000e60810302201034205003000c0c00791410900a0b200000040c842000b00211803540b040c2d05d0b034803d0300d50a4039451000c89500c0444128254140d00040d620303c50300c0d40ca20424058031140d111503910b00300c0658450034122550340f81000104404486c1001404505041001c812113820080c04c51800d6100a102080c000a03162965075070780840d400102c00754440080d405807200905062161405e4a4080b1072980f00490090001d0308240c92250510210310341c100200c84001c069040300c40c08001c2510150700111402101105210154003540d00588902c01402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 729145440 1250 729144190 729144193
    0x403170306010f02062406221a070f23190b010504050714130506040e1e040323090907020d14030709050f061c05010f053a1202 56
    0x346401d50001d040030040b00380a4041d0b410007010003445081c000c800c0941c80c000c421038584141080b9010481034003a0f140e06005012040d81ca90174540c6075071030700390f048603403042c12400c00c600299201002c50050800003055010448140c10015035004510300c44851001300b00326621310071030407a07803400826204440e8514032072441102800030f2034140394050700066a06001505056400511100e0954001d95800c0d41c042402145802204481001440c00405c030300e4856480b41d0102d004548240e82c0c6524141c410841781c111140059203240c46a83c00d500c41c3c00705a515140d04d05841d40c003012000e014000c0820000301241d85100c401030065080d540100500c910190000c0d02c8ac010b100302d030b80c1d0b10000500170040140e0740300c2c66034801e8420903158000d03000700d500086049400307020121548005601a00c0f03000f88102d40c03049049807a042202d201981d40d60040c840255000901c00280800c4900048295641c0300040c100c1c0b8403080036075040d4645980c0300c402110004c005210f006 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 729146690 1250 729145440 729145447
    0x20c090f060114190e0d0c030506060a090903081b0d02030a06061b0b0105010c080724060603110313050c0603010b070209060108091c1803150e010203100b03060402040317 75
    0x42d50740115016040c8450f1083d0303070f1030440c00343c200e81140c080a007149400c03c03036003c00d040a25206c1240401050f0b500c000f046450326141d280c40d03601c400c01150074501511440d0000103040358103009003042a034050701d5007401078075107210414600310044219140c0d640100582d40e50076074213100541c0b160b502503000003142c40c18810000c0036102032640c0c0320101d900038001c0c0390103c0e004040040c1110b1090a000d40c40d2801072521900f14040c1e0704014100080c0c074021084140e40c0503568003a803501101d0100a09500e074a01501101c01d0080c4954030720f00c050000460b90107005040c03851240c0140b04841d100001c280010356940d00c03d8114007510719000c03804a0840c03d01e0300401d508548242040300140c608082216a252401103001640c0b075110141503080318051a04071003c00c05020b916501145c03a41000c00b80b6541220628048900e007e111900e01841842601e004503030402022141c54503003a807041c0c054001400140d0720650070000040025603216482003d070f20003411381c1340c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 729147940 1250 729146690 729146701
    0xf0a270203070b09060d0c1b140c10020d0c06020403020604030309140a0302100513030b010609080601150e130e150910050702060610140304051c050c0c01030507020c090f 75
    0x18040c0d65400f00c114028280181812590b80707900b500d40d100709002c000210b02c0100d42c0c0c02c550810003403e108450700c03c6e4602003c14084c00c6d54030781141069000c1120840003403503060009031940c290406006800c103507404010580329182181c0c1c0306004500c0542443d03169000242640d11944c01100030890f00c0004101742614809180c98650044810442031481c54022404104003c8160000c10100207022098220741180743e06c051038010f44001c80b1581c4514010b80038400034000c0307034030504ca020000100e110503c4500a040b4102d592212500c000e1002400a009520454116141c0d158090190000d004029490741b60304501c101032030a040040312142000c546204150116080030100003005800260058210101384c07070041240218180840f000200340c049280407400000601c81800700009402c03500c2d0400c440b11590b002c100060580c3d10b889200202c84450300038042489440d0301945c131040c1d0102150058600400c500c9c1d00007200303d4000c03100c2c801921001e46c1800b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 729149190 1250 729147940 729147943
    0x33112508070b0a0503040b280203011406090a0b0f0c0d0804060b030a050a081c050c07030318030903060c030209120d122009031c091e0e0f0a270203 65
    0x28018042d82050314903120001100804520000384040c00320144400450002019405040c0c00074014040c0c5008010010b018080a94001e101d010341c40e100124074803500d85002c1c01140c05080e801400300300d07060f18003801003515030400d8040da0f00d00c200c1813044c1c116450050142c400c1e01c094030781d03814619103818a001811a0a6000881d00940c032001c0b18000003440010703094016504051007585130301450f5402000305854080100c40282801c1c05e0108040a80c405000041d201e44c03801d0040140791044044c052200303120140016041a404201103429a440070240c2e400358900585416900da005c2182061100a000750940c06040109031041d0310185408514048403c14031914032001101e00d0304040000e05071000b018001687c41d1286d90400c0019180c808000c442c481c1342141100140815030203100e03905030900146085551442030014000689805107aa4100c6403124040e000c840740d002444503003441d645200d044084003000113010003082513480f40201c090400e20515 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 729150440 1250 729149190 729149203
    0x230913090b150a0f0b1b030d062909010f0e0303041710140105210a050610090501060f0f0f030b1c06151a07030909060f33112508 57
    0x290b0303030102012004c0c004500d01500b00c4030030008040b492403100f60404d1b28942107108100b138400c0e0142c07904d44000740b2a64410800403008200d408a905081d60310640b03000ca07403103540c12460004424250a00200d40210800c030140741d400703011242411b4aa000070510084019000f81d8150721080b541110300030140070380d40c0c5900520085844c1545803002244003c543c5c4040700d4040d003a400c1207840f901d03804009491401e60032000312000c90820000e00c500a15260003074175071150804d0004110980610000902c00c03c3c1c0359150751580d43c40700310481c0c0c401d0488214004250301d854150b03203269100e180c01b0110b40503d019004006021b854600202d42c92101c0501108680368010004080020305005000782e001080d603035280c5962034202d41c003050302e4020303003000c515080b004613162289250040640d0034049a403c1401c0d405100b080800409440e4244c0c004007402841d402c03d0302c07821035000c404110400702d400410640d0b80d017440500c0c0d1030100d80550300c031500041005a1042252 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 729151690 1250 729150440 729150449
    0x90c01020109110f03010f02190207121703061906020d1101050910020c03120406091205090f040b0a0302032512080a1d180601230913090b150a 63
    0x20041e4103000e41c1c0b085000d8803040315284c8204010095000716403030039080801c00e940301090855035000c1d90300c0307600e440c4407040355504014840d01d00e011458134403102400b02200d4000c2d461500200c00d00f066600c0c01c0c0e1000f400203811491950101d1054583e4250700005810300c5c2e0060420840e000c03100a014040d610b03181c004c16810300081c02401c920210301c030721100c00c40c04009a9190020403070540345100d071180d6400c0360a00c02c02000248101544680360252107040d2800314100c2a51007181c56000c0c1621440c0e00c500c2c400d81c0540d41d884e081c1e02613290369501420484800f5500d80019007000384600c21741540030010b000a520f02d08141c420500039200d01c8100910b206002e442c0d0b400140508030300e00051003d00d150600ca2482020305e0300c130507028010302456546040381141d031011101a50007602040e0642246141c8141c088428620402045d0b4000e0522048400300071051103802107518845a4a5540c900031503000340ca01ea200c1c80400d040d01880c3d41d40801405500c1520758403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 729152940 1250 729151690 729151693
    0xb100201290d121803050606090c03160c050c06040b070c12031b050114010314010c050306033c0f060c0307080403032018041d032205030d08090c0102 66
    0x4a142150340300d03402c441015400154140c1140c411000507904504108003c40051806042c004100324000440030312903d010380308110036861718402c12010340001d841400c0406960a04110aa403041c80c104d910680214102c645800032070001c02d0155125400403c10303060300003280d400303001004c00090001c2251000044c20010280c0f802403180c4c19120b0101c5071100a0401130702884400d40041d01d00035030b00ca1003810107582da4500301964004d06000d804c482e5003411aa03140007802034040c2ca00c00c00c0d019002c2c02c82c0c1c89042010481440e480000302c10401e0f01c03089500041401d590f40a0b200c02003242c02031417610302843e0071614003000240171a40450041081005131507200d01d0480c2c1055050802085418112100c80702540984403082c1c4450340c04252024907608051528850440649040107400311160b503c6001c1d0b029100c0c818042d5004000400c420003907108903078002170440b001580d0468030b840000742070060104420300002c07006418441141d40a00c002c00c2920f20900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 729154190 1250 729152940 729153011
    0x3120513050f09060621070309020f0f0a15050f0301080304031502071509050f1c0f080c0a0e010207030510020a03183c05010c080906091f0b100201 65
    0x900040303800400800f45170081030f0200340c2503100e0100c0c10409905d10010440710140e0b00c2d107100020014074901ca0305071310500420103254007034104450600450280034001c0401241001c0c0f080b000b0000161180041050411500e202140707100082c0d400303420484051030b1f4a81ca18240740142100c007211001c0e03039600c1000b03020005180c98a010050b05001000808c502c000f40c10714504100c90380b040d0b0b1400d80501a10400510900302080605030405e480b040c010106001049400103400c40c0c0002103d003041058400c46401a0b0500040610510441c4c03e041d4896070f60302d0521404c1200004040d0300880c0c400501c81e014000c05180c0c282d0805101710301c1100c3d884546440340400040c1c080f09a110a400345004074042020030050201d20134419102030074071300300d4000d2074006607540015404a0114550000100303850b40540d90420041c00d44000c980c41c1031414001c0700054018442c0e48050200a0b0b0b240c1081d03a030780262564000040860358485803032220516001440100303401031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 729155440 1250 729154190 729154219
    0x325031415071407050a030e1c020906040207020a0f0608190c020d18211406130605060f0901030b0f01150f0c060e0a080a120603020f090406060312051305 68
    0x2841e1040e4812164a0100b0300310155940c448214450140060028040e540c251414190000b420f03400c0440256450141000c1c4210341c0e10b4950043c480c000c0d03002041a01290662420340c025002c100d000a00700c803815507441d41480342d02d641c2580410040b41e014410800314035010314074110303080488101448502c0e80128006e4581c03103801020700502080c9080034109442103840310003e86490640c80034802d8070351006105140e02c002c0c0845458141d09401c0e1f10a9001103074250280d2a01d01080c0c020017040c0e0382e05005040000c141b55040003903a11402407035034400180c207008500a071002062418088024080c01c00c05802504801403007200920321035a00030742455840300f16141001c150070751407401308050311402100d4405445400504d8050190b51001024420308513110302000e00d008441e00360944038684000381d809404a620b0000a00b4406070159000e441307400001a20f40d1039950380d0f540842081825800500085041101140a5132040c0040c2900711030800e40341c0f204 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 729156690 1250 729155440 729155473
    0xb010c0c0b0304030314091e0c18070302071b1511060c090a0b07080c06070c1502071b060207170601030b0a0b060d060e060103060b0a09050f03250314 66
    0x41d104010401000000080034180f00341d00448401004007a500c026062601d411541d421218515091800c0322441812454030006030b141000c5801801c04c0c8544101c1d4041514001c000070405c006050b000c011540001e9161001800c00385050f00d8031070401408c1950b11101c100c882199003040c801040c00c80c1c0652034000074805d500c5485404810340e5001c140021442198580d8450100e031500440c41404004140f03004e07100d10000301007141d4090341c4103081241e00c88207103c8040d00c220940b00c00302c0300320843c6030020010680958582408200c52900b0414007111960150340103801164050000708114891140c04150000013013806e5411600d40348400000540841079003a40c0380d40c0c17080306407030700380039a01e100d0742c214420800d80d5035072403c01c1c2206108641160009280000c0810302918240c240c07140747d00d169442d010110b081c86d080c031a669000ca080b00342e0520443e862010b200011401d00501d5800382c000001c0c1040c034501e481540c0303a054000856003900605081c0c0358202e20b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 729157940 1250 729156690 729156713
    0x1b090615050a021c03230a0c02030307050712090506120403140c060109050711030a0e09070c03050d09081c1b03090f080f070c1e0902030c1b030903010509060a0b010c 73
    0x22003641c00400140d002038000703040d00041b03a00c0030700e640c4200304034858074051211300c103103a040400c1c040443c50342d6089880f4401244d02e180030400034460306000c10441c1140c0c081c0d0301070b1410005070750760f01c80b0001203070b54100144850b40c0302408401c02080543c890880c11250903040c94550410b0031441c0d4494844205000d01c0c1c074116aa040001c010b035100c0da0210074035103c4881070301d83d24060403000811042c084001180543d02d40c4001c06e41c0148034122100c0040c5d00740ea10141400c80d40c04061024102902c4243c591410503c030071510308201d100b46030703204000a43d00082c6202c0011415014450900968051503d40300b8240301188410204440203035000701015503c100a000e18241d034090004d01030201c00007803034003142800510ba44030400720400a50302d0700b429960740c00310091340300450b5014103081c4140041e0703040315500740580d03041c24140b0003904e081c0100b00c03010900315181200c0c842030662090301444854406440344000c0c2140a107407400c602ea010340c54134414101d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 729159190 1250 729157940 729157963
    0x10b1c0204140d060f180b13083c270f0909151512070b0406030209130903080403080a05151c1704080706030203060307121b090615050a02 61
    0xf400400c584100005940071924074607143e00b00b0801402c03da280e010070b5001c0e480c0c049454481c420b01203601e202140c0413007049150b00400540c942040030890400070380d074002204990140d410000390308203001d0604034290300d1030340c0e03030041e1220442d10908011107440c240002941001004882450301c1d180a4403c640105031044521501c1c0c189406181400000307048001c22202418061640c07400e40c5001714820084445c7c104180004081d192102c49521862380014402c100c01c01483d806078014210f206002000d40350800e02140b01c1d9001c4d100c00c07000440c0041c001e101000b0800d5088201c0c250401c4100400300120714010810040240c020400070713100d034003450b04181405090303203161082c269001460301c1c09112a0405104c20b0b070000d002d415900d010710385002c00c400c0e1281c800d90f0312943c070080044c54240d00d401880c0704082d0805000b990441f0503010304c42e0b400e201c1000b000005006089002800c5403428299100304034200d9400307402c100080101312400343d8000340c5000e095 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 729160440 1250 729159190 729159199
    0x537020d030c020d06020d0504020a0603021206040c0c0803040510200307050906190903060b0f030712051204140a090612030305060f180a0b0f0102070b0307050f03010b1c020414 78
    0xa0b1090002030702040030200000d03c0345000045040c42420182c0016009901c00d8421003421900c652042d0b080e802000b00d8030042840440019079280781c16003010010b4440f60411049a0f9181c2c1c840401c15807049500340c51a40c480c58403503078840d20903c55144070500c40710160030303100b0740021840368a100141403e400c021010810700100e0f17444008541e624440d402d0b140e42d110110380c0c00034040112920060f80c44618003140c0b5011800c03d07103209400c04800130094030200f802c2c0200b510b81c82000010582d2103100b400b0702c0003007044144005002a140c0350440725042c030028401c0005401d12500255155410321008001000f00300d4841102c455050401141c141d4414020481c4814221000c9038490f0380c4401e480120901c8891060243d50600b07402d000000521003800030307a803820f0b41c2d003032b005030710001007006500710400107150050001d140c41850450464000280d9400a801c0902c0e80303080000c03085252480040d00b0000c2c0c0c00d4000c01075013858a028049420300c0b081d9050701d03005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 729161690 1250 729160440 729160457
    0x60203060f0f03100c05270103151a03090f010212150a0b090906180c040f0e010b0301060503090102040306090308160807120e030708030f0619080606010e0d0537020d03 74
    0x21107002d802503d880000060207210746881104180c0c1c000d0640b6401103000c45c0c9820b142b110f101e20308120031420703105007260440484903140e0780c2204992000300100100e0080000020038078400303000800702c0b0000c01810384007500300955400c58074507500811324802e8079000020880e82d2160300a6441c069002c07100700305079981d07041c00301d000023089480625103807180c1010081003c0385180a08240c1e110144e5010119860707000401c5003c4d001c0c003e00402030b90600040007030a10490046500075040800582010340da603880d6000e540719080d088011403515420040c0440964104151441d0145040021740c142140d004c0c0240c4403212044900c01d407030f419000000c0a080040311045640720706541e40c0e0749000d6200c083c01c0c2a040d41d4a511551075903046c6a10345035607070805010390301040301814054450000640360758621508258000411211420104e682400502044400003000008008481b041010002c101d140304140c0c04840c09044800340e25542060043c040c3c0c5802d00000d03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 729162940 1250 729161690 729161711
    0x203060a1d0123030f100e010b06040e04080f0705062203080106050922090516030c060c210305040210021203040b1f030f03080703050c03042d060203060f0f0310 71
    0x543d5076049180f503014411502c501180280001380000488850fa100300720594100e0031003802d80305282642980aa8140b10500000c0c010504860300113124051140c070300103040c00c0c20340d4039801020003034400e50815002c101a0342035884282c503010100409198030042c0aa502508004041c000c04040140c081a0600c1070740b5000b1090904a5049000480350500c0342c6058000c1c00d041e010880b81d5009010948039841d1000b04100c00344c0381c3c41a183c2c81814204002190116545601503400d2512a01035181540d032642c440001800e0303954010030203142a0050200e0604003032030800031940030038000e9501061201c00d0b69081980500021001e40302c5201c10300c954048000f0020000004940000420850031840c41081c0d200361129825643e6407002582141e80c120b5075104070500c100300080024400c201b0074050718880e0b44003080d40c0400a8172024412020000464004d40c0c00828009185402d0301c0a0820703500441c1e020718810140d41c080b9403600e880d410311001560311040c0030203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 729164190 1250 729162940 729162989
    0x608090319270f0e19150b160204060f0f09021605010c020d02010e03030708160c0b010611100522050a050604060204061b02030c190b0403060203060a1d01 68
    0x200c0c40c180e207500c2d0341c620009002c4a000c0c07010070380c03003065507000030418001205202541690721131085034900d40800c02c0080700c0790014009602014002010300e45000c02c2c10f403000c602606400100100001d040741030351040c801141c285410004130b010040c4010003059951944440c00d980b102640961190440c00c005449041c3d00791008046500700700c80c400740039a00045030070041450354000c2c84803950402200703440784010b443c0500040d00007000117aa010416400400348902c81c5010701200d10701d0348618640c280203803c21400205c4080d0400350b030000420954003a030303088803000c2000d0f00b003d0943c2c02000e0a8401030301c80d802450b482200512000b403114480301c50f0040140e800078a40340c0340640081d40140038120200d2051503018100f01003040c0d10044080d4058020a002480300081000905010010030301c4030a105074003040d0480348501800045104031300258403800d0182c1085200c45240d008001154135035101a03143e0780b90006198110380c81c2001d242c102e588000c2c0d100703 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 729165440 1250 729164190 729164207
    0x120d02040801052d070e301c110c01230f070b0f13260c010b011b150515030a0515060d08030406020904061d010f0608090319 55
    0x390079441c220801912682108600f11082c1c4c081040342e081d0600d03400840c252000541d49180094480d44000000d0708061883c012030300c2c51b0380c0715030324511140417400b011200302100303558442d04204c5154880300b0806032000306071350981c100740040311381c0c00120390f5aa256111101d41007103400b4000e002c414a1441e50113005514240c0038999440ca010040c0840c0d038403003182200c80c00c0c01480001e40080c80c20310214040c010200314200c8400680d01c40611504000ca0b005010929040024040389501401000060314000011420000100016020080503250f81030741000d48403140d07001030801c60300c13400d0301804e0400009807521000c0701c1c0f880041300e00b034400360117104100e035210901800203204480c621001840b03100541e641d03024400740348028030700205009c0041c00820009402600600703200700011b80700081281d550245d1100b00c2462146040c020700e070030401400905040031801c40540141d0070b083c0c3c42402c02c1243d4036500e1052038283d030707507003c1c20b044030b07680e4035104000b803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 729166690 1250 729165440 729165449
    0x203180406050303030109020301030201080c0702100e12010e06040b09060c04060c0302010209041a10020d351e060a060f0809010f0501080c13090f0237080d020c03120d0204 76
    0x440e03881e981c40c0c1c10007d0082d0310a020070780c081100300c80001d035000140703011540b03403a60181c07484403035014622090310b920000c0d0181542c010404d9100a15841c0300744030f10a145454040208040d09060031b002c0020f0b1030207880301d4000d0b00072000b00a5007070a141e08403001c441d020300d40f030014020b0030f0404038021701a07188410750290034102c400084c920480c2d4284500e0704100e0f0426000440340c84c0c00d0340c1e549072100002e401700b003611144038210f000c640980e100e122440c0c40d001d807591140c425035082d09001142c00d04009001907990300d00c115800c041155000c0c905a07020060a402c00002508617099104400c04219031000021403941080d000a5510101d0050520095071100d00e019120b8500940e480d008004110509902e03083e140203600626400c01c0a03a032030070105d23400340286030442004084650644079054080010012070003419004024000307840141001d0f415070a03d10307607009036001c40d070101650038201d030f0b00426021031168100a901d55200119103045019014540c0b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 729167940 1250 729166690 729166693
    0x2010906021c1b09170703080c150109060e011a0d0f021e04030b1b0c0a0804090605030d120209040605190305210405060a0e062b0c02031804060503 65
    0x305694002011494005a412590000e00101c1403040404102c5640303000ca050010751604070170481c2100401405031402042c0041e036040e6030300d80c1c407000f24030342c440c401c0c80c3c56a034043d1140900c80a0a10f45190250a00b0082031001c0c914000e800100c03000c042c0202c0000301980005602e03100c041c0d03421034001c208010400d1044901d107541840080d00000b07100141c5902c450300003001c800c8000102c8060f80c0e4024682e6055440b1704011149550511699415046023009240a010002c0141c00c50041c844c000d00f580c0d803030034503030380f002921941d034001406a4080c0441580c419003200b403100400058000040e180c0d02420009005408030340e0019400c00c401c42e00c00a1454a1030418105481c052011510315007000800b00307107070343c1e1522120191400305000a2100d85844402400c0e0740c042440c20300300204414001902691004900c1101c0c28414615107051b8180c1803964051441e4089040240402c5001c01035104e01c14078018014403461201c1c14440c954665200b0005444040c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 729169190 1250 729167940 729167947
    0xf080c0103111b06010501110d0212130810020301140d020d140106053a1a0402010201060f080a031e020a02090c0706060b03071211040605070f06050709031a04050a030c030201090602 80
    0x3c1072640c0b0362100f802400c1c0081c401146421510707400062412490702c00d41c0c0207124508458040510b40e0b000306804210103807502000144990b02040350303542200d1300b5a00180d030f81d40b500c14074011021003519250301a500843c3c03140b0240e9501101100c4d4a60005040c0401c00a890001d41c01400a500082c5d40304059008448003004100421200e98010100e250004507005920402c0340c408440021710080e5003c0c0300440391034901c0480d541051043c0004a01c0c1605c98800c18081407190300180600c0e804030404101b4154006454240c400c41c42d0b80220561440d590000d444941d2510041d025070f0101c00441c038500d9400c012500d2150300401d04000a540300e42c140b9660f98815500e0b003002442c0a0b882c40c513450441d210b40d81d0200c1045014500c0d1615080c01500c4035040807200b641d000c0c2604490101068090180c64496411641c80c404820304614000d0307105000c1c2e04013440460001d804000000c0c00000d10744007070303030707010305011090b1540c61508902400084200400c102d0010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 729170440 1250 729169190 729169237
    0x340b130c0305071502010608070b040303050c01060b34150207020f0301021809100b0a030e0a0c0b04150801030512032728051b030a140a03090f080c010311 68
    0xc0084c4452520154005e00502d6074603082d00e5903858190084d485503080070042000024060801058001300c2e120000c2492991108122800d03002a8000304155049a81c220307842445100686921000ba50380142455600e44030348803181000d01400d00c100d5800200c0f40c06650f282c0010702541040140255902c0d582c580d2105a400c0008555901400d22040402c05c080b522a0b16041642c0c090052641460807506048001c4c0012041c0ca1085001d40c180c1e0304041110030341108040d01400c102940d80301d140501140a641082c0d64000802c20404014000a94040b4041118150061107952641c65000500c82040d220801d401e0807403070920100f88103441d010440d0a0200481e003640360581c0e1510241a0200850040041a98000c00304c040c2800d5000740e94601d1010028046400d61f0005540d01b00d09044101011074896010005050416078090360340000b03008021010420189800c0e492940c0d16455014503040c5900c9215500890304188161994100d05031862030041000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 729171690 1250 729170440 729170459
    0x702011412180a06060b0d0506010504031205090a050d1b08010207021309111f1205040503090d03050f0a0203090306070203070c0b0901030207060f020a1202091e060f340b130c030507 80
    0x1f0084803030003130b400c01c000146151301030026642125004107074490340d2402c000301107415a10125001c0e82c01180410701064603242c144140900d54840c2e030380003440d100795224600301140140e0051515a00402c1401c006842d100c400c040704a021250106480e403851801e4000502040841c17604245883d00c0c841a12291101043c04c0c6000340d111000f80e0881202403106480c2c080360050200d0f8800c00110103641468058103414501901d00182002c0000c80080c045a11001191005a00c040740203142c17440e00740110381e08611540011441c00542ea9655541e458492003012007890707000c1943d40007a406901110801a40304500308103c002070174148009400c0303600c481001416000045100500c14821a1403080b4000d00c0c3d240724250a50b02d000e0039074400c040242c0c00000c04d02c905511000404090005a04014011381e1001c0b0f140000c0780313400d03001400c1600c000312481011030201d10f40074111a001150458094445481814030307181c0300084e0b510013043c0f4882d4502c0058101c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 729172940 1250 729171690 729171697
    0x170d11070b010807050105071103010e0d020106051f020a23120d0510081c0201020d060e06030d03050709060c21030b0a1719031106010b0702011412180a06060b 70
    0x490745512403030366212000c00d0b80d40c4078103004250204104209000100b03c0e120740d1007014000050011400c208040d201034100001c5600410160391100000c1c86039243c202101c05080105d031017010b000d0b111142000b5514840b14001404011440101500e118011140c882c42503503401c0880d200e40700c00840e980c080c0e80c0501c0c80c0b40b01107494400410070b100740300b8840d241203d03064801405400c10550b07035419595880382c00882999402c01105103000360902500d40200514400725400303240243c24103081c00090300494042610700b40800154941242e03060084d12582d1610030207640342071400e00c00f015403131070441c0c0e0340703001109502000315450782200d4181102500c08182d042e503600c44410100c91045c640d0561a01b158011081c400001c2d6400c00d83c0380d01900c1d1261000740028080c605203c1d081c0c1018800c038038006107134420b558002420f80001440c81282c3d6140010740c8030000b03e81180a01290060480310004100c100d50400c88000c5660708500204503542d62540821207550 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 729174190 1250 729172940 729172943
    0xf07060207030b0603010c0e0f040b091602010b010f051207050d02120601090f060804060528050402090c03130b061f0203030907050a06050708071a15040e06090a170d1107 75
    0x403c400c0003031458201030155244507004c03130b2620382604891004100007021010740d425081a984d482c21809a51058207403401103140c2031460b0415407185200a09480c944c0700c580381800101c842c6140f00303560080440d0800c004c1400342d003440d0340b52620304884500c1404140200b042c00458204d500c10017025016001d074600342c03154200d641d40e4611691606105108900c04202d8500006020580e030343c000c258020440401c0420300000c0c1594031000000030954107110955503410401181000c0304603d03000000d0312005821032904502003842001c010701c2c010810000040404d0107612500b1000407464610b001e45d100c0800d00980080d44e07031b00b007101c03048404c3c4140e0310f00040300e04088012000381ca25941d2003500d4180240c0352810305600111007240d03000d61000802e80c2401c42460341c01d00494200314201c56074483c403002c110541c2c50803540d584540d0441c3c000c2c040c2c281c000003024520140c5c4070310042d100071200c800d0f002590080110340ea06030341c140740329807510061490060014a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 729175440 1250 729174190 729174203
    0xd08031501080105030304062012030106030513080313110424050d1110140a05030a1b0206010510020f1603020109090b031b03011e1a01020303130b0403020f0706020703 74
    0x669803400111030030303442807140a405400030002400598412146040340d00280b00300c043c082c00500c0701301458a8143e801d00749400c880400148001540b6026881d00802003040050410788540c452520305e120103403040c03100d00b03031b180020000c00c072041400c00e00510005008011039098101e01d506c03074070989140c00a401d01c00110205041c41c0019034490000d400042d802c00c1c2a13101000e021520b10140040740c00c1c0044004980800d04410005103010760180d6112512410602481030617900001c0581340c00b0f41c030312500340e2201640000c2140c1140c504648010041c0b41d00c0d401641003082c12804100540200b100c80300c80c040d0179000e0501103903c02c0e42c46600b11592030801c2c1c021600c545140980c0741d00314104014000664107100410000c0080c00050303050030601e00300701401d0111111300500e81c0c403050040303400c0c4002d22500c4000c1c1420b0019500c0c0d40b4180b10303960110740b81510018a40c1c07035110045400c0c180f0030410308540c400030f502100c902c0398858030003a586e03203414801100c01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 729176690 1250 729175440 729175471
    0xa02100e0607030c0315050f03030403170a0e0d030c06020327030405120d09030308280b0411070312020c0a0c17060a090b0f1b040303030b030d080f010b0a0309020d0803 74
    0x2131403003842010300810790040101105401d2104101050300c94240c0243d05200134880440801c0c04000c2181c0301ca81403907000759680400c410058034540480002c60700c10948006c0441c0481c0c3c0040310140400d038454801a40d1f5a1031403440007190701a81411a15002d032402200f225010000003001a80c00031504200c0549501d0f0702540d5480b8242c0041001803842c030410070000b40540d007034907081920300c01c2c00300a26020003150604500007940004a01d51200e0350011641040d115204004240d201002c4c070340840c0740c0300a8101220515800d1900398002030b65915540148850061743e03902180502c0c6c400e40d100303101e05400c660055815480d005480100d010351546200342c4403041e5100100040540e02c094452a81c1c00009142d05c00d03140400740d100c01c003141485c000740041c6200e92070000302100810103040c41c0c420304001040500c0900750501c03840505402d00740c1e0440711110411940e8220340038089000d80800c40000b5003000241020004104400c0091071081015440103a04d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 729177940 1250 729176690 729176711
    0xc05070902030603070e040501140a090c09020f0901110f06130c0504050615030603070e0702030c060f2809020d0b010e0f04240902030a0c2d09020a02100e060703 71
    0x102c0c841600c14983c0f5030300010b420040c254040c8541a4440d02840c000100084e248000e0b1140b8036040701c4100c0e006035626244010426040c1d08032002d0220340c0350440c202202800913a6052060803d40c9050011101c445025410100900c0c51340c02c4c0c0480c25110b0500341110410600c00032450100e810010a4002140600342442150300c50030000709050300000d242040720000ba4005010301d909406180004035080309550075417400b40141c3e500940e40c800c0045169414050050401c1450304070203801d001040104180a400060300714903c1c882c00d510b003025920041054100094003e03034200d00b51000d0000b00d6036198103c8103034044034812580c4145d00c641b01c111046400400c003000b030030300c5140b0f148101c0004030782c0c0f00c041e0000094004620780020746803003046c0c00c0803100e6690301a0300f445601d0116401c40c0740c1107031801d83c0201c0404810402503100102e03005800c02c041c0e000c2035100c205442002140c02e549080d07001008501c031400301e065100c041c101c44070404030741440d41501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 729179190 1250 729177940 729177959
    0x230406200f1902130501060806272d0708010f0602030307080f1801020304060209010e12071e090e0a1101020c090105040f020c0f0102040515030108101508030a0c0507 73
    0x207046501c9030014014900c2a182c1c040c900c0340b041d20b030581c0c00014034a01644148000d100703103400703464640c4940d070740f0b850402e00b00000519500b0030001a64040c000b082c4031580d084149541108449501da00b449102d02e8014440404800d021111300f0340190a1003d0190000403183c180c50703031a42c4100c500c135258001a60341344016504030002074400c80025040081030101c0c0340d00003880120340041200109800e90030790b04123980680b041c944c00144281c15681107414002c1130b00c401d490b12044440411b603442c1e282c544510900b801c0c03424000940003144203041c0248041d01069130100b00b0f400c901082e040c0d070b603070500c141100d0346e1071a4028003060703600009041d002040010000310843c1c1c20034040c48040e000c406004a5016001e1000040c00c03441408441052200d24000688640c6001c042185000034072010259544c0108010310a40324040340b800c900c0c400440c0081400b803c104803d10008217664031281841c000400c285042e1075128218201c90340c0124110b41d0f038507449801e803e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 729180440 1250 729179190 729179203
    0x60c05120705030306010c140a11040f140c0c010f090807020108010b04080a03031808031e0609010506070f0c05031e1506010e1002030403061b030e010b060a23040620 73
    0x29250b5402400043d04647c4100d00070381c03002d44038444882c5c1800d4030003221803400886010460310f01c100381c11b5070303030b5542080d00c2110034112400d6010300c1a400455000404010090890141d8450010352070101e000250002c6500703401446003004220050b003440800e641158404a0021702c0d4107000040303800201040e14155028900900300904465405400a040c20300e8800c001c6e0940020041c04226001c000d1403041e0003d0029600c0510351110f000c84401c0010121ba02c91580c01005016503212442601d030459403040c0c6e20078822015003003032001d0b10016408164148102c044172207a1019003020010610f480504a17401082d400000c0321104004440d1580041c3c0114000420742c40d000c495103a4401603130054a00d066182d44070201580c041140000741030030000c0704852041d9041c880c02002a907030500070030090342079078005181d80c8a80400d0000700302c1c40030a8610004a10740039818010408140f050351250b0341c020107810121252500c1c80c1c025110101c600205130045001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 729181690 1250 729180440 729180443
    0x30a050a17061f03150f080d051905030a09200f09130303090c2c0105010516080903010e03070b01051002070609090203070e0409112b0b0402030109020a060c051207 72
    0x411110100c0c43c0101024605500580800d915078004010144107500c41030301904080190112142c04c0c81001c918080750b00c40e6000c20032504000344030100d884070300510030651040c6440c3ea81c0b40c964200610142060300000f60500d18a881d40129106095028a407144002e035025000314403071901f0010085070807074001c4440c3d1041e455400010b4801d5000403d62446001249940b40d1512080358982a10316a25240c00d009584e000001d1141c43c0c041a0040800346403103440c01c903156038025900c01038a1401402000e020800034031a40c2c0a40001045002d8030003203d854821034240b00005009c00c0c422240945001c0741214801c3c0e1000c81c076032066400945078050100c2c0b815440c0c200a500007050f420811455036816240350355540143c011190148400d044240c140c4001c004200ba00901000b25480034003003c1d80322074a803817a210251903081501401030f41eaa50001c00c2c054040365000a61203480300c0004a00300360890000015540a03000700d801d41b080d07943c5550024854202d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 729182940 1250 729181690 729181699
    0x2c01140613061d0601120c0c110111030f090a0b1e160b0c0c2b08060307030b010b03100501020607081302030f010c0201061406090f0d1103030a050a1706 67
    0x40850601d0188018400c122035000260702d42d452a074803040e1902c001c0158030300c500a90601c0610361703000081ca00c01c0c0b02e101d50200154402d84a003e010001441001401103209504500e0300c3e0f80a500201400d0210300241c80d503483c2149810185540701020203481442e03240008079103007440c007040d500c01d0004440d000e02201c11441c048405030704495289840081b40241c290000b80301400c0c680e00414112035495142d06800c1400c074180f00d0344010060f400740c014030b0650081010b80701c1c41d070102e41e941d0500c0b212a450717a00100341800740070341019148a10381000040c5206030301c001035109a0725044841e0400e0780302d800498a82e40152514030000d040b2001040c181821403400310700356071004007210b0f80041c00300d61a50035100440b519070050b035510401003000d5020500f84981c5090701722441858910312000190079140800c1245d402031610307440f424108004000d40c2844010000c080301c2e00d403550594000d142d54050118180084c1141c070303551070000b0b4021242e5000c1c020061 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 729184190 1250 729182940 729182981
    0x309010c02010804173903041a04080708150a020a080f220303051617280906050402180f0403031e09260a05031504020d2c01 55
    0x400446040b00c3c040d0094035219031400c0c8004050704600001e020b011806004841851051030541141c56410140824141c211880507180d0000110885003901c0001041046981000380741c41c0d01c0b402503810102c01849101030100300f8541c0052440f1140c035648250940c6a07803210b0008041e8010742c24000003055030803010a50880c250500360b0b0780800d41d20b40c0409042080900c1c0020141020015400300303980d2401e1046101c1010220484007206040075080391001c140c000000050003014040c140b5a4106c1e2120092201001c544500c10307019002d0003a4180c0c2e040c500300409095604034411100414800140050440f406115680c6c0d5110080c2c580d4440e20254003514800400e40071441821070f103c2c007240d13585d100e2085180c0c0260511201c400300055598400201f4100415000b0014045011001e0b40501103035070100781c0ca111196080300c00301c0840c020340641c81c1000541e03400d121807030386420751208844d9000da0342081c0304501000da00070b509088440c00c20030851180000f4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 729185440 1250 729184190 729184193
    0x1503024c11030a0f0e19140109050f0906030c060307050d0f0c0f0e0a0f080a11040203090a06150f090b0918032d040b1215010c02010c1a0c04030c080309010c 69
    0x844c819443c0c40303414106204140007803000540b4a0707000e15842c07017480746100400d2015009040048003604020308100c40b44074107020000c4d00c038564804003540b040e80901c00160b41354070180002c114600002d0300064032818025800740c60f603007040c01e00c110b005250071468811b9000900818420702c88940700c04c0351003101c0c92402c542c03440c400c02a00740c00442d242030003c0c900d04045541d0340202601d8001d00020125898240321002d09110294420307030052003480310004000c92108000381d4065800500c00b044507072032003c00c0c005540a112003d40d10100012401c441e50018001c28000702c030711074245d03914600086c5030788200c8080c003140c030b40c4140008007000203011120002c4910103041005601203004001e421076119810001800c90041041a030000c00c0c0d0705419000f040e00100d0340c90144070f07071000811590803001c01034100804024541305024011102149a403c61092407079030340b907d00c010b40e080c0e91003488110b952031304050000480c81d8020040d1810100160b648081c0c0e8080c9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 729186690 1250 729185440 729185447
    0xf15140606130506030901020c010f092a050d030c030216030308010902160501060311150c0c06070f050d0207150201091a071202070c03020406091503024c11030a 71
    0x148060200842d44041015603a010295106080ca000050782e100302d440e580f9400d4407004040103a409007807014034800904503103032a90448840c0d40524890340d103490072a5941d0034955010316000002288124145a48910501100382c080e800322008800303101402e44404060740304c040e00003420760005000507072468009020943d0147c210b443c0d00c220315100d4508540c01035008a9860f50258007150450604903454042d01004003101824120585c0089480c0c0710141e4070a8420b0500042e013004100c0d610300076514241c0c00504941e00042c00b0880690341307107042d0080d2040b054521030052030369481400f07001c0f1115803290203495001e00d03400c0c402000050260848080c403000524107c0d08243c9407018040c00c50080b05050b0103d4a14018003040702c8003508403540090512140004010345603581d00308036941600c80e8441d50051560450507003040302a82c1044100300981c1e043c0111300310140c050b410780f10320f04052008410040940b020035510207410707015003082c811800860302 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 729187940 1250 729186690 729186697
    0x10312080609042a1503050c0f0909101805060f0303340b0f0105010e0f400e100e06151f020307030f0e0102120304020f06070f15140606 60
    0x40c1180203a0a00103c2030100001c854603400c035030341c178000d01d44c1c0021400398075005098001d00e80400e02454250210605001c6114540400e402400352002041e040d90003030000c60010a0740c2880c00000302840b01140016042c1500c03902c0c802d228840201205190200403036140e00605d000320401c5c0b400649401001036040d9481c040e5441507203a542c00480c5500040d207124103000400e50710503605020024241c1801186040d01402e414603e0500c9500da14904014a50100345100103510108070085601a10310070740a640c00c0030009998443c0000360019005031600105582c0c400f4105130078402181c0001040ea281940614007080030507c04241c450440303280076000703400350300b00301c0c4080e22942d00007404540141e0000a18009155018441108504041c504142c01d2225040000e55440041804118985000010500319074035019011252000644203d4850815003824055100b03052000e0b1018004050358541c000712a06c100950340d17a10440015040d16001d0070b0050b540c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 729189190 1250 729187940 729187973
    0xe12031b0c06251b0924030b06030c040f0204090f0e03190201020d020a0e01020d02060702030f090d0b07080f0c120a0c050702030625140d0e07180501031208060904 72
    0x400840c40750300410310302650403216040c0c40c1130b5800d80342d15100141084458006009503d49500400004a584c03900c0d621402c82e904030260b07a0450b00e82d034001a08081809548941c081c3c5004030a94400c44e1035009401110400c180422022074a40005001e9800d1416010fa058104025280c14081001440b42030300c0d21a01c00141000041c60665049902080491380407481c40b8060074401e40c0d04110383c0c0316199a61002d4030f004e051200020399240a0107400103042407000c02e15606a40741c20031807107181500001041114100f82030702030300701c21003a25000511800c650000380031240b41811642032601c1c1c50042c64095455140d010003c0c11010300300c0c1d081040400c0005c0250350104002c500503d183c140c280c10080e05658008450782030020b091090100c00054000e50020100c191008001400404901d0030304d85c001150030902250444d0b603983c44441c0b1000b04400181e4081e6050368401c0c0f106908400d86c0410544162000304c0f10154004001d07400240080d1010140b40d2802 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 729190440 1250 729189190 729189247
    0x70812250609050a060632060c070b03010e1f140a0b190f090e1b070c060203090f04020415031d0a1506050d08190e12031b0c06 56
    0x300d405507929400d0300d0316842e05035001c0d03000100306401d01c0100c0c402c08005000d03038030107000c210000314541c01c06107114810200e0031580545000304951904011070b80085c10301c0703042d61421901c03000f4000c0160800e025882c054908080003070708500511201e00d1050b00307000c0d0343c0030f0020300c1c003c5c00d5103500540e801c00d83e41201d80384000003200b0714060084d00c8c0070158006002c2c426146000000c1c403003e0b8401e0102c040140e00d601c2007044402a405468000f0007402c0842c802c0c0c620500810f10324412000c000b4a1160049400151181d0100142c440350301c045039030704c2400c80d06a08000990081d03014000c0d0140d000503601c50020b00a41c000c2e18040180240e007940c3d07000c103020013814000308040c1616541810318420142800c140300b1500039100468403000703500c2c480d490b1407100f409407182030a41601880511ba14181c000c2e000c0c2030302900000c1c159514a03021501e0203407207401c04000055540b050840c121180034021400c103802640c05002e05052080d407080324115014194401da112 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 729191690 1250 729190440 729190507
    0x103020310110f0403121706210a020901030c03140106060f0302070215130302120105010f0614091509040e0d050d090602040b16120302070201050d020901170a0509070812 75
    0x9914020144c401180265009286140706010290962044d1400214407010301c0c0c04001c981c0d5284010169010701da20500e400d1014403401c45842c1c5080e10070082c2d030160461300000f0410056080c20000e5911541264045100a403c4942030316a640a080040b0765200c1c0405a82ca00c00c0e8090021980000d14031074004111014060966000312030b1030340583e40d00d0b80c050095043ca0702441e941c10342107074002c005640c58172a1f00c510450b0030f40100c000f003026003444802d160680d041540c2c1c06210041480450200c07881d05410280e018801090107035042001c404421600440d912117900e8454541510742016000300c08014844084215061903003480b02007242645d80c4046c100c0e07440d0381d402030201c03008e90f41005081300e0a035820b01c0080500400c140d20041c0d90080c140e07000b001c8240400361316002d01c000165060148680c6030030314074005074104200c41e10580c100901803034001d01620350300c2e41c6884c401c545500c1518000c040441c01007121a600d120300e4004034002c3c9140a6100b00c3c2e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 729192940 1250 729191690 729191707
    0x70c0b2d1c060f0602120403030e150309010906050f1303180e090102070302190507050103020d0605030a060b0f0a0b1b01060b0711010207060c021809031908010815010302031011 78
    0x1d01c00912007800340800d0340c03480c0c00d200c01c030001c01005002c1c2c0201d0000b0141c5142c0305203d00818815400010b00b0004002601196502c0d4901030700c203081c6601106681703a02d4030186c020300801101c0d0050300d80a05140104d40500181100e6900500c00d9000680400c03a90362010348040d40b00030402880100d01c0c080014103071a02022190060801e0800544c1d0307100c541c03c000f0701c2c01c403100170061054440d88280900007003002580320300311031082c24007588528000c0b0320307c4010404c0ea480b207a01740c0103002c0c0c00c104000d299070002c001500222088a205403001040c04101c034428052a800304008102c22031801807444003441e10303500700784000b24070750743c03214441c0070203070440c04040702c820124078601d00841d070701400041d01802075850050321980c00c0c1c2d000182d9500c41020424031070312800001ca00b414005204951800f407000c20590a200b00c0900014040f410912900c0b9035402180d4a109980d5013072584281220340007001804101c11040c0000010400c0e15404180402c04020400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 729194190 1250 729192940 729192967
    0x406030b0447060405010e0703050405010906020d09260a0e0303071217010602061b0a03062d080708120318061006030b2b0305041a070c0b2d 62
    0xca5840015480c424041180c03202c2460510000d02400e00c20b82c14240140941c59a40302c2c0756510140514021840c0d407500d0900f513005084160029040f10700000d00c00c642c15600c2d0b0022760509204070082401010060015a003882c0300b214540c035000381c20411000c019100b110b540f00c050030000d01307591400e107096036204c1c0c0d4141d036008880040341903505101d4544141a091500420b043c0c0007a003900e02c3d000750000711054425000f4400110302107400c080301482072b0f1050b400340c6a80207051100300441c5050302c2c200c140141c8051300c90114924003042441010451804642c041e0005107848075074450f011a840d00f008000241602e010902102c901c0000c100341405603502c001c90080040c104000201500c1d0a00c011600400a20352a261410301c80c01514508c40e140302c5000d00d6020b41d40c54202d5191040740d00c0700b01c4040358500200b0750255001c000300044d5105910741d5005036514001c4044a01496905901454070468609101d0003c03000d080803142c1502100c0d4a08844c2c4182d00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 729195440 1250 729194190 729194273
    0xf0b0405040303090b0705130312180e0a0e0a0b011403150412031802130c0e04060b040602010501082a0109080f070905060d0209011703040f08030d05060406030b04 72
    0x81e000613480c0d412800034032441e540426080451071416601d030414076030020314010321510000b49030303401c2c0325a0112180c0c89074000c00c43c8a4051024810f81540e54506c080c055801950a02540c0d8a001003a010852000440042d102e9001c050000f00c0d0b0f00e00300210403411081c45200381c06000b441d4400900d14039005649100c4c3d8421013000300e44268a0300020201d4400b07414803450081c0544803100540d89501302c042c1c00c121602000300d50380200c800102e0b40050100c042e950494100b00c0082041100c5502410646a840e1700030042c80e82c1c0c80c0609503640e10045d02c00b400510f0740e520580740c0f004612803508048041810602c0300c10303541c0d5403507528196030462100401d802c0500309100b00b9186004440c0c2004040340c1c48000840140c0008160f5407048c860700c1c85054802d540200c00314011301c1a203000740200d0000000217030355044a2038a80d880f00c0c0d050700c0c3d546d2619000800c4d031301e094403800041d2904a00d11416590300c0b41e50340700901c40701e901d0180380d01d00c1204204260303a0105001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 729196690 1250 729195440 729195443
    0x6040c0315020a02150a02071e1a0f0612070503014511040615080405011407050909100308030403112a040221090c03010e0d0804120c02030a23010902090a0f0b040504 73
    0x901d16070304540d0500c40c0108002601d900c0d8ac480144040c48a085049008950090000c0703500c581c0100010107458505049036110715055420041052181010058a803000488203c051044201c0c0d03c80f1a0100300001c0380203a0200460380c0c6e10501044103141102445a80508002411901c8003901298842c2c0c40303443e80005520841048200b10080c000c6c20301c000d04803804600941444000a81107010b1058414002c1214400194101f09031030b41c110001c64004403080e5407800c01d030400825109200040c0c003501d10601c4030708440d50084241c1d2066060101140151501c891020840694080080f80c00b8410344803a45500c101c10050106006010440041802001c80300c103060a503140300825407540d40006600c00b03031290b000040250b00a521080c411100e0136045020f0719240f22105002c1c1d01031003050a080c0800c02c120380b001e240e0708485407000c0408101c2c26025401e031051100004d41000b010303008600b8a148503000303894040c40c40280842d1003203000e4049011280304031030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 729197940 1250 729196690 729196733
    0x30516080d02041e080c220e06041208090705010c140d0e03010f020702180403020a06021305041a22180b07090509100e0a0e06040c0315020a02150a0207 67
    0x40c200081300d0050515001d030b005000007840440e24000590351110200c04503136015050035210015410941044444503210b040020445c5030300110740380ea43e55004580c12206202100e500500090090085078450b03c1000000c0c201075040000444d01920801d20071075401514a849100b0900300740814201d00d61203554100486441350105825600c10a04600d40359104209200268803138000307003500c243c5941000e42c00e136141c1c0d140032817604480c403c1c00b4005910119450781c56900a00c124000c40d030003203d003401000c41c540d10f00c1d500101c030300c1038040d48031414140142c0d0949026402580c0358800303010014014050207245200515a0342048600311541c81c20810745c5900400200b02500c0290741c4c003189468007603030340458100701d030180881e0525801d00080211085810003486059500c041c0c600d2801c2c60320340000071b2041404119100c1c4044144211129603600c01d503100030903280d00900516410b892540119000985142e00700c8d038007000301d18045004201241c0400c0640700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 729199190 1250 729197940 729197947
    0x21305120f072102040c09080d030e07050108090a1b3302070810050c07021309030815010e190f0303050a030c030207080d1a030d0f080c0c0a030516080d02 68
    0x740d5082c14401141c014860a1450298035004900384a10b41540e482d0305440020b400180e076a425520000f581d400001c031481000300705840c4a6054016840d114119822614015103070300040d03481000468905103580c3c0222a07042c04135000216618840e07040a0915036001e445500c40b100c20002288401004111804610780a00700148664200b02d202c1c40900040d81c1030001c25070311800c1c6009030b5504203840b4008110b580041c80100c1c1c0c070495004010420040409000402802ca5021f003500401c09043c0050b03850984015501401a4144d651780c01446c0882c08020b9207000d030703071031802d403465583d41c0c00701e01d21441d81c044801550280e01c5a03a216812400d00070181c0c0e510b16001c0003014014000140003a03d04026107000d00142680450320302840302d00c4469240c0c02001140c0d0612847e64100d5446da04000d40c415801d01503511a1040e94400c0d44030003903807094040b40c001c158003000ca417801207482000903112449400b400d02c0b01c2c00c00d054403080c4a80d0011041c03c1c05142c1e002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 729200440 1250 729199190 729199213
    0x130606080105310803070f09150e01030b0906060d020a020114090c1507020102100b1306150207050103060f052407061d1609020901050403020402040b090a05150d02130512 75
    0x503852a112208030000c54143ca801c10b40e0780c0821800040c02c1c2200b44006400d45180706801004104043c0481c90682540911854802000071007101246030201e440d0000412036401c142d9402c601c1104054100342c903003d00d032141c0034025404030412600b1956220384403c2001c220780e000901541c0310708000d0010311290780130410b4550794440b0007030910204110303104c01070b40c010035044071a020043c0005000186500460003281400002403842032400c0e501045074007101a40000c0910264219002192140015011100d00b806992210b101c019010042e40c5003402003413540021000c0041c04c940f40804585103281c0060700c04840694a829651000380b486041440426400314010404001030414040c070000042c0500a00160001004805c0741d01074411a002543d000e001196603a694081c101300607042001d0051040041c2c682c002003030325110145112080c1d591114038030b8944c2410310803000354480e03c18074044100384000010340d680d44200e90160446504080d05054500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 729201690 1250 729200440 729200491
    0x20a060f0207060507112a06070b16091d0a14100e0f06130e03091215010f0303020d08070e060706050910051005240a020f010e03030c03130606080105 66
    0x31700c05001c00c400e0b00e020f60001d90300010b6420300c0c111200c00e60281000e2000c581a041c1506071840c90708040c3c000355000400581c20000d074414078000165141607002b41200b140c2c0105188500a01c00c5071120134500302c031101d10815900b001c180000080c1c00f120035910003000410071138840d031810040e00402c1106502c5207070041d500c4408002c0c00003840c03412000081203018103030a28074507a541c3d69290040b0355810003ca4010041c02041c1c0030740c6d07110105507141d5405a26000d420b42c4a02040009082c00f50380748110141d07030781a0090407240503101c00c1200c2110000701f21600b0000340311600403054844000400141c1c0c0944004078040ca402c2c40c1c80e43c9008801804800c4482c6000200603040c45000b05980560788200c4000480b0000480305000c0b000b00d138103411071400340000b5204a02500000c4000f012038070703440240700282900724010703101d002c11503801422602c20000900c140e62841103404c1454031480000514549483c8054210742045400140b100222400910504c24 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 729202940 1250 729201690 729201701
    0x14010501060203031b09010c05030c010b041103060306220213050708070918091109090609070609150503060402120703021e0301030c1e080d090501030c030c0c12020a060f020706 78
    0x100360004501c0c2d41403170f01403102c002d0b6200104c10b81134113001c600103400740e106007ca01515a00882100e440395410282c243c020203406903114815841d1096034a8955030220940384501c0005000c0c00c00b540c0c42e540c18441c0700c08088440350010840e00b0380c01d80141c1d18422441e1180490520028152030652b50181111801030440c200344200f6260810051111240fa241c000c168420081580c030413a2034401c4252120354800340c2c2c402c001d0400c100d6040380001c0c00b00e12408032201107a0860783c2e02c1e40306030768102e101c0c011546005c03500c51030700006500550084d90070a001034001441c100c0c500040c0c0341620401c2d194030b40066000a400000310200c40301d200074070010f02e1462880d40d455941c95038a01000c0c0e200320070000046946030034011409408810003480c0240568884202c10034000344000c01764016180401c0c6060b031841700c185c2c0b0920400c03a8a1841d41c031030031001080c6072606114082014588011440341104443c0007407032500a410044442c41d10140e143c0c4554a092001e992 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 729204190 1250 729202940 729202949
    0xb07060606182102041b031b0207090504030c05010207031d03030406020c090619081c09262104080106060224040203190809241c140414010501 63
    0x241c018981003032002c440088800c6071050102405141495a860112228002c2c2d80603143c80218201c1e4404000e030720711614103541d030030844500308802031014803404600c0740e401070703001c1201404180c2d120340c400c5801c28001d040c49c44180b08140c1d0b500307099038806401207002500c2000f00041c03140785d850030343c201c2c04000c8001e10b040a084c100029038403d102004a0702c111050004030701240c03a149406180d19084084a1956a072103140c0c080e59070319845400c40d424000480d822104620074403079001610b8400c00000e1103810028002c01c40303440300301c0d0852614000d507030303000040701c0c0c0014000c1c0401c1d98204040d520383c1e14107500942151210752100d0255008000d002164889038840007542c10082d121078070080d202c500101b464400150401803510400d40c201009200d0020050842c207070080f9801442c1d062086e0300500c049021003141110b805050003951500c555540c001d00d907401e028000000d118072100e00070242501d054078140c8041140718030340c13803101400b80903003030260 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 729205440 1250 729204190 729204197
    0x51201021902060c07300203070524190b1207030510150510020a120c110307260a0204090f0b0a050709030f03050706060b03160c0807080a090f0b07060606 68
    0x4e10300050409164410420300402501a07a20a190900c204044441e981140c00607511203500305207802031741e240d10400c0305840d544140d0030081f4000400d00740c03100148001c0098001b031610f490407884802c252007a42c1c051840cac0c407100d564610361510301e800079026000d00010a0101e01d181859801c0ca862000042d4a103428483c038000100741c1d00540e1000c64500b540e40c0200748402040407800c003019120014a050b8000c150502407991180003030170410301600d00009001a05410591780c0c802a124200440380701c641401c1c002c588074010a8102c004200a84001e254560b00050032a1040d61040300d450402c1102c031400e01481d0400c0ca503000c00c2400081100f42003412000e0100c5d02c00e0b01c030081c0600c1a054070070003054414003c0d80e82d050391020003404199150003c1180344d4104480700010b40100f1158218464400c0ea0480003243c2c0044042d443c00d502504c0b00f00040d8001550700f42440b04031100080d00342c02040228008007000c140c001d8490020f4506441074500a03400365080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 729206690 1250 729205440 729205453
    0x7170f030306090606040305070f0f0801020a080f0c070c12060c02030a080c030414030a0c030e06090a0e04020316060309210206060d060f090503091906050403060213051201021902 79
    0x50000012280c102d1003c441004041e525800001e00768400c540000300303a40921f82d40002c103040780c041d0100580740c0002d54a51000c6d19800d00c50700701c1c0503120340c50b40081e4a04d404511060180a41e0603001805c002c50302d4a02401500c1c4d05000212030760107090b8005800002c5010300039070340304d6203400800d584080c0d0324203d40e40070010308544001e48001c61582000001c5010080b02c1c003800384c000b141000a607600d920f50b204024001030300602c030a901081c0c245807005420724010045401e00000100301c0064035040c00f140c91800640100200e802d48150101d211128100a020100410a0b550045809000b500e01003440f04401d600038664500c0300f07813401900030b0300829120303032082041c1c826010059031414400302900e5445c40091140c0c0c58400d241c418840003000a190307942c41039552051112400600c4101001c052103940f000401c240070902c006480d9400401810001c12009005030b40c9400c006507001b1448441949a69400510f05241081440781103c0742d0070b00f400134091 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 729207940 1250 729206690 729206713
    0x11060a051b1b060a180b07120c08061f02071e0504140709080c1521130311060108030f0a0e0310140a06050105031303110f031b0606010507020409030e0405090717 71
    0x140c0610707000052021515100003451f10344039880000c05c1c0c0c034982c0024042188001c002404002e4240c44a03401065005550301903169006502000d402d400d90040003000c0c80e0061041000d51140038604070700b5218000000c283d550b86c000c51410001c00c9003c162241006480601150000d60042449400c88800c0413410f65549813145001035040401c0c50f514044012907041503000826a0700170107500700305005032110030400c81941c1e244280c880d0009240c103103207000c0c4e88010921800007254000c0000c010502028000340c01050501c2c10050324401c55003001078100301502e026070416903a40c00c0c40c14071130309030350421135004100705a0400c4031a04000009001d848001c000c003959956400c5d00c01c007098412304107103411010003000d5403464004006041d0310795104403a00d040040c259034464552001c007040c12070250f001610762610b0084194240b00c084c0520310020b0302440b0a0300c00030520f0ba162030140900c103c5a00d006407143d541041441c11014800003070011095100606000c1e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 729209190 1250 729207940 729207971
    0x604090f1b051221030c0706060609140a080c0105071a010e0a1b020a03030e03040308041d090f07090c09080f0d0225030807020307080a0f1211060a051b1b060a 70
    0x21010138042d1103180d62030b9540d00e4140c0152040c0f9400a04140c50000001003c60340314060b0415241c0181106845082c0242000989807203030040c07940350303006150009401e40c0600020700c038281c482c3c24050031503001440007004800c000d074001803600b003095007080304118251040c1050800798800580e46860b0100000750b13201001c601c01818940d4803144c59240403820400c0c0d50003154041d8196560702c0c2c84054180308014805011018100c2a002107190381401140005409a282c4010002030f45030001d0031001d040c2e401220020301800d11000708502c4400e100d00702d2811b050400070400340301000b40003032900310f4602d072a03400c0d44881a0200f0030b890320034602c0d80131240c1084950740c858541d0300000e0300b0515590b00c4030f0301920444801c04200803064070003001103409401c401d484410000400d880302031482448202a41040001400400090340066000415002c141d10902400d00c0c0e1511a50310001d40c082d0440d25070451000c070041c081000e2503010103611700900ca2a112005090f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 729210440 1250 729209190 729209233
    0x117070603090b13050709090303150504020f0d1e060b0a08010e0601211506091a0a050702090a0b100c061b020a0b041b030b0f060102150604090f1b0512 67
    0x300304141303a0303020400c1030003c20028100a0181620704101c40106454040d0081c01c0c40d030b45001840c134880c04001030320310b032901c20303604030000c04081507260045941d000c100070142010905102d01d4211004440b8a29521481c07018200d4584a16a140404000504140c205a1100b00f0b01c0c900321042188a9a0158074600340041210102e008244c84801e04405400a10800c441510301e55038005402540000320788111134240260000c0540e80c92019030f064480e6841680104504111560050500340070b03141c1d10a50284001684544820014200568250072180090000008581413110358480c3c542c00801c50820701e0701c0180d4403140691100c404060150070f0f2007140780081c00703100303001c00090504100d44034202d42c030689a11b00849601400d40c0c0642c03440326800001240d40d4000980340e54090042915006079903540c80c10000980710000c42220441c0030300016130001420300313855450003a070820744c0200b403070300346018050000c0c0e54048074072540c0d01c40085061800404c090b007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 729211690 1250 729210440 729210451
    0x30f21140903030415020105160504060c020f0d0506280608060103060903170a1a1923060310051503130305030a02070807060b151206060a14030117070603090b 70
    0x2a40c8416000d0002030440c0955807040066209040c02e017825590706500c09417203103944080b4441c0c44030f01802c04980c41d001d640150804290403c078041c000d0310f094038400309a100b00a007403041e5800c241e40c45905100d01a07940d00e10814100310950303140d110301844503240c0d80744c030340c1c0c100800e502d0144a940c0e40c1906200150001c0d42d0341000c013042c1845100d0b003840054068a02042078100407170020b005002c1b003040c1022400d01e4003040c84c09454240ca006103072050701c00a43d030800d401c101009448482e0b000942c1e0322050074115407000358a03440060b41c4114608100203001c946810107018066038044004031900d1030800810140c150340d504c04a071115018500292260345544418000303105050340601800c00c00b040400821103d0781040c0040c51069502d991a505010201411805070030051901e4440b0840010701e58282000034003140031140c0740884168280070700880c1558001c2c3c2000b1203d04502050454007041040514002c141600e02045810410f440300554801c01801 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 729212940 1250 729211690 729211727
    0x306050d110607020d050a081234020102040f140f0402040803070b04020a0e0f25090603051e10060e031501051215071701050d0b07050304060e010501030f21 69
    0x50100a5454100b15060146d6201c0d0031200f0b40c912a061a948640159030b00c070b800b209541c00056000005440b900301c101290105000c11800207920201d4000e603040188801c41d07500344000a9801080d0010300002c1100e003545000e0300f0280b80911500f80e83d41d00c40c05004500401c401c0203801800001c13288a19040076554810351103510008990001903805140842900414840002400c155644c050041e030403100c401280000004201c05e0200c0030210003003107503003200300442400713a00710a0b03000360b84141c400440c010750310000038200c80c10b0b10360504400b0000c005102d5030f03070410718012403804100c0041181e51000613210401c080c0c14000c8034004c049031070901103624010480e82c08142548000baa9092074408001460856402001c020b006c003180700010f007505000014803116900100000455a11203406441a910113042120907030f58540c2d01c540040001c1c0708080c0078602c42e40c0c5030320b04501c4c50b007018070050418503515106444501200c842481c2c2090041031684003107003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 729214190 1250 729212940 729212947
    0x180b300142030213020403020907200703030516060e030309010b0109092c010f05160f0e0d170708070b060901060e3016080d2307080d0e010c0306050d1106 68
    0x1013044020340150f9000030340200b581340c113100c90f150700300700c40800400030182c0e00e1124480004820f550b400b554400035010031800c010200000c5c154011400c1d0090151300b010550700c489401c0249954811038007140240d541d101e0307184441d03034001030150040200705000e00c824045000404005410350002115482c0400c5016080030300c00c2d00318000c6840e0405040180e803034001041440142460451400a0100242c00307581e18043d19200c116128050406183e210041d035894903004880307002c0c6402800140490310028906000030810343c0d200c1c1c104020203081101c10720044eaa03041c0c11010a000380748840c0c0d41d107600d8140c1c08181c459011007400604c030481a03003d90720005110301c2c2000d80d0040300c1400d5103e04002665004403102d06048500024800d4000c49081050031a201e464030100b5001103107440101c0044c0000a0095503102c0c640f104c0e03e04400704450402c0380c1401c5594503a10800007a036018030841f402003400b070329451b01c00000c80e0b0300c00104402400d1030510442010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 729215440 1250 729214190 729214219
    0x1e0501120603050322060306030b040816020603010305070e0a020304030e22020c030c0f03070c090b010e06030405100c03150501031a1801180b3001420302 68
    0x54008100642c0c1080581741c1d207101011031441095901201200c0303003601c1000000302c49100703102c1d040c21241c004000c180252920703541d0003881d41c03044001d01416140e8299590160b41c400004500840c403480003800c0e21031420003140501a0002c00480360113205108000c007094000700d441c6110340d030480303002c100761020550400b003003d940d00000a8041c40410010440c076000402040308403032000807251135040075042603940c1d00c1070280060446e502281c00b0040f01c40e840c0c00c821030210050611020042c0346001169103504203d4003911303154490b9044d80c0341200c130761060407483d401500c1c0070300084007482d05000b00c44089210b00340c100b680d1000d40350710a680010703042101c0e0400405032200c503200c4131404400600b0a015018096501c5018448082c8161240040d400c1000c0d043e061040e10940403120415800a00ba000a0700c82c00c1d03032060854420300c20655030080fa01d141320080c0b019102000000036203080902d440c00305440050300c5030141c200390707201102c0e17042312400c120761800e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 729216690 1250 729215440 729215477
    0x50a03060507030e1c0e0a03030c140a020907091e230a0503030f1905040e0c0714010905071401090e010e13080c030904180215031807030c08071e0501 66
    0x1064500c1c1c0c0034042c0d600c0c10105421545d0450442020079540c0b03246070000b1008000300c9020a11004000c0b5546600801c000340c2c0d00684001860861825240001030396001f044200c88122120b85c0014000d5401340110b049542480055984c4240400070031424448030b4201e40301080600810380c0340c04980281c26542c0c0603440000380070058180d0780c45444804400303000782c10044080706030402c050824050b944c401c005407811241c3c4040034241c90744981c11001801c0d031180c2e03400d540c2e000da074541d036400c00383c3c3c24051400c030307188194010048a45022852100760500100c501d040100e050710421580c14102815810340b1080c140d0100ca03903c46585440303042107441070003000c40201080c1000c00c4030010003d0500720100342ca05200740d42503001c171088800b8984038025400741a43c2c02d9410804a614051644150040040784590122000107403800c0c210794000c4604005221007802100d005008840c002c00000000d8220404000c4002c01c05c60810300036103041012071030120320034030328 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 729217940 1250 729216690 729216701
    0x90b060603060f13140105060a120908220603050a020f0316020a1209050310181205040f0f03050c011e050d110a08060a05011407020d14150a06090501050a0306050703 73
    0x4e003804000ba03801d084150181c503110182c04108081e00c2c00000341350a01504881d4207036403950701c04800c072124012180007401000d8080d9640e9006009401c4820f1411110340385d80c909655044181a15000004050301e00042c01030101600600c0884098500c40702640c3c2c03c0528001c1030312014410000403403801c3e182e01d001401400108030f100c140c2540006130b02c010b4500980c280d60b8040503d00304070040d2900703002021861404441d80c0d0011801100411500311160302d4071500e0540d0b508a4002208101c3e0080320310510f089104104000c0100701040c0f01e05001e080061544c1c0c0c01d64040d40071020000c0504c018000002105846a60380380e02510301c10214000362901c03214800d2004000e0902120551f00490003aa8041a151300404c4160b81e00d12064100380e1a083c07503030f0300744020302c091068202e070015071034030403107800c200309001680d043c4e50400c000c44900d18085800f1810340340c0301c2e0f02a0700030900e005c00511a6440d0418680c0c05e0b2504404080f400c2e858a0004400130078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 729219190 1250 729217940 729217969
    0x12061e0212071e051b1e070806060d02090105100c38040506060105090102010b15090108150109261b0301060801060f090e07080601060819090b06060306 67
    0x10300c0051604044101c0c1128240200d04940d41c0707150380c0b010b4001e40034819500d041c0180c04904140a1880c1001e180d41501c0d112070002d03415104801061101c000000007041210303616074006210510043d030b401c0140130f40c030079011034410288914139004135000403418000c01d802000b00811004500b03010301900d02d41e0f1071b0b0003455081c0d0150344009981c1c05130f110030819802400c0b80121143d41d4040742440e1401260080040c180d503403107840054503d5070000d4007140c10f554840955807840d5850080c840613601c4550300c0d4980c0c03100810001010180010100000c140b050201c0d540c460b43e001c0035407400c2c0e030125040c00020b01c42087c40341d0b08010b848120003985110300f00031125140f0301d00340c0c0c111501d1405c0c2c0080c4580d42e00d606c0a942a241c00e4094100020500c800410041040e034000b9140e107144c2006484652703840b50321345801c2c544260819030110f04613005102030180c10740030f10301d51074510440801c1160840d5446402c1500090433007807084a01001082c41c0359581d407488007960 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 729220440 1250 729219190 729219251
    0x3051e030a020a03050c0a270801050109200408060f04061d01090308060d03170c040b0c0309180112020904140a150f050910090501140106030b040b06041206 69
    0x249040d10781040698401d40d140742c00282050080b485600c107040c04d407201d03a21103440c0c0c4c043d1035074210700c4802001d4507800062103546114000240c01902817185038003912421b40d0215001c2407009940c42040721307409500c4822502080100072090000c07401a40000803800840d81c035403103a05004010f0320b280c00401c446814015500b607003042e015880307400d00381d1203500c507070301381e55244000c2204400d1580170140228800920585128980c95091940039a00d41388450074261075068800c0107030400041c8038110b41c00041c90404900c0d086440c540b400e0306002c482c100ea5810b0030910364a02c0c241c410001d0143c045900890200003500b5110f0403518440070480e071706080941403c024840d400000c000c0340e50302d030134407040e203001c0240135030380c41241c03030b103000349614040c4c00c40c580010005000d06030303100d540c0d8040110025980441c203500a080c039550204251030b801c82000122080c40482902c5090b0410007085407034102c1401141c0300b50820000160b88003c0c0075400c0102445c102c011512 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 729221690 1250 729220440 729220447
    0x702060a050315011b02040504140708062a0d0e01090204020d0c0e04110324040c080414011401050111030c06010b071407051318020a06020d020114040c0303051e 71
    0x1400d5000024600c10840c04079880c480503100d4006541201c00c403c510740c41da442c02550702000d803c2541015802c64401c0c0f04500d000312b46501802d0070100c850700305a102e82c000c10f040c025401c02c40302d04101600784075204101042c2820021160300e05c544111420340940740d0000000184d400e5001d8060280c0190040d0765808003420ba400082c400d40310220b001c24690100c48a081c00e081c418004001588040c907441c546401c0c0c00400540401e022018103007160441600c0141c0750350117084405007e03911800c449081514041020041d680355001d203503803420042050840c00d0071201411030701c007820300f88000464000103a0851095200d1048035108410000480c140160020403440e401155414008004244d1081d22842244142603001a03040040d40280c4c1d20399015030300e06250090102c0f4038800c00d03408a50300d0041c0c1d038455070250f0001032136150841e1b021b02840f4600403001e860100b641c9056a50075a02c16110b0001404005000c02c542c0241e48500220302c1107d911810440d46 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 729222940 1250 729221690 729221707
    0xc0304091a1002030c0d0309020a0504150b0a0e120a11060c03040305150402030111040b030a0216200103150e13170706020a0207060e06090d060209040f0b12030c150c070206 76
    0x10740380d010040c4c0441c40c0c451806d0f0a000e840c440d10070008025402010028400d01d89406c10014014000002000301d402d00e5000403d011000c0080035401159283c2280c0c038203055082003903003851855510025005480d018000403101c41d003139031112408031402d503100c1c03a0a10790320b40303580226080203042d880341d40f0301c0100d40b09440294500c01c510890080c00720511030650001640110310680018400c140081418400c0035006002910340e0609107040c0c0c3c0100c3d807950f0107a8003060b000480e511444103c00540c650b410b00a00d940040b0010443d45002c0c50070100c481445001882200c1034a0307200801c0d010040c82001c041020102d080005441d6000f41c10141c000794010708901c40541300b1201b000a58a014000d44d103007154006103050b00b043c080209100030000e84442c2100d003103608100f000c01d42c1d07a0301d03c81c0000121011900052234650300007440541e40341803a40010030b42c01409003007681240054440080201602c41c520b03991640f000c8641140110f840003580024080b84020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 729224190 1250 729222940 729222943
    0x201020c100615050a080705160807080d0609020a05181201050c1207080708061003090204020a0905030f0604021018080304150f090807060f020a14030703140c0304091a1002 76
    0x140d0b82c031407688100c50b000f45007040c0e406100f4003c0140c0441d03412400500384600035005803050004e9558100d00010090b680e00c0c51070b610407981120f00c1000450a03410b54585485080064030b02001d0461420b0801d220141490241503c41031610b941e06900660544540c0c0f10ba82d03905110700028040341c202800c403a50990441c901c0d08034036140450020380c295208480e0795000701c01d1074480c4413581d1207000c02e1006c4010031250312418503880c2c00c4d10304010789640c07005011101450351461311050410007010704200e950782e010456075021900380300c0940d42d009040301e400c86a41c2414032207505007002406a2442d194081d00643c0008100000d071071841d800b1900c250041c82e642c8508180c94610159002501ca0190f50340541c00031201340041d50003001281031141082c011a80d01d26540d030f4038048420b03034580102d01c864001194000406400200310302524621204503400c102d071692115031759000301d20034a00403c0c0c49003c10f40c0c0f01507010160040092000d0300704440790f0090b40019 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 729225440 1250 729224190 729224201
    0x103060207120206040b01170f1b100806060d0b031e0102070210181a04050301060f0e070203041d060a03120c11010c020307030b090313080d0e0a05030604060c0201020c10 75
    0x241c07484402c0c1d03416900094800301d0100d1240e90b1180c01400181d00b4000000c20800d41d0852070b05503403141c55500140000104202040455000407448400c0c00400600902c850142c1c078803410b0003405411b010841e540c000c260703850b124441500050300400400041d14101445c081c1440045101868071000e00042d0010700e42c09000b610040501098068101c5555445011030840059480300500140f001c00d07469003603210000164500302920b410009003160041c3e0300468003104030007020803011190000140e4486a10b00142d41881d00d031000240d2012a9240034480010b084030015000c0e0342c6001441016540200e001003868001c41e402601981042205803a43e2840c2000c04500398800d01100d41c0096002e4003600c0b41605c0c59456242ea210003400300403080c0000c0c0158070080700340e444400004d02e150030003802298803240001d00030124105032030f800340c06200701c1440161030000701d141d0410b902880004009402070400c07070083c0a20000900b60340540380401ca000c07809034129 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 729226690 1250 729225440 729225443
    0x2109010504031e0605180a0611041d040605070203040e400c0e060f01080402040b060a02210313020d050c040516110d17090f12031801060503030d20030103060207 71
    0x1c02003a106d00800d039640c1e40078104220311950108401a002400c3d40e00017508036500c4c1600b1741d081030380328001400003803408100448801d040720200401d0048901500c0e820410b035001440c900350070701a0b4a0720842c802001c002d007522941c0d40d0341f2541808080c1c00160803003e08019003c00103203808000040116003010f071119a180b560118017242c0c003504842c01108010b140040d00d100c48001510301e41c80091090b40d00560b6005868803503110000100a110b0b090ba01a009158502c000d42040c03407140c2c03d541e10b44010900410140040c680c450300382c46901210301d01250001ca01d1704070310744160340e180346401c54201010310002e442c07401303519a002551503d2741042d544070f403071304030703a80701c48510007800007480109000f092160031000c141d4110007140140c0d4113134007420400c02d02d050f0301c0139822804014000304000c20f2441d0b010b50054080c840c1c000a200031031810740000e54038021404d04082150392000004480a201300009070140c2c0010403c5440e50703501d0a00c04000c0d0041c040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 729227940 1250 729226690 729226703
    0x317100302040b0a08030a11030c1507081303050f0705161e210f082b050c12360c0411070c060f141801020f2109010504031e 55
    0x54200b5070300e0441d8003030068130a45401107051a84103203040312008e000c00040341960004100a48424a041c07140c0d10300e80c201140c1c40140307403c107850010424000101581c440c404010b50110000b039122080b40c01d44c5990540003500c030891420a94145070342e046083e801003a1140e8006600c0c4400743c4403000344900340005800305a984e0b04810314400fa0282c3d0030461040701302c0041e0008003081101c0c1c242501410703116060405018030403020040d440421141c080015161864400707640c02004ea10001c600401d0b410184c2601642038050005000c80c00302800e486086104803440c00854006000b20940c01142800d08600064a40d401c980304a4003d40c14074100310a00d10002007103c0e0132552000d07227003451a180080845401540032410820030901d00441d100030051080506040d805584a410400c01c0c0741001919155212031070700c107039401c408040a10f520b01490b502031f00c1c0c0c003115070055407403000d0b10040303900d8465a007004043d114180c0000826404980124100912075071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 729229190 1250 729227940 729227951
    0x40b01080127030e06182d12010e070b0304060c020a0224040f030b06040f1b030932010b0a03080d0f061a090f0a080a0f031710030204 59
    0x40e421826100c059000d003440d01c40c1ca80708070100014940584207110b002c0d240c1030300300020410008125501c4045556807509034682010b0315881d001c400c6004880d00354103d401e0008101c01c40811540c02401c0385440f03040c42c60403803020f002080d00000945410001696482c2e515140c500019400548059886a1074640c0b0702030ac2c1c50000804c00c2541e9002003c05180001c50000d0f5420b030b007030416141c00a501c003404000740244006000c0c030051f41c8150b0b4802d041d032605600340011581503801c070766880d40c1455441d0081d074008881d2409100150318000c514405a0b0500001c00c07409442c01c014017400304035240f411100403130340c0d840020051000a0080400c05410019942c201d0302015148280802084a4090325984a48148549000040303082031f91070326a030b000640c40781c9a00800342000600d0704128900003403519840d0318212405014a405d10703000640d02e62800c04005c10b012064000403007858002c9220414240032005074a1551a0240c494148030fa140d1000b01d0180342400d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 729230440 1250 729229190 729229199
    0x12090106030803010e250c02040c090e060402070f080a020d02060c0c0d0e0d06151503061401030c2a0c12030e060a050705030301080c0a1703030112031e08040b01 71
    0x40c01031030200c079007146400741180d082c4204900c508001510243d000045ca104103900400100342681c4414038545a01b43d5901c440e0060100341c480301003201080202ca071505218043d82c1807002c075009481640d0040c4c45401900c0d104c802c500800c030000d8074281c40841c8001c046540051101116500ca030b00b611015120f120055070036000c0d461081c090b640101c00703030026007403150503000c01005008100d5010701030b8a84070340084403404007880910140159050141860131056102c5802641c901040080d1070024410703200441007114034100f58030b8015050006120310b020612a180043c0d0081c103039100d0481036400e00c10041c078101c4034888040750004521410060500c480b94151311030110301c000040410406034003000c0c122040c484140f2610380419401c1010b5802ba285050040403580c1e009810402640c07003a030f01c600401950002d110840c0c00003c41500d044801e002c0459071005c25910b015280c07180c01d20401001d0902c1c00710b00c06901a809050180160f002d0740c400798490340c95 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 729231690 1250 729230440 729230443
    0xa08040512070803070f02150c0d03050106051e0a180e01030201020118051926030109060f060f1d040507081803160b0c0706050c0c1209092214031209 66
    0x1030f0301c24001203410030300014010a5a80c5001c0400d544020580c00080b1400c0c10100f00c680c21420f0500c0569000f41085041c0036010705ca45409001e10703017800750601c2c230354000d00c1e803681c0c0c6002c1090b1010980400c188001c640914100102024541c200304040c0d40c840700041d11101d400d21041e0300560900e80d11900c04104200c0031035036039400101605004060446046c4c00240608007224046000008110525015440805000c001000581d502d514200c0d60400382c0d042034003c2c194160602d02c041041d40e8002e0582c0b015822141040039151010725a0f030307800122a0305501da04941050100300301598010841ca1041075030032601c4450f80d072400e841c0340d503e0040e44180040301d900b11403c080429102424280d004c0c1010044929158180e5a900169401a10146600540441c1c10000c000d030500c4124407000e40c41d4074007130402c2032180014110000262801c0d2900d045100340c0080100d00c1a0440c1c1c401e60080d01c00703075103094100e00c9982e4950004203280301c0b1001000100d80041c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 729232940 1250 729231690 729231703
    0x50c100603110f0102070902030c220503032208010204060c03022b050c0109060e060702060f1e0405010f05090d030e01050f0a0b1f0801180506090a0b0a03050a08040512 74
    0x4100800b44810400881406003410700d0741007860642c0308110001814080600085200d00c2100240a44981403401c3c400c2039004d100190020302d02420740240900d8900205940000e84144804003511220080031402800107070401c54140d40001404595150499080754456200343d088501854480c1a40c40395a0910308100c080102e180c3c031400c40e103504c00e10241c44020306010000401c801700da40e440c1c0c110f59840e20400030b290400c80800504c0c94040c880a03500c814406500520307441d041a0800310f020340943d401950789501004142880000d5010300c7c0071110270174080180d0f0901c00310301680c43c45941d44010010b070400c102070917001018043d55000d001c20324039454081e120001c0310b2014101000d4000d030882220444070708501d41c4182c0d10b090103403e540759044e1650520f402014042d82080021488508013028812143c0700c0c95020f40d1301200342c4000043e0b03490b00800050600620703500190803886134107144414048400c00900454804551101120300d4401889807507a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 729234190 1250 729232940 729232943
    0x1080d0e060a20190b070e031b011805040507090e060307050306011a1306030c030f022b06181508070302031207020d0c060809070918031412010303050c100603 70
    0x300c0c0400c2085843c0707051082030042ca0301100076606901684002d82c100b00f4200c074025242d03035142c1018040c802c1d1300b2004030703100c0c6071066000c0c240c030700c12901e0034140150350ba40300541080186401c0001d110a40f15010019000041003805071707060020004102c0603450041040c007040410100e42c81e4500014060201c95021f0054400b036032070282c80160481d00e8907001000f00d0410840e91800d40e07034059801c005015039407000285004003071402030448041f0f94003000c0c1c0c20f20412aa8514071400080556038410800350344201c00000500480a041c5941c8035400603072540d2800424042c1e03d802c0382148403000000455101c0c2e80c3d882880e1745040d0b43c44040c1d09504800c141c440d10103000c00041c1100e500280541d08910044d580380c03440d541d03040d485800098940001c0c406004410b00954008044403c01400b0180000006030103046984100034140900440d421181540313070402c1c3e42001c4040040030515696038100a0032650100160340d4043c0200b030a01c1c0c030a011030b4400c03002501d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 729235440 1250 729234190 729234197
    0x70b0c15010807120b060a05040c09030b06011701031e0506090120031b0f04081f050a090206090d2a0608090f0c040209030c0d21020c03191a01080d0e060a 68
    0x4c00c016100c14100b444080c1c61260080c07004540403400b511a03004a07140c101d1a035880140c424a1810031002643c03010705007604022190030300c6500101d140d007006040d2900080c8036a16040c0c2d6254403160400245001000c0d03018200c1005850003065114800070005400341c0c2513003026187d502180d82c442150000d0000261202140c15420300300007400389203200034220b604e800d8580078014541090350140c01100c401c880040c4682e00400d00a01d500500d1050040c01086041c1c3c0c000741380ea01450501602508054291f9018440184800c1481007000500880d000030844003420b80c2400318050b401c0860708041c0803891b04030740040c5840021070b59401402c2050001410030001e5400101071075850f103e0301b070300c080b00ba41e5030a03c86004c40c4d21441e010340358843c0b07401740c5c4181004584509410b540120007030402e10345020503c03104540c98000310582212140c50000b09040d261000302402d800f0140c00441e80003130002c3c079982c9140c01074a44042c840450010400c4500c0380303080c1c0e000003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 729236690 1250 729235440 729235469
    0x4050d030c05070506040c0501110d090509061c05061501091d0601050f0c0a0c05030106060918090803070e0118030302030d05040525090c0912110102070b0c15010807 73
    0x18034400da000030105446882e11500e44101c64503003600d0540142c0f02a0b820440300e8000304590368000101d0f090b603200190141816500b0902e02518040e95803003500d021b01c114100107009035480900180d0151014564001c010005d8142165100800c5a202c00da00300700c10300340106580518010021074244400c01e0407030000d50a41c065009002800c0141403040a11100074107642d030b030001d498400341a5008040080c950305060407141099400f41e80281d00d01642070010076407000307500080c1c134060350442501103401a0680d0040070610405011040c020060203034442d880380d04502da0309000d0307890300c02d80444d039080c22921150030710004026a000f040b042e401caa103907030007a0345d025000300256120180454420300b4203003840d0f840307078203078209941d018842c03080c4900c0b40100c001c000303107003044800c0e041c51900301070140070100181c5025070b22101d039000e0760b10030003202c4060300d003072300e004d03903ca00303d0801203656034100314034645c03404100c04004640b0060002e070802c00c42c2d600984202c003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 729237940 1250 729236690 729236713
    0x1080c09060913060f0f0902033906130609030605160903021009050a1d090609060612070b040909060c0c0302061515031f0f030809060d02211603050405 67
    0x20154030f550400c4400c1d50303c500000c42d50043d948aa484008241000425240100d204050818801030301310965186a4081c529080c0d5050007894070100d03103401032401800340070740080e215000c0c50704241c0480d8030b0360380c001c80ca0b0b9900c68032b800304680c45a0ba0902071a129034001d41c101100805008000650440041002d460050360030417440141d401c12201440d2500041106050030760004507408a10090302020308230200c903015444070141015040a0800c210382a444003030180546100d0b1001c819450602c40003404058020f05040c28a01c1d51342d0b07170b2814054003816440509680807450703d411411901d0203028840e12540c0e16178054411340d03462070003440c080c016000503a07800010940000e908909054011806401c0e00f1a490002030000c080c56841140c4542000c443c080417100204000380d089810f03264503820440345103841e031147c2d96103c0e0090044a8524810848403140084a0700766001100d024a00c0d0909816075801203080580942e03006541c02400d581c0203480024 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 729239190 1250 729237940 729237961
    0x1c140c0703050702131d010204050d1407080d020d090905090606190503010504080c07080f0709020307032a08160e0f04061d09011503020d030e03010f0903030501080c090609 76
    0x1400301d1090800a00b0080c554020441c203601d849020107010795a00c50048402e038001441d00540480f4100a521306824480400e110042c1c5110051008100586c80383c039880040c032229003d03018070021107103000c200740e800945e074008140010020030055000840d1401c1079000c2c071449003903024000c104d42c0d1608018040746a5500140c0d8465014002011405642c280142401240190710580e21400c45600c014245a0140d0000819510400c20901d6900c000b0a000c4100e0340c0040c3c0040e01d95940003c10b80280c1403644010400e03d901450701404d80120700c2092840045955a904155940400040c0c030f42003000062070200d90702d030088038201c0c609459800d26004000d000800c441c2d551301810030a402141c4c0b070759402503c13032004201d2081e03001d100d801140210421818041841d540101d11a0800214081c00f04000500c280046442c00d42040e03540011a40e4100000303000b41c00c0042c000c0400307000d002ca141c021041003654a151030480c181c0202c1d001449405d403074686c2100f40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 729240440 1250 729239190 729239197
    0x4030f0f090b09121011070c1e03060b0a05090103120f1d0f361302221407090f0b071703040507050612011502010c1e020705151c140c 59
    0x2080a0310a01c0707800180c1800c0c178098048168006e040340c070f484400ca80b40c070204100c2c090b007288008080e00d40a814420760001500000c803038000d200024441004000704008007025042650454175000c00002001000320841102c2c00403035035000b030080a40c1c0811103d4001d200c1203030401c000481c00c01c14652811004103100810010101008038110300c84401d46000801c204000320b40c003d11586940380114210154072070004154518442c030580d0010b002001200d442e0180c0c510300c442c0c01d9101c031110361310441d644124000d58507a189031000c0c00502d188054043c02d003030702080321400110100c8a80a80c1c10407548102c0c0080f000028144603100e5400040065445215401c4001583d40350b46001788240100c4501d007a1003581081c02500600020030209400c43e890543c690720903540c421b0000b02180411100403070418500d160880c541417507504980da004041083c01c51342c02084100070700c200048854500c64014040f402e4600300c4003014032080040d2031000c0003c1c0310f4005d29004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 729241690 1250 729240440 729240469
    0x120d0f030e010606090f060c05120d0207020a0b030907091a0103050c040f0b090f09150603070e1309170a0c03080a06180b030105011a0409020c1504030f0f090b09 71
    0x41e2450300c401c461801e6900d1a80450080b94034400280101001003810b00082c10307550034070b001200c41940d10296520316941550084141c0410144040d03910f507012650480e4000b840e101c081a00c071000d881081e070059401d451a8400c071400000d040301e160090f0940110043c500b241002c0d0f81030010350140500901849191004002c04514004d8044c082e401070300a400381e02da20b50074130b40c0c10302c8145d508025034244a03c110700100034003e0348000152400d07880a45000d510703074594040a0380c909000d0450b0b1507125100f00b10030889a01c1d07550010120900a52542c10f0404150b0700340e003076900c03030f540740d81d40024201c41c010300103c1c3c000c05940341c03c8101c00400185055032603622040d54418402000c01241e2141001c0c0040e00d030900819000d8441e0602c0c072082e07141d02c210111044d00c41c61003102d006c1ca4010403c0301ca40403080c00300580344000d050204d409860649402080d1614158005d404a01d0740e940c580b0526121386625400d480d0240d946600d408085c404014078084014074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 729242940 1250 729241690 729241697
    0x3060d020a080f03031b03220312020d090c060305070f031518090b0106481b0b03060603040318050a0609050a081b0d080d1107030e120d0f 61
    0x80002c600d1000c1004602c4541c40700042d507203a0501d2900400fa4207141244102520002c2c41484040504900c103610b400043c0103d203840407000c3d150640d90599210f0115910500c0801c0400030f1600541114150510403482e001106484480070381c01c40b2002d5170240f001076110105591200e001c2d610040c83c00712031101100040351b84802c040c00c061080c100d20b0540c030751039492000400599403000e031702501146c18040303c096a00201d8083e14000c40e11003d031111010b49000a800d000e81401d2101e0040320003a0721010b0a00e4106452800d0b0404d481c0b20a2541c0c901c400120030402c3c8068a00a80b4020641403a503169620b08031190031541030441103030ba04c150300002e29581e85008003002441a0703160b1080c1c00e4a03140c20022000c5a5601c40391207600b246500080c284c420103c500301c158400c0703a00c82c41141d214244a0b003580100445220020710f055444c1c2010110311010b0843c0c01c0c401c0e9682038641d200c450a01280201c840c038440a140d010355003140c0780324011144800413000c07618 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 729244190 1250 729242940 729242959
    0x3140307050714010f090e0601120e010213080d0507080702100519020c030d0c0206030c1303050f031306030b0306151324050603010b0a1d030109110906031203060d02 73
    0x111500d0601d02c2d03952014040d0016404034101c1035030001044c26a0700d800d410400c01d1145050301034452468000e00003030400100c110000b0584405a003c1040008944001c540303030040c50f50b500415904034069804144120b010000d901885482107425003548049001e040103410340c24410b64404a21210040c890b09000044032100c101040307203280041342e4010111500000145410140030300048001c010341e41143c540940c0342e080443e0b41041006a039680c2d0394100300d01425100f07203e80c0008105001d402c074082d08540e4000041c120f140b20700b030410492a5516201502203480102a00360180c102e40000741c0360717508400410200000143c400d2550641d00707014031b01200d415840a000c00c641b00010354500d078421000b0700000e040156080e0307255505200c0c0c2c020550094003052410010880510100c181d0b0441003c41401c20140c024010300b60a407034001c10815505201d0703405074000c0000a031461900184461000e030038007071298070316100c581c1800f440c804003040698200700d490 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 729245440 1250 729244190 729244193
    0xf030a0c030c120806040507052502010306051201020706060e0403020a0204050910020705060103050c06031311010207030c03150539040302030a2a05010806090a11040603020403110a0602060103140307 88
    0x583d03481081d04150b0b41d1100a15048040004541000c0e2000007001070a0181103005405064081071072080c003018400383d0300c018401207020f045203400458000d08081e02c6440941c1c07054002d0030801c1e02c100301c180419911045281c000e0441210085c0040c0e100d201d150015062603403106800000382810755014452101610090f40e00c84041103c0c3d541c010705c010801e10409103c0c180016104454071483c509026211841c40300703409201401e407640409040460b680200301c0135009541c040350748220f131684d0341010120090201d00c1440d00030b0900e80028084450300240d1074042104503d40000c03005412940b050042200c40005d0039404208400310140e0703001c00440031000e20803050141d0700034038a41013010000c000e0100c0c1c100d524200d60180401c0c0c0c0c10480c80c681c0300300b0030344202d42680d0b10b551645010704490701e01564241000a0b02280d0217606030010400e580c06500c140207020202020f000f5170400b540315100c0107800c04d40040c000510714181d0580881c00c4075044030b042400c036 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 729246690 1250 729245440 729245453
    0x7050a11061009060e0403050316210903180f0b13050406090c0f030513120210090c050102240601051e0c0d120e1005130f050c0109080f030a0c030c 65
    0x40d10b2145440354940d80400c9400c0340b60080b480603144002c0034a2042c202560040c2c4540009031007000018501c020b0701da00711b40f03e03192011116940c030280c0e107030104418800300c00402003103005400242020041080d081c0402d00c0341c400f1203810f200035040542c85c00c1005d0b255074004080c02c00000c0b04203080003e4954442c064500034101031580000c5004840c0c10141404040550701410f040c100410050741c8550382151a96441d00000301144c400a500400c034100604da00010501c0351801041c841480005071094042c3d460a8088a01c001181130000d49444004541c103010103d0b064000381065124402412101701c00c070f40f007494401c001040303d12682c0c0201244110990152a00002c11070b805150941b00000705081001413581013428642c480030700755080b442d615207500c0070030b0307070340c2c4202080c0c03440c0940104144114128501d4095143c0b540005a1800101c1d81d01020400503804118030010703000c8000154a4160215815180c80001190580c10300c0b46286100010502 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 729247940 1250 729246690 729246703
    0xa320f03091618050c040b21010503010e0c0d08040506040602030306030705012d0e0613090c02060f01060c0f060f0e07090e030405190b0412110306040b07050a11 71
    0x820800940c40c0e15180360341d28030301090038886090200c0e03420380400c803240c8640512004a480c521011840f541c1d81408203580d4803480c2d209021a120004000701c072045866040041e45580026640d8141d98500401d42681d200c180b80403280c1d0400c4c0d03111042480c20b004240403944c0300b02d81c0c007070a150381d0784c0001d200c0e07402c03a90080016070000000c01030b1500c0c0511591001e40800d080c46820101c103042d552810034a03a8800e24000c03012200c42601c400e0040314000459040100025030b140684007885031400054418140001e00b040f40c194501800801c40b64452040400e0048468bca0710724203c60651440009407100d40308800280702084080c050800100c641c5240401d8000d44078605070b2401c10320358846103a0324038001c0c4e103002c4824080115801c6072000c82e6444170501c00030520203402091540000c0c002040010006520007040025141c1c260054a066845005a00070316442d03075001c507401400c24000000161081e40a00d001c0c00c1d4130010740c5410941c4c1000c2804041c980349 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 729249190 1250 729247940 729247957
    0x603010e06070c1110080a1505040609090302062a0d0b0a09140906010f0501050906091201090201080a0203011d180a05060901150b03181f0b0f01050a32 67
    0x31410b10303481d821300140004da01c0b4440401d96802c480710b46000d0005101007809020307030340500c1e1a903074803221440d14150690044d000051041000035505c400c10320080403100b40071005405000d0021b5024035600000c3c120343e20540f8080d100c80c86076004001240e512205c40f010415590390400140d64598242c0880581140c40e000210301c00e078080344604000e8000c05d4070145a00007401844002c0401c94071001f1200c0c28200252941400740019400b4003403040480d070404c80b00e0100c044100d90540041c19058001c0e200c3c4142922030200e2002a403000340110301032000e5000600d4072000c0004115a480303001d9410b010b0a800c080344519003040d05149064a081d4441d000f4845881b00a200314207085c0c22050120b8001072414402c2d60813800014551040310340740e20f40c40301d041c26082c818041d00800c040315100c241911440e0031401800c2e41c1030710502800400100030f595501401c102d40c40351441e80c0310710901441c02501454480742c000321810010703a4200741c081a501c44000505400d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 729250440 1250 729249190 729249197
    0x702100c0b0901051902090a091107050f0c2707080402060d0510211e1b060203181e0411092d010305040f060504051c1709031e030603010e0607 63
    0x174140000c21404003120000b50f8020360348100f0601c8040c0c0c0d40c04045400311031038044045460001010050103c0c0a102400781981c02111101d40c1c1c0700c01d010610440d0004200c4100b12800e0354403584860b05480900ca0005000078074010421150188254a078031034070080a40341780240c00a125001c1d188169214a080e0b40d101da0140720350202d040c0b00800942d91200d03107444610090b290310021101e042d0740b003404094407082c82000c3c080f01c04400c458000a0002d280c45050b603442c0c00a580742c0c02154265424941c0c2407600781189000030040c83c43d80145120805c2c00200c500412000309044100d4103070340344003000703000c2c004c0d12a10194202504a100204040300302004803900e100c600d005100c1c1094a010b04200c00603d402c0c000e2141c0f0381d0002000aa00d41c0c680c5096860304107540e0404544604540308140d20741d038400400c0654002c0748031b4400c01d6468239542d181d80c80c0540ca20440d0307400ca44000c00b030f0a91820001440c0d108400030004203c521605241030308202094a015001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 729251690 1250 729250440 729250451
    0xf050703050c1617011109130509120703020d09080109031e0903052e090c170a17030402031c020706030b06160c1a07080702060327160909080702100c0b0901 69
    0x204e4020b02c203583d01c03003038a880c1e05480d10301000001000013100904600b10241e50302c010902e103c10410945501521b803011550b990b003202e081c0a0b590300d50010743d090002d61072080206217260180164241e0540c551102d1018826815099001c1300202d050f107010412034840010220b00104120341000a4008692075805552500c400e0100c1020050302503a508144042c80007032060405002140d010201030146800c0a01400f418000034050203003605401410404424425800850045100f141200d2007401c480c0002d07540403040e0070701000541c010031410001a4000d030043e4000e142e00800c098a441200351b003001c003403803a91a003690300130300c400e10600c0160010b0340e50712988504455054148000380e038400c08030f031140c104001d01515020020402c480b030500c0300b03102203001a0512203140154442906d50320b44090000c1800d6052185000694101c6031040081880d00040501c1c90140070b074080c004c2e0000074400d80340030000888184070100d181d10030780c0d50107030310843c0c0041342 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 729252940 1250 729251690 729251729
    0x30509010e060c0a0807172a01091a0c0f030109050105040c1407260703020a1b0503120a110303100504060e0c030f0402010224010906060f050703050c16 67
    0x300c0c400d0324a482c051141007040388400080098200007495101201a548850030b00d4139580c40c0300324407100050a0383c08a0300d441803444101040c0194098410b54590350b000040c4000e0a030791807400b018015401851105c0b04a000c2c3c40d401c554402c0703d409840e4a0103102440c5186664400d9112207480c07a90341006120b680b03040d0103850403000742480c7c198031046640001c040c5030710506100503d072034080000c124034a11041e641c141408a40800309403102d40a003406034640a2070401104c0c8000c000208402c80507030030f035040081e658003600811480d104030403503160a522060340d1000b803045d842e003600000d640400042d84900d20200b00c0310012840c160a010070f0f1003550b040854582c0d0341204020b12215240152540210b2103407180d15561070b507000507400e01039241c044510707800c00c81505e510807141c50f65229040702d115807002c011550303440e8011100c0d58100300071240040c070b0402c08400800e22036030182804c00210000d41d2210360b1000000340541c00c059102101e0017061416510 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 729254190 1250 729252940 729252947
    0x6181d070e1002010515040504030815180c031504020a021911100908210313020f092403030405030c0d0c0803030708041b05030c1302070b0a05090d030902030a03030507020a060903050901 82
    0x1406040c0031f4405006608180c0c1d0b0142c80d2000c0101200b10308480d803802c8601c980d80310405080c603c2d17550480814141401c42141020342e1007142c4c5d10a807082140702c00c026606080c82114050051903028103444181c0e43e003440a9200c41410554204c00800c6080c81640c1e18031a0100c610308254542035030f0a40341610301401d10304941d03801030016203d00c42c0140c081300070408484d4000c0c1410b280070341e050070620000e507607030348113000c491382143c2c140c0c081019402000f001691940141008000000c0c2d043c401c1541c1c0348911b00170103802d600003c01d06039050602c4191260018414442c4c0d480e0075845080d064511b0304100c1d0b032100000c01c03201c01d100601011000c100c081618900614084a01300000b00782c0d5103002049460003040c502000c4100440c0300d41c1135a4600e54030002c5034003a81031900702c2c040503060a54000c10301d4040c00e414041e80313038082d210307403c645680a03015041c840c415841c141c000380001080a415801480d00810005e502071181d00d00c03091090301c601e900d42c1c28040005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 729255440 1250 729254190 729254221
    0xe0a1505030d030506011812020607020d052a03010510031106040e09010b0406051807120e0102162904020603070c2316050303070b150307030c06181d070e10020105 72
    0x5111047c4c160001d1106001c0c1341c09941c003076501690740f56581d0107588045111703442c5c03800d400303480c5004202c03040f16140c21254113808080e0500c090741ca076143e012800c046c200e61040e500c00745035400040003040040d0343c00200b01d942035001040e60381401d5690141602d486021601c2c507025075992155080035141510802c400741c40c0030303a0317803107802c0c0804a2004590000980f00c5001e01c149d0784101140c008960b042416018240002590ac4811518599013255498a001c6400792000d50503c01e240003d4140c2126014480400111603100c0d43c0078003100780e1000d4000700800020780c42c86404116540074400a420312120075402080c3c083d0035090a01d5a01038209651112200c0100b01940d400425502c00304e401000b11511512140a552900024042c07042d4142c00703026000018054081040e0044035425118000c1070f84011490000c070310740e98020f06075800701d641d003105803148950241650011880c04e01107a0b1a16040010f40c8520380c015440005039150003c101c0c540c11000f611 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 729256690 1250 729255440 729255467
    0x16090b0d0f0515240412030e10030c02030414041103070c050c100507020405100e0f040c1e03060905070504020c0a0c1502070302150d060609140a0e0a1505030d03050601 74
    0x1c100e61219080f00080240c2815028210b0218500100f0f068601c4e88008407030040c1500c0c295120244501d14016000710401089603220303c41d140364440e4168002c1c01400720004a51740a18680303030509451020030100040a55001540d5103040384160307005100443c0212215100d18231000107603c0d050785000035244040d406420020300c0341c418103801405660107264111404551941c40e074011003150281580903c12402e00501840b1440510081c0c26005500581614100d1030301c99800c200c001c5019081410200e2640c101000490025403101030140e200d142580c0c43c1c5507030350000400340c1e0006003003900c0c241c110202e43c0d007c1010000e04440105105050060b070300e9840c02005c0d403078031550300c006402481c504000500340400101142d02040b8920010040369480341e9000b45004542e0144601260b104542c0450703900d003012888007104c0c962000303840240d60308000301001e0700740600314480c2e4031046100491030303076400d0003500c017074100300c0c2e8002649140c01c40c001801408a03001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 729257940 1250 729256690 729256711
    0x30b010605190c050304060516170702030d030528021e0d0e060f06060c2b030c0c0b07030b04270b100b03070c0305070b090d180b0316090b0d0f05 64
    0x40500c00550b01000340c0e400c880103070030801e49030f4207507001c0550200c079003082c00ac125407c0b100e15562600b0805c400382101038000e40465414010030181901101e000340d4292501140c0c1000e080205244442d01d01c415150b00e070009401c00b83e6060413404640c003030420ba41c03012034021400402054040c030030a4588243c10008100c541001400000300c5030f0041c0c6120300030000010602052041080ba100012807082c40c000380394a198030303402000b0020107502900003400e001d221140300780f0843c440c029042d0408052a0300340c41d0fa05050780240704482420740c220b078443c1c243e0202c1080310f40d14183c1000f200c04d410100081545010039480703074003c01112003a60f42078000d2203000765040959070321007040c0c10050b0408a440c01c0a40b1a401894802801050844100071300c264000c6002904601d16460b0001d86903a403525203840032a990185200d01a02031002442c000d81e4038150300072000b128140707025400d80350060f000710340d0300090042d0030540e2143c951420180f054481c01e03074449000070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 729259190 1250 729257940 729257957
    0x405010c06090c050a0e0402040b0901030b060f0109150302040806090d020304030f0602131221020d031104030f050f0c03070b16230a1b030b06060c0304030b01060519 73
    0x182580c0109180500001d9035850007400b00504020008090080144690760803942d91001c00081c49045400300e01803800c01c038610071541886803030207060700c0e4000048440c070398942d03041c4000c44101c1241181004402d003400035110b180c2d8140f05002448680e40036996a042120107850041c0140c10704a065108110016880d070703010084e14280c80e0b0000034030541d41241c0c1003c1000e0b00400e20003c0c0f04200058000071120074800d41182c01611a821419845020f04d00e1141984449000800581c0100450b50203451203a48a403003000308101c415800e00d41c482c1c8070a0b1007035124400c00c4071551721103c0380f144a68800c0003c050100f2048001300000c03818034130401094020354100c1000641c016501400300002c07148a03861556070286000107203c00030f20503070390340c0300c410906881d014880003d480008000c5040c01054940009050707025441d07180c180a501e0b405800b02d030503940010301001c40002d504010850081c8825030b0ba4984030240700030410a01d48074400240d051110310b2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 729260440 1250 729259190 729259199
    0x314090d1e20180a020d0f0e0d08060f061b030705012903030a030b040b03100c0f050310031101020a0c140901081617030c070e1005060c2a0306180f010204 68
    0xc60510030031280c0000f091495440311000c600290282030340010045040c0507640314800807075407140807011191000c441200e44095410759500005403991601b000e5140912035460804a0082c0a0106000030058100504a05103070954000840880b0f85075100d600d0b5405000303031440004000007910106005e40016040080d0380c07803107118240001d06403108191180e40e940c0b64007141e2514405030989041402d465084d00060020710b08030004a413141c480c220f6810b03c00c1c02035a105a04a19070900381c0d9080d40c4560301288600ca05650440c45951800c00c000788000714a0382c001e00e035528403c0f1a000c007080070040380c0070b0160082c1c14194001d603003030f0782549c01114400c4202c85203c0d400c0c80e002002d0141c0c25045104a01d1406403511440030005010200b41c0441c0b40f0032180e800b5044280d40e100d10410000d4401c08020b00c005074400c1c5c454440d0f60094a41401c0014960031740e0024a0100d08086030030180115222450110325840e0382e0720406044c080310380c001d9540d800071840d05080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 729261690 1250 729260440 729260449
    0x90902042702010f0e030a030305180706090e0a060302120f100221150307140406050a060206190b0d051b120a03081f08060a06090204030314090d1e20 66
    0x4201c01904111400c0c1040f40224000d00c1c403000410030160603191801c05a003005000751805407031900e80340b2882010400f00d0403020070306c90f042c2c030f40d1540c07409107072490402440010750300a84900c41e080d950300310002c01a581c44d0705481c0100e61300401ba004000b8501000d90414040707400c0c11444500400240a071703a4845100c900041c172080f542c0c0c10403900d03100c038525440002c0894641e014071907044089210310a521451561174000c0700d0074800a5100c01c20300c031060300244075910144e4000707008160024030280c2e000c1c0112010900c00111018208000340762904401c500b52030302e8004803c085003801a990306801d219205486c43c2810445520141d56130b458134000c01380400c910403020510140c2d5400090320004800340f202015180c0b030b142d1480c2c07900002d80e214090a0710304000052884424000d8408480d01074551001072000d149220009520500d0fa09612099610319040001c41600c004030003800d0240b82c29940e00340900e48410600c24112000b00c0c0358420440750240b5548 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 729262940 1250 729261690 729261761
    0xf0f030c09020c01140c07060e0c090c0d0f060f06020607030603050c010c080c0609010617070312030506241c1a042301080d0807030b1e060403020a09090204 69
    0x612900069079200e1280070f4500400130314622107898101340090100701030580020380f10150003054200b01c6202210302e42070303a680c01110140d80102c1240000744034140c0500141c840700d40784820101d203031007081a00b0000c5804641010340000d688080c28000380d07504001560b0703c26280c0c20100300007415525465983c8015481150403c09034084940070004101c2c26034050b440c1c1001100da8038100414090f0107000e0070302900300ea02c41c50381003000300300300002200320840c4d422004106075024406800c5002d850300426241c3c01c400c855a024403042d4603640c4000056010710301040d21800e042b07506001c1400300151416070079080944541200d902100b0040079842c081310300241d54006000f840441454682c444910b031b0084200005120300302281e205450303a41c50759016520758809100f50304590f1900030054000309207900f80c0010240f034503840000c902d40145034509150350781e80040c42c10b4100c0d420109000e0f81340c3c10817a0443c2018012000b000c50802041f442d03c904024105500c0b88 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 729264190 1250 729262940 729262949
    0x30a0606080702070b090301090b0a020a26040f0227060103050c0c0c0409140607050406080601030509061302010203130609090c0c0302060c0715020301120b0601030b03030403030528090f0f030c 85
    0x10000486c2c10712960b00354042c440c4161300c020711039110301d090600c2d880250011420540481c00c903000803c03a00040994803407107035110740d005c1206511030f0740394035941e1414114126000822940c00005880900c80340806110754003030442070394580300300010183c50000e000100c80010138081e8258440e030101d0b101a4070001510001b4a502490401699031241070150842c0d9010b00d005000380c3d954131500030301c251051921025034507201c800044084890845815030f15030008804180100384a080744c1a03c40d00502c12039091542100d0003541c803c46940c0658046120500704000d0400c16020304592007940d8100754410f00b20a8501945842c0e00600c002c0034104002421070404c400500c58a0140000c09000c6452350b848105010b1240d258190a44030f02d510200002d80d80d43c824081e245041c07401601031820949545d40940b0301d07030400782e003107139010501d110f4850400308505080d07201c030501ca0340d900b075900b8a4040c00600d241550741090601307030150305083c80401e005040b21401c54 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 729265440 1250 729264190 729264209
    0xf020310061404061d100c06150b030f04022806023c07090501030602070605060406080316020103020706180c0b030c1b0c04060e09100204050f0d0317010b030a060608070207 76
    0x4440388001240784100b4170000540c0003440c2e04076101c103190f0220054000314442d4004000e21444251200d2032000184513044c0c000c1000c00c0003510382185011415041840501540856548403c44211610103a10000c506809840341040956030401400300c59000210704112101351001c041e00c030721040c0704028032915220705d40c00c603c01070040100100809440004100c156101e1030301c1d0004c0d500c40b0006494003400c7c1001f2072500e281501c54102101d000c00000e506d400102c0ca040d585c0304c2181c400070b9040c55420300c100c0780440c003980661f00707100100c1c1a8040f00e181451505507550166134102121100041c01003002c80040034040f134242d480d64010504a01030384c3d10a180c6080c41c0622440c0d08a03040110002c0c2c00c4410b405464080c100c840207440d07840100c291100300724001c0d88503035503105440100c481114202801021055402450481c4d8441c200501214165000f070384064000340000003042510081ca106a10241245260443c003508180304025a070740c4444c0942201b1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 729266690 1250 729265440 729265457
    0x30506060a0c0311060f0f250f1202190201180c060503060d05010e0a031e050d051305070303080603100b0303030f0a270b0c070804030b13060f02031006140406 70
    0x10f16008442901e90406104203c4241780717401040d101a5003007d40740d40049078503150104005600c9802d1064a8200b00948c02440c4065110200d5415280c03940c1c0d0024403a00102c80401141780b40000c101c000080c030b04034010700c81821802400c41d4015424112909098842d070400148064200b01c01c9900601d003054aa807140b0000400c0100040401840d940c6403200d0881ca9510225810799124001d446144100f50400700207144c0045a00c400d01c005501040403142c1d603545a40800d03000070141528500700b0034650b407081d1410450b9002035011403803041c200515031508201c01c825250600d1010300132020b007580803035940d0002420039003075841d22200041c0385410b194400c03039000740480104002002c0081140d0703000d6a21103010358403c2000300001c0c102c459808100c0b04152340c030620712807070140303561520a407201001e0841c1c140d15134410001000b00318076005810704844021170043c0d4a0402001081010416501c500140200c0d00c0b1840b130030b040c911007584c0c111034050800325039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 729267940 1250 729266690 729266693
    0xc0e190207110409120e01111e100608161517070c1b0801050c120402120307080a031e060503120714190507080102130b0a0302091816030506060a0c 65
    0x440b1034201c4103240d042450b18800c0e03400e000300d101d00300c88100b0203174a0b040e00752841d2800450b140c504201c41030055a02003160491844030201c04e0f64100910081a01e0850840e0b00100c02038409642c0121041d51080e581c421020946c02042c1000307010b0340394034401071982e120001d00000c07040001c0712200380d08000000c0c1c160f801202c28942d240d51140c8400d850691348107150090110318001e2218641c40c01c000281c1704820202103849c03201c1462040c804036900ca03800c1200f4030401c940074081501082c0030020002e24408003800805411780c601003407101e03110b400003482c5125805508410b03420010100000e440102d65a001211030001c90b41d540c0c240c50411003540042800c49090030300c1070710048415490061551030000703119400780c23002c06039a44100c40c281d005d001c1b520b200c0000092800c0040803410001171000e0b19183c00c0150070003ea61000520951801c01c0a2840700c0310201002400440000c1140e14406141030821590520b8008a103080c0500900c1c0010b00220024640 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 729269190 1250 729267940 729267953
    0x1212030f0f1104080f070302212505040c050313110415090b030d1d010f2a02010f050a080a0203040c080f161406190504080a0c030c0e190207 62
    0x41c030140c101080c0038121603800e1034295a8002e1040d0b900d603025030605066058004514141160b80007031602107008100c00180d40d005c50700c10110000c0c0e1107041e4a5102c2c1d6840380700703819180c68000c103281010519160601c8151400c8503074060401c0410010400040c281c00301103c4480e811070345040316800d018002c60000c100008500007110300102e400100003032150025080c61b9001e07030550700e007144042c0b81924241c181110040d44800101480c0c0c6040d441140c9103d408078852901c800c0c100300c0b80c801c0880d01e100558401010000c400b103100b0075542c110003982d960314404c2c41c120380f03004a40d104c0100039110141104040540010109050080043d56980641a00010f80701007841d40d6501e07507505d070580c5040f01406080c8000c000703140c2c0300011400c200300070050016440c3c04d980d6080a54103814001000d81400024407010503861800c200a6001c43d12858040c6102400c41c103000309e4485003035100340b400c0c0319040200030348201d00381e403500d031101001880542c840c002d504e08603 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 729270440 1250 729269190 729269201
    0x2803020f0f1803070b041728020103151202010e040e03040b0301080c031209040506030f030c070305060a150302011b0f11010e030a021c0507030f0b101212030f 70
    0x92a900004180314001414110092824030600380e40380c84045842024184c50306100d204107600c90206100400042c6821000c0b036001c0c03035284007a0703000c90314150380c840d00c41c4180b09070460410711000c420b036085503014130076442001c0d070b070544030f00c000d40c50206100740945d0003001c024100540d0304080c440684450700010020609801076035221500c80350404030769002403040e2190351142c401c44aa05040c081900080d0150048001c3d24121102c4207200140c6405007649405115440f80e1b40d010b410144003803c0940842c401800c042d0380356040c080d103006000380c0b000e0412881c0083c0708281c0b0b18203c444804584e82801c100000c05061f150700d824a50186102a21040050003500c080001c4000300350401c41c000d8840700850030b008810b02da652903082d03800070740020071920300c044111400d001d80c48501744118120f50072a52a40c0e590720030ba0200301011a0124000d0040c03103026445046c412014100c8440b0015480c107054448a41210800e034412080c5681c550141c4a0f1542d60f0f00322 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 729271690 1250 729270440 729270457
    0x50607030309120206101202130e1009050105070e0102010e1e03040b0406050a110109020d0b1b12060f060309100b21100507030e060a020d1d0120280302 67
    0x400c411843c2e03409002c5d440d11000caa03a40540388000030f001c601d01c2c2081414200685e00508950108408100e401c00200500071107001c961140000400e030045a074080c1c040890300c82c03400851203003030011001e8103010101818a05590522014914420002071256003010140e0b00e50f80c220000d00e02c4550851040742c101c040c0c9140001404a11160800018010154180d407002d11100040601d58201c03420b181000f0b40c00b511002e00b1902103580c02d41c590303800a4561403c114800d5101048e81411341c46001ca0703541d0920b0a004010162412082e8040024020b49003185540342103c041070300c4c0c6041c120580c0c0d5696680d041c40e440c903100c00c03100c603180d014044d9880c1d8041c580800c000356a184031103c003502e414189400612050301c00c1c0038a1002e1034a0800a0655498110b05c800194000707200c0e250703055076034001e29400c028401100f03402503114207000050b005540f0903260640030070305041c41810720082000c007581c0e038100c4c00420011007010640c0c807800112440304802074030a2140c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 729272940 1250 729271690 729271703
    0xc12040305040302210d21060611070f152604050f0607090b04060c0807062a08310b01090c03151406031302040c03050103060c0c020307050607030309 66
    0x42004040d000760050064a0084444444985040400c03030406040707040070031103c3e000580c85031000740c0691200440240001030390061012816900b60032140d103940030030002050150660701003001070244002030040c0c41180c80c0d60606044041ea80d0094401081d020040041a25601011807600644190028085d11546803d040c00c007165030b981c188a485516006080101e50814002d4000d441101c080300380041c2817610b49001034a410134180c0d000e660058080002c071001540740d100781c80c03403180b00c801c075408408028a0042c66101c0821854801d20101c2010b10075421070700004c04551410b182c00306034068810604c04080000c03040780c002d0600300c01400106030549140c10900808a075a61304201e000c1d0040080d80500c40725115101c00000a040820903030b007060001184e0016a03402d4040ea425001c0e07001c181121801820b00e00029556401801040b14134003c0000324800340c41c1468042100e500040e881d01c10034840da6204550001c4c0660816019402c41e0040d00d80200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 729274190 1250 729272940 729272977
    0x4110a06080a0b10090b0f040503071517040818040e0d0203210f161b060605090604021305061812010c08060d2609040509010903030b0a08030904050c 66
    0x14005000c0d0352040c2c2c0d59080c480d0030520080d00d1400d2021601c07070740c050590b03503c2c0c90172441c0640050455101e11500030100e1400c00c0b01248039101000001d008080400c41c100042d80070b04001403480452011880c140e254100501022652200c25030b820002c000801030031200070440014014034100c2c8004001d4015441454486034020018126a407038070304161000c2014801901c8440c1c0e000ca40451005582c0008241d00b440c0c0200d5101d040940c60070314180c0300c80204480040310940400450b1a02e499020501c400d00b4000681504140e098800f9824040c1e9680400c1c800704484c040d490040c50041094000d020558086051511019041141c2c050440787c1907406046400b0070b441c0800d268501046080c189185080d009507003010f03500402840460507e4403080318140c20700ca88039403c0c06910a10b98a40c819035002c3c01070b120000a9402c201c0c0350290540e082c038134401c2c3c401c03420300d0000c122180b030100450361000c0003214006110f80c0d5030790103000b203402590036010704a145103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 729275440 1250 729274190 729274199
    0xa0215190809010c050a1403150306040f110904080d0b0f040204080c1509031b2110051506040603150b070c080f0304050f010f0c080c0c1905150304110a 67
    0x1c09074501502544000b805480e65042c402c1e203840c42910340450004900c1321110900031518000366412003001c40b01d501244040c1000070345007040603901076418161260426081043c17642502c404138605035a0316003507141c9a1100340090080d480704044403038903200d52405580d10241a10f0031540010011502c81c1c1c0c40761081035072240c00d600b0042c028082d110b640311840d500c40064842e4194001e00070303c094120000d00310390070403c1d2002d05402c16916000428030040c0401846d000d01e450900030f10030240e02d4101001510030203010100080c10208102c9481d488410464040d1a5141004180716611026a01c00b5000c580d0044140400210304801002028100102102d0b43d44084a0210500c580043d88920591094a43c020300100c80c60b180c80d4040c540c151881200e60801050216280d11060795580c4200f54041c11904a043c1c08030036407600c543c0c4038513200040b4078080240e905200110700070101240441070040c00200004042125517414500d003c0c1001d04040100344c0c1d513 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 729276690 1250 729275440 729275447
    0x613081c05190b04020301120206130e040b06030606010f2304171606080c0d05090c0901061112040b030a09021c030e1f0e011206030c030f0210080106020a021519 71
    0x10b055007864107070708100103810145014001d60b4103a40c54046400c0d050080e5a08010032613200300f080390842006450000707000790203450911f00c900d002d85030310102890030034109400d10344024181414000031490503022280c0c020508000c0c2c2e55150040720000b005943d15000d1401140d00035040d6030300311401250000c50106840c520f503142c0d0040c003218540c40d258280d590580880300c0101014041c028400420b000b5004141c00160107000d0b01c00c20040070000c1a0740d16000d800120100e008a01840310440c0d040110740c41002000c0c01542c141401d2410b03204040c400039014036009502c83c0044130641d070360140c85400381080002e40f009004480d10740a00703103501140c14948100348181c03440b00801814051130701ca40b800c40e030720318450080400040da80454042981c008659131001c0210004540642c008003850185020103100c801506c104000300558ec1c1d2324004201818004024860f0005428280c540d1f04031207440d081c8107010342c0000c1c03d024840e4100074190b022502c2d00b1303074030b0340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 729277940 1250 729276690 729276721
    0x90b07060603111c0615050603043002031602010519030c080114030a0b070318030c020f011b0f03050d020d021305030c22110406020f0f0613081c05 65
    0x10a01c1001d20b10543d0408000e50701d11032030711085180c0007264030388002421551052100c490310580c0354a4154848011501e180c00071902190403280842c50826035220780144180a01c441000c01030b41c072125a040291a40608a01003070f041130207000c95400c5a00038400d4503203941462031162110440000010090f10610f000800071032128000410011100c000c1c402d111640540144900e100c0b80e59034080145004042c0c02c00c1507500c000d0705004845a810070346085020391740e250b5804519004101d800d0b0348002d03c42e418000c00e0030b015281d60540c07517000030f990340c0c02039140e802c50403140c03c00759028851042403021141c40040e01d00c032038503016405019000086010315903820340722003d050740c84054034080d80d0700418051110103c0720394107442d5843d003c030304100032030600c18010440c000c03600690010000358201094154564408205814403580c0b41d000401883c02d0a000d5103d9041c030306e2202030000340d4005030174600746200c1c0c1d00d041c42d880700c0c7d0142001540707440c503d0f0704040c41 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 729279190 1250 729277940 729277943
    0x906120a0f0303050601022a0d05070b090a0506070507051026071e14070c0509090d08160804140f060c0c01200a0e0a08010f05041a0411010f090b07060603 68
    0x280f4001c00b0a0700d65100103103a08c110040022080d14060011969401c070342041d14a65511007488000000060001d00503040104814640140c40d01500300801451450742c1c0c10035070041c0400e000c1880854000107881d0111801611414101d03502c442044076102d00f0400c2880c5448004e00f9002044000348808074803c1e4442d41d11815402c01c0ca643c404102c071500c200103030000c1c10201c00c004407225141c005142a521504081000b9a80d82020849005c0c08844010940e0050307103803405403d8000600b198410014404003041414044010308449005071002c1d120320110400310408102c00c2020a4450300b01c40c08980380352074182482e55141c1d00c105040d081d1942840b480c0c81405241500c01071101c41140030050604441d0b0008554801500c0c0c01c45512180c0054000b40b101000c0c0f1032045420582000451300d40341c982011010011744152481844a4400402001c60074055a42502c42401d1928800c3c0c2c01441c0c1c011240c1643c1f90700841092000000c0318800c01141d64006d800301c9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 729280440 1250 729279190 729279197
    0x60819090f03030c020f0c0120060406020316020d020a17070f05060603010b030d080c030601021f1b0801030206120a0e030a080a140c03010306020a02011b030c02120a0e0906120a0f03 80
    0x2144d03040100d80300c00b14030025007881d601c100216945580680c0c017030303103c0d55201d1036920720007040e45060301d28000050724141e03400c0f43d0020034040003500840b905820855180011b040f8041000c4000350b039030201c401c003d46682c201122100a14203580101d411483c2c118000e40000e60290500300c1c0c5810050360b0300340c030035841c000005486d820013050a40d4000c1e0f00b51141c0b98140d5030161092180d41c070051010b030450042071031118810081e8007110390a02000c0600144100840704040b0081130032070708010501c4440401000182c0c0da06084500c0e415070490341d111143c444d4515440509107640c8404168000403139840d0009603c42c500d0361159480100074030236a103080c1d000103141d250503100900603030310401c014030219038035400901040105100019441080000604610300f020704c3c0c2100094030380402203401c5d40c1c10040900c0000d21098080e192800f0840e024140e17100401946014690100000f6280c0e03a030000922034074510b01050b691018214035100d00c28046858046010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 729281690 1250 729280440 729280451
    0x3141b1605010305010807030b091002220902040b041701060305071e05041a06130518010602010e0c1e0f0a060e030f071508091c2102070c060819090f0303 68
    0x42d8802d02643d4103c80703034200a0004641983c48002c1a1400100031030240c1c4600420499030480e1440100640f00c0080030755120850000218003c1034456406103100c540184000d00c100c11362401180c0865040e00b1007940c0d280820b00b501405404907a002034554004d4035030002d02460f807282200100501c020701c040d1f8013500c039010442280c0008841111f81c4011002d001c0080c03c22000404071050180c040700944d0707a41d04c0020303042e0b90030000c008005a003030000400071590240034210814046c1c82c003419442c0420f070f012801c0c2d01200c116182e1040b4101c2e40a0340701e5120031200f91000e041c00342c15280e5080e25902c018005042d0051614003e01c07501081e60004c140c0483c101d02681c40403a004e1560070f20341c110450314000d0160810005008146010121040700c4001c44080b2a0380c0c0c885010142209a514500603510003035050680e00401203440020a41c004034015104181040040d5444501d07641d07031201c07154856080031500c4c00084030203100700c039403801c0e405c24800e0750103002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 729282940 1250 729281690 729281699
    0x90b04060b0f04141203030403050703031107030c2a090c110d020d0320070f020a05120613080912101109090a0c1e080f010803090d03141b16 62
    0x181c0380306000c03451141c09800e22007400501c3e50003480c0e4640c280e00900c00c0c004042c0d210342643c211351080e1001c501080e000292074003010742500900151181c1c8014542c100346054801a02c001c4410301c004002e0074456100050100b56581400c42000c10a00340c0c81c029611000518001d10030119908013107117808410450010001601c80861600c903406064a680510015405490605003031228850303410801c00b90740340814050a1624002e082064200d001c034018003154501980125014859075041800b003541e0025040b50482800f42108900d003840782804103c50084c980b034503031f0041103c441040140740c002440b03030700985003e000b00300c1e031002c00321b03500c42d2031040c21388841d001650000080c0d00c1000a0340054038003181d6003045810091904c00440c03640e0004000300e40801e88810500c0402900c0007000d501500c900c40055140c000404000f580301441c10100404011005060641074004001540c44c40385803210225000740e06d4140c2d442d102d070380070440a229510301880024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 729284190 1250 729282940 729282959
    0x24030506220c0b0304020d0f030e1504080c011d030d09150503061507021f1106011508190e030714060a09030909021602060d06030c1205070e040516090b0406 69
    0x1020180d20280b415501c81c40c01494440b140c000410590703108a481c80030001040c101c07040101100c1c0b29a803440e4091082c4010003a00440ba4174507040a204280720070301444100062400d039410007400c000801040c14103000400e60741c0005000d41500a01c0700c5074181c4e940103020039081c0c840b42004280048030b1404122224003040300c100d588080c0400d402040c101003a001840a50700142110110300082034480c094400d0010340c030710009071482900d10742e0300d00c28804e550143c80c0400713010014400c000703030041251901500183c0e400c21000140401441c1e070b584203042402140060302d8a8040700c3c01c02509640004850840502520340040c107405220710824546a5044d2660584581090980c20080d04004044140da003441d04008000d0307613405016254220b00c0210101d001c03411480e01203010350740340d48407041c80c00920ba1801e0000d031010501c50300b80c4000b00d42c0401941d586052862803c0c0310400240d003501803d0601003600d00194000d02c07000d00741500c0600c5244d40e2800a00f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 729285440 1250 729284190 729284251
    0x3021302092e030b040f23090a03170414060c0406020c04050f0127050c0a030e150a022208010903020f1204150c02090406061502030a020a060c02070b0c06010320090a24030506 77
    0x1030000c0c000c2f4022410150410140a030018016100060880000410680f074210141c0f00c0e58045040440c0c01c020195040108891080090f81e043c0002e0170580300c80501c0c00c5040c007542d03a0390f100e50301c010031304611114100702003c0c00703415090000d0b0070042000d0071142e00501e01c2500080c1414040305d8405800140001c8085d000d0300c2807a1241e880d01c601200a40105010f80020355202c0d8920401c0c002d041e60031005890600000240d81c447c0789806441c1120982c000700003038008640006210040c80c00b81e0b4112500e1031075440149104080840b1584081d0348000e5221020714188800c1c0022036200c807003950503544c120130070742d0700e40c26045e6601e000d010311b14001684030048104c00526a0f07006666007441500407200c1c5692220700f0030180d034000100300381b102d5101c4001013040c0010456003000810f0700f180071040300781980010602c00d910042081500546500d01c2c030b00c002410030200030b02001044400032809803203140188e1541c500341c3e4550f00c3d68144003144082104403600d039 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 729286690 1250 729285440 729285443
    0x3040b040c050f0907080a1805030c06010f0e01030305090312070f1b14040b0406081509011103061003021c02040b040815070c0209040c03021302092e030b040f23090a 73
    0x2084482d80e140070007140c490710700414221a4a40b01c0030980c88c2c1c0942003500d4242180b0a0000c1c1d07031140100358074285070004c142d10001e0056051700d410403c1100303c0074032505683e0180381407565422885c0c0440c0c41c0000c0d81c1000b0b038000340c3c0040d2440c10311a5640c10a80b0340c13442107103040b1a03451140b51a0008400d83d0083c00e4041400d0006103010b8601170388000d800480140c00480c038150348241e2030b8144004075030a03060071040c0b48100400c0b01c6080c4030300142c001c40c03000003900710300300f41001c200e08480d280e80c01d0040c907500140c00d10505002d1900d4184130382072060195581c50712100403111340e4009103d541c10302d01c2503400e104072138000c01c0e42c0e80e807086246039214a01540c03031340c01b000040c2c00003900c15200180d9240d40070000d03072100d40301c40d041505071010140ea07401300a014003400c41041891000710310400c912008001500400e0314440d52074a10b400310715040204000390040a103900c000141a01d000c0300c070541402d0841c0081e81d00ca0805170100041c0d69008401c030b844d05403c400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 729287940 1250 729286690 729286699
    0x170d08090627191b03110d0302010e01090c05010f0302040308090f01121104060f0c020901091a130b0102010b330f030f040219030b0105040b031203040b040c050f 71
    0x203a81c0502d0040e00c2001c982050000c0640c18641c000001d003030441260003106400c11204001042c008410b00e0001010440d9074a005201c0c1795031500e91031260000c0c3c881c0d124101c1c685125040c140300750001d600c200c4130b0302c00810004105207001d00141445105032404211055041c140090007403080d03c044a410940c0249440c0d14401000001d5040c00101d5050004000b1303a050b05040f01e214804007001e5060103d95114104070004d00721501da07004080400254011182c0141c41e400e50183c110b840008010a402e0184000c01010b090303191161500030481d04807181f59507034a1f41048101042c284c001300b0409803c0000d200310a441599411841c209001004042503e00c1c81c08881d1082411810b504003100745040c01803943c410794881000071714250511055140c00092000350f011030785004a0304500c0c690700d020842c1c030140b01d01880b0b655a01028803007a182400356447c4e0800205189a980c0f800e8501032001010030340d801e944528038160042170354101039840c03010600d070042 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 729289190 1250 729287940 729287953
    0x160f06030b03190501090804060810051e090709120303020301031101020303011215020f03090307020a0509071706030f0304030b01060e010c021318050601060908010e0606280b0301170d0809 83
    0x31100f900985045a089030250b503114101c4010a400360041c1003c3c1805903035410946c10f0840f5542208c2949070042442400903010314080c4a191507200350202c0010395201200707a40b550000c0c0c480c10019880288403407122040d4504060741640254140c9200f905040072022120004980d40c1c0024020030440021070740000f004540d0b0f8115007244404000000352400e0300d0204006215002500e50780b006500c0450100214901b0081078006085d0035206140c1ea03180036a401400c038034810003a42001c0b160b002c04501652018064169407140010072a6520b503030341d00d0007011820091003100005003080d90044419840f51420098254004104500e846580e5a60000800040400c031442ca600c8015400000b0420b122090090002d5103400c89981d00e031001c0d440c295080a12524016003011041022542d1602802d601c22400881e02c00c011542c0c2c8026041c00700442c1c0c01c02c1c02c1c4c02c2e502000018810201907900d4114409007c00d403a4240400c41c410303540d5880c01e50300c01c0c9032740c2c020b10b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 729290440 1250 729289190 729289213
    0x50403080304050c04060f18090209010b0d0b040c05030906010e0402060703080a0f1d0c010309170304150e0a1205070b070f170103050c04050f040b13030908160f06030b03 75
    0x160081e64000303000f50107945204910070001380440b42145c0c003013004011042010420103070300c03880602402001c03287c24429501ca550009651700014050102c1c0c4c540c02285034140d1a10607482000154006841009100114400a000780d0422100407805100384800400c0e8140541c0110f07001d540e01400303507400c00905540c2170f911054024014414513546100d01c0b040f000c054010030a4051620700791034a042050a04d4a0038101d0000c40c040c1498240483c1c8400103844119900b2910790b85202d02e900c0f52642e2034084e03000031182c104000d90505100c84074616840100f0b02070304e02403060000e6850310340f081c1e038290b03118002d5038400b17044801104009007819000300c0403400e603040391b0300c0d01505144180e81071400e5482c5c282c00503556544100c90300d2010b410070f841803170b0b0002c0140900400c646001d507101009842c004050080c05880003004100305801954110081c001d004191400c0c01c1c0c0000b901e0030310350054400c820780c500d0004800075040d4024403130070745420b00280c0034007052541d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 729291690 1250 729290440 729290453
    0x51602120901111903090602160506070221010f0f090201080a0b01090519080c03070305100b0f0a030602091e01020a1b0b040e09010608010b010503040b2a0a0207090507050403 77
    0x41d8011034180004a40400b100e58000d01c50401004507006200c046070041e410000d00300c0ea0603410120965000b0884290381209006039003088072812108a5500c501034808a0070b4a841000920a40c201e801c01c8556106811b41001c2440e400b004800c001050307903140b001e030954030b0111001e40030940c40b90200300b030020b01e6080010010018100981e806a440340403601074580031000e1449510004c0080c800c2100520100c0d20340c2400314002d242d03982c1151900e645030b902084a600c0c0b15940c400c141440b83e00d940129140c18400203003032441a503960f080c950044c0d807050000303d209524524180b880709100411415071b010041c0c1c0100445a0719a42d540389559240600301e41d81c80e00c1d07100000703c0c030340480c2c014809480703041c0d580002e03824028852401e40da66030704001e81c43d034146201d4119a907804810740e580640c000903900d80503105d40a806020000310040b0814034600c80e0040e8007440e1002e802440ca4010507400c80c1c100380c0e40c9402c40340444000b500e482c07000413010001003020610 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 729292940 1250 729291690 729291697
    0x9040e01060e1014030d050a1206091521080d0b011103130521030306010e2e0e030c060301261c0f05030708010519180b0405160212 58
    0x4400041c0164440c0c554019034507040b1040700688150703100a004401449041100004090700103040b511400366026080d4040d990101c0308100d81b075941510560761a0301301c84003d18003000100140c40c264205050814400c0c000c1c000442c004c040010741c5582ca084a542d034403500b003c4120304292b050101c00c0c02916981c144241000002c40105400b01000d0006044880381801396500142c5080240035515118000c0f40c0400498000307410180324020007160b600942c24603207001d240300700ca80050081401414000590706041410b0440051190485410b01c80a81c4544640000510406540b00c0c240303052150031042c02e000400011000380503115408058240a000003500000700074a0003c0106410401e41c3c50305088424480d044114401c0700b2b207852030441e10710b150a220141c01c0d49018072502d8050302c0303c10740002403513041901d600040c1c0700920042980341a0513a003803018260503888544682e2801001c42d4005081402c10054440c041d0090801c00c0103200c5003d01540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 729294190 1250 729292940 729292961
    0x1706010609080c1e190806100501020d0801090914030a091e050d020f0a081f0c03020315010c0312110712030b03060103080d0605060a030c030c080621030409050106210b060904 77
    0x10f1704043c1110003100461290030103404c0f401d00401e02071130458050f887c41039461f44010f056400010020340c885500c181c14505403007060102142080e040d1401011d1002d0812588516000100e00a81216444825031080b2040071034014201101940e445a4403c4188142940701c04c2100948005007401c02c0036084c08400180350041b00ca03030702c5081c0da04102c07000d0b01158401180e00c4003408282001c0c400c4040310582d614045056249c5080200d021043c01110981889500182d40d0200340c85580c40c0050035000318030600c0806803401c491038040d00a600e0455208929581c641d000c2446481111024800140100087e03443c540f107110860380703d042e800c400a42c860300042540e03290403004198884050b60001a03015009030018101c603592145a82040fa400090101507a80daa90a103d18061014840c50862a0711400c500d1481603030f0000c6400d5040c88000982d80c2e8000d0268815421618a0340309603c594401c0b040803149508252036012a0500042900d400c0c1903022404c000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 729295440 1250 729294190 729294199
    0x90e07030f03050c12040f0e0a0e1605031c0822020603010311041b0e0103240e060306011505030406020906210a0e0a0b0f060a1706010609080c1e 64
    0x80d440340c4a640910700116025030108100107040c140d0b1040801c00803c403010110391182c2401d0603c0c05400e010403041c03080c8031598104e500030524078034240d1b0000d107052140704102c1e601180004901895601c903441194030a0152000811507034080c60a6004d82048540c1c600c04595101d02c00099004035030300c482a92800d15502c07071001a141c4000a5000e180129004483e101c0001c080106848031000b1240f0005207070b008001c503950700308865140228007424003040744a81e1110b100000b044510031400d1607503030f00100003895100404e486001d003b096050f1800c0e0f81c0c03501c0400010000b42c0c008440010b00410004000ca40306502600c00350070010603945c41c0032008802d0704154584c40310600d40404019041c4140c0e0b0010b441032200c0d180d8480064038041000361601c0d0a400030051290540c85140300000d800e507660b000341d0748060040707801800004184034aa25540c0e160901070030300841c0415402284141340060503520900b0000c01d81032442050384049500510594401030b0032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 729296690 1250 729295440 729295453
    0x80301050d08070506100f0902090102101d010203130303050f010f030206070c09050a0e0d0c0c0e04050a0b09010c0f08010b0304061e020a05071104021242150f04090e 73
    0x4505001c01030103403400d00d1040c0382260a101f04000d01c0d0703206a00c4114113500c1044000c1c0300ea6008142069285910704000802549154000c0c0078050503000400f01940b00008000c0d00d4101d400c5000f40e0309000c0d5a0800480d55083d201a141c0c42c001e016600036021120340030001460301400a244d802d01c1442e4078003406554210a0b429a10256000c140458848080c4640c1000400010b1840c20403494454904030081c6c0f0340c5224049031b4050218220142c60020701030050030800969002c0d88141c1c4242c80c1e1070a003074001e0003000b41800400001c0c080790305242e0524400d412290580d100e40300720a10b5a140c56960b0b0000b03103070001703103040c1a81c41002c549421818a102922803885507894bc0e507602c0c1c105180030003030070b281d540c03410340b28602c1402402c0c2c8180c2220765050740020000c6120008000440c3d00c2054040300b11820703402803003176020315100320441ca080112480d00c141c0d54540b8000880441382030354060403824000000d004c3c0403c1000440ea608181c2d14001002c1c00d0f07a50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 729297940 1250 729296690 729296693
    0x30a08040602010b1014040e0c0f0301060c0c09050408030a09020102010917070b0a0509030304030c032c13060e1306093804020616031701080c010306080307080301050d0807 76
    0x4664119510141c00360750b55040c90851030800915035918901140340800701d001040450320107901507402516200c980842c000b8140720221412540c00d08014840d10b610703903030344da00010b00c4801d42c880121010070199030000764000240c0103207401150300c00007160442c0e694503003038001456040f2050b0704543d00e0701c0621000c1400c440c01081640c1c800b0501d0396482030b584c288084822000340817034100034503100401c01081b0021065035009036051400f41422019400c0031561150584402029841d1440e030311104203441030128940e000c3c003540e01407100c1d1080840354046030304078410b01407003405280c0050b100c0148405455200342c801c61000030100d0030380d00d59014a039a1905081700320400807100104030f00c0c0011031101c8030401501512036500d0298041009805207d1010120210038003e441c105800340d07103503020802110094010941c0d407002d03201d075903100c3c2560f030070b01182c9040004201c4420110880e602e07150060f855a2440c0d01c4d02d0300b0300920310a000002da5100c00c06206200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 729299190 1250 729297940 729297953
    0xc0f070b010f150203090904110a0305151e043305010902071a1005011d0607060f180f020d050309060d0905070b0703021c02070503100e060c090604090b030a 69
    0xc0c0038102c03400d5181005420842d00480c40c030b40b100c1e0b842c0190340c4180300700741080d81c8941c0792652040e803101c118074a0700c0120010524030301c0301d900000c1043c010f80b003c001064540c407a0580c8900128041400194444031150503d1442640c01920b18055180400300341c1c400c030a10807401080721600d59403010b10000e00001112020380000300503a40008103201070050704184c400752070001b04c00340c032079505081e44040301d1007042c2e1281a060103ca0195003442400020418040c100040d080650b02d00c41850f140d001041074111012001c1d1821891100d04080e11204c001c80071380c4148003014540741074003080b812400c50101184c180c80108100c0300c0036110744020b080002881c52003c6000d003500d19015007041c02030b410203640500700388141d1020940c00603000d4904004032440b00003000c1084d43c201d00300605070f0031040d0984680703008044980c400d40d01200f07003030345804250b4080751148003081c0410300c54140030a41c021000e00041c0506000c645c09500400001002c0310103150881c2e0702c1c0e8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 729300440 1250 729299190 729299213
    0x337020106030219050310050c070b07050d0608060702030f0f040306021303200f010c0507320d0c06140d1103010303081b180a09020409060612020903060c0f07 70
    0x500040c0d448450030000c43c03c1c0040c1c1d070449440c074800002d0f940340c281404240d0b9402c070184a410b11035154000b05142c41c040314101d51413190450741e24501840e10a601030080c1c1d1004515501c014644540010401c030007194603070207a41e4540c0a5407502e0b40e0841c1424051b000320412441c0301d20204400000103020303100814410581c7c5031090445803460600803903026142c5021000500344a072040c115603260300144041d01c0b800d01700740c0d150300d0460a0092810003144c00c03080e000010a0080060f40008480d10700b159043d8030342c04980c5810303480a2010042c0213820040c90046450020f008090244011743d1110550200c010f08100c1c000e5100000c2e10686640c03505428000801803040c140d0124401c2da1011007010740c400544001610010f044c81020640e23000800318406903d0950307184625580284030314507044d516251240c4400e00101038901c5030f4004101c000a060040280e18001c2e00c140c07800040182c12159501405030880b94401c0c0050200c504040085000003444070340708 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 729301690 1250 729300440 729300547
    0x150c010516020d0504060806011b02090c090f120a060c050f180a06020606130b040e030c100c14120601090b07061e06030b0c0a1803030309021302070503 67
    0x51003010310a10806070810341040c49000401c1303001c10080c040d842e0000741080e0411020302e0140502a24104038404413540240025405240306040c04004520f4002070400048100e0b004070000c0000c008000c500d014107018260290050450780b4041140c41d48601c05090381070408525081c010b10f41e81d0314a130f115140e5202c3d420342404050015040643c0228050710190004141e03504014000130007c0112404130b804040d250603101071240c030345400c5014841c0d212021070740c44010b400c3c100c944404090185498247c601240d80107414850640041f0410f100b40003940f501100c40207407105682d0080c407403030522001c0d031000900d180000d0001d0050900840380000c010284c0e28029406032190705c940da0000382000c1040c07002c2107a91680d00e4100030010311150796208030440a4482c0300c06240718180c0817464610010505800d9000202c520f40308441c10f04400190300c01942c00c0380155032019010b0fa10600a800e00c0c202088134003000080040b081e840304e20240c4443c1c14500045105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 729302940 1250 729301690 729301711
    0x304051912080a0c02060a09020a180614010e060f0d1506030e160f0b07020a091e0b180a0903180603140108070b09060a14040b0912011a150c0105 64
    0x10780080c0c10b0340000340e40d40001c00b43e0024400708465000003540c0d001c01804200c1060364a0b81040119070f1040fa000340205100702c8030141d00f00c4051412002004035100300449680d8085000c074040d0b10400f9030300341d0924000c10450504074000c511102e160450008040c0c02543c81242170403921444003c00010081c1d43d902180e800c0505640a0030400184014180260b08102c10700030900011b510344d0985503640c0d821900c40d400d034000141140c2d410307030041ca03086290014452200310080124004048000130921a07042c05e81c0912005404440d403207213518560b88003261040b4415000011401c0c00303803500d404045d0500e40340c41d90007040e5901030350101e91345000241001c81c420782c4250040946d44050318040d0725001130b1100520480c0307461441802c00140040c0c809e40500d00c1003007562814260315072201d4880280d015958044180c85102d180e0700040000d40c070380d05010301c0030340c0c001030354401d0345500074041031025084450005581c90b07c03051115003030702c050900c1079030b03c035203401507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 729304190 1250 729302940 729302963
    0x5010609060b031608012108040504020711151309051e1501021203010308071106070c080304030b010e060d0602370905010206010608150604080102031014060909040803040519 77
    0x4107000c1c00b07002c4c1c00085002c2c04026401001072480039228480000e00a1050711f130900460318020005214581080c0e50107840419040140640c0355006a030f142c1060b0303644001495115602043e03400384440101826403000d0b01031201400603002a90800030340d1090415500503030300c251030311000c1111560304c0e00319031440c41601583e04010b0000c4415420020901d994156102c03241c1070f00c1001d43c00342c140c0040c10301d00c1e0140e4649000301c42103107400940c075240b080d80b40d00d0100d440ba4800d10050762060014400494040181d81200d802030034028180c003c158056910000690050041009600c40000405a07070b04030481804100080100c070309421089600d00142040d400750700300a0441d44024010700a4a80008019400080b110b030564040e07a1007100180143c4200d801214240d4008014451020b94094008050302c48101c160004100071000788803050041d00141688042c5a0003c10b012904400003141c0107400b500075507650088001017840e02c1d1440c208100c2c1c02c2d14454 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 729305440 1250 729304190 729304201
    0x6081f030611092d0a0e18070812071208010b16081b0a020310180318030c140307151409130c020303010311040b100813050f0c031b090f0405010609060b03 68
    0x11515050081d0101c5d86040715031300385034114025100080c02c200c3c8411560314082500c4c01d08000d8800204030b080d0445884800d80c0d0040401900092000c684101400e8041002c01d40a0a5528184c0d980207003424106200203400740e81c40310140c541590b20500c20080c10840008142006003120801c20080c40000c41e148103142c035243c283d07044095003030300c1c00d00f40620700c00c0e02030941901c56805280c401001c8070783e1003155440071502e40c8014135601c4808000141d15910031801c0e0021202101901d1445580300030311403103050001000c1000614842c2900281c42d10403010708407003070b8080c1c024509200b44150a208583c1c0484c0c4603030150f48040010001c000101030b243d01404002e03101840040311100101c0c0184e07407046c540300c061040360000945140f007504d01482c0d4440e00042116407419240b646541c559a040c51824040e014044441c1402d5000214645040c40050542401031b6996510902c0d001030103041151655207507600018000507e01840c0d010303040a03a0b8643d503e0412 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 729306690 1250 729305440 729305509
    0x10801050d170d020f280e0927030c0f07121211010e1516031e052505032401020d030f0e0609030406081f03061109 51
    0x1603210a11503681a0700c1440010907481c60909205070782901d076916105141108030280c0600c0c0c21000d0b01c2103021a00c0d81d080e01c0c00c582003600141030203030144441c170303483c403003c0f0307108400c4025a640008030f034001708803d00c2d10361404100d50743e0b840c40c07480e0108440d500c19074210307130018030090025800050f4502c4039440511210000700100400c0326039034900c550711016042c01d0458044184070b0390f051a8251a84c0039048501081008400e603078003000c155215221004003610800700c11000440401d140030301910440320f000c2c040c860061034a64250080c10003510006085c4d40c03021050f0840100d00d07110800c2c101000c1c200075203a2584a29090040200c1c04200e5800c28642c041ba4817031200c5036980100340c01c0c9034880d151030080745400d6003e050310041c1000742c001050a100d03810400c102214044003820a03544682c0c0d4018240e00d624010682d000d0741d045100301c403244c02d00420070001e129030b40034024403a0315101d003d0a054420700010f10031000711892140040144c140310524024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 729307940 1250 729306690 729306707
    0x708060f090708031e090d080712020d050906180a080601030309090c0e010e1302040b040f1d01081e16230102012c07031e03110a0b061e150901 63
    0x4848015418450450809071704407118030108885203800181064039a202e4280140c0300c150011502c550f00d401d18605201c27400080c169010043c01400080d0314114400c60498041d4034009254030305114490581181a00001c104250302c0840a40002000d44e418054a40258005d4aa0080003450f24041a040e80c140c146070804000e00a015040306030f0b045110001054403da0b800c180b00503272240384100902c50358002800300071011400050f0340c0b03c00c05084041c1e034078508007011036800388415030306c008000707008843d201c0e0820b69010180464010080504645050031280340c0380d500a8200c440c0310407500840d55180c100d0590540b41d0803445404d2489550a1000b000005180c4020341c45031250640f9000d640443c052008004e04420011040595081106c400754214041d001e055800d84a09049002c1030342c29030010104000840c040700e4030b0341c002d83d0391074455440f40c040000c12035624000c01c001a0510b1603040641d1200b0704114910b800074003041d603a4840c1c07603001624407103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 729309190 1250 729307940 729307949
    0x50601060305011208040314010b030714010216030b04022704062f0a05130504050a0501030b010b07231c020f150c0a2a08040e010506120402010f020708060f0907 71
    0x1c0c90060f41c0000904903070880b007c4a4110241800700c1210316401409000402c00c850751521542e40042140200c00c4480704040b54240c00316150b410045546007421802c070703c40900143d41d10000140035042618a54501e48140d0000380d05814002911011006068500780d40d10707659008229246412a4400c424855603460740d03e0b40d096078100304008a10a02d6032450070404003040100030034601d01c03880005804014001c0c01140751820343d42c8010502480117660081411000140c1c42001c0703400c40d440c90b50401150308480e18901e80404500000c0e1030000003d1149c50301e8240d0102140d071480c0c942482950151903180071811845180c0300080043e081c42090300d80500004c200c04c1403c40f200340d84c0c1d9090140c118800003155031040d01d00ca508030f0362003d003d0054142040340c0b10707000308255003900302d102d0000d07601d403014803056000d0309105000c40d540000215026600030440c111088020744101d0b10707a162141000b40c100b00054a491f1200d0350100d0607c4000d40003444010041c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 729310440 1250 729309190 729309209
    0x14150109020c07061d031c02120c06010527090c0f04060f1502150906010302270a1a0d0f14010b10032a050a080105030304060e060f090d05060106030501 67
    0x40d1a1140162210b074580b04d46003d00c01d1000c50310000d500352155031403000e039000782030f2181031085002410002451603030b20001030103050f440e50384592840081c0c41c070000c170302030080205a0a20080c1b1030b180c04503420550309c2d480c01d10401192030340c1a000c031500c2a00144040c1c1a00c0d007002c018042c0448449030b21610460400c6014426865209508400c07030f403210020f00401115003c060703003001c0d014841811079602c0c0b08104440c40da000240c441c100d03031090b1400c80070031a10801140d5000e41004001108003039903000f20382054540d030460402c80b0041d0200c80c162420030000103411106910007111105181c10342001800b00b0782d03000b0240380c1000070080c130040d403941d0005940401102240342c1419515031080b0300310085440f40c1540e80d10070168001c903040c104c01c00a0610b8000d040c0341da00040c3c00c1b05c004103140c01c000c001d8800325421a240e0201c800100c00401030380b030b00803844003885450140654103499840c0361110800501609c00360043c0e504240d40101030310f005810401c00c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 729311690 1250 729310440 729310447
    0x1c060e01110313061806060815070311030c0c0106080715081003331109280603020a0509030601030f0507080c01020d0e03010e12040f050d020303180a031415010902 72
    0x1480c401e0852000c483c0d80c4040d0000b51a6607000326104828049940509510300e001c40c041043c2000103081d80e8440e600b075500201aa8179480d08409861001034110600d040034400b0032903076812980070384400c15521001065198503074200c21300d007070312950180402c20344051010a402d0742211220360403a0791980c42c5039820341107850701c3d41c1d8408c5403400c1945041054194105100e40700c8124404138101010912804c82e603460444020341168403094491082c0a04004000741d01249540c80c41d0710046401009a152520950083d0456048002803010070003c13041c4954042c00081d01a61041040d0042d910700340c200176140c01e010740c000008690140159065507038000840304d44140d40c501d40aa1007401082c0401c1c007600e143d0351148a030f4410501c151a00302d00100c003820556980000c01c0d03050b03995880801c40d119400300e0303000e905604200f000861a400303a20301707040c04403005031072944101e55aa440088050304000070b1829500702d1140301440d10102c8000c2401800202020340c01c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 729312940 1250 729311690 729311701
    0xc010f0c050607050307050f0a08150904030e120a1e061530060c110c03010b061b0313060c0605060612060909070b1324080a02091c060e011103 63
    0x40e500300207881030f0300303002022000a00700f911407001c44800381503181076240c031141c0c200e5000e03000352010758179000514003825200e600e90400246503445a81c150761440354600040c420f0000500000131601541d0040b50a041e010901001c14421030b0703075a031046516100e0007030a01c070701125028076942d001c010400d40208645200c0d0700d0b00411140c841448194501c1100051418413008039100412950916200d08203254005490703044151442d01941d001c000d41100305801c03a8096000c45034811000d01081d184e0200104000d2908139007a811645000d0014080d030404002c5036101100194803c84100c0c01c11103a070242540294040d1207990401d04090344c134210803040240200e00402c1450006000910104408002003150840099890005010f0280c440c030580c011010a0503102e034052411840820041c0c800d9101e55039900d040c3d4903034a9180019501610030b00354400903464030168400f5290540718050307032180c6400242c10098042840c25615050004501c4203001d004100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 729314190 1250 729312940 729312943
    0x9040e0c0a0f03050d18030212010504060609230402040b0414041205030112030c0507030b0a06090608070e042a180b01020c010e040c050708030c0c060f101203020312090c010f0c05 79
    0x120f1229440c100381804003801d1b0300c59081c0c00090352019500020600c20b410b60302e441988050b004034007032130061054513294050501680e0158901c1d004992059134400300740c81800c445550483e10050012410294a500103411350b00b40401000c2080303039003001c1c0b02c00c01480419200c00c410403230806174110f6241c08074016001e644850040d09101249051104004041c06018040e40d807100c1040c1103403c007a6000030003030800c1d000b0101e503a07140001c003048407040021404100d0384001c0c4038134000c0c2c1c4d8035510002d40c04a052a40d080001c00340000750800740d617076003d600142094244186801412205076000e44841800090554101003407001d207990b4854030024089406480200e11503848076412143d40c483d030803020740001c0002c07040c0001d100c5100010496040050200c455644681700340c00117081d41034880d642c031200296070400a6000c5203440da00101e020340103a03030400c03600b10000c3c0e807040803c840014503900114485441903801c40024001c06991b450607104038000c1d0358078607 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 729315440 1250 729314190 729314203
    0xf06010912062d0b060313030c14060403051201090506010f0810090f0e010605090c0702040c030e1903030612020303030f0a0b1c0204180503070204050c09040e0c0a0f0305 75
    0x3603800c009508020307400c1c8941d0b0782080c0d014240c03800008240c0c40c0c0000c030303030004801d28408000f0200d05103140c0e001c0601d03004060b41d0180c0722602c5c112003203c9056078143d032504c0110701d048038545d00541e8887c15084051201c207104600035210076603103c0c4440329000d195801604000b150902c0e060900000e030364032040c0740b500c0200e5410114410740b5508190048503205a1040801c43d040075190280349000d030708600d284c501d40c58001e0010030740315020002c1400c1e0480d24100700c000c0601414025180c00e03003040d0161016070400150038a44031007414105810110711009c01c010a4501201700743c2e05109020007040143e02c2528010040c0d40029201c3c400030b880000c0d1100d1000200d4140303c0c06611904400d5401000002010044500651400b8a0307040c00da1140d8500b505840c42e52141c0317480c0b441e2443d8010084e601e000201e0b400c01c8000c0c075002e81300445003101030000601d10780760380c8250514020601300034a14182d40300c00304428207a0380c7c0c0141d181c0314502642040060340020f0310 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 729316546 1106 729315440 729315449
    0x30207050a06021f0c03110d053103030e190b090606030d05071209091a040b1807080405100f020909070306050a0510050c0d11060f060109 61
    0x60340c40e44001041c1c034110040040b2400e1213035505501100780040035040003e810640e203111a4030301d4100c01512150f00d41d81c0c4c001c0c8450882d004c407401c1c51492045035058010b00702d0040c8400030008600c40102815201c8000701c03e01e000a10081d00801410450003444404c117040229a0f90310a44103904a0b0185401182031800c000c07410025041c01034071242d00d0a1002d6813000608280400c0c040c0030803040784408290714601d40150b8203400d0003815a0b10a00220004010803640c3c42c0340c40301c0c40b940700210340f429448880056198000e40c242081c2e083c90b55241441401c002c45102ca0790046842c0807900742c000c2c00d49602510300c68a05aa07600107603030b2401400d90483e091405000d900552020003000649410380c8006074548541c9021810a00151420f525106602d60400c0101b03030b40001d0003000c10f008100040d404442da041044c5e0a041050018004043e94042d = true := by decide +kernel

theorem cover : BRFrame.Cov 729136690 729316546 := by
  have h0 := BRFrame.cov_init 729136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 729136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 729136690 ≤ n) (h2 : n < 729316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
