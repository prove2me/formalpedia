-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5186
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:01:51.757853+00:00
-- url     : https://prove2.me/submissions/04ed2930-b7bb-4cd3-94f6-71795594ee65

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 932553956 ≤ n < 932733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 932555206 1250 932553956 932553961
    0x40b040b04080105010f0b070b0a0e0f0c0414060102151003080c010c020111092209080304053f0c0703080c030a0305130f03050c03071a010e072a05070504090803 71
    0x2d10911913503026180c214007540010345400b02044442c415013000800840041010440d40c034490781000c080640090309440320034480905081d80c0380300012400d4480d030306200c02c1004203400b1044031f600414042e40a80490105507503c00340302030b4054846029804000070010200c1d20035000f4092840c416000440c04d0108614020700307545100c22003603640d40041002001941e500000d8030400e80004000b2055000400b2441008143c81400502003c0e4000100b000304030000c00c280b001c4060355140c0440c3d07512020103502c03645a0382e9462803940e60100c580826502d00200141c00c8a441c1c0d00d0489131415103a03610b6160a07040041d15141c180c1c400f00300b50310041d806014195012000301908100214203859a114881d60041c000d402d01c007001440380e413019401d00448401a4004c08501c003501504991000c7c041800d00c94400018900c201003030b1160302c1881480380465a0083d1030010341d1a900c040c08403520164401c84142c400d5100008858a85002d40002540140b116640340d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 932556456 1250 932555206 932555219
    0x13c080108101a0411090a330815030309191503110301050108041707050604060e150f06060c0708060402010e0d05060c0d020d140a2009060708040b040b04 68
    0x40c101c45a001c0c1c10300f00070799003105182c49110030407440b508480115140d41c0329010f050551140c00741c01900014811800300d408021003100c503051200803c402e00100c00110021401030038a41c45400000d2071503030204004000385e440e98002c0031001130031f0324a07010141c00052601401c681c441040d0018040040004080c0d4000c4003440d114182001c0c407040d102403242c80690302c014007503981070024140c0810b0610209d0014141007403e40f91309150364002c117040039690b4002c1190101d0b00305040c0f081c3c82c40c90030004034508c400c01201e8401c2c03032040e489804454281110042c001600100c00b4801c8150300300b0100141c600070003061340030f0311031418140001044018120f00d00fa01614a04001d04c0005100084203075200d07400000290322200c81c00c02c000f029100b0803003080c007150b0400c40e0a6552103a10003003580200d0358980100f00103d80446c1011000d0b080b4401102241030030b10181c85a030800ca0014a0300d244600d81d0646070a031154518a0319800c0f98200341020040454107100c030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 932557706 1250 932556456 932556463
    0xa091515020312270d0e0a050d02220b06040f0f0801110a08130f0b10150f0c11040908040603050a060521150a29013c080108 55
    0x15032191016500e0004107010141240030041d103182e84956640780030b5541910f0040e8012208a811020b9070400c803880b0f04018100c94030f5501045c4542a40280080c483c509a42441c1e00c059016101d040d4080c428400315607108020003200c80c2c4503459850a6480f03603655001000034001080404d5011070910300d0507041710306550051940da80c0b400e03002001598444007a21007820151900c8981c50359058102c443d80021241c004010100040004040040241c0054400c0000040b690655a6121481c1094984900303500c3c0c040384d490303182801402c0c81040b41c00441030046605441c0407180b8000b2034102e5014040036100c02002040c10311030742e40d140c025990000440e010620009040c0380016404d211001c51200032254614480140e4840902417044083c00c40740b00703400e591504850702c1020780202c110031344007903a29025103ca4015240601d010f50003040e03499150940040c0d40040090928182001504019410745d2402254002d421103030070400366124039565140c450054035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 932558956 1250 932557706 932557739
    0xa140606070201090e10030204360201050901050d060b0301080c030f0105010602120a170702011e06080c04021c020c160501020a03142a0c01090605040e0112020a0915 73
    0x2181900700404005031307a001440e107040d503520b44018030040e2a26600b2141d0200e05601c000e40042c01c003c20040101d108003607182d42100c01d08041000141e9964600e988022107100003804280180002c1c102540701d0400b030611204100c0780065515100c0741c0d000c80340c4e00241d0140d0a03640c400c100038255030800744000c6502c0000c50707000b40015410040b002c0d480303049044150302d08620100780510400d11a4513001d80700300342c3d46000a641d041c2058028060442e8000c100303c10b00032040c11000031403d070700c50702c0111750400b0080d0500304451400c020181d840507403460381c40170b64980308046e64002d5100404086200c10b00030440500e2144540391403400d16807200c2d055401040440c40071030340250258080c4030003404050707038a00030703441c1040003011240b9a9159600c0a0351444c40002000603600351500c100f601d50050041c1d690200300c90310710613030089410750040180104442081c4c1d044058030a0710050003000955296014581150001d0b8035080381c0d00b80f852020801a08052036404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 932560206 1250 932558956 932558959
    0x20d0b0607051f020706020c21120a0c05070c0b040501030b091e07020709060609081605030d0c0203120d0504060e0d05070209180f15010906050d0b070207030206030a1406 75
    0x508224280d15a80c1c0c568112a0f1074455070003140c1c0040c4260035195044401c100d5100d44115214004038600d265038000c1c000c1c903601440d01080c07000c0351268203503017aa02c0b0759426980000c070703642d111030300000034041050201041c82802d03c02c00001400400420016081645003251a103181000060a88030703100b103214064410f05040c0f0082d0043c116044148181d04000000203486100741245400346960005025500d8004042002c1c0d5000400c0c800305c07104402240ca0a0b0003911005050842a21031680e01d580005483d443c07550007580b40c884080c0c002000c2d150240c3c003000040109511540a03030080e103940303400300010840f482c03207041c00d2480f100d002020004945c800142c0345115444019100b0540d0100040902c040124000800c900300410385002a940007181646e41820000309900940d4250000c00d00c81200d201d03503000c603036008040301c82d0b9204588440b10070550141800307045001d20306001c00582c860344029800b0f00071403080040c0007084581d138603450f03d80c090707c2079 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 932561456 1250 932560206 932560219
    0x709050d0c030f0309270515010c300305010303020f06060906040902030a02060d1e0b180a0b0915030714060409150806070c020f0d02011403150a0801020d0b 69
    0x100441c071505411020b603036102082204582c0582015592000e0507030000c2e100014502942c800c5c0301ca28922110003030b0707020341e05211544568860b03074942c0c1d01c14920301c0d001a101142ca4804901e07201d44508110200d0028640201b10085584044078070542c4080003203078540700100101541040380c1106484000040c01c56810900006401140060a081d1040d03844034680e200359030301802052a0940d00a0041d0754a19201d10a2000b4002c0c000003501c00c07401130400b480f4502d085010707a07041d00c10024090000210302d40e4901c40013800207007401030b07500c1e650100c1070341c0c82e2038010101d4001c01102c01003804001000082528229503130300a0312518400c1c20001c030198403a01e090b0740940e8203a850100795490b103000ba20340c85c042140d11000085c4120000c2c07010f2190010800c0342114000d03110300c404402d6400a003c1d60204403800280040c4000e00511944020b480c05550485e814070f0002c0a0207248000082031800070707070001c113070596000450a03d1540c540c81a2555540d00341d540c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 932562706 1250 932561456 932561479
    0x12090c0e160e060a14030901090c0f32031605090a141602011b210501081015050d0503130f03030912080405040504080903010f18140307020306010b03070905 69
    0x41c0400d0b2030002983c050030000c1850103c840c060b03104d4110390418140c6107a201d1401d5040940680107200c42550752481c031101c00b04070703112103004031002d0307520100001402d216206d11500513948905180640d580e000d0b04801d10719602400840006881c42c60046007080c2400100000b484003d01100a0649000c1c00c001c006040c46079403960104000d404290301c540031031800e1340034040100200851103004000b000055030404c003086400850b59880112541440081c00200c80342801000101d47c00a088184000b14940214500324200c100e440e03070305e03580c4034080395180031038502c00c455680002c80c4014182c058071200c10010094100881207083c6183c130f0240501e1002d0158856413160407d21806205841e03040310300411010f4400c101c0344c40c1074109103245421140302e4920035420b00e201050b018072070703008028990711000c42c1800c0030f02c51946d5881900b56010200d0340180014040c0c140581d03014440507008110b1900210b54034030b4403040040001d035007604201d1049216008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 932563956 1250 932562706 932562751
    0x9090606030601020a03320d0c1809053705061804030507110604061d0301051012020307080d0e150406050a14070c08011a0a1a090112090c0e 62
    0x20b062049940609201c1c5828447d0508501b4207801108640c00a81011455203818908a4014201440501000c01c606035010380122503e4070209200341d501c5103020024444441d881d404242c21003d0f04004031001250301d140e01e01c5006400c0c1858058009281e0f0a20004240e8001c5580c0b0250485405410301c1181c000345604010107070002d82003040c00310340350080010004404141140007440c46481d159540d8000b80081460011600b0070740c5902c20711100f6040500405002c3c80543c0281a20315007000d51401d00c29070f00e070909030b80c1440b880d803002604a01c244a403a291712800e55900d021030001c141070212a4404036600007d448081208000091f40003003030b64010000ca2510644400140010382c030f01d4051002c0140c9034500c1c40200180e4100150301c0414109a4018240e0010b200303d0100600252907100b840b141c5440a0440e80800100754001c001c0000c0504001384100c004566120840f54a180d0407690b0a01251090281c2e6890103046940600450312404100d0340c50074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 932565206 1250 932563956 932563963
    0xe1e0717010207170306211f050f0402040b0109030602120f070207060813020a0503060a0905061003081209070b040b07030e0f0d0f1103030a17130c0e2a0909060603060102 75
    0x1301d0080031000210204203955120700041841d5107611460a0009000d05225502c42e49201c0030400c00560f0a021412448001c0c0180d610480c80043e01821550710743d024080642854881c0e1750421044400200c0005d41c070344058910103034984038800580c0340c0300342c64688400001d01100103650140500b0041164000c0390250311290030100d00800c441f441c4041440c0d02c01030b401540e4103004c2d14080008050080c0d100b400002d003d08100c40c4140c8800100e481c0e24403140c08080c203480d00800107088085921400759400038554000c54003000c0d902d4032011515005600600580c8000085420503d40e01c01040a00c0070f00c11544001c041d01000002103540d90300d00e02c0146541c1252042a0030b00068500041803100090150707940c810200c200285954514405040b020030200049400550031080c6981951351106caa030050a05001045c010340c4401014401c0c803404240c40705006034141d501039007001c1c0030203c05545442c4032104001054100419580c0242c9082c002c11043da81e001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 932566456 1250 932565206 932565233
    0xb040606050922090b0405030c0c150a20120408010f0c09090e07050411040501031d061f09060b03160822020f060a08010303120501030c090e1e0717010207 68
    0x1c2050f0800103036805000c3c040d024800d0301130041603d0504206c28403102000500880b229941910105c803590340400a2031139051250400c480810321243c80341c14020005c0b0210060301e03000000021800c1444280f51100041c000003090308003080c06c2000c040d0901491102480c100c20a00598041c080c0041c800b00151044540184c7c035032000b40c120300703002d018250103441c0c040e00910401900340c52180c1c20740c2c0940310b0b0a0000e850001b1031400c4550003d500700360080300e10003500460322100120504402030004828540c1201c02000405200ca44a00c000400300601d030307961240740c080c40b13090081040c42c0700362007072220030310402c1091000c41b111012488011401039044d688a40045081100c0b01c2c0c110b5038025100048001d012900010603a041720700c61303500d50281601c03e1400c501030b02c00a110003002c8080f001d909001082658100d0100400f8400031100283c0038207522110709506209881215002b0705418001d005150102e02c04040303050700203500e016100e0360741500d07a4150 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 932567706 1250 932566456 932566489
    0x730030225060905060a0501140a05150c150a14010e090a02060f0d02030103061406060f0901030b0d0f0c060e010207031104020f090a0306141005010f0804061508010b0406060509 78
    0x40c039000700104050341d40000121a00714045801900c0d144c50840c00520003030241515182e4000030500607403416046032800d640010f054090940c5c0020303420089908110500c191031b00500400c0800c2600071000c0511541c2050030115a0300100c1c4d840c0000408180c10076502e4000000400000e00000070701c2084c000c0c0e065802a56400c0c1c84a0b000321640520440c0d21aa903000100001c02d010760390b000301c0a00c068604041d07802d41ca4140070480346115402c0c103400b0780341e01802810501d43c040e51103600001d2001d0504070004545959000030701d030000c80200c501009000003030090325071064140c040c4820038001000030740d08548417409409d81611603e803203550009000900b15119a069900040f4017a2100d031006480349440c4015000001c0002484500c24001a42510b141110082110410385603512008680c04080315000c0e401042030710081c2e141c40030140b0a95200701d144006003143c40c00040c1c0300720101b0030801501c03c581c4c403c0d0100300040c070421250780e9420404d40d884881 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 932568956 1250 932567706 932567767
    0xc12030f0c05030409060f0e0c0a1704030e2d010e0604090b030c0406081b06040e010302010c24090201020705030102190c03020c030703061a040e120a030207300302 72
    0x707103241c800e1952203560403084c1418101400000c10b1004140f00070152002030b116400d26036507066606006006102101002070000644025440c00400f06150018007901d45468915003480106100102228094072140212426242031403000b090f869441202460913400e4050480c0001f070b034070300880c018040b03140e995811889490794100604801c4c108080c00900000760b6810889407030704452948140403540c070884500c09440e0401c21201a55000b03443c44d00203900796001180c550340f40c030008407485103490701d2400706600c03900400000803d01c40d50110b40990f00f032000a00b440b0056001d140039a0040c00a400704074800c0d1600084010140340c0300d05442c03d035050807450100103000ba1901030040320f10100500c03100e500500c8000e0201803418445984100602c0b0032582e01c0a4054944e8025031440c080c01d0310344100a29203031146207000f41c1030001644411054054241c003841d0215401c0e05545016060004554481d08040c1011401e050340441910540b05005403480c00030503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 932570206 1250 932568956 932568977
    0x3061801080c0402091c050a120c020604140105070609051b091e0c2205040b0d02010903060c050706020c011d0a031d01030f051302130e0c090c041d040c12030f 70
    0x11181c0d160f24600720311040da00c142103006ca05144e500d40d90442c0096900e90310080006080e01e002d04c80e14181d081e8044c4c001498541b0b4441032008840d14015481c3c10814204000f00100341d071802400d00c014014006414103903040d1811401c0300360903502d002e001d4031180e810003d4444004644880385800c00d04c509610b5501e050710100c0340d1084e041c8210440020480807468055075081d12010f0722001c0d04c0810880810400b0060a035080b81d10003030000c1d1018100340001026074028116081007801e00a042041c0c582c1d8041c142d80040c0006403a5a42d10484034048410860800503000010b03c0a84590307541a10020300010440582c0d808600300c8003c9100305910079802042600c0748060100400e00703100d4448101c0701d250603016480340301440c58170721200203548106810400040d00524074852207800f4480881c000514800c4412801d100000c0d080d10041c144240311903844034091083d01d0680b404000004058008500604465118000181c2c002461710340340340c05410141d1501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 932571456 1250 932570206 932570209
    0x60a0513110f07051b06030408031605040807061d09010f1403031b010b010806060a230906071514070509040b0a081f1b0c02010f0c050a0803061801080c040209 70
    0x80c400c0d07050b580c42624000442d002070000116003150a0704110b03003810303400043d6604015850000342c40c0a0034201040000c5003042d9108001504a45018109103003401d541c2c5c0f20190620300583c1c880f002040404a1030403035105000f41c00c40d003070f5008451180d069410245040301c584018003944001200e20320703000c0a00d0341e041040c0e030480300c20303070b415014195920102c55011b0a51070000307501207603520001c14120314000c82540e445501ca607a803c25403140e2840344800d421025608599400e00c03c000403040c2d91180402072100714061014050060211203284048601c030b2100541529000401d00c00007035801030440e141401d0490740403840d04040340c002840180346038000700042c8501c9240714845038180c00b074a407072203501c800c040103c40b15034041110080000911a000148140c40c3d00c1c00640c00341d042040e00000600d4021b007506060340c7d035245800742480042c0c849620100c10081185458929802203103140c01c01e40b0a65403400c81d40399509d6590181c8544644e07008504103a0f82e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 932572706 1250 932571456 932571491
    0x1d0a0317070e090c0d0f09080901031d0304030b0106140405090f0c16060605010f17041410050901051909020a170a020d08070308130f3017060a0513 65
    0x549030060084502d0704002c040b092071380d84201c4e60705000c80d0a086003c00e04072064850702d410a40c10000c1e4a1410b018480110020b0081c441110508150741080b64000035081020384051441802031f0841d550602c5e5018019101714100c40000f0705041000b48500d403550146550800e24103803003041151500c1542a010303020726040c00500020800302c5400f40700564104404460081e21000801494040104d8101c0d800c21240d413a10303403c0701c01040006200f091032000c05140d44d41030b160140110022001625000d1f5030781005a910380092040d800003100d4001d40b841071000c0200440240381d800305c0d6040446220b030713050304401d048090071030300804d001d031b044010b40c000d0250750300856a203415106900303d4181900011644400510b826591801101060340c1041401000729095038079109880d840d8400d83c00c0c24003040d01e5010314004844124001d0700a240c40740000e00c06100254841e02c0c10041c907240c8101081c80c0d00b008140c5451004034412507100c40301060400301d00108881 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 932573956 1250 932572706 932572727
    0x30507140a03021002010f0c0509091914070810170d080c0412081c15030609060219050c060a2d020903070e01090c05041a030a0e060a1d0a031707 64
    0x100180c55031341c00c0b10250790640c801180d010b400b000820072080319808c2100c0703d001c0c80c460176401c600d120b00407c81001d2280b010404007103000e0307408141c03107072000700207000d5041c196040e1002c940f04005025102e503034103a844001e01026440007255450021405940724504031420061103c11004260107504420031078003d4841c9118082c0700800d00e140012003a031160441c0300d4082542ca441140741c030344602038041c20003d22500000454159119000103184281c4200c03002942080038009000781c8003c002c1107084107407501612541500002800c0ca18014030407071900e458803080210541058052042c1c8014905080304000040f03404400203120705102140c0c14402d20300c00050b905040c50141c1d059401d04141445401070300c190039511400783e8014640d0b403190581c80e0110a00700007000d036902000f041e5003c254035203010003407401c2000a032490b48100d62190100705108400c080d104100011700401052000304a07140200b131141c03041d903a60280c2183e140400c041d035125210491 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 932575206 1250 932573956 932573959
    0x3030c031103130c0312171f0e07030e150105040e010c091a0f130f060207030807030c02061c0e010e150105010c241a04021e03090307080c030304110307030507140a0302 74
    0xc0c6d001c00b030300f0400703050071006030a114041058030740020780c00c40e121940b0a5100300444006440d00341050000000d91b5001014442015940c10f00f01540000402c030644558684440407000703175040105020a40d0700703540400e00c150b8144a20801c00d2940a0006400c0311000c010380c41c555403070342c0c44c0c2840c18400e20b5030340b400c44480443d081c241c060100f0002c004030f81c49a03005001e051341d100802e907120300c0d4034030010b0606c46080c81304a0110f0300807880c2c001c0c201e00c001c01040c50000c0010070007010101329203405081e03954a10250002110034440c84040d80034003001001c4442da58200c0c0761040005004841c100403682900c003040044040c1d650103054080c44011035950300c441c41090040080c1d109000000f41c1110034030100e42403034800c86007141000194648482040e04c45885113030300140860b00715210400c02c0c00e01041113007014180803500803024541e60300b000e0801110b20007001c02c2c0a48250003884042001130000500705040f500241c0301a000351558100240c41f003a0150301c081d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 932576456 1250 932575206 932575223
    0x60a030308060d2003060f0907090f06031e030905030a0c18090515060907053c040909060e060c03150102011b051b4b070303030c031103130c03 63
    0x110f0520404c0c80c510204001c00740d01b104c003141d403001c4080360054825070320042c40742c01001c02444106403070340002c40316840044010581c2ca0b0742c4c2d950711b40d0151441801c4403105c00800909010036078068414001000d048000f0701e2011441e880d60350b070b56041407040080b10301c0c07078100f02009050203070400400c042c0c01c40c0982d60310504d50004080080c204a4620344034080410009402c0303030050040d500301c00d1151902003241200f0328901d003002404014040062062182030380e0700c000c40140100041c0054030804922034055150143c241c0707a0160325140540c00c090200030250000b001625445090b03003880c84003014074000141e004081c403019545d102104c124403802c90a400c5001041d44102d2182101c0c0080b040000f081c1d00c07030a82e0320395480012030380442000c0500d1000f0003100c003c0410205480000d480400c103050070100764003460310b40d400c1045c0c1001816050b203d03040d80701102c1d050900c40062003541d041e506100c01800c08001140c00c43c0508103002d151007200d0051603106901 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 932577706 1250 932576456 932576483
    0xb1b0304061101230f1305010e070302190605031f090f0c020d0c0b01090f110c07030209220209190f0f0c09030b07050903031926060a030308060d 64
    0x20301002c161100402c05600b032200c10b00b40d01020701441c880c0c00b0807100d6450740c0c54850300c4030701c402800013808a00c00020750a2020b00421409c0c49803106208041c001010f0107851031051003680009203c107041082d0500904100381900401120792003203203a0060681d00c00e2304000c15000750060340000c1030091400030340614040300c0303500c604c422100c2c0d034080798500c0411500441d17505500036801050040701000401c118100c94000c00e0440901c2d10b004114031002224010310303508250b150441a03400b1f50002c02c254140b805401d908138044d014400301200d842c00c006681d5070140d80000340103134050000039000c074030b1421440c40012003040c0c09005116180d0b841202801c81514000300c0310340742c0041c03403044038003502d420f0041320340c0041010069a24900b0964044c2c00c09880244c25010401c4006011140ca04040074079003015103c210010101400740c40b102c1502140001d850301401062000603910030b210141201d605140c003441a0340e81c1c90200d02105460030004008200e0981c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 932578956 1250 932577706 932577719
    0x2030c030d05180f0c010e040204030506040c0f0602030a020706050708041508060a08010c0e061809040f0b13050c040902040f140a0b0102060f1506190f08011e0b1b0304 74
    0x380185100710441030b01040034580d40342c44d1401040c881e10030b5400035003040c00950059151201700d4400402c01424a596500c5607801c11200300c908840c800d003001002d1140384640c0e40d07130001420040c8000d500300145c5002c041d42d82c000d28007981050090205072101001305a004031806024140380c282c42042c80f042d0081c141c0c01080d214148110300540d000b1030f10031414842c2001c802d490b6516041d2122403602400035036801803003186035494501100350b003151215103c50303000b10302c500180150007556080c400c2c081c1502410140c26414501c0c0480c0201d000060441c01c10042190002f8090905200050040110340310300ea2016081c80c01c1c81c4071550034402198840c10342c1c020180305c09020100120784842d42203481d140c4240b0304801003100d801d00303c60000c42d218000b030314080c80e20081d9140a070b1040b0b0664220f400048c500100b80500c1688108080c0c0100107003c120103001d08607040c20b1a1510250023810450403020075105901601c1424030400301c12040140e950303c0e901d41c2c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 932580206 1250 932578956 932578961
    0xc050a0c1404061a04050d060b0307080a120207030201050415031409010b0a090203042a0e2508070503190f090501240b1b0a02030d02071e0b1902030c030d 68
    0xd2215110b00e00d000c60020f014501d042002c0d110400040046181508000070040014580d10301514602c1c2d030342c1020b40d41620204030080180c00031100a1584074950b28150003000186114078045400c1443c0400040c0d0300042528141d60460500106080541c54210010300c12245201c60064010007800304022040d400b42c00d21030416030341440340c02d440720200816880300b07480050121000900c128030000000e040d0300802c21440102015842d5a40301c40404000c040e900000201e510503c017004100c5441d5000180c100141094603451822803005022030000404140c8440c0d515001704110109552081501c01071018080042c0f07081402c11500030031040000385035512101c0074a01c4003910000d0508100c80c000d00190b89000d00101241903c0700c5840181100c80c0700322601900165818400c031000c1c40a15401800b203a450440240c7c6d40040550f8045035001c91800c0c00d02090030382d0000c6810fa80c0c800b140c5100c612030100c6007245184900d2860f020036001c0881c03005104012038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 932581456 1250 932580206 932580239
    0x50601060905010327083f1e15010908070306050a1113050d02130e0d0201060501030e030d0b060c060103061b0314060904020105040b0f040e0705030402030604030c050a0c 75
    0x1c0c1e03010400005c011740f42c0061031906082030200215028000d02c0081c5168008050b1074094030001040c02e14032110050851007440e001c0d505250107418026030320004452001d0340140c41c20640d2030b000c281c43d160072040c18005001c000580a014201403616400f60040d0002401a841180d03e9a40d5a080260081c40195550b038912400c112543c01e00c034800c401a00c102030901100c210440307140c41d0400c41181c040c80422078001061305c0f40c4000c10041c2c3d1054031009440784024004503106844002d003150340980100341454900562050702d500000b0076501c00400110000540407080c00002d021402448032409183c850726002204100302a08121448140c1030380364000d0290f0640b00750207403119104600301c00000c05000843c1860088412038106006050940c6090384800040b02181d2284000499a400026040181540104100340d00a4032490040d0450030141e000038ac448201420140400003001d00000a010703081c00280211a0f001c1c1244450f00c1d6030b641e0350700c00010b08 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 932582706 1250 932581456 932581459
    0x13606110c09040210030e0c100c020a0503190209090a0221150f0a020d061e0e06150405100212040e07170403230913062c010e07020a050601060905 65
    0x500c0c40703101c91070912600c01401554014500142e1041c0031404030020180104402c0c030324800d1014007980368507400c1f40c090030040f541d50b030030407541d0080c014040892400e50181b8000c0e4444845000c6c450600060104401d504580c2c5d880a5100c001c1e165180404009020358820901c07907814299003016440001d21b42c01c54802da070300c2c018483c184803003802002c035900c4081080078800251400392903401801c015040160020f1860b4880304e460100080030118190034005103c4240100c42c2200c0b0f600c0d0b0300860031661079085c080c56a0801c01540100e01c0340f90b018107940c2400704460780c0244141010725580042003a1107603034910800c031071050b0945146000c92000440098444118042148241c0d0103403942c404018140305040509003a50f01c0c51440b142080c402400e0f203580c3c901c403200710703503024080c0440c81d079040c8021403c04001c1c01e8410030700070300b001c840c0c505c2c0190034202146c1181c414503030f00e0b84503503505c54050741040c004800040c128011440041410354004a0303c5066420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 932583956 1250 932582706 932582713
    0x91a030303101802030f0408071a0a0e010f0203041110201f2a170f07020106050607122a03090320010e060a0c2103150501360611 57
    0x800f400c0320012403006a41162001c4d40d59000580850248401012030903c101c1a0032243c004203030758412000000d0700c400390300a480d6400811488003d000b80d690306494030308110300c0c6007456640c0803507200c11011954001d507099162009454020680901c5941101c00800500508408255200c0c0e28038046171284500b9070b00410754940781889a1550b00c00b41c950076900841d41c503070001c2c05030200a18100204100014681600000c80072030a010b520003890500050030018006801d4600a81040703020304001d014030408120b810000c11000102424541c0902190313500d840c88407c03901a04058111030100f094081640c861050000c990041d85030001d0300e40c00c0b0b00c401358480201c40d10540040c060f20a228020720349407005200308102c0d801c1180441095a850046518403400c9003600361402009055003107402d80140103410480986100701e40c1c1c10400003804110111040401c81c0c2c032400030f41c04802105002a10b0138840c100042421240d440c82c00804c0e891254071480030030300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 932585206 1250 932583956 932583989
    0x21302040f14040c0f0e151b010e070e0c040612091703040c05150d022203051b091b18120109030e06090d03180e071106071701091a03030310 62
    0x2841502c060b1120282e50740e540c0306c54030041e82040800c08034172040c060100c000b0884603032400120750040000b8411280040b901d0454030710403d05010300390f802405aa00c0142c20801e20003c504200d9058540e1400d00c8183c403520518400d0041507031560080c0364403107010b030001d282902d22000c0c5202e188509581000d90381c5500038882078000c0c2880f0b0a81000341441130602ca00516009055051414580c0b0088600100381c00d00e080c0310aa4801c0e00d1580015090100c144014600031880c0b1905444a24640c103002010002c49144082003072041040414172020803606410801c4541f04001e1040e020034000e010403600800400d881107011a01c440003822103410000d050f103e0040000703118858022403030301c0c180c2c1e0b400000d01e00c02ca15900109004a0180c1d48450405e0040035075981b00000d603031000c080180360030b02c0941804140581c0180c051004807144849a05642c80c8980208a4181c04d450381080301d880032440f2035042c00080100034040350758030384840c1280d21700e040c0c2c2d403c601d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 932586456 1250 932585206 932585231
    0x901230a05151e032a130306110c010e030d0b031504081c0603030e01030c0305100b0a090e0f090d0c03080c0304020a08010504060b030f010b030307021302040f1404 72
    0x18418440d15820400e015080c02d84620311078042c2120790245642d92441000182000d01154811101c088441451480e44200030008002042070301c0c201c45000d0380360401100c00c3c80f40c0904507100040c00252500d034545610085001960b560011000080c4840d9a030401b01a480750002240c00c03844c0d43c0b410000700c40514001a0980d411150500751a181752030b1a05d402d1580e51100c01c041c1c6001c00001400c0c0c45811a6100c1c880056002e980c0d408115180d03800010186c6070803c4060040600b41130911072900546480c203022109080126a91a1180042a80c00d40800d43c0259444007112041244d404480b565003441640a0003c0e04c0c2070180e03150040d604200240c0010b80095400700010701c1008401c401581c01500007000d1702c01f0b0301d9440340303947d00355001218116009a200c131030720021418200400e000c1c04201030700078030103002e00c0070200350b0b40d00420340d010b40702d00c060900c080912000b035411507001d0408903000e415885e84940002c10200c83c400303252805585040d0041628 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 932587706 1250 932586456 932586469
    0x1d060a0c0f050f0d14190e15090f0901030b07030b011b03020106050307170d0e04060e010803090916050904021305030a0308041a0c0301050111010b0a120c08060c090d03020a02090123 80
    0x880d83e4021569041811015268403420038050300341d407d001903418001c100356507081d09010861214440d19598200031000d01584079000c0312039501929201c001070000230011ba9186510810900c3e00040049203940105c0700300c1c100e0104584417040e451521800c8c158190080815070301c0a400303c0e000b07241d50300c0104094030418910101e141d00710a42800003d403060903404002c1c000100003103400d41c1c94861206801750203911031900f40c4c0c00054000c2690510740485a0700480b04645c1c0035008500d50000781c860311400d210b02d0301c101e900180004000e02e80c1e080c2003010f440c0240495150000e1850f000c0c0070b01002b910190744143c480903401c840168403417681441184808815800c41c0d1a001c01500e40280090640302d49548034108540107489030040c000c000c0c0040462039103c01264101440034002c00c0e04003180766040070b010070120507014400c580391090280c0c2c0c028070080b0315040880c2071051030400254440320b400000921710902c043d05d154590310302c00400c3c00c56010135040041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 932588956 1250 932587706 932587727
    0x2040603051f26120405011b1e1407080a021903020f011125060f080f0f180f0a14060f04021e090a0f050105011d060a0c0f050f0d 57
    0x12040002428010301010700540101000000c0d488110000444103940c04e141018241c981c003858042001c0165680c00320300905000206460210b0007041c82d00d8000000c190784030305000040c010300c00402040030781091454448c0341c10b8299584680c0303911760b103526082c01303030401d920600f0300f001408140041c40c104041169802041440316142c1c6500542e440700070001005807078040e95040765a02c00000d159501d600134903003080e402e500d040c003101501851460107540304001a4004010907201c88002054024450802c1000580e84454400c041180300318500020740c0514103840d0484070f0f001075511400c4d44030300c6400381880419009581d5505c1c0840c0c0509080d031400c0041009420044280c0007104103d81410040341c151301c3c08611840015203020030071030387c1c0300142106e1351414800c0a014040034680102408038400001a088070070341c4409100d010000307040442d9500071403d40c94003d61061a440070382540e4180303207485011440d950311290040119440401e403160341520b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 932590206 1250 932588956 932589001
    0x10c110a030e04020c03132103050301050f03010209060a0302031e0601170606192606092d070513050f01050a1101060e0f0714130311130f0204060305 66
    0x90341036000d441c201e402144508429400c07039030803c0503040d001c4090004007520b500614100c000340b413900c85c46100d10410001483c15400e81e0511040010303501400f168111131048443c100c003c510440040d0080c4500e80c1c80e560300c6080010261403044d01500603500c950040d50f61444044680504814203c008a562a0008000c400c08075188603802d42d900340c01031400340406040120603a01841612040307411600480c0c40c15104d14070b0080c444202e9200c070560302e84080083e05000d0049030181030080c10003103a43c08031120380b0248103110240c040d0b00110321020300c0c8060034600310180c69940200e80c04031060140c000301083c1800c00100c114104131060351031034607090700401c1c100e494402070407654446548494000074441c8108045502450010100e04294140a04054003030081c1041541c0c0c081c20a020764240340705d010030680c0803290003440d03040359128007400280030052540c15040216250402c2d47c0104281035001d0015a10703039032010800364450940f007049482d100700b0007a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 932591456 1250 932590206 932590213
    0xe1e0a1112250309230a0f050a081204050c0a0501051c06080d02011413020102060402060705010b1003020a030b0d080412150c08060f010e010206070f091208040602010c11 75
    0x210101c000c811079111805a0000b10342100c051050304442c0c50009040e400a40c5a4041d50300340101d12044140300300b0b00b0030750005140501451075440c0e050152000e40300c44d0168003110107000b014801e04002c554490765941e034401e441e04c0030400034071055405440c5880b070500090b01c14205501e080c026110161515030401060027801c00c01c00c050800d024080079250700c8001404c3c0d00401070711042c941c10350000310b0011a070000c83e20b0342e40402004921075412103082d01700582d8021801980260b010303030340e2543c0c8900504116014050341200f1680000441d641840996403660140640c07001d6a034061060103803420030084a01c141040150849904000421484c20380d81652599103204049030011000c0002440b001c0768620b2030341c80c020071f40a07020000e41d032030b00c0301014460031024202402c0440c40070000075610030f4010400310074000500041324009004801003c0100146030000d0880481840c101c83c03103400521600000d03600b42081150074a0259010880e65031307159006 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 932592706 1250 932591456 932591467
    0x11110150501230a05091e01030b030a080409021305030607080402030d020c1c0203150414060105150711150f130905130f03170112020111010213090b0a0e1e0a11 71
    0x80c03e003a03110110840511608100086440e2201003000104019001da41c0100c02c1c2c0010002d0140c8080700b01881c4a508100180c2002410f40020b44081d170352a01070040e22244110720600500003141c002c00d50500c2902c0c1040b280603442200c00f84214800d9060b28150f40d07542c1d1003a84e40c0d0100d01344c41540102103100c400084190a070704503910390300080486103883c050409943c240c2606039070641d21800920072515038804100a8103006040540d9075104500880035808035074040c1d510000c1c820400e50b1903401040c0d03151003881e0a00d5402184441c0c3e21511f4402e851600d43c400d400e088084158040005203140c0c8a1207082c0c0300c0c00480c541c075448030500d0b5440d45d50321400103004405000c48190b41d140074044840030309018040c0c1c0d00c00862199032500005d0001040b245003091140e00400240a40c140003055a03030859807100400318001d131400000039002e0215800404203030ba24002000300020b800c07140070f1043d00d1010344140341e40c0c0b40c17451341d502515030352404002c440300701304107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 932593956 1250 932592706 932592767
    0x3170601140d020d0e1b010203091003020d0b1f091502120a11010213080f060105210c04020f03060901120f11040b1009090f050f15011110150501 64
    0xc011507003482c200180380500c2c84407007108440c00074541c510030b0b81c00200d00e0b440150301e245229500d04003d00056041900d580c000560303062040950380c0406402042c1d0644000389134101c0203604c08001c3c26900c002d0041881c00011264440d1068000385410710001030303808126140c9509805a640505682855140c2c050213030b61186041d00200540401003c2c40d160007840a0001800c2e070390f40c0414002e10b40684103192010003020342440d41c001a00402150343c0d075425056181000c68000c02002c00380380596820440750490a80d0003d00000308080c03510301c00c500070f500c25502241e075691240d27201c0c640031500201204000b002030940801c44800f084100606488002c0000c1010610240c002d000c1112084194214004984608401d101c5618075021384d040152032610100554507006000c104000c002402001501104184548569104522a1401e015080300f00c464040c4501a5203005080e04201c02c0101880524041095031103400d0399000081454140c601c41814011b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 932595206 1250 932593956 932593997
    0x26040f110307030606270c090501140d05040f0203190809011805030f06010305060c090105040b0d061205030c011a0f1e0d0b06030d0906020a06020306041d0a03170601 73
    0xc026a500d449000340000000340140145005081441e0800960743c4901d00511581440080422181d03420b1440c03032042a0b40c030040c0c803c01c80d002403818550501071f1600703160443c400c01440c4e01c00282040100000c0c40002d06000407005d1080d41100c60b50404140c2035909416010030085c6008010889001c8640c403a842d510480500750100e01407059980c400a0318042564000d024070390020350040051040912031140c3c044030580c403113841c02e103000f000240284540d0240b1071a40801003400fa1f440142a84094081d0021483c035105800386410515681d40019048481d50340c20220040c0c0300150500707440680c41c802404503200307400d82004001c01101c081030b441c450340380040000b402c56550703480e1514226006075041c114038180319084c1400e004005600e1810300c00710744030403c002d82d40000c2c200e01e000d03000f16005841c1d845c0c3e00005006017110821031080200c280b443c0000c6020007084546180f482f9444600960131a802426007040040720260f021580340310320701c1483c07501301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 932596456 1250 932595206 932595233
    0x30306090e2a0d151407110d0e0d020112020426010605150403110f100903030e030f1c230414091501030207060e03040603050403020d030e1018060c26040f 68
    0xa0300c0105204171824019402c841e004c0b0741c1c0000085a1034203c01101c1010b000c0f0800203403551500100600c501000f10360000344401009041000354854846d4914080c7d05171000380804001c400400302c011510459286605030750490b4951802e040000d00d0300c3d15100e8001034051245055090034070b1070302c54501d1010500703002030304595400b94040250307582c002200c06040150321111101411814000c10302003400d243c1c2e5000b03602c01886081d14400000700341c04011701150307410540300036804003100c400307800d41c02200c451000850f13078440c01e404c0440900207455400d030800280e0302000c400c02c01440000e0b518130881000400350b00e5071303d503c6500104107260003500003088043d50401036605c0d5600981c041400203907120b040c0300030540d041c031088000c0c06240c80c003404800700a60079142c864960306a940d07589542c0c0c0155026214290159907107103030300544108100000c403900a010341030545580070a0380481d0401d214941c01c0481c04601030754006003048180c502d150b81320074a49115 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 932597706 1250 932596456 932596493
    0x40926030f062701030303020d0c051c090302120f030708090303040f030f26060a12031d0a18150603141f080604080703030b010306031e030306090e2a0d 67
    0x41850f042240510002e071500a40c03095030016580c280442420080368003401743e003020080c04100410703d80825940c0c0c0c005040b03404000103440f0a03e45026483e0140e444209900e1900105042d011088100040c41c070440710b03510f1710784c22680c642c00309640303c0c0300842e80205800000303400c01012034414941c2d000c0c0251941012030562803121268402d12a09100700d04041c40c04604204140c2007940108000f01010700404180d20b00c079580c051b009542003024440001d5502d02400d905540b035203158030081c01c1024140d001c0c40d002105c424054445040c0c0d01907604000d44c1c000644030f202c4d228140032540103107014482d0791240d00102c1000500e00c413100c0a80580c4001c0800e13200340601c01d00f801a880382c2c5a4a41d21300940c80c02506482500c402c0c40d06240c90711900b040031640c007818241c19464514a081504410ba02c0c0c103a0050620b508a2078095141c141e000000140005c1c01d40090003000101d4401002c03100500c3d03a403813030381c00702107608200700540c1d140001c0d4040340c034000c15005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 932598956 1250 932597706 932597749
    0x10f0507241802040b0f010801170a02130509160503150a110a09080d0806090703020c0f011d10020f0901050c010f02072a05060405190302040926030f06 67
    0x40d08450101039031049118002c1800d104089103046290900c502d400300b5100742c4110031014030f1070001030b0806205104800c02405e18111024070704100740306914180342e00501920550082c22203e10080c94115801c881c980700796085a0010925010200202c40c80100109403480700d0014031f80740760a0140110740e5481d25811900c010503c0d000c007504680b4440c0e6540c0b1941071070200070301e02c0e024004401505020f020402d202c001d40310609410780c098141d08015a540d410f5156003032400c0307242034400126500e40745010620380781140034248605880022160b902c0f2440440342e0482c4180246000c50420820600d042c0354002ccc00a400380419100c00040d02c41003c0c0000d50a13a40130810031195020880c154440c0c01542d50302d5510300e0000107a11900403824840400c2043c82140541d034810504240740d04002c544440511014540c05803051200702c4440c5802542c40c20090b1102042c0141d01c16107201310b4400409583c8100c0b503005030101203468840910000c101d1100c2d50b10103004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 932600206 1250 932598956 932599013
    0x509030705090106030e060c0c030406110a0f1209090b090402010810030b07030c141305061305120c01021e060c030402011214070e10090e0a021b030d0b010f0507 71
    0x29102c1003820300070803058502080d44480f000f0900d0800e40001d00a00c410320043c084003c03110b000000750340030384200e17003000c4084602c2d2540c142d1a1410001008003d031031a00c480d0340803c081440c02d80c4106034161640003010751100d4203c0d040c0d40100007010380080d4a040007501540c070824031180c018141070100107030703140c0340e880c0c00400c1308040b5100d5010a4a510510031284e80c08440c00a202942c28045401d00c0300e910380c11201c0200318490b00b84036020200f0190340380802c42c007522005080c001d004406900d106800c0d41c4c0c030380500c05040c0f07015019490351001040000409900280a41d50140c0025618003603491215040a401603040012003920702c141c11520b4031510b5809000b2400e040203170300d0001401843e2800018001c0d001c4c5164009480800390052110310640d16258589400c0e5612050010000d001daa0b145000001c1181000c581221010004001c050100c1c0c1040c042000c440c00151846a0082d140e1070016808100c1040410004550700d0700702c2000d1410740c0c0044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 932601456 1250 932600206 932600209
    0x1005030a062f073e040f0b03060a1109041a13111c091704140402040303050f07050a020907023304020d0528050d03110a0509030705 58
    0x14802a004803589a81c0318500595004003a44040820000120460384200390600000582c0186079001340790b20350724200040c0802c807041415100f40b014903902034035001d80e1210000148900a4010301841c54001100c00001503030007842c071200c01c040e008001544a40c40b4200c000d251012100700c4001d001d103c0c0e06203d5980e4050319902c0031000a10b6084416290100000009110240d041603031a10b00010120300801e810746000d80d414009200141000a07002405080400b0005007800345010701e0720300b200009400742094995200192683e00320181c01d010892003507002c058040307902440040000000f14005010181c400e8041d035903c0303c040d502064801c4001c0e02c000c000360304008007040c00321007600c10b80c240610b100d04e142c1400c03009504082078401406440640183d010301003540c00c0c080108003007903c4020000726050041c41e41c0c15500c50710f0b030007131034200c7c1c3e103001c0d4071f08041010340300e4017510302c3d440034480f100c83c036100542409444640c88080f00740c2c0c240c000c007000002c15 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 932602706 1250 932601456 932601463
    0x603210315060c0703110a1a0c0709230603060411010309020f03010615020f010606020a020f0409061104090b01031a0f01180e04030e010e0a140307080a050102130f08061906090f0b120102041d100503 87
    0x1c800311074331404a030740500303141c484000c0c0041c05036000303501110400012600a9020110f04030007802e00080542050010516440201a42c00d80543c2030840000304c44003014060820588030768250703592560480321890a0b1904c0c6c1c49682c0040c0d01100c10300b40945400c481e00c10303100308001e100090343c1175166070b84429698084103030200c4210125042040102c40d000e5100a04000d103020001484125400c40b18a04032188040c05904407102c068010b0f409046070000d04040554415001513844085c5100f15108840c22000038031a40c2620800703501403c0c00444a01004140b09280703410202e907120880b1800e030b0340301e0785489602d00029104e0340900000038082e003e0700026035200c0d00003071900c1c4a2078003a0f002c2c0c800100f2545c0100a4010042580e6230024164000002c6040316140c0304000b400150304011003861030000d003240340d111a640070b10425541541d0000603a4003074001c160807401280304074100d16621040f896031401c0e607840c000340c1c030207040c4900d00403041c1c444c00030a29 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 932603956 1250 932602706 932602721
    0x807140715091209030f080f1b0d090f0b031b0417070e18030a081f0608160207080309010c0c0e010303170603210315060c0703110a1a0c0709 62
    0x85607102d00700000d10040b0b0140042c0c00e84541005002c0d1031030b56981c45c4501040740405400c44001041003042c444010084825a85000e43e07040d00b880d001131a160b88401c1481c0c3d811020941d80a40060b503140d5154a6800320350482c048141140d1751900240304100305160a042181800c12003c10808611000900303030344050401000c17040e0a01d8107110607903c0103410300c40740a91010009440310400001c0341c10303104003444c0801c01034561040c030360407640080604821044a03010003040e00c992080c4402c0c403c1000d5194a085401c0c80c0300140e0b10380b60039004900c00e90700b04000440c1d40b540107c03801c0800512900d030300494a6a02e068000c810003080e0800c80020b80000c402070100d0011084068202e0f80880107414106402c07601020703814800c0303c4d01154004003100007401002041d51010682001502d5240e980c1c07900f00d0304903281d08a078001250b8003170703081c000c002e03060809800b8101a00c4200c3d200d010300c00049060320340305400040301084c240c407541201042c03800c0240108030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 932605206 1250 932603956 932603993
    0xe10060c14010e1f0e03030606070606030605191d0c0607020a0306110301180e031c020d0608102904051b0c03070b01081902040b1203031905100608071407 68
    0x40711804210136130600c004903061203820b140c10855030703c1c0c0c901408411260004422a00d15954844529004000d030240b0390010b40b40c20b107440704200da0820f010144c1003005002d140c080100074581c400c004100c581002011003280d200c0704182c0c1407810103c00900201d0300040a101c100b60752644d40740c00b0f07161032540d0103030000750120040040c1030500442e844601011402803000d510301111090381d138042c103400001c600d26000340c00540382c1c60f15412204000c07200d8400717001d40740c1c4800011741d54140040c0103180e0107250040f161016144000035151000e03845140400c0d01c5400c02c1017001403e00038004050100c0055211001c410300c00009016500030308010756151780d4981400c0c800ca100591205503a40c02c114541031000600c40b03001c13140a40d04072000074001d0603000c041240c480401c4100e038a9440004140040c9228052030041c0611520301d044c0126a692903036490008594400c03803001c180d420700402d0409014580400a840311194801d003048001d0f203900c61407012040112 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 932606456 1250 932605206 932605213
    0x6080f0109112505162d0306150501080c040b0d0c270501033b102405030f0d0f030908031303120b011205090709020c15010e10060c14010e 61
    0x40c2c3c1001010701089508404885081392902e181c0b09140b600100c10007008080c80701021041140c9011074036070703d0043c1da0499010401307903880c1010717994042c190b03024281c0494091000910f82d240088100d409442d00b090701c841c00c2000da14007000103401d4118010b004d2140c00c030903214100302040c84154510a404240b60b80861414001404a810004541c00f0202ea40d118a000300c10004050303a02c80601c0c7c2901c2c503030035904942c6c0c0030b00340f080b94101c0807016410b00c13019403000502e07100044031a08a54000764046940c0e8410580c0c1c03130840c1d000c0c00350030350009200d00100e80d024030898459000c050402140c4807500d0307500d40c1c415038000c451466008810210b0001419484002d8440b4480b452104018404013880040c1907038503040211680301d80c941000030740b41c00c001d01010000b022151400e5464610700120300d0f4449800b20b401400216034400000350700c00c0c215810781d004190b034600305060781d81450402c541c280301015094600c40151461451101e01c2441910744805200001c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 932607706 1250 932606456 932606527
    0x1809080c0d05191b020118032102070906120b04151b030f0c141e03070c1a060d02040c1e030e010b0105040825080708030301090606080f010911 63
    0x5455078054143c044404000b0b480101d041140200c0c3c10408800e80c0900f400d02052580303000500408209030401001c800e100c400c1d240701c2c003e00204115040e4070503000d076140c003500c4040c42011100d40303108003202d40001c0400c0001041c00e58210315000fa015810701011460340010035420340d00c0254854001c1e000e800040108aa0b1521034442045006081400704503400c1c00001c4c860701d01d0006510f00900c0024010100c004039210100d414441e408032a070300c03454550340146c50800034001c00d4688611301c0f046200c03490203000400b44210300c010078a202d02130145d000c2c04010102d00ca2508180400000400782c100d400342c06078101121199004503105004000c1c080c2502d404049140c1409028071040c004c0c690701190070a8408185050009070784500c4072401f0500c45640d110315441c0c01004004120b404002c401103041e58007950341400b560fa034501e41110600c4044402c1903130901c400300184000d0038a904802d110320340d10500305080807483c4103040e4594007158049100c401c181d524 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 932608956 1250 932607706 932607727
    0x304060501120201080a05071b0b0105092a0a030b03011424010c021c0807030f02070e060120010b060c030403060e0105250c06050901150503071809080c0d05 69
    0x10345015000c0c00c2684110442c1990000e001101d0142c070002d8842d0f140c80014182502c540342a0a8401e4500d0090b190304001c0e04095601e03030000e006484c0a40400350001e9180000c04d4a19844002001002d00000e1031a40c4d40c09410b41144244408054a0b13012203001d0307690074000c58121841d00652101c060800307006500c0d01c0441d044034984640304040800c89103070b82201078007e42079010b480100d2030b21020740c0e00c2003885000880042040c0d00204007041032603401544820948065001c6901c100c0d101c44030345103907038012210315000621001800c603c02c00d44804040c1106001d5002080400150000803105c0d0031211022106900201e130410900c010703400f0b90581402e51a00070070060405290030104400b01c601079102e44800d203205100f242d0701c03c2d5210082542c05c910200450700b04580054060241247d0700b4614144030b00c4041050300c0c000c14410100c0f060700070185800017949030040040e10040c80c0650300b981043c04101036121003400505044605035031951b58807a901c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 932610206 1250 932608956 932608961
    0x3110d1a4c181514030c0c06010303050304050c040908031602011104080c010305010f2d08100c030518100e070515071506120809030f070906141503060f0a0e010605030406 75
    0x5003ca5226010051403e850760b030400315542201c0e00c3c10704180e0f680d9803028500003840c440e80f580300d03945105900c000000d06512401640c00303144580180c1d07440341085004c120036283ca00b04003070300100041003c0f03412603084a426541c5604940004216620b03000e5150340c55800c25801841d5030303004956004802d42e414442e85014015118003503140500b400d40070356840c5511603e000600d503071070044003040c4640548420041c4040300866202c040708280c140c0c040c3c81c0807190840868100400310b482a04158001c0030741c0d030400030052080984611010002d0215903c10702460700448401051075118001c500e080c0c00f5621078a242e64108614294098203400030311400403a28102c0180501a6120188080103410411403a1100c02ca1b8001900704a0b10080341c4442e4495260000f642c2c010a07000402120b9900380c40241c1036203180c0902c01004595540f0581c62602080045d81c649041d0103446020580900a0360302251102c10b01b1005007000c0e0400ca001c0780011080004211050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 932611456 1250 932610206 932610209
    0x807030b150d27020111122803020307020a150b060705061506030903091003181a060f061215090f1b090603070c020103110d1a4c18 58
    0x70303000c0f0300b02405a281c0e0032081909100000e0400c07000c00c001100c401005c121101c280e03c1c0380740c40160744485501009910100084030315510206449843c40106d0080c429240318010a4000c2c06425403142d5400081c10320440c42c0b1103c5030342e2107800b1185a10f400018118030ba103d000100300034200b080442d0342d40001484081d01c210810400c10010801c0802074514050096074098040d140807942607000d092819218a9450302c0b8401040900c08a0383e4251f00c0042050a0b03403016031213440505c071282545801240e0461307002c0107480e5a00c03074842c201951210f0303195075030303010306110f1000251402c009403481840360303030b00c2030900c50b5440e032002e8003940503048009428a0710340344001203803040c04002c1c401010700c00340c038100100f5640260080f0403510b0200c01170710b43e81c5a00b8519480100394134400400300500d080814040c0d402c20708050341410444140c100d10640c0601c1c1782d0720301c0c0109880344607030791901507200c104a660f0045811410188079101c2000c00b0340030ba1188a03160702607 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 932612706 1250 932611456 932611481
    0xb031e010f0906090c05101e170a0f0606050f120603030903060f0906010f0f0b0c0f0d030905010f05060913060e060403030912020a0305040501031d03070302030703081b0a0807030b150d 81
    0x87d0444103502038001101e8001c0c90020141d0345542005d60009440e82d04190702a034101010050400008030243e0b400b001c0c7d005040e0504000458503072008403454001d10000040654041000000140681900302e6101e28014112490412400042170400038140c0e124030107416000c0502c04050340a0201d940034002c0c042d80108102d251021985489109110b801703051000081d4005000a09020600c1141c00b00000c8440301044140010001d0104001c29241940303080030945e2989040e0051030702581008016a085403102408607210005520b0704451196441e400b440e0200000d00582d8402c0303000f5203002500f442141810000500145d2640c011034120300c07070000c0000e4000d800c2d501514028600000c9101070301c420941071000c0360340e01c903000c0d200100f4400e04055001004041b480d00c2544c078041d660300c41002c0340c1c21a10b000c64010a03043e109010401000c1e124082c00e40c2d10070802c4ca0b000c81d1001540d4049440641ca144024024460008110f03482c01898010030310403405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 932613956 1250 932612706 932612719
    0xd05190c0215071e080c0705090402030d1b0f11090603010207021e0f0a080d0306150203040303050a050904050f09010c0e0a0b2b0e100b031e010f0906090c05 69
    0x201c0d03000945421114809003050200400c0c20014441010200110703840b0301c0b200c9103024030007070908060541000030400e02c01c1c412110042400c4c1003000c6c1d1b07103001310760140050806800e9810280e488004003484013444280696611001c205800001c1029900503e0f00c1c0c0030440c50300050140c1610000c0c040790107a80100011801a121403620315072401450004a0701c1c540220009140e4440081000380c0c0031015a0010403074007400b00780d4840948103510200f210030f56a00b86112410400c96107400581c2060000b0170110380204028004a881c5142041c079002c0312030b00180480340f0070f44051503503c0c0c0c00c90400071901003d22810340d9111284c2495030a4202d590005031a6228500518501080218030402010141c1e00c9400040a1456800407a01800605100101414070991003280300f4220344000407007103032040c1c009503180600606254a1040c44070700c4240344140900740603650390841c2101007a070700d110f10042c851140c500800c05603503508000501c40f0711600a54441c4c3e9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 932615206 1250 932613956 932613977
    0x100302010f030c051806090402120a0501141003111b0a1211190f020303030726010f09020912010507020a020f060a02070612390f050a200d0519 63
    0x140c0190640d0611348205c0d0444515561100120301d0901405001541050010880e00c140f1450381d105203114802d604000c02240c0e90383e200c0d150003240341c114129040042c10842e10308162098200f003142100e8010082e10b40044d271000800030441c0d61090390b4203504282112010020140c14000c2100c49600e40600450030751460700c1c2c1c84507a21031051040b0319800391790204200800e01c1d903203100398000b000d0302e03260319000c2c00103450300026802000c960808094100c8494014810550685000603501c00310035040070444402076100034500f03030340620038032520101000c003406820300c203155660103031240303001d240b040c45041e0f080c0c121070603c6030a0600c0607480745640060741500b15072580c40c0002107040754403980001800019102c0c0305040ca840c0807440c00d401522002c003180320fa1941c414000f01c0000b04116056294861240c00182c000c00c0040c400074414441d8021904146001002c40f10070700402d549005448100c020101d080864189020304889455030240220341c2000700048 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 932616456 1250 932615206 932615231
    0x30406050714041e0306060e012c0a050612010609060504060501030209091605120103080a1e0212031f240c080f1e1215030703051005041a100302010f03 67
    0x90245000e6104407102002001d0814600c940104d0000c54210104200c020340300d00524119030424010050411000340c404030384040e900b40c0a40703201e05134111207622500c0d5003412402410024203241e0303000507003d0007110b08980070b1007048010800075800041107481c0206200070f546c03266001c81d061501c10f2120758960303100e100c0c0c0d065012000f0700101541062a001c20740303840c00703420a40b103d4507220030004001c1221000c0100f035000d03503a86400f0a1071074810411805036046041400040e001f02c06460048507204000d56080b0348410741145441d520403e13100d18890840d4001c3c070719003c0b2018040e02c000c89600310029071200c10304c1c1c6009280140d84828000e4891041d507522040d8000030b005219001d400401c1450300a18100f0682d0703061101640d00e10b10500740e03844862121011203409907440e0000c0c502045a42c014040d01680114103000b40080c03d0041c016201001c2d101c20065001c3c0203501c03524400d46c20300e48500b44490441c00018500400c485100781894605120b030143e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 932617706 1250 932616456 932616497
    0x20f0c030c0a0b03070903120f02010b040b0319050c12012301030c1401140c060a0b0603150d02040b100908010e150109021b060a02070b0a02040b090d050109020d080304060507 77
    0x680c1d002e6804184d0b6510384443c100d403a54010f52001e8003440001e15103038040c5030b004ca072079080d00c040755000f0b01091004808010840c3c013a46030341a0316920040307450242d10082030b003100302c03540558180d0f010525020017140b4925402250b00350700e41d540f00b103543ca04926240100507030440316180b0030360541c107564800f6102c22580c0908125148010040596a88107403028005122125540e649503a403c1741460399130202035a0000c1c1060500c00c900b0f03481d080c000c0c142c0b1b10031a24601e520090244001c10310550b900c0c12081030b600b060701c0c0e80328510503407101c07240c890071501103680d5203075891301c1c1c4000d003130840314100a040d00f150840711880d21001c1550b18082d045d03a400b50307001070b600d18581d607011031341848070b800e103101600030042040600700355139000c0c0ca000c602500b0007400564070f00c00e1241c2280302c0c03070207140c40e15036042c0a08400ca090484400c007a55105600000f14903030960001007401801d00001c41e444c100000c20401000010b014050704030030241170006100b038132402e10619 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 932618956 1250 932617706 932617709
    0x506030304061803050114180f030a12060f0b031f030308011710061e05030115030b04170d0b040b0418021027050301150e0a0b01031b020f0c030c0a 65
    0x4210203c1e410900124070360f010440210b078000d000300300d811001c400d0f0b4018410100e8800c486031200c604940d4643d000410f4001c464241400654a08041d141c0240d03111a694000303094220750f00c00012820051601c003d60103030035030540480d201c0c90604448030303a41c0b0244040084240144e0400c000082d00f09100078159454001100300700398034038103207d1900181ca541c1e40c010354180751001507140c8446141c80520996000c10603000782c0c503001072500742e40b400c15407248181c03400402080071480c1c0e82c1e080c6400a105001401c003005c0304e00d0201d0000e40042c520100d00c1e03552200d926600d49845c1c401c040f8a01e100361403d1000c148c4416809041c20039051029000f4449241005080c0c0c1c4a000b4841610210b41c04c40c1040090203400c0b0140300406005041c082e6180c03441c008401c80240f940c1c2c82c103c580e440c000514655603505182d000e03002c070114143c14903031901290301d0003181c0d00480000c18a801c0c2c2c010600f1146094110385032180302c405150098000d0a0440c2d000c0c0c560001440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 932620206 1250 932618956 932618969
    0x30804050f0f062a07060e040c03090b01030b0105010e0406060c030309030318053003011403070b040b030a1505030c19150c030e03070b07110a031e05100506030304 72
    0x14410356184003180407050b44141c61070b4008000580d862040307503007150b442404003044503064006207041c104140d80d03000a000e49404241850603860343d514143e000260400748a15011804480e6a502d00306440300c20380080301d101c0003850050040e560320500b401c0f0000c808070703024048180342070f0b0003a04030f011070384000d01019101e5518009140c000c1e0404c031204181c64015100c100f1040c00c102c0e07103038820a181a880b00e90072411104041c3742c80c0d80d85003030f0303080c82c548034528503468901101240480804200d403d401005000240d07500c1150250005203612040c959a0b8900108000c0844901203948807040048a80501c000d45001801e50a084004e60316512135503000c4440a0301c0554640c0104280181940d0101c0219800441d1910051103620f810004020b02d00415480c0d03500c90080c1075803d1014090040130030880c003c40c7c80c16030f00250034404d40644a88505072110203a180403c02103200124410400400300719000107500d20803400c20580c02e280000940f81d20503407090a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 932621456 1250 932620206 932620219
    0xf011e0203070e09070306090f020711060705120406030911040903090501120e1b03060106020c130f0b210c0402090a17031603021c08040b0705030705041208180a03080405 75
    0x2582c0103004400003007103541c00404400441c6400d850042c0540b90f00c0c010345443c142030103440000c0400e01e0081d07854050f0702c6188440300c00107540074800c2e070ba000f04105840b03520441c01c240e401905120000d1001e06125134000c03884c1c0c0305d241050380f81c40c55203d1032103000e6440d00d80d0321400309a2200c4850181c80c42482c0250410161380c1080c009000e400888900b1809080c0300311407000c2c013403542c1100751a82941034404030381c0d0743c4405984a045e00c1610b1074011080c0300200700441d010343d120088141c400390700007a155606601280249d110f9003065043c121520b140c0061840d4200501542d20300110b40035460708101d0000708a04886038420482c2d00c450160004003400024000e0b10a03811041c0343c16004600e0504000b550f0b080c22074048010a80400c40000341c0714407421810344615001407107504141c44411007110641d000500c03210401005110102e190f261014410103518021170f46140c403071080c0030421152103c1c00c114942326070841402000004c0c00a0240e40454404a42c90b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 932622706 1250 932621456 932621461
    0x1e06010c030801260f0313080d090501080709170c03070801061212020f03030a050105040c0801062715020307050f0c01120902150c100c0806030a0b040f080f0c0f011e0203 75
    0x19004036925401000070140141c0c0d00205442c05c0000140113014000e04400e04501d41d81e41c040c64032401c140c00400001344181e0070510095010b11031251704141a894035141041d0f4800401030440310709141c007140ea4004820065a9140400038003002d040d114000300552071a041c14580d04140307204000301a91103410110080c0c500034044840d26107881800d4940c1c9150003118a801040d0900826100e14a0718000701d03820351042e06494141d400d903850700b240f40c41c09901448044181300c0e5880a20001d4900040389003180c0d0b1039500000041da400442c1c46488500d0100d041800c210034941d0030760b204050401c03250b03a0102c152100f4032000032000848140318004550250138444031241c180400017002c8100350740000c1e103210000070b922010000404185030071101c4400c00c1e21565810303072205010340003240000c00c4590300588210b0002035520325541e50710740c0a42040100341040040495045da035510140700d4000c0516480e8001c01580d100c2d002c0306614008034401c9080c0c04c1e607004c0f00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 932623956 1250 932622706 932622749
    0xd150f0f181e0b0f19060302010c03030e0a0c15030e0c0a030212152509240e04050a140708010f270e0606040c0504080309011112031e06010c030801 65
    0x1140380d00b6802c0b0800c0082032410300c2c040850490251588400c50300324804004d10002184180c0058076816919081410703185c1d00e0450150503040045000c5008041d01800081e104503000001850880072880203040e801d0406021111645101c2c0e085800030111030b0200d0341e500c9014020f07658100c5e4080d00c0040c0d403241d114a80403445100c0d10b41070405c28107011000c42d0b032540507003010360134040c0c0c2010740307040d44401c943c500c0e514880c03410a03501c80300d001c42e042240c2c242c0040d500e004500d802c1d00c950a803040060152201501c09805859507403444c843c1866000004960003501c07414041841d501d05070282c9a10401d52199070341030034445071104685040803000c600800e404803003c0c803c0c00b03441c04506407159025207050303210364500b52000e91054010310554007140c29440c095030803c032003000107444003d152207000c0c00c01e000304090b9425100300c0b20084d60040c4e110f03c2626295091481e1018500d00c4060226810320640c4990070300041e50110a55040d2640d20360368540704405080c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 932625206 1250 932623956 932624003
    0x5061302070302100c1206060203120406180c0306060e160f0c1a040b27120306010203120c0a1b020f2101060b0c1014010e060d150f0f18 60
    0x101c00c2d01c4d80740c1002c150101e80c1c0d50051600a269008080800c5200c0d0760b08802d0340d503840b81d00741c110030140290700002c02003202c170b91010081c41c060740d41e8240402000d5446001d0101550800c86425039641d40600c050a080c000d243d40c0407104205440c0314500d44800a03095006010005080180d60a942401c0209504004002c0400114902040d06152030244100101210440100420409104170040c400c102c06001e40c4a0a0090601d1001d00a070300383c0030ba400100124113502c810004802500100c45100703110310140400b15480e103a4260005280140c4644056000d5415100c1500960740390704480d400e603031b0119200841c40e40c142c407002032450510700c2c0c00d2415500e0004006620301e5510300800017481c1344801d0351203039042801a44225401841d10140030102800144140b60f0758071034194121800410610000701140e440f80490080c41045888040c1c440c826203100800754001c0d502c20185202c1c00344200d400c2d4010040d074810049402410b035030305540300002e045d49501c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 932626456 1250 932625206 932625223
    0x81e1510030c08010203150406050f041508030f1e0f0306040c02010f1e110705060f070c060204090204050913120e121903021603051b060c2e05061302070302 69
    0x144002c440d05949040d028002d40044886500302600c001201d1401d14043c4900c0b0143e80000f80b04100340742d04241484000c104900f11611780380170080c008901c072082003010303020f1f00840307540c400c1d40d0f42c2000c414400001129001600881c409000c0000b40d040b00f501600d41c80303072080e500000d0311015a43d040f800341010102c1100c60a1504405035902c14940400c151001036a410501c902034034805003582c0c0c4d10500e40060100c1d0030000101e17540540306c101064004003030b8a400b503000c038181d84901049920a030f100e030000f654001020841c030b080c0354040c40c0e4072a43c0700041511098040c2c442e43c100c200f10391303012030421a850494280564a400c0039224030101d22080391400ba20380c1d84920008808020b098026108030002100410101c001030310650340c0c028050701d4100600b50384040100844007250760300020900c6030507041c0c5030810901d0041480e010400b0b0110725500740300d42c9594902520b030f0070403e09000030000e01ea00e8406011a01c1c1d82e0b10b42c0b0041e59280541422030500720031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 932627706 1250 932626456 932626463
    0x409020f070f03050d0e070e0f100f060906030507021b060c0304170d080606070c0510090e070e281505040302120a061103040b0f0405010e0313081e151003 68
    0xaa1140b10525501201800401d03d201ea400c00c0071040620b4199542d40080c4a40021450320000040380b0002c1c4900c4941c00082200c40004015141c15407540054000d410a800080381050100140d03545401256042001360014065408028003c408003845620038035000751000912504081d40800c220b46c000d00d000408552000c50b054032942d15003001c040100000340e03141340850800d180010489070010380c07201030504050314050601c0b00c1c003840104a413040c4040320074009840e640d4481e00a00c0340015039140300a00084808108149034401c010302001b00b183c940344507006800d803040c24142c607e44806016103d100020072100c40c46030ba00000d4109012541080c10780350f0004555568510880041c0701c0c0e0414218001050f00084a010302140d0705040812070443c0743c0ca049a4100e4010400464404150a481071070b66004a0070140c034488240002c01c003c8509002c580340d240108500075916400780d0305100e54a6401c444050b11203181c01c4081000a041040180300039a071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 932628956 1250 932627706 932627723
    0x507031d03032a031b011113090c0306090515120f030406050d060f03030c060b010c0f030815040203070903020307120c0b220312080610020d030e0307171b120409020f07 74
    0x21880c0703500720745c0340e148480804a0341c20650111403001800303050313596981d806680094000e00c0c0c442d0600180c5107030f0144505050307541a02190b104450b000d8144039900c0014200800142d510a00c098840c0241e001002500607100380b003100f110200450f01211100d2803c0d41e21004031f21011001410315912120340241d43c140000200f6421105106c112402820108a40078000f4019035440c0035509004200980c055001d10000e03020709286a005945c0e20b07240b401180c034a1001c80c00f280e01c20780700b0380c0c003207444004200114541007003448054422140344501551007941c8943c0ca55134140564510514003084564080d0009094510000e00100e40f01086a64170b0034045245010fa0107080000b80b00117000452508000d050400020707031690042c4405501d11030120b00400ea021050981400100f1a4401080c4070824100003400418100391342d030340f640000524420041d00741d40c3d40c1030700b0a2200b560545e05010545c1d00701d4080a0380540e448540182c2c00e0308611610600506e10384 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 932630206 1250 932628956 932628967
    0x30d09031b050105160c02030304050d0326100b120f0402130c0503070905120d080a0b180a0b0d0f030c0c033309110609041401060507031d03032a03 65
    0x201500001c0c010003103044024940170781da8004541000d5840b03000fa4040d4810401005541030001c08900c2c020702a1800342e0202409240142c4441100b010681d078404036041409450074483c104a0002c00200d03034118600700f052158030104c60f070000d0129880d1041c881c0050155101c0e211600044c1c280844200100341d0750322009880ca4106480b0100003510a40c40490749081489240c40104814002080d214140a00885508500a2080030340300d40320031203130406889401d002ca001e20160306c0346854900d4900b0000b41280c8a9060071445107a50705110030215046941c901580c682520300340c1c1042e116401c1c54500900180e000400c4a41d502070b540c890303020310100418062640202d00707112010800a03c0080c3c1d03c4c2020080c0c0a000003030700e408100c1ca01200100315040003e44042540c2821407100030503c6000d1b4020400704100113000720030550b00c07101202254000b603945481b140034010100f50389005107250401e00c103040c40d0304295a860384020862800b81000201c80e591b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 932631456 1250 932630206 932630213
    0x1504020f0c070321120c050409090822030f290708060f090c09120703121d03212d0a02061501020a030518060304110f010f02030d09031b 60
    0x201410f103c00c2c3e0709402030308500055141c45245002c1030106a5540f50755581051240381c0041107001080000d00c90300f0040010203003418001c825640b4018014107460758031411010711145800c0c044c4160808940c1420300004890302d07480003405401441404990424812040c94201d41c44100008640a61304212145038003520041c4602403c0e03400040020668082c002c2e24403040d01d4585407031406000902c83c038140500b0034005000880300300c0780880d0b907988070b248030348004501003c009003002c0400c180404002c807821071481025001800d0300d200d0f8810441a0098002c07861142c0080040c2103295204030340c0c0b00c1d08840d5011008009244244100c891442c0e0040300481c003d03020710b00006580000318260701d1440c0340e040e006840c14003016501200c195001081030011080c03064117a42c030b036031550030103541309520465000880c0311012081100b040314182c1d001d810862000300c407400d1150b0200c2075840001ca0160085409004c51405032240180089000700504143c2102d8050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 932632706 1250 932631456 932631463
    0x90308130b0423040c05180109030b0403050a093f020301050a1d210c0a05070603060603062420011410050904080901081b03090708060c0702091504020f0c 68
    0x90803e400c1e50ba82038890900054403004407948020031824001284262001c8041e030410000500d0f00b181050707100e5444483c04c0500740c400391300040002c80c0310440650400305840c0a02a99405640f010182c428412a22024200f540c1c1c41000003842c0403041140392050340c07011940c010003d01040c0f40400d81c000050280c3d80d81c0c0c03e0800c1c1d800340e05402022001c984a40808203014010144007010744803070307003a940002170381b0025100e20210280400c1d4148078680107032035030342e03400b196080ca040b60050580d00c094000301441c04290621040420f859140e14040081e14100040708044a07180c0c0000740449616404440d4245011151500c15000e541741c0705540711250542540e807600c01b8800c8901d0101c400505200c8104080c0b030340c1c1d6006040d015840400c85030031800003000d5007038480540d0002d9030044000d50204006000004043c480550710644840c82c0034200344643d00004c6500401070b0034015051103c4100c4040d03611150121240b003450210b52130384d66171609480599 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 932633956 1250 932632706 932632739
    0x406030c030e031602100302130506090f060c0606181e06040e1005180c0901120c0302150304020a0902310f030b1803090f1c050f010903030e03040501090308130b04 72
    0x4c5241e0300650491b4050192007500c03883c5102c0080400c8680c1804140011a07001143c003550120f0190316800706992410001c02d0b0341172004000d171159003400420703c80300205081e24180c09082e22010810f1000450003100302110807020780c009251207050126006026074040b02d000f0b030203011644d09603a0704507007007140140540541c0c0740320400e51030b2030f05485149046c0c1142e401004100100f15094061082c0742600380543c200c0b9000f81ea0b82d9001464000803030f4003100b01d9440201c100402d41c0303807006500c4010f03c9041c109515048e400805d0300e072042141102040c150351801d0300608031b1801d240d0100081c00c2c6181805071200d0310b900307109000540885403000f040f2000d00003807021010100c1a13921a1002910344009150700504001e21002c0d202e203494050400107809002081d01002844403c5a0750400000d101d90b150600a00303a40502d03c40031290b82c400c0000b0419641d0090720300c0210781d0000d1302aa290b02c619102d07030040f071100b544517550403c000f00700802c40c2c5c10810390004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 932635206 1250 932633956 932633959
    0x1b0724270f0e060a030c03120e0306010e01030203010b0d020f1005070515330f18040b181606111204030309240e06030a090602030c09090f09030406030c030e031602 72
    0x2d801c1e41c0c3d92400c0100001c0c45020082890b01785410800001d29940c2060b4122a05070401d52060008100031038a401001d83c040c4014800782001003055080c01c6c420701c88420300544181207944095004200f000501b4a02d060140400c0403804090300d2060068cd02100d600900341c0300344180d041d40744041c0c103509854045030428a103044071408d2600042c0046c00742d0400034152980d00c02141002024101c1c41c0c004c50b00414500303030b0107c002425a0790144600c1c45074240300d00b00c0c10301e82d1101d00710324903204d1501c0c0306d54003059040064403003c8210804980c800e123810102100d503103c42c030b400e00541c0800000d1140d000706022040503000740b0800140c5010400007010402103500d18000304801224030008104010502a102c0c10410029a48490200c0c808907240d915907503601e0403070b072044403038400401000c14a407a1501d080c02c603060b08811114002406810415011070712071140e8030030402855a512500c14219000e500f01c0c00042015038140c0c0e4503038030021040041d040300844100d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 932636456 1250 932635206 932635229
    0xa0f0308010803120114040615021f060b04120606030f11152d130306021b010209031e1903030f0e06092802061b0724270f 54
    0x400e00080000507102c0226580030030500592030a091003180b40d06c00070032942c100c0c3c4c481001040056803a0b200401100c03455000b40000034101b0142c1131900ca0030700c0b0090b401d500b0480100540030303c00782981d00351001841e90908490080c80d12100611880d0f200500c039003600380e92481440220302094000305004e5403410407048120b07509902503c520381e4241e06609107903600450b0002d0901c0c0c00e075020f02d00000d0a40c6041580400c0c401e1141840c1e00403204c41d50000f0310910407100d28050b02e00402c156100035402d01540100081d00d4052030001007451090381d403143d212516040000200600040070101e185080c54103000b00030b02580c4402c446d405041c20b80e64648803800040c000d1284000b030000e001c51850385c010130007905071408100180c05404040f100096540c80c0f0041c1544091044012010380114110f41d01b8544594801c0d805000002c105841c3c0b0341c6150f2203901411028130709160710032202a030300d201c202c0b441208038907800142040421000d02020f849001d1700e041c480f40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 932637706 1250 932636456 932636459
    0x9050f0a09092904020a03030f090812070510090314070804090f020307020f060c03010b0c070806011715060108010902030403030f05070908072403020c1e07090c051e0a0c050a0f030801 81
    0x18481c800f001c3c0d0f030094002e0940c0e501040030a1061402e540040c02c64601140c617103640d20b802900d000b009042e440d43d40100000c1540030070404104920080d484003006010a00c882d032401782403644084031400000038001440d204011302070040700c000c0d04041e00100014000c0c0f4041d030380250021031300d60700944100d1400e540302c02800100907100c1c0c2140c0010f01c1c80c1da0300300313030b20b083c803a4009a0308020306100304e840200d0307a00c4090104a0103004015508240740040c4603045182c03006407525402c3c41c000300e00c280885a64800d482505441d00110f0150381c07a1590710b41180100305152400700d10501d08001e0102c11a481034070441200e85202c11980781a17141c407030008000001c0460100e0105112001190160003600a03041c54440c0e4003c1d0703044500b080005540b075240b003200321a00c1c2d030000c01c0e0511000c0b40364072600014214a10308241410b054411191951076502d01d0404000030102c1e030220824070444064494650242c10b49440c2c10b080c0c541036115029a0b00200e0106035850300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 932638956 1250 932637706 932637773
    0x80105060a03080a110105130201170910091a0f0108071a030f07030905190303060b0c0d081017030712030e03030106140f0c0f060601050a09050f0a0909 67
    0x95540201402001d408640786983e5819009500100b03081d004e0007504102e0001e249000c0c803403284035819141d0b602d024100f40f8400103100040c000000c01c08000c121003408218900050341c4901d0300c4c2549400103040000b03080c01c142000e2541703c062390684140c020041600c20a001890480d03124108640c1d4507500c07054074a0102603240350f0f42105020900006414021420000740c00c8116401c0000780c40d403850711498140707251a0000084d00c00b4402030b00e02015030500c521001401403140c1070741003849484805031100060074490081200e150042080c20400751041001131242c6807204c4148071641c64016125007100c0740c241c038500b0203c818109064000e005111500d969100511300d142e003801c10a849444095101103243c0809004994810f02020300900c280300304072000f04400300c24940c02c1c526081d401826503040003c00e00400803c40c0d0064400d1003902d20403680654060303104408a03403c0e0340300d42c2c420740e0490306060241092101d07100c00402c40420050302039104440807031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 932640206 1250 932638956 932638961
    0x203041d131403070512041d041401020301080d11010510181508160518010e0a020c06070305220c290d0c020601091116020316080c0f241308010203071205010801 71
    0x448c000c2c1c40c0c0346601c850b401d03030013441c142c50382c1c070500ca03001403421550851030050072a002604000c10030740c0510244900203400417488890b0a034110001e2286140800c000d4098244074821040c0e01d4420300f50f0071422101ba6000030032320500042980d20421b5540c01010b0f039400f020104a20f03030359120075010602d400c11018001c40b00302030b292508003030303482c0a40c3c182e040c0000900307100220b50300780702002d1040e0341800382e20300400b0310750340100360303400d091b0400d007a08640400c2d0400e500800d80c40d000002012140390504503001020444041700c011380c600c0351034004040c24486124400a40d4080c0c0d90010780c084100100d2690841c3c080780c0e2900b10000c200e82988540c010100300600c400101d40d0003070070103444024809002c0e01c50281c0402c2d180035643c01150401e1081d078104281e40c03265400c003d1455241d100303003169940410152611044003088900d4596a4541c03400542411910602c101c010020a40c41008659038900404011304120f26184103c024a023000000a01c000050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 932641456 1250 932640206 932640209
    0xd091112010b1e13180b011211010f030e1203011d0c12060d0212010518010b092409010305030901141215131e0b010203041d13140307051204 62
    0x380460400820545007001460b2180c0382c0f150f840304281d04000715030304403030159152044500c00c483d2410740c66803800400310f501c140c00001d85c10303502005000110740d4800400c441c0307030020700b0001c2c410240c0e154100e01034207078410074610751311540f0540c840030318101d80118100d0b441e0700b110400b0400e5a0b2000303045880159881405001c1c1807181c00114014040242d410000007000a074080440d540400c04001a11171031121f45d940d80c00410041e00c0c0b45130054484003040d0300c001c115290ba00c000254052034060541c810100d000101c1d00d0108065038584008100020705206656940e1302e0000d03500d904c00c9005600107030700542c410100b001444140d48450030390741004d94080c0c0c0c880c40310b00d00c40304035840ca00d42d1094085c044485e05901510400c9503001c040001d0420710346856400c40243c07041050701504551081000700462040c1d081180c0008882070b4040e44241c581c9035144c400f60001c504041c01500480d2620410924000014043e1610900a5907003280ca103d04090080c00b49 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 932642706 1250 932641456 932641459
    0x150405010f0e0706120b280e0105010c1b1a0304050d08060d0303020d0f0c0201022125020109062903070602060604020a090801090501230118050406020d091112010b 72
    0x108003403105501450610b001744800c6840042e0b036101034000245404000c0402c0c02e80e000308444214440c40803458460f014012080c12203c0551511000800c00f1016110150088070500030b000060110f56002c20004c00380226080d8020707400c0300c20b00d07410b640151402c0310175118105024070018003550761a03216030780c002c0c070310280c3c58190f46059020394009001a8030566413400c00120300303040d41c41042c680036029800149c2f030300342e03100079808454004065102c4505d4403804000f9141c40804048080345a40741c0c0e202d1134524003080607400341c4441080107110908241c40681c0c0120a01c03102c040c0c1000e05606503e00f4102e034410f242c6c9810090041200580101000640e9420141c004214800071458400354080d80c1f00c42150031200407647c116181c2c2d440701c54a0816400350400340c851444150120740455160100009404920035031102c8a251100c2c000f9043c40f400d981503501c801d00019040c440d1140740e02c2c00c4080050881081882a5900c3c150840705120511501409150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 932643956 1250 932642706 932642713
    0xc151e04150e0108190e070b1c0228050f0c030703080a020c06011e2409082802040f09030309020907230702041d1f020a0f0311040503150405010f0e 65
    0x4810b0951840c04510341081000311ba203a140c200014001004840000d242e80c40c18070351070b200c620a8640f209030420012a20340e03070060104c00000017400f9025021200c0031500840c000c42040c03400e07140d0b40104031444c1c4010b1030202e44e503d80e00e24088001c00d1641e100b03546132078080d901c507a07240f0105c1c080c031171004119621290041c4603840c0001c03455408240100480c00107550790b18410348103042007604000c54001d4540001c40481e030060002005407244202418103015998020303c051030400c880200303c00000041c04042d9196540441001c40c240700050290030424280900030f8013150100324050b040d20000a000a0303c64040c4c01c0c0c2c10590000740581e0a00010814100c54004400a9900c140d0326402c00342180d00d07142c1541d80d002090406001000000440494103101c0140000f400a0041018145e070a40c0210118840f44450400182e0303450402054009070103a40c111603014494100201c280d41c034550741c00b038440c1e0b1282c0000c0c000d41d42d2190b101c0c41601c0b48020031021a0b070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 932645206 1250 932643956 932643961
    0x305070f02061603180501050a0c0602030a06150c021011100f0209041d10090b07030203091f02120c0a08040201110a050105040f020916020c151e04150e0108 69
    0x10011042400c855000400c014100410100c0a003101410407600701c0c0452003564500c1140c2c00340c07010b00c400800c1c09080040c00d2003d071400c090302104c000400280300660000004050400660114024000c522a49602008200d0010f05030341500f950580c402c0d031a5104400e0654460070a20a10f540c55030041c242ca080e80f0b1040b200900302081f0703140c039519000cbc0280c001c980c59a208044e20ba002070682032900c640700340a5541051086203001800c0c1d0b04041418000c00d80d0b592241b90422001d142c016507d0f80d81411041c00c000a419070b010000d9000828002d1b1252140c0240201a4011114041c0c6440c2c81503001030070b101d00041c28000c24803d10000e800340d1300409000225507018020340b261503038a540c440f82114400c807005c40f44000341d610345506604150a10ba5403140300c03401c4c1c0c89103a0700d886101035611807040800710710510b14090a440418122820307202da19110004481e4490800c2c8080403054026000e950380814611203c0c171140351081c9481240c001d01a1140c07106038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 932646456 1250 932645206 932645213
    0x712090606180615020f0d08070c02090c0405100306080d050304081e0a08090c0a0b0912030c06150603070e190b07030c0c0503070308041e0e0a022104030507 69
    0x82016a2050310031aa50301000928404441ca40086040d8107100000340142480043d80c003088000d80c41e40115409400c01e0318052100041c18403070404103041ca40e101d0b03034a480d0100c60f20340344114002d4006242c201031001e850b1440000d403040c1d40c001c582070804030055401c100e0444045204441541d40000e40004c5558000c40056400a0160843d1844c04210b0300041880540031448150200c01c0043e0092000d94040c0c642c80d0412050005403085600040010300103207114090000b151400140f48102d55440d1100c43d1810000d103001d0725111003102c1d0b9225200c04044039510103c181c1409024440d10709481180c0c07040045440da890620350300c0003840340d0b40600c41c10003100c0d000840008100440900081c0c40e12901c2a42d511150781041d18080d10710708001d0b8800c5020b0b40c0422010300000e6088001c2c2c40594108403842c04480c004211403038450380c000d5000b00a10000c080600c0154480c0d0340003410015082a042a40001c9148052103003000494020707001074400c0c001d02001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 932647706 1250 932646456 932646461
    0x7060c03020705150703060608011d2d090708060108100c090506071101110105070e0d02180117070803090f01030c0905130e010b0a03050a1214030117010b03060712 72
    0x48018a00c0d0041c00c0c10036541d10545040d5142c8580c050078a440720811042d0340c0d050040c100944240d1900c03246c81e515003011700804409422505245184243c0000c201910030352802408050031181011b0381c1140e501e01446089046d1a1209140075400000c20000170001d20789040318103100080014040c3c2c1c107503100003002d01015060412040480004965855901a00110340109005035081080100244c40b00c8a0142e0303044072641401c04120741e4a070002c1704080e030200b0990341000d90b11301d07620008691010507a0a60104024600040ba010304103400d030800d50000d400444418076251440c560342c900844510a80c40742000d80c0f9010715511a4000900400b00360816960040e180c00028101e164402c02d12807105a40c0c10b01408603074024080c5e10171502041e2005800c00f82142c03100c54542070030001c05480c0c03404031400c0300d1300d082c4034041030400c5c0004000041d480b0358450f01261943d045440d0000000d608003070414420349000b0503000c2c00b800003910780040b01440725000801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 932648956 1250 932647706 932647721
    0x140301050c030c161b18050907050f060906090604090e12190f030212010b090109050406050f010309080403080a020604230d1d1509121b0f040b060a0c140d050706 71
    0x11070307407451803070113a406417000b2684c009892000c440030442100805480202c0c1c81c014007824103030340115002c000f941c40d06031240d030305550180d5a550323540e02c042d0f003c680240304d4501d510341c01500000d000114641c0c01c2e400714440795401429a12031502001d104400d40c02100e122104044050010805c018010301e500381d009500c80c2800340c20404590007400010809901c03101c044c41c0700080c045410369101c0a8100a403400301d6040107540c1c18071011800e65800340c1c0f072031418542c0e2a5803100c00d02c910300041c0c500841d40907050a0740c8800c140780c02919480300791800c49201c00c07801d400040402180d8612030069180c10028100c41c03400103012102101c1c601603851040701140c0c03a4401c540c031401403905009048040156450041900380120304400301445411604484040c6070030500814103800143c504a40c682002801500018010b218003008294000c900082a090803504110103030302e66402080b46442654002404544403503100b0708150015004020410000d0141c1e80200d9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 932650206 1250 932648956 932648963
    0x1180530160f020d0c05190b030a270c0e010902030c03160315060503010509010618060309050c0612060a05010e01020a031d0d0b04060509070311010e031204140301050c030c16 77
    0x40d1000c0b54003c82c0b0020001e02080d506194110414000390420401c005286140340c926100d401e407a080602c070140c08058407401f412a29904440003030f201182c035040010b41a003580440100c0c1e20f1410007244a0103216030650511200700001c0c0d804035610a49110b0b1411422061555072280c7d0204034440c00c046107103041c90350710808038070141c0490034403a01401c40c607210b1719660b505081c10062603480592150f4100300c42c4150400c002841074602c1c208544031420f0221ba0b10540345011070818242001c2d00e90001c10110b002580e0341455050603001d26016120854401c3e01d8030011200c00d001c0a0515015a02448904c80000e00c1251580d201501300070040f10361000107000181c1c00c8107070301c41c255020740c803080601090004034460309802219440013000300c0c61031961190b001c5482540f82505000d0f000203c030887c0d8800340500007010785248401640c0d00d4030b03201c8510254403403400302c074042d42c0703021f0005282c03e4001d0308590003414250981030800d821134007500c2d00d620741017030100d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 932651456 1250 932650206 932650223
    0x3040810090218062b0b13110d06061d0402132d0b0a0b03060a090b010c06230405010c0e09040c03060b0307080f010204031a160e01020118053016 64
    0x20064068a440c5d040c2d5603040e108151a070101e41420a82d030711042c050510108044c142c2580000911484942401c121040d40c0711482c0e200b59083c00401414180c0c00a5410b410391021170052494916115220318030843d414000b20048800520803100707406100e00586d5250514910395842c0540d40002c2c40b2450200441c4842c500004100e84018950062001050110a00a0a1420150f0140906001d03d000c01010581b440000c1050913105030142000b952400c8089600701810b42001c140c81000180d00f01c513003018500f2900a080800d58030b0006141065403084a180802000c1d004580010106422604580f034502c010088000b51070f915214030000002d2180080c45494944107204000680b1103285080000d0b201200341560010304031000100b06945e910200329540d1000701c1e2802d40c0f08180b80b040180e00500c010640d10001d0740b95101900c0801400240b4040705005004104100d0340a04100c2c03c1e0099101000c0e6040c4803040c0940a12215500c860025050054241e03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 932652706 1250 932651456 932651479
    0x8010e0f0109050c040b04030b01091b020c0402030c12070f1101020f040b0904061802070b060109031211010617011a04110a110a0f211107060c0819020304081009021806 74
    0xd80c46d99503c107510480701050f481c40100f290702018814000c0200e10b03070031452000380340940001d403035803903080070701e1b214990101c0454040d07011034041d5203000c00000003501c202d0810b00c5014111810302043c41000881001403040765107818002d541d00740c411015000d042a060540700e102c541c00500c151713034010f69507510010781c501d0000107100b51121154801a654501c074201034002100c020050350521255560800000b00d10101d001b0301181d441c44d1018071034615201c018050001e603442448100c10d4071403410308648040d440200b08800301c4030754480e81c501e03001c10310040d5004103034021050881448408803e40c02000e07001030b2000740800341c03142402a5564105445039182c41a40c2a40100031f4080034420b54085e48280b8299504080c0c00c0e41124140155a507c2140504820003500c5003a0300d00300002c41040c3c40702001c3c0c00000107040c1a824000030344e0380c3c0040c031801e141481a0110413100c1c00451050101c41900070380701d403000151201107001011005404a0b030820b168914 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 932653956 1250 932652706 932652719
    0x302130e0312011d010f030609142d01060609030803072f010506030c090a1812030b010822171905091e1003180b010807030308010e0f0109050c04 64
    0x2072240d42e0461611450075410312001c07a20b10002c140743c0c031442c20400001840300e140c1081005080342d5010340045440d00c0d40e03140c01840b0350300c40038106006200703042128000b00640c85008030741381c81050f0850645480306910b6800d0711020322070540411000681031000c80d10301c0000f154405201d0500340941260340b0100105003580f214120403032001007500b2030384202c0a004854021804400030701d00905860006045002c01620412006540701d084600d0240706101440c96282c20580241b0002071050000d805449082122400118548001107007501c9141a8000c3c800698859a00c0054070f95101d46000031404840c5420307010600c140c40141600b41d0070605d941e2101e90f00c075a1a0010282032000111201c1c0000c600c4410f0000e840900303494040c511080c0103298030b808540d0b14498905103408030990900a01281c0d00100086a15000029580304991080d95590782680c0d98607084061228183d40300c0441c40c00000040041d402c3c03982002d07070404a078100b01450540c0d90346 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 932655206 1250 932653956 932653963
    0xa151404050903120c1b0327030c090f06030d02060106120c0c08030a0e010c030b06160317100602151905040c080f070f0503030a02100917030702010e01110406090302130e 75
    0x40c4c041e1458100001c10180318003040386c0900740100b0300c000a43c10006c0c4001c00d250b596045000d000b9401c1081ca1000034150390070020200f10038009883c41e409030400c60011568203c084900d02e00a00c6081c8205100510005206040b03483c03903a02e510030068124003480283c160f000710341d420080007040081c0172600400040d406040600000114000e0f00c2c4003090030b554851100d00300b4503150600894240d02d4401c100c036558a42c0c071170a400420098039003a038024407100c91440c51840390004000c42c00140b280c1103025035115401719005502c46500c80a0006011903040100700191030881c038102c00310350059070b0840d01c5107400c01e2246403110b08583c0f40160100701000c55a0100004000003400400c01c02c005e8030064002d1032500d8507020010b0754610702c42e07070000301859540d6850b00900c440800d121000f010b40c2004960b590a011034000d019104903203100c1c9155291403104000d0443c280201c4049403159121034030040e240d0f4080000c800488412043d480c0e480c0c110303010003000e060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 932656456 1250 932655206 932655211
    0xa0f08060d0b071d03060c0d09061503050d0813150209030f10020406080c0a02030715020d020d06210c18110705060907090e0606060a020f07060203030a15140405090312 74
    0x130f079036060f100202c80c1000c0c0e494400fa041d4442c080e4101c28284200400321400f10f03140418092004180c083c058540240140b48100070401032080390078002c410014085130010707000c4103030340d1803035090b8072142da00d00e40c0d80200000007407034403a03a0b111070350441c0c0aa8014210070940101900e14107042a11b0290904031060a04842240c0c0042e00b44802c6d034104030f260b9004080c1135401802c1c0f40c4041406035981c42544809400f0003030001d800602045142c049402c40c00783d505056444041c00d0110700c020700b03080c0c0100158040b217910402c0c10340700000090681c603500604100c0c2101d14164a01c0603180c50741c1200701013580c8599481521b031850304000c2180e00d104000030b203607600c1e000e41c0380f904040103078100f001503500b8640d002208000004146810940c11680d2556420311480184d1404030011503d90083c040c0072000610f081d0080040d41c81000205024841d040310040e0703030410b441b10750040c0f00030b443c000700c000b51a83c01c0c284e200c0c0b42c4c0028640100d80c0b50148101e0051903039a001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 932657706 1250 932656456 932656471
    0x405010818010b040c110d08090d230d1401090902100f09050d08090315190c17040b190c02030d0207060b0d0606091b0c020f03031309200a0f08060d0b 66
    0x4290102e00c6d2940204082c4541072000c3c41c0450340ea082c111000c0b07881d00b503c1030001e01007000c07200c540c1518140503425542d070680e0440d07106607a440c80002d14801b501c0a004280200101c040c000680c41006024903001550b00030059007038030199100546040d458126040100000e464010a46807035040000500034001e242c516143d4035540c0805140a100c3c00107404040d0580050159a5031100409001883c20b07010100d19510103010171190b0b40c8000000d2a030114500051100b07008060321481d0140c2c54500980305007004242e0014241c9982140c0310700107030b00401a0f010b08007096405418002d01c1400045800403142000521410207540165181d07542e910080010740514400c141c0d90368201c00181c01061604d480c054041050160f029025144c0c0850341c3d07802e0354062045400d02a4080101541c040d150030040000303140e008221344030f0040b900080780e900304840c030694484071619642e00480c5242d680d41161444000b800c2c541c0c2000c2c802c0e84000c002880c2e100268410700c02d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 932658956 1250 932657706 932657717
    0x9150c2a03050111130b1e070308180d090b031807031202071a070f03030b0306150f1509060703020f0a030c03030f0b01080a11160b0711030405010818010b040c 70
    0x1c6042c00c2e82180c84007a00c94521940c00c100d03d03401540806101c0d802c8a00320720341c90740c49401003001005c5865100c881884210000a503900070140c01c100154080c103c20390424484800d0300c0d01b8155161508200031010071240b210820541a01c4001564854007506141c1281820141c0141c9030270321582044034801440000a0f800a40c100120f03c0100040b0b00f590501c1c00c442c00e5004c0c0c2d01d201d58040035007484140c00515040c1806904030304034240c1c0280072140140360140306101801c01d00788941e07200364080961000c0351315000283c58980c0071480d01d038614080040b401c01c1103e9008590450542c0035841400461120a01081651501070b864840e90003256144c01000c90b9140c0803581d445624041e440000ca0741c0c81481d4030b81c4600303690300014218000112180060141d0003008038001342d05e02805e010401003c3d4450f004546a88803050050603811b40e01e6100d02550045500184106001620080d4440c44281c003500540c0d000044c070710081000310b000e5805545803440440d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 932660206 1250 932658956 932658959
    0x150a0e030d030606110c0a06030911130606020114041208090f0a060b13090b070516020d080406030c0504030b0606030c1b0a2121180f020a0609150c2a 66
    0x81c3c02c81c0c1802040c0b400c0034046e242d10020100001d24581c0140560010503644545040401c1035a03506844201c2000b000c05809070601c0305100058038090141d10010750034100c0c20b04880321503100e442d00403680700400a0001c01215001c84034208020004801c0f032103210070a420a11080c000d909185004220208400e00400184408120410a03007150303180713006020400300d1000040282c00c4503c9103400c503603442d002c148200d00003101c0d07070010b584250941800d104000d0900001d0089501c1a14217002102d81d03118141c03038a005034400584041c0101c000180c1034900300c0000e6030311280c41c4000c0e42c1081003d8813904000c004018440200398043d0812806200031645035050b4440684890800740d880341c81c00602c9512180801c02e02110103902140b141c00711904401030129800460058210780780c2042ca0810078098007d90050a07038640114810703206600140070340d101110015100222803500b11111100180107031803001461405d0b0304032000c075100c1980070015400c0300e0307440203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 932661456 1250 932660206 932660219
    0xd020402090418060f05010b0424140c030c010b040203010b0711060d0e0c01020c04050c0d1d010924020f0414010c020316030309080d09051905100c14010b150a0e030d0306 75
    0x6c03601070f0001c0300c8408c01030000704081e2428402442114000005682200e80c280e00207071554111707101d1804800c4004a84038003000030010142030341320a80002031010a64030024041284400c1c007500e0700c841000c01401d0041401710b0150216044d026000c913290102e50084dc108640011950312402d13080b001800b1000e42e4100000c1089480c00c80f01048603042800825a403842504512568039071150a000503a0202c14551010341e24010300034841524145041800e441005449045070700391107102442419840c405e813985010092880d51030903041024803607000c071055520504004000700c038480140c4080c0300000c8221035200d54182d40d14107503d40078148108030b42254005901ca01c6480e030945a204400500301c4406541040c135103400c0c07403035120719035600e40c010076080202805000346d1960b04c03400f81500303140500100111120a000a01e003038940031101941c3c004060098400d5400c158001042d0030545420180480c1e82d011021034201103003003500e031010079aaa441003110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 932662706 1250 932661456 932661461
    0x1810230f030d0806010c080c0a0b100b090109030201030b040e01060306020a0f0203030f0f040c090513170a082d0c030a060806010b0d050414010e07081b0d020402090418060f 76
    0x40c1102203014100700021400c0041540400a240c58100603944101e00c0a01100c4401c88103408003a0041d0750b4400b8090504804000342611017031541480c040c0300003121410041696075619059462058072407075900110007810f40a0300307103680666222441021074100340320750402113118400250300c0b20361804000c0d140c11541407480301550410004c005202c0b10b4040d41c0350b8000041b04202e10300c0d8640b810440000841600180c4910f072500051140300b0300710b4208000098441c006c1c00c0748400c1c544640100f03c1c01183e2440e00842c0002020455150005114032403041d0980c619080c20046180c0c180b41c910420f46030780020b0080002800042182030003090042d041f19401429107501d45503150045200f800c00342d000096480c4003050030800e020020b0b54184542200901581c898036800c1500c4510741c0c46034908900c40c1441e400600c558441065490300402071015500580307076000e00c0080d501c1810041d500130341d40d00b41c203032024058141001c004c03405040c0014050780d030303250072004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 932663956 1250 932662706 932662729
    0x60e070302040f1205030909040308010f0510020c0108071404030c090e0309090424060e0f0a0507020a0204150306050408030405240718051c0b011202181023 69
    0x41600410060003c2d041102c0307040202c1d0010511a000c090341400c1007411070091981c4c1d503611007071403070520042c10307480500e050680301014005005503640340108941700e5075500d081409a0040c54521109600a108171648078050f414409005d41c0001c10940c526845a0000c403000d81c107010060102603060301c0740100d181140d8006500e80310241d400140503000080004084840c180d81d44460805850807000c0b07281c140703000a00006444031000c800f00c0004850481219410301c00040707034001540034041c00b621141d0040c0c102141540c00b480080c190400c040c03108491107000020000740c051140f07500c2140180c0800d6101e04051411500f8001500c08441e511300340d902e00c203044204400d1b01550809030a081c04d4030b200300142d41d600c1d180f040c1341c0c1c0510b03884041000d400741d4820254030b01203102ea2040043c43c21680c1c85007280302c0d180902c20782c042c0d000b14401c1c0c0781c0c0d200c2c800301c2041c0a8100030b03103405101400d5568800c010341044140c615104002c03079001c0d02c0130035080c4002c5100c0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 932665206 1250 932663956 932663971
    0xf09050f0123040801050a021b1501060c020109030c151403060117090f10050601022407050f0d050717060f01171e0906010e06030d050703120b060a03060e 68
    0xc0803566100c0024080034020303a88044105030180d81400d500003001c1150300030664103000b8041d03845c1103000b050003500413603160701c80c181c0709021041040c1c40c041000345036500b409903010100c1c0d00f00101202d001140b1070080381800f002c078001201080c1841d140e040204031883d0b00820310314012000403e55248030070504244501802440704d181e0304403101428006400c0c0308003086994906403d841e06500310820345145c02220001000341c070b0f103904103d10070202a000c0b605070643d40c8114102100200100040d600082c07404030f400c9030301c5040208405e00e1907192403400c10010321104821260b0030baa6600114245602041c5004200c0b08030641c454002c0f00d001d0b60760700c00701c0006850300070a0b20703000900c600e03407000042150805030050380000b540c104041105181602840b592002e080c02165900700d032403c000303810707441c3c0000c3c12403c0c003c10b60b90300390800c206680c0950b442e45203041a0544a62103410b0012030380c0f5061302812100b400c90343c02185091500c01ba00343c1d802c201038582c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 932666456 1250 932665206 932665219
    0x901051f0312030f110a031d1504060906290301270210050d091401050132030a020d120e040216021504030204020708030403020c01020a21090e01060f0905 68
    0xc1000c2420240311041d0b000c1e203800c000c500c1e00511854a001400910310401c0c0000d000f0907034070015940b41d842024002a0480009020248403121030f5880d07600c05802d800064040c00001c0001c0c070b5903040081d215118a8002c145140307200f4544024400e10302104d014500e144544521919003402082803030244100c01001d4808500149090500000000ba000354203100d610b0208611590485400042c03158042049900c0c030316025071038924103200b042040d8240780000c99086800008030400400b0210400001070121a0001d82960b400c0303105a418013948a41c6005a2a43c01c40b0300d0455100d212035204159041101902c4540280486405548184400b45464081da06103050040e012640360082c90170020503003940e480340c1c0c0c0000790001c0c004a131a030b0400001d0406540220b100ba000d0740c603202c4180004981d00c2001c403d018050100c00348502030912810591405040030341e1030940716164980c500b00030aa082a4031240003d080b034103e51400c1c60380034101801400d411182c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 932667706 1250 932666456 932666459
    0x190c0b070e09040206071704120c080c280b030a141305190819030c081b03010515072307060504030f080c0307050d0201090303230f0a090206030901051f 67
    0xc10301e20b00005000a0140900161035024402c801c0800349461100e450415510380d01d0309030600c0900d04400044805a4540101181100000c01d4008040102030415030642c40fa4440b42c0100e043c0000c07003007541c40c3d414040400c8a0844000452054500d1a004500c041da01c00101c0da98083c000c0c42071300c1c2c0e0a07882a80100040010456403202e4019080003804107001d4206692244194140812400c5184091602c1c882d0540c01800400c000ca45408142d641d950810361011101d00c0d403100f80142040005001c1882c022402d0866410f0024102d402d1458507615074284420102c520302c20306031050340d1319414403420002c00d4082c0c055860b103542001c0c80c40c0c0d03070303000140717041c3c40000d0107510041800c400c1c209081043e03404854001044401141d000d0a01900802c00759000303400003800d02410401c024601d001d555400c1410307980c04031130783c0d481111007074003a031000d081000d1860b01c170740418000d603a40701c0285d07000e0b010107000043c007230400c50503505602000540301107170340f800e8210 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 932668956 1250 932667706 932667709
    0x6031a0702150a02040f14030607021b0d06020418060e060d1e03031e150b03010302010e100225080706020c060d050907050406032103020910030f02190c0b070e 70
    0x20700c81d0210100c40e03040403190320f5448210010340210707085854016091400090403d803240480813404ca4241e007981c2050b110943c0482e01c400c2100103803109868a48008151410480d10781a01c00d80240c500505207034403041c40b04451380880c0000c81d220754451405100301142c5401080e00300300d04071140300900c060b0743d860b110420340c6240d80d182a01d000401010070700d8020342001d240f2421b1090b41400f20103480c0728000080c0804860941e5041c4c076910042024101d003002c42c0d05a81d0140c60380341518010104219006001021400840c000c00c8000251828140110096104400142c500081c1000b41d40c514120321071b44160119440260701c001d44c1e484400444c0c4100201d101d01245c542e40f00305510b0b1901000ba488550018a803001c008144421011740003202d00340f19401d03000150118a00f1800d13070141081c9281d10402100440d0062800b85d8080c124540a20a0150803d41c24121151150007000c0441004c80c00c285019000c00c080c1c0c01c41c1a80c0400d0a0800308014040701c0b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 932670206 1250 932668956 932668963
    0xc0306080c010e0a0e2809020d060e011103010609030201080a11030f040c05150301051804170c010609060b0a12050f0f1e070e0112020c060a0b12060a06031a0702 71
    0x101c110b06001800c2c43c21455502d981d00320801074012800003071514281802c0c2690325203002c00c0070032418401c000c850701001e0101e00484400c150000d125065070034842c0c0350040103211030312070a51659a901030091028241201440c020400358035141e081d60300e5130002511300b081c01130801c401c091601c4150f1f40341c4d08044c0181c81c2c05c07803448141d42d03000c1d960710314040d00c4480194200690003a1700c80c1340081c2031070b4100d0056042c0e5a0541d05440601c0d140c0c01c5100b01c27005c1c207580c01408400308138403402000c10308070701030948850110004a10a55651501c40c1191095040090050400903410020f2500b1454480b019011001c04000c1e500d407c0000004100c3c014003500028070218010820503060200c41c60350b04482d084081032a070800c00405000d00b0602030109001c18815000c1005410440c8261002058180d000d0841907640c2d0810200400580320310720b41c0a89100201258000100691845100090b1f000141c450841c20441500d41450711020040000c0d141084407082e80070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 932671456 1250 932670206 932670223
    0x302190f032717250c06020d12020c0c0a030f060c140403020f01140d0e06011235130603050a0b060706091401021303120203041d04020d0b01060201020c010c030608 72
    0x2003e000c0307030364402443d02c60900c2444424070310f00505605030307003520800790f40c020720f03682c49842800d05a503542c03242680c95a5030882d05201040740e10700d250f5174030001130300184040c0c1440740c00e40e071003ca03010700000e81d43c1d030182d0815903000d90452401c2003000000d03c183d0803207152030b050081c60b1f410591390b0301e1102d10540c000203024405410a00020741d016aa4481402141040301c03501c40d50441d03030410060486888001c3c651040f44000aa0041000711591072603801c0041e2650100300c00411011103160440c08000301451039500032136481c0e13100e0141ca4012240030b2040701c103d251190080c2138034800340031000810700e407080c85601c0742d48000c100c960766a44a5008245028107051455a114804243c402194000109042600d64650114082d00e100e800d443c81c41007070f00003080742d0368040c42c0039541482d5100c80070800c2100744a0205540148000c19000050340360f680c4051034040c00b81c2c0144003513034001c280000040030a000d41c00621002d0300d410807406151400699440051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 932672706 1250 932671456 932671463
    0x210020c0d06111e09040b22090f02030109081305033903330603070611160906060e010228050102120f010611010b0f01050a0302190f0327 61
    0xe072105007000d10100d0081d1100c1c0003130785030700f01c4d1a640c01030066030a80d88400485e0307202c0d03480e024011005107400440c0e00d084210165080c4212010200110f0040c142c41900f0340c0c01d59403001c445030041c2c0c0d09002d00c107581807151146944514159023005910750054200c00e201c0c2d009513612180c1401d410040105141a42c40b64008540c00104401c000340c0d804a00f40f9094042d50301420040d0720120107215000303e8550141c0510315450020b0100c142003a2303101541a0000c40c81042840d200f28414114807419005649014290b2206440010031640c0a05403082d103c400170850342d42c02031580d5607049028009010516100d03440300240f040d00011100641c00c080c441c0c10203104013541613480d40d0001e030705844d0386030500e01e65000040d102441041c1c00200602c40344812250103001e810790242e00941000c038006508001540d09800010160b01099400d00100e04100b03c64080d560011140f074550903206002d0070300003801d44034030a0301600658940d44d484401c1921303405003198496003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 932673956 1250 932672706 932672711
    0x210a09050607032f0a17060303040e270d03060503030c061f0b0403110a0819060c050d0c12050c040302011d0118060e100f080f06040e01090f0210020c0d06 68
    0x2040d00b802144c1442c0411078403d0041c810090400c51102c40c0041c100101c0030b40b42e1407009000d40c144041411700c21151180c1641007840304000c220541c0716000e801c4409030700121442c9210000141844100c03070120704169102442c01d41c803464052091350086d09058015504c0e00c124040d005030740c0c240181030700252205c80c841c0861150a50629500a400e16070703021039569581e42040b414460751003810a1054601500c0028022400204550100144e054441e0700400d20340f102401005049010014894100301c0700c1000c000d144100381d96070f10192114004141600c40003000c07100010404001c043e0200320900160780c110078034851140410902d680c00341d0102d40100c45145403110400c910050080c2c0210343c0c80d400c0043c2c2c580c1e02100390345c6039001949402080355080d0a15a852000c07070f000f1400301e540507a038a039226500801c007038004a00329140442a0f400c5444119041d145101d10150240440c60f042c4035216800041c0d20052100f02e005600041e00c000c0343c035100400059 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 932675206 1250 932673956 932673971
    0xf0f060d06180309030501050c04060c08090109050d0b041a13080313020a0f06020606041a28060302130803031006110f0712141605041a06210a0905060703 68
    0x500e500710188207100e1400d40b810300e40061801824100c0d5a000441c0e89500340400124007a8001007600d08440076540c0f86503003541151521000f41d4401d409460402002c0703600071606840d5010910f108038403900c5103230010b1030141041041603902d0340807040200352410600140308018040141c1d0030740c004840503902c1d15582405a17100c1c1002c070300203402030740d20b010000300d29400321056002c803809078080d25820f5598000700401c03520b03450f12195070398039010400101818000300c40481d01d0211000403d841c415118950105062907001a00103500022008030103a98085003d0041800e03000660031411b040405540402090041900304180c05040003c805010010180b40a00c910103582038161245244020300c0c070034220a440c0c40c000140c44840e0700200041e6458002458002401e00074180820413019180e28100d080502c0035064801c0c02558070100205089810041c402d40c10100d0710000400b0108010b10900d4924545403064020440100d00703154488446d15000030040c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 932676456 1250 932675206 932675213
    0xb1837200f040501081501080d0c060b0117101e0503030f1e0a200a1a090f060109060303140f0d020d020714010c09140d141c0c06050f0f060d 62
    0x1800001d040381d489070400000140035800429280800c3c03803e0805564140c1c0c03030741c03041c540d1140d08280d08000141c08180b0000403404550010882010514003900743d881c2d44d400003900e119003914901c0300c0410303400e0108070b22418194020b8424030b98101403140706140200003601c0340030300c416412500714005112440c0210346a03c10406d48070600d011303a11800b04c0e80008245e0681800078508414181c41e4065105a002074000c3c07403194040d50300d15070707200103041c500c44d000c5003e056080b5034031858184a28094003440740c14007070203841800103146442d43c100186034400501410504c80c42c208121900076460340103d03284140000d02c00340c1d541c900000d03800c00a205851001d02483e001074440070304400190000014020140c0c2c80e014441e0719040c01c4115590107910290b03018040540100020303503132255010b00e0200035402e441c04101d90711a2002840d049007002e10004181014000402046114464000740041c50640b40b624003c06d80900300701025100034402cac4101c1081d04100b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 932677706 1250 932676456 932676469
    0x18010312090305070308030106020c0a032f030106060305041110020d050702030a140a0215091e12070303111c14090d06020a09051e010c0b183720 64
    0x150341c40f804442c204c56407424014415082805101c0042c02444107130805868650301240a0300d403c40c80e0300b801183c0c40076031086165240c6040c1e0a621651409840c0310750750a2103440018141074401240b185000d20b8101c000302d00555010340301d41c829a908800031507000a955200c215039007031041c0d4545160000074a084901500140384441140707003603442d624042034484004c2d10030f40d45500200c8100c24001441c0c001c190540750840000c07400f901101c404103100c004280700140c42d03001014285194242010101d030415404680e00c03000300350451504011700c040c61402e25440b440c0200c449c54008100d000d80d20600114040081840c0c40d0550b5241000345000340d001108541c2d40f158400041d101d1791040c8905481040e00041422203420342030000d0b21007540503500c2a510030b12507039400c5034140b0060411900f8061a810400ca65001005030511286901c4440404a0700c88518401c1404040081080b03440c140613005000a2031001b0813060030442e010a250540301c0440451341 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 932678956 1250 932677706 932677709
    0x14100206040f1a100512010b03030a050a031404060b01170106080f0604140a0621050304030204050405030c190c0519091e05040c0312091a0a2d0e1801031209 69
    0x7100d02e9560510803c600c210754424103d40c41515260206c0c0d4104290354200c8502c0c00f49250076405c10010a001c1500c2000101450340c0c0310304001501203031110b22801c640d041240c040b103e45070ba1f00c420f200f096070420404901c04101c18118005581070100050022002500810000c841d22001c122640e80c1c41e08502e401c5c02c500d10101410340f400409060280649101e040c01b80e00b22240004102c2402c525803640c0c8a4000c802103103094034513800d100080c0300007031090340c03a40010f122104448005220740c4c0c494902d5103040e054a826203081c450f141a100b58040303071140030300314800b030100d10620010348101c682110700040c1c0740b0001090340709007034409003516046616003010402000034000d0f480d01500d000d004014084048500c042d142e08540e4000d0040d41e1340c144141404001614004110440c01890145503846e102d811a04c119010300042c003a40030180b10035400310660000030452500720803115910200c09d052010440c1d03041c10f0001500c0301160101070404640a080b81d0030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 932680206 1250 932678956 932678993
    0x90c13050915060a020105100b040602030319150311011404060804060b01180305060115181203050f0a1d09010b27061c050603010603121d04050c0414100206040f 71
    0x29501d00c89134000a008140c00c440d8002c104001d5a00420038601c10380030740303055031141e40040d8a10340315108413507001c1da10b0480034203105459040c440010030080c0300c03000c005d5216590420181d080240003402d0010711051442190070207000070001c0b180c0c0309060303c0c0c00075007000000a480080600480e00c1a0184520151f486e010307840000401500007003d9048034400360f01810b01d0150044221511000c00c06801180007030070310180000940441e508082500c44d0030414034240e030b91500035400b900140d440b000810940188500501c40b00581c940c001d1408950039075a80d810509024240d00522501a0400e1038856402c05c03a0002c2101c1030b059418000c21854031030780c00c1080211400103e00082d841c00d805c241c081246410140640350682c0d501c0440001e01d8140c00000319010b080c0d0f100704030341e0100500d40407281303603c56110b024003c807140100c09aa550a00d2a07a0002d0844c01c101d950107100d0707414044070003d074041900c1e80c000d6404040b038901071015090000f5400a11000003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 932681456 1250 932680206 932680219
    0xb091c02041b090321140c070915080c030d021e1509010902030d020a02030a0305030a0f060b0d0606090b04030b0c280f17070f0507060e010506090c13050915 69
    0x10b0362200e030094800d1003100d100c0ca12000d17070308201942003c4494041d0b42160007091100440b4150002118054495040d502d400c4034082650303071040f4419120480310903410082c0200c414840800144045000f0002c19030040102601c0241700075600e200385541e2010007000006108020581442a081840510721844020b030428500040c001c0031074990891185c81003095a43d0107600114a449013150001c014103030210041d10b0070b94107503200409414003907030f43c3d1900e9401411603118040280c005003480a0312008228801030840c0c9050700003009005400004102d46480c0c982241c007525032000c46507400d5100c08641c44542d01480d0001208000107160504080703450b400300380000120707540ca603c60301501c00c0043e00c0c04414010420940720244000a0390366000760152600745a40f86002d505d0303e2202e4440d202102d007048564031443c0d44035000d00c0358500c0d066408a81101d08804610324100304800c1e8680420030314403c0d940501900e80020350074060101c041d122070300303020700381 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 932682706 1250 932681456 932681501
    0x20307140c0c191e15080a1404050d023013081b0f040606050703030b030c120601080c10170406020d050c0703020f01052205070f0b040905010b091c0204 67
    0x5003410554140580f041d0390f1200c985004c2c8142c00004136001721a03811100c16800c0d82902000c440b04c840052074140590348464020081003800010148194000c00140038603111002e002800d105408602c03c0d140c0c0758618425901c0940380828800d954011440180da50007203140f906442100f541c480516070090101e0592994031100003005d80301d00441c2c4100d004110340040104580c003900030a070000e80d09100000c0002d0103a07000d40d0b00703124000c003114110181d000c00105000d141c15441c0ba0700ba01303c02d004100c0840200000d002c03280b001c4a0440701d01002c0e8400400701480c0f1030420799811541ca001c50b0034003076036604441c2d00c1050954140001d140014400903035502001d021001445032508058480d1410320407140195508000f40c038212a02222171211040031030f0f816585406600d00c0000c1320710321101c50100030014460074070b88451900d800c0708100d0b03c0c140e01c4420614030400918005e40d580c1524164074007021103655041d8482400441c00a0010710301024000e000480c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 932683956 1250 932682706 932682739
    0x319020301061d1804030305151e0112050424060e04080703020c0411162306040507080606010f050c0a330204030816030212031e0604020307140c0c 65
    0x151008070a4001002e1070311400c0f103001d0004001108400807006503080c1e001c14002446500000d400c460010200303800d4817150030006070f4400c801203200484000b82290100300e541c1006100181000d0040100554038103511141e050000c0070006941606601042409941c0703d80d0104000d072810a1a150541c50079280614217a806840c0c180c01500c65130044c0a164902401902a48040840240e0900d940e480d64520303900c10100b000c459541e00408905070950021074000c0001101d40000c1070b590034142061418070310940c03c0111503401c200b08100302c0b079130403641800300c2c0c14184c03030116a40c141c0e041d10581810030361180100780390b40c0c40503d100002c4050f6000b00050034554644002e4451402d0000100d100d10b2000401c040014403480e91044120061400024000e0060780c6a4000034030301c0720420350007142d450286000d24a1080781000303201075415403245094404603e981000c00b40500403604c10380b520000e940c000141301c0014042440418109000078050200d0401000c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 932685206 1250 932683956 932683967
    0x120106020a1a1005040c030221010f050315150d021c060609020c10050705040f03080309013b0304090c120e0a0c181803110c04060f0b031902030106 65
    0x580035070b920589000082c07105148076112502415030f103a00048218903000600024007a10382c200700a0590a0000d00d1804214850706003102120f41c408041a6040c035045241c40740c4142c10181c080d44c01800110341c4181c24004044e04000c030100c101140000c4140082e040172406000290010140850340071418458101000e41a110b680140031082d1202c03280b50883c058643c0420319507002031090701c440322003a03001c160000030320328205280c280c60700312807900c1c6140f591084400c1c0b4030000400ad4030350b03801c0c40b40d1035005c0280d04d04280d003030700c401d0155100d508684ca10410324818180c0c03c7c0704001c10400494004002050003484641c1e20100040c11400980c419140c40c203080109036444403002095585005a2001e11590518241480900c50014064458940300d07a5050107a590f000201c006500092196403a004008420400c40e401c0804041d4154000c1c0e003050814003200b81c2300a80901903516802440703849030b0780c09021610301080b07182c0261b20503100100100c0c1041c1c0c0007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 932686456 1250 932685206 932685223
    0xf080703020f042d15020a081305281a0301050f21070608060901050919090611040302010201150b1903020708040305061b0309100f02070512030a0e0102091f020312010602 75
    0x401100042591360b0301550781085a10817040040e000070034083e0015060001600510b180c040d100d118461701d0390042161603070034030072461032030110500e800d00403003144850320007901d900304404103800d0b00443e0702402030006004051081c805c90b5005a41525241104002c03047c400c0200e0761000c80000109403108494010b00740010714240004a6034104444114102e80002e0490034084c1e84215019130070940c101003044505485a040d000414014010f150310482300050b15079842d8079500c0060300b11982012a03040201d440d0f031082204030030a805a0b045450401c40701c1d03c000340746e03480480003849543c00c0207111410224000c810301c000007820900c910f901e02465401620b403d40c550000b408100c8265910341e00001c58a0a100c4140c2c000c0c0c800c0030008107026061551654805041500244956000300f201208104d104a883c5c00b940459282d02002140b45c0312081d004103180310141e00003000340300450b142c1110900e00c20804c0f150103079842106551956100c000003510b48000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 932687706 1250 932686456 932686529
    0x618040905060a0b100309020328050d02060f0601110c0126012408091b0f060315010e0a0819020619020303150628030f020a021c0f080703020f04 64
    0x3005c1c00303030740034060311030f5181e0321360000c000b400c1075001c2c00d0440300d007124001041c0f540c602c210380b0035000048040205481e200f4803600600f1b0b0b41e01d48135211030401c0b40018045810401142007180c161309001c5801c0031590002c0c82c10034401d00d070080390300310078002c2117103050b0700303072040000000e0a80c1200e14190000c40070850fa400d03420000400486600805440e05141600100e8403000c0c0f15800300b003000b44056014019401f0f1012070000240c0c240c2044503c0d16880c01400c01408866078080782c0161440c0041310120411405d00001c642c1d01d900460041400101101c41d880030740d0355040943d40100c00c41e1300d090b25820000c00b00203442c0d070815194444403030704440d8620360610344039064030740c0f91074003241e07a040d40180e0404210038643c03200d00302c6080c143ea401242c6211003c1d070000303140040854005180100000d07899070304104e41d000c458405c200207452460304842e84000a243c1081241c84c0158940b000140c1c0f583d498852544440c0e2000420110080e01f003d2044401c920b0468 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 932688956 1250 932687706 932687719
    0x1e03022217010b060d0c030605180609091c030b3c0d120804060e0f010b0909010c09231306030b10080618101107200618040905060a0b 59
    0x241020381900743c07080010303441d5000f0024050704480c00510703880404000b44070301d80170a05980d582c01080241003d42c105404039180842084224107200f80126007280c0500c00611005100c800d450b02046441800c0c90205611440243c005a60341c00010745005840700701c10b03002040041c03201d02c0c000307030301e260060001d1042d0340c404a061030556250705c2e200303800440031162104100303001c40b0b684000500c12107416980d40e81e20003024508002e02c080d140c401d02c000183c1458017808115803250000c0038200640c1c148000941c0240e841b07140001103424038000748117036010680c2d12840d0400544030381d9802c60807580704000d080d081500301200726400b60728540d44a4440e0503155803501d900740220081a170005002c281003848140705452040004015915520300480013607003602c10040031808040b4012862605200c400c41c3e034903004820810a404041c81c0e05004036000b8014400c881054240c1000710002e140ca49800200e1940c0d030003026130340c903031500c841000000d01519000b98000e81 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 932690206 1250 932688956 932688989
    0x3080310170102250f14010501090f02070f030f09090c170115020a0b06040608030f0315060c12070309031209031403040501020a080f07050a150b0904031e030222 71
    0x606100b1201260301104e01501314032035070155121900e60510f42240c010108801d0307000860310f10050072500f4030048001046a514040b005d0068589aa0b00141000e104100001c00510920070010750030b0750504098002c0c0191a10a8a601394181d002602c3d5500705142c500300103500029075807060907018041303250341c1d03281c00c4c11400111582d2000c501591041900c80e011030960000c15038007540083c00400c890f174071000316a0443c0c000c400300c924044004002d01c94600d00102c0b00c3e140300b000075101c203428401040c0c2c6007580d4282694902d281485c0c0024800140761050070000055904072030300d1001c541070107100800d03040b824403042e101c451414840002d5910044100c07402c9030816401891420603036169981d50358888030500d82c200408204200008100b402042107a90050620b1850f00c01451100b009039140c0c1c040d41d52160741d00c5000c010000c0d4021505009416000440d8107400c0c40841d005c1e0028401c0304002c503154100b459110a0701150b420310750043d69083c0c900c500039070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 932691456 1250 932690206 932690249
    0x2090c030402011b020d0620220e0402030d0c0302030d230a060803120604090c0b130807050a14130614040f0510181b270513020703020703080310 64
    0x90130915000f50702101101030301c00071901d241c001141901d402120f4000c011100072280aa541c0f0841b60315a0301c1c10442042c020a4079110328100003800e05104044c02c528065000a17110340040c080c00d0f045c015036070b0702e50090510810543d0400f8101140821001060121580c0b10300090040b1103224448100003600304580d038041c100403510480e00450400341560030401d55000001c0925420079559031408000c9039810b40d00340020f1a401590582d10910303070f02d0610486807107400c111085c1c1d102800070400740d1100010300080320ac82043d10070f00081100009000364410b00d106103640d0f42440c0d00071404c2d0391409940c82c400d080c00c13541006848000c80c40001550800c880c06400580b9226082215800f62408003225018412002640418910a055622102c2d4141c440041d0410504603a240140d94000c0982e030a220750701c285862410780011207041c40f001d006103400b03070081204800c141c000c020301809940d2010000ba103d20303107030150241740c0416101c0c92108803040040140c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 932692706 1250 932691456 932691497
    0x70b0112021309030504210206070b06011407050c060307120f0506030c030a0c0312140a02030a0e0f09040318030204091419050312041e03030f05100e06090405030702090c03040201 79
    0x307103501d45c8595060615040404461302d440c0c5002000030f00c0400c1c3c2940c016034440c0300400c0b070b00b44a00603c030341d1400e01c2c2000410001c2203070144845c0c4402008004046031001a01500901003150b0301a500d6880000403102c1034000344c03400c0703103180c02c1032050f4085050b190000ca10440d000d800b112541c0808808065840c40740c030001a01107940c1442c2440800c42e0110b00c042e408085080480c078903195806042110b41c80344503018016000070038610b140940c801e103030640c41401152001503484640c4000f40504501074070003800e10900c000078141ea5121840f00320010b540082c0104144032140c1043d00181c5010045010140160700300b200c0d0401c1024080c2c2d513541e030070400450a0200d8807104400119018000b61442100358510300815400350715010300d410302c02d690205100303840005000c00e07584080c04003400031b91900010f114081d140c030b403240e40c0030108a6041b20140c49609000d82184a040c40107500b01000310204000c002d0b52a004500440c401c1c0c0c1e8202e50603c280301c2c0d1005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 932693956 1250 932692706 932692721
    0x20703060f090b0a110712020606180f0a0c030f090503031009020301150309080706180c0603020301051e0d081611060f07120e031e060f060102031608070b01120213 72
    0x92049010415000150307100b00000c040352415941b80038140e4070ba50710103c50340c2c8a000c00590080040002e98200b016924039014503000011020703050005035046800c10080c4400b40440e1303039102e0481002c3c031a8000030f40c0200d41d180e0811a502d412b003051512544100e17800100d03a640300c04006031946851007207a0484030300940120743d4600c0070100b207000d028254020340f003010301842a0390104400303100300c02c10041d050404140c1120340d46001e0001c11241c0d44a4070925206000401c125180c8421844a07a8511141100c0c0000307803c00040d1224040c00004d0401d140c089484240d85485c4d1014188450140010032502419801001810b1082c4400c44031410700c14032224000850565060850143d5401d041c210070200101092030500700030800d489041c4880c07904000950148500c94100c00000560b482500d08a00040d550740b10b1959041c00302c0c001d5016103010700c82050144e03403500c0d600800044855030b40e4506468001c0b0030240a0f0b01c0b46d607240a83e02d600c0000c0b44070700e65 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 932695206 1250 932693956 932693963
    0x3050601020a02041e0b0a060c021c0b0a020a0f02011506200106080307022d0603222409080702060304051213090c05070c03110a0b0705030a3b1201020a020703060f09 73
    0x10441c40380b94244001d030891082f26408a1024210200c000381b0455107407072141c0c50b00d980050300d40074079500040020104200c0c00c0250791500000701015440045100190740e21814500a40000301300e00e5600e480d8200078060042d4a80755003c038180300302200403c0c0a0b4002c8409682c08006c003c2050070358140114a503031019004180c132031403400c0c1700020710b0740a001640005801040b5883d007450b241120360040310301c00201d00d0062070000b02d04000480340311f062070701085243c3d025a901c0c44140f0440c103000c1c3c45504080001000c010f420040340e1010ba02d0050342c41e403144600d052101001c0024010031031041d08040c1e180107a40d20941c29604810b4000e070742548590f20395100e0300007040c1d064030040e8100d0100c510108030f45440300024482280724100850345e90b0031104000f0180000007500401c2000300301d801c900e1170005611480070700300e0146070302c0c4500c003441c200052070b0148801100c801307540041001d00146070007041c0b01c000c46e40160400d010030303440281c001c403c0301d00815004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 932696456 1250 932695206 932695217
    0xb0307080711060a0b0a08010c08040b0c090a2411030702120106050a0b12070e01200c0d030201150b0f04060302070609020a08030a0e0d08030703050601020a02041e0b0a06 75
    0x1444544512185a04803400742062040200c081d10b01500380350741201c1d2042c4654940101d80c040d42032419000c030040c4001c4000300595084d9140040c9443d0020b0005800ca200110203d4191625182202e511540c020510100345680300c1d200401040304030851042062071290026815008020001342080400040c500c0c04586600700854040c1140308214a5075030303413001203400d0304d403501e07490b02a0980c42c0b2032030385610600c40003580e4644020f25003020400000003a400c00d9800502800c6500030b01031412120100d00c5404520701030300c4020b07480e03000c4001d00c1003d060680661180300a4401760b034048441c01d46802c426011032240c12460141c0308010001000481d109a0140a200d07101d5017011071003035882d8001984000154000401d0340d080010040000d40e0445421000d91a0a407801500c0340c0d05900c9403d0301e800010508824542c550001a401c1da10a00072007809a5000300704002c1d00d85d014245c940d0740b461032098040c0b050328208111000d442c0c0315250a04a5440e580c0c5c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 932697706 1250 932696456 932696461
    0x14090c060a08060607150c0201150f080606060318011a0f0109082a0901030606051f0c02040207060209031515060f040306151a0a080c1620040504050106031b0b03 71
    0x41c40200c1d40600030a6907820801c050030403032082031f1b01600c00da44072075a001040a45050a0206940001d0343c0854103401241c070080040c40c0e0f001c1805544103404845094413036032440e212010303000c07002c0c004079129442c04148802c030008102049004020594000320302180e01e000540d4540d215009103049039001001c4240c10416181c00004e520807000c2980004902c0302012a540300c0b0281c1044955540b1000c0c10f1200e802c005c2a0303c0d000320010b221302d003081009040041d108410001001c0e010750380009000041c02450340491707000c08000750848904010b8584131111105003514200b001420340036210090f884d1001c2540d01c0c20050403922854540307103235141ca00800c420210041000a541c200081c04103000000385c82c50b407040a0b1050350f4840d00140103251040003440b041051205104134024485480404ea500542c0a130b55440305d502c00176004000489040c801950042c20402007004101c1c044d0003040c01c4900c210b96440c03166007605070200c0441100c0c000d406100406200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 932698956 1250 932697706 932697709
    0x70b0412111806100504120b015d15051602150907080f0703120906020a02090603070519240c300509010207060e030c010c060e0114090c060a0806 64
    0x25600201592030400c5407800b1f07542c1740a0200e2085c2120107855010040004001d034024840c0078285666604498044200e503440103a4410807800b6000e00b0300c18603504805141d45004c100d8051800090f062061007511304d454001100c00308944400c000d6410b150200da4426102e40140e2501c00154001e880031480400100915910082404111384140100011981401e00001d80d0300c100980203002030754114144140034009205a4008000c240c0c482001a642e02190401c6100c0c1c0c1114026841d03111000080d1070200280c01035603101120b1490801880014003d0740202c07844881c081002000341840719801d54882c50f040004600160740c600c0005105685c0c50150000c01d84034141000e10500b1300021040ba030f030460700007007000011140101c3d0b03010482c03580200480e2428131491340039a8040380c1c4811402d9045414040040002d200b007082d40d8100c2462148024002c1000b10039140e4880b03084002900c00308000e00900a0a525074101002103444d13551840c1c07920180d0781c880700c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 932700206 1250 932698956 932698969
    0x1150f0e060409080307052d070303091a07020f0114070c020d14011103071d0a061d1302030f22020603070314010e07090e0423070b0412111806 63
    0xe06031680070f03603640e60b0000080d00b1100030b103000d000d0596901c2e032106903803154014004001800b250b0781d502c000c03a008040a08203401c0700d00c042c0c0c1c54503000c9425200fa1074059a00c0014484100c05100040c08000d0350b00d41c00030300e030100389090b44002d000300300c08101150901c41050b40c20b8000502ca03402e45070098106583c0040c441881009402e605a1420310f0031402c440b219403400452001c000144007810354402900421303a01c96802c10002c480e19980000c000180740d01c03404040c8010400c0508001c0d00015002e03440d24000350041391900d0142001000962003102c0c0320015504a102041c180500020300150b01540c4442c07000a0080607000c11071140c0000b04002d00701610303101e03d41c640c28174242c00c06000308403040c10311903e400c24800140c0f142e4810f4210000d0003034440100404624202c94103150380324501e64403e01e4011088400d82800d0310303900109005000082c0024990011342801c2e5005400348031030001070941541040b002408a00700d01d420a0014000704040e45043e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 932701456 1250 932700206 932700211
    0x160305130210110604302a080309010f060f0f0621021318090f021c02030f07051e060d0f06080712110f0a0618210501150f0e 55
    0x24200103d8401c1c11403d104e107889812601100d4141c11200c02c0c10549020b40c0b151021008400d01280007035000000c000c01664440003102c541c1e0311015070401300701002006501103e07400a44050350b03446c1c4600040d000e440402901c0781024540200001c09011140e000015a04850011010369280200803140d04807420a0603107159800c413440e04140110748024411608244030b07450240d840c18241a013510009071021006c1803c000d11000000c115100b0b0301c148130b504076032060116000300c1c02c004099126200c000d4040c4105d9800c450400c81c0050884201d9200b00d9403c44d10075540c411078110040700669a0b40c12600c1072140d49940004c41d040801d240303a0740400020321640d50050741c0e2900c40c0503440094001242440d01c01400700340051280400410742d81c452211840307501140000c0c582c0e00c19030701040b21410041100e424283d134480c001300049403200722041001c1c0812070031034840e420704640d0f03507281c07003044030b5030000b0103401104441101c1d071a0950341b0305e445583d60364410300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 932702706 1250 932701456 932701489
    0x5030703020d0903020a17030705070b041104151e0518060f0a0f18060807030b09010906020d05150d150b03070b030408090a0b0408030403081812061603051302 70
    0xb8010082c241055101d40c1075064080e600030070030082182005628002c2451844a002c1010010045020b400c07104a481c4a0b0f030051080e1345a503540e0900040008107058019401070a0080e02145800c6151460068030b4400040342001900d0101000000c0914803c4941203000883c0b1b1a80e89590306510584c00a8040c207072a00f003031f40e100005003502c3c415030070220110135a00c0c170a0128031a00042c06000b4034041904101590402040c00c0e580c5107584001803c01010701c0c00140891029080010300d00d0703010f4019920743c0030b0500ca04003d44000c4034048502c007180c01c00c44c0202d16100d440c81c1c80d1190000c98000d00c15a40d0b0700d80402504040003000e17058841c1560014196020341e0040d80304074091606561039421035020030800805960026030480741c244014401da10b4084100c0e000c0b40e034080c202c20741e0744015980c40000c0841904245078803207403100c00200308200c04200c1510400448205007502030341e4000070707800c950054035011003180041407890010300340381c240c04004804 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 932703956 1250 932702706 932702711
    0x90203010b0907110705010207080a020904020315010803040e0f161b02030f1506032e1e06030506060301181b21060638130303110f0a03050a05030703 66
    0x80384804212190400d54000d40029003485414869113800e210000c041c00b4244054142580b514a0443c2d03500001e43c0c1c040d00c644520000316007117542c1004840c0303081d003000b5440001980e4800809450380c01510030b5544a00e194000520300100411040b80700b0708141d0b40904007450001c1d000c0b9000c0b1041d109102100ea1101801c03070259a08100035698070b8a840020a80444401f001002414025120702d01940c060001600ca02c02d0f8490000070b5002c1c86a0401f0a070340e9090f00b45e00191101d2031040f9080d09000001410747d02e80c0703800410a03603005404035070741038841c2011306080329820a580c01c1094054200e6200045450070030000310091071103406a450344520725aa4400543d5000200c025188009041000f905009800c01400b40c0401d5884c1c029074100030b01000c88002a0300201c001003555255080750b04101598a100c22405000c60f010f40c40340307406400c00000040f401014860701079841015000003034543c44042d8165079590a004030b8000030b07201c5401c050401024583c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 932705206 1250 932703956 932703971
    0x160203041a031e070918180b070f2c060c0613150515130f051303030608011b051b1203040201030507081b0d06050306010f0e0c07050606010309020301 66
    0x88400040310a100752094a50ba41e03400c141a1690344206040320710307074a01c039525082020594114400b04119040c0320345400001e00c40303408080040a0f81450000303c0160640031400b841100d2141611924481d1220201300300c1d1000c1c01d40301007480b124a0051413104000300d036410030001c2c1046e03418040140c0a14203000f0403058003806d10400b1a0200008190302d03512201780f100398106401c40522183c0108190b05000d800020010031400b112402810310b101c0c0108400c603194010000038607610800c0105040025140c0c90525184500b600001c2c1000d901068078581032041c440c03401410501600e50000d1003100b510b0f580c0040d01c00051040b44407a10f1845607905024800d4414401c0c074080c1d41d04d1401c4d100240440e84064502c0c000c00c0300b070904000d002c040044030a0101d101c07500381c2c240c60305040d046400c0a0300072504110307018081d005c000141c0108880b046400d4881900c281c0700c0075a6100d405c42454006c0d880c014046600400106100354000d610440e810f9002800200b940c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 932706456 1250 932705206 932705219
    0x307091112010308072a05010809030d060303110106051c030e0a15170703020a020a170d181716060b040906022b0903120f0209130b0306060609010816020304 69
    0x1e5000f6807003a1414840090300000f00034041d8000d0715400c2c017800e2820f4001140202c40c0329101118080c45060101c501c0104074000010816190f14440081052064030307100d00d00180307039035038500a41c811517080150106941c40c0c5512a20381c5d408280ca108002d18a0b191402c9400f4a51903180503004040c00c2c102041280c2070396003d001855903615500c0078081c400c4481c08403180020b100c00d08140c81440b00b02c5500d0790100303207483c84580061031802000a414191006803082104182030b040c5800800a684401c0c4031729810154080c00240310101b03e41c0d1459241c40c42007140b41c0c9844040e4900c100000346c0c03964400e5901603c00707480042d41900300c1c2e81e1441240d105442d26a07940c20750444010341c651301c0c02c801b81c1c505e42c0c492000303001c0da18450b41d0240ca92020866803440d100d44402c58a8805a61036064802c1c4560041c901c001515482045100800300000061b019006900002d00c0700e0074039400302d03000c0c21410380d140c0c203083d0343c1d102c00c609001c5241c7d24440f0440c04100b00001b80c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 932707706 1250 932706456 932706487
    0x70e040624060302190903020609210a0f0c05030a081c09060501120b090c011d06070b010e0405060702010c0c021c0512090a08010501080307032d08010e0f040203070911 74
    0x2521658600507903917007190101110b00d522460342c2c5010030034240810b1005071110b000341d60040000b0340d440441417001d000125140190340104840707070300c10b221000060000c0a15241744841c00b45000d0695241c4a0f428103403542c402c203402410301201003144440c00381120701e86d0784401c1e400d54030000d65801c1c1503541e2400c1e00c4080e804810801001000b40d800c1c0141c0406444d00b004040b801005040341351000a0000d5140380780400505a848554203201d40310901120b98940e400129000c1e550703101d4040c0c200c2c020082d03406682710300c81d05c00005d14840c014401d45c241c01c91716484021901c03280d50f08006101c9407016041030100d0300e0251801c00501c00b0050221540d0b01440c0da0341d01d5200704810f0011420840c1d110305426070411703004000100c03020080341c014030f0b0180761060078040104624802c4d0000003098a103078441258031443c0c2381d6440306842e41680d010182c1e28a43d52108656100d03840d405a170003a40c941c100c4c0704100030b08090f55004c22500b074882d403682400d04038100c81b2101d9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 932708956 1250 932707706 932707709
    0x203031626091f1407080d052d060f1c0b15030d020c0901050d1b0305030a1205250908060c070b0c2517031509060102070e040624 57
    0x59030118401080b4a044900481440301d0499202004110f1903002050400704814003000c03640005400c9050055510445103c6039a440c0140040d041c0800322042680f42100e15007801020829407110040c1025a264050403004009a507c4a005400c00c141c5050790000039002c80b10f080712107030004041040480c8111700d8a43d1000d03d03140e03500241402c01c151103032540115000900002420703500d0903111815640141c0b40e103003200180c0c1c1380c00700031074070750502c1c403240720f007100c480041003000010040904000c02c2c6d4415490402111900c81a580c09483d084042c44600004515082003418414011005460184c04060f960b0b50310300c0c07c0440a4070126100315000030030509120688000c1c0d500100406109450041035241e02c00e845490403041c000900321001050080c2b219041208007000d01804240303940b814140d100c0200d0700071215026000e1807821001a20660011900310100c50743c0280c0d146981d95140d60b07000090804810744243c07049180404140c11001051305c80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 932710206 1250 932708956 932709023
    0x10e13140106090f06120504050a02090c1309060605070b060112060e0402030d02061b0a0507170c0d0815040b0d0b0f01030605100b0d1e050901091a0402030316 70
    0x10103504088005198003c01d401c0f07811480b40384001000141d6000501181c0c4c101c0103080001c5a4546291040c04c106c402c00010b540b100c40708084c004103400c043c008000b6007220315000300a503640c0300c2a00003612903911420000c41e0080c080000481c0c0103000040e401034052414043c108104180c460440e0590f0308081c001522035010007013182002c004140b0b0364a40c60006201a2400c400c80200040c4021040c2c0c211040100e91882c950740908281c49480394000ca840c896801003442c501c00c04c0d001500a80020302c10758000e100402e004488180c0107106014200c411f0304031403014040a44207044049070003200001c1402d010500e002c0d000c50050401600c00c000300e514605107001580d0f400b805095501d55020340401072107a009086070300c0443d1580f00800c50344104581d284a03a0b0040403200f01d090b090104010a00c2c40c10b6214003001c80c413684000425080070320401402c28030403100250903610810070030103986032186500440500c903480c81d01c0d4980d035103001c2400b0000c99070300300c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 932711456 1250 932710206 932710241
    0xa0306031415090f12490c080612120f0901271205160f1703090604170f0d03050114120a06050a06090216060501050d0809010e13 57
    0x20340c0d01d03101801e8080d0040c0e03c80f402014240708101c1265142c0c2158910501c0080000400d401415100604200c0070005110412084c1000c01c004400000c540400b0039039204104000c600e00d414540f09802c00c140c0d80fa9248500e43d980c2c2350901c2031075120044049000d200340b800e56008a8144801030084600c201d00c903c0e20781e0f2869001604084001214211150b400500c85070403044204401046404003200e015008046041c00d50400c520089011011741e070600d40800c1c110341d8001300c6401c0f0307100001418131200041c1642910f90081c002036540c011002c0000304060100c1804860743d41c0c130351605858080000501c60f914180000441da00481d0301c6200401c00040a08110300503442c081c0c440c1d004500fa00c0316103689a0300d5091000b040310342d642010818240c0c0d0340e4400300180005580c115510703d08c0c80400c0703018005c01e61044600504020000c40d00f41842d0078001c0030700364030010340c1c1d04044c0800010768040394001e030500d811540ca01d0030300d030180c0d905010300841e50f01480140c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 932712706 1250 932711456 932711473
    0x9050d03170615161a0c0a0503060409050f1614011e0e0901141e090612070f06020604120c0510020304020f04060b2701020709050c0903010c080709050103060302010c06020a03060314 80
    0xc101c00d0320503250101c174018840070030845e0729624202201e01c1c1e01c82618001c0c0d0303a41d807407000103002080802c80c040c1061084172400603800c074001620420800092070994a210b82c0ca030b601c24024070303038426240d00092030401300e4640c260f1624003481224086007000070290880c000481c0c81c500b002d0340302d4044500d05c03000490240c1820b4441c5814051820355508402c41d4400100701d000d6070262030540118040c21200c05150300c240415005042407100e480c5400303603500b1009589a105440c00e030703a821456500082d40e00d00070310300910f081d0f42c40302c007800545042c1401c1e40002c1d000100142d07040450707600444e085a44512590010b080003c0c92640c880b80f60600c01041820702c0d18003107001518080c41e144083ea00014800c045901d5464082420341c0d8551012119000750601542c040d800c000344c09420710b81207042244621b14544e1058806980c2c8c200440640d0f8541c072000e40030403d406422408540c29400801c0c50058600b03011421a503295034010001401c004406600c0d00528031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 932713956 1250 932712706 932712713
    0x2040615050a0f030219050702040f060605090301141b0304140703031205060414060d15090b06091605071112070303020d182616080109020109050d0317061516 70
    0x1d0f1081400d51854218104004510b5100c911090a00f84c10706102d03011964008540d2940c00025569090040c14468281d41c0e030409442a0006540c26110303500300b402654844404022180c03103000d403401e0703c0141d0170a0700c032010510340c4050810b581d10401c03481c2000602500304050f400541c841e9850342d116820300300d44001100c1014003224800c6040502c4004404850240681c11840489a01e100810645042000004a0081c00804500307011600c42440141c20b51544500411b6510040c00e507075943d044900514525100c4012802c00e01c02c040201d06044080d54000f64041c1981c0c445000ea40441441c2c15000c0c1d0048005a00c050750001071a0303442017040c100030040d04d91400301c20303041c15000184043d600088010346400200100685002006085898107840c00348113012926003e0482c00f1f40a241c00603400715416410002d621f040000c604003440d034045c0e0381c0b9070500b0a024000d00c0c0014020780500d5105403610440d20700b11144a0050a02c8910040b41c1a00300b8801e14 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 932715206 1250 932713956 932713967
    0x1b18090501140a15020d030f02040e04080301050a0501020a031d010e210d020a0302030d0b010c0212010605030c06031e0619170c030313060507080f0417100c021902040615050a 77
    0x300400881030740c00e02c01d1391074a0b8000030b1010b007040c900d0030041500007070079031140c000303004a9202c01c1e24185007000b40424420001c000b141030300d03412307602e078001d994540c1d0042e6915640369800500007002c114429521040c0c41461015124051401908a103507203c0051018011084101c00002606040c40040c820030800c045e0001d80500240120b100355403000383d1280038200500303c1440e203802c00c0c08002c0e072185c01c3c80341120307a0051000400d181c0c942a201e000382070500525020340302d04444070455240c040c041e00c0c40f41000190380060380754002c10300002100c0103440503070400c01d400304c0281c00010f8039090030060080c51000b1051185440200d61504401d4200c0320b010350420444205480c03001660203041e99954100555201c2003850443e42a10030750034006a0600040750102d44903012010802c0109016411604010301c1d04a41d40211a08046444090ba110341840501400351250740344d4501c0c0001e000040803039a036030500d500c41d020394500400140c00001c984104a4000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 932716456 1250 932715206 932715209
    0x90f101a220b1c0e01060b07030801050102160308070201020a020301021b120406051213120f080703060803031504111612090b34030e0a08011b18090501140a 69
    0x341c200c100c40601d005054100c511800b03420802d5918148401401d80140d50004c02008401400030003d81c2c0d501d0380180844d40020318200d00285a010002074207610004620685c901e0500c64401403d02e50303a03c078007407503008140c1241907000e07424076100940d8083c4064207201a140a8040c0d0b01e010341c3c01d9140c10042d40100404242209010903c08a42d100301502c207050192000282c00d5141c4004800b055140b20500034583e01c800c0701a854070702d030b010250000340040c5456580700391315503c0058040c0e480e14090100154030600c0022144107947e000008004000750001a1030303680081028117a0b8024443c400008940032200e41c1005089080c181c0f12a807d4949409614108071000c0701310b210f030503c0030540100c45101d40880c800070005401c41c0031130328001912481c1d070f180340c0034207807400e2245075511641d00c5071303c0012440818043c045102c400300c0080d41c981c40c00307044140e420303501217442106442d0b50100045040b440e180300b640c1c00303443d107550b503501c00c0403c81c81000b518545a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 932717706 1250 932716456 932716507
    0x201140f18060f0f06030f030a09060318110402030712021201030c06021c0f050c0d020f071a0412030324050913120804150c09030218010302090f101a 66
    0xb2604008248018224070303034021401d00003820744d039143c920000e85821600d901c5550280400140e02d2010760f00010003104407003240c0c909200c030401d404401086d400001c035024100100340c2c0d40c1c0c2d0071180f40c02da00039540007003141400c0d80801700303a4008004980200700c19288a03500200184140f01e58441284000d00b1a0302c000c041410041c4425401c91140d480b460080c84644004510654041d60507501502566402c813000c13a0700c050402940d40e0001e0b0b040c61858040d08202182c42d010b00a0321308800c060504d990381c54103250135400d9411107041e031001da04141d642d0301481d59900c150304094000f4003501c0b885e00050790802c0d00b007110301c504c054440c00c884880c0381080000030b04050404901c2000a042c0084143d40c0c600f01011040c3c45803050640603032030003822030380d4150848c0281c0e050328000e40341c04c0030309120100686480700082c04060744c08441d030300005101d01c101c0c041c0fa42d400f908000c802b01401e136072424449100e8001d4444002c05041c00304101e00051003030000121401e80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 932718956 1250 932717706 932717713
    0x60801050408040b0a1704030c0605010b0c030f0c0102040302190603050708100504090236063a0b10050f0f100302070302010905120712050306031c0201140f18 70
    0x40c00c0c0c1d1084101d20461003000e6400d01c01040c0c9a845c0d9026210704802e034107180c201c0036103e251a240043c1042110003040394a6883c5c040042103045480c0c3c180c95546450100035460981610050556500207102c800c443d907400b00408801602c8a4041d00c0800c08125500c1c0000c80c2020409815640000c02d0f0f14100204501084100c0032581001c5040310015100051176000038000b04000c4d504d0010b0f5100a1968584521044582e0680e860680041004200401d07101d803000c0109112030b00410303000c5101e44c1c03d01c0c5441c09258070780c512844a80920307201c003c00c2180c1d075004c000501c01caa25944856144000704160701348a17450011158044494504a2100705c00180004010080c00d00030140d02142940c01c0500035803012003682d4001080321410b80480d05525415070144d00308842100b00c0a8008020f01d01031801d0b240a42c000401614441c1d14045803030010002c0d0915603803c540d203a983d2100c428030301100733603402011040d10a840901d098000c005e08103c81001c40102e40c0e1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 932720206 1250 932718956 932718961
    0x912030c090b09030c0904111509030a14030403060609060e060d030c032601230604123002011b021209060c010b1003050a1404030509310209030106080105 68
    0x40d8030080c040c00ba03400200380c1e2520b414a080109140200220a954000d900001444144417088a00c140418021141d0340206034200d4080c100c18094184420b405603c40d5841d84006006074004400001a19084070b04140e500e8850700f0550352194404007500795504014444035120540b01d40d4020781c141c405985401b0b02d50b48c001c1000e50010000740401c804622902044080d081c0360071101d00b0350581c072030801c2d6160000d981107003c50404961440d8580c0c004001c43e420300b04d042c0d80450301e41030300300c00b58015251501d14110421025030303810380d026600c0e18180300316441038062140c95142d00005070385441746a010366490040c0c030004255484041d50851006500d4200d800c100350a40d449500c502c0c507400401d024010800c0d100f035000105c501e00c000101ea059000b00e1140c0c0a8480c140480c0c1008a071800605a06403000350009204010176181800c008030b182d014915031a160314441011003030200c1c81d8444440300754103255000140c212a80c81d00340906d0740900200345c0200541d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 932721456 1250 932720206 932720231
    0x1507150b0102121908150604030b09010b0d05073b0603070e09030906090315091018030f1d0a081f11090d0302070f0b0903210f1b0d0201091203 63
    0x2903132900c044020004105c0c00144401e02c42d06091034a00c50160401c3c0d21161a0300e454a5113680441c0c0c840c0c11586070444908041c5409020000400d40200140c001e042c200425803010702c01d400c45002800b40d001c0051241c2040700038010040106169845490781010400c040c10030840b5072004910005620501c01e81c0c880202c02c86101100458540e580c48410034003003424045121000042040c03a41c0030444158000300300e100c98080354280c10040920642004005440d0f0880080d000903002c1202046041c081c2c281c00503100000c6001400920958001988100541c0c002c100c3c0b90700041035192125922010070304601000c907400b4004901c0112401c82a40281c0d20094801c180e00700003041494000c2c00b0000141c01a0811000b840707450b407907141200c0e0b2000546900a224212b049000101e4407000c2c074210a0030015003a10300881c0c82ea1480c09604020010001c0c00000500c0a510b4a010000140140c500b41c0000c0b8901c0154203240300c41060754039030003050506110407140a03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 932722706 1250 932721456 932721487
    0xb030a14060328060f1b0c1a18010606120b01110606100c0b1f082113051f02070f08030a2001150302040b0411091507150b010212 57
    0x300c00d81a000c0080b880c4070720f0398411030048652405083c4a20300392012100c40d1168000300c00c16400c205802040040002048542400c6a540a080b04943c550380c174103c070401126581d00701e9018102c0c5a00c0e112031401407030840e0004e5100c0d0380170a041415040c000f0010703000b000d1041c082428046403580c50400710742d03200e5134000c0943d84142403005501c0041c6000d90b11032100c01e130f00304040c02128a003203c0d0058545446510341c1014200036180025a80c0000031451007400013400c2468000d88001d44c1c05600d50003016100700d1085503d80040740b0341d1603101082080c0c841c00c400408040c1103001010342421440d8210801c1c018442a050001010000172240c00020600d8036000507034414a08850300107020758560495400d1543c120140750483c01131400b035034000c4504101c1310000a00701303c216084840041c0d4200814080f0199510700304208a41400d0b280007140e150401030384c0c48078184046c440025445c565a48451411035a04100e01c00e0103034600550149890418161601c2c07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 932723956 1250 932722706 932722723
    0x3050d030e06060f030a05061602211c0f180c171f02070c0e04020a0e0105030703021302250c0906180e01151710020f070209040614010b030a140603 65
    0x20040510444d0003030700c00304030000322503411000b41c5d402401d200ea24409031040c80200e41006205580712404024004042048100001c00000d450b11500c6403184031001e21500323000d1031266442640102d611124010b00300c4040010a214030f0340180c1d403500360000f00d020b411000031200c456101c24032240e00000c482900d1008804920041200c0301b0084010784110503006110421000c000a520003121b485140220301c200e9462640315181d84652410f000d0074810954141c2c442e2200304054201506e48400c0c041e40108007514040b404c034043c030040302d80c08811001121f48624100b082c4001c070b0303900d0009050000d4080c0b1406261545580c00b6800f100c04001c1c03825500c91003281c004500750710000002d070080c540c0440846d074525160042280d080e0b40000c1034000c250009400e141e00d4800c941c07008044c0d196440c207140031902030141082006000300c0340665190408002420403440803402043d804281a68a103010300390f210903170300e41c040603400000c140014055207a401042520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 932725206 1250 932723956 932723959
    0x3270804031707050a060903020114101202030304080f1c02010c050409050a150b0a11012309100203090d030b010513090b01030b090f070e18071815020703050d030e0606 74
    0x34030040b141070149803a48200ca0000745148602d0b02150304010fa15080007503118060380003040305a0b00007090014001c0112032808074602050818055054401e03030181c05180041c041f6824140c403410340300d11f0f24028103401d0081d0340c0840701b044420203000c681001100381d40c8c4028825000d50304409081d501450090120076903d48000a100900541c0311345a6100154906a66259102c846254a600c00100701000400c00900c001408205014010f110865041c203007000400b003400300310043c41c0191801d205409114503012040486001650081041c2c1000c1c20585400c83c4003e422a0b98288115040c010180180702c03045420081e00800c032410054041000207030500120010820012480e504c01c40700d20610118011101e540c030310030310058a90b4012160100100903482c103621607007015200047c00012205481603405480f108080c0c4242d050803500c4042c1ca0030600c40c0c4203000801030b80650020014400200603440002410f81010809420090800354035100000d0816 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 932726456 1250 932725206 932725223
    0x9120106211a180a030314150d020904030e030607180f05030c1e060f180f100c0203122704060f0302060f07080c0d090608190c0903120327080403 64
    0x41c0300c8030003c01401060903001415030710f800303050f4074001d0f00501c0d4103105102e02119010000741c0134004410500c488080c0100040801400b50342080400c8070000c004038100302c4000c0801c1c115890800c203450081c0101d85420004100c9120500310040c06036000240d510f042d1a0200100d48000c5000001d44c00161440c140202020510664800c1545181e035002000017807081055204a000f070851404a9501d5840c86161101040344c3c6110800300c040e07001b241c58002d10301850050701740e2061140302506403806403811000c2e804a50300090349582c00f034002c0041d41e20382c0d181d15103441780f220f101c00c6404009050500300c038a903c4c80d00e240002402980c001496241c2d809407442a078002582c448000c950302ca03104049203441348101030404000c1801c0c071001080390340c041c1d26654480d414900c00c079144400f508410320043e18071f03e90715800b8000c607080c020021600c00e45c65071507030380010b450100d000c41240903000070109404c9680c0001c150503214502c00035030148100c0c3c084a8000c40d06 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 932727706 1250 932726456 932726461
    0x31b02011b060e1605040b0d05032a060106032705060712110307210b2407060c0201050915010305060f0601020316060b09060d020a05120309120106211a 67
    0x4a006100d2800c503103040b0b1003400c01e030301901503440321184d0980d402a101401003140500900c184100540801440703a0018007803400d5840d0740034902030300800c0d08018020b45400101c0042d040100a8003c500020b40312038009900980c001490411a209042480a01c003101e446480e10381c440640340f40c04000c1d14043c41403011540760851043e86028070100c5a503402c1c0024041e02c601c0401181c05842070700c500d80d02c81c3d003070710744d2041e009010f0001d0005164001030200c0c440b1031442103411130290b40c40921000d40411841c0c49004070115545e00001110700f000300340541f41150143c8000c500d00b0300200103100003000454110703000038540310301603121788030000140e040d4000c102c200941c03055003521040078008180c011600b040015100b51180b92640b8090001d4038000c508045e4002c0c4c2084c000300014200050b6080002e070744081131341c0c2440890300c0006c42e80c080320720300389002d43c0d142d41003409404018020344481d00e02115140c07440c030003542e4401003240308880c0000c0725410309400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 932728956 1250 932727706 932727713
    0x13030303150801150302030706020613020d020406031203090215040602250e090d03051506160201020304180f0e0610030b040302030d020a030c0212091302090d020a030c03031b02011b 80
    0x441c40081d00300140280f0004e0380c035000c01406001c0c5403005920038890614005100c5002042203400b80649444c00d1a0702c082e42e0f024001c4d01d510b0550f0480c0c0055492400101258103803a0078400c00d8880d98000c2440950b0740104032881d286005c055403045d404100400540d500020741c03148070798a0b4400f0805003031640c0407801305900b01d80d100044044000007004003030782012959419101103500e0401042e2126405903042548010649411200c1040200e89140101902c400701c0c0d0320500c101d80c5050f0f1038124244ca8032401389028100c1d940c4401d0480c60303903041c60082614403803c1900038038070381c83d04500c6824001c0790b034400030b0031521a040104081c14824000c803004041c0c151001d40d0b4482d0709a000800420041c01032600600a2101105030320412100300c822408008181060304102c00035034000075840300f45200e0703201800c2c080c1da00040e2103024528000718043c1d40c0c0310707a180d4038504003d0200d01000f114240307490400840040181c1c0c0150001800000803c480f84140c1010301c5e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 932730206 1250 932728956 932728991
    0xd1b0f110a121e090b040509040c080d0507030201060b0a08270114070e0d02031c0507060e0d0206070e0306130311060a060f0902030c180a0f08012013030303 69
    0x60140c030100400c1505184240c108580c0302460720a1000700480140003c1c003240e01042034080c019500e84100010452440c01d49605034000380580c016a844a913154015440c142801c180e00d404920f0200d044828950280700d408002c240d08103520b4a4242102d100500c0e04074010115112140760141d00d0000000360480c0c03140318280c510003003000c3c000390740c0c1e4076000c400d04581d0381d0002001c070902d0f13803518184a07906021090380a8020030310076410fa04000740d15401100c1c07210030401c0c1849050b000c90034900410400d20070850281039060000c00009040085c0200b005080c081c451102d00a83d03100054090350020000400e00d54a150b54a0f08542641e6a040d0f03114842c450071042c403088454036440082200d0008030407117411070742c5a007040241e0004481018580e0400d21180480c90a00840300520007002410409090b80342d03038403a8030654664200055a070b640308115070480c00340b01071050b813011041ca8010f0803d07002d48144801c00c8001d010040c205a01c9142040070400c43c40c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 932731456 1250 932730206 932730223
    0x7081b040f0303321213150c0201110d05160801150503040f0b090601060305090d081b070b040602120a09050c040c091715060d051b010203040e0703020d1b0f11 70
    0x185001041c4130aa58001c0003d40140031848a0b0100e0440443d80c5c1a4a01c00c042d02c0d9180e022003151840c203807070f11030030f40284410174001003955256203111030400340c46030007080592140d000014aa040490041840c010803201403014081004010b02001510790605103910505151250f581d965902c0d01103603e607403601005000300c540ba000d21403490800308107103050300c12035681000540e94241c201c56882464030200000f1442e401c0114001d03422480c1000c20200d5102609480c0106a5441c1040c0d03610458096408942c04640d40100120305412950070000006050250b48030944405444850703185280d44140d0f03850302e0990440740242c0032103000f0104044400326050f2501a41919074040d00001e50441c001da00c00207030146040e07528a800035801400621300c6e03c4258034003464040010702d05505600c0700b4040013580e424220b6880c0e2080500d6900982c075007034081c0101d003c3e40c1e140130424aa81105240b8203040680c041280c184005451405528509100424501307202a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 932732706 1250 932731456 932731517
    0x343080a1e020f0d2f0c1c05061005060f180a0603090c050a0f03030813020607030306061106150d020a2c0901020306030304050d0303020d0507081b040f0303 69
    0x2505111281c0030380228030510003120324000d580d1400c010389411200b10305200300303440c00203a803414030320071aa0b0940072031300c42c9480318001c40d6080c440c01400501c2c010303003400c91001d05040300b10602007080310034000c013a00220001c1d0041013103410400011031500034841d180e00100380100e403406802d80903d00c0310192140207804d448a2984030346004000c3c081c80802030702d000000410000796030034180300303c10444100000c403064440c216502140c145c0310140c144100610741260400140e03458500529405110303490005510717250130b0300604405441010080c2c941c10800030002030400d554a990006c840c03c80710004003000d103200240f107042c203030b80207100000c0c614030402901c10310015041592468011b149a8950348030b40300c140c280e1108039440340d00341e00180010000b50501e1142d505042d44a0b040c0981455400d200107011a0401c803924000260701c1001c0c8070860361804810040c01100c00c00561a09041803060824441070780b10040c03c214989111030b60b54103d82d003511042842 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 932733812 1106 932732706 932732747
    0xf020609060d050115080109090201020604120908101a100c0b15130c03230f0903070b0c0901030b040516110f0343080a 53
    0x100d418155080344040c4140c2d010310b0000c1c00307034070301a2043d05075600800312600c1d4000c245100690000c1c40a500d130058410150744d0100c1c10740c0c0c1c081c0d008031000c030700321140180413a202802a806810580200d260001200450760000e403504c444003034400916600d044104040c681d009291240850380c2d41440b000042d058000c06039110605c0e214841c044404440030440356101d20501c180c15907a42c1c02031100c4580c040c4580f9002680846c9031102c108000203810b40d1000300645a0a0840302071000100c150000300101c1d010f81c0c1c0d0162043d5518240030000c03082c40d40183d00744501007070a0440c100540e042074480c0c2407140403070400081d0704c81c10081013605c42007403c40d401d00b8240101a45010240c1c0104001d141e030700c031454600400d2a626461000126128214000d1211141c03c1c8030021507410041740714113640c00c401c84554810981c0c40030b070b0b120b160801240c0440e05 = true := by decide +kernel

theorem cover : BRFrame.Cov 932553956 932733812 := by
  have h0 := BRFrame.cov_init 932553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 932553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 932553956 ≤ n) (h2 : n < 932733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
